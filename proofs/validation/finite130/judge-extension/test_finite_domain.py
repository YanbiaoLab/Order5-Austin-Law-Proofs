"""Finite-domain API tests; run against the proposed judge-v3-repl extension."""

from __future__ import annotations

import asyncio
from pathlib import Path
from types import SimpleNamespace

import pytest
from fastapi import HTTPException
from judge_v3_repl.common.models import VerifyReq
from judge_v3_repl.config import DEFAULT_STAGE2_JUDGE_REPO, JudgeV3ReplSettings
from judge_v3_repl.control.config import ControlSettings
from judge_v3_repl.control.runtime import ControlRuntime, _request_key
from judge_v3_repl.official import load_official_verify_module
from judge_v3_repl.repl import ReplInfrastructureError
from judge_v3_repl.runtime import JudgeV3ReplRuntime
from judge_v3_repl.verifier import render_repl_problem_source, verify_answer_repl_blocking
from pydantic import ValidationError


def request(domain: str = "all") -> VerifyReq:
    return VerifyReq(
        problem={
            "id": "finite-5093-2",
            "eq1_id": 5093,
            "eq2_id": 2,
            "equation1": "x = y * (y * (y * (x * (z * y))))",
            "equation2": "x = y",
        },
        verdict="true",
        code="import JudgeProblem\ndef submission : Goal := by exact finite_trivial\n",
        model_domain=domain,
        timeout_seconds=10,
    )


def test_domain_is_explicit_validated_and_defaults_to_all() -> None:
    req = request()
    payload = req.model_dump(exclude={"model_domain"})
    assert VerifyReq.model_validate(payload).model_domain == "all"
    assert request("finite").model_domain == "finite"
    with pytest.raises(ValidationError):
        request("infinite")


@pytest.mark.parametrize("domain", ["all", "finite"])
@pytest.mark.parametrize("verdict", ["true", "false"])
def test_exact_judge_owned_target(domain: str, verdict: str) -> None:
    module = load_official_verify_module(DEFAULT_STAGE2_JUDGE_REPO)
    spec = module._parse_problem(request().problem)
    text = render_repl_problem_source(
        module, spec, SimpleNamespace(verdict=verdict), model_domain=domain
    )
    if domain == "finite":
        assert "import Mathlib.Data.Finite.Defs" in text
        target = (
            "∀ (G : Type) [Magma G] [Finite G], EquationLHS G → EquationRHS G"
            if verdict == "true"
            else "∃ (G : Type) (_ : Magma G) (_ : Finite G), EquationLHS G ∧ ¬ EquationRHS G"
        )
    else:
        assert "Finite" not in text
        target = (
            "∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G"
            if verdict == "true"
            else "∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G"
        )
    assert f"abbrev Goal : Prop := {target}" in text


def test_cache_and_persisted_request_distinguish_domains() -> None:
    all_req, finite_req = request(), request("finite")
    assert _request_key(all_req) != _request_key(finite_req)
    assert VerifyReq.model_validate_json(finite_req.model_dump_json()).model_domain == "finite"


def test_finite_default_policy_preserves_axioms_and_explicit_policy() -> None:
    from judge_v3_repl.common.proof_policy import ensure_stage2_official_problem_defaults

    original = request().problem
    all_policy = ensure_stage2_official_problem_defaults(original)["proof_policy"]
    finite_policy = ensure_stage2_official_problem_defaults(original, model_domain="finite")[
        "proof_policy"
    ]
    assert "Finite" not in all_policy["allowed_declarations"]
    assert "Finite" in finite_policy["allowed_declarations"]
    assert "Finite." in finite_policy["allowed_declaration_prefixes"]
    assert finite_policy["allowed_axioms"] == all_policy["allowed_axioms"]
    assert "proof_policy" not in original
    explicit = {**original, "proof_policy": {"allowed_axioms": [], "allowed_declarations": []}}
    assert ensure_stage2_official_problem_defaults(explicit, model_domain="finite") == explicit


def test_blocking_verifier_passes_domain_to_module_renderer() -> None:
    calls = []

    class Capture:
        def verify(self, **kwargs):
            calls.append(kwargs)
            raise ReplInfrastructureError("captured generated target")

    req = request("finite")
    with pytest.raises(ReplInfrastructureError, match="captured"):
        verify_answer_repl_blocking(
            judge_repo=str(DEFAULT_STAGE2_JUDGE_REPO),
            problem=req.problem,
            verdict=req.verdict,
            code=req.code,
            model_domain=req.model_domain,
            timeout_seconds=10,
            repl_pool=Capture(),
            max_code_length=None,
            max_false_cert_bytes=None,
            execution=None,
        )
    assert "[Finite G]" in calls[0]["problem_source"]
    assert calls[0]["submission_source"] == req.code


def test_worker_propagates_and_reports_domain(tmp_path: Path) -> None:
    calls = []

    def fake(**kwargs):
        calls.append(kwargs)
        return {"status": "incorrect", "error_code": "LEAN_REJECTED"}

    runtime = JudgeV3ReplRuntime(
        JudgeV3ReplSettings(judge_repo=tmp_path / "repo", repl_bin=tmp_path / "repl", workers=1),
        verify_func=fake,
    )
    try:
        result = runtime.verify(request("finite"))
        assert calls[0]["model_domain"] == "finite"
        assert result["model_domain"] == "finite"
        assert runtime.health()["supported_model_domains"] == ["all", "finite"]
    finally:
        runtime.shutdown()


class Backend:
    def __init__(self, domains=None, wrong_echo=False):
        self.domains = domains
        self.wrong_echo = wrong_echo
        self.calls = []

    async def health(self, base_url, *, timeout):
        response = {
            "status": "ok",
            "workers_busy": 0,
            "workers_total": 1,
            "timeout_contract_rev": "participant-lean-module-shared-v2",
            "request_timeout_overhead_seconds": 1,
        }
        if self.domains is not None:
            response["supported_model_domains"] = self.domains
        return response

    async def verify(self, base_url, req, *, timeout):
        self.calls.append(req.model_domain)
        if req.model_domain == "finite":
            assert "Finite" in req.problem["proof_policy"]["allowed_declarations"]
        return {
            "status": "accepted",
            "error_code": "ACCEPTED",
            "model_domain": "all" if self.wrong_echo else req.model_domain,
        }


def settings(tmp_path: Path) -> ControlSettings:
    return ControlSettings(
        backends=("http://worker",),
        db_path=tmp_path / "jobs.sqlite",
        dispatchers=1,
        max_attempts=1,
        retry_delay_seconds=0.01,
        backend_health_timeout_seconds=1,
        default_timeout_seconds=10,
        timeout_grace_seconds=1,
        job_wait_timeout_seconds=5,
    )


@pytest.mark.parametrize(
    "domains,wrong_echo,allowed",
    [
        (None, False, False),
        (["all"], False, False),
        (["all", "finite"], True, False),
        (["all", "finite"], False, True),
    ],
)
def test_control_requires_finite_capability_and_matching_result(
    tmp_path: Path,
    domains,
    wrong_echo,
    allowed: bool,
) -> None:
    async def scenario():
        client = Backend(domains, wrong_echo)
        runtime = ControlRuntime(settings(tmp_path), client=client)
        await runtime.start()
        try:
            if allowed:
                result = await runtime.verify_sync(request("finite"))
                assert result["model_domain"] == "finite"
                assert client.calls == ["finite"]
            else:
                with pytest.raises(HTTPException):
                    await runtime.verify_sync(request("finite"))
                assert client.calls == (["finite"] if wrong_echo else [])
        finally:
            await runtime.stop()

    asyncio.run(scenario())

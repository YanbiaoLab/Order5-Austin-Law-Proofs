"""Check saved Aurora-56 evidence without running Lean or contacting the service."""

import hashlib
import json
from collections import Counter
from pathlib import Path


ROOT = Path(__file__).resolve().parents[3]
BATCH = Path(__file__).resolve().parent
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def digest(path):
    value = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(65536), b""):
            value.update(block)
    return value.hexdigest()


def require(condition, message):
    if not condition:
        raise ValueError(message)


def load(relative):
    return json.loads((ROOT / relative).read_text())


def main():
    manifest = json.loads((BATCH / "manifest.json").read_text())
    index = load("proofs/index.json")
    rows = {row["equation"]: row for row in index["equations"]}
    entries = manifest["equations"]
    require(len(entries) == len({e["equation"] for e in entries}) == 56,
            "Expected 56 distinct equation certificates")
    for relative, expected in manifest["files"].items():
        require(digest(ROOT / relative) == expected, f"Hash mismatch: {relative}")

    for entry in entries:
        name = entry["equation"]
        row = rows[name]
        for key in ("certificate", "judge_problem", "request", "result"):
            require(digest(ROOT / entry[key]) == entry[key + "_sha256"],
                    f"{name}: {key} hash mismatch")
        request = load(entry["request"])
        response = load(entry["result"])
        result = response["result"]
        require(request["problem"]["eq1_id"] == int(name.removeprefix("Equation")),
                f"{name}: wrong source equation ID")
        require(request["problem"]["eq2_id"] == 2 and request["verdict"] == "false",
                f"{name}: wrong target/verdict")
        require(request["problem"]["equation1"] == row["formula"],
                f"{name}: source formula mismatch")
        require(request["problem"]["equation2"] == "x = y",
                f"{name}: target formula mismatch")
        require(hashlib.sha256(request["code"].encode()).hexdigest()
                == entry["certificate_sha256"], f"{name}: submitted code differs")
        goal = (ROOT / entry["judge_problem"]).read_text()
        require(row["formula"] in goal and "abbrev Goal : Prop := ∃" in goal,
                f"{name}: companion Goal mismatch")
        require(response["job_id"] == entry["job_id"] and response["status"] == "done",
                f"{name}: job identity/completion mismatch")
        require(result["status"] == "accepted" and result["error_code"] == "ACCEPTED"
                and result["verdict"] == "false", f"{name}: not accepted")
        require("judge-v3-repl" in result["service_rev"], f"{name}: wrong service")
        require(set(result["axioms"]) <= ALLOWED_AXIOMS,
                f"{name}: unexpected axiom dependency")
        require("theorem tower_injective" in request["code"],
                f"{name}: missing explicit infinity declaration")
        imports = {line for line in request["code"].splitlines()
                   if line.startswith("import ")}
        require(imports == {"import Lean.Elab.Tactic.Omega", "import JudgeProblem"},
                f"{name}: unexpected dependency")
        recorded = row["aurora_validation"]
        require(recorded["job_id"] == entry["job_id"]
                and recorded["certificate_sha256"] == entry["certificate_sha256"],
                f"{name}: index/receipt mismatch")
        proof = row["infinite_model_proof"]
        if entry["previously_in_main"]:
            require(any(p["path"] == entry["certificate"]
                        and p["sha256"] == entry["certificate_sha256"]
                        for p in row["additional_model_proofs"]),
                    f"{name}: missing additional proof record")
        else:
            require(digest(ROOT / proof["path"]) == entry["certificate_sha256"],
                    f"{name}: primary proof differs from accepted bytes")
        local = entry["standalone_local_check"]
        if local:
            require(digest(ROOT / local["record"]) == local["record_sha256"]
                    and digest(ROOT / local["log"]) == local["log_sha256"],
                    f"{name}: saved local-check files differ")
            check = load(local["record"])
            require(check["status"] == "passed" and check["exit_code"] == 0
                    and check["sha256"] == entry["certificate_sha256"],
                    f"{name}: local check applies to different bytes")

    require(sum(not e["previously_in_main"] for e in entries) == 30,
            "Expected 30 newly covered equations")
    require(sum(bool(e["standalone_local_check"]) for e in entries) == 30,
            "Expected 30 saved exact standalone local checks")
    models = [row for row in rows.values() if row["infinite_model_proof"]]
    require(len(models) == 98, "Expected 98 model equations")
    require(Counter(row["table"] for row in models)
            == {"20.1": 10, "20.2": 86, "20.3": 2}, "Model table counts differ")
    require(sum(row["explicit_infinity"] for row in rows.values()) == 70,
            "Expected 70 equations with an explicit infinity proof")
    for name in ("Equation5834", "Equation40037"):
        proof = rows[name]["unrestricted_triviality_proof"]
        require(digest(ROOT / proof["path"]) == proof["sha256"],
                f"{name}: preserved triviality proof hash mismatch")
    print("PASS: 56 accepted request/certificate/receipt bindings; 30 new equations; "
          "26 existing equations supplemented; 98 total models; Lean/Judge not rerun")


if __name__ == "__main__":
    main()

"""Read-only binding audit of current proofs, local checks and Judge acceptance."""
import hashlib
import json
from pathlib import Path
from verify import ROOT, HERE, ALLOWED, sha

REMOTE = ROOT / "proofs/validation/aurora/Equation27863"


def audit(check_index=True):
    manifest_path = HERE / "summary.json"
    local = json.loads(manifest_path.read_text())
    assert local["status"] == "passed" and local["modules_checked"] == 7
    for name, digest in local["source_hashes"].items():
        assert sha(ROOT / name) == digest, name
    for unit in local["reports"]:
        assert unit["status"] == "passed"
        assert sha(ROOT / unit["log"]) == unit["log_sha256"]
        assert all(set(v) <= ALLOWED for v in unit["axioms"].values())
    source = ROOT / "proofs/Equation27863/InfiniteModel.lean"
    copy = REMOTE / "certificate.lean"
    payload = json.loads((REMOTE / "request.json").read_text())
    state = json.loads((REMOTE / "submission-state.json").read_text())
    job = json.loads((REMOTE / "job.json").read_text())
    receipt = json.loads((REMOTE / "latest.json").read_text())
    assert source.read_bytes() == copy.read_bytes() == payload["code"].encode()
    request_hash = hashlib.sha256(json.dumps(payload, sort_keys=True, ensure_ascii=False).encode()).hexdigest()
    assert state["request_sha256"] == request_hash
    assert state["certificate_sha256"] == sha(source)
    assert state["post_attempts"] == 1 and state["phase"] == "terminal"
    assert state["job_id"] == job["job_id"] == receipt["job_id"]
    assert receipt["status"] == "done" and receipt["error"] is None
    result = receipt["result"]
    assert result["status"] == "accepted" and result["error_code"] == "ACCEPTED"
    assert result["verdict"] == payload["verdict"] == "false"
    assert set(result["axioms"]) <= ALLOWED
    assert payload["cache_mode"] == "off"
    problem = payload["problem"]
    assert problem["eq1_id"] == 27863 and problem["eq2_id"] == 2
    assert problem["equation1"] == local["source_law"]
    assert problem["equation2"] == "x = y"
    index = json.loads((ROOT / "proofs/index.json").read_text())
    entry = next(e for e in index["equations"] if e["equation"] == "Equation27863")
    assert entry["formula"] == problem["equation1"]
    if check_index:
        assert entry["infinite_model_proof"]["sha256"] == sha(source)
        assert entry["explicit_infinity"] is True
        remote = entry["aurora_validation"]
        assert remote["status"] == "accepted" and remote["job_id"] == receipt["job_id"]
        assert remote["certificate_sha256"] == sha(source)
        assert remote["result_sha256"] == sha(REMOTE / "latest.json")
        assert index["local_formalizations"]["eq27863"]["manifest_sha256"] == sha(manifest_path)
    return {"status": "passed", "equation": "Equation27863", "local_units_checked": 7,
            "certificate_sha256": sha(source), "request_sha256": request_hash,
            "local_manifest_sha256": sha(manifest_path), "remote_job_id": receipt["job_id"],
            "remote_status": result["status"], "error_code": result["error_code"],
            "elapsed_ms": result["elapsed_ms"], "cache_mode": payload["cache_mode"],
            "remote_axioms": result["axioms"], "post_attempts": 1,
            "receipt": str((REMOTE / "latest.json").relative_to(ROOT)),
            "receipt_sha256": sha(REMOTE / "latest.json"),
            "scope": "Current source bytes, exact equation binding, local proof audit and accepted remote submission"}


if __name__ == "__main__":
    result = audit()
    (HERE / "remote-audit.json").write_text(json.dumps(result, indent=2, ensure_ascii=False) + "\n")
    print(json.dumps(result, ensure_ascii=False))

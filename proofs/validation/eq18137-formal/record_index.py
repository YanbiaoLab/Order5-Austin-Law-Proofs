"""Register only Equation18137, after verifying the current checked bytes."""
import json
from pathlib import Path
from verify import ROOT, HERE, sha


def main():
    manifest = HERE / "summary.json"
    summary = json.loads(manifest.read_text())
    assert summary["status"] == "passed" and summary["classification"] == "nontrivial_infinite_model"
    for name, digest in summary["source_hashes"].items():
        assert sha(ROOT / name) == digest, name
    index_path = ROOT / "proofs/index.json"
    index = json.loads(index_path.read_text())
    entry = next(e for e in index["equations"] if e["equation"] == "Equation18137")
    assert entry["formula"] == summary["source_law"]
    before_others = json.dumps([e for e in index["equations"] if e is not entry], ensure_ascii=False)
    cert = "proofs/Equation18137/InfiniteModel.lean"
    goal = "proofs/Equation18137/JudgeProblem.lean"
    report = "proofs/validation/eq18137-formal/README.md"
    manifest_path = str(manifest.relative_to(ROOT))
    result = next(r for r in summary["reports"] if r["module"] == "InfiniteModel")
    entry["infinite_model_proof"] = {
        "path": cert, "sha256": sha(ROOT / cert), "origin": "local_formalization",
        "validation": "local_lean_recompiled_axioms_checked",
        "source": "Nat-labelled finite binary trees with unique relational decoding of infinite key sets",
        "goal": "Exact Equation18137, nontriviality and an explicit injection from Nat",
        "dependencies": {goal: sha(ROOT / goal)}, "report": report}
    entry["explicit_infinity"] = True
    entry["local_lean_validation"] = "passed_for_local_formalization"
    entry["explicit_infinity_proof"] = {
        "path": cert, "sha256": sha(ROOT / cert), "theorem": "submission.CM.tower_injective",
        "validation": "local_lean_recompiled_axioms_checked"}
    entry["model_compilation"] = {
        "status": "passed", "checked_sha256": sha(ROOT / cert), "version": summary["version"],
        "log": result["log"], "log_sha256": result["log_sha256"], "axioms": result["axioms"],
        "elapsed_seconds": result["seconds"],
        "sampled_peak_rss_mib": round(result["sampled_peak_rss_bytes"] / 2**20, 2),
        "dependency_manifest": manifest_path}
    note = "2026-09-14: 关系型无限树模型完成；四模块与独立展平证书均从空目录编译，原式、非平凡性、Nat 单射通过。仅本地验证，未调用远端 Judge。"
    if note not in entry["notes"]:
        entry["notes"].append(note)
    index.setdefault("local_formalizations", {})["eq18137"] = {
        "status": "passed", "equations": ["Equation18137"], "version": summary["version"],
        "report": report, "manifest": manifest_path, "manifest_sha256": sha(manifest)}
    files = set(summary["source_hashes"])
    files.update({report, manifest_path, "proofs/Equation18137/README.md",
                  "proofs/Equation18137/MODEL.zh-CN.md",
                  "proofs/validation/eq18137-formal/record_index.py", "proofs/README.md"})
    files.update(r["log"] for r in summary["reports"])
    remote_dir = ROOT / "proofs/validation/aurora/Equation18137"
    if (remote_dir / "latest.json").exists():
        from audit_remote import audit
        remote_audit = audit(check_index=False)
        (HERE / "remote-audit.json").write_text(json.dumps(remote_audit, indent=2, ensure_ascii=False) + "\n")
        receipt = json.loads((remote_dir / "latest.json").read_text())
        state = json.loads((remote_dir / "submission-state.json").read_text())
        result = receipt["result"]
        entry["aurora_validation"] = {
            "status": "accepted", "job_id": receipt["job_id"], "base_url": state["base_url"],
            "certificate": str((remote_dir / "certificate.lean").relative_to(ROOT)),
            "certificate_sha256": sha(remote_dir / "certificate.lean"),
            "result": str((remote_dir / "latest.json").relative_to(ROOT)),
            "result_sha256": sha(remote_dir / "latest.json"),
            "request_sha256": remote_audit["request_sha256"],
            "execution_fingerprint": result["execution_fingerprint"],
            "proof_policy_rev": result["proof_policy_rev"], "finished_at": receipt["finished_at"]}
        remote_note = ("2026-09-14: 随后将展平证书的辅助声明放入 submission 命名空间，再次本地核验后提交远端；"
                       "任务 25f7dd0341414b5c83e91957ee920fba 返回 ACCEPTED，缓存关闭，仅提交一次。")
        if remote_note not in entry["notes"]:
            entry["notes"].append(remote_note)
        index["local_formalizations"]["eq18137"]["aurora_status"] = "accepted"
        index["local_formalizations"]["eq18137"]["aurora_job_id"] = receipt["job_id"]
        files.update(str(p.relative_to(ROOT)) for p in remote_dir.iterdir() if p.is_file())
        files.update({"proofs/validation/aurora/README.md",
                      "proofs/validation/eq18137-formal/audit_remote.py",
                      "proofs/validation/eq18137-formal/remote_judge.py",
                      "proofs/validation/eq18137-formal/remote-audit.json"})
    for name in files:
        index["archived_files"][name] = sha(ROOT / name)
    index["updated_on"] = "2026-09-14"
    assert before_others == json.dumps([e for e in index["equations"] if e is not entry], ensure_ascii=False)
    index_path.write_text(json.dumps(index, indent=2, ensure_ascii=False) + "\n")
    print("Recorded Equation18137 only; other equation entries unchanged.")


if __name__ == "__main__":
    main()

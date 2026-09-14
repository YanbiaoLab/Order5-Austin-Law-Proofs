"""Register the checked and accepted Equation27863 dual model only."""
import json
from verify import ROOT, HERE, sha
from audit_remote import audit, REMOTE


def main():
    checked = audit(check_index=False)
    (HERE / "remote-audit.json").write_text(json.dumps(checked, indent=2, ensure_ascii=False) + "\n")
    manifest = HERE / "summary.json"
    summary = json.loads(manifest.read_text())
    receipt = json.loads((REMOTE / "latest.json").read_text())
    state = json.loads((REMOTE / "submission-state.json").read_text())
    remote = receipt["result"]
    index_path = ROOT / "proofs/index.json"
    index = json.loads(index_path.read_text())
    entry = next(e for e in index["equations"] if e["equation"] == "Equation27863")
    others = json.dumps([e for e in index["equations"] if e is not entry], ensure_ascii=False)
    assert entry["formula"] == summary["source_law"] and entry["dual"] == "Equation18137"
    cert = "proofs/Equation27863/InfiniteModel.lean"
    goal = "proofs/Equation27863/JudgeProblem.lean"
    report = "proofs/validation/eq27863-formal/README.md"
    manifest_path = str(manifest.relative_to(ROOT))
    compiled = next(r for r in summary["reports"] if r["module"] == "InfiniteModel")
    entry["infinite_model_proof"] = {
        "path": cert, "sha256": sha(ROOT / cert), "origin": "local_formalization",
        "validation": "local_lean_recompiled_axioms_checked",
        "source": "Opposite of the Equation18137 infinite tree model; full source construction and exact dual transfer included",
        "goal": "Exact Equation27863, nontriviality and an explicit injection from Nat",
        "dependencies": {goal: sha(ROOT / goal)}, "report": report}
    entry["explicit_infinity"] = True
    entry["local_lean_validation"] = "passed_for_local_formalization"
    entry["explicit_infinity_proof"] = {
        "path": cert, "sha256": sha(ROOT / cert), "theorem": "submission.CM.tower_injective",
        "validation": "local_lean_recompiled_axioms_checked"}
    entry["model_compilation"] = {
        "status": "passed", "checked_sha256": sha(ROOT / cert), "version": summary["version"],
        "log": compiled["log"], "log_sha256": compiled["log_sha256"], "axioms": compiled["axioms"],
        "elapsed_seconds": compiled["seconds"],
        "sampled_peak_rss_mib": round(compiled["sampled_peak_rss_bytes"] / 2**20, 2),
        "dependency_manifest": manifest_path}
    entry["aurora_validation"] = {
        "status": "accepted", "job_id": receipt["job_id"], "base_url": state["base_url"],
        "certificate": str((REMOTE / "certificate.lean").relative_to(ROOT)),
        "certificate_sha256": sha(REMOTE / "certificate.lean"),
        "result": str((REMOTE / "latest.json").relative_to(ROOT)),
        "result_sha256": sha(REMOTE / "latest.json"), "request_sha256": checked["request_sha256"],
        "execution_fingerprint": remote["execution_fingerprint"],
        "proof_policy_rev": remote["proof_policy_rev"], "finished_at": receipt["finished_at"]}
    note = ("2026-09-14: 反转 Equation18137 的运算并交换原式后两个变量；独立证书包含完整构造、"
            "精确对偶原式与 Nat 单射。七单元本地核验通过；远端任务 " + receipt["job_id"] + " 返回 ACCEPTED。")
    if note not in entry["notes"]:
        entry["notes"].append(note)
    index.setdefault("local_formalizations", {})["eq27863"] = {
        "status": "passed", "equations": ["Equation27863"], "source_equation": "Equation18137",
        "version": summary["version"], "report": report, "manifest": manifest_path,
        "manifest_sha256": sha(manifest), "aurora_status": "accepted", "aurora_job_id": receipt["job_id"]}
    files = set(summary["source_hashes"])
    files.update(r["log"] for r in summary["reports"])
    files.update(str(p.relative_to(ROOT)) for p in REMOTE.iterdir() if p.is_file())
    files.update(str(p.relative_to(ROOT)) for p in HERE.iterdir() if p.is_file())
    files.update({"proofs/Equation27863/README.md", "proofs/Equation18137/README.md",
                  "proofs/README.md", "proofs/validation/aurora/README.md"})
    for name in files:
        index["archived_files"][name] = sha(ROOT / name)
    index["updated_on"] = "2026-09-14"
    assert others == json.dumps([e for e in index["equations"] if e is not entry], ensure_ascii=False)
    index_path.write_text(json.dumps(index, indent=2, ensure_ascii=False) + "\n")
    print("Recorded Equation27863 and its accepted receipt; other equation entries unchanged.")


if __name__ == "__main__":
    main()

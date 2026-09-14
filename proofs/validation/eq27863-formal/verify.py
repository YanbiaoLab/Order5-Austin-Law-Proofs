"""Fresh serial builds of the dual model and an independent exact-goal certificate."""
import hashlib
import json
import os
from pathlib import Path
import re
import resource
import signal
import subprocess
import sys
import tempfile
import time
from export_certificate import ROOT, MODULES, certificate_text

HERE = Path(__file__).resolve().parent
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
SOURCE_PREFIX = "Equation18137TreeSchema."
DUAL_PREFIX = "Equation27863TreeModel."
EXPECTED = {
    "TreeSchema": {"column_of_step", "column_realized", "target_decompose", "target_of_step",
                   "code_trace_iff", "template_law", "atom_injective"},
    "TreeBounds": {"column_rank", "target_rank", "column_ne_self", "target_not_right",
                   "raw_double_not_target", "target_right_empty"},
    "TreeUnique": {"raw_columns_unique", "raw_target_columns_disjoint", "target_point_unique",
                   "target_inherit_cases", "column_fork_unique", "code_output_unique"},
    "TreeModel": {"column_triangle_free", "step_middle_no_code", "step_outer_no_code", "op_step",
                  "op_hit", "source_law_explicit", "nontrivial", "infinite_model"},
    "DualModel": {"source_law_explicit", "embed_injective", "nontrivial", "infinite_model"},
}


def sha(path):
    digest = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for chunk in iter(lambda: stream.read(65536), b""):
            digest.update(chunk)
    return digest.hexdigest()


def rss(pid):
    with subprocess.Popen(["ps", "-axo", "pid=,ppid=,rss="], stdout=subprocess.PIPE,
                          text=True) as proc:
        rows = [tuple(map(int, line.split())) for line in proc.stdout if line.strip()]
    pids = {pid}
    while True:
        expanded = pids | {p for p, parent, _ in rows if parent in pids}
        if expanded == pids:
            return sum(r * 1024 for p, _, r in rows if p in pids)
        pids = expanded


def compile_one(name, source, build, expected=None):
    output = build / (name + ".olean")
    output.parent.mkdir(parents=True, exist_ok=True)
    log = HERE / "logs" / (name.replace("/", "_") + ".log")
    log.parent.mkdir(exist_ok=True)
    command = ["lean", "+leanprover/lean4:v4.33.1", "-j1", "-M192", "-DwarningAsError=true",
               "-Dlinter.unusedVariables=false", "-Dlinter.defProp=false", "-o", str(output), str(source)]
    start, peak, stop = time.monotonic(), 0, None
    with log.open("w") as stream:
        proc = subprocess.Popen(command, cwd=ROOT, env=dict(os.environ, LEAN_PATH=str(build)),
                                stdout=stream, stderr=subprocess.STDOUT, start_new_session=True)
        try:
            while proc.poll() is None:
                peak = max(peak, rss(proc.pid))
                if peak > 256 * 1024**2:
                    stop = "rss_limit"
                elif time.monotonic() - start > 20:
                    stop = "time_limit"
                if stop:
                    os.killpg(proc.pid, signal.SIGKILL)
                    break
                time.sleep(.05)
            proc.wait()
        finally:
            if proc.poll() is None:
                os.killpg(proc.pid, signal.SIGKILL)
                proc.wait()
    text = log.read_text()
    assert proc.returncode == 0 and stop is None, (name, stop, text[:5000])
    axioms = {n: [] for n in re.findall(r"'([^']+)' does not depend on any axioms", text)}
    for n, values in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text):
        axioms[n] = [v.strip() for v in values.split(",")]
    if expected is not None:
        assert set(axioms) == expected, (name, axioms, expected)
    assert all(set(v) <= ALLOWED for v in axioms.values()), (name, axioms)
    assert "sorryAx" not in text
    high_water = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
    return {"module": name, "source": str(source.relative_to(ROOT)), "source_sha256": sha(source),
            "status": "passed", "axioms": axioms, "command": command,
            "log": str(log.relative_to(ROOT)), "log_sha256": sha(log),
            "seconds": time.monotonic() - start, "sampled_peak_rss_bytes": peak,
            "cumulative_child_high_water_bytes": high_water if sys.platform == "darwin" else high_water * 1024,
            "rss_limit_mib": 256, "lean_internal_memory_mib": 192, "seconds_limit": 20}


def main():
    certificate = ROOT / "proofs/Equation27863/InfiniteModel.lean"
    assert certificate.read_text() == certificate_text(), "Regenerate the certificate first"
    parent = ROOT / ".build"
    parent.mkdir(exist_ok=True)
    reports = []
    with tempfile.TemporaryDirectory(prefix="27863-modules-", dir=parent) as td:
        build = Path(td)
        for name, path in MODULES:
            prefix = DUAL_PREFIX if name == "DualModel" else SOURCE_PREFIX
            reports.append(compile_one(name, ROOT / path, build, {prefix + n for n in EXPECTED[name]}))
    with tempfile.TemporaryDirectory(prefix="27863-certificate-", dir=parent) as td:
        build = Path(td)
        reports.append(compile_one("JudgeProblem", ROOT / "proofs/Equation27863/JudgeProblem.lean", build, set()))
        reports.append(compile_one("InfiniteModel", certificate, build,
                                   {"submission", "submission.CM.tower_injective", "submission." + DUAL_PREFIX + "infinite_model"}))
    sources = {r["source"]: r["source_sha256"] for r in reports}
    for path in [HERE / "verify.py", HERE / "export_certificate.py"]:
        sources[str(path.relative_to(ROOT))] = sha(path)
    summary = {"status": "passed", "equations": ["Equation27863"], "source_equation": "Equation18137",
               "version": "4.33.1", "fresh_directories": 2, "modules_checked": 7,
               "source_law": "x = ((y ◇ (y ◇ x)) ◇ y) ◇ (x ◇ z)",
               "operation": "dualOp(a,b) = Equation18137.op(b,a)",
               "classification": "nontrivial_infinite_model", "explicit_infinity": True,
               "reports": reports, "source_hashes": sources,
               "remote_judge": "not_run_by_this_local_verifier"}
    (HERE / "summary.json").write_text(json.dumps(summary, indent=2, ensure_ascii=False) + "\n")
    print("PASS: seven units in two clean builds; exact Equation27863, nontriviality and Nat injection.")


if __name__ == "__main__":
    main()

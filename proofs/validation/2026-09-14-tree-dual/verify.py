"""Read-only inventory, source-hash and accepted-certificate audit for this batch."""
from collections import Counter
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[3]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
JOBS = {18137: "25f7dd0341414b5c83e91957ee920fba", 27863: "c57824e679ec4461b923a5237bdfcd56"}


def sha(path):
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(65536), b""):
            h.update(chunk)
    return h.hexdigest()


def read(path):
    return json.loads((ROOT / path).read_text())


def links(path):
    for target in re.findall(r"\]\(([^)]+)\)", path.read_text()):
        if "://" not in target and not target.startswith("#"):
            assert (path.parent / target.split("#")[0]).is_file(), (path, target)


def check_record(value):
    if isinstance(value, list):
        for item in value:
            check_record(item)
    elif isinstance(value, dict):
        if value.get("path") and value.get("sha256"):
            assert sha(ROOT / value["path"]) == value["sha256"], value["path"]
        for key, item in value.items():
            if key == "dependencies" and isinstance(item, dict):
                for path, digest in item.items():
                    assert sha(ROOT / path) == digest, path
            elif isinstance(item, str) and item.startswith("proofs/"):
                assert (ROOT / item).exists(), item
                if value.get(key + "_sha256"):
                    assert sha(ROOT / item) == value[key + "_sha256"], item
            else:
                check_record(item)


def main():
    index = read("proofs/index.json")
    rows = {e["equation"]: e for e in index["equations"]}
    assert len(rows) == len(index["equations"]) == 130
    assert Counter(e["table"] for e in rows.values()) == {"20.1": 10, "20.2": 96, "20.3": 24}
    for e in rows.values():
        assert rows[e["dual"]]["dual"] == e["equation"]
        assert rows[e["dual"]]["table"] == e["table"]
        assert not (e.get("unrestricted_triviality_proof") and e["infinite_model_proof"])
        check_record(e)
    for path, digest in index["archived_files"].items():
        assert sha(ROOT / path) == digest, path

    counts = [sum(bool(e.get(key)) for e in rows.values()) for key in
              ["finite_proof", "infinite_model_proof", "explicit_infinity", "unrestricted_triviality_proof"]]
    assert counts == [120, 116, 88, 2], counts
    assert sum(bool(e["finite_proof"] and e["infinite_model_proof"]) for e in rows.values()) == 108
    finite_open = {e["equation"] for e in rows.values() if not e["finite_proof"]}
    infinite_open = {e["equation"] for e in rows.values()
                     if not e["infinite_model_proof"] and not e.get("unrestricted_triviality_proof")}
    assert len(finite_open) == 10 and len(infinite_open) == 12

    for number, job_id in JOBS.items():
        name = f"Equation{number}"
        folder = f"proofs/validation/aurora/{name}"
        local = f"proofs/validation/eq{number}-formal"
        manifest = read(f"{local}/summary.json")
        assert manifest["status"] == "passed"
        assert manifest["modules_checked"] == (6 if number == 18137 else 7)
        assert manifest["fresh_directories"] == 2 and manifest["version"] == "4.33.1"
        for path, digest in manifest["source_hashes"].items():
            assert path.startswith("proofs/") and sha(ROOT / path) == digest, path
        for report in manifest["reports"]:
            assert report["status"] == "passed"
            assert sha(ROOT / report["log"]) == report["log_sha256"]
            assert all(set(a) <= ALLOWED for a in report["axioms"].values())
        source = (ROOT / f"proofs/{name}/InfiniteModel.lean").read_bytes()
        payload = read(f"{folder}/request.json")
        receipt = read(f"{folder}/latest.json")
        state = read(f"{folder}/submission-state.json")
        job = read(f"{folder}/job.json")
        assert source == (ROOT / f"{folder}/certificate.lean").read_bytes() == payload["code"].encode()
        assert hashlib.sha256(source).hexdigest() == state["certificate_sha256"]
        assert state["request_sha256"] == hashlib.sha256(
            json.dumps(payload, sort_keys=True, ensure_ascii=False).encode()).hexdigest()
        assert state["phase"] == "terminal" and state["post_attempts"] == 1
        assert receipt["job_id"] == state["job_id"] == job["job_id"] == job_id
        assert receipt["status"] == "done" and receipt["error"] is None
        result = receipt["result"]
        assert result["status"] == "accepted" and result["error_code"] == "ACCEPTED"
        assert result["verdict"] == payload["verdict"] == "false"
        assert set(result["axioms"]) <= ALLOWED and payload["cache_mode"] == "off"
        assert payload["problem"]["eq1_id"] == number and payload["problem"]["eq2_id"] == 2
        assert payload["problem"]["equation1"] == rows[name]["formula"] == manifest["source_law"]
        assert payload["problem"]["equation2"] == "x = y"
        assert rows[name]["explicit_infinity"] and rows[name]["aurora_validation"]["job_id"] == job_id
        assert index["local_formalizations"][f"eq{number}"]["manifest_sha256"] == sha(ROOT / local / "summary.json")
        assert not re.search(rb"\b(sorry|admit|sorryAx|unsafe|native_decide)\b", source)
        for path in [ROOT / f"proofs/{name}/README.md", ROOT / local / "README.md", ROOT / folder / "README.md"]:
            links(path)

    for filename in ["README.md", "README.zh-CN.md"]:
        path = ROOT / filename
        links(path)
        text = path.read_text()
        details = [line for line in text.splitlines() if line.startswith("| [Equation")]
        assert len(details) == 130
        for line, e in zip(details, rows.values()):
            cells = [v.strip() for v in line.strip("|").split("|")]
            assert f'[{e["equation"]}]' in cells[0] and cells[1] == e["dual"] and cells[2] == e["table"]
            for column, key in [(4, "finite_proof"), (6, "infinite_model_proof")]:
                proof = e[key]
                assert (f'({proof["path"]})' in cells[column]) if proof else (".lean)" not in cells[column])
        for line in text.splitlines():
            if re.match(r"^\| (?:20\.[123]|\*\*(?:Total|合计)\*\*) \|", line):
                cells = [v.strip(" *") for v in line.strip("|").split("|")]
                subset = list(rows.values()) if cells[0] in {"Total", "合计"} else [e for e in rows.values() if e["table"] == cells[0]]
                assert list(map(int, cells[1:])) == [len(subset), sum(not e["finite_proof"] for e in subset),
                    sum(bool(e["infinite_model_proof"]) for e in subset),
                    sum(bool(e.get("unrestricted_triviality_proof")) for e in subset),
                    sum(e["equation"] in infinite_open for e in subset)]
        current = text.split("<!-- current-proof-status:start -->")[1].split("<!-- current-proof-status:end -->")[0]
        open_lines = [line for line in current.splitlines() if line.startswith("- **")]
        assert len(open_lines) == 2
        assert set(re.findall(r"\[(Equation\d+)\]", open_lines[0])) == finite_open
        assert set(re.findall(r"\[(Equation\d+)\]", open_lines[1])) == infinite_open
    links(Path(__file__).with_name("README.md"))
    links(ROOT / "proofs/Equation18137/MODEL.zh-CN.md")
    print(f"PASS: 130 equations, {len(index['archived_files'])} archived hashes, both accepted certificates, and bilingual README.")
    print("PASS: 120 finite / 116 models / 88 explicit infinity / 108 both / 2 exclusions; 10 finite and 12 infinite open.")


if __name__ == "__main__":
    main()

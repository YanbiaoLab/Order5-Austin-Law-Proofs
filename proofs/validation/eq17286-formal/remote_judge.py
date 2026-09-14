"""Submit the checked Equation17286/Equation28626 certificate once; resume by durable job ID.

--submit posts only if no submission state exists. --wait observes that same
job through the documented long-poll endpoint. A lost POST response is never
retried automatically. Only the exact checked source certificate is sent.
"""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import urllib.parse
import urllib.request
from verify import ROOT, HERE, sha
from audit import audit

BASE = "http://10.220.69.172:8900"
TERMINAL = {"done", "failed", "cancelled"}


def save(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_name(path.name + ".tmp")
    with tmp.open("w") as stream:
        json.dump(data, stream, indent=2, ensure_ascii=False)
        stream.write("\n")
        stream.flush()
        os.fsync(stream.fileno())
    tmp.replace(path)


def request(route, payload=None, timeout=40):
    data = None if payload is None else json.dumps(payload, ensure_ascii=False).encode()
    req = urllib.request.Request(BASE + route, data=data, headers={"Content-Type": "application/json"})
    with urllib.request.urlopen(req, timeout=timeout) as response:
        raw = response.read(2 * 1024 * 1024 + 1)
    assert len(raw) <= 2 * 1024 * 1024, "Unexpectedly large response"
    return json.loads(raw)


def prepared_request(number):
    manifest = audit(check_index=False)
    equation = next(e for e in json.loads((ROOT / "proofs/index.json").read_text())["equations"]
                    if e["equation"] == f"Equation{number}")
    assert equation["formula"] == manifest["source_laws"][str(number)]
    source = ROOT / f"proofs/Equation{number}/InfiniteModel.lean"
    payload = {"problem": {"id": f"order5-Equation{number}-to-Equation2", "eq1_id": number, "eq2_id": 2,
                           "equation1": equation["formula"], "equation2": "x = y"},
               "verdict": "false", "code": source.read_text(), "timeout_seconds": 300, "cache_mode": "off"}
    digest = hashlib.sha256(json.dumps(payload, sort_keys=True, ensure_ascii=False).encode()).hexdigest()
    return source, payload, digest


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("equation", type=int, choices=(17286, 28626))
    parser.add_argument("--submit", action="store_true")
    parser.add_argument("--wait", action="store_true")
    args = parser.parse_args()
    OUT = ROOT / f"proofs/validation/aurora/Equation{args.equation}"
    source, payload, digest = prepared_request(args.equation)
    state_path = OUT / "submission-state.json"
    if state_path.exists():
        state = json.loads(state_path.read_text())
        assert state["request_sha256"] == digest and state["base_url"] == BASE
        assert state.get("job_id"), "Prior POST outcome uncertain: resolve it before any retry"
    elif args.submit:
        health = request("/health")
        assert health["status"] == "ok" and any(b.get("healthy") for b in health.get("backends", []))
        save(OUT / "health-at-submission.json", health)
        save(OUT / "request.json", payload)
        (OUT / "certificate.lean").write_bytes(source.read_bytes())
        state = {"base_url": BASE, "request_sha256": digest, "certificate_sha256": sha(source),
                 "phase": "posting", "post_attempts": 1,
                 "submitted_at": datetime.datetime.now(datetime.timezone.utc).isoformat()}
        save(state_path, state)
        try:
            job = request("/jobs", payload=payload, timeout=20)
            state.update(job_id=job["job_id"], phase="observing")
            save(OUT / "job.json", job)
            save(state_path, state)
        except Exception as error:
            state.update(phase="post_outcome_uncertain", error=str(error))
            save(state_path, state)
            raise
    else:
        raise SystemExit("No existing submission; use --submit after inspecting the checked certificate")
    route = "/jobs/" + urllib.parse.quote(state["job_id"], safe="")
    if args.wait:
        route += "/wait?timeout_seconds=30"
    job = request(route)
    assert job["job_id"] == state["job_id"]
    save(OUT / "latest.json", job)
    state.update(phase="terminal" if job["status"] in TERMINAL else "observing",
                 last_status=job["status"], last_observed_at=datetime.datetime.now(datetime.timezone.utc).isoformat())
    save(state_path, state)
    result = job.get("result") or {}
    print(json.dumps({"job_id": job["job_id"], "status": job["status"],
                      "result_status": result.get("status"), "error_code": result.get("error_code"),
                      "message": result.get("message"), "certificate_sha256": state["certificate_sha256"]},
                     ensure_ascii=False))
    if result:
        print(json.dumps(result, ensure_ascii=False)[:12000])


if __name__ == "__main__":
    main()

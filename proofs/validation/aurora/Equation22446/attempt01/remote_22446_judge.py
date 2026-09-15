"""Submit the verified E22446 export once and resume its durable remote Judge job."""
import argparse
import datetime
import hashlib
import json
import os
import urllib.parse
import urllib.request

from check_22446_judge_export import audit_export
from check_22446_infinite_model import sha
from export_22446_judge import ROOT, DEST

BASE = 'http://10.220.69.172:8900'
OUT = ROOT/'proofs/validation/aurora/Equation22446'


def save(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name+'.tmp')
    with temporary.open('w') as stream:
        json.dump(data, stream, ensure_ascii=False, indent=2)
        stream.write('\n')
        stream.flush()
        os.fsync(stream.fileno())
    temporary.replace(path)


def request(route, payload=None, timeout=35):
    body = None if payload is None else json.dumps(payload, ensure_ascii=False).encode()
    req = urllib.request.Request(BASE+route, data=body,
                                 headers={'Content-Type': 'application/json'})
    opener = urllib.request.build_opener(urllib.request.ProxyHandler({}))
    with opener.open(req, timeout=timeout) as response:
        raw = response.read(2*1024*1024+1)
    assert len(raw) <= 2*1024*1024, 'Unexpectedly large remote response'
    return json.loads(raw)


def prepared_request():
    audit_export()
    entry = next(e for e in json.loads((ROOT/'proofs/index.json').read_text())['equations']
                 if e['equation'] == 'Equation22446')
    assert entry['formula'] == 'x = (y ◇ (x ◇ x)) ◇ ((x ◇ z) ◇ z)'
    payload = dict(problem=dict(id='order5-Equation22446-to-Equation2', eq1_id=22446, eq2_id=2,
        equation1=entry['formula'], equation2='x = y'), verdict='false',
        code=DEST.read_text(), timeout_seconds=300, cache_mode='off')
    digest = hashlib.sha256(json.dumps(payload, sort_keys=True, ensure_ascii=False).encode()).hexdigest()
    return payload, digest


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--submit', action='store_true')
    parser.add_argument('--wait', action='store_true')
    args = parser.parse_args()
    payload, digest = prepared_request()
    state_path = OUT/'submission-state.json'
    if state_path.exists():
        state = json.loads(state_path.read_text())
        assert state['request_sha256'] == digest and state['base_url'] == BASE
        assert state.get('job_id'), 'Previous POST outcome uncertain; do not submit again'
    elif args.submit:
        assert not (OUT/'job.json').exists(), 'Existing job record must be resolved first'
        health = request('/health', timeout=15)
        assert health['status'] == 'ok' and any(b.get('healthy') for b in health['backends'])
        save(OUT/'health-at-submission.json', health)
        save(OUT/'request.json', payload)
        (OUT/'certificate.lean').write_bytes(DEST.read_bytes())
        state = dict(base_url=BASE, equation='Equation22446', certificate=str(DEST.relative_to(ROOT)),
            certificate_sha256=sha(DEST), request_sha256=digest, phase='posting', post_attempts=1,
            submitted_at=datetime.datetime.now(datetime.timezone.utc).isoformat())
        save(state_path, state)
        try:
            job = request('/jobs', payload, timeout=20)
            state.update(job_id=job['job_id'], phase='observing')
            save(OUT/'job.json', job)
            save(state_path, state)
        except Exception as error:
            state.update(phase='post_outcome_uncertain', error=str(error))
            save(state_path, state)
            raise
    else:
        raise SystemExit('No recorded submission; use --submit')
    route = '/jobs/'+urllib.parse.quote(state['job_id'], safe='')
    if args.wait:
        route += '/wait?timeout_seconds=25'
    receipt = request(route)
    assert receipt['job_id'] == state['job_id']
    save(OUT/'latest.json', receipt)
    state.update(phase='terminal' if receipt['status'] in {'done', 'failed', 'cancelled'} else 'observing',
        last_status=receipt['status'], last_observed_at=datetime.datetime.now(datetime.timezone.utc).isoformat())
    save(state_path, state)
    result = receipt.get('result') or {}
    print(json.dumps(dict(job_id=state['job_id'], status=receipt['status'],
        result_status=result.get('status'), error_code=result.get('error_code'),
        message=result.get('message'), elapsed_ms=result.get('elapsed_ms'),
        certificate_sha256=state['certificate_sha256']), ensure_ascii=False))
    if result:
        print(json.dumps({k: v for k, v in result.items()
            if k not in {'stdout', 'stderr', 'direct_declarations', 'code'}}, ensure_ascii=False)[:6000])
        if result.get('status') != 'accepted':
            print(result.get('stdout', '')[-6000:])
            print(result.get('stderr', '')[-2000:])


if __name__ == '__main__':
    main()

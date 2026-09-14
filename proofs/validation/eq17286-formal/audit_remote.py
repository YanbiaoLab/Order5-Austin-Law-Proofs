"""Read-only audit of both accepted submissions against current local evidence."""
import argparse
import hashlib
import json
from audit import audit as local_audit
from verify import ROOT, HERE, ALLOWED, sha

NUMBERS = (17286, 28626)


def audit(check_index=True):
    local = local_audit(check_index=check_index)
    index = json.loads((ROOT / 'proofs/index.json').read_text())
    results = []
    for number in NUMBERS:
        equation = f'Equation{number}'
        out = ROOT / 'proofs/validation/aurora' / equation
        source = ROOT / 'proofs' / equation / 'InfiniteModel.lean'
        payload = json.loads((out / 'request.json').read_text())
        state = json.loads((out / 'submission-state.json').read_text())
        job = json.loads((out / 'job.json').read_text())
        receipt = json.loads((out / 'latest.json').read_text())
        assert source.read_bytes() == (out / 'certificate.lean').read_bytes() == payload['code'].encode()
        digest = hashlib.sha256(json.dumps(payload, sort_keys=True, ensure_ascii=False).encode()).hexdigest()
        assert state['request_sha256'] == digest
        assert state['certificate_sha256'] == sha(source)
        assert state['base_url'] == 'http://10.220.69.172:8900'
        assert state['post_attempts'] == 1 and state['phase'] == 'terminal'
        assert state['last_status'] == receipt['status'] == 'done'
        assert state['job_id'] == job['job_id'] == receipt['job_id']
        assert receipt['error'] is None and receipt['attempts'] == 1
        result = receipt['result']
        assert result['status'] == 'accepted' and result['error_code'] == 'ACCEPTED'
        assert result['verdict'] == payload['verdict'] == 'false'
        assert set(result['axioms']) <= ALLOWED
        assert payload['cache_mode'] == 'off' and payload['timeout_seconds'] == 300
        assert payload['problem'] == dict(id=f'order5-{equation}-to-Equation2',
            eq1_id=number, eq2_id=2, equation1=local['source_laws'][str(number)], equation2='x = y')
        entry = next(e for e in index['equations'] if e['equation'] == equation)
        assert entry['formula'] == payload['problem']['equation1']
        if check_index:
            remote = entry['aurora_validation']
            assert remote['status'] == 'accepted' and remote['job_id'] == receipt['job_id']
            assert remote['certificate_sha256'] == sha(source)
            assert remote['result_sha256'] == sha(out / 'latest.json')
            assert remote['request_sha256'] == digest
            formalization = index['local_formalizations']['eq17286']
            assert formalization['remote_judge_status'] == 'accepted'
            assert formalization['remote_job_ids'][equation] == receipt['job_id']
            for p in out.iterdir():
                if p.is_file():
                    assert index['archived_files'][str(p.relative_to(ROOT))] == sha(p)
        results.append(dict(equation=equation, status='passed', remote_status=result['status'],
            error_code=result['error_code'], remote_job_id=receipt['job_id'],
            certificate_sha256=sha(source), request_sha256=digest,
            local_manifest_sha256=sha(HERE / 'summary.json'), local_units_checked=8,
            receipt=str((out / 'latest.json').relative_to(ROOT)),
            receipt_sha256=sha(out / 'latest.json'), elapsed_ms=result['elapsed_ms'],
            cache_mode=payload['cache_mode'], post_attempts=state['post_attempts'],
            backend_attempts=receipt['attempts'], remote_axioms=result['axioms']))
    return dict(status='passed', equations=results,
        scope='Exact equations, current certificate bytes, local builds, accepted remote receipts and optional index binding')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--without-index', action='store_true')
    args = parser.parse_args()
    print(json.dumps(audit(check_index=not args.without_index), ensure_ascii=False, indent=2))

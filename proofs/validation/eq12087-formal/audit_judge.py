"""Bind standalone checks, exact submitted bytes and actual Judge receipts."""
import hashlib
import json
from pathlib import Path
from verify import ROOT, HERE, ALLOWED, sha
from export_judge import certificate_text, certificate_parts
from audit import audit as audit_core


def local_audit():
    core = audit_core()
    manifest = HERE / 'judge-local/summary.json'
    local = json.loads(manifest.read_text())
    assert local['status'] == 'passed' and not local['reused_olean_files']
    assert len(local['reports']) == 129
    assert local['validation_mode'] == 'exact_export_bodies_checked_in_segments'
    assert local['monolithic_local_pass'] is False
    for name, digest in local['source_hashes'].items():
        assert sha(ROOT / name) == digest, name
    for unit in local['reports']:
        assert unit['status'] == 'passed' and unit['exit_code'] == 0
        assert sha(ROOT / unit['source']) == unit['sha256']
        assert sha(ROOT / unit['log']) == unit['log_sha256']
        assert sha(Path(unit['command'][unit['command'].index('-o') + 1])) == unit['olean_sha256']
        assert '-j1' in unit['command']
        assert '-M256' in unit['command']
        assert unit['memory_limit_mib'] == 256 and unit['rss_limit_mib'] == 384
        assert unit['peak_rss_mib'] <= unit['rss_limit_mib']
        assert all(set(v) <= ALLOWED for v in unit['axioms'].values())
    for eq in core['equations']:
        assert (ROOT / 'proofs' / eq / 'JudgeSubmission.lean').read_text() == certificate_text(eq)
        imports, sections, wrapper = certificate_parts(eq)
        common = [i for i in imports if i != 'import JudgeProblem']
        previous = None
        for name, body in sections:
            stem = 'Judge' + name
            header = 'prelude\n' + '\n'.join(common) + '\n'
            if previous:
                header += 'import ' + previous + '\n'
            assert (HERE / 'judge-local/parts' / (stem + '.lean')).read_text() == header + 'set_option Elab.async false\n' + body + '\n'
            previous = stem
        unit = next(r for r in local['reports'] if r['module'] == eq + '-JudgeSubmission-Export')
        assert (ROOT / unit['source']).read_text() == ('prelude\nimport JudgeProblem\nimport ' + previous
            + '\nset_option Elab.async false\n' + wrapper + '\n')
        assert {'submission', 'submission.source_law', 'submission.CM.tower_injective'} <= set(unit['axioms'])
    return local


def remote_audit(eq, check_index=True):
    local_audit()
    out = ROOT / 'proofs/validation/aurora' / eq
    source = ROOT / 'proofs' / eq / 'JudgeSubmission.lean'
    payload = json.loads((out / 'request.json').read_text())
    state = json.loads((out / 'submission-state.json').read_text())
    job = json.loads((out / 'job.json').read_text())
    receipt = json.loads((out / 'latest.json').read_text())
    assert source.read_bytes() == (out / 'certificate.lean').read_bytes() == payload['code'].encode()
    digest = hashlib.sha256(json.dumps(payload, sort_keys=True, ensure_ascii=False).encode()).hexdigest()
    assert state['request_sha256'] == digest and state['certificate_sha256'] == sha(source)
    assert state['post_attempts'] == 1 and state['phase'] == 'terminal'
    if eq == 'Equation12087':
        prior = out / 'attempt01'
        old_request = json.loads((prior / 'request.json').read_text())
        old_state = json.loads((prior / 'submission-state.json').read_text())
        old_receipt = json.loads((prior / 'latest.json').read_text())
        assert old_request['code'].encode() == (prior / 'certificate.lean').read_bytes()
        assert old_state['certificate_sha256'] == sha(prior / 'certificate.lean')
        assert old_state['request_sha256'] == hashlib.sha256(json.dumps(old_request, sort_keys=True, ensure_ascii=False).encode()).hexdigest()
        assert old_state['job_id'] == old_receipt['job_id']
        assert old_receipt['status'] == 'done'
        assert old_receipt['result']['error_code'] == 'DISALLOWED_DECLARATIONS'
        assert old_state['job_id'] != state['job_id']
    assert state['job_id'] == job['job_id'] == receipt['job_id']
    assert receipt['status'] == 'done' and receipt['error'] is None
    result = receipt['result']
    assert result['status'] == 'accepted' and result['error_code'] == 'ACCEPTED'
    assert result['verdict'] == payload['verdict'] == 'false'
    assert set(result['axioms']) <= ALLOWED and payload['cache_mode'] == 'off'
    index = json.loads((ROOT / 'proofs/index.json').read_text())
    entry = next(e for e in index['equations'] if e['equation'] == eq)
    assert payload['problem'] == dict(id='order5-' + eq + '-to-Equation2',
        eq1_id=int(eq.removeprefix('Equation')), eq2_id=2,
        equation1=entry['formula'], equation2='x = y')
    if check_index:
        remote = entry['aurora_validation']
        assert remote['status'] == 'accepted' and remote['job_id'] == receipt['job_id']
        assert remote['certificate_sha256'] == sha(source)
        assert remote['result_sha256'] == sha(out / 'latest.json')
        assert remote['request_sha256'] == digest
    return dict(status='passed', equation=eq, remote_status=result['status'],
        error_code=result['error_code'], remote_job_id=receipt['job_id'],
        elapsed_ms=result['elapsed_ms'], remote_axioms=result['axioms'],
        certificate_sha256=sha(source), request_sha256=digest,
        receipt=str((out / 'latest.json').relative_to(ROOT)), receipt_sha256=sha(out / 'latest.json'),
        local_manifest_sha256=sha(HERE / 'judge-local/summary.json'),
        core_manifest_sha256=sha(HERE / 'summary.json'), post_attempts=1,
        certificate_versions_submitted=2 if eq == 'Equation12087' else 1, cache_mode='off')


if __name__ == '__main__':
    for eq in ('Equation12087', 'Equation33884'):
        result = remote_audit(eq)
        (HERE / (eq + '-remote-audit.json')).write_text(json.dumps(result, indent=2) + '\n')
        print(json.dumps(result))

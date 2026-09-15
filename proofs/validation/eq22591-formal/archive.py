"""Read-only audit of E22591 proof, Judge receipt, finite evidence and publication inventory."""
import json
import re
import subprocess

from export import HERE, ROOT, sha
from verify import ALLOWED, ENDPOINTS, audit_remote, load


def check_links(path):
    for value in re.findall(r'\]\(([^)]+)\)', path.read_text()):
        if '://' in value or value.startswith('#'):
            continue
        target = (path.parent/value.split('#')[0]).resolve()
        if not target.exists():
            result = subprocess.run(['git', 'cat-file', '-e', 'HEAD:'+str(target.relative_to(ROOT))],
                                    cwd=ROOT, capture_output=True)
            assert result.returncode == 0, (path, value)


def verify():
    manifest = load(HERE/'archive-manifest.json')
    assert manifest['equation'] == 'Equation22591' and manifest['status'] == 'passed'
    for p, digest in manifest['files'].items():
        assert sha(ROOT/p) == digest, p
    receipt = audit_remote()
    assert manifest['remote_job_id'] == receipt['job_id']
    summary = load(HERE/'summary.json')
    assert summary['nontriviality_proved'] and summary['fresh_empty_build']
    assert not summary['reused_olean_files'] and summary['temporary_build_removed']
    assert (summary['core_modules'], summary['additional_export_modules'],
            summary['total_compilations']) == (58, 56, 114)
    for record in summary['results']:
        assert sha(ROOT/record['source']) == record['sha256']
        assert summary['source_hashes'][record['source']] == record['sha256']
    index = load(ROOT/'proofs/index.json')
    rows = index['equations']
    entry = next(r for r in rows if r['equation'] == 'Equation22591')
    request = load(ROOT/'proofs/validation/aurora/Equation22591/request.json')
    assert entry['formula'] == request['problem']['equation1'] and entry['dual'] == 'Equation22446'
    model = summary['results'][57]
    proof = entry['infinite_model_proof']
    assert proof['path'] == model['source'] and proof['sha256'] == model['sha256']
    assert proof['dependencies'] == {r['source']: r['sha256'] for r in summary['results'][:57]}
    compiled = entry['model_compilation']
    assert compiled['status'] == 'passed' and compiled['checked_sha256'] == model['sha256']
    assert compiled['log'] == model['log'] and compiled['log_sha256'] == model['log_sha256']
    assert compiled['axioms'] == model['axioms'] and set(compiled['axioms']) == ENDPOINTS
    assert entry['explicit_infinity'] and entry['explicit_infinity_proof'] == dict(
        path=model['source'], sha256=model['sha256'], theorem='submission.CM.tower_injective',
        validation='local_lean_recompiled_axioms_checked')
    remote = entry['aurora_validation']
    assert remote['status'] == 'accepted' and remote['job_id'] == receipt['job_id']
    for field in ['certificate', 'result']:
        assert sha(ROOT/remote[field]) == remote[field+'_sha256']
    assert remote['certificate_sha256'] == summary['certificate_sha256']
    state = load(ROOT/'proofs/validation/aurora/Equation22591/submission-state.json')
    assert remote['request_sha256'] == state['request_sha256']
    for field in ['execution_fingerprint', 'proof_policy_rev']:
        assert remote[field] == receipt['result'][field]
    finite, prior = entry['finite_proof'], entry['finite_compilation']
    record = load(ROOT/prior['validation_record'])
    assert record['status'] == 'passed' and record['proves_unconditional_finite_equation2']
    assert sha(ROOT/finite['path']) == finite['sha256'] == prior['checked_sha256'] == record['source_sha256']
    assert sha(ROOT/prior['log']) == prior['log_sha256'] == record['log_sha256']
    assert record['theorem'] == finite['theorem'] == 'finite_trivial_dual'
    assert set(record['axioms']) <= ALLOWED
    excluded = lambda r: bool(r.get('unrestricted_triviality_proof') or r.get('universal_triviality_proof'))
    pending = {r['equation'] for r in rows if not r['infinite_model_proof'] and not excluded(r)}
    for name in ['README.md', 'README.zh-CN.md']:
        path = ROOT/name
        lines = path.read_text().splitlines()
        row = next(line for line in lines if line.startswith('| [Equation22591]'))
        assert '(proofs/Equation22591/InfiniteModel.lean)' in row and 'Judge' in row
        listing = next(line for line in lines if line.startswith(('- **Infinite-model certificates pending', '- **无限侧待补模型证书')))
        assert set(re.findall(r'\[(Equation\d+)\]', listing)) == pending
        for line in lines:
            if re.match(r'^\| (?:20\.[123]|\*\*(?:Total|合计)\*\*) \|', line):
                cells = [s.strip().strip('*') for s in line.strip('|').split('|')]
                group = rows if cells[0] in {'Total', '合计'} else [r for r in rows if r['table'] == cells[0]]
                expected = [len(group), sum(not r['finite_proof'] for r in group),
                    sum(bool(r['infinite_model_proof']) for r in group), sum(excluded(r) for r in group),
                    sum(not r['infinite_model_proof'] and not excluded(r) for r in group)]
                assert list(map(int, cells[1:])) == expected, (name, line)
        check_links(path)
    for name in manifest['documents']:
        check_links(ROOT/name)
    for name in ['README.md', 'README.zh-CN.md', 'proofs/README.md',
                 'proofs/Equation22446/README.md', 'proofs/Equation22591/README.md']:
        assert index['archived_files'][name] == sha(ROOT/name), name
    print(json.dumps(dict(status='passed', archived_files=len(manifest['files']),
        compilations=114, job_id=receipt['job_id'], remote_status='ACCEPTED',
        model_certificates=sum(bool(r['infinite_model_proof']) for r in rows),
        explicit_infinity=sum(bool(r['explicit_infinity']) for r in rows),
        pending_infinite_certificates=len(pending))))


if __name__ == '__main__':
    verify()

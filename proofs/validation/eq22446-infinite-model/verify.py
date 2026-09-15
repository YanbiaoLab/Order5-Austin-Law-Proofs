"""Read-only audit of the E22446 publication, exact Judge receipts and README inventory."""
import hashlib
import json
from pathlib import Path
import re
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def sha(path):
    digest = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(65536), b''):
            digest.update(block)
    return digest.hexdigest()


def load(path):
    return json.loads(path.read_text())


def check_links(path):
    for value in re.findall(r'\]\(([^)]+)\)', path.read_text()):
        if '://' in value or value.startswith('#'):
            continue
        target = (path.parent/value.split('#')[0]).resolve()
        if not target.exists():
            # Also support a sparse Git worktree without checking out unrelated proofs.
            result = subprocess.run(['git', 'cat-file', '-e', 'HEAD:'+str(target.relative_to(ROOT))],
                                    cwd=ROOT, capture_output=True)
            assert result.returncode == 0, (path, value)


def verify():
    manifest = load(HERE/'archive-manifest.json')
    for p, h in manifest['files'].items():
        assert sha(ROOT/p) == h, p
    core = load(HERE/'summary.json')
    assert core['status'] == 'passed' and core['model_proved']
    assert core['modules'] == 58 and core['remaining_source_obligations'] == []
    for result in core['results']:
        assert result['status'] == 'passed'
        assert sha(ROOT/result['source']) == result['sha256']
        assert sha(ROOT/result['log']) == result['log_sha256']
        assert all(set(a) <= ALLOWED for a in result['axioms'].values())
    export_dir = HERE.parent/'eq22446-judge-export-v2'
    export = load(export_dir/'summary.json')
    assert export['status'] == 'passed' and len(export['results']) == 58
    for p, h in export['source_hashes'].items():
        path = export_dir/'provenance'/Path(p).name if p.startswith('scripts/') else ROOT/p
        assert sha(path) == h, p
    for result in export['results']:
        assert result['status'] == 'passed'
        assert sha(ROOT/result['source']) == result['sha256']
        assert sha(ROOT/result['log']) == result['log_sha256']
        assert all(set(a) <= ALLOWED for a in result['axioms'].values())
    assert export['results'][-1]['axioms']['submission.CM.tower_injective'] == []
    remote = HERE.parent/'aurora/Equation22446'
    request, receipt, state = [load(remote/name) for name in
        ['request.json', 'latest.json', 'submission-state.json']]
    code = (ROOT/'proofs/Equation22446/JudgeSubmission.lean').read_bytes()
    assert code == (remote/'certificate.lean').read_bytes() == request['code'].encode()
    assert sha(remote/'certificate.lean') == state['certificate_sha256']
    assert state['request_sha256'] == hashlib.sha256(
        json.dumps(request, sort_keys=True, ensure_ascii=False).encode()).hexdigest()
    assert receipt['job_id'] == state['job_id'] == load(remote/'job.json')['job_id']
    assert receipt['status'] == 'done' and receipt['result']['status'] == 'accepted'
    assert receipt['result']['error_code'] == 'ACCEPTED'
    assert request['verdict'] == receipt['result']['verdict'] == 'false'
    assert request['cache_mode'] == 'off' and set(receipt['result']['axioms']) <= ALLOWED
    data = load(ROOT/'proofs/index.json')
    rows = data['equations']
    entry = next(r for r in rows if r['equation'] == 'Equation22446')
    assert request['problem'] == dict(id='order5-Equation22446-to-Equation2',
        eq1_id=22446, eq2_id=2, equation1=entry['formula'], equation2='x = y')
    assert entry['aurora_validation']['job_id'] == receipt['job_id']
    for field in ['certificate', 'result']:
        assert sha(ROOT/entry['aurora_validation'][field]) == entry['aurora_validation'][field+'_sha256']
    for p, h in entry['infinite_model_proof']['dependencies'].items():
        assert sha(ROOT/p) == h, p
    assert sha(ROOT/entry['infinite_model_proof']['path']) == entry['infinite_model_proof']['sha256']
    finite = core['finite_evidence']
    for field in ['source', 'log', 'validation_record']:
        assert sha(ROOT/finite[field]) == finite[field+'_sha256']
    old = remote/'attempt01'
    assert load(old/'latest.json')['result']['error_code'] == 'BANNED_PLACEHOLDER'
    assert load(old/'request.json')['code'].encode() == (old/'certificate.lean').read_bytes()
    excluded = lambda r: bool(r.get('unrestricted_triviality_proof') or r.get('universal_triviality_proof'))
    for name in ['README.md', 'README.zh-CN.md']:
        path = ROOT/name
        check_links(path)
        lines = path.read_text().splitlines()
        row = next(line for line in lines if line.startswith('| [Equation22446]'))
        assert '(proofs/Equation22446/InfiniteModel.lean)' in row
        for line in lines:
            if re.match(r'^\| (?:20\.[123]|\*\*(?:Total|合计)\*\*) \|', line):
                cells = [s.strip().strip('*') for s in line.strip('|').split('|')]
                group = rows if cells[0] in {'Total', '合计'} else [r for r in rows if r['table'] == cells[0]]
                expected = [len(group), sum(not r['finite_proof'] for r in group),
                    sum(bool(r['infinite_model_proof']) for r in group), sum(excluded(r) for r in group),
                    sum(not r['infinite_model_proof'] and not excluded(r) for r in group)]
                assert list(map(int, cells[1:])) == expected, (name, line)
    for name in manifest['documents']:
        check_links(ROOT/name)
    print(f'PASS: {len(manifest["files"])} archived files; 58 core modules; 58 export segments; '
          f'exact source, Nat injection, Judge ACCEPTED {receipt["job_id"]}; bilingual inventory.')


if __name__ == '__main__':
    verify()

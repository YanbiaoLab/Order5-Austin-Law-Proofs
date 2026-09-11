"""Audit the ten-equation archive using saved evidence; never invokes Lean/Judge."""
import hashlib
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / 'scripts'))
from build_index import validate


def digest(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for chunk in iter(lambda: stream.read(65536), b''):
            h.update(chunk)
    return h.hexdigest()


def main():
    data = json.loads((ROOT / 'proofs/index.json').read_text())
    validate(data)
    rows = {row['equation']: row for row in data['equations']}
    manifest = json.loads((HERE / 'manifest.json').read_text())
    targets = set(manifest['equations'])
    assert len(targets) == 10
    for path, expected in manifest['files'].items():
        assert digest(ROOT / path) == expected, path
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    checked = 0
    for run, count in [('eq10222-formal', 15), ('eq21866-formal', 30)]:
        folder = ROOT / 'proofs/validation' / run
        summary = json.loads((folder / 'summary.json').read_text())
        assert summary['status'] == 'passed'
        assert summary['modules_checked'] == len(summary['results']) == count
        for path, expected in summary['source_hashes'].items():
            assert digest(ROOT / path) == expected, path
        for record in summary['results']:
            assert record['status'] == 'passed' and record['exit_code'] == 0
            assert json.loads((folder / (record['module'] + '.json')).read_text()) == record
            assert digest(ROOT / record['source']) == record['sha256']
            log_path = ROOT / record['log']
            if record.get('log_sha256'):
                assert digest(log_path) == record['log_sha256']
            log = log_path.read_text()
            axioms = {name: [] for name in re.findall(r"'([^']+)' does not depend on any axioms", log)}
            axioms.update({name: [a.strip() for a in raw.split(',') if a.strip()]
                           for name, raw in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log)})
            assert all(set(items) <= allowed for items in axioms.values())
            if record.get('axioms'):
                assert all(axioms.get(name) == items for name, items in record['axioms'].items())
            expected = set(re.findall(r'^#print axioms ([A-Za-z0-9_.]+)\s*$',
                                      (ROOT / record['source']).read_text(), re.M))
            assert expected <= set(axioms), record['source']
            checked += 1
    remote_count = 0
    for name in targets:
        row = rows[name]
        assert row['finite_proof'] and row['infinite_model_proof'] and row['explicit_infinity']
        assert row['finite_compilation']['status'] == row['model_compilation']['status'] == 'passed'
        assert {'submission', 'submission.CM.tower_injective'} <= set(row['model_compilation']['axioms'])
        goal = (ROOT / f'proofs/{name}/JudgeProblem.lean').read_text()
        assert row['formula'] in goal, name
        remote = row.get('aurora_validation')
        if remote:
            folder = ROOT / 'proofs/validation/aurora' / name
            request = json.loads((folder / 'request.json').read_text())
            receipt = json.loads((folder / 'latest.json').read_text())
            job = json.loads((folder / 'job.json').read_text())
            assert request['problem']['equation1'] == row['formula']
            assert request['problem']['equation2'] == 'x = y' and request['verdict'] == 'false'
            assert request['code'] == (ROOT / remote['certificate']).read_text()
            assert digest(ROOT / remote['certificate']) == job['certificate_sha256'] == remote['certificate_sha256']
            assert receipt['job_id'] == job['response']['job_id'] == remote['job_id']
            assert receipt['status'] == 'done' and receipt['result']['status'] == 'accepted'
            assert receipt['result']['error_code'] == 'ACCEPTED'
            assert set(receipt['result']['axioms']) <= allowed
            remote_count += 1
    assert checked == 45 and remote_count == 8
    actual = {
        'finite_certificates': sum(bool(r.get('finite_proof')) for r in rows.values()),
        'model_certificates': sum(bool(r.get('infinite_model_proof')) for r in rows.values()),
        'both_certificates': sum(bool(r.get('finite_proof')) and bool(r.get('infinite_model_proof')) for r in rows.values()),
        'explicit_infinity': sum(bool(r.get('explicit_infinity')) for r in rows.values()),
    }
    assert actual == manifest['counts_after'], actual
    print('PASS: 10 complete Austin laws, 45 saved compilation records, 8 accepted receipts, all archive hashes')


if __name__ == '__main__':
    main()

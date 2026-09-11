"""Audit archived proof evidence without invoking Lean, solvers, or a service."""
from collections import Counter
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def digest(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(65536), b''):
            h.update(block)
    return h.hexdigest()


def check_record(value):
    if isinstance(value, list):
        for item in value:
            check_record(item)
    elif isinstance(value, dict):
        if value.get('path') and value.get('sha256'):
            assert digest(ROOT / value['path']) == value['sha256'], value['path']
        for key, item in value.items():
            if isinstance(item, str) and item.startswith('proofs/'):
                assert (ROOT / item).exists(), item
                if value.get(key + '_sha256'):
                    assert digest(ROOT / item) == value[key + '_sha256'], item
            elif key == 'dependencies' and isinstance(item, dict):
                for path, expected in item.items():
                    assert digest(ROOT / path) == expected, path
            else:
                check_record(item)


def axioms_from(log):
    found = {name: [] for name in re.findall(r"'([^']+)' does not depend on any axioms", log)}
    found.update({name: [a.strip() for a in raw.split(',') if a.strip()]
                  for name, raw in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log)})
    return found


def check_links(path):
    for target in re.findall(r'\]\(([^)]+)\)', path.read_text()):
        if '://' not in target and not target.startswith('#'):
            assert (path.parent / target.split('#')[0]).exists(), (str(path), target)


def main():
    data = json.loads((ROOT / 'proofs/index.json').read_text())
    rows = {r['equation']: r for r in data['equations']}
    assert len(rows) == len(data['equations']) == 130
    assert Counter(r['table'] for r in rows.values()) == {'20.1': 10, '20.2': 96, '20.3': 24}
    for row in rows.values():
        assert rows[row['dual']]['dual'] == row['equation']
        assert rows[row['dual']]['table'] == row['table']
        check_record(row)
        for proof, compilation in [('finite_proof', 'finite_compilation'),
                                    ('infinite_model_proof', 'model_compilation')]:
            record = row.get(compilation)
            if record and record.get('status') == 'passed':
                assert record['checked_sha256'] == row[proof]['sha256']
        if row.get('unrestricted_triviality_proof'):
            assert not row['infinite_model_proof']
    for path, expected in data['archived_files'].items():
        assert digest(ROOT / path) == expected, path

    manifest = json.loads((HERE / 'manifest.json').read_text())
    for path, expected in manifest['files'].items():
        assert digest(ROOT / path) == expected, path
        if path.endswith('.md'):
            check_links(ROOT / path)

    for name in manifest['new_finite_equations']:
        row = rows[name]
        proof, comp = row['finite_proof'], row['finite_compilation']
        record = json.loads((ROOT / comp['validation_record']).read_text())
        assert record['status'] == 'passed' and record['exit_code'] == 0
        assert record['source'] == proof['path']
        assert record['source_sha256'] == record['certificate_sha256'] == proof['sha256']
        assert record['log_sha256'] == comp['log_sha256'] == digest(ROOT / comp['log'])
        assert record['lean_version'] == 'leanprover/lean4:v4.33.1'
        source = (ROOT / proof['path']).read_text()
        normalized = re.sub(r'\s+', '', source)
        assert re.sub(r'\s+', '', row['formula']) in normalized
        theorem = proof['theorem'].split('.')[-1]
        declaration = re.search(r'theorem ' + re.escape(theorem) + r'\b(.*?) := by', source, re.S)
        assert declaration and '[Finite G]' in declaration[1] and 'Equation2 G' in declaration[1]
        assert name + ' G' in declaration[1]
        axioms = axioms_from((ROOT / comp['log']).read_text())
        assert axioms and all(set(items) <= ALLOWED for items in axioms.values())
        assert all(axioms.get(key) == items for key, items in comp['axioms'].items())
        assert proof['theorem'] in axioms
        assert not re.search(r'\b(sorry|admit|sorryAx)\b', source)

    for name in manifest['new_model_equations']:
        row = rows[name]
        remote = row['aurora_validation']
        folder = (ROOT / remote['result']).parent
        request = json.loads((folder / 'request.json').read_text())
        receipt = json.loads((folder / 'latest.json').read_text())
        job = json.loads((folder / 'job.json').read_text())
        source = (ROOT / row['infinite_model_proof']['path']).read_text()
        assert request['problem']['equation1'] == row['formula']
        assert request['problem']['equation2'] == 'x = y'
        assert request['verdict'] == receipt['result']['verdict'] == 'false'
        assert request['code'] == source == (ROOT / remote['certificate']).read_text()
        assert row['infinite_model_proof']['sha256'] == job['certificate_sha256'] == remote['certificate_sha256']
        assert receipt['job_id'] == job['response']['job_id'] == remote['job_id']
        assert receipt['status'] == 'done' and receipt['result']['status'] == 'accepted'
        assert receipt['result']['error_code'] == 'ACCEPTED'
        assert set(receipt['result']['axioms']) <= ALLOWED
        goal = (ROOT / f'proofs/{name}/JudgeProblem.lean').read_text()
        assert row['formula'] in goal and 'EquationLHS G ∧ ¬ EquationRHS G' in goal
        assert 'theorem tower_injective' in source and row['explicit_infinity']
        assert not re.search(r'\b(sorry|admit|sorryAx)\b', source)

    actual = {
        'finite_certificates': sum(bool(r['finite_proof']) for r in rows.values()),
        'model_certificates': sum(bool(r['infinite_model_proof']) for r in rows.values()),
        'explicit_infinity': sum(bool(r.get('explicit_infinity')) for r in rows.values()),
        'both_certificates': sum(bool(r['finite_proof']) and bool(r['infinite_model_proof']) for r in rows.values()),
        'excluded': sum(bool(r.get('unrestricted_triviality_proof')) for r in rows.values()),
    }
    assert actual == manifest['counts_after'], actual
    finite_missing = {r['equation'] for r in rows.values() if not r['finite_proof']}
    infinite_open = {r['equation'] for r in rows.values() if not r['infinite_model_proof'] and not r.get('unrestricted_triviality_proof')}
    assert finite_missing == set(manifest['finite_open'])
    assert infinite_open == set(manifest['infinite_open'])
    assert len(finite_missing) == 10 and len(infinite_open) == 14
    assert data['finite_campaign']['local_by_table'] == {'20.1': 10, '20.2': 96, '20.3': 14}
    finite_inventory = json.loads((ROOT / 'proofs/validation/finite130/inventory.json').read_text())
    for entry in finite_inventory:
        proof = rows[entry['equation']]['finite_proof']
        assert entry['finite_certificate'] == (proof['path'] if proof else None)
        assert entry['local_status'] == ('passed' if proof else 'missing')

    for filename in ['README.md', 'README.zh-CN.md']:
        path = ROOT / filename
        check_links(path)
        text = path.read_text()
        details = [line for line in text.splitlines() if line.startswith('| [Equation')]
        assert len(details) == 130
        for line, row in zip(details, rows.values()):
            columns = [v.strip() for v in line.strip('|').split('|')]
            assert f'[{row["equation"]}]' in columns[0] and columns[1] == row['dual']
            assert columns[2] == row['table']
            for column, field in [(4, 'finite_proof'), (6, 'infinite_model_proof')]:
                proof = row[field]
                assert (f'({proof["path"]})' in columns[column]) if proof else ('.lean)' not in columns[column])
        for line in text.splitlines():
            if re.match(r'^\| 20\.[123] \|', line):
                columns = [v.strip() for v in line.strip('|').split('|')]
                subset = [r for r in rows.values() if r['table'] == columns[0]]
                assert int(columns[1]) == len(subset)
                assert int(columns[-2]) == sum(not r['finite_proof'] for r in subset)
                assert int(columns[-1]) == sum(not r['infinite_model_proof'] for r in subset)
        current = text.split('<!-- current-proof-status:start -->')[1].split('<!-- current-proof-status:end -->')[0]
        for name in finite_missing | infinite_open:
            assert name in current, name
    print('PASS: 130 inventory entries; 6 saved finite runs; 4 accepted model receipts; hashes, goals, axioms and bilingual README; 120 finite / 114 models / 2 exclusions, 10 and 14 open.')


if __name__ == '__main__':
    main()

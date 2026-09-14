"""Fresh serial builds of the entire E12087 model and its exact dual goal."""
import hashlib
import json
from pathlib import Path
import re
import sys
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sys.path.insert(0, str(ROOT / 'scripts'))
import check_12857_lean as checker

ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def sha(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for chunk in iter(lambda: stream.read(65536), b''):
            h.update(chunk)
    return h.hexdigest()


def module_order():
    source_dir = ROOT / 'proofs/Equation12087/Lean'
    order, seen = [], set()
    def visit(name):
        if name in seen:
            return
        seen.add(name)
        for line in (source_dir / (name + '.lean')).read_text().splitlines():
            if line.startswith('import Trace'):
                for dep in line.split()[1:]:
                    visit(dep)
        order.append(name)
    visit('TraceFullSource')
    return source_dir, order


def checked(label, source, output, search):
    text = source.read_text()
    assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b', text), source
    result = checker.check(label, 256, 384, source, output, search)
    log = ROOT / result['log']
    text_log = log.read_text()
    axioms = {n: [] for n in re.findall(r"'([^']+)' does not depend on any axioms", text_log)}
    for name, raw in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text_log):
        axioms[name] = [v.strip() for v in raw.split(',') if v.strip()]
    expected = set(re.findall(r'^#print axioms ([\w.]+)$', text, re.M))
    assert expected == set(axioms), (label, expected, axioms)
    assert all(set(v) <= ALLOWED for v in axioms.values()), (label, axioms)
    assert 'sorryAx' not in text_log
    result.update(axioms=axioms, log_sha256=sha(log), olean_sha256=sha(output))
    (checker.LOGS / (label + '.json')).write_text(json.dumps(result, indent=2) + '\n')
    return result


def main():
    source_dir, order = module_order()
    assert len(order) == 125
    archived = json.loads((ROOT / 'search/validation/12087-trace-candidate/TraceFullSource-summary.json').read_text())
    for r in archived['results']:
        assert sha(source_dir / (r['module'] + '.lean')) == r['sha256']
    parent = ROOT / '.build'
    parent.mkdir(exist_ok=True)
    build = Path(tempfile.mkdtemp(prefix='eq12087-fresh-', dir=parent))
    assert not list(build.iterdir())
    checker.BUILD = build
    checker.LOGS = HERE / 'logs'
    checker.LOGS.mkdir(parents=True, exist_ok=True)
    reports = []
    for name in order:
        reports.append(checked(name, source_dir / (name + '.lean'), build / (name + '.olean'), [build]))
    assert sum(len(r['axioms']) for r in reports) == 311
    for eq in ('Equation12087', 'Equation33884'):
        dest = build / eq
        for stem in ('JudgeProblem', 'InfiniteModel'):
            reports.append(checked(eq + '-' + stem, ROOT / 'proofs' / eq / (stem + '.lean'),
                dest / (stem + '.olean'), [dest, build]))
    endpoint = {r['module']: r for r in reports}
    for eq in ('Equation12087', 'Equation33884'):
        assert {'submission', 'submission.source_law', 'submission.CM.tower_injective'} <= set(endpoint[eq + '-InfiniteModel']['axioms'])
    hashes = {r['source']: r['sha256'] for r in reports}
    hashes[str(Path(__file__).relative_to(ROOT))] = sha(Path(__file__))
    hashes['scripts/check_12857_lean.py'] = sha(ROOT / 'scripts/check_12857_lean.py')
    assert all(sha(ROOT / p) == digest for p, digest in hashes.items())
    summary = dict(status='passed', classification='nontrivial_infinite_model', version='4.33.1',
        equations=['Equation12087', 'Equation33884'],
        source_laws={'Equation12087': 'x = y ◇ (((y ◇ x) ◇ z) ◇ (x ◇ z))',
                     'Equation33884': 'x = ((y ◇ x) ◇ (y ◇ (x ◇ z))) ◇ z'},
        fresh_build=str(build), reused_olean_files=False, reports=reports, source_hashes=hashes,
        core_modules=125, core_endpoints=311, modules_checked=len(reports),
        sampled_peak_rss_mib=max(r['peak_rss_mib'] for r in reports),
        seconds=sum(r['elapsed_seconds'] for r in reports),
        limits=dict(lean_internal_mib=256, rss_stop_mib=384, seconds_per_module=120, jobs=1),
        remote_judge_called=False)
    (HERE / 'summary.json').write_text(json.dumps(summary, ensure_ascii=False, indent=2) + '\n')
    print('FULL MODEL PASS: Equation12087 and Equation33884; 129 fresh module builds', flush=True)


if __name__ == '__main__':
    main()

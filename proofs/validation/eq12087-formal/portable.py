"""Portable archive audit and bounded Lean replay; no original checkout needed.

Default: audit archived sources, logs, exact exports and remote receipts.
--rebuild: additionally rebuild the 125 core modules and both exact goals in a
fresh .build directory, serially at 256 MiB internal / 384 MiB RSS.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
EQUATIONS = ('Equation12087', 'Equation33884')


def sha(path):
    h = hashlib.sha256()
    with path.open('rb') as f:
        for chunk in iter(lambda: f.read(65536), b''):
            h.update(chunk)
    return h.hexdigest()


def read(path):
    return json.loads(path.read_text())


def source_path(name):
    # Preserve the original run's manifest, while archiving its tool in proofs/.
    if name == 'scripts/check_12857_lean.py':
        return HERE / 'support/check_12857_lean.py'
    return ROOT / name


def module_order():
    folder = ROOT / 'proofs/Equation12087/Lean'
    order, seen = [], set()
    def visit(name):
        if name in seen:
            return
        seen.add(name)
        for line in (folder / (name + '.lean')).read_text().splitlines():
            if line.startswith('import Trace'):
                for dep in line.split()[1:]:
                    visit(dep)
        order.append(name)
    visit('TraceFullSource')
    assert len(order) == 125
    return folder, order


def axioms(text):
    result = {n: [] for n in re.findall(r"'([^']+)' does not depend on any axioms", text)}
    for name, raw in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text):
        result[name] = [a.strip() for a in raw.split(',') if a.strip()]
    assert all(set(a) <= ALLOWED for a in result.values())
    assert 'sorryAx' not in text
    return result


def export_parts(eq):
    folder, order = module_order()
    imports, parts = {'import JudgeProblem'}, []
    rename = lambda s: s.replace('Austin12087Trace', 'submission.Austin12087Trace')
    for name in order:
        lines = (folder / (name + '.lean')).read_text().splitlines()
        imports.update(l for l in lines if l.startswith('import Init.'))
        body = '\n'.join(l for l in lines if l != 'prelude' and not l.startswith(('import ', '#print axioms ')))
        parts.append((name, rename('/- Checked module: ' + name + ' -/\n' + body)))
    wrapper = '\n'.join(l for l in (ROOT / 'proofs' / eq / 'InfiniteModel.lean').read_text().splitlines()
                        if l != 'prelude' and not l.startswith('import '))
    wrapper = wrapper.replace('instance : Magma CM :=', 'instance modelMagma : Magma CM :=')
    wrapper = rename(wrapper.replace('inferInstance', 'submission.modelMagma'))
    return sorted(imports), parts, wrapper


def audit():
    core = read(HERE / 'summary.json')
    exported = read(HERE / 'judge-local/summary.json')
    index = read(ROOT / 'proofs/index.json')
    entries = {e['equation']: e for e in index['equations']}
    assert core['modules_checked'] == 129 and core['core_endpoints'] == 311
    assert exported['validation_mode'] == 'exact_export_bodies_checked_in_segments'
    assert not exported['monolithic_local_pass']
    for manifest in (core, exported):
        assert manifest['status'] == 'passed' and not manifest['reused_olean_files']
        assert len(manifest['reports']) == 129
        for name, digest in manifest['source_hashes'].items():
            assert sha(source_path(name)) == digest, name
        for unit in manifest['reports']:
            assert unit['status'] == 'passed' and unit['exit_code'] == 0
            assert sha(source_path(unit['source'])) == unit['sha256']
            log = ROOT / unit['log']
            assert sha(log) == unit['log_sha256']
            assert axioms(log.read_text()) == unit['axioms']
            assert '-j1' in unit['command'] and '-M256' in unit['command']
            assert unit['peak_rss_mib'] <= unit['rss_limit_mib'] == 384
    form = index['local_formalizations']['eq12087']
    assert form['manifest_sha256'] == sha(HERE / 'summary.json')
    assert form['standalone_manifest_sha256'] == sha(HERE / 'judge-local/summary.json')
    for eq in EQUATIONS:
        imports, parts, wrapper = export_parts(eq)
        expected = ('prelude\n' + '\n'.join(imports) + '\nset_option Elab.async false\n\n'
                    + '\n\n'.join(b for _, b in parts) + '\n\n' + wrapper + '\n')
        cert = ROOT / 'proofs' / eq / 'JudgeSubmission.lean'
        assert cert.read_text() == expected
        previous = None
        common = [i for i in imports if i != 'import JudgeProblem']
        for name, body in parts:
            stem = 'Judge' + name
            header = 'prelude\n' + '\n'.join(common) + '\n'
            if previous:
                header += 'import ' + previous + '\n'
            assert (HERE / 'judge-local/parts' / (stem + '.lean')).read_text() == header + 'set_option Elab.async false\n' + body + '\n'
            previous = stem
        assert (HERE / 'judge-local/parts' / (eq + 'Wrapper.lean')).read_text() == (
            'prelude\nimport JudgeProblem\nimport ' + previous + '\nset_option Elab.async false\n' + wrapper + '\n')
        out = ROOT / 'proofs/validation/aurora' / eq
        request, state, receipt, job = [read(out / n) for n in ('request.json', 'submission-state.json', 'latest.json', 'job.json')]
        assert cert.read_bytes() == (out / 'certificate.lean').read_bytes() == request['code'].encode()
        digest = hashlib.sha256(json.dumps(request, sort_keys=True, ensure_ascii=False).encode()).hexdigest()
        assert state['request_sha256'] == digest and state['certificate_sha256'] == sha(cert)
        assert state['phase'] == 'terminal' and state['post_attempts'] == 1
        assert state['job_id'] == receipt['job_id'] == job['job_id']
        assert receipt['status'] == 'done' and receipt['error'] is None
        result = receipt['result']
        assert result['status'] == 'accepted' and result['error_code'] == 'ACCEPTED'
        assert result['verdict'] == request['verdict'] == 'false'
        assert set(result['axioms']) <= ALLOWED and request['cache_mode'] == 'off'
        assert request['problem'] == dict(id='order5-' + eq + '-to-Equation2', eq1_id=int(eq[8:]),
            eq2_id=2, equation1=core['source_laws'][eq], equation2='x = y')
        entry = entries[eq]
        assert entry['formula'] == core['source_laws'][eq] and entry['explicit_infinity']
        for key in ('infinite_model_proof', 'explicit_infinity_proof'):
            assert sha(ROOT / entry[key]['path']) == entry[key]['sha256']
        for name, digest in entry['infinite_model_proof']['dependencies'].items():
            assert sha(ROOT / name) == digest
        remote = entry['aurora_validation']
        assert remote['status'] == 'accepted' and remote['job_id'] == receipt['job_id']
        assert remote['certificate_sha256'] == sha(cert) and remote['result_sha256'] == sha(out / 'latest.json')
    for name, digest in index['archived_files'].items():
        assert sha(ROOT / name) == digest, name
    print('PORTABLE AUDIT PASS: exact equations, source/log hashes, exports, Nat injections, ACCEPTED receipts and inventory')
    return core


def rebuild(core):
    from support import check_12857_lean as checker
    parent = ROOT / '.build'
    parent.mkdir(exist_ok=True)
    build = Path(tempfile.mkdtemp(prefix='eq12087-replay-', dir=parent))
    checker.ROOT, checker.BUILD, checker.LOGS = ROOT, build, build / 'logs'
    checker.LOGS.mkdir()
    folder, order = module_order()
    reports = []
    for old in core['reports']:
        source = ROOT / old['source']
        if old['module'].startswith('Trace'):
            output, search = build / (old['module'] + '.olean'), [build]
        else:
            eq, stem = old['module'].split('-', 1)
            output, search = build / eq / (stem + '.olean'), [build / eq, build]
        unit = checker.check('Replay-' + old['module'], 256, 384, source, output, search)
        assert axioms((ROOT / unit['log']).read_text()) == old['axioms']
        reports.append(unit)
    result = dict(status='passed', modules_checked=len(reports), reports=reports,
                  peak_rss_mib=max(r['peak_rss_mib'] for r in reports),
                  scope='Fresh core and exact goal builds; archived remote receipts audited without resubmission')
    (build / 'summary.json').write_text(json.dumps(result, indent=2) + '\n')
    print('FRESH REPLAY PASS:', len(reports), 'builds;', result['peak_rss_mib'], 'MiB;', build)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--rebuild', action='store_true')
    args = parser.parse_args()
    core = audit()
    if args.rebuild:
        rebuild(core)

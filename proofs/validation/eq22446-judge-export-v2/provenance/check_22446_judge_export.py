"""Compile the exact exported sections serially; leave full-file checking to remote Judge."""
import json
from pathlib import Path
import re
import tempfile

from check_22446_infinite_model import c, sha, ALLOWED_AXIOMS
from export_22446_judge import ROOT, DEST, certificate_parts, certificate_text

HERE = ROOT/'proofs/validation/eq22446-judge-export-v2'
EXPECTED = {'submission', 'submission.source_law', 'submission.nontrivial',
            'submission.CM.tower_injective', 'submission.Equation22446Lineage.infinite_model'}


def checked(name, source, output):
    result = c.check(name, 192, 256, source, output)
    log = (ROOT/result['log']).read_text()
    axioms = {n: [] for n in re.findall(r"'([^']+)' does not depend on any axioms", log)}
    for n, raw in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log):
        axioms[n] = [x.strip() for x in raw.split(',') if x.strip()]
    assert all(set(ax) <= ALLOWED_AXIOMS for ax in axioms.values())
    result.update(axioms=axioms, log_sha256=sha(ROOT/result['log']), olean_sha256=sha(output))
    (HERE/(name+'.json')).write_text(json.dumps(result, indent=2)+'\n')
    return result


def audit_export():
    summary = json.loads((HERE/'summary.json').read_text())
    assert summary['status'] == 'passed' and len(summary['results']) == 58
    assert DEST.read_text() == certificate_text()
    for name, digest in summary['source_hashes'].items():
        assert sha(ROOT/name) == digest, name
    for result in summary['results']:
        assert result['status'] == 'passed'
        assert sha(ROOT/result['log']) == result['log_sha256']
        assert sha(Path(result['command'][result['command'].index('-o')+1])) == result['olean_sha256']
    common, sections, wrapper = certificate_parts()
    previous = None
    for name, body in sections:
        stem = 'Export'+name.replace('.', '')
        header = 'prelude\n'+'\n'.join(common)+'\n'
        if previous:
            header += 'import '+previous+'\n'
        expected = header+'set_option Elab.async false\n'+body+'\n'
        assert (HERE/'parts'/(stem+'.lean')).read_text() == expected
        previous = stem
    assert (HERE/'parts/ExportWrapper.lean').read_text() == (
        'prelude\nimport JudgeProblem\nimport '+previous+'\n'+wrapper+'\n')
    assert set(summary['results'][-1]['axioms']) == EXPECTED
    return summary


def main():
    HERE.mkdir(parents=True, exist_ok=True)
    if (HERE/'summary.json').exists():
        summary = audit_export()
        print(json.dumps(dict(existing_export_audit='passed', modules=len(summary['results']))))
        return
    assert DEST.read_text() == certificate_text()
    src = HERE/'parts'
    src.mkdir(exist_ok=True)
    c.BUILD = Path(tempfile.mkdtemp(prefix='eq22446-judge-export-', dir=ROOT/'.build'))
    c.LOGS = HERE
    results = []
    common, sections, wrapper = certificate_parts()
    previous = None
    for name, body in sections:
        stem = 'Export'+name.replace('.', '')
        path = src/(stem+'.lean')
        header = 'prelude\n'+'\n'.join(common)+'\n'
        if previous:
            header += 'import '+previous+'\n'
        path.write_text(header+'set_option Elab.async false\n'+body+'\n')
        results.append(checked(stem, path, c.BUILD/(stem+'.olean')))
        previous = stem
    for name, source in [('JudgeMagma.Magma', ROOT/'proofs/Equation22446/Lean/JudgeMagma/Magma.lean'),
                         ('JudgeProblem', ROOT/'proofs/Equation22446/JudgeProblem.lean')]:
        results.append(checked(name.replace('.', '-'), source,
                               c.BUILD/(name.replace('.', '/')+'.olean')))
    path = src/'ExportWrapper.lean'
    path.write_text('prelude\nimport JudgeProblem\nimport '+previous+'\n'+wrapper+'\n')
    results.append(checked('ExportWrapper', path, c.BUILD/'ExportWrapper.olean'))
    assert set(results[-1]['axioms']) == EXPECTED
    assert len(results) == 58
    hashes = {r['source']: r['sha256'] for r in results}
    for path in [DEST, ROOT/'scripts/export_22446_judge.py', Path(__file__).resolve(),
                 ROOT/'proofs/validation/eq22446-infinite-model/summary.json']:
        hashes[str(path.relative_to(ROOT))] = sha(path)
    summary = dict(status='passed', validation_mode='exact_export_bodies_checked_in_segments',
        monolithic_local_pass=False, equation='Equation22446',
        certificate=str(DEST.relative_to(ROOT)), certificate_sha256=sha(DEST),
        bytes=DEST.stat().st_size, fresh_build=str(c.BUILD), reused_olean_files=False,
        sampled_peak_rss_mib=max(r['peak_rss_mib'] for r in results),
        total_seconds=round(sum(r['elapsed_seconds'] for r in results), 3),
        limits=dict(jobs=1, lean_memory_mib=192, rss_stop_mib=256, seconds_per_module=120),
        source_hashes=hashes, results=results)
    (HERE/'summary.json').write_text(json.dumps(summary, indent=2)+'\n')
    audit_export()
    print(json.dumps({k: v for k, v in summary.items() if k not in {'source_hashes', 'results'}}))


if __name__ == '__main__':
    main()

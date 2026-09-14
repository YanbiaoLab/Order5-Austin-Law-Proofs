"""Check exact exported proof bodies in small serial modules.

Local monolithic attempts hit RSS guards. The remote Judge checks the full file.
"""
import json
from pathlib import Path
import tempfile
from verify import ROOT, HERE, checker, checked, sha
from export_judge import certificate_text, certificate_parts
from audit import audit


def main():
    audit()
    out = HERE / 'judge-local'
    out.mkdir(exist_ok=True)
    assert not (out / 'summary.json').exists(), 'Preserve completed verification before rerunning'
    src = out / 'parts'
    src.mkdir(exist_ok=True)
    build = Path(tempfile.mkdtemp(prefix='eq12087-judge-parts-', dir=ROOT / '.build'))
    checker.LOGS = out
    checker.BUILD = build
    reports = []
    imports, sections, _ = certificate_parts('Equation12087')
    common = [i for i in imports if i != 'import JudgeProblem']
    previous = None
    for name, body in sections:
        stem = 'Judge' + name
        path = src / (stem + '.lean')
        header = 'prelude\n' + '\n'.join(common) + '\n'
        if previous:
            header += 'import ' + previous + '\n'
        path.write_text(header + 'set_option Elab.async false\n' + body + '\n')
        reports.append(checked(stem, path, build / (stem + '.olean'), [build]))
        previous = stem
    for eq in ('Equation12087', 'Equation33884'):
        certificate = ROOT / 'proofs' / eq / 'JudgeSubmission.lean'
        assert certificate.read_text() == certificate_text(eq)
        _, same, wrapper = certificate_parts(eq)
        assert same == sections
        dest = build / eq
        wrapper_path = src / (eq + 'Wrapper.lean')
        wrapper_path.write_text('prelude\nimport JudgeProblem\nimport ' + previous
            + '\nset_option Elab.async false\n' + wrapper + '\n')
        reports.append(checked(eq + '-JudgeProblem-Export',
            ROOT / 'proofs' / eq / 'JudgeProblem.lean', dest / 'JudgeProblem.olean', [dest, build]))
        reports.append(checked(eq + '-JudgeSubmission-Export', wrapper_path,
            dest / 'JudgeSubmission.olean', [dest, build]))
    hashes = {r['source']: r['sha256'] for r in reports}
    for p in (HERE / 'verify_judge.py', HERE / 'export_judge.py', HERE / 'summary.json',
              ROOT / 'proofs/Equation12087/JudgeSubmission.lean', ROOT / 'proofs/Equation33884/JudgeSubmission.lean'):
        hashes[str(p.relative_to(ROOT))] = sha(p)
    summary = dict(status='passed', validation_mode='exact_export_bodies_checked_in_segments',
        monolithic_local_pass=False, equations=['Equation12087', 'Equation33884'],
        reports=reports, source_hashes=hashes, fresh_build=str(build), reused_olean_files=False,
        sampled_peak_rss_mib=max(r['peak_rss_mib'] for r in reports),
        seconds=sum(r['elapsed_seconds'] for r in reports),
        limits=dict(lean_internal_mib=256, rss_stop_mib=384, seconds_per_module=120, jobs=1))
    (out / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    print('EXACT EXPORT SEGMENTS PASS', summary['sampled_peak_rss_mib'], 'MiB')


if __name__ == '__main__':
    main()

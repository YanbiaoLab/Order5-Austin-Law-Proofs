"""Fresh standalone checks under the established serial memory limits."""
import json
import tempfile
from verify import ROOT, HERE, checker, checked, sha
from export_judge import certificate_text
from audit import audit


def main():
    audit()
    out = HERE / 'judge-local'
    out.mkdir(exist_ok=True)
    assert not (out / 'summary.json').exists(), 'Preserve completed verification before rerunning'
    build = ROOT / '.build' / tempfile.mkdtemp(prefix='eq12087-judge-', dir=ROOT / '.build')
    checker.LOGS = out
    checker.BUILD = build
    reports = []
    for eq in ('Equation12087', 'Equation33884'):
        source = ROOT / 'proofs' / eq / 'JudgeSubmission.lean'
        assert source.read_text() == certificate_text(eq)
        dest = build / eq
        for stem in ('JudgeProblem', 'JudgeSubmission'):
            reports.append(checked(eq + '-' + stem + '-Standalone',
                ROOT / 'proofs' / eq / (stem + '.lean'), dest / (stem + '.olean'), [dest]))
    hashes = {r['source']: r['sha256'] for r in reports}
    for p in (HERE / 'verify_judge.py', HERE / 'export_judge.py', HERE / 'summary.json'):
        hashes[str(p.relative_to(ROOT))] = sha(p)
    summary = dict(status='passed', equations=['Equation12087', 'Equation33884'],
        reports=reports, source_hashes=hashes, fresh_build=str(build), reused_olean_files=False,
        sampled_peak_rss_mib=max(r['peak_rss_mib'] for r in reports),
        seconds=sum(r['elapsed_seconds'] for r in reports),
        limits=dict(lean_internal_mib=256, rss_stop_mib=384, seconds_per_module=120, jobs=1))
    (out / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    print('STANDALONE PASS', summary['sampled_peak_rss_mib'], 'MiB')


if __name__ == '__main__':
    main()

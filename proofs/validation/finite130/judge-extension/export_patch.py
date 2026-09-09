"""Export the tested local proposal without changing the running judge or its repo."""

from pathlib import Path
import difflib
import hashlib
import json
import subprocess

ROOT = Path(__file__).resolve().parents[4]
OUT = Path(__file__).resolve().parent
BUILD = ROOT / '.build/judge-finite-extension'
SERVICE = ROOT.parent / 'math-distill-equational-stage2'
PACKAGE = Path('src/judge_v3/judge_v3_repl')


def sha(path):
    h = hashlib.sha256()
    with path.open('rb') as f:
        for chunk in iter(lambda: f.read(65536), b''):
            h.update(chunk)
    return h.hexdigest()


def main():
    base = json.loads((BUILD / 'base-manifest.json').read_text())
    parts = []
    files = []
    for rel, expected in sorted(base.items()):
        original = SERVICE / PACKAGE / rel
        proposed = BUILD / 'judge_v3_repl' / rel
        assert sha(original) == expected, f'Service source changed: {rel}'
        if sha(proposed) == expected:
            continue
        path = (PACKAGE / rel).as_posix()
        parts.append(''.join(difflib.unified_diff(
            original.read_text().splitlines(keepends=True),
            proposed.read_text().splitlines(keepends=True),
            fromfile='a/' + path, tofile='b/' + path)))
        files.append(dict(path=path, before_sha256=expected, after_sha256=sha(proposed)))
    test = OUT / 'test_finite_domain.py'
    test_path = 'src/judge_v3/tests/test_finite_domain.py'
    assert not (SERVICE / test_path).exists(), 'Proposed test already exists in service repo'
    parts.append(''.join(difflib.unified_diff(
        [], test.read_text().splitlines(keepends=True),
        fromfile='/dev/null', tofile='b/' + test_path)))
    files.append(dict(path=test_path, before_sha256=None, after_sha256=sha(test)))
    patch = OUT / 'finite-domain.patch'
    patch.write_text(''.join(parts))
    subprocess.run(['git', 'apply', '--check', str(patch)], cwd=SERVICE, check=True)

    rows = {r['equation']: r for r in json.loads((ROOT / 'proofs/index.json').read_text())['equations']}
    kernel = json.loads((OUT / 'kernel/all-finite-summary.json').read_text())
    requests = []
    for result in kernel:
        eq = result['case'].removesuffix('-finite')
        row = rows[eq]
        assert result['submission_status'] == 'passed'
        assert not result['bad_axioms'] and not result['bad_declarations']
        assert sha(ROOT / result['finite_certificate']) == result['finite_certificate_sha256']
        assert sha(ROOT / result['request']) == result['request_sha256']
        payload = json.loads((ROOT / result['request']).read_text())
        assert payload['model_domain'] == 'finite' and payload['verdict'] == 'true'
        assert payload['problem']['eq1_id'] == int(eq[8:])
        assert payload['problem']['eq2_id'] == 2
        assert payload['problem']['equation1'] == row['formula']
        assert '[Finite G]' in result['target_source']
        assert not result['submitted_to_aurora']
        requests.append(dict(equation=eq, table=row['table'], status='ready_not_submitted',
                             path=result['request'], sha256=result['request_sha256'],
                             certificate=result['finite_certificate'],
                             certificate_sha256=result['finite_certificate_sha256']))
    assert len(requests) == sum(bool(row['finite_proof']) for row in rows.values())
    assert len({r['equation'] for r in requests}) == len(requests)
    requests.sort(key=lambda r: (r['table'], int(r['equation'][8:])))
    (OUT / 'requests-manifest.json').write_text(json.dumps(requests, ensure_ascii=False, indent=2) + '\n')
    controls = json.loads((OUT / 'kernel/controls-summary.json').read_text())
    assert len(controls) == 3
    assert [c.get('submission_status', c.get('status')) for c in controls] == ['failed', 'failed', 'passed']
    tests = (OUT / 'python-tests.log').read_text()
    assert '80 passed' in tests
    peak = 0
    for path in (OUT / 'kernel').glob('*.json'):
        record = json.loads(path.read_text())
        if isinstance(record, dict):
            peak = max(peak, record.get('peak_rss_mib', 0))
    repl = json.loads((OUT / 'repl-integration/summary.json').read_text())
    assert len(repl) >= 6
    assert {'Equation4916-finite', 'Equation5093-finite', 'Equation18137-finite',
            'Equation5093-all', 'Equation5093-finite-unrelated', 'finite-false-Bool'} <= {r['case'] for r in repl}
    for record in repl:
        assert record['http_status'] == 200
        assert (record['result']['status'] == 'accepted') == record['expected_accepted']
        assert not record['submitted_to_aurora']
    manifest = dict(
        status='tested_proposal_not_applied_not_deployed',
        patch=patch.name, patch_sha256=sha(patch), files=files,
        service_repository_head=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=SERVICE, text=True).strip(),
        service_base_manifest_sha256=sha(BUILD / 'base-manifest.json'),
        git_apply_check='passed', python_tests_passed=80,
        python_tests_log_sha256=sha(OUT / 'python-tests.log'),
        finite_kernel_and_policy_checks_passed=len(requests),
        finite_kernel_summary_sha256=sha(OUT / 'kernel/all-finite-summary.json'),
        controls_passed=3, controls_summary_sha256=sha(OUT / 'kernel/controls-summary.json'),
        lean_memory_limit_mib=2048, sampled_rss_stop_mib=3072, sampled_peak_rss_mib=peak,
        full_custom_repl_integration_checked=True,
        native_worker_repl_cases_passed=len(repl),
        native_repl_build_manifest_sha256=sha(OUT / 'repl-build/manifest.json'),
        native_worker_repl_summary_sha256=sha(OUT / 'repl-integration/summary.json'),
        aurora_finite_accepted=0,
    )
    (OUT / 'patch-manifest.json').write_text(json.dumps(manifest, ensure_ascii=False, indent=2) + '\n')
    print(f'Exported {len(files)} files, {patch.stat().st_size} patch bytes; {len(requests)} requests; peak RSS {peak} MiB.')
    print('git apply --check passed. No service source or deployment changed.')


if __name__ == '__main__':
    main()

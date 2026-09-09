"""Exercise the real staged REPL through the local worker ASGI application."""

from pathlib import Path
import argparse
import hashlib
import json
import time

from fastapi.testclient import TestClient
from judge_v3_repl.app import create_app
from judge_v3_repl.config import DEFAULT_STAGE2_JUDGE_REPO, JudgeV3ReplSettings

ROOT = Path(__file__).resolve().parents[4]
OUT = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--equations', nargs='+')
    args = parser.parse_args()
    build = json.loads((OUT / 'repl-build/manifest.json').read_text())
    settings = JudgeV3ReplSettings(
        judge_repo=DEFAULT_STAGE2_JUDGE_REPO,
        repl_bin=Path(build['wrapper']), repl_env_file=Path(build['env_file']),
        workers=1, default_timeout_seconds=120, timeout_cap_seconds=120,
    )
    cases = [(name, json.loads((OUT / 'requests' / (name + '.json')).read_text()), expected)
             for name, expected in [('Equation4916-finite', True), ('Equation5093-finite', True),
                                    ('Equation18137-finite', True), ('Equation5093-all', False),
                                    ('Equation5093-finite-unrelated', False)]]
    bool_code = (ROOT / '.build/judge-finite-extension/kernel/finite-false-Bool/Submission.lean').read_text()
    cases.append(('finite-false-Bool', dict(
        problem=dict(id='finite-false-Bool', eq1_id=1, eq2_id=2, equation1='x = x', equation2='x = y'),
        verdict='false', model_domain='finite', code=bool_code, timeout_seconds=120, cache_mode='off'), True))
    if args.equations:
        cases = [(eq+'-finite', json.loads((OUT/'requests'/(eq+'-finite.json')).read_text()), True)
                 for eq in args.equations]
    records = []
    folder = OUT / 'repl-integration'
    folder.mkdir(exist_ok=True)
    if args.equations and (folder/'summary.json').exists():
        replacing = {name for name, _, _ in cases}
        records = [r for r in json.loads((folder/'summary.json').read_text()) if r['case'] not in replacing]
    with TestClient(create_app(settings)) as client:
        health = client.get('/health').json()
        assert health['supported_model_domains'] == ['all', 'finite']
        (folder / 'health.json').write_text(json.dumps(health, ensure_ascii=False, indent=2)+'\n')
        for name, request, expected in cases:
            started = time.monotonic()
            response = client.post('/verify', json=request)
            result = response.json()
            record = dict(case=name, expected_accepted=expected,
                          request_sha256=hashlib.sha256(json.dumps(request, sort_keys=True).encode()).hexdigest(),
                          http_status=response.status_code, elapsed_seconds=round(time.monotonic()-started, 3),
                          result=result, local_only=True, submitted_to_aurora=False)
            (folder / (name+'.json')).write_text(json.dumps(record, ensure_ascii=False, indent=2)+'\n')
            records.append(record)
            (folder / 'summary.json').write_text(json.dumps(records, ensure_ascii=False, indent=2)+'\n')
            print(name, response.status_code, result.get('status'), result.get('error_code'), flush=True)
            assert response.status_code == 200, record
            assert result['model_domain'] == request['model_domain'], record
            assert (result['status'] == 'accepted') == expected, record
            if not expected:
                assert result['error_code'] == 'LEAN_REJECTED', record
    print(f'All {len(cases)} real REPL cases met expectations locally; no Aurora submissions.', flush=True)


if __name__ == '__main__':
    main()

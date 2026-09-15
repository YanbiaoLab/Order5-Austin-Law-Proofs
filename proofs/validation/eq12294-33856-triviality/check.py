"""Audit the published pair, or rebuild its Lean certificates in fresh directories.

Default: read-only archive verification. --compile requires a destination for new
logs and refuses to overwrite a prior summary. No command submits remote jobs.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
VERSION = 'leanprover/lean4:v4.33.1'
FORMULAS = {12294: 'x = y ◇ (((z ◇ y) ◇ x) ◇ (x ◇ y))',
            33856: 'x = ((y ◇ x) ◇ (x ◇ (y ◇ z))) ◇ y'}
DIGESTS = {12294: 'e594322cd9a5652ecbf6a124316acdec468efef94be6ec1ea87f5280b8e85675',
           33856: 'cbea0aa9706bad6ca77eaf2da51ca0cd22b8ad1d458b7e9e0a73e6bcc6b1f287'}


def sha(path):
    result = hashlib.sha256()
    with path.open('rb') as stream:
        for chunk in iter(lambda: stream.read(65536), b''):
            result.update(chunk)
    return result.hexdigest()


def read(path):
    return json.loads(path.read_text())


def rss(pid):
    # Only process IDs, parent IDs and RSS are read; no command-line contents.
    with subprocess.Popen(['ps', '-axo', 'pid=,ppid=,rss='], stdout=subprocess.PIPE,
                          text=True) as proc:
        rows = [tuple(map(int, line.split())) for line in proc.stdout if line.strip()]
    selected = {pid}
    while True:
        extended = selected | {p for p, parent, _ in rows if parent in selected}
        if extended == selected:
            break
        selected = extended
    return sum(size * 1024 for p, _, size in rows if p in selected)


def compile_all(output):
    output.mkdir(parents=True, exist_ok=True)
    assert not (output / 'summary.json').exists(), 'Preserve existing evidence; choose a new output directory'
    logs = output / 'logs'
    logs.mkdir(exist_ok=True)
    compiler = shutil.which('lean')
    assert compiler, 'Lean/elan is required for --compile'
    version = subprocess.check_output([compiler, '+' + VERSION, '--version'], text=True).strip()
    results = []
    with tempfile.TemporaryDirectory(prefix='eq12294-33856-lean-') as temporary:
        temporary = Path(temporary)
        for number in FORMULAS:
            source_root = temporary / str(number) / 'source'
            build = temporary / str(number) / 'build'
            source_root.mkdir(parents=True)
            build.mkdir()
            equation = ROOT / f'proofs/Equation{number}'
            sources = [('JudgeMagma.Magma', HERE / 'Magma.lean'),
                       ('JudgeProblem', equation / 'JudgeProblem.lean'),
                       ('Triviality', equation / 'Triviality.lean'),
                       ('Audit', HERE / 'Audit.lean'),
                       ('AllModelsTrivial', equation / 'AllModelsTrivial.lean')]
            env = dict(os.environ, LEAN_PATH=str(build))
            for name, original in sources:
                filename = name.replace('.', '/') + '.lean'
                source = source_root / filename
                source.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(original, source)
                target = build / (name.replace('.', '/') + '.olean')
                target.parent.mkdir(parents=True, exist_ok=True)
                label = f'Equation{number}-{name.replace(".", "-")}'
                log = logs / (label + '.log')
                command = [compiler, '+' + VERSION, '-j1', '-M96', '-DwarningAsError=true',
                           '-o', str(target), filename]
                if sys.platform == 'darwin':
                    command = ['/usr/bin/time', '-l'] + command
                start = time.monotonic()
                peak = 0
                reason = None
                with log.open('w') as stream:
                    proc = subprocess.Popen(command, cwd=source_root, env=env,
                        stdout=stream, stderr=subprocess.STDOUT, start_new_session=True)
                    try:
                        while proc.poll() is None:
                            peak = max(peak, rss(proc.pid))
                            if peak > 160 * 1024**2:
                                reason = 'rss_limit'
                            elif time.monotonic() - start > 15:
                                reason = 'time_limit'
                            if reason:
                                os.killpg(proc.pid, signal.SIGKILL)
                                break
                            time.sleep(.1)
                        proc.wait()
                    finally:
                        if proc.poll() is None:
                            os.killpg(proc.pid, signal.SIGKILL)
                            proc.wait()
                text = log.read_text()
                high = re.search(r'(\d+)\s+maximum resident set size', text)
                status = reason or ('passed' if proc.returncode == 0 else 'failed')
                result = dict(equation=number, module=name, status=status,
                    source=str(original.relative_to(ROOT)), source_sha256=sha(original),
                    log='logs/' + log.name, log_sha256=sha(log),
                    seconds=time.monotonic()-start, sampled_peak_rss_bytes=peak,
                    process_max_rss_bytes=int(high[1]) if high else None,
                    exit_code=proc.returncode,
                    command_template=['lean', '+' + VERSION, '-j1', '-M96',
                        '-DwarningAsError=true', '-o', '<temporary-build>/' + name + '.olean', filename],
                    command_note='Executed in a fresh source directory; temporary absolute paths omitted.',
                    axiom_free_declarations=re.findall(r"'([^']+)' does not depend on any axioms", text))
                results.append(result)
                (output / 'partial-results.json').write_text(json.dumps(results, indent=2)+'\n')
                print(label, status, flush=True)
                assert status == 'passed', text
                assert 'sorryAx' not in text and not re.search(r'depends on axioms: \[[^\]]', text)
                assert not high or int(high[1]) < 160 * 1024**2
                if name == 'Audit':
                    assert result['axiom_free_declarations'] == ['submission']
                if name == 'AllModelsTrivial':
                    assert len(result['axiom_free_declarations']) == (7 if number == 12294 else 9)
    summary = dict(status='passed', lean_version=version, equations=[12294, 33856],
        units=10, results=results, temporary_builds_removed=True, reused_oleans=False,
        limits=dict(threads=1, lean_internal_mib=96, rss_stop_mib=160, seconds_per_module=15))
    (output / 'summary.json').write_text(json.dumps(summary, indent=2)+'\n')
    (output / 'partial-results.json').unlink()
    print(json.dumps(dict(status='passed', units=10, temporary_builds_removed=True)))


def audit():
    manifest = read(HERE / 'manifest.json')
    for item in manifest:
        path = ROOT / item['path']
        assert path.is_relative_to(ROOT) and sha(path) == item['sha256'], item['path']
    summary = read(HERE / 'summary.json')
    assert summary['status'] == 'passed' and summary['units'] == 10
    for result in summary['results']:
        assert result['status'] == 'passed' and result['exit_code'] == 0
        assert sha(ROOT / result['source']) == result['source_sha256']
        assert sha(HERE / result['log']) == result['log_sha256']
        if result['module'] == 'Audit':
            assert result['axiom_free_declarations'] == ['submission']
    responses = {}
    index = read(ROOT / 'proofs/index.json')
    for number, formula in FORMULAS.items():
        equation = ROOT / f'proofs/Equation{number}'
        cert = equation / 'Triviality.lean'
        receipt = read(equation / 'judge_acceptance.json')
        problem = read(equation / 'problem.json')
        request = read(HERE / f'Equation{number}/request.json')
        response = read(HERE / f'Equation{number}/response.json')
        responses[number] = response
        assert sha(cert) == DIGESTS[number] == receipt['certificate_sha256']
        assert cert.read_text() == request['code']
        assert problem == request['problem'] == receipt['problem']
        assert problem['eq1_id'] == number and problem['eq2_id'] == 2
        assert problem['equation1'] == formula and problem['equation2'] == 'x = y'
        assert request['verdict'] == receipt['verdict'] == response['result']['verdict'] == 'true'
        assert request['cache_mode'] == 'off' and receipt['submission_attempt'] == 1
        assert response['status'] == 'done'
        assert receipt['status'] == response['result']['status'] == 'accepted'
        assert receipt['error_code'] == response['result']['error_code'] == 'ACCEPTED'
        assert receipt['axioms'] == response['result']['axioms'] == []
        assert receipt['job_id'] == response['job_id']
        assert sha(ROOT / receipt['response_record']) == receipt['response_record_sha256']
        assert receipt['problem_sha256'] == hashlib.sha256(json.dumps(problem, sort_keys=True,
            ensure_ascii=False, separators=(',', ':')).encode()).hexdigest()
        goal = (equation / 'JudgeProblem.lean').read_text()
        assert formula in goal and 'Finite' not in goal
        assert '∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G' in goal
        assert not re.search(r'\b(sorry|admit|sorryAx|axiom|unsafe)\b', cert.read_text())
        row = next(r for r in index['equations'] if r['equation'] == f'Equation{number}')
        assert row['austin_status'] == 'excluded_all_models_trivial'
        assert row['infinite_model_proof'] is None and not row['explicit_infinity']
        assert row['unrestricted_triviality_proof']['sha256'] == sha(cert)
        assert sha(ROOT / row['finite_proof']['path']) == row['finite_proof']['sha256']
    assert responses[12294]['finished_at'] < responses[33856]['created_at']
    counts = dict(models=sum(bool(r.get('infinite_model_proof')) for r in index['equations']),
        excluded=sum(r.get('austin_status') == 'excluded_all_models_trivial' for r in index['equations']))
    counts['open'] = len(index['equations']) - counts['models'] - counts['excluded']
    assert counts == dict(models=122, excluded=4, open=4)
    for filename in ['README.md', 'README.zh-CN.md']:
        text = (ROOT / filename).read_text()
        assert '| 20.3 | 24 | 10 | 20 | 2 | 2 |' in text
        pending = next(line for line in text.splitlines() if line.startswith('- **Infinite-model certificates pending')
                       or line.startswith('- **无限侧待补'))
        assert 'Equation12294' not in pending and 'Equation33856' not in pending
    # New proof documents must resolve without the private research directory.
    for item in manifest:
        path = ROOT / item['path']
        if path.suffix != '.md':
            continue
        if path not in {ROOT / 'proofs/Equation12294/README.md',
                        ROOT / 'proofs/Equation12294/PROOF.zh-CN.md',
                        ROOT / 'proofs/Equation33856/README.md', HERE / 'README.md'}:
            continue
        for link in re.findall(r'\]\(([^)]+)\)', path.read_text()):
            if '://' in link or link.startswith('#'):
                continue
            target = path.parent / link.split('#', 1)[0]
            assert target.exists(), (item['path'], link)
    print(json.dumps(dict(status='passed', files=len(manifest), lean_units=10,
        remote_accepted=[12294, 33856], axioms=[], counts=counts)))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compile', action='store_true')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if args.compile:
        parser.error('--output is required for --compile') if args.output is None else compile_all(args.output)
    else:
        audit()

"""Compile/audit the E22591 proof and export with serial, bounded Lean processes."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import tempfile
import time

from export import HERE, ROOT, CERTIFICATE, export, export_parts, sha

ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
ENDPOINTS = {'submission', 'submission.source_law', 'submission.nontrivial',
             'submission.CM.tower_injective', 'submission.infinite_model'}


def load(path):
    return json.loads(path.read_text())


def axiom_reports(text):
    result = {name: [] for name in re.findall(r"'([^']+)' does not depend on any axioms", text)}
    for name, raw in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text):
        result[name] = [s.strip() for s in raw.split(',') if s.strip()]
    return result


def compile_unit(name, source, output, build):
    output.parent.mkdir(parents=True, exist_ok=True)
    log = HERE/'logs'/(name+'.log')
    log.parent.mkdir(exist_ok=True)
    args = ['lean', '+leanprover/lean4:v4.33.1', '-j1', '-M192',
        '-DwarningAsError=true', '-Dlinter.unusedVariables=false',
        '-Dlinter.unusedSimpArgs=false', '-Dlinter.defProp=false', '-o', str(output), str(source)]
    start = time.monotonic()
    peak = 0.0
    reason = None
    with log.open('w') as stream:
        process = subprocess.Popen(args, cwd=ROOT,
            env=dict(os.environ, LEAN_PATH=str(build)), stdout=stream,
            stderr=subprocess.STDOUT, start_new_session=True)
        try:
            while process.poll() is None:
                sample = subprocess.run(['ps', '-o', 'rss=', '-p', str(process.pid)],
                                        capture_output=True, text=True)
                peak = max(peak, int(sample.stdout.strip() or 0)/1024)
                if peak > 256:
                    reason = 'rss_limit'
                if time.monotonic()-start > 120:
                    reason = 'time_limit'
                if reason:
                    os.killpg(process.pid, signal.SIGKILL)
                    break
                time.sleep(0.1)
            process.wait()
        finally:
            if process.poll() is None:
                os.killpg(process.pid, signal.SIGKILL)
                process.wait()
    status = reason or ('passed' if process.returncode == 0 else 'failed')
    print(json.dumps(dict(module=name, status=status, sampled_peak_rss_mib=round(peak, 2))), flush=True)
    if status != 'passed':
        print(log.read_text()[-8000:])
        raise SystemExit(1)
    axioms = axiom_reports(log.read_text())
    assert all(set(a) <= ALLOWED for a in axioms.values())
    return dict(module=name, status=status, source=str(source.relative_to(ROOT)), sha256=sha(source),
        log=str(log.relative_to(ROOT)), log_sha256=sha(log), axioms=axioms, command=args,
        elapsed_seconds=round(time.monotonic()-start, 3), sampled_peak_rss_mib=round(peak, 2),
        olean_sha256=sha(output))


def compile_all():
    assert not (HERE/'summary.json').exists(), 'Preserve an earlier completed audit before rebuilding'
    export()
    core = load(ROOT/'proofs/validation/eq22446-infinite-model/summary.json')
    exported = load(ROOT/'proofs/validation/eq22446-judge-export-v2/summary.json')
    results = []
    with tempfile.TemporaryDirectory(prefix='eq22591-lean-') as temporary:
        build = Path(temporary)
        for record in core['results']:
            if record['module'] in {'JudgeProblem', 'InfiniteModel'}:
                continue
            source = ROOT/record['source']
            assert sha(source) == record['sha256']
            relative = source.relative_to(ROOT/'proofs/Equation22446/Lean')
            results.append(compile_unit(record['module'], source,
                (build/relative).with_suffix('.olean'), build))
        for stem in ['JudgeProblem', 'InfiniteModel']:
            results.append(compile_unit('Equation22591-'+stem,
                ROOT/'proofs/Equation22591'/(stem+'.lean'), build/(stem+'.olean'), build))
        assert len(results) == 58 and set(results[-1]['axioms']) == ENDPOINTS
        for record in exported['results']:
            if record['module'] in {'JudgeMagma-Magma', 'JudgeProblem', 'ExportWrapper'}:
                continue
            source = ROOT/record['source']
            assert sha(source) == record['sha256']
            results.append(compile_unit(record['module'], source, build/(source.stem+'.olean'), build))
        results.append(compile_unit('Equation22591-ExportWrapper', HERE/'ExportWrapper.lean',
                                    build/'ExportWrapper.olean', build))
    assert len(results) == 114 and set(results[-1]['axioms']) == ENDPOINTS
    hashes = {r['source']: r['sha256'] for r in results}
    for path in [CERTIFICATE, HERE/'export.py', HERE/'verify.py']:
        hashes[str(path.relative_to(ROOT))] = sha(path)
    summary = dict(status='passed', equation='Equation22591', source_law_proved=True,
        nontriviality_proved=True, explicit_nat_injection_proved=True,
        fresh_empty_build=True, reused_olean_files=False, temporary_build_removed=True,
        core_modules=58, additional_export_modules=56, total_compilations=114,
        monolithic_local_pass=False, lean_version='leanprover/lean4:v4.33.1',
        limits=dict(jobs=1, internal_memory_mib=192, rss_stop_mib=256, seconds_per_module=120),
        sampled_peak_rss_mib=max(r['sampled_peak_rss_mib'] for r in results),
        total_seconds=round(sum(r['elapsed_seconds'] for r in results), 3),
        certificate_sha256=sha(CERTIFICATE), source_hashes=hashes, results=results)
    (HERE/'summary.json').write_text(json.dumps(summary, indent=2)+'\n')
    return summary


def audit_local():
    summary = load(HERE/'summary.json')
    assert summary['status'] == 'passed' and len(summary['results']) == 114
    assert summary['source_law_proved'] and summary['explicit_nat_injection_proved']
    prefix, wrapper = export_parts()
    assert CERTIFICATE.read_text() == prefix+'\n'+wrapper+'\n'
    assert (HERE/'ExportWrapper.lean').read_text() == (
        'prelude\nimport JudgeProblem\nimport ExportLineageSyntaxModel\n'+wrapper+'\n')
    for p, digest in summary['source_hashes'].items():
        assert sha(ROOT/p) == digest, p
    for record in summary['results']:
        assert record['status'] == 'passed' and sha(ROOT/record['log']) == record['log_sha256']
        assert record['axioms'] == axiom_reports((ROOT/record['log']).read_text())
        assert all(set(a) <= ALLOWED for a in record['axioms'].values())
    for i in [57, 113]:
        assert set(summary['results'][i]['axioms']) == ENDPOINTS
        assert summary['results'][i]['axioms']['submission.CM.tower_injective'] == []
    return summary


def audit_remote():
    audit_local()
    folder = ROOT/'proofs/validation/aurora/Equation22591'
    payload, state, receipt, job = [load(folder/name) for name in
        ['request.json', 'submission-state.json', 'latest.json', 'job.json']]
    assert CERTIFICATE.read_bytes() == (folder/'certificate.lean').read_bytes() == payload['code'].encode()
    assert sha(CERTIFICATE) == state['certificate_sha256']
    digest = hashlib.sha256(json.dumps(payload, sort_keys=True, ensure_ascii=False).encode()).hexdigest()
    assert state['request_sha256'] == digest
    assert state['job_id'] == receipt['job_id'] == job['job_id']
    assert state['post_attempts'] == 1 and state['phase'] == 'terminal'
    assert receipt['status'] == 'done' and receipt['error'] is None
    assert receipt['result']['status'] == 'accepted' and receipt['result']['error_code'] == 'ACCEPTED'
    assert payload['verdict'] == receipt['result']['verdict'] == 'false' and payload['cache_mode'] == 'off'
    assert payload['problem'] == dict(id='order5-Equation22591-to-Equation2', eq1_id=22591, eq2_id=2,
        equation1='x = (y ◇ (y ◇ x)) ◇ ((x ◇ x) ◇ z)', equation2='x = y')
    assert set(receipt['result']['axioms']) <= ALLOWED
    return receipt


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compile', action='store_true')
    parser.add_argument('--remote', action='store_true')
    args = parser.parse_args()
    if args.compile:
        compile_all()
    summary = audit_local()
    result = dict(status='passed', core_modules=58, export_modules=56,
        sampled_peak_rss_mib=summary['sampled_peak_rss_mib'], seconds=summary['total_seconds'])
    if args.remote:
        receipt = audit_remote()
        result.update(remote_status='accepted', job_id=receipt['job_id'])
    print(json.dumps(result))


if __name__ == '__main__':
    main()

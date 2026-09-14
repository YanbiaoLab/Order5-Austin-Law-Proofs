"""Read-only audit of frozen sources, fresh builds, axioms, and model entries."""
import json
from pathlib import Path
import re
from verify import ROOT, HERE, ALLOWED, sha


def audit(check_index=True):
    manifest = HERE / 'summary.json'
    summary = json.loads(manifest.read_text())
    assert summary['status'] == 'passed' and summary['classification'] == 'nontrivial_infinite_model'
    assert summary['modules_checked'] == 129 and summary['core_modules'] == 125 and summary['core_endpoints'] == 311
    assert summary['reused_olean_files'] is False and summary['remote_judge_called'] is False
    build = Path(summary['fresh_build'])
    assert len(list(build.rglob('*.olean'))) == 129
    assert all(sha(ROOT / p) == digest for p,digest in summary['source_hashes'].items())
    core_endpoints = 0
    for r in summary['reports']:
        assert r['status'] == 'passed' and r['exit_code'] == 0
        assert r['memory_limit_mib'] == 256 and r['rss_limit_mib'] == 384 and r['peak_rss_mib'] <= 384
        assert '-j1' in r['command'] and '-M256' in r['command']
        assert all(Path(p) == build or Path(p).parent == build for p in r['lean_path'])
        assert sha(ROOT / r['source']) == r['sha256']
        log = ROOT / r['log']
        assert sha(log) == r['log_sha256']
        assert sha(Path(r['command'][r['command'].index('-o') + 1])) == r['olean_sha256']
        text = (ROOT / r['source']).read_text()
        assert set(re.findall(r'^#print axioms ([\w.]+)$', text, re.M)) == set(r['axioms'])
        assert all(set(v) <= ALLOWED for v in r['axioms'].values())
        assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b', text)
        assert 'sorryAx' not in log.read_text()
        if r['module'].startswith('Trace'):
            core_endpoints += len(r['axioms'])
    assert core_endpoints == 311
    final = next(r for r in summary['reports'] if r['module'] == 'TraceFullSource')
    assert {'Austin12087Trace.full_source_law', 'Austin12087Trace.infinite_model'} <= set(final['axioms'])
    entries = {r['equation']:r for r in json.loads((ROOT / 'proofs/index.json').read_text())['equations']}
    for eq in summary['equations']:
        assert entries[eq]['formula'] == summary['source_laws'][eq]
        result = next(r for r in summary['reports'] if r['module'] == eq + '-InfiniteModel')
        assert {'submission', 'submission.source_law', 'submission.CM.tower_injective'} <= set(result['axioms'])
        if check_index:
            entry = entries[eq]
            proof = entry['infinite_model_proof']
            assert proof['path'] == result['source'] and proof['sha256'] == result['sha256']
            deps = {p:d for p,d in summary['source_hashes'].items()
                    if p.startswith('proofs/Equation12087/Lean/') or p == f'proofs/{eq}/JudgeProblem.lean'}
            assert proof['dependencies'] == deps
            assert entry['explicit_infinity'] and entry['explicit_infinity_proof']['sha256'] == result['sha256']
            assert entry['model_compilation']['axioms'] == result['axioms']
            assert entry['model_compilation']['log_sha256'] == result['log_sha256']
            assert entry['model_compilation']['dependency_manifest'] == str(manifest.relative_to(ROOT))
    if check_index:
        index = json.loads((ROOT / 'proofs/index.json').read_text())
        form = index['local_formalizations']['eq12087']
        assert form['manifest_sha256'] == sha(manifest)
        assert form['equations'] == summary['equations']
    return summary


if __name__ == '__main__':
    audit()
    print('AUDIT PASS: both exact equations, nontriviality, Nat injection, full dependencies and index')

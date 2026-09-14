"""Register exactly the two verified E12087 model certificates."""
import json
from audit import audit
from verify import ROOT, HERE, sha


def main():
    summary = audit(check_index=False)
    manifest = HERE / 'summary.json'
    index_path = ROOT / 'proofs/index.json'
    before_sha = sha(index_path)
    index = json.loads(index_path.read_text())
    targets = set(summary['equations'])
    others_before = [r for r in index['equations'] if r['equation'] not in targets]
    report = str((HERE / 'README.md').relative_to(ROOT))
    for entry in index['equations']:
        eq = entry['equation']
        if eq not in targets:
            continue
        result = next(r for r in summary['reports'] if r['module'] == eq + '-InfiniteModel')
        deps = {p:d for p,d in summary['source_hashes'].items()
                if p.startswith('proofs/Equation12087/Lean/') or p == f'proofs/{eq}/JudgeProblem.lean'}
        entry['infinite_model_proof'] = dict(path=result['source'], sha256=result['sha256'],
            origin='local_formalization', validation='local_lean_recompiled_axioms_checked',
            source='Normal finite code trees over Nat; actual-origin decoding and complete height induction'
                   if eq == 'Equation12087' else 'Opposite operation of the Equation12087 normal-tree model',
            goal=f'Exact {eq}, nontriviality and an explicit injection from Nat',
            dependencies=deps, report=report)
        entry['explicit_infinity'] = True
        entry['local_lean_validation'] = 'passed_for_local_formalization'
        entry['explicit_infinity_proof'] = dict(path=result['source'], sha256=result['sha256'],
            theorem='submission.CM.tower_injective', validation='local_lean_recompiled_axioms_checked')
        entry['model_compilation'] = dict(status='passed', checked_sha256=result['sha256'],
            version=summary['version'], log=result['log'], log_sha256=result['log_sha256'],
            axioms=result['axioms'], elapsed_seconds=result['elapsed_seconds'],
            sampled_peak_rss_mib=result['peak_rss_mib'], dependency_manifest=str(manifest.relative_to(ROOT)))
        note = ('2026-09-14: 完整正规树模型及对偶通过；125 个核心模块与两条精确目标共 129 次空目录串行构建，'
                '原式、非平凡性、显式 Nat 单射均已核验。仅本地验证，未调用远端 Judge。')
        if note not in entry.setdefault('notes', []):
            entry['notes'].append(note)
    index.setdefault('local_formalizations', {})['eq12087'] = dict(status='passed',
        equations=summary['equations'], version=summary['version'], report=report,
        manifest=str(manifest.relative_to(ROOT)), manifest_sha256=sha(manifest))
    files = set(summary['source_hashes'])
    files.update(r['log'] for r in summary['reports'])
    files.update({report, str(manifest.relative_to(ROOT)), 'proofs/README.md',
        'proofs/Equation12087/README.md', 'proofs/Equation33884/README.md',
        'proofs/Equation12087/MODEL.zh-CN.md',
        'proofs/validation/eq12087-formal/audit.py', 'proofs/validation/eq12087-formal/record_index.py'})
    for name in files:
        index.setdefault('archived_files', {})[name] = sha(ROOT / name)
    index['updated_on'] = '2026-09-14'
    assert others_before == [r for r in index['equations'] if r['equation'] not in targets]
    assert sha(index_path) == before_sha, 'Inventory changed during preparation; rerun on latest state.'
    index_path.write_text(json.dumps(index, ensure_ascii=False, indent=2) + '\n')
    audit()
    print('REGISTERED: Equation12087 and Equation33884; other equation entries preserved')
    print('Current model certificates:', sum(bool(r.get('infinite_model_proof')) for r in index['equations']))


if __name__ == '__main__':
    main()

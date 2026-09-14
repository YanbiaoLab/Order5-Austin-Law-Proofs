"""Read-only audit scoped to the new E17286/E28626 model evidence."""
import json,re
from export_certificate import ROOT,HERE,FORMULAS,certificate_text,problem_text
from verify import sha,ALLOWED

def audit(check_index=True):
    manifest=HERE/'summary.json';s=json.loads(manifest.read_text())
    assert s['status']=='passed' and s['classification']=='nontrivial_infinite_model'
    assert s['modules_checked']==8 and len(s['reports'])==8
    assert s['fresh_directories']==3 and s['reused_olean_files'] is False
    assert s['remote_judge_called'] is False
    assert s['source_laws']=={str(n):v for n,v in FORMULAS.items()}
    assert len(s['source_hashes'])==8
    for rel,digest in s['source_hashes'].items():assert sha(ROOT/rel)==digest,rel
    for r in s['reports']:
        assert r['status']=='passed' and r['exit_code']==0
        assert sha(ROOT/r['source'])==r['sha256']
        assert sha(ROOT/r['log'])==r['log_sha256']
        log=(ROOT/r['log']).read_text()
        parsed={n:[] for n in re.findall(r"'([^']+)' does not depend on any axioms",log)}
        for n,used in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",log):
            parsed[n]=[a.strip() for a in used.split(',')]
        assert parsed==r['axioms'] and all(set(a)<=ALLOWED for a in parsed.values())
        assert 'sorryAx' not in log and 'error:' not in log
    index=json.loads((ROOT/'proofs/index.json').read_text())
    for n in FORMULAS:
        e=next(e for e in index['equations'] if e['equation']==f'Equation{n}')
        assert e['formula']==FORMULAS[n]
        folder=ROOT/f'proofs/Equation{n}'
        assert (folder/'JudgeProblem.lean').read_text()==problem_text(n)
        assert (folder/'InfiniteModel.lean').read_text()==certificate_text(n)
        for key in ['finite_proof']:
            assert sha(ROOT/e[key]['path'])==e[key]['sha256']
        fc=e['finite_compilation']
        assert fc['status']=='passed' and fc['checked_sha256']==e['finite_proof']['sha256']
        assert sha(ROOT/fc['log'])==fc['log_sha256']
        if check_index:
            mp=e['infinite_model_proof'];assert mp and e['explicit_infinity']
            assert sha(ROOT/mp['path'])==mp['sha256']
            assert e['model_compilation']['checked_sha256']==mp['sha256']
            assert sha(ROOT/e['model_compilation']['log'])==e['model_compilation']['log_sha256']
            assert e['explicit_infinity_proof']['theorem']=='submission.CM.tower_injective'
            for p,digest in mp['dependencies'].items():assert sha(ROOT/p)==digest
    if check_index:
        assert index['local_formalizations']['eq17286']['manifest_sha256']==sha(manifest)
        documents={'README.md','README.zh-CN.md','proofs/README.md',
                   'proofs/Equation17286/README.md','proofs/Equation28626/README.md',
                   'proofs/Equation17286/MODEL.zh-CN.md',
                   'proofs/Equation17286/ResearchRetrospective-2026-09-14.md'}
        for p,digest in index['archived_files'].items():
            if p in s['source_hashes'] or p in documents or p.startswith('proofs/validation/eq17286-formal/'):
                assert sha(ROOT/p)==digest,p
        for rel in documents|{'proofs/validation/eq17286-formal/README.md'}:
            p=ROOT/rel
            for target in re.findall(r'\]\(([^)]+)\)',p.read_text()):
                if '://' not in target and not target.startswith('#'):
                    assert (p.parent/target.split('#')[0]).exists(),(rel,target)
    return s

if __name__=='__main__':
    s=audit()
    print('PASS: both exact source laws, both Nat injections, eight fresh builds, allowed axioms, current model and historical finite certificate bindings.')

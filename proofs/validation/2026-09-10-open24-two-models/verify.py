"""Read-only audit of archived bytes and saved Judge receipts; no Lean run."""
from collections import Counter
import hashlib
import json
from pathlib import Path
import re

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
EXPECTED={
    20911:'eb3fa642caa3c0532a5060a09b216ca4fb984c45a1cc16c0eb5bf286d26ee185',
    25087:'c34100d47dd51620bb4d19e3b4241a191353886e20a4be7b7e8e6e41182c1441',
}

def load(path):
    return json.loads(path.read_text(encoding='utf-8'))

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def normalized(text):
    return re.sub(r'\s+','',text.replace('◇','*'))

def main():
    manifest=load(HERE/'manifest.json')
    assert manifest['count']==2 and {e['eq1_id'] for e in manifest['entries']}==set(EXPECTED)
    inventory=load(ROOT/'proofs/index.json');rows={r['equation']:r for r in inventory['equations']}
    checked=0
    for entry in manifest['entries']:
        eq=entry['eq1_id'];folder=ROOT/f'proofs/Equation{eq}'
        for file in entry['files']:
            path=(ROOT/file['path']).resolve()
            assert path.is_relative_to(ROOT) and path.stat().st_size==file['bytes'] and sha(path)==file['sha256'],file['path']
            checked+=1
        receipt=load(folder/'judge_acceptance.json');problem=load(folder/'problem.json');row=rows[f'Equation{eq}']
        assert receipt['record_kind']=='historical_judge_receipt_excerpt'
        for field in ('eq1_id','eq2_id','equation1','equation2'):
            assert receipt[field]==problem[field]==entry[field],(eq,field)
        assert receipt['eq1_id']==eq and receipt['eq2_id']==2 and receipt['equation2']=='x = y'
        assert receipt['status']=='accepted' and receipt['error_code']=='ACCEPTED' and receipt['verdict']=='false'
        assert receipt['certificate_sha256']==EXPECTED[eq]==sha(folder/'InfiniteModel.lean')
        assert receipt['certificate_bytes']==(folder/'InfiniteModel.lean').stat().st_size
        assert set(receipt['axioms']) <= {'Classical.choice','Quot.sound','propext'}
        assert receipt['source_receipt_sha256']==entry['source_receipt_sha256']
        assert row['table']=='20.3' and row['finite_proof'] is None and row['finite_math']=='未知'
        assert normalized(row['formula'])==normalized(problem['equation1'])
        assert row['infinite_model_proof']['sha256']==EXPECTED[eq] and row['explicit_infinity'] is True
        assert row['explicit_infinity_proof']['theorem']=='submission.CM.tower_injective'
        assert row['local_lean_validation']=='not_run_for_new_model_archive'
        module=(folder/'JudgeProblem.lean').read_text(encoding='utf-8')
        match=re.search(r'def EquationLHS.*?:=\s*∀[^,]+,\s*(.*?)\s*@\[reducible\]',module,re.S)
        assert match and normalized(match.group(1))==normalized(problem['equation1'])
        assert 'EquationLHS G ∧ ¬ EquationRHS G' in module
        code=(folder/'InfiniteModel.lean').read_text(encoding='utf-8')
        assert 'def submission : Goal := submission.CM.model' in code
        assert 'theorem tower_injective' in code and '#print axioms submission.CM.tower_injective' in code
    for path,expected in manifest['dependencies'].items():
        assert sha(ROOT/path)==expected;checked+=1
    assert Counter(r['table'] for r in rows.values())=={'20.1':10,'20.2':96,'20.3':24}
    assert sum(bool(r.get('infinite_model_proof')) for r in rows.values())==manifest['counts']['total_model_equations_after']==100
    assert sum(bool(r.get('explicit_infinity')) for r in rows.values())==72
    open24=[r for r in rows.values() if r['table']=='20.3']
    assert sum(bool(r.get('infinite_model_proof')) for r in open24)==4
    assert sum(bool(r.get('finite_proof')) for r in open24)==8
    print(f'PASS: 2 exact accepted certificates, source/target bindings, {checked} file/dependency hashes; inventory 100 models / 72 explicit infinity / 4 Table20.3 models. No new Lean/Judge run.')

if __name__=='__main__':
    main()

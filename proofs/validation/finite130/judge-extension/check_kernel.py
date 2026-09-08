"""Compile generated judge targets and inspect proofs in a fresh Lean module.

This validates the proposed renderer locally, not an Aurora acceptance.
Run with the proposed judge_v3_repl package first on PYTHONPATH.
"""
from pathlib import Path
import argparse
import hashlib
import json
import re
import sys
from types import SimpleNamespace

ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT/'scripts'))
import recompile_lean as compiler
from judge_v3_repl.common.proof_policy import ensure_stage2_official_problem_defaults
from judge_v3_repl.config import DEFAULT_STAGE2_JUDGE_REPO
from judge_v3_repl.official import load_official_verify_module
from judge_v3_repl.verifier import render_repl_problem_source

NONCE = 'f'*32


def wire_certificate(row, *, finite=True):
    original = (ROOT/row['finite_proof']['path']).read_text()
    imports = re.findall(r'^import .*$', original, re.M)
    body = re.sub(r'^import .*\n?', '', original, flags=re.M)
    body = re.sub(r'^#print axioms .*\n?', '', body, flags=re.M).strip()
    theorem = row['finite_proof'].get('theorem', f'InfModel.Finite.{row["equation"]}_implies_Equation2')
    return ('import JudgeProblem\n'+'\n'.join(imports)+'\n\n'
            'set_option linter.defProp false\nset_option linter.unusedVariables false\n'
            'set_option linter.unusedSimpArgs false\n\nnamespace submission\n\n'+body+
            '\n\nend submission\n\ndef submission : Goal := by\n'
            + ('  intro G inst hfin h\n' if finite else '  intro G inst h\n')
            + f'  exact submission.{theorem} G h\n')


def run_case(module, row, domain, *, unrelated=False):
    suffix = domain + ('-unrelated' if unrelated else '')
    label = row['equation']+'-'+suffix
    work = ROOT/'.build/judge-finite-extension/kernel'/label
    work.mkdir(parents=True, exist_ok=True)
    problem = {'id':label, 'eq1_id':1 if unrelated else int(row['equation'][8:]),
               'eq2_id':2, 'equation1':'x = x' if unrelated else row['formula'], 'equation2':'x = y'}
    problem = ensure_stage2_official_problem_defaults(problem, model_domain=domain)
    spec = module._parse_problem(problem)
    target = render_repl_problem_source(module, spec, SimpleNamespace(verdict='true'), model_domain=domain)
    (work/'JudgeProblem.lean').write_text(target)
    cert = wire_certificate(row, finite=domain=='finite')
    (work/'Submission.lean').write_text(cert)
    payload = dict(problem=problem, verdict='true', code=cert, model_domain=domain,
                   timeout_seconds=120, cache_mode='off')
    request_path = ROOT/'proofs/validation/finite130/judge-extension/requests'/(label+'.json')
    request_path.parent.mkdir(exist_ok=True)
    request_path.write_text(json.dumps(payload,ensure_ascii=False,indent=2)+'\n')
    paths = [work, ROOT/'.build/recompile/support', DEFAULT_STAGE2_JUDGE_REPO/'.lake/build/lib/lean',
             *sorted(DEFAULT_STAGE2_JUDGE_REPO.glob('.lake/packages/*/.lake/build/lib/lean'))]
    prep = compiler.compile_file(work/'JudgeProblem.lean', work, paths, label+'-goal', work/'JudgeProblem.olean')
    assert prep['status']=='passed', prep
    checked = compiler.compile_file(work/'Submission.lean', work, paths, label+'-submission', work/'Submission.olean')
    expected = domain=='finite' and not unrelated
    result = {'case':label, 'expected_compile_success':expected, 'submission_status':checked['status'],
              'target_source':target, 'finite_certificate':row['finite_proof']['path'],
              'finite_certificate_sha256':row['finite_proof']['sha256'],
              'request':str(request_path.relative_to(ROOT)),
              'request_sha256':hashlib.sha256(request_path.read_bytes()).hexdigest(),
              'submission_sha256':checked['source_sha256'], 'submitted_to_aurora':False}
    assert (checked['status']=='passed') == expected, result
    if expected:
        (work/'Check.lean').write_text('import Submission\nimport JudgeSupport.Inspect\n'
            f'def _judge_checked_{NONCE} : Goal := submission\n'
            f'#judge_report submission "{NONCE}"\n#judge_report _judge_checked_{NONCE} "{NONCE}"\n')
        audit = compiler.compile_file(work/'Check.lean', work, paths, label+'-audit')
        assert audit['status']=='passed', audit
        log = (ROOT/audit['log']).read_text()
        report = module._parse_report(log, NONCE)
        bad_axioms, bad_decls = module._policy_violations(report, spec.proof_policy)
        result.update(axioms=report['axioms'], direct_declarations=report['direct_declarations'],
                      bad_axioms=bad_axioms,bad_declarations=bad_decls)
        assert not bad_axioms, result
        assert not bad_decls, result
    else:
        result['rejection_log']=checked['log']
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--all',action='store_true')
    parser.add_argument('--equations', nargs='+')
    args=parser.parse_args()
    compiler.RUN = ROOT/'proofs/validation/finite130/judge-extension/kernel'
    compiler.MEMORY_MIB = 2048
    compiler.RSS_MIB = 3072
    rows = {r['equation']:r for r in json.loads((ROOT/'proofs/index.json').read_text())['equations']}
    module = load_official_verify_module(DEFAULT_STAGE2_JUDGE_REPO)
    selected = set(args.equations or [])
    summary_path = compiler.RUN / ('all-finite-summary.json' if args.all or selected else 'summary.json')
    results = json.loads(summary_path.read_text()) if selected and summary_path.exists() else []
    results = [r for r in results if r['case'].removesuffix('-finite') not in selected]
    cases = ([(r['equation'],'finite',False) for r in rows.values() if r['finite_proof'] and (not selected or r['equation'] in selected)] if args.all or selected else
             [('Equation5093','finite',False),('Equation5093','all',False),
              ('Equation5093','finite',True),('Equation27863','finite',False)])
    for position, (eq,domain,unrelated) in enumerate(cases, 1):
        result=run_case(module,rows[eq],domain,unrelated=unrelated)
        results.append(result)
        summary_path.write_text(json.dumps(results,ensure_ascii=False,indent=2)+'\n')
        print('CASE PASS:',result['case'],'checked',position,'/',len(cases),flush=True)


if __name__=='__main__':main()

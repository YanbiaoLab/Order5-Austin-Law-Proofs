"""Negative target controls and a genuine finite countermodel for the extension."""
from pathlib import Path
import json
from types import SimpleNamespace
import check_kernel as checks


def main():
    root=checks.ROOT
    compiler=checks.compiler
    compiler.RUN=root/'proofs/validation/finite130/judge-extension/kernel'
    compiler.MEMORY_MIB=2048
    compiler.RSS_MIB=3072
    module=checks.load_official_verify_module(checks.DEFAULT_STAGE2_JUDGE_REPO)
    rows={r['equation']:r for r in json.loads((root/'proofs/index.json').read_text())['equations']}
    results=[checks.run_case(module,rows['Equation5093'],'all'),
             checks.run_case(module,rows['Equation5093'],'finite',unrelated=True)]
    work=root/'.build/judge-finite-extension/kernel/finite-false-Bool'
    work.mkdir(parents=True,exist_ok=True)
    problem=checks.ensure_stage2_official_problem_defaults(
        dict(id='finite-false-Bool',eq1_id=1,eq2_id=2,equation1='x = x',equation2='x = y'),
        model_domain='finite',
    )
    spec=module._parse_problem(problem)
    target=checks.render_repl_problem_source(module,spec,SimpleNamespace(verdict='false'),model_domain='finite')
    (work/'JudgeProblem.lean').write_text(target)
    (work/'Submission.lean').write_text('''import JudgeProblem
import Mathlib.Data.Fintype.Card

namespace submission

def finite_bool_model : Goal := by
  refine ⟨Bool, ⟨fun x _ => x⟩, (by infer_instance), ?_, ?_⟩
  · intro x
    rfl
  · intro h
    have he : true = false := h true false
    exact Bool.noConfusion he

end submission

def submission : Goal := submission.finite_bool_model
''')
    paths=[work,root/'.build/recompile/support',checks.DEFAULT_STAGE2_JUDGE_REPO/'.lake/build/lib/lean',
           *sorted(checks.DEFAULT_STAGE2_JUDGE_REPO.glob('.lake/packages/*/.lake/build/lib/lean'))]
    for filename in ['JudgeProblem','Submission']:
        result=compiler.compile_file(work/(filename+'.lean'),work,paths,'finite-false-Bool-'+filename,work/(filename+'.olean'))
        assert result['status']=='passed',result
    nonce=checks.NONCE
    (work/'Check.lean').write_text('import Submission\nimport JudgeSupport.Inspect\n'
        f'def _judge_checked_{nonce} : Goal := submission\n'
        f'#judge_report submission "{nonce}"\n#judge_report _judge_checked_{nonce} "{nonce}"\n')
    result=compiler.compile_file(work/'Check.lean',work,paths,'finite-false-Bool-audit')
    assert result['status']=='passed',result
    report=module._parse_report((root/result['log']).read_text(),nonce)
    bad_axioms,bad_decls=module._policy_violations(report,spec.proof_policy)
    assert not bad_axioms and not bad_decls,(bad_axioms,bad_decls)
    results.append(dict(case='finite-false-Bool',status='passed',verdict='false',model_domain='finite',
                        target_source=target,axioms=report['axioms'],direct_declarations=report['direct_declarations'],
                        submitted_to_aurora=False))
    (compiler.RUN/'controls-summary.json').write_text(json.dumps(results,ensure_ascii=False,indent=2)+'\n')
    print('PASS: finite-only proof rejected for all-model and unrelated targets; finite Bool countermodel accepted locally.')


if __name__=='__main__':main()

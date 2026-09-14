"""Build independent exact-goal certificates from the four tree modules."""
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
MODULES = ['TreeSchema','TreeBounds','TreeGeometry','TreeModel']
FORMULAS = {
    17286: 'x = (y ◇ x) ◇ (z ◇ (z ◇ (x ◇ z)))',
    28626: 'x = (((y ◇ x) ◇ y) ◇ y) ◇ (x ◇ z)',
}

def problem_text(number):
    return '''prelude
import Init.Classical

class Magma (G : Type _) where
  op : G → G → G
infix:65 " ◇ " => Magma.op

/- Exact local target reconstructed from the inventory; not a remote receipt. -/
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop :=
  ∀ x y z : G, ''' + FORMULAS[number] + '''
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop :=
  ∀ x y : G, x = y
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G
'''

def certificate_text(number):
    header = '''prelude
import JudgeProblem
import Init.Classical
import Init.Data.Nat.Basic
import Init.WF
set_option autoImplicit false
set_option Elab.async false

/- Complete nontrivial infinite tree model. Local Lean verification only.
   Reproduce: python3 proofs/validation/eq17286-formal/verify.py -/
'''
    body=[]
    for name in MODULES:
        source=(ROOT/'proofs/Equation17286'/f'{name}.lean').read_text()
        kept=[line for line in source.splitlines()
              if line!='prelude' and not line.startswith(('import ','#print '))]
        body.append(f'\n/- Module: {name} -/\n'+'\n'.join(kept).replace(
            'Equation17286Tree','submission.Equation17286Tree'))
    op='op' if number==17286 else 'dualOp'
    law='source_law_explicit' if number==17286 else 'dual_source_law_explicit'
    inf='infinite_model' if number==17286 else 'dual_infinite_model'
    footer=f'''

namespace submission
abbrev CM := Equation17286Tree.Tree
noncomputable instance modelMagma : Magma CM := ⟨Equation17286Tree.{op}⟩
namespace CM
theorem tower_injective (m n : Nat)
    (h : Equation17286Tree.Tree.atom m = Equation17286Tree.Tree.atom n) : m = n :=
  Equation17286Tree.atom_injective m n h
end CM
end submission

theorem submission : Goal := by
  refine ⟨submission.CM, submission.modelMagma, ?_, ?_⟩
  · exact submission.Equation17286Tree.{law}
  · intro h
    exact Nat.noConfusion (submission.Equation17286Tree.Tree.atom.inj
      (h (submission.Equation17286Tree.Tree.atom 0) (submission.Equation17286Tree.Tree.atom 1)))

example : Goal := submission
example (x y z : submission.CM) : {FORMULAS[number]} :=
  submission.Equation17286Tree.{law} x y z

#print axioms submission
#print axioms submission.CM.tower_injective
#print axioms submission.Equation17286Tree.{inf}
'''
    return header+'\n'.join(body)+footer

if __name__=='__main__':
    index=json.loads((ROOT/'proofs/index.json').read_text())
    for number in FORMULAS:
        entry=next(e for e in index['equations'] if e['equation']==f'Equation{number}')
        assert entry['formula']==FORMULAS[number]
        folder=ROOT/f'proofs/Equation{number}'
        (folder/'JudgeProblem.lean').write_text(problem_text(number))
        (folder/'InfiniteModel.lean').write_text(certificate_text(number))
    print('Generated both independent certificates and exact local targets.')

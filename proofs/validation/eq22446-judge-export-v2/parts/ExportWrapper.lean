prelude
import JudgeProblem
import ExportLineageSyntaxModel
set_option autoImplicit false
set_option Elab.async false

namespace submission
abbrev CM := submission.Equation22446Lineage.NormalTree
noncomputable instance modelMagma : Magma CM := ⟨submission.Equation22446Lineage.multiplication⟩

namespace CM
theorem tower_injective (m n : Nat)
    (h : submission.Equation22446Lineage.normalTower m = submission.Equation22446Lineage.normalTower n) : m = n :=
  submission.Equation22446Lineage.normalTower_injective h
end CM

theorem source_law : EquationLHS CM := submission.Equation22446Lineage.equation22446
theorem nontrivial : ¬ EquationRHS CM := submission.Equation22446Lineage.model_nontrivial
end submission

theorem submission : Goal :=
  ⟨submission.CM,submission.modelMagma,submission.source_law,submission.nontrivial⟩

#print axioms submission
#print axioms submission.source_law
#print axioms submission.nontrivial
#print axioms submission.CM.tower_injective
#print axioms submission.Equation22446Lineage.infinite_model

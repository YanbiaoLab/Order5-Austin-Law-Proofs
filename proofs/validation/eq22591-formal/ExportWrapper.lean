prelude
import JudgeProblem
import ExportLineageSyntaxModel
set_option autoImplicit false
set_option Elab.async false

namespace submission
abbrev CM := submission.Equation22446Lineage.NormalTree

noncomputable instance modelMagma : Magma CM :=
  ⟨fun a b => submission.Equation22446Lineage.multiplication b a⟩

namespace CM
theorem tower_injective (m n : Nat)
    (h : submission.Equation22446Lineage.normalTower m = submission.Equation22446Lineage.normalTower n) : m = n :=
  submission.Equation22446Lineage.normalTower_injective h
end CM

theorem source_law : EquationLHS CM := by
  intro x y z
  exact submission.Equation22446Lineage.equation22446 x z y

theorem nontrivial : ¬ EquationRHS CM := submission.Equation22446Lineage.model_nontrivial

theorem infinite_model : EquationLHS CM ∧ (¬ EquationRHS CM) ∧
    (∀ m n : Nat,
      submission.Equation22446Lineage.normalTower m = submission.Equation22446Lineage.normalTower n → m = n) :=
  ⟨source_law,nontrivial,CM.tower_injective⟩
end submission

theorem submission : Goal :=
  ⟨submission.CM,submission.modelMagma,submission.source_law,submission.nontrivial⟩

#print axioms submission
#print axioms submission.source_law
#print axioms submission.nontrivial
#print axioms submission.CM.tower_injective
#print axioms submission.infinite_model

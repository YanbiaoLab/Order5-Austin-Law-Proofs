prelude
import JudgeProblem
import LineageSyntax.Model
set_option autoImplicit false
set_option Elab.async false

namespace submission
abbrev CM := Equation22446Lineage.NormalTree
noncomputable instance : Magma CM := ⟨Equation22446Lineage.multiplication⟩

namespace CM
theorem tower_injective (m n : Nat)
    (h : Equation22446Lineage.normalTower m = Equation22446Lineage.normalTower n) : m = n :=
  Equation22446Lineage.normalTower_injective h
end CM

theorem source_law : EquationLHS CM := Equation22446Lineage.equation22446
theorem nontrivial : ¬ EquationRHS CM := Equation22446Lineage.model_nontrivial
end submission

theorem submission : Goal :=
  ⟨submission.CM,inferInstance,submission.source_law,submission.nontrivial⟩

#print axioms submission
#print axioms submission.source_law
#print axioms submission.nontrivial
#print axioms submission.CM.tower_injective
#print axioms Equation22446Lineage.infinite_model

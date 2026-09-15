prelude
import Init.Classical
import Init.Data.Nat.Lemmas
import Init.RCases
import ExportLineageSyntaxPrincipalUnique
set_option Elab.async false
set_option autoImplicit false
set_option Elab.async false

namespace submission.Equation22446Lineage

 
theorem equation22446 (x y z : NormalTree) :
    x = multiplication (multiplication y (multiplication x x))
      (multiplication (multiplication x z) z) :=
  source_with_principal_unique principal_unique x y z

theorem normalTower_nontrivial : normalTower 0 ≠ normalTower 1 := by
  intro h
  cases normalTower_injective h

theorem model_nontrivial : ¬ ∀ x y : NormalTree, x = y := by
  intro h
  exact normalTower_nontrivial (h (normalTower 0) (normalTower 1))

 
theorem infinite_model :
    (∀ x y z : NormalTree,
      x = multiplication (multiplication y (multiplication x x))
        (multiplication (multiplication x z) z)) ∧
    (¬ ∀ x y : NormalTree, x = y) ∧
    (∀ {m n : Nat}, normalTower m = normalTower n → m = n) :=
  ⟨equation22446,model_nontrivial,normalTower_injective⟩

end submission.Equation22446Lineage

prelude
import LineageSyntax.PrincipalUnique
set_option autoImplicit false
set_option Elab.async false

namespace Equation22446Lineage

/-- The exact source equation, with every construction obligation discharged. -/
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

/-- Source, nontriviality, and an explicit injection of Nat into the same carrier. -/
theorem infinite_model :
    (∀ x y z : NormalTree,
      x = multiplication (multiplication y (multiplication x x))
        (multiplication (multiplication x z) z)) ∧
    (¬ ∀ x y : NormalTree, x = y) ∧
    (∀ {m n : Nat}, normalTower m = normalTower n → m = n) :=
  ⟨equation22446,model_nontrivial,normalTower_injective⟩

#print axioms equation22446
#print axioms normalTower_nontrivial
#print axioms model_nontrivial
#print axioms infinite_model
end Equation22446Lineage

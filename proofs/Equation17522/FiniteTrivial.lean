import Mathlib.Data.Fintype.Card
import JudgeMagma.Magma

@[reducible] def Equation2 (G : Type _) [Magma G] : Prop := ∀ (x y : G), x = y
@[reducible] def Equation28770 (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (((y ◇ y) ◇ y) ◇ x) ◇ (y ◇ z)

namespace InfModel

theorem Finite.Equation28770_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation28770 G) :
    Equation2 G := by
  have : ∀ (y z u : G), y ◇ z = y ◇ u := by
    intro y
    let f (x : G) := ((y ◇ y) ◇ y) ◇ x
    let g (x : G) := x ◇ (y ◇ y)
    have : Function.RightInverse f g := fun _ ↦ by simp [f, g, ← h]
    apply fun _ _ ↦ this.injective _
    obtain ⟨finv, hf⟩ := (Finite.surjective_of_injective this.injective).hasRightInverse
    let fy := finv ((y ◇ y) ◇ y)
    replace hf : ((y ◇ y) ◇ y) ◇ fy = (y ◇ y) ◇ y := hf _
    have := h fy y
    simp only [hf] at this
    simp [f, ← this]
  intro x u
  have y := x
  have z := x
  rw [h x y z, this ((y ◇ y) ◇ y)  x u, ← this ((y ◇ y) ◇ y) u u, ← h]

end InfModel

@[reducible] def Equation17522 (G : Type _) [Magma G] : Prop := ∀ (x y z : G), x = (y ◇ z) ◇ (x ◇ (z ◇ (z ◇ z)))

theorem finite_trivial_dual (G : Type*) [Magma G] [Finite G] (h : Equation17522 G) : Equation2 G := by
  let opposite : Magma G := ⟨fun x y => y ◇ x⟩
  have hd : @Equation28770 G opposite := by
    intro x y z
    exact h x z y
  exact @InfModel.Finite.Equation28770_implies_Equation2 G opposite inferInstance hd

#print axioms finite_trivial_dual

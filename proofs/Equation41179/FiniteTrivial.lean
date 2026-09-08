import Mathlib.Data.Fintype.Card
import JudgeMagma.Magma

@[reducible] def Equation2 (G : Type _) [Magma G] : Prop := ∀ (x y : G), x = y
@[reducible] def Equation5093 (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ (y ◇ (y ◇ (x ◇ (z ◇ y))))

namespace InfModel

theorem Finite.Equation5093_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation5093 G) :
    Equation2 G:= by
  intro x y
  let f (y w : G) := y ◇ w
  have f_onto : ∀ y : G, Function.Surjective (f y) := by
    intro y x
    use (y ◇ (y ◇ (x ◇ (x ◇ y))))
    dsimp [f]
    rw [← h]
  have f_inj : ∀ y : G, Function.Injective (f y) :=
    fun _ ↦ Finite.injective_iff_surjective.mpr (f_onto _)
  have hh : ∀ y z w : G, z ◇ y = w ◇ y := by
    intro y z w
    let g := f y
    exact f_inj x (f_inj y (f_inj y (f_inj y (by dsimp [g, f]; rw [← h, ← h]))))
  have hhh : ∀ a b c d: G, c ◇ (a ◇ b) = d ◇ (a ◇ b) := fun _ _ _ _  ↦ hh ..
  have hhhh : ∀ a b: G, b ◇ (b ◇ (b ◇ (x ◇ (a ◇ b)))) = b ◇ (b ◇ (b ◇ (y ◇ (a ◇ b)))) := by
    intro a b
    rw [hhh a b]
  calc
    x = x ◇ (x ◇ (x ◇ (x ◇ (x ◇ x)))) := h x x x
    _= x ◇ (x ◇ (x ◇ (y ◇ (x ◇ x)))) := by rw [hhhh]
    _= y := by rw [← h y x x]

end InfModel

@[reducible] def Equation41179 (G : Type _) [Magma G] : Prop := ∀ (x y z : G), x = ((((y ◇ z) ◇ x) ◇ y) ◇ y) ◇ y

theorem finite_trivial_dual (G : Type*) [Magma G] [Finite G] (h : Equation41179 G) : Equation2 G := by
  let opposite : Magma G := ⟨fun x y => y ◇ x⟩
  have hd : @ Equation5093 G opposite := by
    intro x y z
    exact h x y z
  exact @ InfModel.Finite.Equation5093_implies_Equation2 G opposite inferInstance hd

#print axioms finite_trivial_dual

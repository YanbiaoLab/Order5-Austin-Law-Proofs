import Mathlib.Data.Fintype.Card
import JudgeMagma.Magma

@[reducible] def Equation2 (G : Type _) [Magma G] : Prop := ∀ (x y : G), x = y
@[reducible] def Equation12883 (G : Type _) [Magma G] : Prop := ∀ (x y z : G), x = y ◇ ((x ◇ (z ◇ (y ◇ x))) ◇ y)

theorem finite_trivial (G : Type*) [Magma G] [Finite G] (h : Equation12883 G) : Equation2 G := by
  intro a b
  have li (y : G) : Function.Injective (fun t : G => y ◇ t) := by
    apply Finite.injective_iff_surjective.mpr
    intro x
    exact ⟨((x ◇ (a ◇ (y ◇ x))) ◇ y), (h x y a).symm⟩
  have ri (t : G) : Function.Injective (fun w : G => w ◇ t) := by
    have ti : Function.Injective (fun x : G => ((x ◇ (a ◇ (t ◇ x))) ◇ t)) := by
      intro u v huv
      change ((u ◇ (a ◇ (t ◇ u))) ◇ t) = ((v ◇ (a ◇ (t ◇ v))) ◇ t) at huv
      calc u = (t ◇ ((u ◇ (a ◇ (t ◇ u))) ◇ t)) := h u t a
           _ = (t ◇ ((v ◇ (a ◇ (t ◇ v))) ◇ t)) := by rw [huv]
           _ = v := (h v t a).symm
    apply Finite.injective_iff_surjective.mpr
    intro u
    obtain ⟨x, hx⟩ := (Finite.injective_iff_surjective.mp ti) u
    exact ⟨(x ◇ (a ◇ (t ◇ x))), hx⟩
  exact ri (a ◇ a) (li a (ri a (li a ((h a a a).symm.trans (h a a b)))))

#print axioms finite_trivial

import Mathlib.Data.Fintype.Card
import JudgeMagma.Magma

@[reducible] def Equation2 (G : Type _) [Magma G] : Prop := ∀ (x y : G), x = y
@[reducible] def Equation13992 (G : Type _) [Magma G] : Prop := ∀ (x y z : G), x = y ◇ ((z ◇ ((x ◇ y) ◇ y)) ◇ y)

theorem finite_trivial (G : Type*) [Magma G] [Finite G] (h : Equation13992 G) : Equation2 G := by
  intro a b
  have li (y : G) : Function.Injective (fun t : G => y ◇ t) := by
    apply Finite.injective_iff_surjective.mpr
    intro x
    exact ⟨((a ◇ ((x ◇ y) ◇ y)) ◇ y), (h x y a).symm⟩
  have ri (t : G) : Function.Injective (fun w : G => w ◇ t) := by
    have ti : Function.Injective (fun x : G => ((a ◇ ((x ◇ t) ◇ t)) ◇ t)) := by
      intro u v huv
      change ((a ◇ ((u ◇ t) ◇ t)) ◇ t) = ((a ◇ ((v ◇ t) ◇ t)) ◇ t) at huv
      calc u = (t ◇ ((a ◇ ((u ◇ t) ◇ t)) ◇ t)) := h u t a
           _ = (t ◇ ((a ◇ ((v ◇ t) ◇ t)) ◇ t)) := by rw [huv]
           _ = v := (h v t a).symm
    apply Finite.injective_iff_surjective.mpr
    intro u
    obtain ⟨x, hx⟩ := (Finite.injective_iff_surjective.mp ti) u
    exact ⟨(a ◇ ((x ◇ t) ◇ t)), hx⟩
  exact ri ((a ◇ a) ◇ a) (ri a (li a ((h a a a).symm.trans (h a a b))))

#print axioms finite_trivial

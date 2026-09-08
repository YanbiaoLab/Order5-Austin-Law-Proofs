import Mathlib.Data.Fintype.Card
import JudgeMagma.Magma

@[reducible] def Equation2 (G : Type _) [Magma G] : Prop := ∀ (x y : G), x = y
@[reducible] def Equation7701 (G : Type _) [Magma G] : Prop := ∀ (x y z : G), x = y ◇ (y ◇ ((x ◇ (z ◇ x)) ◇ y))

theorem finite_trivial (G : Type*) [Magma G] [Finite G] (h : Equation7701 G) : Equation2 G := by
  intro a b
  have li (y : G) : Function.Injective (fun t : G => y ◇ t) := by
    apply Finite.injective_iff_surjective.mpr
    intro x
    exact ⟨(y ◇ ((x ◇ (a ◇ x)) ◇ y)), (h x y a).symm⟩
  have ri (t : G) : Function.Injective (fun w : G => w ◇ t) := by
    have ti : Function.Injective (fun x : G => ((x ◇ (a ◇ x)) ◇ t)) := by
      intro u v huv
      change ((u ◇ (a ◇ u)) ◇ t) = ((v ◇ (a ◇ v)) ◇ t) at huv
      calc u = (t ◇ (t ◇ ((u ◇ (a ◇ u)) ◇ t))) := h u t a
           _ = (t ◇ (t ◇ ((v ◇ (a ◇ v)) ◇ t))) := by rw [huv]
           _ = v := (h v t a).symm
    apply Finite.injective_iff_surjective.mpr
    intro u
    obtain ⟨x, hx⟩ := (Finite.injective_iff_surjective.mp ti) u
    exact ⟨(x ◇ (a ◇ x)), hx⟩
  exact ri a (li a (ri a (li a (li a ((h a a a).symm.trans (h a a b))))))

@[reducible] def Equation38303 (G : Type _) [Magma G] : Prop := ∀ (x y z : G), x = ((y ◇ ((x ◇ z) ◇ x)) ◇ y) ◇ y

theorem finite_trivial_dual (G : Type*) [Magma G] [Finite G] (h : Equation38303 G) : Equation2 G := by
  let opposite : Magma G := ⟨fun x y => y ◇ x⟩
  have hd : @ Equation7701 G opposite := by
    intro x y z
    exact h x y z
  exact @ finite_trivial G opposite inferInstance hd

#print axioms finite_trivial_dual

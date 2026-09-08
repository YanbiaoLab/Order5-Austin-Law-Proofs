import Mathlib.Data.Fintype.Card
import JudgeMagma.Magma

@[reducible] def Equation2 (G : Type _) [Magma G] : Prop := ∀ (x y : G), x = y
@[reducible] def Equation6820 (G : Type _) [Magma G] : Prop := ∀ (x y z : G), x = y ◇ (y ◇ ((x ◇ y) ◇ (z ◇ y)))

theorem finite_trivial (G : Type*) [Magma G] [Finite G] (h : Equation6820 G) : Equation2 G := by
  intro a b
  have li (y : G) : Function.Injective (fun t : G => y ◇ t) := by
    apply Finite.injective_iff_surjective.mpr
    intro x
    exact ⟨(y ◇ ((x ◇ y) ◇ (a ◇ y))), (h x y a).symm⟩
  have ri (t : G) : Function.Injective (fun w : G => w ◇ t) := by
    have ti : Function.Injective (fun x : G => (x ◇ t)) := by
      intro u v huv
      change (u ◇ t) = (v ◇ t) at huv
      calc u = (t ◇ (t ◇ ((u ◇ t) ◇ (a ◇ t)))) := h u t a
           _ = (t ◇ (t ◇ ((v ◇ t) ◇ (a ◇ t)))) := by rw [huv]
           _ = v := (h v t a).symm
    apply Finite.injective_iff_surjective.mpr
    intro u
    obtain ⟨x, hx⟩ := (Finite.injective_iff_surjective.mp ti) u
    exact ⟨x, hx⟩
  exact ri a (li (a ◇ a) (li a (li a ((h a a a).symm.trans (h a a b)))))

@[reducible] def Equation39485 (G : Type _) [Magma G] : Prop := ∀ (x y z : G), x = (((y ◇ z) ◇ (y ◇ x)) ◇ y) ◇ y

theorem finite_trivial_dual (G : Type*) [Magma G] [Finite G] (h : Equation39485 G) : Equation2 G := by
  let opposite : Magma G := ⟨fun x y => y ◇ x⟩
  have hd : @ Equation6820 G opposite := by
    intro x y z
    exact h x y z
  exact @ finite_trivial G opposite inferInstance hd

#print axioms finite_trivial_dual

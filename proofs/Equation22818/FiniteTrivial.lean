import Mathlib.Data.Fintype.Card
import JudgeMagma.Magma

@[reducible] def Equation2 (G : Type _) [Magma G] : Prop := ∀ (x y : G), x = y
@[reducible] def Equation22455 (G : Type _) [Magma G] : Prop := ∀ (x y z : G), x = (y ◇ (x ◇ x)) ◇ ((y ◇ z) ◇ y)

theorem finite_trivial (G : Type*) [Magma G] [Finite G] (h : Equation22455 G) : Equation2 G := by
  intro a b
  have si : Function.Injective (fun x : G => x ◇ x) := by
    intro u v huv
    change u ◇ u = v ◇ v at huv
    calc
      u = (a ◇ (u ◇ u)) ◇ ((a ◇ a) ◇ a) := h u a a
      _ = (a ◇ (v ◇ v)) ◇ ((a ◇ a) ◇ a) := by rw [huv]
      _ = v := (h v a a).symm
  have ss := Finite.surjective_of_injective si
  have li (y : G) : Function.Injective (fun t : G => y ◇ t) := by
    intro u v huv
    obtain ⟨p, hp⟩ := ss u
    obtain ⟨q, hq⟩ := ss v
    change p ◇ p = u at hp
    change q ◇ q = v at hq
    change y ◇ u = y ◇ v at huv
    have hpq : p = q := by
      calc
        p = (y ◇ (p ◇ p)) ◇ ((y ◇ a) ◇ y) := h p y a
        _ = (y ◇ (q ◇ q)) ◇ ((y ◇ a) ◇ y) := by rw [hp, hq, huv]
        _ = q := (h q y a).symm
    rw [← hp, ← hq, hpq]
  have ri (y z w : G) : (y ◇ z) ◇ y = (y ◇ w) ◇ y := by
    apply li (y ◇ (a ◇ a))
    exact (h a y z).symm.trans (h a y w)
  have independent (u v t : G) : u ◇ t = v ◇ t := by
    obtain ⟨z, hz⟩ := Finite.surjective_of_injective (li t) u
    obtain ⟨w, hw⟩ := Finite.surjective_of_injective (li t) v
    rw [← hz, ← hw]
    exact ri t z w
  calc
    a = (a ◇ (a ◇ a)) ◇ ((a ◇ a) ◇ a) := h a a a
    _ = (a ◇ (b ◇ b)) ◇ ((a ◇ a) ◇ a) := independent _ _ _
    _ = b := (h b a a).symm


@[reducible] def Equation22818 (G : Type _) [Magma G] : Prop := ∀ (x y z : G), x = (y ◇ (z ◇ y)) ◇ ((x ◇ x) ◇ y)

theorem finite_trivial_dual (G : Type*) [Magma G] [Finite G] (h : Equation22818 G) : Equation2 G := by
  let opposite : Magma G := ⟨fun x y => y ◇ x⟩
  have hd : @Equation22455 G opposite := by
    intro x y z
    exact h x y z
  exact @finite_trivial G opposite inferInstance hd

#print axioms finite_trivial_dual

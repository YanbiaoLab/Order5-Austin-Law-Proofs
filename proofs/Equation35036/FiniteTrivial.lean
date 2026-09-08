import Mathlib.Data.Fintype.Card
import JudgeMagma.Magma

@[reducible] def Equation2 (G : Type _) [Magma G] : Prop := ∀ (x y : G), x = y
@[reducible] def Equation11081 (G : Type _) [Magma G] : Prop := ∀ (x y z : G), x = y ◇ ((x ◇ (y ◇ x)) ◇ (z ◇ y))

theorem finite_trivial (G : Type*) [Magma G] [Finite G] (h : Equation11081 G) : Equation2 G := by
  intro a b
  have li (y : G) : Function.Injective (fun t : G => y ◇ t) := by
    apply Finite.injective_iff_surjective.mpr
    intro x
    exact ⟨((x ◇ (y ◇ x)) ◇ (a ◇ y)), (h x y a).symm⟩
  have ind (u v y : G) : u ◇ y = v ◇ y := by
    exact li (a ◇ (y ◇ a)) (li y ((h a y u).symm.trans (h a y v)))
  exact (h a a a).trans (((congrArg (fun t : G => a ◇ t) (ind (a ◇ (a ◇ a)) (b ◇ (a ◇ b)) (a ◇ a))).trans (ind a a ((b ◇ (a ◇ b)) ◇ (a ◇ a)))).trans (h b a a).symm)

@[reducible] def Equation35036 (G : Type _) [Magma G] : Prop := ∀ (x y z : G), x = ((y ◇ z) ◇ ((x ◇ y) ◇ x)) ◇ y

theorem finite_trivial_dual (G : Type*) [Magma G] [Finite G] (h : Equation35036 G) : Equation2 G := by
  let opposite : Magma G := ⟨fun x y => y ◇ x⟩
  have hd : @ Equation11081 G opposite := by
    intro x y z
    exact h x y z
  exact @ finite_trivial G opposite inferInstance hd

#print axioms finite_trivial_dual

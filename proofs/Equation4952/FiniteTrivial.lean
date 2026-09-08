import Mathlib.Data.Fintype.Card
import JudgeMagma.Magma

@[reducible] def Equation2 (G : Type _) [Magma G] : Prop := ∀ (x y : G), x = y
@[reducible] def Equation4952 (G : Type _) [Magma G] : Prop := ∀ (x y z : G), x = y ◇ (x ◇ (y ◇ (y ◇ (z ◇ y))))

theorem finite_trivial (G : Type*) [Magma G] [Finite G] (h : Equation4952 G) : Equation2 G := by
  intro a b
  have li (y : G) : Function.Injective (fun t : G => y ◇ t) := by
    apply Finite.injective_iff_surjective.mpr
    intro x
    exact ⟨(x ◇ (y ◇ (y ◇ (a ◇ y)))), (h x y a).symm⟩
  have ind (u v y : G) : u ◇ y = v ◇ y := by
    exact li y (li y (li a (li y ((h a y u).symm.trans (h a y v)))))
  exact (h a a a).trans (((congrArg (fun t : G => a ◇ t) (ind a b (a ◇ (a ◇ (a ◇ a))))).trans (ind a a (b ◇ (a ◇ (a ◇ (a ◇ a)))))).trans (h b a a).symm)

#print axioms finite_trivial

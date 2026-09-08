import Mathlib.Data.Fintype.Card
import JudgeMagma.Magma

@[reducible] def Equation2 (G : Type _) [Magma G] : Prop := ∀ (x y : G), x = y
@[reducible] def Equation5066 (G : Type _) [Magma G] : Prop := ∀ (x y z : G), x = y ◇ (y ◇ (x ◇ (y ◇ (z ◇ y))))

theorem finite_trivial (G : Type*) [Magma G] [Finite G] (h : Equation5066 G) : Equation2 G := by
  intro a b
  have li (y : G) : Function.Injective (fun t : G => y ◇ t) := by
    apply Finite.injective_iff_surjective.mpr
    intro x
    exact ⟨(y ◇ (x ◇ (y ◇ (a ◇ y)))), (h x y a).symm⟩
  have ind (u v y : G) : u ◇ y = v ◇ y := by
    exact li y (li a (li y (li y ((h a y u).symm.trans (h a y v)))))
  exact (h a a a).trans (((congrArg (fun t : G => a ◇ t) ((congrArg (fun t : G => a ◇ t) (ind a b (a ◇ (a ◇ a)))).trans (ind a a (b ◇ (a ◇ (a ◇ a)))))).trans (ind a a (a ◇ (b ◇ (a ◇ (a ◇ a)))))).trans (h b a a).symm)

#print axioms finite_trivial

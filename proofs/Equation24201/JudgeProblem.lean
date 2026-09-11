import JudgeMagma.Magma
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop :=
  ∀ (x y z w : G), x = ((y ◇ x) ◇ x) ◇ ((x ◇ z) ◇ w)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x y : G), x = y
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G

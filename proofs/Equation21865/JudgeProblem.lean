import JudgeMagma.Magma
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop :=
  ∀ (x y z : G), x = (y ◇ (z ◇ x)) ◇ (x ◇ (x ◇ z))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x y : G), x = y
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G

import JudgeMagma.Magma

-- Reconstructed from the frozen paper input; not an archived Judge module.
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop :=
  ∀ (x y z : G), x = y ◇ ((z ◇ y) ◇ (y ◇ (x ◇ y)))

@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop :=
  ∀ (x y : G), x = y

abbrev Goal : Prop :=
  ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G

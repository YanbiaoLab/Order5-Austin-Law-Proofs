import JudgeMagma.Magma

-- Reconstructed from the exact submitted problem, not a server-returned file.
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop :=
  ∀ (x y z : G), x = y ◇ (x ◇ (y ◇ ((z ◇ x) ◇ z)))

@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop :=
  ∀ (x y : G), x = y

abbrev Goal : Prop :=
  ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G

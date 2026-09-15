prelude
import JudgeMagma.Magma

-- Reconstructed from the submitted problem, not a server-returned module.
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop :=
  ∀ (x y z : G), x = ((y ◇ x) ◇ (x ◇ (y ◇ z))) ◇ y
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop :=
  ∀ (x y : G), x = y

abbrev Goal : Prop :=
  ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G

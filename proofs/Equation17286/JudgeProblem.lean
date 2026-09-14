prelude
import Init.Classical

class Magma (G : Type _) where
  op : G → G → G
infix:65 " ◇ " => Magma.op

/- Exact local target reconstructed from the inventory; not a remote receipt. -/
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop :=
  ∀ x y z : G, x = (y ◇ x) ◇ (z ◇ (z ◇ (x ◇ z)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop :=
  ∀ x y : G, x = y
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G

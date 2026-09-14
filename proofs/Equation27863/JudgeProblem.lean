prelude
import Init.Classical

/- Minimal local target reconstructed from this equation's archive entry. -/
class Magma (G : Type _) where
  op : G → G → G
infix:65 " ◇ " => Magma.op

@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop :=
  ∀ x y z : G, x = ((y ◇ (y ◇ x)) ◇ y) ◇ (x ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ x y : G, x = y
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G

prelude
import Init.Classical

/- Minimal magma interface; no Fin-table helpers or full Init import. -/
class Magma (G : Type _) where
  op : G → G → G
infix:65 " ◇ " => Magma.op

/- Reconstructed local target from proofs/index.json, not an official receipt. -/
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop :=
  ∀ x y z : G, x = (y ◇ x) ◇ (z ◇ ((x ◇ z) ◇ z))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop :=
  ∀ x y : G, x = y
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G

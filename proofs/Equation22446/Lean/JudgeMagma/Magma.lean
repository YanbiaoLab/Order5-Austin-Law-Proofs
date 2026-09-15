prelude
import Init.Data.Nat.Lemmas

/-- Minimal judge-compatible interface; finite table helpers are unnecessary here. -/
class Magma (α : Type _) where
  op : α → α → α

infix:65 " ◇ " => Magma.op

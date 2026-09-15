prelude
import Init.Prelude
import Init.Core
import Init.Notation
import Init.Tactics

class Magma (G : Type u) where
  op : G → G → G

infix:65 " ◇ " => Magma.op

prelude
import TreeModel
set_option autoImplicit false

namespace Equation27863TreeModel

abbrev Carrier := Equation18137TreeSchema.Tree

noncomputable def op (a b : Carrier) : Carrier := Equation18137TreeSchema.op b a

/- Reversal of the operation, with the last two source variables exchanged. -/
theorem source_law_explicit (x y z : Carrier) :
    x = op (op (op y (op y x)) y) (op x z) :=
  Equation18137TreeSchema.source_law_explicit x z y

def embed : Nat → Carrier := Equation18137TreeSchema.Tree.atom

theorem embed_injective (m n : Nat) (he : embed m = embed n) : m = n :=
  Equation18137TreeSchema.atom_injective m n he

theorem nontrivial : ∃ a b : Carrier, a ≠ b := Equation18137TreeSchema.nontrivial

theorem infinite_model : ∃ (G : Type) (f : G → G → G) (e : Nat → G),
    (∀ x y z, x = f (f (f y (f y x)) y) (f x z)) ∧
    (∀ m n, e m = e n → m = n) :=
  ⟨Carrier, op, embed, source_law_explicit, embed_injective⟩

end Equation27863TreeModel

#print axioms Equation27863TreeModel.source_law_explicit
#print axioms Equation27863TreeModel.embed_injective
#print axioms Equation27863TreeModel.nontrivial
#print axioms Equation27863TreeModel.infinite_model

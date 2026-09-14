prelude
import Init.Core
set_option autoImplicit false

/- Relational presentation for Equation17286. TreeGeometry proves decoder
   uniqueness; TreeModel supplies all hypotheses of conditional_source.
   The right-child counterexample explains why the E18137 proof needed revision. -/
namespace Equation17286Tree

inductive Tree where
  | atom : Nat → Tree
  | pair : Tree → Tree → Tree

open Tree

mutual
inductive Column : Tree → Tree → Prop where
  | raw (a b : Tree) : Column b (pair a b)
  | target {b o : Tree} : Target b o → Column b o
inductive Target : Tree → Tree → Prop where
  | single (x z : Tree) : Target (pair z (pair z (pair x z))) x
  | inherit {z v x : Tree} : Target z v → Column v x →
      Target (pair z (pair z v)) x
end

def Code (a b o : Tree) : Prop := Target b o ∧ Column o a

inductive Step : Tree → Tree → Tree → Prop where
  | raw (a b : Tree) : Step a b (pair a b)
  | hit {a b o : Tree} : Code a b o → Step a b o

theorem column_of_step {a b o : Tree} (h : Step a b o) : Column b o := by
  cases h with
  | raw => exact Column.raw a b
  | hit hc => exact Column.target hc.1

theorem target_of_step {x z v : Tree} (h : Step x z v) :
    Target (pair z (pair z v)) x := by
  cases h with
  | raw => exact Target.single x z
  | hit hc => exact Target.inherit hc.1 hc.2

/-- This is a list of proof obligations, not a construction of op. -/
theorem conditional_source (op : Tree → Tree → Tree)
    (hstep : ∀ a b, Step a b (op a b))
    (hhit : ∀ a b o, Code a b o → op a b = o)
    (hmiddle : ∀ x z, op z (op x z) = pair z (op x z))
    (houter : ∀ x z, op z (pair z (op x z)) = pair z (pair z (op x z))) :
    ∀ x y z, x = op (op y x) (op z (op z (op x z))) := by
  intro x y z
  have hc : Code (op y x) (pair z (pair z (op x z))) x :=
    ⟨target_of_step (hstep x z), column_of_step (hstep y x)⟩
  rw [hmiddle, houter]
  exact (hhit _ _ _ hc).symm

/-- The analogue of E18137's target_not_right is false for this relation. -/
theorem inherited_target_is_right_child {z v : Tree} (h : Target z v) :
    Target (pair z (pair z v)) (pair z v) :=
  Target.inherit h (Column.raw z v)

theorem explicit_right_child_target :
    let a := atom 0
    let q := pair a (pair a (pair a a))
    Target (pair q (pair q a)) (pair q a) :=
  inherited_target_is_right_child (Target.single (atom 0) (atom 0))

theorem right_child_exclusion_false :
    ¬ (∀ b o, Target b o → ∀ a, b ≠ pair a o) := by
  intro h
  exact h _ _ explicit_right_child_target _ rfl

end Equation17286Tree

#print axioms Equation17286Tree.column_of_step
#print axioms Equation17286Tree.target_of_step
#print axioms Equation17286Tree.conditional_source
#print axioms Equation17286Tree.inherited_target_is_right_child
#print axioms Equation17286Tree.explicit_right_child_target
#print axioms Equation17286Tree.right_child_exclusion_false

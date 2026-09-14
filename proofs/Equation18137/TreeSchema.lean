prelude
import Init.Core
import Init.Classical
set_option autoImplicit false

/- Infinite-key schema. This module gives the relational reduction and a
   conditional assembly theorem. TreeUnique and TreeModel discharge all its
   hypotheses and construct the nontrivial infinite magma. -/
namespace Equation18137TreeSchema

def SourceLaw {G : Type} (f : G → G → G) : Prop :=
  ∀ x y z, x = f (f y x) (f z (f (f x z) z))

inductive Tree where
  | atom : Nat → Tree
  | pair : Tree → Tree → Tree

open Tree

mutual
inductive Column : Tree → Tree → Prop where
  | raw (a b : Tree) : Column b (pair a b)
  | target {b o : Tree} : Target b o → Column b o
inductive Target : Tree → Tree → Prop where
  | single (x z : Tree) : Target (pair z (pair (pair x z) z)) x
  | inherit {z v x : Tree} : Target z v → Column v x →
      Target (pair z (pair v z)) x
end

def Code (a b o : Tree) : Prop := Target b o ∧ Column o a

inductive Step : Tree → Tree → Tree → Prop where
  | raw (a b : Tree) : Step a b (pair a b)
  | hit {a b o : Tree} : Code a b o → Step a b o

theorem column_of_step {a b o : Tree} (hs : Step a b o) : Column b o := by
  cases hs with
  | raw => exact Column.raw a b
  | hit hc => exact Column.target hc.1

theorem column_realized {b o : Tree} (hc : Column b o) : ∃ a, Step a b o := by
  cases hc with
  | raw a b => exact ⟨a, Step.raw a b⟩
  | target hr => exact ⟨pair (atom 0) o, Step.hit ⟨hr, Column.raw (atom 0) o⟩⟩

theorem target_decompose {b x : Tree} (hr : Target b x) :
    ∃ z v, b = pair z (pair v z) ∧ Step x z v := by
  cases hr with
  | single x z => exact ⟨z, pair x z, rfl, Step.raw x z⟩
  | inherit hz hc => exact ⟨_, _, rfl, Step.hit ⟨hz, hc⟩⟩

theorem target_of_step {x z v : Tree} (hs : Step x z v) :
    Target (pair z (pair v z)) x := by
  cases hs with
  | raw => exact Target.single x z
  | hit hc => exact Target.inherit hc.1 hc.2

theorem code_trace_iff (u b x : Tree) : Code u b x ↔
    ∃ y z v, b = pair z (pair v z) ∧ Step y x u ∧ Step x z v := by
  constructor
  · intro hc
    cases column_realized hc.2 with
    | intro y hy =>
      cases target_decompose hc.1 with
      | intro z hz =>
        cases hz with
        | intro v hv => exact ⟨y, z, v, hv.1, hy, hv.2⟩
  · intro h
    cases h with
    | intro y hy =>
      cases hy with
      | intro z hz =>
        cases hz with
        | intro v hv =>
          rw [hv.1]
          exact ⟨target_of_step hv.2.2, column_of_step hv.2.1⟩

theorem template_law (op : Tree → Tree → Tree)
    (hstep : ∀ a b, Step a b (op a b))
    (hhit : ∀ a b o, Code a b o → op a b = o)
    (hmiddle : ∀ x z, op (op x z) z = pair (op x z) z)
    (houter : ∀ x z, op z (pair (op x z) z) = pair z (pair (op x z) z)) :
    SourceLaw op := by
  intro x y z
  have hc : Code (op y x) (pair z (pair (op x z) z)) x :=
    ⟨target_of_step (hstep x z), column_of_step (hstep y x)⟩
  change x = op (op y x) (op z (op (op x z) z))
  rw [hmiddle, houter]
  exact (hhit _ _ _ hc).symm

theorem atom_injective (m n : Nat) (he : atom m = atom n) : m = n :=
  Tree.atom.inj he

end Equation18137TreeSchema

#print axioms Equation18137TreeSchema.column_of_step
#print axioms Equation18137TreeSchema.column_realized
#print axioms Equation18137TreeSchema.target_decompose
#print axioms Equation18137TreeSchema.target_of_step
#print axioms Equation18137TreeSchema.code_trace_iff
#print axioms Equation18137TreeSchema.template_law
#print axioms Equation18137TreeSchema.atom_injective

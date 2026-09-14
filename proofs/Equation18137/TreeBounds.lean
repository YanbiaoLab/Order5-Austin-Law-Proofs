prelude
import TreeSchema
import Init.Data.Nat.Basic
set_option autoImplicit false

namespace Equation18137TreeSchema
open Tree

def size : Tree → Nat
  | atom _ => 1
  | pair a b => Nat.succ (size a + size b)

def rank : Tree → Nat
  | atom _ => 0
  | pair _ b => size b

theorem left_lt_size (a b : Tree) : size a < size (pair a b) :=
  Nat.lt_succ_of_le (Nat.le_add_right _ _)

theorem right_lt_size (a b : Tree) : size b < size (pair a b) :=
  Nat.lt_succ_of_le (Nat.le_add_left _ _)

theorem rank_lt_size (a : Tree) : rank a < size a := by
  cases a with
  | atom _ => exact Nat.zero_lt_succ 0
  | pair a b => exact right_lt_size a b

theorem column_rank {b o : Tree} (hc : Column b o) : rank o ≤ size b := by
  apply Column.rec
    (motive_1 := fun b o _ => rank o ≤ size b)
    (motive_2 := fun b o _ => rank o < rank b)
    ?_ ?_ ?_ ?_ hc
  · intro a b
    exact Nat.le_refl _
  · intro b o hr ih
    exact Nat.le_of_lt (Nat.lt_trans ih (rank_lt_size b))
  · intro x z
    exact Nat.lt_trans (rank_lt_size x)
      (Nat.lt_trans (left_lt_size x z) (left_lt_size (pair x z) z))
  · intro z v x hz hc _ ih
    exact Nat.lt_of_le_of_lt ih (left_lt_size v z)

theorem target_rank {b o : Tree} (hr : Target b o) : rank o < rank b := by
  cases hr with
  | single x z =>
    exact Nat.lt_trans (rank_lt_size o)
      (Nat.lt_trans (left_lt_size o z) (left_lt_size (pair o z) z))
  | inherit hz hc => exact Nat.lt_of_le_of_lt (column_rank hc) (left_lt_size _ _)

theorem target_ne_self {b : Tree} (hr : Target b b) : False :=
  Nat.lt_irrefl _ (target_rank hr)

theorem target_not_raw {b a : Tree} (hr : Target b (pair a b)) : False :=
  Nat.lt_irrefl _ (Nat.lt_trans (target_rank hr) (rank_lt_size b))

theorem column_ne_identity {b o : Tree} (hc : Column b o) : o ≠ b := by
  cases hc with
  | raw a b =>
    intro he
    have hs := right_lt_size a b
    rw [he] at hs
    exact Nat.lt_irrefl _ hs
  | target hr =>
    intro he
    rw [he] at hr
    exact target_ne_self hr

theorem column_ne_self {b : Tree} (hc : Column b b) : False :=
  column_ne_identity hc rfl

theorem target_not_right {b o : Tree} (hr : Target b o) :
    ∀ a, b ≠ pair a o := by
  cases hr with
  | single x z =>
    intro a he
    have he' := (Tree.pair.inj he).2
    have hs := Nat.lt_trans (left_lt_size o z) (left_lt_size (pair o z) z)
    rw [he'] at hs
    exact Nat.lt_irrefl _ hs
  | inherit hz hc =>
    intro a he
    have he' := (Tree.pair.inj he).2
    cases hc with
    | raw y v =>
      have hzv := (Tree.pair.inj he').2
      rw [hzv] at hz
      exact target_ne_self hz
    | target ht =>
      have hs := target_rank ht
      rw [← he'] at hs
      exact Nat.lt_irrefl _ (Nat.lt_trans hs
        (Nat.lt_trans (target_rank hz) (rank_lt_size _)))

theorem raw_double_not_target (x z o : Tree) :
    ¬ Target (pair (pair x z) z) o := by
  intro hr
  cases target_decompose hr with
  | intro a ha =>
    cases ha with
    | intro v hv =>
      have hleft := (Tree.pair.inj hv.1).1
      have hright := (Tree.pair.inj hv.1).2
      rw [← hleft] at hright
      have hs := Nat.lt_trans (right_lt_size x z) (right_lt_size v (pair x z))
      rw [← hright] at hs
      exact Nat.lt_irrefl _ hs

theorem target_right_empty {a b o : Tree} (hr : Target (pair a b) o)
    (p : Tree) : ¬ Target b p := by
  cases hr with
  | single x z => exact raw_double_not_target o a p
  | inherit hz hc =>
    intro ht
    cases target_decompose ht with
    | intro u hu =>
      cases hu with
      | intro v hv =>
        have hleft := (Tree.pair.inj hv.1).1
        have hright := (Tree.pair.inj hv.1).2
        rw [← hleft] at hright
        exact target_not_right hz v hright

end Equation18137TreeSchema

#print axioms Equation18137TreeSchema.column_rank
#print axioms Equation18137TreeSchema.target_rank
#print axioms Equation18137TreeSchema.column_ne_self
#print axioms Equation18137TreeSchema.target_not_right
#print axioms Equation18137TreeSchema.raw_double_not_target
#print axioms Equation18137TreeSchema.target_right_empty

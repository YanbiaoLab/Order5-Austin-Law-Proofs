prelude
import TreeSchema
import Init.Classical
import Init.Data.Nat.Basic
import Init.WF
set_option autoImplicit false

namespace Equation17286Tree
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
      (Nat.lt_trans (left_lt_size x z) (right_lt_size z (pair x z)))
  · intro z v x hz hc _ ih
    exact Nat.lt_of_le_of_lt ih (right_lt_size z v)

theorem target_rank {b o : Tree} (hr : Target b o) : rank o < rank b := by
  cases hr with
  | single x z =>
    exact Nat.lt_trans (rank_lt_size o)
      (Nat.lt_trans (left_lt_size o z) (right_lt_size z (pair o z)))
  | inherit hz hc => exact Nat.lt_of_le_of_lt (column_rank hc) (right_lt_size _ _)

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

theorem column_cases {b o : Tree} (hc : Column b o) :
    (∃ a, o = pair a b) ∨ Target b o := by
  cases hc with
  | raw a b => exact Or.inl ⟨a, rfl⟩
  | target hr => exact Or.inr hr

theorem target_decompose {b x : Tree} (hr : Target b x) :
    ∃ z v, b = pair z (pair z v) ∧ Step x z v := by
  cases hr with
  | single x z => exact ⟨z, pair x z, rfl, Step.raw x z⟩
  | inherit hz hc => exact ⟨_, _, rfl, Step.hit ⟨hz,hc⟩⟩

theorem target_cases {b o : Tree} (hr : Target b o) :
    (∃ z, b = pair z (pair z (pair o z))) ∨
    (∃ z v, b = pair z (pair z v) ∧ Target z v ∧ Column v o) := by
  cases hr with
  | single x z => exact Or.inl ⟨z, rfl⟩
  | inherit hz hc => exact Or.inr ⟨_, _, rfl, hz, hc⟩

theorem target_point_unique (x z y : Tree)
    (hr : Target (pair z (pair z (pair x z))) y) : y = x := by
  cases target_cases hr with
  | inl hh =>
    cases hh with
    | intro w he =>
      exact ((Tree.pair.inj (Tree.pair.inj (Tree.pair.inj he).2).2).1).symm
  | inr hh =>
    cases hh with
    | intro w hh =>
      cases hh with
      | intro v hh =>
        have hzw := (Tree.pair.inj hh.1).1
        have hxv := (Tree.pair.inj (Tree.pair.inj hh.1).2).2
        have hz := hh.2.1
        rw [← hzw, ← hxv] at hz
        exact False.elim (target_not_raw hz)

theorem target_inherit_cases (z v y : Tree) (hz : Target z v)
    (hr : Target (pair z (pair z v)) y) : Column v y := by
  cases target_cases hr with
  | inl hh =>
    cases hh with
    | intro w he =>
      have hzw := (Tree.pair.inj he).1
      have hvy := (Tree.pair.inj (Tree.pair.inj he).2).2
      rw [← hzw] at hvy
      rw [hvy] at hz
      exact False.elim (target_not_raw hz)
  | inr hh =>
    cases hh with
    | intro w hh =>
      cases hh with
      | intro t hh =>
        have hvt := (Tree.pair.inj (Tree.pair.inj hh.1).2).2
        rw [hvt]
        exact hh.2.2

end Equation17286Tree

#print axioms Equation17286Tree.column_rank
#print axioms Equation17286Tree.target_rank
#print axioms Equation17286Tree.column_ne_self
#print axioms Equation17286Tree.target_point_unique
#print axioms Equation17286Tree.target_inherit_cases

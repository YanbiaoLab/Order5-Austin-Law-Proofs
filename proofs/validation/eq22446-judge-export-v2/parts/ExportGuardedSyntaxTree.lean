prelude
import Init.Classical
import Init.Data.Nat.Lemmas
import Init.RCases
set_option Elab.async false
set_option autoImplicit false
set_option Elab.async false

namespace submission.Equation22446Guarded

 

inductive Shade where
  | zero | one | two
  deriving DecidableEq

inductive T where
  | e : Shade → Nat → T
  | p : Shade → T → T → T
  deriving DecidableEq

def next : Shade → Shade
  | .zero => .one
  | .one => .two
  | .two => .zero

def S : T → T
  | .e c n => .e (next c) n
  | .p c a b => .p (next c) a b

def P (a b : T) : T := .p .zero a b

def nodes : T → Nat
  | .e _ _ => 0
  | .p _ a b => nodes a + nodes b + 1

theorem cube (a : T) : S (S (S a)) = a := by
  cases a with
  | e c n => cases c <;> rfl
  | p c a b => cases c <;> rfl

theorem S_injective {a b : T} (h : S a = S b) : a = b := by
  have h' := congrArg (fun t => S (S t)) h
  rwa [cube,cube] at h'

theorem S_ne (a : T) : S a ≠ a := by
  cases a with
  | e c n => cases c <;> intro h <;> cases h
  | p c a b => cases c <;> intro h <;> cases h

theorem SS_ne (a : T) : S (S a) ≠ a := by
  intro h
  have h' := congrArg S h
  rw [cube] at h'
  exact S_ne a h'.symm

theorem nodes_S (a : T) : nodes (S a) = nodes a := by
  cases a <;> rfl

theorem pair_left (c : Shade) (a b : T) : nodes a < nodes (.p c a b) :=
  Nat.lt_succ_of_le (Nat.le_add_right _ _)

theorem pair_right (c : Shade) (a b : T) : nodes b < nodes (.p c a b) :=
  Nat.lt_succ_of_le (Nat.le_add_left _ _)

theorem children_bound {x : T} {c : Shade} {a b : T} (h : x = .p c a b) :
    nodes a < nodes x ∧ nodes b < nodes x := by
  rw [h]
  exact ⟨pair_left c a b,pair_right c a b⟩

theorem phase_two_or_square_nonzero (x : T) :
    (∃ a b, x = .p .two a b) ∨ (∀ a b, S x ≠ P a b) := by
  cases x with
  | e c n => right; intro a b h; cases c <;> cases h
  | p c a b =>
      cases c with
      | zero => right; intro u v h; cases h
      | one => right; intro u v h; cases h
      | two => exact Or.inl ⟨a,b,rfl⟩

end submission.Equation22446Guarded

import JudgeProblem
set_option Elab.async false


set_option autoImplicit false
set_option Elab.async false

namespace submission.Austin23354

inductive T where
  | e : T
  | k : T → T
  | p : T → T → T

open T

def size : T → Nat
  | e => 0
  | k a => size a + 1
  | p a b => size a + size b + 2

inductive Row : T → T → Prop where
  | direct (a b : T) : Row a (p a b)
  | back (a b : T) : Row (p (p a b) a) b
  | cross (a b c : T) (h : Row a c) (h' : Row b a) : Row (p a b) (p a c)

noncomputable instance (a b : T) : Decidable (Row a b) := Classical.propDecidable _

noncomputable def op (a : T) : T → T
  | p x t => if Row x t ∧ Row a x then x else p a (p x t)
  | b => p a b

theorem op_hit (a x t : T) (h : Row x t) (h' : Row a x) :
    op a (p x t) = x := by
  simp only [op, if_pos (And.intro h h')]

theorem op_miss (a x t : T) (h : ¬(Row x t ∧ Row a x)) :
    op a (p x t) = p a (p x t) := by
  simp only [op, if_neg h]

inductive Eval : T → T → T → Prop where
  | raw (a b : T) : Eval a b (p a b)
  | hit (a x t : T) (h : Row x t) (h' : Row a x) : Eval a (p x t) x

theorem eval_op (a b : T) : Eval a b (op a b) := by
  cases b with
  | e => exact Eval.raw a e
  | k b => exact Eval.raw a (k b)
  | p x t =>
    classical
    by_cases h : Row x t ∧ Row a x
    · rw [op_hit a x t h.1 h.2]
      exact Eval.hit a x t h.1 h.2
    · rw [op_miss a x t h]
      exact Eval.raw a (p x t)

theorem row_eval {a b c : T} (h : Eval a b c) : Row a c := by
  cases h with
  | raw b => exact Row.direct a b
  | hit x t h h' => exact h'

theorem row_op (a b : T) : Row a (op a b) := row_eval (eval_op a b)

end submission.Austin23354

set_option autoImplicit false
set_option Elab.async false
namespace submission.Austin23354
open T

theorem row_not_left (a b : T) : ¬ Row (p a b) a := by
  intro h
  cases h

theorem row_asymm {a b : T} (h : Row a b) : ¬ Row b a := by
  induction h with
  | direct a b => exact row_not_left a b
  | back a b => intro hr; cases hr
  | cross a b c hr hs ih ih' =>
    intro rev
    cases rev
    exact ih (by assumption)

theorem row_irrefl (a : T) : ¬ Row a a := fun h => row_asymm h h

theorem row_not_sandwich_head (a b c : T) :
    ¬ Row (p (p a (p b c)) a) b := by
  intro h
  cases h

theorem row_not_left_left {a b : T} (h : Row a b) (c : T) :
    ¬ Row (p (p a b) c) a := by
  intro hr
  cases hr
  exact row_irrefl _ h

theorem row_not_triangle {a b t : T} (hab : Row a b) (h : Row (p a b) t) :
    ¬ Row t a := by
  cases h
  · rename_i c
    exact row_not_left_left hab c
  · exact False.elim (row_not_left _ _ hab)
  · exact row_not_left _ _

theorem op_row_raw {a b : T} (h : Row a b) : op a b = p a b := by
  cases h
  · rename_i c
    exact op_miss a a c (fun hh => row_irrefl a hh.2)
  · rename_i x
    cases b with
    | e => rfl
    | k t => rfl
    | p c d =>
      exact op_miss (p (p x (p c d)) x) c d
        (fun hh => row_not_sandwich_head x c d hh.2)
  · rename_i x y z hr hs
    exact op_miss (p x y) x z (fun hh => row_not_left x y hh.2)

theorem eval_sandwich {x y t a : T} (h : Eval y x t) (h' : Eval t y a) :
    Row a x := by
  cases h <;> cases h'
  · exact Row.back _ _
  · rename_i v hr hs
    exact False.elim (row_not_left_left hr _ hs)
  · rename_i v ht hy
    exact Row.cross _ _ _ ht hy
  · rename_i v ht u hau hta hy
    exact False.elim (row_not_triangle hau hy hta)

theorem row_sandwich (x y : T) : Row (op (op y x) y) x :=
  eval_sandwich (eval_op y x) (eval_op (op y x) y)

end submission.Austin23354

set_option autoImplicit false
set_option Elab.async false

namespace submission.Austin23354
open T

theorem equation23354 (x y z : T) :
    x = op (op (op y x) y) (op x (op x z)) := by
  rw [op_row_raw (row_op x z)]
  exact (op_hit (op (op y x) y) x (op x z) (row_op x z) (row_sandwich x y)).symm

noncomputable def dualOp (x y : T) : T := op y x

def tower : Nat → T
  | 0 => e
  | n+1 => k (tower n)

theorem tower_size (n : Nat) : size (tower n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [tower, size, ih]

theorem tower_injective (n m : Nat) (h : tower n = tower m) : n = m := by
  have hs := congrArg size h
  simpa only [tower_size] using hs

theorem infinite_model :
    ∃ (G : Type) (f : G → G → G) (i : Nat → G),
      (∀ n m, i n = i m → n = m) ∧
      (∀ x y z, x = f (f (f y x) y) (f x (f x z))) :=
  ⟨T, op, tower, tower_injective, equation23354⟩

end submission.Austin23354

set_option Elab.async false

namespace submission.Austin23354

theorem equation23337 (x y z : T) :
    x = (dualOp (dualOp (dualOp y x) x) (dualOp z (dualOp x z))) := equation23354 x z y

end submission.Austin23354

namespace submission
abbrev CM := Austin23354.T
namespace CM
theorem tower_injective (n m : Nat)
    (h : Austin23354.tower n = Austin23354.tower m) : n = m :=
  Austin23354.tower_injective n m h
end CM
noncomputable instance modelMagma : Magma CM := ⟨Austin23354.op⟩
end submission

theorem submission : Goal := by
  refine ⟨submission.CM, submission.modelMagma, ?_, ?_⟩
  · intro x y z
    exact submission.Austin23354.equation23354 x y z
  · intro h
    have bad : 0 = 1 := submission.Austin23354.tower_injective 0 1
      (h (submission.Austin23354.tower 0) (submission.Austin23354.tower 1))
    exact Nat.noConfusion bad
example : Goal := submission
#print axioms submission
#print axioms submission.CM.tower_injective


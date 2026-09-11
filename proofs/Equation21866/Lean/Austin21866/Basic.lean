import Init
set_option autoImplicit false
set_option Elab.async false

namespace submission.Austin21866

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
  | back (a b c : T) : Row (p a (p b c)) c
  | cross (a b c : T) (h : Row b c) : Row (p a b) (p b c)
  | lift (a b c : T) (h : Row a b) (h' : Row (p a b) c) : Row a (p (p a b) c)

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

theorem eval_back {y z x t a : T} (h : Eval z x t) (h' : Eval y t a) :
    Row a x := by
  cases h with
  | raw x =>
    cases h' with
    | raw t => exact Row.back y z x
    | hit z x hr hy => exact hr
  | hit t v ht hz =>
    cases h' with
    | raw t => exact Row.cross y t v ht
    | hit a b hab hya => exact Row.lift a b v hab ht

theorem row_back (x y z : T) : Row (op y (op z x)) x :=
  eval_back (eval_op z x) (eval_op y (op z x))

end submission.Austin21866

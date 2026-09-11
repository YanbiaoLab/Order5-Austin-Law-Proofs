import JudgeProblem
set_option Elab.async false


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

set_option autoImplicit false
set_option Elab.async false

namespace submission.Austin21866
open T

theorem row_ne {a b : T} (h : Row a b) : a ≠ b := by
  induction h with
  | direct a c => intro he; cases he
  | back x y z => intro he; cases he
  | cross x y z hr ih =>
    intro he
    exact ih (T.p.inj he).2
  | lift x y z hr hs ih ih' => intro he; cases he

theorem row_irrefl (a : T) : ¬ Row a a := fun h => row_ne h rfl

theorem row_not_right (a b : T) : ¬ Row (p a b) b := by
  intro h
  cases h

theorem row_not_right3 (a b c d : T) : ¬ Row (p a (p b (p c d))) c := by
  intro h
  cases h

theorem op_row_shape {a b : T} (h : Row a b) :
    ∃ c, op a b = p a c ∧ Row a c := by
  cases h
  · rename_i c
    refine ⟨p a c, ?_, Row.direct a c⟩
    exact op_miss a a c (fun hh => row_irrefl a hh.2)
  · rename_i x y
    refine ⟨b, ?_, Row.back x y b⟩
    cases b with
    | e => rfl
    | k t => rfl
    | p c d =>
      exact op_miss (p x (p y (p c d))) c d (fun hh => row_not_right3 x y c d hh.2)
  · rename_i x y z hr
    refine ⟨p y z, ?_, Row.cross x y z hr⟩
    exact op_miss _ y z (fun hh => row_not_right x y hh.2)
  · rename_i c v hr hs
    refine ⟨c, ?_, hr⟩
    exact op_hit a (p a c) v hs (Row.direct a c)

end submission.Austin21866

set_option autoImplicit false
set_option Elab.async false

namespace submission.Austin21866
open T

theorem equation21866 (x y z w : T) :
    x = op (op y (op z x)) (op x (op x w)) := by
  obtain ⟨v, hv, hr⟩ := op_row_shape (row_op x w)
  rw [hv]
  exact (op_hit (op y (op z x)) x v hr (row_back x y z)).symm

theorem equation21714 (x y z : T) :
    x = op (op y (op y x)) (op x (op x z)) := equation21866 x y y z

theorem equation21864 (x y z : T) :
    x = op (op y (op z x)) (op x (op x y)) := equation21866 x y z y

theorem equation21865 (x y z : T) :
    x = op (op y (op z x)) (op x (op x z)) := equation21866 x y z z

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
      (∀ x y z w, x = f (f y (f z x)) (f x (f x w))) :=
  ⟨T, op, tower, tower_injective, equation21866⟩

end submission.Austin21866

set_option Elab.async false

namespace submission.Austin21866

theorem equation24200 (x y z : T) :
    x = (dualOp (dualOp (dualOp y x) x) (dualOp (dualOp x z) z)) := equation21714 x z y

theorem equation24199 (x y z : T) :
    x = (dualOp (dualOp (dualOp y x) x) (dualOp (dualOp x z) y)) := equation21864 x y z

theorem equation24197 (x y z : T) :
    x = (dualOp (dualOp (dualOp y x) x) (dualOp (dualOp x y) z)) := equation21865 x z y

theorem equation24201 (x y z w : T) :
    x = (dualOp (dualOp (dualOp y x) x) (dualOp (dualOp x z) w)) := equation21866 x w z y

end submission.Austin21866

namespace submission
abbrev CM := Austin21866.T
namespace CM
theorem tower_injective (n m : Nat)
    (h : Austin21866.tower n = Austin21866.tower m) : n = m :=
  Austin21866.tower_injective n m h
end CM
noncomputable instance modelMagma : Magma CM := ⟨Austin21866.dualOp⟩
end submission

theorem submission : Goal := by
  refine ⟨submission.CM, submission.modelMagma, ?_, ?_⟩
  · intro x y z
    exact submission.Austin21866.equation24200 x y z
  · intro h
    have bad : 0 = 1 := submission.Austin21866.tower_injective 0 1
      (h (submission.Austin21866.tower 0) (submission.Austin21866.tower 1))
    exact Nat.noConfusion bad
example : Goal := submission
#print axioms submission
#print axioms submission.CM.tower_injective


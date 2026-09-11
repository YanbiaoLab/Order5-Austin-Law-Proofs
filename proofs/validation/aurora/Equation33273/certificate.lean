import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.SplitIfs
import JudgeProblem


set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000

/- Bruno Le Floch's rational piecewise model, posted 2025-11-09:
https://leanprover-community.github.io/archive/stream/458659-Equational/topic/Some.20results.20from.20order.205.html#554572972
The ordered branches below agree with the original formula at their boundaries. -/
namespace submission.Piecewise13102

def op (x y : ℚ) : ℚ :=
  if x ≤ 0 then y - x
  else if y ≤ 0 then y - x / 2
  else if y ≤ x then (y - x) / 2
  else y - x

def B (x : ℚ) : ℚ := if x ≤ 0 then -x else -x / 2
def Q (x : ℚ) : ℚ := if x ≤ 0 then -2 * x else -x

theorem square (x : ℚ) : op x x = 0 := by
  unfold op
  split_ifs <;> linarith

theorem right_zero (x : ℚ) : op x 0 = B x := by
  unfold op B
  split_ifs <;> linarith

theorem sandwich (x y : ℚ) : op y (op x y) = B x := by
  unfold op B
  split_ifs <;> linarith

theorem triple (x y : ℚ) : op y (op x (op x y)) = Q x := by
  unfold op Q
  split_ifs <;> linarith

theorem B_Q (x : ℚ) : B (Q x) = x := by
  unfold B Q
  split_ifs <;> linarith

theorem equation13102 (x y z : ℚ) :
    x = op y (op (op z (op x (op x z))) y) := by
  rw [triple, sandwich, B_Q]

theorem equation25087 (x y z : ℚ) :
    x = op (op y (op x (op x y))) (op z z) := by
  rw [triple, square, right_zero, B_Q]

def dualOp (x y : ℚ) : ℚ := op y x

theorem equation33273 (x y z : ℚ) :
    x = dualOp (dualOp y (dualOp (dualOp (dualOp z x) x) z)) y :=
  equation13102 x y z

theorem equation20911 (x y z : ℚ) :
    x = dualOp (dualOp y y) (dualOp (dualOp (dualOp z x) x) z) :=
  equation25087 x z y

def embed (n : Nat) : ℚ := n

theorem embed_injective (n m : Nat) (h : embed n = embed m) : n = m := by
  exact Nat.cast_injective h

theorem infinite_model :
    ∃ (G : Type) (f : G → G → G) (i : Nat → G),
      (∀ n m, i n = i m → n = m) ∧
      (∀ x y z, x = f y (f (f z (f x (f x z))) y)) :=
  ⟨ℚ, op, embed, embed_injective, equation13102⟩

end submission.Piecewise13102

namespace submission
abbrev CM := ℚ
namespace CM
theorem tower_injective (n m : Nat)
    (h : Piecewise13102.embed n = Piecewise13102.embed m) : n = m :=
  Piecewise13102.embed_injective n m h
end CM
instance modelMagma : Magma CM := ⟨Piecewise13102.dualOp⟩
end submission

theorem submission : Goal := by
  refine ⟨submission.CM, submission.modelMagma, ?_, ?_⟩
  · intro x y z
    exact submission.Piecewise13102.equation33273 x y z
  · intro h
    have bad : 0 = 1 := submission.Piecewise13102.embed_injective 0 1
      (h (submission.Piecewise13102.embed 0) (submission.Piecewise13102.embed 1))
    exact Nat.noConfusion bad
example : Goal := submission
#print axioms submission
#print axioms submission.CM.tower_injective

#print axioms submission.Piecewise13102.square
#print axioms submission.Piecewise13102.right_zero
#print axioms submission.Piecewise13102.sandwich
#print axioms submission.Piecewise13102.triple
#print axioms submission.Piecewise13102.B_Q
#print axioms submission.Piecewise13102.equation13102
#print axioms submission.Piecewise13102.equation25087
#print axioms submission.Piecewise13102.equation33273
#print axioms submission.Piecewise13102.equation20911
#print axioms submission.Piecewise13102.embed_injective
#print axioms submission.Piecewise13102.infinite_model

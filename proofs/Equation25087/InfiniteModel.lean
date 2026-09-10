import Mathlib
import JudgeProblem

set_option maxHeartbeats 4000000

/- The operation below is Bruno Le Floch's published model for E13102
   (2025-11-09, Zulip message 554572972). This file tests the additional
   consequences E25087 / E20911, and does not claim a new base operation. -/
namespace submission.CM
def f (x y : ℚ) : ℚ :=
  if 0 ≤ y ∧ y ≤ x then (y-x)/2
  else if y ≤ 0 ∧ 0 ≤ x then y-x/2
  else y-x

def q (x : ℚ) : ℚ := if 0 ≤ x then -x else -2*x

theorem square (x : ℚ) : f x x = 0 := by
  unfold f
  split_ifs <;> linarith

theorem left_nonpos {x : ℚ} (hx : x ≤ 0) (y : ℚ) : f x y = y-x := by
  unfold f
  split_ifs <;> linarith

theorem right_nonpos {x y : ℚ} (hx : 0 ≤ x) (hy : y ≤ 0) : f x y = y-x/2 := by
  simp only [f, if_pos (And.intro hy hx)]
  split_ifs <;> linarith

theorem middle {x y : ℚ} (hy : 0 ≤ y) (hxy : y ≤ x) : f x y = (y-x)/2 := by
  simp only [f, if_pos (And.intro hy hxy)]

theorem above {x y : ℚ} (hxy : x ≤ y) : f x y = y-x := by
  unfold f
  split_ifs <;> linarith

theorem triple (x y : ℚ) : f y (f x (f x y)) = q x := by
  by_cases hx : x ≤ 0
  · rw [left_nonpos hx, left_nonpos hx, above (by linarith)]
    unfold q
    split_ifs <;> linarith
  · have hx0 : 0 ≤ x := le_of_not_ge hx
    rw [q, if_pos hx0]
    by_cases hy : y ≤ 0
    · rw [right_nonpos hx0 hy, right_nonpos hx0 (by linarith), left_nonpos hy]
      ring
    · have hy0 : 0 ≤ y := le_of_not_ge hy
      by_cases hxy : y ≤ x
      · rw [middle hy0 hxy, right_nonpos hx0 (by linarith), right_nonpos hy0 (by linarith)]
        ring
      · rw [above (le_of_not_ge hxy)]
        by_cases h2 : y-x ≤ x
        · rw [middle (by linarith) h2, right_nonpos hy0 (by linarith)]
          ring
        · rw [above (x := x) (y := y-x) (by linarith),
              middle (x := y) (y := y-x-x) (by linarith) (by linarith)]
          ring

theorem q_right_zero (x : ℚ) : f (q x) 0 = x := by
  by_cases hx : 0 ≤ x
  · rw [q, if_pos hx, left_nonpos (by linarith)]
    ring
  · rw [q, if_neg hx, right_nonpos (by linarith) (le_refl 0)]
    ring

theorem law25087 (x y z : ℚ) : x = f (f y (f x (f x y))) (f z z) := by
  rw [square, triple, q_right_zero]

theorem tower_injective (n m : ℕ) (h : (n : ℚ) = (m : ℚ)) : n = m := by
  exact_mod_cast h

end submission.CM

set_option maxHeartbeats 4000000

theorem submission.CM.model : Goal := by
  letI : Magma ℚ := ⟨submission.CM.f⟩
  refine ⟨ℚ, inferInstance, ?_, ?_⟩
  · intro x y z
    change x = submission.CM.f (submission.CM.f y (submission.CM.f x (submission.CM.f x y))) (submission.CM.f z z)
    exact submission.CM.law25087 x y z
  · intro h
    have bad : (0 : ℚ) = 1 := h 0 1
    norm_num at bad

def submission : Goal := submission.CM.model

#print axioms submission
#print axioms submission.CM.tower_injective

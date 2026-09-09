import Peak21Roots00
import Peak21Roots01
import Peak21Roots02
import Peak21Roots03
import Peak21Roots04
import Peak21Roots05
import Peak21Roots06
import Peak21Roots07
import Peak21Roots08
import Peak21Roots09
import Peak21Roots10
import Peak21Roots11
import Peak21Roots12
import Peak21Roots13
import Peak21Roots14
import Peak21Context00
import Peak21Context01
import Peak21Context02
import Peak21Context03
import Peak21Context04
import Peak21Context05
import Peak21Context06
import Peak21Context07
import Peak21Context08
import Peak21Context09
import Peak21Context10
import Peak21Context11
import Peak21Context12
import Peak21Context13
import Basic
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak21 (x0 : T) (x1 : T) (x2 : T) {u : T} (h : Step (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) u) : Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) u := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
    · rw [ho]
      exact peak21_root0 he
    · rw [ho]
      exact peak21_root1 he
    · rw [ho]
      exact peak21_root2 he
    · rw [ho]
      exact peak21_root3 he
    · rw [ho]
      exact peak21_root4 he
    · rw [ho]
      exact peak21_root5 he
    · rw [ho]
      exact peak21_root6 he
    · rw [ho]
      exact peak21_root7 he
    · rw [ho]
      exact peak21_root8 he
    · rw [ho]
      exact peak21_root9 he
    · rw [ho]
      exact peak21_root10 he
    · rw [ho]
      exact peak21_root11 he
    · rw [ho]
      exact peak21_root12 he
    · rw [ho]
      exact peak21_root13 he
    · rw [ho]
      exact peak21_root14 he
    · rw [ho]
      exact peak21_root15 he
    · rw [ho]
      exact peak21_root16 he
    · rw [ho]
      exact peak21_root17 he
    · rw [ho]
      exact peak21_root18 he
    · rw [ho]
      exact peak21_root19 he
    · rw [ho]
      exact peak21_root20 he
  | @left _ t0 _ h0 =>
    exact peak21_context_1 h0
  | @right _ _ t0 h0 =>
    exact peak21_context_2 h0
end submission.Austin5837

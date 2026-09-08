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
import Basic
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak21_context_2 {x0 x1 x2 u : T} (h : Step (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) u) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) u) := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
    · rw [ho]
      exact peak21_root147 he
    · rw [ho]
      exact peak21_root148 he
    · rw [ho]
      exact peak21_root149 he
    · rw [ho]
      exact peak21_root150 he
    · rw [ho]
      exact peak21_root151 he
    · rw [ho]
      exact peak21_root152 he
    · rw [ho]
      exact peak21_root153 he
    · rw [ho]
      exact peak21_root154 he
    · rw [ho]
      exact peak21_root155 he
    · rw [ho]
      exact peak21_root156 he
    · rw [ho]
      exact peak21_root157 he
    · rw [ho]
      exact peak21_root158 he
    · rw [ho]
      exact peak21_root159 he
    · rw [ho]
      exact peak21_root160 he
    · rw [ho]
      exact peak21_root161 he
    · rw [ho]
      exact peak21_root162 he
    · rw [ho]
      exact peak21_root163 he
    · rw [ho]
      exact peak21_root164 he
    · rw [ho]
      exact peak21_root165 he
    · rw [ho]
      exact peak21_root166 he
    · rw [ho]
      exact peak21_root167 he
  | @firstC _ t1 _ _ h1 =>
    exact peak21_context_21 h1
  | @secondC _ _ t1 _ h1 =>
    exact peak21_context_22 h1
  | @thirdC _ _ _ t1 h1 =>
    exact peak21_context_23 h1
end submission.Austin5837

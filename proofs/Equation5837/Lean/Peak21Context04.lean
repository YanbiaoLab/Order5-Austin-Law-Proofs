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
import Basic
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak21_context_11 {x0 x1 x2 u : T} (h : Step (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) u) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d u x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
    · rw [ho]
      exact peak21_root42 he
    · rw [ho]
      exact peak21_root43 he
    · rw [ho]
      exact peak21_root44 he
    · rw [ho]
      exact peak21_root45 he
    · rw [ho]
      exact peak21_root46 he
    · rw [ho]
      exact peak21_root47 he
    · rw [ho]
      exact peak21_root48 he
    · rw [ho]
      exact peak21_root49 he
    · rw [ho]
      exact peak21_root50 he
    · rw [ho]
      exact peak21_root51 he
    · rw [ho]
      exact peak21_root52 he
    · rw [ho]
      exact peak21_root53 he
    · rw [ho]
      exact peak21_root54 he
    · rw [ho]
      exact peak21_root55 he
    · rw [ho]
      exact peak21_root56 he
    · rw [ho]
      exact peak21_root57 he
    · rw [ho]
      exact peak21_root58 he
    · rw [ho]
      exact peak21_root59 he
    · rw [ho]
      exact peak21_root60 he
    · rw [ho]
      exact peak21_root61 he
    · rw [ho]
      exact peak21_root62 he
  | @leftD _ t2 _ h2 =>
    exact peak21_context_111 h2
  | @rightD _ _ t2 h2 =>
    exact peak21_context_112 h2
end submission.Austin5837

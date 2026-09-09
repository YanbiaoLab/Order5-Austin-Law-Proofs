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
import Basic
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak21_context_111 {x0 x1 x2 u : T} (h : Step (T.c (T.d x0 x1) (T.d x0 x1) x2) u) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d u (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
    · rw [ho]
      exact peak21_root63 he
    · rw [ho]
      exact peak21_root64 he
    · rw [ho]
      exact peak21_root65 he
    · rw [ho]
      exact peak21_root66 he
    · rw [ho]
      exact peak21_root67 he
    · rw [ho]
      exact peak21_root68 he
    · rw [ho]
      exact peak21_root69 he
    · rw [ho]
      exact peak21_root70 he
    · rw [ho]
      exact peak21_root71 he
    · rw [ho]
      exact peak21_root72 he
    · rw [ho]
      exact peak21_root73 he
    · rw [ho]
      exact peak21_root74 he
    · rw [ho]
      exact peak21_root75 he
    · rw [ho]
      exact peak21_root76 he
    · rw [ho]
      exact peak21_root77 he
    · rw [ho]
      exact peak21_root78 he
    · rw [ho]
      exact peak21_root79 he
    · rw [ho]
      exact peak21_root80 he
    · rw [ho]
      exact peak21_root81 he
    · rw [ho]
      exact peak21_root82 he
    · rw [ho]
      exact peak21_root83 he
  | @firstC _ t3 _ _ h3 =>
    exact peak21_context_1111 h3
  | @secondC _ _ t3 _ h3 =>
    exact peak21_context_1112 h3
  | @thirdC _ _ _ t3 h3 =>
    exact ⟨(T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) t3) (T.c (T.d x0 x1) (T.d x0 x1) t3) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) t3) (T.d x0 x1))), (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.thirdC (T.d x0 x1) (T.d x0 x1) h3))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.secondC (T.c (T.d x0 x1) (T.d x0 x1) t3) (T.d x0 x1) (Step.thirdC (T.d x0 x1) (T.d x0 x1) h3))) (Steps.cons (Step.rightR (T.c (T.c (T.d x0 x1) (T.d x0 x1) t3) (T.c (T.d x0 x1) (T.d x0 x1) t3) (T.d x0 x1)) (Step.leftD (T.d x0 x1) (Step.thirdC (T.d x0 x1) (T.d x0 x1) h3))) (Steps.refl _)))), (Steps.cons (Step.right (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) t3) (T.d x0 x1)) x0) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.thirdC (T.d x0 x1) (T.d x0 x1) h3))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) t3) (T.d x0 x1)) x0) (Step.secondC (T.c (T.d x0 x1) (T.d x0 x1) t3) (T.d x0 x1) (Step.thirdC (T.d x0 x1) (T.d x0 x1) h3))) (Steps.cons (Step.root (Root.r21 x0 x1 t3)) (Steps.refl _))))⟩
end submission.Austin5837

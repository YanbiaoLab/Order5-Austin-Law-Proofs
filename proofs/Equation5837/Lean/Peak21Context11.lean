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
import Basic
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak21_context_22 {x0 x1 x2 u : T} (h : Step (T.c (T.d x0 x1) (T.d x0 x1) x2) u) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) u (T.d x0 x1))) := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
    · rw [ho]
      exact peak21_root231 he
    · rw [ho]
      exact peak21_root232 he
    · rw [ho]
      exact peak21_root233 he
    · rw [ho]
      exact peak21_root234 he
    · rw [ho]
      exact peak21_root235 he
    · rw [ho]
      exact peak21_root236 he
    · rw [ho]
      exact peak21_root237 he
    · rw [ho]
      exact peak21_root238 he
    · rw [ho]
      exact peak21_root239 he
    · rw [ho]
      exact peak21_root240 he
    · rw [ho]
      exact peak21_root241 he
    · rw [ho]
      exact peak21_root242 he
    · rw [ho]
      exact peak21_root243 he
    · rw [ho]
      exact peak21_root244 he
    · rw [ho]
      exact peak21_root245 he
    · rw [ho]
      exact peak21_root246 he
    · rw [ho]
      exact peak21_root247 he
    · rw [ho]
      exact peak21_root248 he
    · rw [ho]
      exact peak21_root249 he
    · rw [ho]
      exact peak21_root250 he
    · rw [ho]
      exact peak21_root251 he
  | @firstC _ t2 _ _ h2 =>
    exact peak21_context_221 h2
  | @secondC _ _ t2 _ h2 =>
    exact peak21_context_222 h2
  | @thirdC _ _ _ t2 h2 =>
    exact ⟨(T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) t2) (T.c (T.d x0 x1) (T.d x0 x1) t2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) t2) (T.d x0 x1))), (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.thirdC (T.d x0 x1) (T.d x0 x1) h2))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.secondC (T.c (T.d x0 x1) (T.d x0 x1) t2) (T.d x0 x1) (Step.thirdC (T.d x0 x1) (T.d x0 x1) h2))) (Steps.cons (Step.rightR (T.c (T.c (T.d x0 x1) (T.d x0 x1) t2) (T.c (T.d x0 x1) (T.d x0 x1) t2) (T.d x0 x1)) (Step.leftD (T.d x0 x1) (Step.thirdC (T.d x0 x1) (T.d x0 x1) h2))) (Steps.refl _)))), (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) t2) (T.d x0 x1)) (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.thirdC (T.d x0 x1) (T.d x0 x1) h2)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) t2) (T.d x0 x1)) x0) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) t2) (T.d x0 x1) (Step.thirdC (T.d x0 x1) (T.d x0 x1) h2))) (Steps.cons (Step.root (Root.r21 x0 x1 t2)) (Steps.refl _))))⟩
end submission.Austin5837

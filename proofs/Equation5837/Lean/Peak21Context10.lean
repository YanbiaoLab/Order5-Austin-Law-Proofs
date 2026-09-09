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
import Basic
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak21_context_222 {x0 x1 x2 u : T} (h : Step (T.d x0 x1) u) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) u x2) (T.d x0 x1))) := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
    · rw [ho]
      exact peak21_root273 he
    · rw [ho]
      exact peak21_root274 he
    · rw [ho]
      exact peak21_root275 he
    · rw [ho]
      exact peak21_root276 he
    · rw [ho]
      exact peak21_root277 he
    · rw [ho]
      exact peak21_root278 he
    · rw [ho]
      exact peak21_root279 he
    · rw [ho]
      exact peak21_root280 he
    · rw [ho]
      exact peak21_root281 he
    · rw [ho]
      exact peak21_root282 he
    · rw [ho]
      exact peak21_root283 he
    · rw [ho]
      exact peak21_root284 he
    · rw [ho]
      exact peak21_root285 he
    · rw [ho]
      exact peak21_root286 he
    · rw [ho]
      exact peak21_root287 he
    · rw [ho]
      exact peak21_root288 he
    · rw [ho]
      exact peak21_root289 he
    · rw [ho]
      exact peak21_root290 he
    · rw [ho]
      exact peak21_root291 he
    · rw [ho]
      exact peak21_root292 he
    · rw [ho]
      exact peak21_root293 he
  | @leftD _ t3 _ h3 =>
    exact ⟨(T.r (T.c (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1))), (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.secondC (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.secondC (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.thirdC (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.c (T.d t3 x1) (T.d t3 x1) x2) (Step.leftD x1 h3))) (Steps.cons (Step.rightR (T.c (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.rightR (T.c (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (Step.leftD (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.rightR (T.c (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (Step.rightD (T.c (T.d t3 x1) (T.d t3 x1) x2) (Step.leftD x1 h3))) (Steps.refl _))))))))), (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d t3 x1) x2) (T.d x0 x1)) (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3))))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d t3 x1) x2) (T.d x0 x1)) (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3))))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d t3 x1) x2) (T.d x0 x1)) (Step.leftD x0 (Step.rightD (T.c (T.d t3 x1) (T.d t3 x1) x2) (Step.leftD x1 h3)))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d t3 x1) x2) (T.d x0 x1)) (Step.rightD (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) h3)) (Steps.cons (Step.right (T.d (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) t3) (Step.firstC (T.c (T.d x0 x1) (T.d t3 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) t3) (Step.firstC (T.c (T.d x0 x1) (T.d t3 x1) x2) (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) t3) (Step.secondC (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d x0 x1) (Step.firstC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) t3) (Step.thirdC (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.c (T.d t3 x1) (T.d t3 x1) x2) (Step.leftD x1 h3))) (Steps.cons (Step.root (Root.r21 t3 x1 x2)) (Steps.refl _))))))))))⟩
  | @rightD _ _ t3 h3 =>
    exact ⟨(T.r (T.c (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3))), (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.secondC (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.secondC (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.thirdC (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.c (T.d x0 t3) (T.d x0 t3) x2) (Step.rightD x0 h3))) (Steps.cons (Step.rightR (T.c (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.rightR (T.c (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.rightR (T.c (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (Step.rightD (T.c (T.d x0 t3) (T.d x0 t3) x2) (Step.rightD x0 h3))) (Steps.refl _))))))))), (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 t3) x2) (T.d x0 x1)) (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3))))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 t3) x2) (T.d x0 x1)) (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3))))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 t3) x2) (T.d x0 x1)) (Step.leftD x0 (Step.rightD (T.c (T.d x0 t3) (T.d x0 t3) x2) (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) x0) (Step.firstC (T.c (T.d x0 x1) (T.d x0 t3) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) x0) (Step.firstC (T.c (T.d x0 x1) (T.d x0 t3) x2) (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) x0) (Step.secondC (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 x1) (Step.firstC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) x0) (Step.thirdC (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.c (T.d x0 t3) (T.d x0 t3) x2) (Step.rightD x0 h3))) (Steps.cons (Step.root (Root.r21 x0 t3 x2)) (Steps.refl _)))))))))⟩
end submission.Austin5837

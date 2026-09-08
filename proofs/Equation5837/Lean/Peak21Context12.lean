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
import Basic
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak21_context_23 {x0 x1 x2 u : T} (h : Step (T.d x0 x1) u) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) u)) := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
    · rw [ho]
      exact peak21_root294 he
    · rw [ho]
      exact peak21_root295 he
    · rw [ho]
      exact peak21_root296 he
    · rw [ho]
      exact peak21_root297 he
    · rw [ho]
      exact peak21_root298 he
    · rw [ho]
      exact peak21_root299 he
    · rw [ho]
      exact peak21_root300 he
    · rw [ho]
      exact peak21_root301 he
    · rw [ho]
      exact peak21_root302 he
    · rw [ho]
      exact peak21_root303 he
    · rw [ho]
      exact peak21_root304 he
    · rw [ho]
      exact peak21_root305 he
    · rw [ho]
      exact peak21_root306 he
    · rw [ho]
      exact peak21_root307 he
    · rw [ho]
      exact peak21_root308 he
    · rw [ho]
      exact peak21_root309 he
    · rw [ho]
      exact peak21_root310 he
    · rw [ho]
      exact peak21_root311 he
    · rw [ho]
      exact peak21_root312 he
    · rw [ho]
      exact peak21_root313 he
    · rw [ho]
      exact peak21_root314 he
  | @leftD _ t2 _ h2 =>
    exact ⟨(T.r (T.c (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.d t2 x1)) (T.d (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.d t2 x1))), (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h2)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.secondC (T.d t2 x1) x2 (Step.leftD x1 h2)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.secondC (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h2)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.secondC (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.d x0 x1) (Step.secondC (T.d t2 x1) x2 (Step.leftD x1 h2)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.thirdC (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.c (T.d t2 x1) (T.d t2 x1) x2) (Step.leftD x1 h2))) (Steps.cons (Step.rightR (T.c (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.d t2 x1)) (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h2)))) (Steps.cons (Step.rightR (T.c (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.d t2 x1)) (Step.leftD (T.d x0 x1) (Step.secondC (T.d t2 x1) x2 (Step.leftD x1 h2)))) (Steps.cons (Step.rightR (T.c (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.d t2 x1)) (Step.rightD (T.c (T.d t2 x1) (T.d t2 x1) x2) (Step.leftD x1 h2))) (Steps.refl _))))))))), (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d t2 x1)) (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h2))))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d t2 x1)) (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.secondC (T.d t2 x1) x2 (Step.leftD x1 h2))))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d t2 x1)) (Step.leftD x0 (Step.rightD (T.c (T.d t2 x1) (T.d t2 x1) x2) (Step.leftD x1 h2)))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d t2 x1)) (Step.rightD (T.d (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.d t2 x1)) h2)) (Steps.cons (Step.right (T.d (T.d (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.d t2 x1)) t2) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d t2 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h2)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.d t2 x1)) t2) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d t2 x1) (Step.secondC (T.d t2 x1) x2 (Step.leftD x1 h2)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.d t2 x1)) t2) (Step.secondC (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.d t2 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h2)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.d t2 x1)) t2) (Step.secondC (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.d t2 x1) (Step.secondC (T.d t2 x1) x2 (Step.leftD x1 h2)))) (Steps.cons (Step.root (Root.r21 t2 x1 x2)) (Steps.refl _))))))))))⟩
  | @rightD _ _ t2 h2 =>
    exact ⟨(T.r (T.c (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.d x0 t2)) (T.d (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.d x0 t2))), (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h2)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.secondC (T.d x0 t2) x2 (Step.rightD x0 h2)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.secondC (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h2)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.secondC (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.d x0 x1) (Step.secondC (T.d x0 t2) x2 (Step.rightD x0 h2)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.thirdC (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.c (T.d x0 t2) (T.d x0 t2) x2) (Step.rightD x0 h2))) (Steps.cons (Step.rightR (T.c (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.d x0 t2)) (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h2)))) (Steps.cons (Step.rightR (T.c (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.d x0 t2)) (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t2) x2 (Step.rightD x0 h2)))) (Steps.cons (Step.rightR (T.c (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.d x0 t2)) (Step.rightD (T.c (T.d x0 t2) (T.d x0 t2) x2) (Step.rightD x0 h2))) (Steps.refl _))))))))), (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 t2)) (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h2))))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 t2)) (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t2) x2 (Step.rightD x0 h2))))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 t2)) (Step.leftD x0 (Step.rightD (T.c (T.d x0 t2) (T.d x0 t2) x2) (Step.rightD x0 h2)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.d x0 t2)) x0) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 t2) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h2)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.d x0 t2)) x0) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 t2) (Step.secondC (T.d x0 t2) x2 (Step.rightD x0 h2)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.d x0 t2)) x0) (Step.secondC (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.d x0 t2) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h2)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.d x0 t2)) x0) (Step.secondC (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.d x0 t2) (Step.secondC (T.d x0 t2) x2 (Step.rightD x0 h2)))) (Steps.cons (Step.root (Root.r21 x0 t2 x2)) (Steps.refl _)))))))))⟩
end submission.Austin5837

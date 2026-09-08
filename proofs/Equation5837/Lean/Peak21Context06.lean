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
import Basic
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak21_context_211 {x0 x1 x2 u : T} (h : Step (T.d x0 x1) u) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c u (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
    · rw [ho]
      exact peak21_root189 he
    · rw [ho]
      exact peak21_root190 he
    · rw [ho]
      exact peak21_root191 he
    · rw [ho]
      exact peak21_root192 he
    · rw [ho]
      exact peak21_root193 he
    · rw [ho]
      exact peak21_root194 he
    · rw [ho]
      exact peak21_root195 he
    · rw [ho]
      exact peak21_root196 he
    · rw [ho]
      exact peak21_root197 he
    · rw [ho]
      exact peak21_root198 he
    · rw [ho]
      exact peak21_root199 he
    · rw [ho]
      exact peak21_root200 he
    · rw [ho]
      exact peak21_root201 he
    · rw [ho]
      exact peak21_root202 he
    · rw [ho]
      exact peak21_root203 he
    · rw [ho]
      exact peak21_root204 he
    · rw [ho]
      exact peak21_root205 he
    · rw [ho]
      exact peak21_root206 he
    · rw [ho]
      exact peak21_root207 he
    · rw [ho]
      exact peak21_root208 he
    · rw [ho]
      exact peak21_root209 he
  | @leftD _ t3 _ h3 =>
    exact ⟨(T.r (T.c (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1))), (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.secondC (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.secondC (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.thirdC (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.c (T.d t3 x1) (T.d t3 x1) x2) (Step.leftD x1 h3))) (Steps.cons (Step.rightR (T.c (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.rightR (T.c (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (Step.leftD (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.rightR (T.c (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (Step.rightD (T.c (T.d t3 x1) (T.d t3 x1) x2) (Step.leftD x1 h3))) (Steps.refl _))))))))), (Steps.cons (Step.left (T.c (T.c (T.d t3 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3))))) (Steps.cons (Step.left (T.c (T.c (T.d t3 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3))))) (Steps.cons (Step.left (T.c (T.c (T.d t3 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD x0 (Step.rightD (T.c (T.d t3 x1) (T.d t3 x1) x2) (Step.leftD x1 h3)))) (Steps.cons (Step.left (T.c (T.c (T.d t3 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.rightD (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) h3)) (Steps.cons (Step.right (T.d (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) t3) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) t3) (Step.secondC (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) t3) (Step.secondC (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) t3) (Step.thirdC (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.c (T.d t3 x1) (T.d t3 x1) x2) (Step.leftD x1 h3))) (Steps.cons (Step.root (Root.r21 t3 x1 x2)) (Steps.refl _))))))))))⟩
  | @rightD _ _ t3 h3 =>
    exact ⟨(T.r (T.c (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3))), (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.secondC (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.secondC (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.thirdC (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.c (T.d x0 t3) (T.d x0 t3) x2) (Step.rightD x0 h3))) (Steps.cons (Step.rightR (T.c (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.rightR (T.c (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.rightR (T.c (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (Step.rightD (T.c (T.d x0 t3) (T.d x0 t3) x2) (Step.rightD x0 h3))) (Steps.refl _))))))))), (Steps.cons (Step.left (T.c (T.c (T.d x0 t3) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3))))) (Steps.cons (Step.left (T.c (T.c (T.d x0 t3) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3))))) (Steps.cons (Step.left (T.c (T.c (T.d x0 t3) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD x0 (Step.rightD (T.c (T.d x0 t3) (T.d x0 t3) x2) (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) x0) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) x0) (Step.secondC (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) x0) (Step.secondC (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) x0) (Step.thirdC (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.c (T.d x0 t3) (T.d x0 t3) x2) (Step.rightD x0 h3))) (Steps.cons (Step.root (Root.r21 x0 t3 x2)) (Steps.refl _)))))))))⟩
end submission.Austin5837

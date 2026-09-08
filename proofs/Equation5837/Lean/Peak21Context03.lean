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
import Basic
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak21_context_112 {x0 x1 x2 u : T} (h : Step (T.d x0 x1) u) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) u) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
    · rw [ho]
      exact peak21_root126 he
    · rw [ho]
      exact peak21_root127 he
    · rw [ho]
      exact peak21_root128 he
    · rw [ho]
      exact peak21_root129 he
    · rw [ho]
      exact peak21_root130 he
    · rw [ho]
      exact peak21_root131 he
    · rw [ho]
      exact peak21_root132 he
    · rw [ho]
      exact peak21_root133 he
    · rw [ho]
      exact peak21_root134 he
    · rw [ho]
      exact peak21_root135 he
    · rw [ho]
      exact peak21_root136 he
    · rw [ho]
      exact peak21_root137 he
    · rw [ho]
      exact peak21_root138 he
    · rw [ho]
      exact peak21_root139 he
    · rw [ho]
      exact peak21_root140 he
    · rw [ho]
      exact peak21_root141 he
    · rw [ho]
      exact peak21_root142 he
    · rw [ho]
      exact peak21_root143 he
    · rw [ho]
      exact peak21_root144 he
    · rw [ho]
      exact peak21_root145 he
    · rw [ho]
      exact peak21_root146 he
  | @leftD _ t3 _ h3 =>
    exact ⟨(T.r (T.c (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1))), (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.secondC (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.secondC (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.thirdC (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.c (T.d t3 x1) (T.d t3 x1) x2) (Step.leftD x1 h3))) (Steps.cons (Step.rightR (T.c (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.rightR (T.c (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (Step.leftD (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.rightR (T.c (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (Step.rightD (T.c (T.d t3 x1) (T.d t3 x1) x2) (Step.leftD x1 h3))) (Steps.refl _))))))))), (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD x0 (Step.leftD (T.d t3 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3))))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD x0 (Step.leftD (T.d t3 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3))))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.rightD (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) h3)) (Steps.cons (Step.right (T.d (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) t3) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) t3) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) t3) (Step.secondC (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) t3) (Step.secondC (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) t3) (Step.thirdC (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.c (T.d t3 x1) (T.d t3 x1) x2) (Step.leftD x1 h3))) (Steps.cons (Step.root (Root.r21 t3 x1 x2)) (Steps.refl _))))))))))⟩
  | @rightD _ _ t3 h3 =>
    exact ⟨(T.r (T.c (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3))), (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.secondC (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.secondC (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.thirdC (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.c (T.d x0 t3) (T.d x0 t3) x2) (Step.rightD x0 h3))) (Steps.cons (Step.rightR (T.c (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.rightR (T.c (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.rightR (T.c (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (Step.rightD (T.c (T.d x0 t3) (T.d x0 t3) x2) (Step.rightD x0 h3))) (Steps.refl _))))))))), (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD x0 (Step.leftD (T.d x0 t3) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3))))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD x0 (Step.leftD (T.d x0 t3) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3))))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) x0) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) x0) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) x0) (Step.secondC (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) x0) (Step.secondC (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) x0) (Step.thirdC (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.c (T.d x0 t3) (T.d x0 t3) x2) (Step.rightD x0 h3))) (Steps.cons (Step.root (Root.r21 x0 t3 x2)) (Steps.refl _)))))))))⟩
end submission.Austin5837

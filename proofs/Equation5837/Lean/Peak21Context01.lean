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
import Basic
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak21_context_1112 {x0 x1 x2 u : T} (h : Step (T.d x0 x1) u) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) u x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
    · rw [ho]
      exact peak21_root105 he
    · rw [ho]
      exact peak21_root106 he
    · rw [ho]
      exact peak21_root107 he
    · rw [ho]
      exact peak21_root108 he
    · rw [ho]
      exact peak21_root109 he
    · rw [ho]
      exact peak21_root110 he
    · rw [ho]
      exact peak21_root111 he
    · rw [ho]
      exact peak21_root112 he
    · rw [ho]
      exact peak21_root113 he
    · rw [ho]
      exact peak21_root114 he
    · rw [ho]
      exact peak21_root115 he
    · rw [ho]
      exact peak21_root116 he
    · rw [ho]
      exact peak21_root117 he
    · rw [ho]
      exact peak21_root118 he
    · rw [ho]
      exact peak21_root119 he
    · rw [ho]
      exact peak21_root120 he
    · rw [ho]
      exact peak21_root121 he
    · rw [ho]
      exact peak21_root122 he
    · rw [ho]
      exact peak21_root123 he
    · rw [ho]
      exact peak21_root124 he
    · rw [ho]
      exact peak21_root125 he
  | @leftD _ t4 _ h4 =>
    exact ⟨(T.r (T.c (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.d t4 x1)) (T.d (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.d t4 x1))), (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h4)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.secondC (T.d t4 x1) x2 (Step.leftD x1 h4)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.secondC (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h4)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.secondC (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.d x0 x1) (Step.secondC (T.d t4 x1) x2 (Step.leftD x1 h4)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.thirdC (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.c (T.d t4 x1) (T.d t4 x1) x2) (Step.leftD x1 h4))) (Steps.cons (Step.rightR (T.c (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.d t4 x1)) (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h4)))) (Steps.cons (Step.rightR (T.c (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.d t4 x1)) (Step.leftD (T.d x0 x1) (Step.secondC (T.d t4 x1) x2 (Step.leftD x1 h4)))) (Steps.cons (Step.rightR (T.c (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.d t4 x1)) (Step.rightD (T.c (T.d t4 x1) (T.d t4 x1) x2) (Step.leftD x1 h4))) (Steps.refl _))))))))), (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.firstC (T.d t4 x1) x2 (Step.leftD x1 h4))))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD x0 (Step.rightD (T.c (T.d t4 x1) (T.d t4 x1) x2) (Step.leftD x1 h4)))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.rightD (T.d (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.d t4 x1)) h4)) (Steps.cons (Step.right (T.d (T.d (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.d t4 x1)) t4) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h4)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.d t4 x1)) t4) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.secondC (T.d t4 x1) x2 (Step.leftD x1 h4)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.d t4 x1)) t4) (Step.secondC (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h4)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.d t4 x1)) t4) (Step.secondC (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.d x0 x1) (Step.secondC (T.d t4 x1) x2 (Step.leftD x1 h4)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.d t4 x1)) t4) (Step.thirdC (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.c (T.d t4 x1) (T.d t4 x1) x2) (Step.leftD x1 h4))) (Steps.cons (Step.root (Root.r21 t4 x1 x2)) (Steps.refl _))))))))))⟩
  | @rightD _ _ t4 h4 =>
    exact ⟨(T.r (T.c (T.c (T.d x0 t4) (T.d x0 t4) x2) (T.c (T.d x0 t4) (T.d x0 t4) x2) (T.d x0 t4)) (T.d (T.c (T.d x0 t4) (T.d x0 t4) x2) (T.d x0 t4))), (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h4)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.secondC (T.d x0 t4) x2 (Step.rightD x0 h4)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.secondC (T.c (T.d x0 t4) (T.d x0 t4) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h4)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.secondC (T.c (T.d x0 t4) (T.d x0 t4) x2) (T.d x0 x1) (Step.secondC (T.d x0 t4) x2 (Step.rightD x0 h4)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.thirdC (T.c (T.d x0 t4) (T.d x0 t4) x2) (T.c (T.d x0 t4) (T.d x0 t4) x2) (Step.rightD x0 h4))) (Steps.cons (Step.rightR (T.c (T.c (T.d x0 t4) (T.d x0 t4) x2) (T.c (T.d x0 t4) (T.d x0 t4) x2) (T.d x0 t4)) (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h4)))) (Steps.cons (Step.rightR (T.c (T.c (T.d x0 t4) (T.d x0 t4) x2) (T.c (T.d x0 t4) (T.d x0 t4) x2) (T.d x0 t4)) (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t4) x2 (Step.rightD x0 h4)))) (Steps.cons (Step.rightR (T.c (T.c (T.d x0 t4) (T.d x0 t4) x2) (T.c (T.d x0 t4) (T.d x0 t4) x2) (T.d x0 t4)) (Step.rightD (T.c (T.d x0 t4) (T.d x0 t4) x2) (Step.rightD x0 h4))) (Steps.refl _))))))))), (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 t4) x2 (Step.rightD x0 h4))))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD x0 (Step.rightD (T.c (T.d x0 t4) (T.d x0 t4) x2) (Step.rightD x0 h4)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d x0 t4) (T.d x0 t4) x2) (T.d x0 t4)) x0) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h4)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d x0 t4) (T.d x0 t4) x2) (T.d x0 t4)) x0) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.secondC (T.d x0 t4) x2 (Step.rightD x0 h4)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d x0 t4) (T.d x0 t4) x2) (T.d x0 t4)) x0) (Step.secondC (T.c (T.d x0 t4) (T.d x0 t4) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h4)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d x0 t4) (T.d x0 t4) x2) (T.d x0 t4)) x0) (Step.secondC (T.c (T.d x0 t4) (T.d x0 t4) x2) (T.d x0 x1) (Step.secondC (T.d x0 t4) x2 (Step.rightD x0 h4)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d x0 t4) (T.d x0 t4) x2) (T.d x0 t4)) x0) (Step.thirdC (T.c (T.d x0 t4) (T.d x0 t4) x2) (T.c (T.d x0 t4) (T.d x0 t4) x2) (Step.rightD x0 h4))) (Steps.cons (Step.root (Root.r21 x0 t4 x2)) (Steps.refl _)))))))))⟩
end submission.Austin5837

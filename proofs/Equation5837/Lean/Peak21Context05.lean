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
import Basic
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak21_context_1 {x0 x1 x2 u : T} (h : Step (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) u) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m u (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
    · rw [ho]
      exact peak21_root21 he
    · rw [ho]
      exact peak21_root22 he
    · rw [ho]
      exact peak21_root23 he
    · rw [ho]
      exact peak21_root24 he
    · rw [ho]
      exact peak21_root25 he
    · rw [ho]
      exact peak21_root26 he
    · rw [ho]
      exact peak21_root27 he
    · rw [ho]
      exact peak21_root28 he
    · rw [ho]
      exact peak21_root29 he
    · rw [ho]
      exact peak21_root30 he
    · rw [ho]
      exact peak21_root31 he
    · rw [ho]
      exact peak21_root32 he
    · rw [ho]
      exact peak21_root33 he
    · rw [ho]
      exact peak21_root34 he
    · rw [ho]
      exact peak21_root35 he
    · rw [ho]
      exact peak21_root36 he
    · rw [ho]
      exact peak21_root37 he
    · rw [ho]
      exact peak21_root38 he
    · rw [ho]
      exact peak21_root39 he
    · rw [ho]
      exact peak21_root40 he
    · rw [ho]
      exact peak21_root41 he
  | @leftD _ t1 _ h1 =>
    exact peak21_context_11 h1
  | @rightD _ _ t1 h1 =>
    exact ⟨(T.r (T.c (T.c (T.d t1 x1) (T.d t1 x1) x2) (T.c (T.d t1 x1) (T.d t1 x1) x2) (T.d t1 x1)) (T.d (T.c (T.d t1 x1) (T.d t1 x1) x2) (T.d t1 x1))), (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h1)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.secondC (T.d t1 x1) x2 (Step.leftD x1 h1)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.secondC (T.c (T.d t1 x1) (T.d t1 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h1)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.secondC (T.c (T.d t1 x1) (T.d t1 x1) x2) (T.d x0 x1) (Step.secondC (T.d t1 x1) x2 (Step.leftD x1 h1)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.thirdC (T.c (T.d t1 x1) (T.d t1 x1) x2) (T.c (T.d t1 x1) (T.d t1 x1) x2) (Step.leftD x1 h1))) (Steps.cons (Step.rightR (T.c (T.c (T.d t1 x1) (T.d t1 x1) x2) (T.c (T.d t1 x1) (T.d t1 x1) x2) (T.d t1 x1)) (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h1)))) (Steps.cons (Step.rightR (T.c (T.c (T.d t1 x1) (T.d t1 x1) x2) (T.c (T.d t1 x1) (T.d t1 x1) x2) (T.d t1 x1)) (Step.leftD (T.d x0 x1) (Step.secondC (T.d t1 x1) x2 (Step.leftD x1 h1)))) (Steps.cons (Step.rightR (T.c (T.c (T.d t1 x1) (T.d t1 x1) x2) (T.c (T.d t1 x1) (T.d t1 x1) x2) (T.d t1 x1)) (Step.rightD (T.c (T.d t1 x1) (T.d t1 x1) x2) (Step.leftD x1 h1))) (Steps.refl _))))))))), (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD t1 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h1))))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD t1 (Step.leftD (T.d x0 x1) (Step.secondC (T.d t1 x1) x2 (Step.leftD x1 h1))))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD t1 (Step.rightD (T.c (T.d t1 x1) (T.d t1 x1) x2) (Step.leftD x1 h1)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d t1 x1) (T.d t1 x1) x2) (T.d t1 x1)) t1) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h1)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d t1 x1) (T.d t1 x1) x2) (T.d t1 x1)) t1) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.secondC (T.d t1 x1) x2 (Step.leftD x1 h1)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d t1 x1) (T.d t1 x1) x2) (T.d t1 x1)) t1) (Step.secondC (T.c (T.d t1 x1) (T.d t1 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h1)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d t1 x1) (T.d t1 x1) x2) (T.d t1 x1)) t1) (Step.secondC (T.c (T.d t1 x1) (T.d t1 x1) x2) (T.d x0 x1) (Step.secondC (T.d t1 x1) x2 (Step.leftD x1 h1)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d t1 x1) (T.d t1 x1) x2) (T.d t1 x1)) t1) (Step.thirdC (T.c (T.d t1 x1) (T.d t1 x1) x2) (T.c (T.d t1 x1) (T.d t1 x1) x2) (Step.leftD x1 h1))) (Steps.cons (Step.root (Root.r21 t1 x1 x2)) (Steps.refl _))))))))))⟩
end submission.Austin5837

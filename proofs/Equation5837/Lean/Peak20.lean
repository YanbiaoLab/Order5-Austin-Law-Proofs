import Peak20Roots00
import Peak20Roots01
import Peak20Roots02
import Peak20Roots03
import Peak20Roots04
import Peak20Roots05
import Peak20Roots06
import Peak20Roots07
import Peak20Roots08
import Peak20Roots09
import Peak20Roots10
import Peak20Roots11
import Peak20Roots12
import Peak20Roots13
import Basic
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak20 (x0 : T) (x1 : T) (x2 : T) {u : T} (h : Step (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) u) : Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) u := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
    · rw [ho]
      exact peak20_root0 he
    · rw [ho]
      exact peak20_root1 he
    · rw [ho]
      exact peak20_root2 he
    · rw [ho]
      exact peak20_root3 he
    · rw [ho]
      exact peak20_root4 he
    · rw [ho]
      exact peak20_root5 he
    · rw [ho]
      exact peak20_root6 he
    · rw [ho]
      exact peak20_root7 he
    · rw [ho]
      exact peak20_root8 he
    · rw [ho]
      exact peak20_root9 he
    · rw [ho]
      exact peak20_root10 he
    · rw [ho]
      exact peak20_root11 he
    · rw [ho]
      exact peak20_root12 he
    · rw [ho]
      exact peak20_root13 he
    · rw [ho]
      exact peak20_root14 he
    · rw [ho]
      exact peak20_root15 he
    · rw [ho]
      exact peak20_root16 he
    · rw [ho]
      exact peak20_root17 he
    · rw [ho]
      exact peak20_root18 he
    · rw [ho]
      exact peak20_root19 he
    · rw [ho]
      exact peak20_root20 he
  | @left _ t0 _ h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
      · rw [ho]
        exact peak20_root21 he
      · rw [ho]
        exact peak20_root22 he
      · rw [ho]
        exact peak20_root23 he
      · rw [ho]
        exact peak20_root24 he
      · rw [ho]
        exact peak20_root25 he
      · rw [ho]
        exact peak20_root26 he
      · rw [ho]
        exact peak20_root27 he
      · rw [ho]
        exact peak20_root28 he
      · rw [ho]
        exact peak20_root29 he
      · rw [ho]
        exact peak20_root30 he
      · rw [ho]
        exact peak20_root31 he
      · rw [ho]
        exact peak20_root32 he
      · rw [ho]
        exact peak20_root33 he
      · rw [ho]
        exact peak20_root34 he
      · rw [ho]
        exact peak20_root35 he
      · rw [ho]
        exact peak20_root36 he
      · rw [ho]
        exact peak20_root37 he
      · rw [ho]
        exact peak20_root38 he
      · rw [ho]
        exact peak20_root39 he
      · rw [ho]
        exact peak20_root40 he
      · rw [ho]
        exact peak20_root41 he
    | @leftD _ t1 _ h1 =>
      cases h1 with
      | root hr =>
        rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
        · rw [ho]
          exact peak20_root42 he
        · rw [ho]
          exact peak20_root43 he
        · rw [ho]
          exact peak20_root44 he
        · rw [ho]
          exact peak20_root45 he
        · rw [ho]
          exact peak20_root46 he
        · rw [ho]
          exact peak20_root47 he
        · rw [ho]
          exact peak20_root48 he
        · rw [ho]
          exact peak20_root49 he
        · rw [ho]
          exact peak20_root50 he
        · rw [ho]
          exact peak20_root51 he
        · rw [ho]
          exact peak20_root52 he
        · rw [ho]
          exact peak20_root53 he
        · rw [ho]
          exact peak20_root54 he
        · rw [ho]
          exact peak20_root55 he
        · rw [ho]
          exact peak20_root56 he
        · rw [ho]
          exact peak20_root57 he
        · rw [ho]
          exact peak20_root58 he
        · rw [ho]
          exact peak20_root59 he
        · rw [ho]
          exact peak20_root60 he
        · rw [ho]
          exact peak20_root61 he
        · rw [ho]
          exact peak20_root62 he
      | @firstC _ t2 _ _ h2 =>
        cases h2 with
        | root hr =>
          rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
          · rw [ho]
            exact peak20_root63 he
          · rw [ho]
            exact peak20_root64 he
          · rw [ho]
            exact peak20_root65 he
          · rw [ho]
            exact peak20_root66 he
          · rw [ho]
            exact peak20_root67 he
          · rw [ho]
            exact peak20_root68 he
          · rw [ho]
            exact peak20_root69 he
          · rw [ho]
            exact peak20_root70 he
          · rw [ho]
            exact peak20_root71 he
          · rw [ho]
            exact peak20_root72 he
          · rw [ho]
            exact peak20_root73 he
          · rw [ho]
            exact peak20_root74 he
          · rw [ho]
            exact peak20_root75 he
          · rw [ho]
            exact peak20_root76 he
          · rw [ho]
            exact peak20_root77 he
          · rw [ho]
            exact peak20_root78 he
          · rw [ho]
            exact peak20_root79 he
          · rw [ho]
            exact peak20_root80 he
          · rw [ho]
            exact peak20_root81 he
          · rw [ho]
            exact peak20_root82 he
          · rw [ho]
            exact peak20_root83 he
        | @leftD _ t3 _ h3 =>
          exact ⟨(T.d (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) t3), (Steps.cons (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.leftD x0 (Step.rightD (T.c (T.d t3 x1) (T.d t3 x1) x2) (Step.leftD x1 h3))) (Steps.cons (Step.rightD (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) h3) (Steps.refl _))))), (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.rightD (T.c (T.d t3 x1) (T.d t3 x1) x2) (Step.leftD x1 h3))) (Steps.cons (Step.right (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.right (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.right (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (Step.secondC (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.right (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (Step.secondC (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.right (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (Step.thirdC (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.c (T.d t3 x1) (T.d t3 x1) x2) (Step.leftD x1 h3))) (Steps.cons (Step.root (Root.r20 t3 x1 x2)) (Steps.refl _)))))))))⟩
        | @rightD _ _ t3 h3 =>
          exact ⟨(T.d (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) x0), (Steps.cons (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.leftD x0 (Step.rightD (T.c (T.d x0 t3) (T.d x0 t3) x2) (Step.rightD x0 h3))) (Steps.refl _)))), (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.rightD (T.c (T.d x0 t3) (T.d x0 t3) x2) (Step.rightD x0 h3))) (Steps.cons (Step.right (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (Step.secondC (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (Step.secondC (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (Step.thirdC (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.c (T.d x0 t3) (T.d x0 t3) x2) (Step.rightD x0 h3))) (Steps.cons (Step.root (Root.r20 x0 t3 x2)) (Steps.refl _)))))))))⟩
      | @secondC _ _ t2 _ h2 =>
        cases h2 with
        | root hr =>
          rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
          · rw [ho]
            exact peak20_root84 he
          · rw [ho]
            exact peak20_root85 he
          · rw [ho]
            exact peak20_root86 he
          · rw [ho]
            exact peak20_root87 he
          · rw [ho]
            exact peak20_root88 he
          · rw [ho]
            exact peak20_root89 he
          · rw [ho]
            exact peak20_root90 he
          · rw [ho]
            exact peak20_root91 he
          · rw [ho]
            exact peak20_root92 he
          · rw [ho]
            exact peak20_root93 he
          · rw [ho]
            exact peak20_root94 he
          · rw [ho]
            exact peak20_root95 he
          · rw [ho]
            exact peak20_root96 he
          · rw [ho]
            exact peak20_root97 he
          · rw [ho]
            exact peak20_root98 he
          · rw [ho]
            exact peak20_root99 he
          · rw [ho]
            exact peak20_root100 he
          · rw [ho]
            exact peak20_root101 he
          · rw [ho]
            exact peak20_root102 he
          · rw [ho]
            exact peak20_root103 he
          · rw [ho]
            exact peak20_root104 he
        | @leftD _ t3 _ h3 =>
          exact ⟨(T.d (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) t3), (Steps.cons (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.leftD x0 (Step.rightD (T.c (T.d t3 x1) (T.d t3 x1) x2) (Step.leftD x1 h3))) (Steps.cons (Step.rightD (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) h3) (Steps.refl _))))), (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD (T.d x0 x1) (Step.firstC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.rightD (T.c (T.d t3 x1) (T.d t3 x1) x2) (Step.leftD x1 h3))) (Steps.cons (Step.right (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.right (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.right (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (Step.secondC (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.right (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (Step.secondC (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.right (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (Step.thirdC (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.c (T.d t3 x1) (T.d t3 x1) x2) (Step.leftD x1 h3))) (Steps.cons (Step.root (Root.r20 t3 x1 x2)) (Steps.refl _)))))))))⟩
        | @rightD _ _ t3 h3 =>
          exact ⟨(T.d (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) x0), (Steps.cons (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.leftD x0 (Step.rightD (T.c (T.d x0 t3) (T.d x0 t3) x2) (Step.rightD x0 h3))) (Steps.refl _)))), (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.rightD (T.c (T.d x0 t3) (T.d x0 t3) x2) (Step.rightD x0 h3))) (Steps.cons (Step.right (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (Step.secondC (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (Step.secondC (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (Step.thirdC (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.c (T.d x0 t3) (T.d x0 t3) x2) (Step.rightD x0 h3))) (Steps.cons (Step.root (Root.r20 x0 t3 x2)) (Steps.refl _)))))))))⟩
      | @thirdC _ _ _ t2 h2 =>
        exact ⟨(T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) t2) (T.d x0 x1)) x0), (Steps.cons (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.thirdC (T.d x0 x1) (T.d x0 x1) h2))) (Steps.refl _)), (Steps.cons (Step.right (T.d (T.c (T.d x0 x1) (T.d x0 x1) t2) (T.d x0 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.thirdC (T.d x0 x1) (T.d x0 x1) h2))) (Steps.cons (Step.right (T.d (T.c (T.d x0 x1) (T.d x0 x1) t2) (T.d x0 x1)) (Step.secondC (T.c (T.d x0 x1) (T.d x0 x1) t2) (T.d x0 x1) (Step.thirdC (T.d x0 x1) (T.d x0 x1) h2))) (Steps.cons (Step.root (Root.r20 x0 x1 t2)) (Steps.refl _))))⟩
    | @rightD _ _ t1 h1 =>
      cases h1 with
      | root hr =>
        rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
        · rw [ho]
          exact peak20_root105 he
        · rw [ho]
          exact peak20_root106 he
        · rw [ho]
          exact peak20_root107 he
        · rw [ho]
          exact peak20_root108 he
        · rw [ho]
          exact peak20_root109 he
        · rw [ho]
          exact peak20_root110 he
        · rw [ho]
          exact peak20_root111 he
        · rw [ho]
          exact peak20_root112 he
        · rw [ho]
          exact peak20_root113 he
        · rw [ho]
          exact peak20_root114 he
        · rw [ho]
          exact peak20_root115 he
        · rw [ho]
          exact peak20_root116 he
        · rw [ho]
          exact peak20_root117 he
        · rw [ho]
          exact peak20_root118 he
        · rw [ho]
          exact peak20_root119 he
        · rw [ho]
          exact peak20_root120 he
        · rw [ho]
          exact peak20_root121 he
        · rw [ho]
          exact peak20_root122 he
        · rw [ho]
          exact peak20_root123 he
        · rw [ho]
          exact peak20_root124 he
        · rw [ho]
          exact peak20_root125 he
      | @leftD _ t2 _ h2 =>
        exact ⟨(T.d (T.d (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.d t2 x1)) t2), (Steps.cons (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h2)))) (Steps.cons (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.secondC (T.d t2 x1) x2 (Step.leftD x1 h2)))) (Steps.cons (Step.leftD x0 (Step.rightD (T.c (T.d t2 x1) (T.d t2 x1) x2) (Step.leftD x1 h2))) (Steps.cons (Step.rightD (T.d (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.d t2 x1)) h2) (Steps.refl _))))), (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD (T.d t2 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h2)))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD (T.d t2 x1) (Step.secondC (T.d t2 x1) x2 (Step.leftD x1 h2)))) (Steps.cons (Step.right (T.d (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.d t2 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h2)))) (Steps.cons (Step.right (T.d (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.d t2 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.secondC (T.d t2 x1) x2 (Step.leftD x1 h2)))) (Steps.cons (Step.right (T.d (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.d t2 x1)) (Step.secondC (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h2)))) (Steps.cons (Step.right (T.d (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.d t2 x1)) (Step.secondC (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.d x0 x1) (Step.secondC (T.d t2 x1) x2 (Step.leftD x1 h2)))) (Steps.cons (Step.right (T.d (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.d t2 x1)) (Step.thirdC (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.c (T.d t2 x1) (T.d t2 x1) x2) (Step.leftD x1 h2))) (Steps.cons (Step.root (Root.r20 t2 x1 x2)) (Steps.refl _)))))))))⟩
      | @rightD _ _ t2 h2 =>
        exact ⟨(T.d (T.d (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.d x0 t2)) x0), (Steps.cons (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h2)))) (Steps.cons (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t2) x2 (Step.rightD x0 h2)))) (Steps.cons (Step.leftD x0 (Step.rightD (T.c (T.d x0 t2) (T.d x0 t2) x2) (Step.rightD x0 h2))) (Steps.refl _)))), (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD (T.d x0 t2) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h2)))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD (T.d x0 t2) (Step.secondC (T.d x0 t2) x2 (Step.rightD x0 h2)))) (Steps.cons (Step.right (T.d (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.d x0 t2)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h2)))) (Steps.cons (Step.right (T.d (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.d x0 t2)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.secondC (T.d x0 t2) x2 (Step.rightD x0 h2)))) (Steps.cons (Step.right (T.d (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.d x0 t2)) (Step.secondC (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h2)))) (Steps.cons (Step.right (T.d (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.d x0 t2)) (Step.secondC (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.d x0 x1) (Step.secondC (T.d x0 t2) x2 (Step.rightD x0 h2)))) (Steps.cons (Step.right (T.d (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.d x0 t2)) (Step.thirdC (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.c (T.d x0 t2) (T.d x0 t2) x2) (Step.rightD x0 h2))) (Steps.cons (Step.root (Root.r20 x0 t2 x2)) (Steps.refl _)))))))))⟩
  | @right _ _ t0 h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
      · rw [ho]
        exact peak20_root126 he
      · rw [ho]
        exact peak20_root127 he
      · rw [ho]
        exact peak20_root128 he
      · rw [ho]
        exact peak20_root129 he
      · rw [ho]
        exact peak20_root130 he
      · rw [ho]
        exact peak20_root131 he
      · rw [ho]
        exact peak20_root132 he
      · rw [ho]
        exact peak20_root133 he
      · rw [ho]
        exact peak20_root134 he
      · rw [ho]
        exact peak20_root135 he
      · rw [ho]
        exact peak20_root136 he
      · rw [ho]
        exact peak20_root137 he
      · rw [ho]
        exact peak20_root138 he
      · rw [ho]
        exact peak20_root139 he
      · rw [ho]
        exact peak20_root140 he
      · rw [ho]
        exact peak20_root141 he
      · rw [ho]
        exact peak20_root142 he
      · rw [ho]
        exact peak20_root143 he
      · rw [ho]
        exact peak20_root144 he
      · rw [ho]
        exact peak20_root145 he
      · rw [ho]
        exact peak20_root146 he
    | @firstC _ t1 _ _ h1 =>
      cases h1 with
      | root hr =>
        rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
        · rw [ho]
          exact peak20_root147 he
        · rw [ho]
          exact peak20_root148 he
        · rw [ho]
          exact peak20_root149 he
        · rw [ho]
          exact peak20_root150 he
        · rw [ho]
          exact peak20_root151 he
        · rw [ho]
          exact peak20_root152 he
        · rw [ho]
          exact peak20_root153 he
        · rw [ho]
          exact peak20_root154 he
        · rw [ho]
          exact peak20_root155 he
        · rw [ho]
          exact peak20_root156 he
        · rw [ho]
          exact peak20_root157 he
        · rw [ho]
          exact peak20_root158 he
        · rw [ho]
          exact peak20_root159 he
        · rw [ho]
          exact peak20_root160 he
        · rw [ho]
          exact peak20_root161 he
        · rw [ho]
          exact peak20_root162 he
        · rw [ho]
          exact peak20_root163 he
        · rw [ho]
          exact peak20_root164 he
        · rw [ho]
          exact peak20_root165 he
        · rw [ho]
          exact peak20_root166 he
        · rw [ho]
          exact peak20_root167 he
      | @firstC _ t2 _ _ h2 =>
        cases h2 with
        | root hr =>
          rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
          · rw [ho]
            exact peak20_root168 he
          · rw [ho]
            exact peak20_root169 he
          · rw [ho]
            exact peak20_root170 he
          · rw [ho]
            exact peak20_root171 he
          · rw [ho]
            exact peak20_root172 he
          · rw [ho]
            exact peak20_root173 he
          · rw [ho]
            exact peak20_root174 he
          · rw [ho]
            exact peak20_root175 he
          · rw [ho]
            exact peak20_root176 he
          · rw [ho]
            exact peak20_root177 he
          · rw [ho]
            exact peak20_root178 he
          · rw [ho]
            exact peak20_root179 he
          · rw [ho]
            exact peak20_root180 he
          · rw [ho]
            exact peak20_root181 he
          · rw [ho]
            exact peak20_root182 he
          · rw [ho]
            exact peak20_root183 he
          · rw [ho]
            exact peak20_root184 he
          · rw [ho]
            exact peak20_root185 he
          · rw [ho]
            exact peak20_root186 he
          · rw [ho]
            exact peak20_root187 he
          · rw [ho]
            exact peak20_root188 he
        | @leftD _ t3 _ h3 =>
          exact ⟨(T.d (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) t3), (Steps.cons (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.leftD x0 (Step.rightD (T.c (T.d t3 x1) (T.d t3 x1) x2) (Step.leftD x1 h3))) (Steps.cons (Step.rightD (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) h3) (Steps.refl _))))), (Steps.cons (Step.left (T.c (T.c (T.d t3 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.left (T.c (T.c (T.d t3 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.left (T.c (T.c (T.d t3 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.rightD (T.c (T.d t3 x1) (T.d t3 x1) x2) (Step.leftD x1 h3))) (Steps.cons (Step.right (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.right (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (Step.secondC (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.right (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (Step.secondC (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.right (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (Step.thirdC (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.c (T.d t3 x1) (T.d t3 x1) x2) (Step.leftD x1 h3))) (Steps.cons (Step.root (Root.r20 t3 x1 x2)) (Steps.refl _)))))))))⟩
        | @rightD _ _ t3 h3 =>
          exact ⟨(T.d (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) x0), (Steps.cons (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.leftD x0 (Step.rightD (T.c (T.d x0 t3) (T.d x0 t3) x2) (Step.rightD x0 h3))) (Steps.refl _)))), (Steps.cons (Step.left (T.c (T.c (T.d x0 t3) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.left (T.c (T.c (T.d x0 t3) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.left (T.c (T.c (T.d x0 t3) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.rightD (T.c (T.d x0 t3) (T.d x0 t3) x2) (Step.rightD x0 h3))) (Steps.cons (Step.right (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (Step.secondC (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (Step.secondC (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (Step.thirdC (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.c (T.d x0 t3) (T.d x0 t3) x2) (Step.rightD x0 h3))) (Steps.cons (Step.root (Root.r20 x0 t3 x2)) (Steps.refl _)))))))))⟩
      | @secondC _ _ t2 _ h2 =>
        cases h2 with
        | root hr =>
          rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
          · rw [ho]
            exact peak20_root189 he
          · rw [ho]
            exact peak20_root190 he
          · rw [ho]
            exact peak20_root191 he
          · rw [ho]
            exact peak20_root192 he
          · rw [ho]
            exact peak20_root193 he
          · rw [ho]
            exact peak20_root194 he
          · rw [ho]
            exact peak20_root195 he
          · rw [ho]
            exact peak20_root196 he
          · rw [ho]
            exact peak20_root197 he
          · rw [ho]
            exact peak20_root198 he
          · rw [ho]
            exact peak20_root199 he
          · rw [ho]
            exact peak20_root200 he
          · rw [ho]
            exact peak20_root201 he
          · rw [ho]
            exact peak20_root202 he
          · rw [ho]
            exact peak20_root203 he
          · rw [ho]
            exact peak20_root204 he
          · rw [ho]
            exact peak20_root205 he
          · rw [ho]
            exact peak20_root206 he
          · rw [ho]
            exact peak20_root207 he
          · rw [ho]
            exact peak20_root208 he
          · rw [ho]
            exact peak20_root209 he
        | @leftD _ t3 _ h3 =>
          exact ⟨(T.d (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) t3), (Steps.cons (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.leftD x0 (Step.rightD (T.c (T.d t3 x1) (T.d t3 x1) x2) (Step.leftD x1 h3))) (Steps.cons (Step.rightD (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) h3) (Steps.refl _))))), (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d t3 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d t3 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d t3 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.rightD (T.c (T.d t3 x1) (T.d t3 x1) x2) (Step.leftD x1 h3))) (Steps.cons (Step.right (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.firstC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.right (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (Step.secondC (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.right (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (Step.secondC (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.right (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (Step.thirdC (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.c (T.d t3 x1) (T.d t3 x1) x2) (Step.leftD x1 h3))) (Steps.cons (Step.root (Root.r20 t3 x1 x2)) (Steps.refl _)))))))))⟩
        | @rightD _ _ t3 h3 =>
          exact ⟨(T.d (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) x0), (Steps.cons (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.leftD x0 (Step.rightD (T.c (T.d x0 t3) (T.d x0 t3) x2) (Step.rightD x0 h3))) (Steps.refl _)))), (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 t3) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 t3) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 t3) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.rightD (T.c (T.d x0 t3) (T.d x0 t3) x2) (Step.rightD x0 h3))) (Steps.cons (Step.right (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (Step.secondC (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (Step.secondC (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (Step.thirdC (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.c (T.d x0 t3) (T.d x0 t3) x2) (Step.rightD x0 h3))) (Steps.cons (Step.root (Root.r20 x0 t3 x2)) (Steps.refl _)))))))))⟩
      | @thirdC _ _ _ t2 h2 =>
        exact ⟨(T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) t2) (T.d x0 x1)) x0), (Steps.cons (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.thirdC (T.d x0 x1) (T.d x0 x1) h2))) (Steps.refl _)), (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) t2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD (T.d x0 x1) (Step.thirdC (T.d x0 x1) (T.d x0 x1) h2))) (Steps.cons (Step.right (T.d (T.c (T.d x0 x1) (T.d x0 x1) t2) (T.d x0 x1)) (Step.secondC (T.c (T.d x0 x1) (T.d x0 x1) t2) (T.d x0 x1) (Step.thirdC (T.d x0 x1) (T.d x0 x1) h2))) (Steps.cons (Step.root (Root.r20 x0 x1 t2)) (Steps.refl _))))⟩
    | @secondC _ _ t1 _ h1 =>
      cases h1 with
      | root hr =>
        rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
        · rw [ho]
          exact peak20_root210 he
        · rw [ho]
          exact peak20_root211 he
        · rw [ho]
          exact peak20_root212 he
        · rw [ho]
          exact peak20_root213 he
        · rw [ho]
          exact peak20_root214 he
        · rw [ho]
          exact peak20_root215 he
        · rw [ho]
          exact peak20_root216 he
        · rw [ho]
          exact peak20_root217 he
        · rw [ho]
          exact peak20_root218 he
        · rw [ho]
          exact peak20_root219 he
        · rw [ho]
          exact peak20_root220 he
        · rw [ho]
          exact peak20_root221 he
        · rw [ho]
          exact peak20_root222 he
        · rw [ho]
          exact peak20_root223 he
        · rw [ho]
          exact peak20_root224 he
        · rw [ho]
          exact peak20_root225 he
        · rw [ho]
          exact peak20_root226 he
        · rw [ho]
          exact peak20_root227 he
        · rw [ho]
          exact peak20_root228 he
        · rw [ho]
          exact peak20_root229 he
        · rw [ho]
          exact peak20_root230 he
      | @firstC _ t2 _ _ h2 =>
        cases h2 with
        | root hr =>
          rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
          · rw [ho]
            exact peak20_root231 he
          · rw [ho]
            exact peak20_root232 he
          · rw [ho]
            exact peak20_root233 he
          · rw [ho]
            exact peak20_root234 he
          · rw [ho]
            exact peak20_root235 he
          · rw [ho]
            exact peak20_root236 he
          · rw [ho]
            exact peak20_root237 he
          · rw [ho]
            exact peak20_root238 he
          · rw [ho]
            exact peak20_root239 he
          · rw [ho]
            exact peak20_root240 he
          · rw [ho]
            exact peak20_root241 he
          · rw [ho]
            exact peak20_root242 he
          · rw [ho]
            exact peak20_root243 he
          · rw [ho]
            exact peak20_root244 he
          · rw [ho]
            exact peak20_root245 he
          · rw [ho]
            exact peak20_root246 he
          · rw [ho]
            exact peak20_root247 he
          · rw [ho]
            exact peak20_root248 he
          · rw [ho]
            exact peak20_root249 he
          · rw [ho]
            exact peak20_root250 he
          · rw [ho]
            exact peak20_root251 he
        | @leftD _ t3 _ h3 =>
          exact ⟨(T.d (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) t3), (Steps.cons (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.leftD x0 (Step.rightD (T.c (T.d t3 x1) (T.d t3 x1) x2) (Step.leftD x1 h3))) (Steps.cons (Step.rightD (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) h3) (Steps.refl _))))), (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d t3 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d t3 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d t3 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.rightD (T.c (T.d t3 x1) (T.d t3 x1) x2) (Step.leftD x1 h3))) (Steps.cons (Step.right (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (Step.firstC (T.c (T.d t3 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.right (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (Step.firstC (T.c (T.d t3 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.right (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (Step.secondC (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.right (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (Step.thirdC (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.c (T.d t3 x1) (T.d t3 x1) x2) (Step.leftD x1 h3))) (Steps.cons (Step.root (Root.r20 t3 x1 x2)) (Steps.refl _)))))))))⟩
        | @rightD _ _ t3 h3 =>
          exact ⟨(T.d (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) x0), (Steps.cons (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.leftD x0 (Step.rightD (T.c (T.d x0 t3) (T.d x0 t3) x2) (Step.rightD x0 h3))) (Steps.refl _)))), (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 t3) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 t3) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 t3) (T.d x0 x1) x2) (T.d x0 x1)) (Step.rightD (T.c (T.d x0 t3) (T.d x0 t3) x2) (Step.rightD x0 h3))) (Steps.cons (Step.right (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (Step.firstC (T.c (T.d x0 t3) (T.d x0 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (Step.firstC (T.c (T.d x0 t3) (T.d x0 x1) x2) (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (Step.secondC (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (Step.thirdC (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.c (T.d x0 t3) (T.d x0 t3) x2) (Step.rightD x0 h3))) (Steps.cons (Step.root (Root.r20 x0 t3 x2)) (Steps.refl _)))))))))⟩
      | @secondC _ _ t2 _ h2 =>
        cases h2 with
        | root hr =>
          rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
          · rw [ho]
            exact peak20_root252 he
          · rw [ho]
            exact peak20_root253 he
          · rw [ho]
            exact peak20_root254 he
          · rw [ho]
            exact peak20_root255 he
          · rw [ho]
            exact peak20_root256 he
          · rw [ho]
            exact peak20_root257 he
          · rw [ho]
            exact peak20_root258 he
          · rw [ho]
            exact peak20_root259 he
          · rw [ho]
            exact peak20_root260 he
          · rw [ho]
            exact peak20_root261 he
          · rw [ho]
            exact peak20_root262 he
          · rw [ho]
            exact peak20_root263 he
          · rw [ho]
            exact peak20_root264 he
          · rw [ho]
            exact peak20_root265 he
          · rw [ho]
            exact peak20_root266 he
          · rw [ho]
            exact peak20_root267 he
          · rw [ho]
            exact peak20_root268 he
          · rw [ho]
            exact peak20_root269 he
          · rw [ho]
            exact peak20_root270 he
          · rw [ho]
            exact peak20_root271 he
          · rw [ho]
            exact peak20_root272 he
        | @leftD _ t3 _ h3 =>
          exact ⟨(T.d (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) t3), (Steps.cons (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.leftD x0 (Step.rightD (T.c (T.d t3 x1) (T.d t3 x1) x2) (Step.leftD x1 h3))) (Steps.cons (Step.rightD (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) h3) (Steps.refl _))))), (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d t3 x1) x2) (T.d x0 x1)) (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d t3 x1) x2) (T.d x0 x1)) (Step.leftD (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d t3 x1) x2) (T.d x0 x1)) (Step.rightD (T.c (T.d t3 x1) (T.d t3 x1) x2) (Step.leftD x1 h3))) (Steps.cons (Step.right (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d t3 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.right (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d t3 x1) x2) (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.right (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (Step.secondC (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d x0 x1) (Step.firstC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.right (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (Step.thirdC (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.c (T.d t3 x1) (T.d t3 x1) x2) (Step.leftD x1 h3))) (Steps.cons (Step.root (Root.r20 t3 x1 x2)) (Steps.refl _)))))))))⟩
        | @rightD _ _ t3 h3 =>
          exact ⟨(T.d (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) x0), (Steps.cons (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.leftD x0 (Step.rightD (T.c (T.d x0 t3) (T.d x0 t3) x2) (Step.rightD x0 h3))) (Steps.refl _)))), (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 t3) x2) (T.d x0 x1)) (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 t3) x2) (T.d x0 x1)) (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 t3) x2) (T.d x0 x1)) (Step.rightD (T.c (T.d x0 t3) (T.d x0 t3) x2) (Step.rightD x0 h3))) (Steps.cons (Step.right (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 t3) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 t3) x2) (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (Step.secondC (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 x1) (Step.firstC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (Step.thirdC (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.c (T.d x0 t3) (T.d x0 t3) x2) (Step.rightD x0 h3))) (Steps.cons (Step.root (Root.r20 x0 t3 x2)) (Steps.refl _)))))))))⟩
      | @thirdC _ _ _ t2 h2 =>
        exact ⟨(T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) t2) (T.d x0 x1)) x0), (Steps.cons (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.thirdC (T.d x0 x1) (T.d x0 x1) h2))) (Steps.refl _)), (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) t2) (T.d x0 x1)) (Step.leftD (T.d x0 x1) (Step.thirdC (T.d x0 x1) (T.d x0 x1) h2))) (Steps.cons (Step.right (T.d (T.c (T.d x0 x1) (T.d x0 x1) t2) (T.d x0 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) t2) (T.d x0 x1) (Step.thirdC (T.d x0 x1) (T.d x0 x1) h2))) (Steps.cons (Step.root (Root.r20 x0 x1 t2)) (Steps.refl _))))⟩
    | @thirdC _ _ _ t1 h1 =>
      cases h1 with
      | root hr =>
        rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
        · rw [ho]
          exact peak20_root273 he
        · rw [ho]
          exact peak20_root274 he
        · rw [ho]
          exact peak20_root275 he
        · rw [ho]
          exact peak20_root276 he
        · rw [ho]
          exact peak20_root277 he
        · rw [ho]
          exact peak20_root278 he
        · rw [ho]
          exact peak20_root279 he
        · rw [ho]
          exact peak20_root280 he
        · rw [ho]
          exact peak20_root281 he
        · rw [ho]
          exact peak20_root282 he
        · rw [ho]
          exact peak20_root283 he
        · rw [ho]
          exact peak20_root284 he
        · rw [ho]
          exact peak20_root285 he
        · rw [ho]
          exact peak20_root286 he
        · rw [ho]
          exact peak20_root287 he
        · rw [ho]
          exact peak20_root288 he
        · rw [ho]
          exact peak20_root289 he
        · rw [ho]
          exact peak20_root290 he
        · rw [ho]
          exact peak20_root291 he
        · rw [ho]
          exact peak20_root292 he
        · rw [ho]
          exact peak20_root293 he
      | @leftD _ t2 _ h2 =>
        exact ⟨(T.d (T.d (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.d t2 x1)) t2), (Steps.cons (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h2)))) (Steps.cons (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.secondC (T.d t2 x1) x2 (Step.leftD x1 h2)))) (Steps.cons (Step.leftD x0 (Step.rightD (T.c (T.d t2 x1) (T.d t2 x1) x2) (Step.leftD x1 h2))) (Steps.cons (Step.rightD (T.d (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.d t2 x1)) h2) (Steps.refl _))))), (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d t2 x1)) (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h2)))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d t2 x1)) (Step.leftD (T.d x0 x1) (Step.secondC (T.d t2 x1) x2 (Step.leftD x1 h2)))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d t2 x1)) (Step.rightD (T.c (T.d t2 x1) (T.d t2 x1) x2) (Step.leftD x1 h2))) (Steps.cons (Step.right (T.d (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.d t2 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d t2 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h2)))) (Steps.cons (Step.right (T.d (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.d t2 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d t2 x1) (Step.secondC (T.d t2 x1) x2 (Step.leftD x1 h2)))) (Steps.cons (Step.right (T.d (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.d t2 x1)) (Step.secondC (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.d t2 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h2)))) (Steps.cons (Step.right (T.d (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.d t2 x1)) (Step.secondC (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.d t2 x1) (Step.secondC (T.d t2 x1) x2 (Step.leftD x1 h2)))) (Steps.cons (Step.root (Root.r20 t2 x1 x2)) (Steps.refl _)))))))))⟩
      | @rightD _ _ t2 h2 =>
        exact ⟨(T.d (T.d (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.d x0 t2)) x0), (Steps.cons (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h2)))) (Steps.cons (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t2) x2 (Step.rightD x0 h2)))) (Steps.cons (Step.leftD x0 (Step.rightD (T.c (T.d x0 t2) (T.d x0 t2) x2) (Step.rightD x0 h2))) (Steps.refl _)))), (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 t2)) (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h2)))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 t2)) (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t2) x2 (Step.rightD x0 h2)))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 t2)) (Step.rightD (T.c (T.d x0 t2) (T.d x0 t2) x2) (Step.rightD x0 h2))) (Steps.cons (Step.right (T.d (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.d x0 t2)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 t2) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h2)))) (Steps.cons (Step.right (T.d (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.d x0 t2)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 t2) (Step.secondC (T.d x0 t2) x2 (Step.rightD x0 h2)))) (Steps.cons (Step.right (T.d (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.d x0 t2)) (Step.secondC (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.d x0 t2) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h2)))) (Steps.cons (Step.right (T.d (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.d x0 t2)) (Step.secondC (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.d x0 t2) (Step.secondC (T.d x0 t2) x2 (Step.rightD x0 h2)))) (Steps.cons (Step.root (Root.r20 x0 t2 x2)) (Steps.refl _)))))))))⟩
end submission.Austin5837

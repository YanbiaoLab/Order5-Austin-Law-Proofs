import Peak19Roots00
import Peak19Roots01
import Peak19Roots02
import Peak19Roots03
import Peak19Roots04
import Peak19Roots05
import Peak19Roots06
import Peak19Roots07
import Peak19Roots08
import Peak19Roots09
import Peak19Roots10
import Peak19Roots11
import Basic
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak19 (x0 : T) (x1 : T) (x2 : T) {u : T} (h : Step (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) u) : Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) u := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
    · rw [ho]
      exact peak19_root0 he
    · rw [ho]
      exact peak19_root1 he
    · rw [ho]
      exact peak19_root2 he
    · rw [ho]
      exact peak19_root3 he
    · rw [ho]
      exact peak19_root4 he
    · rw [ho]
      exact peak19_root5 he
    · rw [ho]
      exact peak19_root6 he
    · rw [ho]
      exact peak19_root7 he
    · rw [ho]
      exact peak19_root8 he
    · rw [ho]
      exact peak19_root9 he
    · rw [ho]
      exact peak19_root10 he
    · rw [ho]
      exact peak19_root11 he
    · rw [ho]
      exact peak19_root12 he
    · rw [ho]
      exact peak19_root13 he
    · rw [ho]
      exact peak19_root14 he
    · rw [ho]
      exact peak19_root15 he
    · rw [ho]
      exact peak19_root16 he
    · rw [ho]
      exact peak19_root17 he
    · rw [ho]
      exact peak19_root18 he
    · rw [ho]
      exact peak19_root19 he
    · rw [ho]
      exact peak19_root20 he
  | @left _ t0 _ h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
      · rw [ho]
        exact peak19_root21 he
      · rw [ho]
        exact peak19_root22 he
      · rw [ho]
        exact peak19_root23 he
      · rw [ho]
        exact peak19_root24 he
      · rw [ho]
        exact peak19_root25 he
      · rw [ho]
        exact peak19_root26 he
      · rw [ho]
        exact peak19_root27 he
      · rw [ho]
        exact peak19_root28 he
      · rw [ho]
        exact peak19_root29 he
      · rw [ho]
        exact peak19_root30 he
      · rw [ho]
        exact peak19_root31 he
      · rw [ho]
        exact peak19_root32 he
      · rw [ho]
        exact peak19_root33 he
      · rw [ho]
        exact peak19_root34 he
      · rw [ho]
        exact peak19_root35 he
      · rw [ho]
        exact peak19_root36 he
      · rw [ho]
        exact peak19_root37 he
      · rw [ho]
        exact peak19_root38 he
      · rw [ho]
        exact peak19_root39 he
      · rw [ho]
        exact peak19_root40 he
      · rw [ho]
        exact peak19_root41 he
    | @leftD _ t1 _ h1 =>
      cases h1 with
      | root hr =>
        rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
        · rw [ho]
          exact peak19_root42 he
        · rw [ho]
          exact peak19_root43 he
        · rw [ho]
          exact peak19_root44 he
        · rw [ho]
          exact peak19_root45 he
        · rw [ho]
          exact peak19_root46 he
        · rw [ho]
          exact peak19_root47 he
        · rw [ho]
          exact peak19_root48 he
        · rw [ho]
          exact peak19_root49 he
        · rw [ho]
          exact peak19_root50 he
        · rw [ho]
          exact peak19_root51 he
        · rw [ho]
          exact peak19_root52 he
        · rw [ho]
          exact peak19_root53 he
        · rw [ho]
          exact peak19_root54 he
        · rw [ho]
          exact peak19_root55 he
        · rw [ho]
          exact peak19_root56 he
        · rw [ho]
          exact peak19_root57 he
        · rw [ho]
          exact peak19_root58 he
        · rw [ho]
          exact peak19_root59 he
        · rw [ho]
          exact peak19_root60 he
        · rw [ho]
          exact peak19_root61 he
        · rw [ho]
          exact peak19_root62 he
      | @leftD _ t2 _ h2 =>
        exact ⟨(T.r (T.c (T.d (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.d t2 x1)) t2 x1) (T.d t2 x1)), (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h2))))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.secondC (T.d t2 x1) x2 (Step.leftD x1 h2))))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.rightD (T.c (T.d t2 x1) (T.d t2 x1) x2) (Step.leftD x1 h2)))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.secondC (T.d (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.d t2 x1)) x1 h2)) (Steps.cons (Step.rightR (T.c (T.d (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.d t2 x1)) t2 x1) (Step.leftD x1 h2)) (Steps.refl _)))))), (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (Step.rightD (T.d t2 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h2)))) (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (Step.rightD (T.d t2 x1) (Step.secondC (T.d t2 x1) x2 (Step.leftD x1 h2)))) (Steps.cons (Step.right (T.d (T.d t2 x1) (T.c (T.d t2 x1) (T.d t2 x1) x2)) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h2))))) (Steps.cons (Step.right (T.d (T.d t2 x1) (T.c (T.d t2 x1) (T.d t2 x1) x2)) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.secondC (T.d t2 x1) x2 (Step.leftD x1 h2))))) (Steps.cons (Step.right (T.d (T.d t2 x1) (T.c (T.d t2 x1) (T.d t2 x1) x2)) (Step.firstC x0 x1 (Step.rightD (T.c (T.d t2 x1) (T.d t2 x1) x2) (Step.leftD x1 h2)))) (Steps.cons (Step.right (T.d (T.d t2 x1) (T.c (T.d t2 x1) (T.d t2 x1) x2)) (Step.secondC (T.d (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.d t2 x1)) x1 h2)) (Steps.cons (Step.root (Root.r19 t2 x1 x2)) (Steps.refl _))))))))⟩
      | @rightD _ _ t2 h2 =>
        exact ⟨(T.r (T.c (T.d (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.d x0 t2)) x0 t2) (T.d x0 t2)), (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h2))))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t2) x2 (Step.rightD x0 h2))))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.rightD (T.c (T.d x0 t2) (T.d x0 t2) x2) (Step.rightD x0 h2)))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.thirdC (T.d (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.d x0 t2)) x0 h2)) (Steps.cons (Step.rightR (T.c (T.d (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.d x0 t2)) x0 t2) (Step.rightD x0 h2)) (Steps.refl _)))))), (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (Step.rightD (T.d x0 t2) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h2)))) (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (Step.rightD (T.d x0 t2) (Step.secondC (T.d x0 t2) x2 (Step.rightD x0 h2)))) (Steps.cons (Step.right (T.d (T.d x0 t2) (T.c (T.d x0 t2) (T.d x0 t2) x2)) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h2))))) (Steps.cons (Step.right (T.d (T.d x0 t2) (T.c (T.d x0 t2) (T.d x0 t2) x2)) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t2) x2 (Step.rightD x0 h2))))) (Steps.cons (Step.right (T.d (T.d x0 t2) (T.c (T.d x0 t2) (T.d x0 t2) x2)) (Step.firstC x0 x1 (Step.rightD (T.c (T.d x0 t2) (T.d x0 t2) x2) (Step.rightD x0 h2)))) (Steps.cons (Step.right (T.d (T.d x0 t2) (T.c (T.d x0 t2) (T.d x0 t2) x2)) (Step.thirdC (T.d (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.d x0 t2)) x0 h2)) (Steps.cons (Step.root (Root.r19 x0 t2 x2)) (Steps.refl _))))))))⟩
    | @rightD _ _ t1 h1 =>
      cases h1 with
      | root hr =>
        rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
        · rw [ho]
          exact peak19_root63 he
        · rw [ho]
          exact peak19_root64 he
        · rw [ho]
          exact peak19_root65 he
        · rw [ho]
          exact peak19_root66 he
        · rw [ho]
          exact peak19_root67 he
        · rw [ho]
          exact peak19_root68 he
        · rw [ho]
          exact peak19_root69 he
        · rw [ho]
          exact peak19_root70 he
        · rw [ho]
          exact peak19_root71 he
        · rw [ho]
          exact peak19_root72 he
        · rw [ho]
          exact peak19_root73 he
        · rw [ho]
          exact peak19_root74 he
        · rw [ho]
          exact peak19_root75 he
        · rw [ho]
          exact peak19_root76 he
        · rw [ho]
          exact peak19_root77 he
        · rw [ho]
          exact peak19_root78 he
        · rw [ho]
          exact peak19_root79 he
        · rw [ho]
          exact peak19_root80 he
        · rw [ho]
          exact peak19_root81 he
        · rw [ho]
          exact peak19_root82 he
        · rw [ho]
          exact peak19_root83 he
      | @firstC _ t2 _ _ h2 =>
        cases h2 with
        | root hr =>
          rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
          · rw [ho]
            exact peak19_root84 he
          · rw [ho]
            exact peak19_root85 he
          · rw [ho]
            exact peak19_root86 he
          · rw [ho]
            exact peak19_root87 he
          · rw [ho]
            exact peak19_root88 he
          · rw [ho]
            exact peak19_root89 he
          · rw [ho]
            exact peak19_root90 he
          · rw [ho]
            exact peak19_root91 he
          · rw [ho]
            exact peak19_root92 he
          · rw [ho]
            exact peak19_root93 he
          · rw [ho]
            exact peak19_root94 he
          · rw [ho]
            exact peak19_root95 he
          · rw [ho]
            exact peak19_root96 he
          · rw [ho]
            exact peak19_root97 he
          · rw [ho]
            exact peak19_root98 he
          · rw [ho]
            exact peak19_root99 he
          · rw [ho]
            exact peak19_root100 he
          · rw [ho]
            exact peak19_root101 he
          · rw [ho]
            exact peak19_root102 he
          · rw [ho]
            exact peak19_root103 he
          · rw [ho]
            exact peak19_root104 he
        | @leftD _ t3 _ h3 =>
          exact ⟨(T.r (T.c (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) t3 x1) (T.d t3 x1)), (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3))))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3))))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.rightD (T.c (T.d t3 x1) (T.d t3 x1) x2) (Step.leftD x1 h3)))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.secondC (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) x1 h3)) (Steps.cons (Step.rightR (T.c (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) t3 x1) (Step.leftD x1 h3)) (Steps.refl _)))))), (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (Step.leftD (T.c (T.d t3 x1) (T.d x0 x1) x2) (Step.leftD x1 h3))) (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (Step.rightD (T.d t3 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.right (T.d (T.d t3 x1) (T.c (T.d t3 x1) (T.d t3 x1) x2)) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3))))) (Steps.cons (Step.right (T.d (T.d t3 x1) (T.c (T.d t3 x1) (T.d t3 x1) x2)) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3))))) (Steps.cons (Step.right (T.d (T.d t3 x1) (T.c (T.d t3 x1) (T.d t3 x1) x2)) (Step.firstC x0 x1 (Step.rightD (T.c (T.d t3 x1) (T.d t3 x1) x2) (Step.leftD x1 h3)))) (Steps.cons (Step.right (T.d (T.d t3 x1) (T.c (T.d t3 x1) (T.d t3 x1) x2)) (Step.secondC (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) x1 h3)) (Steps.cons (Step.root (Root.r19 t3 x1 x2)) (Steps.refl _))))))))⟩
        | @rightD _ _ t3 h3 =>
          exact ⟨(T.r (T.c (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) x0 t3) (T.d x0 t3)), (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3))))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3))))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.rightD (T.c (T.d x0 t3) (T.d x0 t3) x2) (Step.rightD x0 h3)))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.thirdC (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) x0 h3)) (Steps.cons (Step.rightR (T.c (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) x0 t3) (Step.rightD x0 h3)) (Steps.refl _)))))), (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (Step.leftD (T.c (T.d x0 t3) (T.d x0 x1) x2) (Step.rightD x0 h3))) (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (Step.rightD (T.d x0 t3) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.d x0 t3) (T.c (T.d x0 t3) (T.d x0 t3) x2)) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3))))) (Steps.cons (Step.right (T.d (T.d x0 t3) (T.c (T.d x0 t3) (T.d x0 t3) x2)) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3))))) (Steps.cons (Step.right (T.d (T.d x0 t3) (T.c (T.d x0 t3) (T.d x0 t3) x2)) (Step.firstC x0 x1 (Step.rightD (T.c (T.d x0 t3) (T.d x0 t3) x2) (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.d x0 t3) (T.c (T.d x0 t3) (T.d x0 t3) x2)) (Step.thirdC (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) x0 h3)) (Steps.cons (Step.root (Root.r19 x0 t3 x2)) (Steps.refl _))))))))⟩
      | @secondC _ _ t2 _ h2 =>
        cases h2 with
        | root hr =>
          rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
          · rw [ho]
            exact peak19_root105 he
          · rw [ho]
            exact peak19_root106 he
          · rw [ho]
            exact peak19_root107 he
          · rw [ho]
            exact peak19_root108 he
          · rw [ho]
            exact peak19_root109 he
          · rw [ho]
            exact peak19_root110 he
          · rw [ho]
            exact peak19_root111 he
          · rw [ho]
            exact peak19_root112 he
          · rw [ho]
            exact peak19_root113 he
          · rw [ho]
            exact peak19_root114 he
          · rw [ho]
            exact peak19_root115 he
          · rw [ho]
            exact peak19_root116 he
          · rw [ho]
            exact peak19_root117 he
          · rw [ho]
            exact peak19_root118 he
          · rw [ho]
            exact peak19_root119 he
          · rw [ho]
            exact peak19_root120 he
          · rw [ho]
            exact peak19_root121 he
          · rw [ho]
            exact peak19_root122 he
          · rw [ho]
            exact peak19_root123 he
          · rw [ho]
            exact peak19_root124 he
          · rw [ho]
            exact peak19_root125 he
        | @leftD _ t3 _ h3 =>
          exact ⟨(T.r (T.c (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) t3 x1) (T.d t3 x1)), (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3))))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3))))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.rightD (T.c (T.d t3 x1) (T.d t3 x1) x2) (Step.leftD x1 h3)))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.secondC (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) x1 h3)) (Steps.cons (Step.rightR (T.c (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) t3 x1) (Step.leftD x1 h3)) (Steps.refl _)))))), (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (Step.leftD (T.c (T.d x0 x1) (T.d t3 x1) x2) (Step.leftD x1 h3))) (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (Step.rightD (T.d t3 x1) (Step.firstC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.right (T.d (T.d t3 x1) (T.c (T.d t3 x1) (T.d t3 x1) x2)) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3))))) (Steps.cons (Step.right (T.d (T.d t3 x1) (T.c (T.d t3 x1) (T.d t3 x1) x2)) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3))))) (Steps.cons (Step.right (T.d (T.d t3 x1) (T.c (T.d t3 x1) (T.d t3 x1) x2)) (Step.firstC x0 x1 (Step.rightD (T.c (T.d t3 x1) (T.d t3 x1) x2) (Step.leftD x1 h3)))) (Steps.cons (Step.right (T.d (T.d t3 x1) (T.c (T.d t3 x1) (T.d t3 x1) x2)) (Step.secondC (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) x1 h3)) (Steps.cons (Step.root (Root.r19 t3 x1 x2)) (Steps.refl _))))))))⟩
        | @rightD _ _ t3 h3 =>
          exact ⟨(T.r (T.c (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) x0 t3) (T.d x0 t3)), (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3))))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3))))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.rightD (T.c (T.d x0 t3) (T.d x0 t3) x2) (Step.rightD x0 h3)))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.thirdC (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) x0 h3)) (Steps.cons (Step.rightR (T.c (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) x0 t3) (Step.rightD x0 h3)) (Steps.refl _)))))), (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (Step.leftD (T.c (T.d x0 x1) (T.d x0 t3) x2) (Step.rightD x0 h3))) (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (Step.rightD (T.d x0 t3) (Step.firstC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.d x0 t3) (T.c (T.d x0 t3) (T.d x0 t3) x2)) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3))))) (Steps.cons (Step.right (T.d (T.d x0 t3) (T.c (T.d x0 t3) (T.d x0 t3) x2)) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3))))) (Steps.cons (Step.right (T.d (T.d x0 t3) (T.c (T.d x0 t3) (T.d x0 t3) x2)) (Step.firstC x0 x1 (Step.rightD (T.c (T.d x0 t3) (T.d x0 t3) x2) (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.d x0 t3) (T.c (T.d x0 t3) (T.d x0 t3) x2)) (Step.thirdC (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) x0 h3)) (Steps.cons (Step.root (Root.r19 x0 t3 x2)) (Steps.refl _))))))))⟩
      | @thirdC _ _ _ t2 h2 =>
        exact ⟨(T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) t2) (T.d x0 x1)) x0 x1) (T.d x0 x1)), (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.thirdC (T.d x0 x1) (T.d x0 x1) h2)))) (Steps.refl _)), (Steps.cons (Step.right (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) t2)) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.thirdC (T.d x0 x1) (T.d x0 x1) h2)))) (Steps.cons (Step.root (Root.r19 x0 x1 t2)) (Steps.refl _)))⟩
  | @right _ _ t0 h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
      · rw [ho]
        exact peak19_root126 he
      · rw [ho]
        exact peak19_root127 he
      · rw [ho]
        exact peak19_root128 he
      · rw [ho]
        exact peak19_root129 he
      · rw [ho]
        exact peak19_root130 he
      · rw [ho]
        exact peak19_root131 he
      · rw [ho]
        exact peak19_root132 he
      · rw [ho]
        exact peak19_root133 he
      · rw [ho]
        exact peak19_root134 he
      · rw [ho]
        exact peak19_root135 he
      · rw [ho]
        exact peak19_root136 he
      · rw [ho]
        exact peak19_root137 he
      · rw [ho]
        exact peak19_root138 he
      · rw [ho]
        exact peak19_root139 he
      · rw [ho]
        exact peak19_root140 he
      · rw [ho]
        exact peak19_root141 he
      · rw [ho]
        exact peak19_root142 he
      · rw [ho]
        exact peak19_root143 he
      · rw [ho]
        exact peak19_root144 he
      · rw [ho]
        exact peak19_root145 he
      · rw [ho]
        exact peak19_root146 he
    | @firstC _ t1 _ _ h1 =>
      cases h1 with
      | root hr =>
        rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
        · rw [ho]
          exact peak19_root147 he
        · rw [ho]
          exact peak19_root148 he
        · rw [ho]
          exact peak19_root149 he
        · rw [ho]
          exact peak19_root150 he
        · rw [ho]
          exact peak19_root151 he
        · rw [ho]
          exact peak19_root152 he
        · rw [ho]
          exact peak19_root153 he
        · rw [ho]
          exact peak19_root154 he
        · rw [ho]
          exact peak19_root155 he
        · rw [ho]
          exact peak19_root156 he
        · rw [ho]
          exact peak19_root157 he
        · rw [ho]
          exact peak19_root158 he
        · rw [ho]
          exact peak19_root159 he
        · rw [ho]
          exact peak19_root160 he
        · rw [ho]
          exact peak19_root161 he
        · rw [ho]
          exact peak19_root162 he
        · rw [ho]
          exact peak19_root163 he
        · rw [ho]
          exact peak19_root164 he
        · rw [ho]
          exact peak19_root165 he
        · rw [ho]
          exact peak19_root166 he
        · rw [ho]
          exact peak19_root167 he
      | @leftD _ t2 _ h2 =>
        cases h2 with
        | root hr =>
          rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
          · rw [ho]
            exact peak19_root168 he
          · rw [ho]
            exact peak19_root169 he
          · rw [ho]
            exact peak19_root170 he
          · rw [ho]
            exact peak19_root171 he
          · rw [ho]
            exact peak19_root172 he
          · rw [ho]
            exact peak19_root173 he
          · rw [ho]
            exact peak19_root174 he
          · rw [ho]
            exact peak19_root175 he
          · rw [ho]
            exact peak19_root176 he
          · rw [ho]
            exact peak19_root177 he
          · rw [ho]
            exact peak19_root178 he
          · rw [ho]
            exact peak19_root179 he
          · rw [ho]
            exact peak19_root180 he
          · rw [ho]
            exact peak19_root181 he
          · rw [ho]
            exact peak19_root182 he
          · rw [ho]
            exact peak19_root183 he
          · rw [ho]
            exact peak19_root184 he
          · rw [ho]
            exact peak19_root185 he
          · rw [ho]
            exact peak19_root186 he
          · rw [ho]
            exact peak19_root187 he
          · rw [ho]
            exact peak19_root188 he
        | @firstC _ t3 _ _ h3 =>
          cases h3 with
          | root hr =>
            rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
            · rw [ho]
              exact peak19_root189 he
            · rw [ho]
              exact peak19_root190 he
            · rw [ho]
              exact peak19_root191 he
            · rw [ho]
              exact peak19_root192 he
            · rw [ho]
              exact peak19_root193 he
            · rw [ho]
              exact peak19_root194 he
            · rw [ho]
              exact peak19_root195 he
            · rw [ho]
              exact peak19_root196 he
            · rw [ho]
              exact peak19_root197 he
            · rw [ho]
              exact peak19_root198 he
            · rw [ho]
              exact peak19_root199 he
            · rw [ho]
              exact peak19_root200 he
            · rw [ho]
              exact peak19_root201 he
            · rw [ho]
              exact peak19_root202 he
            · rw [ho]
              exact peak19_root203 he
            · rw [ho]
              exact peak19_root204 he
            · rw [ho]
              exact peak19_root205 he
            · rw [ho]
              exact peak19_root206 he
            · rw [ho]
              exact peak19_root207 he
            · rw [ho]
              exact peak19_root208 he
            · rw [ho]
              exact peak19_root209 he
          | @leftD _ t4 _ h4 =>
            exact ⟨(T.r (T.c (T.d (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.d t4 x1)) t4 x1) (T.d t4 x1)), (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h4))))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.secondC (T.d t4 x1) x2 (Step.leftD x1 h4))))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.rightD (T.c (T.d t4 x1) (T.d t4 x1) x2) (Step.leftD x1 h4)))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.secondC (T.d (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.d t4 x1)) x1 h4)) (Steps.cons (Step.rightR (T.c (T.d (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.d t4 x1)) t4 x1) (Step.leftD x1 h4)) (Steps.refl _)))))), (Steps.cons (Step.left (T.c (T.d (T.c (T.d t4 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (Step.leftD (T.c (T.d x0 x1) (T.d x0 x1) x2) (Step.leftD x1 h4))) (Steps.cons (Step.left (T.c (T.d (T.c (T.d t4 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (Step.rightD (T.d t4 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h4)))) (Steps.cons (Step.left (T.c (T.d (T.c (T.d t4 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (Step.rightD (T.d t4 x1) (Step.secondC (T.d t4 x1) x2 (Step.leftD x1 h4)))) (Steps.cons (Step.right (T.d (T.d t4 x1) (T.c (T.d t4 x1) (T.d t4 x1) x2)) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.secondC (T.d t4 x1) x2 (Step.leftD x1 h4))))) (Steps.cons (Step.right (T.d (T.d t4 x1) (T.c (T.d t4 x1) (T.d t4 x1) x2)) (Step.firstC x0 x1 (Step.rightD (T.c (T.d t4 x1) (T.d t4 x1) x2) (Step.leftD x1 h4)))) (Steps.cons (Step.right (T.d (T.d t4 x1) (T.c (T.d t4 x1) (T.d t4 x1) x2)) (Step.secondC (T.d (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.d t4 x1)) x1 h4)) (Steps.cons (Step.root (Root.r19 t4 x1 x2)) (Steps.refl _))))))))⟩
          | @rightD _ _ t4 h4 =>
            exact ⟨(T.r (T.c (T.d (T.c (T.d x0 t4) (T.d x0 t4) x2) (T.d x0 t4)) x0 t4) (T.d x0 t4)), (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h4))))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t4) x2 (Step.rightD x0 h4))))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.rightD (T.c (T.d x0 t4) (T.d x0 t4) x2) (Step.rightD x0 h4)))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.thirdC (T.d (T.c (T.d x0 t4) (T.d x0 t4) x2) (T.d x0 t4)) x0 h4)) (Steps.cons (Step.rightR (T.c (T.d (T.c (T.d x0 t4) (T.d x0 t4) x2) (T.d x0 t4)) x0 t4) (Step.rightD x0 h4)) (Steps.refl _)))))), (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 t4) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (Step.leftD (T.c (T.d x0 x1) (T.d x0 x1) x2) (Step.rightD x0 h4))) (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 t4) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (Step.rightD (T.d x0 t4) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h4)))) (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 t4) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (Step.rightD (T.d x0 t4) (Step.secondC (T.d x0 t4) x2 (Step.rightD x0 h4)))) (Steps.cons (Step.right (T.d (T.d x0 t4) (T.c (T.d x0 t4) (T.d x0 t4) x2)) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t4) x2 (Step.rightD x0 h4))))) (Steps.cons (Step.right (T.d (T.d x0 t4) (T.c (T.d x0 t4) (T.d x0 t4) x2)) (Step.firstC x0 x1 (Step.rightD (T.c (T.d x0 t4) (T.d x0 t4) x2) (Step.rightD x0 h4)))) (Steps.cons (Step.right (T.d (T.d x0 t4) (T.c (T.d x0 t4) (T.d x0 t4) x2)) (Step.thirdC (T.d (T.c (T.d x0 t4) (T.d x0 t4) x2) (T.d x0 t4)) x0 h4)) (Steps.cons (Step.root (Root.r19 x0 t4 x2)) (Steps.refl _))))))))⟩
        | @secondC _ _ t3 _ h3 =>
          cases h3 with
          | root hr =>
            rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
            · rw [ho]
              exact peak19_root210 he
            · rw [ho]
              exact peak19_root211 he
            · rw [ho]
              exact peak19_root212 he
            · rw [ho]
              exact peak19_root213 he
            · rw [ho]
              exact peak19_root214 he
            · rw [ho]
              exact peak19_root215 he
            · rw [ho]
              exact peak19_root216 he
            · rw [ho]
              exact peak19_root217 he
            · rw [ho]
              exact peak19_root218 he
            · rw [ho]
              exact peak19_root219 he
            · rw [ho]
              exact peak19_root220 he
            · rw [ho]
              exact peak19_root221 he
            · rw [ho]
              exact peak19_root222 he
            · rw [ho]
              exact peak19_root223 he
            · rw [ho]
              exact peak19_root224 he
            · rw [ho]
              exact peak19_root225 he
            · rw [ho]
              exact peak19_root226 he
            · rw [ho]
              exact peak19_root227 he
            · rw [ho]
              exact peak19_root228 he
            · rw [ho]
              exact peak19_root229 he
            · rw [ho]
              exact peak19_root230 he
          | @leftD _ t4 _ h4 =>
            exact ⟨(T.r (T.c (T.d (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.d t4 x1)) t4 x1) (T.d t4 x1)), (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h4))))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.secondC (T.d t4 x1) x2 (Step.leftD x1 h4))))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.rightD (T.c (T.d t4 x1) (T.d t4 x1) x2) (Step.leftD x1 h4)))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.secondC (T.d (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.d t4 x1)) x1 h4)) (Steps.cons (Step.rightR (T.c (T.d (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.d t4 x1)) t4 x1) (Step.leftD x1 h4)) (Steps.refl _)))))), (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 x1) (T.d t4 x1) x2) (T.d x0 x1)) x0 x1) (Step.leftD (T.c (T.d x0 x1) (T.d x0 x1) x2) (Step.leftD x1 h4))) (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 x1) (T.d t4 x1) x2) (T.d x0 x1)) x0 x1) (Step.rightD (T.d t4 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h4)))) (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 x1) (T.d t4 x1) x2) (T.d x0 x1)) x0 x1) (Step.rightD (T.d t4 x1) (Step.secondC (T.d t4 x1) x2 (Step.leftD x1 h4)))) (Steps.cons (Step.right (T.d (T.d t4 x1) (T.c (T.d t4 x1) (T.d t4 x1) x2)) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.firstC (T.d t4 x1) x2 (Step.leftD x1 h4))))) (Steps.cons (Step.right (T.d (T.d t4 x1) (T.c (T.d t4 x1) (T.d t4 x1) x2)) (Step.firstC x0 x1 (Step.rightD (T.c (T.d t4 x1) (T.d t4 x1) x2) (Step.leftD x1 h4)))) (Steps.cons (Step.right (T.d (T.d t4 x1) (T.c (T.d t4 x1) (T.d t4 x1) x2)) (Step.secondC (T.d (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.d t4 x1)) x1 h4)) (Steps.cons (Step.root (Root.r19 t4 x1 x2)) (Steps.refl _))))))))⟩
          | @rightD _ _ t4 h4 =>
            exact ⟨(T.r (T.c (T.d (T.c (T.d x0 t4) (T.d x0 t4) x2) (T.d x0 t4)) x0 t4) (T.d x0 t4)), (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h4))))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t4) x2 (Step.rightD x0 h4))))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.rightD (T.c (T.d x0 t4) (T.d x0 t4) x2) (Step.rightD x0 h4)))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.thirdC (T.d (T.c (T.d x0 t4) (T.d x0 t4) x2) (T.d x0 t4)) x0 h4)) (Steps.cons (Step.rightR (T.c (T.d (T.c (T.d x0 t4) (T.d x0 t4) x2) (T.d x0 t4)) x0 t4) (Step.rightD x0 h4)) (Steps.refl _)))))), (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 x1) (T.d x0 t4) x2) (T.d x0 x1)) x0 x1) (Step.leftD (T.c (T.d x0 x1) (T.d x0 x1) x2) (Step.rightD x0 h4))) (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 x1) (T.d x0 t4) x2) (T.d x0 x1)) x0 x1) (Step.rightD (T.d x0 t4) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h4)))) (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 x1) (T.d x0 t4) x2) (T.d x0 x1)) x0 x1) (Step.rightD (T.d x0 t4) (Step.secondC (T.d x0 t4) x2 (Step.rightD x0 h4)))) (Steps.cons (Step.right (T.d (T.d x0 t4) (T.c (T.d x0 t4) (T.d x0 t4) x2)) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 t4) x2 (Step.rightD x0 h4))))) (Steps.cons (Step.right (T.d (T.d x0 t4) (T.c (T.d x0 t4) (T.d x0 t4) x2)) (Step.firstC x0 x1 (Step.rightD (T.c (T.d x0 t4) (T.d x0 t4) x2) (Step.rightD x0 h4)))) (Steps.cons (Step.right (T.d (T.d x0 t4) (T.c (T.d x0 t4) (T.d x0 t4) x2)) (Step.thirdC (T.d (T.c (T.d x0 t4) (T.d x0 t4) x2) (T.d x0 t4)) x0 h4)) (Steps.cons (Step.root (Root.r19 x0 t4 x2)) (Steps.refl _))))))))⟩
        | @thirdC _ _ _ t3 h3 =>
          exact ⟨(T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) t3) (T.d x0 x1)) x0 x1) (T.d x0 x1)), (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.thirdC (T.d x0 x1) (T.d x0 x1) h3)))) (Steps.refl _)), (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) t3) (T.d x0 x1)) x0 x1) (Step.rightD (T.d x0 x1) (Step.thirdC (T.d x0 x1) (T.d x0 x1) h3))) (Steps.cons (Step.root (Root.r19 x0 x1 t3)) (Steps.refl _)))⟩
      | @rightD _ _ t2 h2 =>
        cases h2 with
        | root hr =>
          rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
          · rw [ho]
            exact peak19_root231 he
          · rw [ho]
            exact peak19_root232 he
          · rw [ho]
            exact peak19_root233 he
          · rw [ho]
            exact peak19_root234 he
          · rw [ho]
            exact peak19_root235 he
          · rw [ho]
            exact peak19_root236 he
          · rw [ho]
            exact peak19_root237 he
          · rw [ho]
            exact peak19_root238 he
          · rw [ho]
            exact peak19_root239 he
          · rw [ho]
            exact peak19_root240 he
          · rw [ho]
            exact peak19_root241 he
          · rw [ho]
            exact peak19_root242 he
          · rw [ho]
            exact peak19_root243 he
          · rw [ho]
            exact peak19_root244 he
          · rw [ho]
            exact peak19_root245 he
          · rw [ho]
            exact peak19_root246 he
          · rw [ho]
            exact peak19_root247 he
          · rw [ho]
            exact peak19_root248 he
          · rw [ho]
            exact peak19_root249 he
          · rw [ho]
            exact peak19_root250 he
          · rw [ho]
            exact peak19_root251 he
        | @leftD _ t3 _ h3 =>
          exact ⟨(T.r (T.c (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) t3 x1) (T.d t3 x1)), (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3))))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3))))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.rightD (T.c (T.d t3 x1) (T.d t3 x1) x2) (Step.leftD x1 h3)))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.secondC (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) x1 h3)) (Steps.cons (Step.rightR (T.c (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) t3 x1) (Step.leftD x1 h3)) (Steps.refl _)))))), (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d t3 x1)) x0 x1) (Step.leftD (T.c (T.d x0 x1) (T.d x0 x1) x2) (Step.leftD x1 h3))) (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d t3 x1)) x0 x1) (Step.rightD (T.d t3 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d t3 x1)) x0 x1) (Step.rightD (T.d t3 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.right (T.d (T.d t3 x1) (T.c (T.d t3 x1) (T.d t3 x1) x2)) (Step.firstC x0 x1 (Step.leftD (T.d t3 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3))))) (Steps.cons (Step.right (T.d (T.d t3 x1) (T.c (T.d t3 x1) (T.d t3 x1) x2)) (Step.firstC x0 x1 (Step.leftD (T.d t3 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3))))) (Steps.cons (Step.right (T.d (T.d t3 x1) (T.c (T.d t3 x1) (T.d t3 x1) x2)) (Step.secondC (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) x1 h3)) (Steps.cons (Step.root (Root.r19 t3 x1 x2)) (Steps.refl _))))))))⟩
        | @rightD _ _ t3 h3 =>
          exact ⟨(T.r (T.c (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) x0 t3) (T.d x0 t3)), (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3))))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3))))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.rightD (T.c (T.d x0 t3) (T.d x0 t3) x2) (Step.rightD x0 h3)))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.thirdC (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) x0 h3)) (Steps.cons (Step.rightR (T.c (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) x0 t3) (Step.rightD x0 h3)) (Steps.refl _)))))), (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 t3)) x0 x1) (Step.leftD (T.c (T.d x0 x1) (T.d x0 x1) x2) (Step.rightD x0 h3))) (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 t3)) x0 x1) (Step.rightD (T.d x0 t3) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 t3)) x0 x1) (Step.rightD (T.d x0 t3) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.d x0 t3) (T.c (T.d x0 t3) (T.d x0 t3) x2)) (Step.firstC x0 x1 (Step.leftD (T.d x0 t3) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3))))) (Steps.cons (Step.right (T.d (T.d x0 t3) (T.c (T.d x0 t3) (T.d x0 t3) x2)) (Step.firstC x0 x1 (Step.leftD (T.d x0 t3) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3))))) (Steps.cons (Step.right (T.d (T.d x0 t3) (T.c (T.d x0 t3) (T.d x0 t3) x2)) (Step.thirdC (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) x0 h3)) (Steps.cons (Step.root (Root.r19 x0 t3 x2)) (Steps.refl _))))))))⟩
    | @secondC _ _ t1 _ h1 =>
      exact ⟨(T.r (T.c (T.d (T.c (T.d t1 x1) (T.d t1 x1) x2) (T.d t1 x1)) t1 x1) (T.d t1 x1)), (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h1))))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.secondC (T.d t1 x1) x2 (Step.leftD x1 h1))))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.rightD (T.c (T.d t1 x1) (T.d t1 x1) x2) (Step.leftD x1 h1)))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.secondC (T.d (T.c (T.d t1 x1) (T.d t1 x1) x2) (T.d t1 x1)) x1 h1)) (Steps.cons (Step.rightR (T.c (T.d (T.c (T.d t1 x1) (T.d t1 x1) x2) (T.d t1 x1)) t1 x1) (Step.leftD x1 h1)) (Steps.refl _)))))), (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) t1 x1) (Step.leftD (T.c (T.d x0 x1) (T.d x0 x1) x2) (Step.leftD x1 h1))) (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) t1 x1) (Step.rightD (T.d t1 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h1)))) (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) t1 x1) (Step.rightD (T.d t1 x1) (Step.secondC (T.d t1 x1) x2 (Step.leftD x1 h1)))) (Steps.cons (Step.right (T.d (T.d t1 x1) (T.c (T.d t1 x1) (T.d t1 x1) x2)) (Step.firstC t1 x1 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h1))))) (Steps.cons (Step.right (T.d (T.d t1 x1) (T.c (T.d t1 x1) (T.d t1 x1) x2)) (Step.firstC t1 x1 (Step.leftD (T.d x0 x1) (Step.secondC (T.d t1 x1) x2 (Step.leftD x1 h1))))) (Steps.cons (Step.right (T.d (T.d t1 x1) (T.c (T.d t1 x1) (T.d t1 x1) x2)) (Step.firstC t1 x1 (Step.rightD (T.c (T.d t1 x1) (T.d t1 x1) x2) (Step.leftD x1 h1)))) (Steps.cons (Step.root (Root.r19 t1 x1 x2)) (Steps.refl _))))))))⟩
    | @thirdC _ _ _ t1 h1 =>
      exact ⟨(T.r (T.c (T.d (T.c (T.d x0 t1) (T.d x0 t1) x2) (T.d x0 t1)) x0 t1) (T.d x0 t1)), (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h1))))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t1) x2 (Step.rightD x0 h1))))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.rightD (T.c (T.d x0 t1) (T.d x0 t1) x2) (Step.rightD x0 h1)))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.thirdC (T.d (T.c (T.d x0 t1) (T.d x0 t1) x2) (T.d x0 t1)) x0 h1)) (Steps.cons (Step.rightR (T.c (T.d (T.c (T.d x0 t1) (T.d x0 t1) x2) (T.d x0 t1)) x0 t1) (Step.rightD x0 h1)) (Steps.refl _)))))), (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 t1) (Step.leftD (T.c (T.d x0 x1) (T.d x0 x1) x2) (Step.rightD x0 h1))) (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 t1) (Step.rightD (T.d x0 t1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h1)))) (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 t1) (Step.rightD (T.d x0 t1) (Step.secondC (T.d x0 t1) x2 (Step.rightD x0 h1)))) (Steps.cons (Step.right (T.d (T.d x0 t1) (T.c (T.d x0 t1) (T.d x0 t1) x2)) (Step.firstC x0 t1 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h1))))) (Steps.cons (Step.right (T.d (T.d x0 t1) (T.c (T.d x0 t1) (T.d x0 t1) x2)) (Step.firstC x0 t1 (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t1) x2 (Step.rightD x0 h1))))) (Steps.cons (Step.right (T.d (T.d x0 t1) (T.c (T.d x0 t1) (T.d x0 t1) x2)) (Step.firstC x0 t1 (Step.rightD (T.c (T.d x0 t1) (T.d x0 t1) x2) (Step.rightD x0 h1)))) (Steps.cons (Step.root (Root.r19 x0 t1 x2)) (Steps.refl _))))))))⟩
end submission.Austin5837

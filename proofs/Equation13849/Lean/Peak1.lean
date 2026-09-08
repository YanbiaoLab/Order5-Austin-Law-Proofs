import Basic
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin13849
open T
theorem peak1 (x0 : T) (x1 : T) {u : T} (h : Step (T.m (T.m x0 x1) x1) u) : Join (T.r x0 x1) u := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := (T.m.inj e0).1
      have e3 := (T.m.inj e0).2
      subst x1
      subst x0
      exact ⟨(T.r q0 q1), (Steps.refl _), (Steps.refl _)⟩
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := (T.m.inj e0).1
      have e3 := (T.m.inj e0).2
      subst x1
      subst x0
      have cycle := congrArg size e3
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst q0
      have cycle := congrArg size e1
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      cases e0
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst q0
      have cycle := congrArg size e1
      simp only [size] at cycle
      omega
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      cases e0
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      cases e0
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := (T.m.inj e0).1
      have e3 := (T.m.inj e0).2
      subst x1
      subst x0
      have e4 := e3.symm
      have cycle := congrArg size e4
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      cases e0
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      cases e0
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      cases e0
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst q0
      have cycle := congrArg size e1
      simp only [size] at cycle
      omega
  | @left _ t0 _ h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        subst x1
        exact ⟨(T.r (T.m q0 q1) q1), (Steps.refl _), (Steps.cons (Step.root (Root.r4 q0 q1)) (Steps.refl _))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        subst x1
        exact ⟨(T.r (T.m q0 (T.r q1 q2)) q2), (Steps.refl _), (Steps.cons (Step.root (Root.r7 q0 q1 q2)) (Steps.refl _))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        subst x1
        exact ⟨(T.r q0 (T.c q0 q1 q2)), (Steps.refl _), (Steps.cons (Step.root (Root.r5 q1 q0 q2)) (Steps.refl _))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        subst x1
        exact ⟨(T.r (T.r q0 q1) q1), (Steps.refl _), (Steps.cons (Step.root (Root.r4 (T.m q0 q1) q1)) (Steps.cons (Step.leftR q1 (Step.root (Root.r1 q0 q1))) (Steps.refl _)))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        subst x1
        exact ⟨(T.r q0 (T.c q1 q0 q2)), (Steps.refl _), (Steps.cons (Step.root (Root.r4 q1 (T.c q1 q0 q2))) (Steps.cons (Step.leftR (T.c q1 q0 q2) (Step.root (Root.r3 q1 q0 q2))) (Steps.refl _)))⟩
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        subst x1
        exact ⟨(T.r (T.c q0 q1 q2) q2), (Steps.refl _), (Steps.cons (Step.root (Root.r4 (T.m q0 (T.r q1 q2)) q2)) (Steps.cons (Step.leftR q2 (Step.root (Root.r2 q0 q1 q2))) (Steps.refl _)))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        subst x1
        exact ⟨(T.r (T.r q0 (T.r q1 q2)) q2), (Steps.refl _), (Steps.cons (Step.root (Root.r7 (T.m q0 (T.r q1 q2)) q1 q2)) (Steps.cons (Step.leftR q2 (Step.root (Root.r1 q0 (T.r q1 q2)))) (Steps.refl _)))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        subst x1
        exact ⟨(T.r (T.m q0 q1) (T.c q1 q1 q2)), (Steps.refl _), (Steps.cons (Step.root (Root.r7 q0 q1 (T.c q1 q1 q2))) (Steps.cons (Step.leftR (T.c q1 q1 q2) (Step.right q0 (Step.root (Root.r6 q1 q2)))) (Steps.refl _)))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        subst x1
        exact ⟨(T.r (T.r q0 q1) (T.c q1 q1 q2)), (Steps.refl _), (Steps.cons (Step.root (Root.r7 (T.m q0 q1) q1 (T.c q1 q1 q2))) (Steps.cons (Step.leftR (T.c q1 q1 q2) (Step.right (T.m q0 q1) (Step.root (Root.r6 q1 q2)))) (Steps.cons (Step.leftR (T.c q1 q1 q2) (Step.root (Root.r1 q0 q1))) (Steps.refl _))))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        subst x1
        exact ⟨(T.r (T.c q0 q1 (T.r q2 q3)) q3), (Steps.refl _), (Steps.cons (Step.root (Root.r7 (T.m q0 (T.r q1 (T.r q2 q3))) q2 q3)) (Steps.cons (Step.leftR q3 (Step.root (Root.r2 q0 q1 (T.r q2 q3)))) (Steps.refl _)))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        subst x1
        exact ⟨(T.r (T.c q0 q1 q2) (T.c q2 q2 q3)), (Steps.refl _), (Steps.cons (Step.root (Root.r7 (T.m q0 (T.r q1 q2)) q2 (T.c q2 q2 q3))) (Steps.cons (Step.leftR (T.c q2 q2 q3) (Step.right (T.m q0 (T.r q1 q2)) (Step.root (Root.r6 q2 q3)))) (Steps.cons (Step.leftR (T.c q2 q2 q3) (Step.root (Root.r2 q0 q1 q2))) (Steps.refl _))))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        subst x1
        exact ⟨(T.r q0 (T.c (T.c q1 q0 q2) (T.c q1 q0 q2) q3)), (Steps.refl _), (Steps.cons (Step.root (Root.r7 q1 (T.c q1 q0 q2) (T.c (T.c q1 q0 q2) (T.c q1 q0 q2) q3))) (Steps.cons (Step.leftR (T.c (T.c q1 q0 q2) (T.c q1 q0 q2) q3) (Step.right q1 (Step.root (Root.r6 (T.c q1 q0 q2) q3)))) (Steps.cons (Step.leftR (T.c (T.c q1 q0 q2) (T.c q1 q0 q2) q3) (Step.root (Root.r3 q1 q0 q2))) (Steps.refl _))))⟩
    | @left _ t1 _ h1 =>
      exact ⟨(T.r t1 x1), (Steps.cons (Step.leftR x1 h1) (Steps.refl _)), (Steps.cons (Step.root (Root.r1 t1 x1)) (Steps.refl _))⟩
    | @right _ _ t1 h1 =>
      exact ⟨(T.r x0 t1), (Steps.cons (Step.rightR x0 h1) (Steps.refl _)), (Steps.cons (Step.right (T.m x0 t1) h1) (Steps.cons (Step.root (Root.r1 x0 t1)) (Steps.refl _)))⟩
  | @right _ _ t0 h0 =>
    exact ⟨(T.r x0 t0), (Steps.cons (Step.rightR x0 h0) (Steps.refl _)), (Steps.cons (Step.left t0 (Step.right x0 h0)) (Steps.cons (Step.root (Root.r1 x0 t0)) (Steps.refl _)))⟩
end submission.Austin13849

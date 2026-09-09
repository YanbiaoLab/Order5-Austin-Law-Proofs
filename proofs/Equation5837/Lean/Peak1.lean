import Basic
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak1 (x0 : T) (x1 : T) {u : T} (h : Step (T.m (T.m x0 x1) x1) u) : Join (T.r x1 x0) u := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := (T.m.inj e0).1
      have e3 := (T.m.inj e0).2
      have e4 := e1.symm
      subst e4
      have e5 := e2.symm
      subst e5
      exact ⟨(T.r q1 q0), (Steps.refl _), (Steps.refl _)⟩
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      have cycle := congrArg size e1
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      subst e1
      exact ⟨(T.c (T.c x0 q1 q2) q1 q2), (Steps.cons (Step.root (Root.r7 q1 q2 x0)) (Steps.refl _)), (Steps.cons (Step.firstC q1 q2 (Step.root (Root.r3 x0 q1 q2))) (Steps.refl _))⟩
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
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
      cases e0
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
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
      cases e0
    · rw [ho]
      cases he
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
      have e2 := e0.symm
      subst e2
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
      cases e0
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      cases e0
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      cases e0
  | @left _ t0 _ h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst e0
        have e2 := e1.symm
        subst e2
        exact ⟨(T.r q1 (T.m q0 q1)), (Steps.refl _), (Steps.cons (Step.root (Root.r5 q1 q0)) (Steps.refl _))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        have e2 := e0.symm
        subst e2
        subst e1
        exact ⟨(T.r (T.r q0 q1) q0), (Steps.refl _), (Steps.cons (Step.root (Root.r6 q0 q1)) (Steps.refl _))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        have e2 := e0.symm
        subst e2
        subst e1
        exact ⟨(T.c (T.c q0 q1 q2) q1 q2), (Steps.cons (Step.root (Root.r7 q1 q2 q0)) (Steps.refl _)), (Steps.cons (Step.root (Root.r3 (T.c q0 q1 q2) q1 q2)) (Steps.refl _))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        have e2 := e0.symm
        subst e2
        subst e1
        exact ⟨(T.r (T.c q1 q0 q2) q0), (Steps.refl _), (Steps.cons (Step.root (Root.r8 q1 q0 q2)) (Steps.refl _))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst e0
        have e2 := e1.symm
        subst e2
        exact ⟨(T.r q0 (T.r q0 q1)), (Steps.refl _), (Steps.cons (Step.root (Root.r5 q0 (T.m q1 q0))) (Steps.cons (Step.rightR q0 (Step.root (Root.r1 q1 q0))) (Steps.refl _)))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst e0
        subst e1
        exact ⟨(T.r (T.r q0 q1) (T.d q0 q1)), (Steps.refl _), (Steps.cons (Step.root (Root.r5 (T.r q0 q1) q0)) (Steps.cons (Step.rightR (T.r q0 q1) (Step.root (Root.r2 q0 q1))) (Steps.refl _)))⟩
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        have e2 := e0.symm
        subst e2
        subst e1
        exact ⟨(T.r (T.c q0 q1 q2) q0), (Steps.refl _), (Steps.cons (Step.root (Root.r5 (T.c q0 q1 q2) q1)) (Steps.cons (Step.rightR (T.c q0 q1 q2) (Step.root (Root.r4 q1 q0 q2))) (Steps.refl _)))⟩
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst e0
        have e2 := e1.symm
        subst e2
        exact ⟨(T.r q0 (T.c q0 q0 q1)), (Steps.refl _), (Steps.cons (Step.root (Root.r11 q0 q1)) (Steps.refl _))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst e0
        have e2 := e1.symm
        subst e2
        exact ⟨(T.r q0 (T.d (T.c q0 q0 q1) q0)), (Steps.refl _), (Steps.cons (Step.root (Root.r5 q0 (T.c q0 q0 q1))) (Steps.cons (Step.rightR q0 (Step.root (Root.r10 q0 q1))) (Steps.refl _)))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst e0
        subst e1
        exact ⟨(T.r (T.c (T.c q2 q0 q1) q0 q1) (T.d q0 q1)), (Steps.refl _), (Steps.cons (Step.root (Root.r16 q0 q1 q2)) (Steps.refl _))⟩
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst e0
        subst e1
        exact ⟨(T.r (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2)), (Steps.refl _), (Steps.cons (Step.root (Root.r17 q0 q1 q2)) (Steps.refl _))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst e0
        subst e1
        exact ⟨(T.r (T.c (T.c q2 q0 q1) q0 q1) (T.d (T.d q0 q1) q2)), (Steps.refl _), (Steps.cons (Step.root (Root.r5 (T.c (T.c q2 q0 q1) q0 q1) (T.d q0 q1))) (Steps.cons (Step.rightR (T.c (T.c q2 q0 q1) q0 q1) (Step.root (Root.r12 q0 q1 q2))) (Steps.refl _)))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        have e2 := e0.symm
        subst e2
        subst e1
        exact ⟨(T.r (T.c (T.d q0 q1) (T.d q0 q1) q2) q0), (Steps.refl _), (Steps.cons (Step.root (Root.r5 (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2))) (Steps.cons (Step.rightR (T.c (T.d q0 q1) (T.d q0 q1) q2) (Step.root (Root.r15 q0 q1 q2))) (Steps.refl _)))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst e0
        subst e1
        exact ⟨(T.r (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1) (T.d q0 q1)), (Steps.refl _), (Steps.cons (Step.root (Root.r19 q0 q1 q2)) (Steps.refl _))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst e0
        subst e1
        exact ⟨(T.r (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1) (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2))), (Steps.refl _), (Steps.cons (Step.root (Root.r5 (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1) (T.d q0 q1))) (Steps.cons (Step.rightR (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1) (Step.root (Root.r18 q0 q1 q2))) (Steps.refl _)))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst e0
        subst e1
        exact ⟨(T.r (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))), (Steps.refl _), (Steps.cons (Step.root (Root.r21 q0 q1 q2)) (Steps.refl _))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst e0
        subst e1
        exact ⟨(T.r (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0)), (Steps.refl _), (Steps.cons (Step.root (Root.r5 (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) (Steps.cons (Step.rightR (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (Step.root (Root.r20 q0 q1 q2))) (Steps.refl _)))⟩
    | @left _ t1 _ h1 =>
      exact ⟨(T.r x1 t1), (Steps.cons (Step.rightR x1 h1) (Steps.refl _)), (Steps.cons (Step.root (Root.r1 t1 x1)) (Steps.refl _))⟩
    | @right _ _ t1 h1 =>
      exact ⟨(T.r t1 x0), (Steps.cons (Step.leftR x0 h1) (Steps.refl _)), (Steps.cons (Step.right (T.m x0 t1) h1) (Steps.cons (Step.root (Root.r1 x0 t1)) (Steps.refl _)))⟩
  | @right _ _ t0 h0 =>
    exact ⟨(T.r t0 x0), (Steps.cons (Step.leftR x0 h0) (Steps.refl _)), (Steps.cons (Step.left t0 (Step.right x0 h0)) (Steps.cons (Step.root (Root.r1 x0 t0)) (Steps.refl _)))⟩
end submission.Austin5837

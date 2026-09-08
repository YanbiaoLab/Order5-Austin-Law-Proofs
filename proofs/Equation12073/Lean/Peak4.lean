import Basic
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin12073
open T
theorem peak4 (x0 : T) (x1 : T) {u : T} (h : Step (T.m (T.m x0 x1) x1) u) : Join (T.u (T.u (T.d x0 x1))) u := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩
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
      exact ⟨(T.u (T.u x0)), (Steps.cons (Step.underU (Step.underU (Step.root (Root.r7 x0)))) (Steps.refl _)), (Steps.cons (Step.underU (Step.root (Root.r2 x0))) (Steps.refl _))⟩
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := (T.m.inj e0).1
      have e3 := (T.m.inj e0).2
      have e4 := e1.symm
      subst e4
      have e5 := e2.symm
      subst e5
      exact ⟨(T.u (T.u (T.d q0 q1))), (Steps.refl _), (Steps.refl _)⟩
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
      cases he
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      cases e0
    · rw [ho]
      cases he
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
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      have cycle := congrArg size e1
      simp only [size] at cycle
      omega
  | @left _ t0 _ h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        have e2 := e0.symm
        subst e2
        have e3 := e1.symm
        subst e3
        exact ⟨(T.u (T.u (T.d q0 q0))), (Steps.refl _), (Steps.cons (Step.root (Root.r8 q0)) (Steps.refl _))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        have e2 := e0.symm
        subst e2
        subst e1
        exact ⟨(T.u (T.u q0)), (Steps.cons (Step.underU (Step.underU (Step.root (Root.r7 q0)))) (Steps.refl _)), (Steps.cons (Step.root (Root.r2 (T.u q0))) (Steps.refl _))⟩
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst e0
        have e2 := e1.symm
        subst e2
        exact ⟨(T.u (T.u (T.d (T.m q0 q1) q1))), (Steps.refl _), (Steps.cons (Step.root (Root.r19 q0 q1)) (Steps.refl _))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        have e2 := e0.symm
        subst e2
        subst e1
        exact ⟨(T.u (T.u (T.d q0 (T.d q0 q1)))), (Steps.refl _), (Steps.cons (Step.root (Root.r12 q1 q0)) (Steps.refl _))⟩
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst e0
        have e2 := e1.symm
        subst e2
        exact ⟨(T.u (T.u (T.d T.e q0))), (Steps.refl _), (Steps.cons (Step.root (Root.r19 q0 q0)) (Steps.cons (Step.underU (Step.underU (Step.leftD q0 (Step.root (Root.r1 q0))))) (Steps.refl _)))⟩
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst e0
        subst e1
        exact ⟨(T.d T.e q0), (Steps.cons (Step.underU (Step.underU (Step.root (Root.r11 q0)))) (Steps.cons (Step.root (Root.r3 (T.d T.e q0))) (Steps.refl _))), (Steps.cons (Step.root (Root.r10 q0)) (Steps.refl _))⟩
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        have e2 := e0.symm
        subst e2
        subst e1
        exact ⟨(T.u (T.u (T.d q0 (T.d q1 q0)))), (Steps.refl _), (Steps.cons (Step.root (Root.r19 q1 (T.d q1 q0))) (Steps.cons (Step.underU (Step.underU (Step.leftD (T.d q1 q0) (Step.root (Root.r5 q1 q0))))) (Steps.refl _)))⟩
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        have e2 := e0.symm
        subst e2
        subst e1
        exact ⟨(T.u (T.u (T.d q0 (T.u q0)))), (Steps.refl _), (Steps.cons (Step.root (Root.r15 q0)) (Steps.refl _))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst e0
        subst e1
        exact ⟨(T.u (T.u (T.d (T.d q0 q0) (T.u q0)))), (Steps.refl _), (Steps.cons (Step.root (Root.r19 q0 (T.u q0))) (Steps.cons (Step.underU (Step.underU (Step.leftD (T.u q0) (Step.root (Root.r14 q0))))) (Steps.refl _)))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst e0
        have e2 := e1.symm
        subst e2
        exact ⟨(T.d T.e (T.u (T.u q0))), (Steps.cons (Step.underU (Step.underU (Step.root (Root.r18 q0)))) (Steps.cons (Step.root (Root.r3 (T.d T.e (T.u (T.u q0))))) (Steps.refl _))), (Steps.cons (Step.root (Root.r16 q0)) (Steps.refl _))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst e0
        have e2 := e1.symm
        subst e2
        exact ⟨(T.u (T.u (T.d (T.u (T.u q0)) q0))), (Steps.refl _), (Steps.cons (Step.root (Root.r20 q0)) (Steps.refl _))⟩
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst e0
        have e2 := e1.symm
        subst e2
        exact ⟨(T.u (T.u (T.d (T.u (T.u (T.d q0 q1))) q1))), (Steps.refl _), (Steps.cons (Step.root (Root.r19 (T.m q0 q1) q1)) (Steps.cons (Step.underU (Step.underU (Step.leftD q1 (Step.root (Root.r4 q0 q1))))) (Steps.refl _)))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst e0
        have e2 := e1.symm
        subst e2
        exact ⟨(T.u (T.u (T.d (T.d (T.u (T.u q0)) (T.u (T.u q0))) q0))), (Steps.refl _), (Steps.cons (Step.root (Root.r19 (T.u (T.u q0)) q0)) (Steps.cons (Step.underU (Step.underU (Step.leftD q0 (Step.root (Root.r17 q0))))) (Steps.refl _)))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst e0
        subst e1
        exact ⟨(T.u (T.u (T.d (T.u q0) (T.u (T.d T.e q0))))), (Steps.refl _), (Steps.cons (Step.root (Root.r19 (T.d T.e q0) (T.u (T.d T.e q0)))) (Steps.cons (Step.underU (Step.underU (Step.leftD (T.u (T.d T.e q0)) (Step.root (Root.r14 (T.d T.e q0)))))) (Steps.cons (Step.underU (Step.underU (Step.leftD (T.u (T.d T.e q0)) (Step.root (Root.r9 q0))))) (Steps.refl _))))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        have e2 := e0.symm
        subst e2
        subst e1
        exact ⟨(T.u (T.u (T.d q0 (T.u (T.d T.e (T.u (T.u q0))))))), (Steps.refl _), (Steps.cons (Step.root (Root.r19 (T.d T.e (T.u (T.u q0))) (T.u (T.d T.e (T.u (T.u q0)))))) (Steps.cons (Step.underU (Step.underU (Step.leftD (T.u (T.d T.e (T.u (T.u q0)))) (Step.root (Root.r14 (T.d T.e (T.u (T.u q0)))))))) (Steps.cons (Step.underU (Step.underU (Step.leftD (T.u (T.d T.e (T.u (T.u q0)))) (Step.root (Root.r9 (T.u (T.u q0))))))) (Steps.cons (Step.underU (Step.underU (Step.leftD (T.u (T.d T.e (T.u (T.u q0)))) (Step.root (Root.r3 q0))))) (Steps.refl _)))))⟩
    | @left _ t1 _ h1 =>
      exact ⟨(T.u (T.u (T.d t1 x1))), (Steps.cons (Step.underU (Step.underU (Step.leftD x1 h1))) (Steps.refl _)), (Steps.cons (Step.root (Root.r4 t1 x1)) (Steps.refl _))⟩
    | @right _ _ t1 h1 =>
      exact ⟨(T.u (T.u (T.d x0 t1))), (Steps.cons (Step.underU (Step.underU (Step.rightD x0 h1))) (Steps.refl _)), (Steps.cons (Step.right (T.m x0 t1) h1) (Steps.cons (Step.root (Root.r4 x0 t1)) (Steps.refl _)))⟩
  | @right _ _ t0 h0 =>
    exact ⟨(T.u (T.u (T.d x0 t0))), (Steps.cons (Step.underU (Step.underU (Step.rightD x0 h0))) (Steps.refl _)), (Steps.cons (Step.left t0 (Step.right x0 h0)) (Steps.cons (Step.root (Root.r4 x0 t0)) (Steps.refl _)))⟩
end submission.Austin12073

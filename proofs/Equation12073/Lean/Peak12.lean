import Basic
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin12073
open T
theorem peak12 (x0 : T) (x1 : T) {u : T} (h : Step (T.m x0 (T.d x1 x0)) u) : Join (T.u (T.u (T.d x1 (T.d x1 x0)))) u := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      have e3 := e1.symm
      have cycle := congrArg size e3
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      cases e1
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
      have e2 := e1.symm
      have cycle := congrArg size e2
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      have e3 := (T.d.inj e1).1
      have e4 := (T.d.inj e1).2
      have e5 := e3.symm
      subst e5
      have e6 := e4.symm
      subst e6
      exact ⟨q1, (Steps.cons (Step.underU (Step.underU (Step.root (Root.r13 q1)))) (Steps.cons (Step.root (Root.r3 q1)) (Steps.refl _))), (Steps.refl _)⟩
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
      exact ⟨(T.u (T.u (T.d x1 x1))), (Steps.cons (Step.underU (Step.underU (Step.rightD x1 (Step.root (Root.r7 x1))))) (Steps.refl _)), (Steps.cons (Step.underU (Step.underU (Step.leftD (T.d x1 T.e) (Step.root (Root.r7 x1))))) (Steps.cons (Step.underU (Step.underU (Step.rightD x1 (Step.root (Root.r7 x1))))) (Steps.refl _)))⟩
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
      cases e1
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      have e3 := (T.d.inj e1).1
      have e4 := (T.d.inj e1).2
      have e5 := e3.symm
      subst e5
      exact ⟨(T.u (T.u (T.d q1 (T.d q1 q0)))), (Steps.refl _), (Steps.refl _)⟩
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      cases e1
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
      cases e1
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
      have e2 := e1.symm
      have cycle := congrArg size e2
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
      have e2 := e1.symm
      have cycle := congrArg size e2
      simp only [size] at cycle
      omega
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
      have e2 := e1.symm
      have cycle := congrArg size e2
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
      have e2 := e1.symm
      have cycle := congrArg size e2
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
      cases e1
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      cases e1
  | @left _ t0 _ h0 =>
    exact ⟨(T.u (T.u (T.d x1 (T.d x1 t0)))), (Steps.cons (Step.underU (Step.underU (Step.rightD x1 (Step.rightD x1 h0)))) (Steps.refl _)), (Steps.cons (Step.right t0 (Step.rightD x1 h0)) (Steps.cons (Step.root (Root.r12 t0 x1)) (Steps.refl _)))⟩
  | @right _ _ t0 h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.d.inj he).1
        have e1 := (T.d.inj he).2
        have e2 := e0.symm
        subst e2
        subst e1
        exact ⟨(T.u (T.u (T.d q0 q0))), (Steps.cons (Step.underU (Step.underU (Step.rightD q0 (Step.root (Root.r7 q0))))) (Steps.refl _)), (Steps.cons (Step.root (Root.r8 q0)) (Steps.refl _))⟩
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.d.inj he).1
        have e1 := (T.d.inj he).2
        subst e0
        subst e1
        exact ⟨(T.d T.e q0), (Steps.cons (Step.underU (Step.underU (Step.root (Root.r13 (T.d T.e q0))))) (Steps.cons (Step.root (Root.r3 (T.d T.e q0))) (Steps.refl _))), (Steps.cons (Step.root (Root.r10 q0)) (Steps.refl _))⟩
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.d.inj he).1
        have e1 := (T.d.inj he).2
        subst e0
        subst e1
        exact ⟨(T.u (T.u (T.d (T.d T.e q0) (T.u (T.d T.e q0))))), (Steps.cons (Step.underU (Step.underU (Step.rightD (T.d T.e q0) (Step.root (Root.r11 q0))))) (Steps.refl _)), (Steps.cons (Step.root (Root.r21 q0)) (Steps.refl _))⟩
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.d.inj he).1
        have e1 := (T.d.inj he).2
        have e2 := e0.symm
        subst e2
        subst e1
        exact ⟨(T.u (T.u (T.d q0 (T.u q0)))), (Steps.cons (Step.underU (Step.underU (Step.rightD q0 (Step.root (Root.r13 q0))))) (Steps.refl _)), (Steps.cons (Step.root (Root.r15 q0)) (Steps.refl _))⟩
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.d.inj he).1
        have e1 := (T.d.inj he).2
        subst e0
        have e2 := e1.symm
        subst e2
        exact ⟨(T.u (T.u (T.d (T.d T.e (T.u (T.u q0))) (T.u (T.d T.e (T.u (T.u q0))))))), (Steps.cons (Step.underU (Step.underU (Step.rightD (T.d T.e (T.u (T.u q0))) (Step.root (Root.r18 q0))))) (Steps.refl _)), (Steps.cons (Step.root (Root.r22 q0)) (Steps.refl _))⟩
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
    | @leftD _ t1 _ h1 =>
      exact ⟨(T.u (T.u (T.d t1 (T.d t1 x0)))), (Steps.cons (Step.underU (Step.underU (Step.leftD (T.d x1 x0) h1))) (Steps.cons (Step.underU (Step.underU (Step.rightD t1 (Step.leftD x0 h1)))) (Steps.refl _))), (Steps.cons (Step.root (Root.r12 x0 t1)) (Steps.refl _))⟩
    | @rightD _ _ t1 h1 =>
      exact ⟨(T.u (T.u (T.d x1 (T.d x1 t1)))), (Steps.cons (Step.underU (Step.underU (Step.rightD x1 (Step.rightD x1 h1)))) (Steps.refl _)), (Steps.cons (Step.left (T.d x1 t1) h1) (Steps.cons (Step.root (Root.r12 t1 x1)) (Steps.refl _)))⟩
end submission.Austin12073

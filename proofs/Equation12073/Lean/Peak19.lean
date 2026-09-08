import Basic
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin12073
open T
theorem peak19 (x0 : T) (x1 : T) {u : T} (h : Step (T.m (T.u (T.u (T.d x0 x1))) x1) u) : Join (T.u (T.u (T.d (T.m x0 x1) x1))) u := by
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
      exact ⟨x0, (Steps.cons (Step.underU (Step.underU (Step.root (Root.r7 (T.m x0 T.e))))) (Steps.cons (Step.underU (Step.underU (Step.root (Root.r2 x0)))) (Steps.cons (Step.root (Root.r3 x0)) (Steps.refl _)))), (Steps.cons (Step.root (Root.r3 (T.d x0 T.e))) (Steps.cons (Step.root (Root.r7 x0)) (Steps.refl _)))⟩
    · rw [ho]
      cases he
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
      have e2 := T.u.inj e0
      have e3 := e1.symm
      subst e3
      have e4 := T.u.inj e2
      have e5 := e4.symm
      have cycle := congrArg size e5
      simp only [size] at cycle
      omega
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := T.u.inj e0
      have e3 := e1.symm
      subst e3
      have e4 := T.u.inj e2
      have e5 := (T.d.inj e4).1
      have e6 := (T.d.inj e4).2
      have e7 := e5.symm
      subst e7
      exact ⟨(T.u (T.u (T.d (T.m q0 q1) q1))), (Steps.refl _), (Steps.refl _)⟩
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      cases e0
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := T.u.inj e0
      subst e1
      have e3 := e2.symm
      have cycle := congrArg size e3
      simp only [size] at cycle
      omega
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
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := T.u.inj he
        have e1 := T.u.inj e0
        cases e1
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := T.u.inj he
        cases e0
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
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
    | @underU _ t1 h1 =>
      cases h1 with
      | root hr =>
        rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          have e0 := T.u.inj he
          cases e0
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          have e0 := T.u.inj he
          cases e0
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
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
      | @underU _ t2 h2 =>
        cases h2 with
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
            exact ⟨q0, (Steps.cons (Step.underU (Step.underU (Step.root (Root.r7 (T.m q0 T.e))))) (Steps.cons (Step.underU (Step.underU (Step.root (Root.r2 q0)))) (Steps.cons (Step.root (Root.r3 q0)) (Steps.refl _)))), (Steps.cons (Step.root (Root.r2 (T.u (T.u q0)))) (Steps.cons (Step.root (Root.r3 q0)) (Steps.refl _)))⟩
          · rw [ho]
            cases he
          · rw [ho]
            have e0 := (T.d.inj he).1
            have e1 := (T.d.inj he).2
            subst e0
            subst e1
            exact ⟨(T.u (T.u (T.d T.e (T.d T.e q0)))), (Steps.cons (Step.underU (Step.underU (Step.leftD (T.d T.e q0) (Step.root (Root.r1 (T.d T.e q0)))))) (Steps.refl _)), (Steps.cons (Step.left (T.d T.e q0) (Step.root (Root.r3 q0))) (Steps.cons (Step.root (Root.r12 q0 T.e)) (Steps.refl _)))⟩
          · rw [ho]
            cases he
          · rw [ho]
            have e0 := (T.d.inj he).1
            have e1 := (T.d.inj he).2
            subst e0
            subst e1
            exact ⟨(T.d T.e q0), (Steps.cons (Step.underU (Step.underU (Step.leftD (T.u q0) (Step.root (Root.r10 q0))))) (Steps.cons (Step.underU (Step.underU (Step.root (Root.r11 q0)))) (Steps.cons (Step.root (Root.r3 (T.d T.e q0))) (Steps.refl _)))), (Steps.cons (Step.left (T.u q0) (Step.root (Root.r3 (T.d T.e q0)))) (Steps.cons (Step.root (Root.r10 q0)) (Steps.refl _)))⟩
          · rw [ho]
            cases he
          · rw [ho]
            have e0 := (T.d.inj he).1
            have e1 := (T.d.inj he).2
            have e2 := e0.symm
            subst e2
            subst e1
            exact ⟨q0, (Steps.cons (Step.underU (Step.underU (Step.leftD (T.d q0 q0) (Step.root (Root.r5 q0 q0))))) (Steps.cons (Step.underU (Step.underU (Step.root (Root.r13 q0)))) (Steps.cons (Step.root (Root.r3 q0)) (Steps.refl _)))), (Steps.cons (Step.left (T.d q0 q0) (Step.root (Root.r3 q0))) (Steps.cons (Step.root (Root.r5 q0 q0)) (Steps.refl _)))⟩
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
            exact ⟨(T.d T.e (T.u (T.u q0))), (Steps.cons (Step.underU (Step.underU (Step.leftD q0 (Step.root (Root.r16 q0))))) (Steps.cons (Step.underU (Step.underU (Step.root (Root.r18 q0)))) (Steps.cons (Step.root (Root.r3 (T.d T.e (T.u (T.u q0))))) (Steps.refl _)))), (Steps.cons (Step.left q0 (Step.root (Root.r3 (T.d T.e (T.u (T.u q0)))))) (Steps.cons (Step.root (Root.r16 q0)) (Steps.refl _)))⟩
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
        | @leftD _ t3 _ h3 =>
          exact ⟨(T.u (T.u (T.d (T.m t3 x1) x1))), (Steps.cons (Step.underU (Step.underU (Step.leftD x1 (Step.left x1 h3)))) (Steps.refl _)), (Steps.cons (Step.root (Root.r19 t3 x1)) (Steps.refl _))⟩
        | @rightD _ _ t3 h3 =>
          exact ⟨(T.u (T.u (T.d (T.m x0 t3) t3))), (Steps.cons (Step.underU (Step.underU (Step.leftD x1 (Step.right x0 h3)))) (Steps.cons (Step.underU (Step.underU (Step.rightD (T.m x0 t3) h3))) (Steps.refl _))), (Steps.cons (Step.right (T.u (T.u (T.d x0 t3))) h3) (Steps.cons (Step.root (Root.r19 x0 t3)) (Steps.refl _)))⟩
  | @right _ _ t0 h0 =>
    exact ⟨(T.u (T.u (T.d (T.m x0 t0) t0))), (Steps.cons (Step.underU (Step.underU (Step.leftD x1 (Step.right x0 h0)))) (Steps.cons (Step.underU (Step.underU (Step.rightD (T.m x0 t0) h0))) (Steps.refl _))), (Steps.cons (Step.left t0 (Step.underU (Step.underU (Step.rightD x0 h0)))) (Steps.cons (Step.root (Root.r19 x0 t0)) (Steps.refl _)))⟩
end submission.Austin12073

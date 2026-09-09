import Basic
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin12073
open T
theorem peak22 (x0 : T) {u : T} (h : Step (T.m x0 (T.u (T.d T.e (T.u (T.u x0))))) u) : Join (T.u (T.u (T.d (T.d T.e (T.u (T.u x0))) (T.u (T.d T.e (T.u (T.u x0))))))) u := by
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
      cases e1
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
      exact ⟨T.e, (Steps.cons (Step.underU (Step.underU (Step.leftD (T.u (T.d T.e (T.u (T.u T.e)))) (Step.rightD T.e (Step.underU (Step.root (Root.r6 ))))))) (Steps.cons (Step.underU (Step.underU (Step.leftD (T.u (T.d T.e (T.u (T.u T.e)))) (Step.rightD T.e (Step.root (Root.r6 )))))) (Steps.cons (Step.underU (Step.underU (Step.leftD (T.u (T.d T.e (T.u (T.u T.e)))) (Step.root (Root.r7 T.e))))) (Steps.cons (Step.underU (Step.underU (Step.rightD T.e (Step.underU (Step.rightD T.e (Step.underU (Step.root (Root.r6 )))))))) (Steps.cons (Step.underU (Step.underU (Step.rightD T.e (Step.underU (Step.rightD T.e (Step.root (Root.r6 ))))))) (Steps.cons (Step.underU (Step.underU (Step.rightD T.e (Step.underU (Step.root (Root.r7 T.e)))))) (Steps.cons (Step.underU (Step.underU (Step.rightD T.e (Step.root (Root.r6 ))))) (Steps.cons (Step.underU (Step.underU (Step.root (Root.r7 T.e)))) (Steps.cons (Step.underU (Step.root (Root.r6 ))) (Steps.cons (Step.root (Root.r6 )) (Steps.refl _))))))))))), (Steps.cons (Step.underU (Step.underU (Step.leftD (T.u (T.d T.e (T.u (T.u T.e)))) (Step.underU (Step.rightD T.e (Step.underU (Step.root (Root.r6 )))))))) (Steps.cons (Step.underU (Step.underU (Step.leftD (T.u (T.d T.e (T.u (T.u T.e)))) (Step.underU (Step.rightD T.e (Step.root (Root.r6 ))))))) (Steps.cons (Step.underU (Step.underU (Step.leftD (T.u (T.d T.e (T.u (T.u T.e)))) (Step.underU (Step.root (Root.r7 T.e)))))) (Steps.cons (Step.underU (Step.underU (Step.leftD (T.u (T.d T.e (T.u (T.u T.e)))) (Step.root (Root.r6 ))))) (Steps.cons (Step.underU (Step.underU (Step.rightD T.e (Step.underU (Step.rightD T.e (Step.underU (Step.root (Root.r6 )))))))) (Steps.cons (Step.underU (Step.underU (Step.rightD T.e (Step.underU (Step.rightD T.e (Step.root (Root.r6 ))))))) (Steps.cons (Step.underU (Step.underU (Step.rightD T.e (Step.underU (Step.root (Root.r7 T.e)))))) (Steps.cons (Step.underU (Step.underU (Step.rightD T.e (Step.root (Root.r6 ))))) (Steps.cons (Step.underU (Step.underU (Step.root (Root.r7 T.e)))) (Steps.cons (Step.underU (Step.root (Root.r6 ))) (Steps.cons (Step.root (Root.r6 )) (Steps.refl _))))))))))))⟩
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
      have e2 := T.u.inj e1
      have e3 := e2.symm
      have cycle := congrArg size e3
      simp only [size] at cycle
      omega
    · rw [ho]
      cases he
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
      have e2 := e0.symm
      subst e2
      have e3 := T.u.inj e1
      have e4 := e3.symm
      have cycle := congrArg size e4
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
      have e2 := T.u.inj e1
      have e3 := e2.symm
      have cycle := congrArg size e3
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
      have e2 := T.u.inj e1
      have e3 := (T.d.inj e2).1
      have e4 := (T.d.inj e2).2
      have e5 := e4.symm
      have cycle := congrArg size e5
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      exact ⟨(T.u (T.u (T.d (T.d T.e (T.u (T.u q0))) (T.u (T.d T.e (T.u (T.u q0))))))), (Steps.refl _), (Steps.refl _)⟩
  | @left _ t0 _ h0 =>
    exact ⟨(T.u (T.u (T.d (T.d T.e (T.u (T.u t0))) (T.u (T.d T.e (T.u (T.u t0))))))), (Steps.cons (Step.underU (Step.underU (Step.leftD (T.u (T.d T.e (T.u (T.u x0)))) (Step.rightD T.e (Step.underU (Step.underU h0)))))) (Steps.cons (Step.underU (Step.underU (Step.rightD (T.d T.e (T.u (T.u t0))) (Step.underU (Step.rightD T.e (Step.underU (Step.underU h0))))))) (Steps.refl _))), (Steps.cons (Step.right t0 (Step.underU (Step.rightD T.e (Step.underU (Step.underU h0))))) (Steps.cons (Step.root (Root.r22 t0)) (Steps.refl _)))⟩
  | @right _ _ t0 h0 =>
    cases h0 with
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
    | @underU _ t1 h1 =>
      cases h1 with
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
          cases e1
        · rw [ho]
          cases he
        · rw [ho]
          have e0 := (T.d.inj he).1
          have e1 := (T.d.inj he).2
          cases e0
        · rw [ho]
          cases he
        · rw [ho]
          have e0 := (T.d.inj he).1
          have e1 := (T.d.inj he).2
          cases e0
        · rw [ho]
          cases he
        · rw [ho]
          have e0 := (T.d.inj he).1
          have e1 := (T.d.inj he).2
          have e2 := e0.symm
          subst e2
          cases e1
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
          cases e0
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
      | @leftD _ t2 _ h2 =>
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
      | @rightD _ _ t2 h2 =>
        cases h2 with
        | root hr =>
          rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            have e0 := T.u.inj he
            have e1 := T.u.inj e0
            subst e1
            exact ⟨(T.u (T.u (T.d (T.d T.e q0) (T.u (T.d T.e q0))))), (Steps.cons (Step.underU (Step.underU (Step.leftD (T.u (T.d T.e (T.u (T.u (T.u q0))))) (Step.rightD T.e (Step.root (Root.r3 q0)))))) (Steps.cons (Step.underU (Step.underU (Step.rightD (T.d T.e q0) (Step.underU (Step.rightD T.e (Step.root (Root.r3 q0))))))) (Steps.refl _))), (Steps.cons (Step.root (Root.r21 q0)) (Steps.refl _))⟩
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
        | @underU _ t3 h3 =>
          cases h3 with
          | root hr =>
            rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩
            · rw [ho]
              cases he
            · rw [ho]
              cases he
            · rw [ho]
              have e0 := T.u.inj he
              subst e0
              exact ⟨(T.u (T.u (T.d (T.d T.e (T.u q0)) (T.u (T.d T.e (T.u q0)))))), (Steps.cons (Step.underU (Step.underU (Step.leftD (T.u (T.d T.e (T.u (T.u (T.u (T.u q0)))))) (Step.rightD T.e (Step.root (Root.r3 (T.u q0))))))) (Steps.cons (Step.underU (Step.underU (Step.rightD (T.d T.e (T.u q0)) (Step.underU (Step.rightD T.e (Step.root (Root.r3 (T.u q0)))))))) (Steps.refl _))), (Steps.cons (Step.root (Root.r21 (T.u q0))) (Steps.refl _))⟩
            · rw [ho]
              cases he
            · rw [ho]
              cases he
            · rw [ho]
              have e0 := T.u.inj he
              subst e0
              exact ⟨T.e, (Steps.cons (Step.underU (Step.underU (Step.leftD (T.u (T.d T.e (T.u (T.u T.e)))) (Step.rightD T.e (Step.underU (Step.root (Root.r6 ))))))) (Steps.cons (Step.underU (Step.underU (Step.leftD (T.u (T.d T.e (T.u (T.u T.e)))) (Step.rightD T.e (Step.root (Root.r6 )))))) (Steps.cons (Step.underU (Step.underU (Step.leftD (T.u (T.d T.e (T.u (T.u T.e)))) (Step.root (Root.r7 T.e))))) (Steps.cons (Step.underU (Step.underU (Step.rightD T.e (Step.underU (Step.rightD T.e (Step.underU (Step.root (Root.r6 )))))))) (Steps.cons (Step.underU (Step.underU (Step.rightD T.e (Step.underU (Step.rightD T.e (Step.root (Root.r6 ))))))) (Steps.cons (Step.underU (Step.underU (Step.rightD T.e (Step.underU (Step.root (Root.r7 T.e)))))) (Steps.cons (Step.underU (Step.underU (Step.rightD T.e (Step.root (Root.r6 ))))) (Steps.cons (Step.underU (Step.underU (Step.root (Root.r7 T.e)))) (Steps.cons (Step.underU (Step.root (Root.r6 ))) (Steps.cons (Step.root (Root.r6 )) (Steps.refl _))))))))))), (Steps.cons (Step.root (Root.r8 (T.u (T.d T.e (T.u T.e))))) (Steps.cons (Step.underU (Step.underU (Step.leftD (T.u (T.d T.e (T.u T.e))) (Step.underU (Step.rightD T.e (Step.root (Root.r6 ))))))) (Steps.cons (Step.underU (Step.underU (Step.leftD (T.u (T.d T.e (T.u T.e))) (Step.underU (Step.root (Root.r7 T.e)))))) (Steps.cons (Step.underU (Step.underU (Step.leftD (T.u (T.d T.e (T.u T.e))) (Step.root (Root.r6 ))))) (Steps.cons (Step.underU (Step.underU (Step.rightD T.e (Step.underU (Step.rightD T.e (Step.root (Root.r6 ))))))) (Steps.cons (Step.underU (Step.underU (Step.rightD T.e (Step.underU (Step.root (Root.r7 T.e)))))) (Steps.cons (Step.underU (Step.underU (Step.rightD T.e (Step.root (Root.r6 ))))) (Steps.cons (Step.underU (Step.underU (Step.root (Root.r7 T.e)))) (Steps.cons (Step.underU (Step.root (Root.r6 ))) (Steps.cons (Step.root (Root.r6 )) (Steps.refl _)))))))))))⟩
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
          | @underU _ t4 h4 =>
            exact ⟨(T.u (T.u (T.d (T.d T.e (T.u (T.u t4))) (T.u (T.d T.e (T.u (T.u t4))))))), (Steps.cons (Step.underU (Step.underU (Step.leftD (T.u (T.d T.e (T.u (T.u x0)))) (Step.rightD T.e (Step.underU (Step.underU h4)))))) (Steps.cons (Step.underU (Step.underU (Step.rightD (T.d T.e (T.u (T.u t4))) (Step.underU (Step.rightD T.e (Step.underU (Step.underU h4))))))) (Steps.refl _))), (Steps.cons (Step.left (T.u (T.d T.e (T.u (T.u t4)))) h4) (Steps.cons (Step.root (Root.r22 t4)) (Steps.refl _)))⟩
end submission.Austin12073

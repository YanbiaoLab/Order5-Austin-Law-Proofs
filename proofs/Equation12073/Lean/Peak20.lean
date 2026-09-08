import Basic
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin12073
open T
theorem peak20 (x0 : T) {u : T} (h : Step (T.m (T.d (T.u (T.u x0)) (T.u (T.u x0))) x0) u) : Join (T.u (T.u (T.d (T.u (T.u x0)) x0))) u := by
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
      exact ⟨T.e, (Steps.cons (Step.underU (Step.underU (Step.root (Root.r7 (T.u (T.u T.e)))))) (Steps.cons (Step.root (Root.r3 (T.u T.e))) (Steps.cons (Step.root (Root.r6 )) (Steps.refl _)))), (Steps.cons (Step.underU (Step.leftD (T.u (T.u T.e)) (Step.underU (Step.root (Root.r6 ))))) (Steps.cons (Step.underU (Step.leftD (T.u (T.u T.e)) (Step.root (Root.r6 )))) (Steps.cons (Step.underU (Step.rightD T.e (Step.underU (Step.root (Root.r6 ))))) (Steps.cons (Step.underU (Step.rightD T.e (Step.root (Root.r6 )))) (Steps.cons (Step.underU (Step.root (Root.r7 T.e))) (Steps.cons (Step.root (Root.r6 )) (Steps.refl _)))))))⟩
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
      have e2 := (T.d.inj e0).1
      have e3 := (T.d.inj e0).2
      subst e1
      cases e2
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
      have e2 := (T.d.inj e0).1
      have e3 := (T.d.inj e0).2
      subst e1
      have e4 := e2.symm
      have cycle := congrArg size e4
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := (T.d.inj e0).1
      have e3 := (T.d.inj e0).2
      have e4 := e1.symm
      subst e4
      cases e2
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
      have e2 := (T.d.inj e0).1
      have e3 := (T.d.inj e0).2
      have e4 := e1.symm
      subst e4
      exact ⟨(T.u (T.u (T.d (T.u (T.u q0)) q0))), (Steps.refl _), (Steps.refl _)⟩
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
    | @leftD _ t1 _ h1 =>
      cases h1 with
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
          exact ⟨(T.u (T.u (T.d q0 (T.u q0)))), (Steps.cons (Step.underU (Step.underU (Step.leftD (T.u q0) (Step.root (Root.r3 q0))))) (Steps.refl _)), (Steps.cons (Step.left (T.u q0) (Step.rightD q0 (Step.root (Root.r3 q0)))) (Steps.cons (Step.root (Root.r15 q0)) (Steps.refl _)))⟩
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
            have e0 := T.u.inj he
            subst e0
            exact ⟨(T.u (T.u (T.d (T.u q0) (T.u (T.u q0))))), (Steps.cons (Step.underU (Step.underU (Step.leftD (T.u (T.u q0)) (Step.root (Root.r3 (T.u q0)))))) (Steps.refl _)), (Steps.cons (Step.left (T.u (T.u q0)) (Step.rightD (T.u q0) (Step.root (Root.r3 (T.u q0))))) (Steps.cons (Step.root (Root.r15 (T.u q0))) (Steps.refl _)))⟩
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            have e0 := T.u.inj he
            subst e0
            exact ⟨T.e, (Steps.cons (Step.underU (Step.underU (Step.root (Root.r7 (T.u (T.u T.e)))))) (Steps.cons (Step.root (Root.r3 (T.u T.e))) (Steps.cons (Step.root (Root.r6 )) (Steps.refl _)))), (Steps.cons (Step.root (Root.r2 (T.d (T.u T.e) (T.u (T.u T.e))))) (Steps.cons (Step.underU (Step.leftD (T.u (T.u T.e)) (Step.root (Root.r6 )))) (Steps.cons (Step.underU (Step.rightD T.e (Step.underU (Step.root (Root.r6 ))))) (Steps.cons (Step.underU (Step.rightD T.e (Step.root (Root.r6 )))) (Steps.cons (Step.underU (Step.root (Root.r7 T.e))) (Steps.cons (Step.root (Root.r6 )) (Steps.refl _)))))))⟩
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
          exact ⟨(T.u (T.u (T.d (T.u (T.u t3)) t3))), (Steps.cons (Step.underU (Step.underU (Step.leftD x0 (Step.underU (Step.underU h3))))) (Steps.cons (Step.underU (Step.underU (Step.rightD (T.u (T.u t3)) h3))) (Steps.refl _))), (Steps.cons (Step.left x0 (Step.rightD (T.u (T.u t3)) (Step.underU (Step.underU h3)))) (Steps.cons (Step.right (T.d (T.u (T.u t3)) (T.u (T.u t3))) h3) (Steps.cons (Step.root (Root.r20 t3)) (Steps.refl _))))⟩
    | @rightD _ _ t1 h1 =>
      cases h1 with
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
          exact ⟨(T.u (T.u (T.d q0 (T.u q0)))), (Steps.cons (Step.underU (Step.underU (Step.leftD (T.u q0) (Step.root (Root.r3 q0))))) (Steps.refl _)), (Steps.cons (Step.left (T.u q0) (Step.leftD q0 (Step.root (Root.r3 q0)))) (Steps.cons (Step.root (Root.r15 q0)) (Steps.refl _)))⟩
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
            have e0 := T.u.inj he
            subst e0
            exact ⟨(T.u (T.u (T.d (T.u q0) (T.u (T.u q0))))), (Steps.cons (Step.underU (Step.underU (Step.leftD (T.u (T.u q0)) (Step.root (Root.r3 (T.u q0)))))) (Steps.refl _)), (Steps.cons (Step.left (T.u (T.u q0)) (Step.leftD (T.u q0) (Step.root (Root.r3 (T.u q0))))) (Steps.cons (Step.root (Root.r15 (T.u q0))) (Steps.refl _)))⟩
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            have e0 := T.u.inj he
            subst e0
            exact ⟨T.e, (Steps.cons (Step.underU (Step.underU (Step.root (Root.r7 (T.u (T.u T.e)))))) (Steps.cons (Step.root (Root.r3 (T.u T.e))) (Steps.cons (Step.root (Root.r6 )) (Steps.refl _)))), (Steps.cons (Step.root (Root.r2 (T.d (T.u (T.u T.e)) (T.u T.e)))) (Steps.cons (Step.underU (Step.leftD (T.u T.e) (Step.underU (Step.root (Root.r6 ))))) (Steps.cons (Step.underU (Step.leftD (T.u T.e) (Step.root (Root.r6 )))) (Steps.cons (Step.underU (Step.rightD T.e (Step.root (Root.r6 )))) (Steps.cons (Step.underU (Step.root (Root.r7 T.e))) (Steps.cons (Step.root (Root.r6 )) (Steps.refl _)))))))⟩
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
          exact ⟨(T.u (T.u (T.d (T.u (T.u t3)) t3))), (Steps.cons (Step.underU (Step.underU (Step.leftD x0 (Step.underU (Step.underU h3))))) (Steps.cons (Step.underU (Step.underU (Step.rightD (T.u (T.u t3)) h3))) (Steps.refl _))), (Steps.cons (Step.left x0 (Step.leftD (T.u (T.u t3)) (Step.underU (Step.underU h3)))) (Steps.cons (Step.right (T.d (T.u (T.u t3)) (T.u (T.u t3))) h3) (Steps.cons (Step.root (Root.r20 t3)) (Steps.refl _))))⟩
  | @right _ _ t0 h0 =>
    exact ⟨(T.u (T.u (T.d (T.u (T.u t0)) t0))), (Steps.cons (Step.underU (Step.underU (Step.leftD x0 (Step.underU (Step.underU h0))))) (Steps.cons (Step.underU (Step.underU (Step.rightD (T.u (T.u t0)) h0))) (Steps.refl _))), (Steps.cons (Step.left t0 (Step.leftD (T.u (T.u x0)) (Step.underU (Step.underU h0)))) (Steps.cons (Step.left t0 (Step.rightD (T.u (T.u t0)) (Step.underU (Step.underU h0)))) (Steps.cons (Step.root (Root.r20 t0)) (Steps.refl _))))⟩
end submission.Austin12073

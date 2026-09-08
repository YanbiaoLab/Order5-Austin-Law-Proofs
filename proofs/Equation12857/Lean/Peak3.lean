import Basic
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace Austin12857
open T
theorem peak3 (x0 : T) (x1 : T) {u : T} (h : Step (m x0 (m (s (m x0 (s x1))) x0)) u) : Join (m x0 (s x1)) u := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst x0
      have e2 := e1.symm
      have cycle := congrArg size e2
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst x0
      have e2 := (T.m.inj e1).1
      have e3 := (T.m.inj e1).2
      cases e2
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst x0
      have e2 := (T.m.inj e1).1
      have e3 := (T.m.inj e1).2
      have e4 := T.s.inj e2
      have e5 := (T.m.inj e4).1
      have e6 := (T.m.inj e4).2
      have e7 := T.s.inj e6
      subst x1
      exact ⟨(m q0 (s q1)), (Steps.refl _), (Steps.refl _)⟩
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst x0
      have e2 := (T.m.inj e1).1
      have e3 := (T.m.inj e1).2
      cases e2
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst x0
      have e2 := (T.m.inj e1).1
      have e3 := (T.m.inj e1).2
      have e4 := e2.symm
      have cycle := congrArg size e4
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst x0
      have e2 := (T.m.inj e1).1
      have e3 := (T.m.inj e1).2
      have e4 := T.s.inj e2
      have e5 := e4.symm
      subst q1
      exact ⟨(m (s q0) (s x1)), (Steps.refl _), (Steps.cons (Step.right (s q0) (Step.underS (Step.root (Root.r10 q0 x1)))) (Steps.cons (Step.right (s q0) (Step.root (Root.r7 x1))) (Steps.refl _)))⟩
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst x0
      have e2 := (T.m.inj e1).1
      have e3 := (T.m.inj e1).2
      cases e2
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst x0
      have e2 := (T.m.inj e1).1
      have e3 := (T.m.inj e1).2
      have e4 := e2.symm
      have cycle := congrArg size e4
      simp only [size] at cycle
      omega
    · rw [ho]
      cases he
  | @left _ t0 _ h0 =>
    exact ⟨(m t0 (s x1)), (Steps.cons (Step.left (s x1) h0) (Steps.refl _)), (Steps.cons (Step.right t0 (Step.left x0 (Step.underS (Step.left (s x1) h0)))) (Steps.cons (Step.right t0 (Step.right (s (m t0 (s x1))) h0)) (Steps.cons (Step.root (Root.r3 t0 x1)) (Steps.refl _))))⟩
  | @right _ _ t0 h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩
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
        have e2 := e0.symm
        subst q0
        have cycle := congrArg size e1
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
        have e2 := T.s.inj e0
        subst x0
        have e3 := e2.symm
        have cycle := congrArg size e3
        simp only [size] at cycle
        omega
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        cases e0
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        have e2 := T.s.inj e0
        subst x0
        have e3 := e2.symm
        have cycle := congrArg size e3
        simp only [size] at cycle
        omega
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        have e2 := T.s.inj e0
        subst x0
        cases e2
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        cases e0
      · rw [ho]
        cases he
    | @left _ t1 _ h1 =>
      cases h1 with
      | root hr =>
        rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩
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
          have e0 := T.s.inj he
          cases e0
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          have e0 := T.s.inj he
          have e1 := (T.m.inj e0).1
          have e2 := (T.m.inj e0).2
          subst x0
          have e3 := T.s.inj e2
          subst x1
          exact ⟨(m (s q0) (s q1)), (Steps.refl _), (Steps.cons (Step.root (Root.r6 q0 (s (s q1)))) (Steps.cons (Step.right (s q0) (Step.root (Root.r7 q1))) (Steps.refl _)))⟩
      | @underS _ t2 h2 =>
        cases h2 with
        | root hr =>
          rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩
          · rw [ho]
            have e0 := (T.m.inj he).1
            have e1 := (T.m.inj he).2
            subst x0
            have e2 := e1.symm
            subst q0
            exact ⟨(s (s x1)), (Steps.cons (Step.root (Root.r1 (s x1))) (Steps.refl _)), (Steps.cons (Step.root (Root.r6 x1 (s (s x1)))) (Steps.cons (Step.right (s x1) (Step.root (Root.r7 x1))) (Steps.cons (Step.root (Root.r1 (s x1))) (Steps.refl _))))⟩
          · rw [ho]
            have e0 := (T.m.inj he).1
            have e1 := (T.m.inj he).2
            subst x0
            cases e1
          · rw [ho]
            have e0 := (T.m.inj he).1
            have e1 := (T.m.inj he).2
            subst x0
            cases e1
          · rw [ho]
            have e0 := (T.m.inj he).1
            have e1 := (T.m.inj he).2
            subst x0
            cases e1
          · rw [ho]
            have e0 := (T.m.inj he).1
            have e1 := (T.m.inj he).2
            subst x0
            cases e1
          · rw [ho]
            have e0 := (T.m.inj he).1
            have e1 := (T.m.inj he).2
            subst x0
            cases e1
          · rw [ho]
            cases he
          · rw [ho]
            have e0 := (T.m.inj he).1
            have e1 := (T.m.inj he).2
            subst x0
            cases e1
          · rw [ho]
            have e0 := (T.m.inj he).1
            have e1 := (T.m.inj he).2
            subst x0
            cases e1
          · rw [ho]
            cases he
        | @left _ t3 _ h3 =>
          exact ⟨(m t3 (s x1)), (Steps.cons (Step.left (s x1) h3) (Steps.refl _)), (Steps.cons (Step.left (m (s (m t3 (s x1))) x0) h3) (Steps.cons (Step.right t3 (Step.right (s (m t3 (s x1))) h3)) (Steps.cons (Step.root (Root.r3 t3 x1)) (Steps.refl _))))⟩
        | @right _ _ t3 h3 =>
          cases h3 with
          | root hr =>
            rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩
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
              have e0 := T.s.inj he
              subst x1
              exact ⟨(m x0 (s q0)), (Steps.cons (Step.right x0 (Step.root (Root.r7 q0))) (Steps.refl _)), (Steps.cons (Step.root (Root.r3 x0 q0)) (Steps.refl _))⟩
            · rw [ho]
              cases he
            · rw [ho]
              cases he
            · rw [ho]
              have e0 := T.s.inj he
              subst x1
              exact ⟨(m x0 (s (s (s q1)))), (Steps.cons (Step.right x0 (Step.root (Root.r10 q0 q1))) (Steps.refl _)), (Steps.cons (Step.root (Root.r3 x0 (s (s q1)))) (Steps.refl _))⟩
          | @underS _ t4 h4 =>
            exact ⟨(m x0 (s t4)), (Steps.cons (Step.right x0 (Step.underS h4)) (Steps.refl _)), (Steps.cons (Step.root (Root.r3 x0 t4)) (Steps.refl _))⟩
    | @right _ _ t1 h1 =>
      exact ⟨(m t1 (s x1)), (Steps.cons (Step.left (s x1) h1) (Steps.refl _)), (Steps.cons (Step.left (m (s (m x0 (s x1))) t1) h1) (Steps.cons (Step.right t1 (Step.left t1 (Step.underS (Step.left (s x1) h1)))) (Steps.cons (Step.root (Root.r3 t1 x1)) (Steps.refl _))))⟩
end Austin12857

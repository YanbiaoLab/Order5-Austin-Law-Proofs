import Basic
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace Austin12857
open T
theorem peak2 (x0 : T) (x1 : T) (x2 : T) {u : T} (h : Step (m x0 (m (m x1 (m x0 (s x2))) x0)) u) : Join x1 u := by
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
      have e4 := (T.m.inj e2).1
      have e5 := (T.m.inj e2).2
      subst x1
      have e6 := (T.m.inj e5).1
      have e7 := (T.m.inj e5).2
      have e8 := T.s.inj e7
      subst x2
      exact ⟨q1, (Steps.refl _), (Steps.refl _)⟩
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
      have e4 := (T.m.inj e2).1
      have e5 := (T.m.inj e2).2
      subst x1
      cases e5
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
      cases e2
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst x0
      have e2 := (T.m.inj e1).1
      have e3 := (T.m.inj e1).2
      have e4 := (T.m.inj e2).1
      have e5 := (T.m.inj e2).2
      subst x1
      cases e5
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
    exact ⟨x1, (Steps.refl _), (Steps.cons (Step.right t0 (Step.left x0 (Step.right x1 (Step.left (s x2) h0)))) (Steps.cons (Step.right t0 (Step.right (m x1 (m t0 (s x2))) h0)) (Steps.cons (Step.root (Root.r2 t0 x1 x2)) (Steps.refl _))))⟩
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
        cases e0
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        have e2 := (T.m.inj e0).1
        have e3 := (T.m.inj e0).2
        subst x0
        subst x1
        have e4 := (T.m.inj e3).1
        have e5 := (T.m.inj e3).2
        cases e4
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
        have e2 := (T.m.inj e0).1
        have e3 := (T.m.inj e0).2
        subst x0
        subst x1
        cases e3
      · rw [ho]
        cases he
    | @left _ t1 _ h1 =>
      cases h1 with
      | root hr =>
        rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩
        · rw [ho]
          have e0 := (T.m.inj he).1
          have e1 := (T.m.inj he).2
          subst x1
          have e2 := e1.symm
          subst q0
          exact ⟨(m x0 (s x2)), (Steps.refl _), (Steps.cons (Step.root (Root.r3 x0 x2)) (Steps.refl _))⟩
        · rw [ho]
          have e0 := (T.m.inj he).1
          have e1 := (T.m.inj he).2
          subst x1
          have e2 := (T.m.inj e1).1
          have e3 := (T.m.inj e1).2
          subst x0
          have e4 := e3.symm
          subst q0
          exact ⟨(s x2), (Steps.refl _), (Steps.cons (Step.root (Root.r5 q1 x2 q2)) (Steps.refl _))⟩
        · rw [ho]
          have e0 := (T.m.inj he).1
          have e1 := (T.m.inj he).2
          subst x1
          have e2 := (T.m.inj e1).1
          have e3 := (T.m.inj e1).2
          subst x0
          have e4 := e3.symm
          subst q0
          exact ⟨(s x2), (Steps.refl _), (Steps.cons (Step.left (m (m (s x2) (s q1)) (s (m (s x2) (s q1)))) (Step.root (Root.r10 x2 q1))) (Steps.cons (Step.right (s (s (s q1))) (Step.right (m (s x2) (s q1)) (Step.root (Root.r10 x2 q1)))) (Steps.cons (Step.root (Root.r8 q1 (s x2))) (Steps.refl _))))⟩
        · rw [ho]
          have e0 := (T.m.inj he).1
          have e1 := (T.m.inj he).2
          subst x1
          have e2 := (T.m.inj e1).1
          have e3 := (T.m.inj e1).2
          subst x0
          have e4 := T.s.inj e3
          subst x2
          exact ⟨(s q0), (Steps.refl _), (Steps.cons (Step.root (Root.r9 q1 (s q0))) (Steps.cons (Step.root (Root.r7 q0)) (Steps.refl _)))⟩
        · rw [ho]
          have e0 := (T.m.inj he).1
          have e1 := (T.m.inj he).2
          subst x1
          have e2 := (T.m.inj e1).1
          have e3 := (T.m.inj e1).2
          subst x0
          cases e3
        · rw [ho]
          have e0 := (T.m.inj he).1
          have e1 := (T.m.inj he).2
          subst x1
          have e2 := (T.m.inj e1).1
          have e3 := (T.m.inj e1).2
          subst x0
          have e4 := T.s.inj e3
          subst x2
          exact ⟨(s q0), (Steps.refl _), (Steps.cons (Step.root (Root.r4 q1 (s q0))) (Steps.refl _))⟩
        · rw [ho]
          cases he
        · rw [ho]
          have e0 := (T.m.inj he).1
          have e1 := (T.m.inj he).2
          subst x1
          have e2 := (T.m.inj e1).1
          have e3 := (T.m.inj e1).2
          subst x0
          have e4 := T.s.inj e3
          subst x2
          exact ⟨(s (s (s q0))), (Steps.refl _), (Steps.cons (Step.root (Root.r9 q1 q0)) (Steps.refl _))⟩
        · rw [ho]
          have e0 := (T.m.inj he).1
          have e1 := (T.m.inj he).2
          subst x1
          have e2 := (T.m.inj e1).1
          have e3 := (T.m.inj e1).2
          subst x0
          cases e3
        · rw [ho]
          cases he
      | @left _ t2 _ h2 =>
        exact ⟨t2, (Steps.cons h2 (Steps.refl _)), (Steps.cons (Step.root (Root.r2 x0 t2 x2)) (Steps.refl _))⟩
      | @right _ _ t2 h2 =>
        cases h2 with
        | root hr =>
          rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩
          · rw [ho]
            have e0 := (T.m.inj he).1
            have e1 := (T.m.inj he).2
            subst x0
            have e2 := e1.symm
            subst q0
            exact ⟨x1, (Steps.refl _), (Steps.cons (Step.root (Root.r4 x2 x1)) (Steps.refl _))⟩
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
          exact ⟨x1, (Steps.refl _), (Steps.cons (Step.left (m (m x1 (m t3 (s x2))) x0) h3) (Steps.cons (Step.right t3 (Step.right (m x1 (m t3 (s x2))) h3)) (Steps.cons (Step.root (Root.r2 t3 x1 x2)) (Steps.refl _))))⟩
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
              subst x2
              exact ⟨x1, (Steps.refl _), (Steps.cons (Step.root (Root.r2 x0 x1 q0)) (Steps.refl _))⟩
            · rw [ho]
              cases he
            · rw [ho]
              cases he
            · rw [ho]
              have e0 := T.s.inj he
              subst x2
              exact ⟨x1, (Steps.refl _), (Steps.cons (Step.root (Root.r2 x0 x1 (s (s q1)))) (Steps.refl _))⟩
          | @underS _ t4 h4 =>
            exact ⟨x1, (Steps.refl _), (Steps.cons (Step.root (Root.r2 x0 x1 t4)) (Steps.refl _))⟩
    | @right _ _ t1 h1 =>
      exact ⟨x1, (Steps.refl _), (Steps.cons (Step.left (m (m x1 (m x0 (s x2))) t1) h1) (Steps.cons (Step.right t1 (Step.left t1 (Step.right x1 (Step.left (s x2) h1)))) (Steps.cons (Step.root (Root.r2 t1 x1 x2)) (Steps.refl _))))⟩
end Austin12857

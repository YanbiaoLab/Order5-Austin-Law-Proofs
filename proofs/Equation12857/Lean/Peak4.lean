import Basic
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace Austin12857
open T
theorem peak4 (x0 : T) (x1 : T) {u : T} (h : Step (m (s x0) (m (m x1 (s (s x0))) (s x0))) u) : Join x1 u := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst q0
      cases e1
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst q0
      have e3 := (T.m.inj e1).1
      have e4 := (T.m.inj e1).2
      have e5 := (T.m.inj e3).1
      have e6 := (T.m.inj e3).2
      subst x1
      cases e6
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst q0
      have e3 := (T.m.inj e1).1
      have e4 := (T.m.inj e1).2
      cases e3
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := T.s.inj e0
      have e3 := (T.m.inj e1).1
      have e4 := (T.m.inj e1).2
      subst x0
      have e5 := (T.m.inj e3).1
      have e6 := (T.m.inj e3).2
      subst x1
      exact ⟨q1, (Steps.refl _), (Steps.refl _)⟩
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      cases e0
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := T.s.inj e0
      have e3 := (T.m.inj e1).1
      have e4 := (T.m.inj e1).2
      subst x0
      cases e3
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := T.s.inj e0
      have e3 := (T.m.inj e1).1
      have e4 := (T.m.inj e1).2
      subst x0
      have e5 := (T.m.inj e3).1
      have e6 := (T.m.inj e3).2
      subst x1
      have e7 := T.s.inj e6
      have e8 := e7.symm
      have cycle := congrArg size e8
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      cases e0
    · rw [ho]
      cases he
  | @left _ t0 _ h0 =>
    cases h0 with
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
        subst x0
        exact ⟨x1, (Steps.refl _), (Steps.cons (Step.right (s q0) (Step.left (s (s (s (s q0)))) (Step.right x1 (Step.root (Root.r7 (s q0)))))) (Steps.cons (Step.right (s q0) (Step.right (m x1 (s (s q0))) (Step.root (Root.r7 q0)))) (Steps.cons (Step.root (Root.r4 q0 x1)) (Steps.refl _))))⟩
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := T.s.inj he
        subst x0
        exact ⟨x1, (Steps.refl _), (Steps.cons (Step.right (s (s (s q1))) (Step.left (s (m (s q0) (s q1))) (Step.right x1 (Step.underS (Step.root (Root.r10 q0 q1)))))) (Steps.cons (Step.right (s (s (s q1))) (Step.left (s (m (s q0) (s q1))) (Step.right x1 (Step.root (Root.r7 q1))))) (Steps.cons (Step.right (s (s (s q1))) (Step.right (m x1 (s q1)) (Step.root (Root.r10 q0 q1)))) (Steps.cons (Step.root (Root.r8 q1 x1)) (Steps.refl _)))))⟩
    | @underS _ t1 h1 =>
      exact ⟨x1, (Steps.refl _), (Steps.cons (Step.right (s t1) (Step.left (s x0) (Step.right x1 (Step.underS (Step.underS h1))))) (Steps.cons (Step.right (s t1) (Step.right (m x1 (s (s t1))) (Step.underS h1))) (Steps.cons (Step.root (Root.r4 t1 x1)) (Steps.refl _))))⟩
  | @right _ _ t0 h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        have e2 := e0.symm
        subst q0
        cases e1
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        have e2 := e0.symm
        subst q0
        cases e1
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        have e2 := e0.symm
        subst q0
        cases e1
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        cases e0
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        have e2 := (T.m.inj e0).1
        have e3 := (T.m.inj e0).2
        cases e1
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
        cases e1
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
          exact ⟨(s (s x0)), (Steps.refl _), (Steps.cons (Step.root (Root.r6 x0 (s (s x0)))) (Steps.cons (Step.right (s x0) (Step.root (Root.r7 x0))) (Steps.cons (Step.root (Root.r1 (s x0))) (Steps.refl _))))⟩
        · rw [ho]
          have e0 := (T.m.inj he).1
          have e1 := (T.m.inj he).2
          subst x1
          cases e1
        · rw [ho]
          have e0 := (T.m.inj he).1
          have e1 := (T.m.inj he).2
          subst x1
          cases e1
        · rw [ho]
          have e0 := (T.m.inj he).1
          have e1 := (T.m.inj he).2
          subst x1
          cases e1
        · rw [ho]
          have e0 := (T.m.inj he).1
          have e1 := (T.m.inj he).2
          subst x1
          cases e1
        · rw [ho]
          have e0 := (T.m.inj he).1
          have e1 := (T.m.inj he).2
          subst x1
          cases e1
        · rw [ho]
          cases he
        · rw [ho]
          have e0 := (T.m.inj he).1
          have e1 := (T.m.inj he).2
          subst x1
          cases e1
        · rw [ho]
          have e0 := (T.m.inj he).1
          have e1 := (T.m.inj he).2
          subst x1
          cases e1
        · rw [ho]
          cases he
      | @left _ t2 _ h2 =>
        exact ⟨t2, (Steps.cons h2 (Steps.refl _)), (Steps.cons (Step.root (Root.r4 x0 t2)) (Steps.refl _))⟩
      | @right _ _ t2 h2 =>
        cases h2 with
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
            have e1 := T.s.inj e0
            subst x0
            exact ⟨x1, (Steps.refl _), (Steps.cons (Step.root (Root.r8 q0 x1)) (Steps.refl _))⟩
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            have e0 := T.s.inj he
            cases e0
        | @underS _ t3 h3 =>
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
              subst x0
              exact ⟨x1, (Steps.refl _), (Steps.cons (Step.root (Root.r8 (s q0) x1)) (Steps.refl _))⟩
            · rw [ho]
              cases he
            · rw [ho]
              cases he
            · rw [ho]
              have e0 := T.s.inj he
              subst x0
              exact ⟨x1, (Steps.refl _), (Steps.cons (Step.left (m (m x1 (s (s (s (s q1))))) (s (m (s q0) (s q1)))) (Step.root (Root.r10 q0 q1))) (Steps.cons (Step.right (s (s (s q1))) (Step.left (s (m (s q0) (s q1))) (Step.right x1 (Step.root (Root.r7 q1))))) (Steps.cons (Step.right (s (s (s q1))) (Step.right (m x1 (s q1)) (Step.root (Root.r10 q0 q1)))) (Steps.cons (Step.root (Root.r8 q1 x1)) (Steps.refl _)))))⟩
          | @underS _ t4 h4 =>
            exact ⟨x1, (Steps.refl _), (Steps.cons (Step.left (m (m x1 (s (s t4))) (s x0)) (Step.underS h4)) (Steps.cons (Step.right (s t4) (Step.right (m x1 (s (s t4))) (Step.underS h4))) (Steps.cons (Step.root (Root.r4 t4 x1)) (Steps.refl _))))⟩
    | @right _ _ t1 h1 =>
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
          subst x0
          exact ⟨x1, (Steps.refl _), (Steps.cons (Step.left (m (m x1 (s (s (s (s (s q0)))))) (s q0)) (Step.root (Root.r7 q0))) (Steps.cons (Step.right (s q0) (Step.left (s q0) (Step.right x1 (Step.root (Root.r7 (s q0)))))) (Steps.cons (Step.root (Root.r4 q0 x1)) (Steps.refl _))))⟩
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          have e0 := T.s.inj he
          subst x0
          exact ⟨x1, (Steps.refl _), (Steps.cons (Step.left (m (m x1 (s (s (m (s q0) (s q1))))) (s (s (s q1)))) (Step.root (Root.r10 q0 q1))) (Steps.cons (Step.right (s (s (s q1))) (Step.left (s (s (s q1))) (Step.right x1 (Step.underS (Step.root (Root.r10 q0 q1)))))) (Steps.cons (Step.root (Root.r4 (s (s q1)) x1)) (Steps.refl _))))⟩
      | @underS _ t2 h2 =>
        exact ⟨x1, (Steps.refl _), (Steps.cons (Step.left (m (m x1 (s (s x0))) (s t2)) (Step.underS h2)) (Steps.cons (Step.right (s t2) (Step.left (s t2) (Step.right x1 (Step.underS (Step.underS h2))))) (Steps.cons (Step.root (Root.r4 t2 x1)) (Steps.refl _))))⟩
end Austin12857

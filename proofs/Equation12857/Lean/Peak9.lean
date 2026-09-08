import Basic
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace Austin12857
open T
theorem peak9 (x0 : T) (x1 : T) {u : T} (h : Step (m (m x0 (s x1)) (m x0 (m x0 (s x1)))) u) : Join (s (s (s x1))) u := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst q0
      have e3 := (T.m.inj e1).1
      have e4 := (T.m.inj e1).2
      cases e4
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst q0
      have e3 := (T.m.inj e1).1
      have e4 := (T.m.inj e1).2
      have cycle := congrArg size e3
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst q0
      have e3 := (T.m.inj e1).1
      have e4 := (T.m.inj e1).2
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
      have e2 := (T.m.inj e0).1
      have e3 := (T.m.inj e0).2
      have e4 := (T.m.inj e1).1
      have e5 := (T.m.inj e1).2
      subst x0
      cases e3
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
      have e4 := (T.m.inj e1).1
      have e5 := (T.m.inj e1).2
      subst x0
      have e6 := T.s.inj e3
      have e7 := (T.m.inj e5).1
      have e8 := (T.m.inj e5).2
      subst x1
      exact ⟨(s (s (s q1))), (Steps.refl _), (Steps.refl _)⟩
    · rw [ho]
      cases he
  | @left _ t0 _ h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        have e2 := e1.symm
        subst q0
        exact ⟨(s (s (s x1))), (Steps.refl _), (Steps.cons (Step.right (s (s x1)) (Step.root (Root.r6 x1 x1))) (Steps.cons (Step.root (Root.r6 (s x1) x1)) (Steps.cons (Step.root (Root.r1 (s (s x1)))) (Steps.refl _))))⟩
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
    | @left _ t1 _ h1 =>
      exact ⟨(s (s (s x1))), (Steps.refl _), (Steps.cons (Step.right (m t1 (s x1)) (Step.left (m x0 (s x1)) h1)) (Steps.cons (Step.right (m t1 (s x1)) (Step.right t1 (Step.left (s x1) h1))) (Steps.cons (Step.root (Root.r9 t1 x1)) (Steps.refl _))))⟩
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
          subst x1
          exact ⟨(s (s (s q0))), (Steps.cons (Step.root (Root.r7 (s (s q0)))) (Steps.refl _)), (Steps.cons (Step.right (m x0 (s q0)) (Step.right x0 (Step.right x0 (Step.root (Root.r7 q0))))) (Steps.cons (Step.root (Root.r9 x0 q0)) (Steps.refl _)))⟩
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          have e0 := T.s.inj he
          subst x1
          exact ⟨(s (s q1)), (Steps.cons (Step.underS (Step.underS (Step.root (Root.r10 q0 q1)))) (Steps.cons (Step.root (Root.r7 (s q1))) (Steps.refl _))), (Steps.cons (Step.right (m x0 (s (s (s q1)))) (Step.right x0 (Step.right x0 (Step.root (Root.r10 q0 q1))))) (Steps.cons (Step.root (Root.r9 x0 (s (s q1)))) (Steps.cons (Step.root (Root.r7 (s q1))) (Steps.refl _))))⟩
      | @underS _ t2 h2 =>
        exact ⟨(s (s (s t2))), (Steps.cons (Step.underS (Step.underS (Step.underS h2))) (Steps.refl _)), (Steps.cons (Step.right (m x0 (s t2)) (Step.right x0 (Step.right x0 (Step.underS h2)))) (Steps.cons (Step.root (Root.r9 x0 t2)) (Steps.refl _)))⟩
  | @right _ _ t0 h0 =>
    cases h0 with
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
        have cycle := congrArg size e2
        simp only [size] at cycle
        omega
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        have e2 := (T.m.inj e1).1
        have e3 := (T.m.inj e1).2
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
        have e5 := T.s.inj e3
        subst q0
        subst x1
        exact ⟨(s (s (s q1))), (Steps.refl _), (Steps.cons (Step.left (m (s q1) (s (s q1))) (Step.root (Root.r1 (s q1)))) (Steps.cons (Step.root (Root.r6 (s q1) q1)) (Steps.cons (Step.root (Root.r1 (s (s q1)))) (Steps.refl _))))⟩
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
    | @left _ t1 _ h1 =>
      exact ⟨(s (s (s x1))), (Steps.refl _), (Steps.cons (Step.left (m t1 (m x0 (s x1))) (Step.left (s x1) h1)) (Steps.cons (Step.right (m t1 (s x1)) (Step.right t1 (Step.left (s x1) h1))) (Steps.cons (Step.root (Root.r9 t1 x1)) (Steps.refl _))))⟩
    | @right _ _ t1 h1 =>
      cases h1 with
      | root hr =>
        rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩
        · rw [ho]
          have e0 := (T.m.inj he).1
          have e1 := (T.m.inj he).2
          subst x0
          have e2 := e1.symm
          subst q0
          exact ⟨(s (s (s x1))), (Steps.refl _), (Steps.cons (Step.left (m (s x1) (s (s x1))) (Step.root (Root.r1 (s x1)))) (Steps.cons (Step.root (Root.r6 (s x1) x1)) (Steps.cons (Step.root (Root.r1 (s (s x1)))) (Steps.refl _))))⟩
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
      | @left _ t2 _ h2 =>
        exact ⟨(s (s (s x1))), (Steps.refl _), (Steps.cons (Step.left (m x0 (m t2 (s x1))) (Step.left (s x1) h2)) (Steps.cons (Step.right (m t2 (s x1)) (Step.left (m t2 (s x1)) h2)) (Steps.cons (Step.root (Root.r9 t2 x1)) (Steps.refl _))))⟩
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
            subst x1
            exact ⟨(s (s (s q0))), (Steps.cons (Step.root (Root.r7 (s (s q0)))) (Steps.refl _)), (Steps.cons (Step.left (m x0 (m x0 (s q0))) (Step.right x0 (Step.root (Root.r7 q0)))) (Steps.cons (Step.root (Root.r9 x0 q0)) (Steps.refl _)))⟩
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            have e0 := T.s.inj he
            subst x1
            exact ⟨(s (s q1)), (Steps.cons (Step.underS (Step.underS (Step.root (Root.r10 q0 q1)))) (Steps.cons (Step.root (Root.r7 (s q1))) (Steps.refl _))), (Steps.cons (Step.left (m x0 (m x0 (s (s (s q1))))) (Step.right x0 (Step.root (Root.r10 q0 q1)))) (Steps.cons (Step.root (Root.r9 x0 (s (s q1)))) (Steps.cons (Step.root (Root.r7 (s q1))) (Steps.refl _))))⟩
        | @underS _ t3 h3 =>
          exact ⟨(s (s (s t3))), (Steps.cons (Step.underS (Step.underS (Step.underS h3))) (Steps.refl _)), (Steps.cons (Step.left (m x0 (m x0 (s t3))) (Step.right x0 (Step.underS h3))) (Steps.cons (Step.root (Root.r9 x0 t3)) (Steps.refl _)))⟩
end Austin12857

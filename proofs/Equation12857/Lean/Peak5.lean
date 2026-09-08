import Basic
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace Austin12857
open T
theorem peak5 (x0 : T) (x1 : T) (x2 : T) {u : T} (h : Step (m (m x0 (m (s x1) (s x2))) (m x0 (m x0 (m (s x1) (s x2))))) u) : Join (s x1) u := by
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
      have e5 := (T.m.inj e4).1
      have e6 := (T.m.inj e4).2
      subst x0
      cases e6
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
      have e6 := (T.m.inj e3).1
      have e7 := (T.m.inj e3).2
      have e8 := (T.m.inj e5).1
      have e9 := (T.m.inj e5).2
      have e10 := T.s.inj e6
      have e11 := T.s.inj e7
      have e12 := (T.m.inj e9).1
      have e13 := (T.m.inj e9).2
      subst x1
      subst x2
      exact ⟨(s q1), (Steps.refl _), (Steps.refl _)⟩
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
      cases e3
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
        exact ⟨(s x1), (Steps.refl _), (Steps.cons (Step.left (m (m (s x1) (s x2)) (m (m (s x1) (s x2)) (m (s x1) (s x2)))) (Step.root (Root.r10 x1 x2))) (Steps.cons (Step.right (s (s (s x2))) (Step.right (m (s x1) (s x2)) (Step.root (Root.r1 (m (s x1) (s x2)))))) (Steps.cons (Step.right (s (s (s x2))) (Step.right (m (s x1) (s x2)) (Step.root (Root.r10 x1 x2)))) (Steps.cons (Step.root (Root.r8 x2 (s x1))) (Steps.refl _)))))⟩
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
        have e5 := e3.symm
        subst q0
        subst x1
        exact ⟨(s (s (s q1))), (Steps.cons (Step.root (Root.r10 x2 q1)) (Steps.refl _)), (Steps.cons (Step.right (m (s x2) (s q1)) (Step.right (s x2) (Step.root (Root.r3 (s x2) q1)))) (Steps.cons (Step.root (Root.r9 (s x2) q1)) (Steps.refl _)))⟩
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
        subst q0
        cases e3
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        have e2 := (T.m.inj e1).1
        have e3 := (T.m.inj e1).2
        have e4 := T.s.inj e2
        have e5 := T.s.inj e3
        subst x1
        subst x2
        exact ⟨(s q1), (Steps.refl _), (Steps.cons (Step.right (m (s q0) (s (s q1))) (Step.right (s q0) (Step.root (Root.r6 q0 q1)))) (Steps.cons (Step.root (Root.r9 (s q0) (s q1))) (Steps.cons (Step.root (Root.r7 q1)) (Steps.refl _))))⟩
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
        subst q0
        cases e3
      · rw [ho]
        cases he
    | @left _ t1 _ h1 =>
      exact ⟨(s x1), (Steps.refl _), (Steps.cons (Step.right (m t1 (m (s x1) (s x2))) (Step.left (m x0 (m (s x1) (s x2))) h1)) (Steps.cons (Step.right (m t1 (m (s x1) (s x2))) (Step.right t1 (Step.left (m (s x1) (s x2)) h1))) (Steps.cons (Step.root (Root.r5 t1 x1 x2)) (Steps.refl _))))⟩
    | @right _ _ t1 h1 =>
      cases h1 with
      | root hr =>
        rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩
        · rw [ho]
          have e0 := (T.m.inj he).1
          have e1 := (T.m.inj he).2
          have e2 := e0.symm
          subst q0
          have e3 := T.s.inj e1
          subst x2
          exact ⟨(s x1), (Steps.refl _), (Steps.cons (Step.right (m x0 (s (s x1))) (Step.right x0 (Step.right x0 (Step.root (Root.r1 (s x1)))))) (Steps.cons (Step.root (Root.r9 x0 (s x1))) (Steps.cons (Step.root (Root.r7 x1)) (Steps.refl _))))⟩
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
          have e2 := T.s.inj e0
          cases e1
        · rw [ho]
          have e0 := (T.m.inj he).1
          have e1 := (T.m.inj he).2
          cases e0
        · rw [ho]
          have e0 := (T.m.inj he).1
          have e1 := (T.m.inj he).2
          have e2 := T.s.inj e0
          cases e1
        · rw [ho]
          cases he
        · rw [ho]
          have e0 := (T.m.inj he).1
          have e1 := (T.m.inj he).2
          have e2 := T.s.inj e0
          cases e1
        · rw [ho]
          have e0 := (T.m.inj he).1
          have e1 := (T.m.inj he).2
          cases e0
        · rw [ho]
          cases he
      | @left _ t2 _ h2 =>
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
            exact ⟨(s q0), (Steps.cons (Step.root (Root.r7 q0)) (Steps.refl _)), (Steps.cons (Step.right (m x0 (m (s q0) (s x2))) (Step.right x0 (Step.right x0 (Step.left (s x2) (Step.root (Root.r7 q0)))))) (Steps.cons (Step.root (Root.r5 x0 q0 x2)) (Steps.refl _)))⟩
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            have e0 := T.s.inj he
            subst x1
            exact ⟨(s (s (s q1))), (Steps.cons (Step.root (Root.r10 q0 q1)) (Steps.refl _)), (Steps.cons (Step.right (m x0 (m (s (s (s q1))) (s x2))) (Step.right x0 (Step.right x0 (Step.left (s x2) (Step.root (Root.r10 q0 q1)))))) (Steps.cons (Step.root (Root.r5 x0 (s (s q1)) x2)) (Steps.refl _)))⟩
        | @underS _ t3 h3 =>
          exact ⟨(s t3), (Steps.cons (Step.underS h3) (Steps.refl _)), (Steps.cons (Step.right (m x0 (m (s t3) (s x2))) (Step.right x0 (Step.right x0 (Step.left (s x2) (Step.underS h3))))) (Steps.cons (Step.root (Root.r5 x0 t3 x2)) (Steps.refl _)))⟩
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
            subst x2
            exact ⟨(s x1), (Steps.refl _), (Steps.cons (Step.right (m x0 (m (s x1) (s q0))) (Step.right x0 (Step.right x0 (Step.right (s x1) (Step.root (Root.r7 q0)))))) (Steps.cons (Step.root (Root.r5 x0 x1 q0)) (Steps.refl _)))⟩
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            have e0 := T.s.inj he
            subst x2
            exact ⟨(s x1), (Steps.refl _), (Steps.cons (Step.right (m x0 (m (s x1) (s (s (s q1))))) (Step.right x0 (Step.right x0 (Step.right (s x1) (Step.root (Root.r10 q0 q1)))))) (Steps.cons (Step.root (Root.r5 x0 x1 (s (s q1)))) (Steps.refl _)))⟩
        | @underS _ t3 h3 =>
          exact ⟨(s x1), (Steps.refl _), (Steps.cons (Step.right (m x0 (m (s x1) (s t3))) (Step.right x0 (Step.right x0 (Step.right (s x1) (Step.underS h3))))) (Steps.cons (Step.root (Root.r5 x0 x1 t3)) (Steps.refl _)))⟩
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
        cases e3
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
      exact ⟨(s x1), (Steps.refl _), (Steps.cons (Step.left (m t1 (m x0 (m (s x1) (s x2)))) (Step.left (m (s x1) (s x2)) h1)) (Steps.cons (Step.right (m t1 (m (s x1) (s x2))) (Step.right t1 (Step.left (m (s x1) (s x2)) h1))) (Steps.cons (Step.root (Root.r5 t1 x1 x2)) (Steps.refl _))))⟩
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
          exact ⟨(s x1), (Steps.refl _), (Steps.cons (Step.left (m (m (s x1) (s x2)) (s (m (s x1) (s x2)))) (Step.root (Root.r1 (m (s x1) (s x2))))) (Steps.cons (Step.left (m (m (s x1) (s x2)) (s (m (s x1) (s x2)))) (Step.root (Root.r10 x1 x2))) (Steps.cons (Step.right (s (s (s x2))) (Step.right (m (s x1) (s x2)) (Step.root (Root.r10 x1 x2)))) (Steps.cons (Step.root (Root.r8 x2 (s x1))) (Steps.refl _)))))⟩
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
          have e5 := e3.symm
          subst q0
          subst x1
          exact ⟨(s (s (s q1))), (Steps.cons (Step.root (Root.r10 x2 q1)) (Steps.refl _)), (Steps.cons (Step.left (m (s x2) (m (s x2) (s q1))) (Step.root (Root.r3 (s x2) q1))) (Steps.cons (Step.root (Root.r9 (s x2) q1)) (Steps.refl _)))⟩
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
          subst q0
          cases e3
        · rw [ho]
          have e0 := (T.m.inj he).1
          have e1 := (T.m.inj he).2
          subst x0
          have e2 := (T.m.inj e1).1
          have e3 := (T.m.inj e1).2
          have e4 := T.s.inj e2
          have e5 := T.s.inj e3
          subst x1
          subst x2
          exact ⟨(s q1), (Steps.refl _), (Steps.cons (Step.left (m (s q0) (m (s q0) (s (s q1)))) (Step.root (Root.r6 q0 q1))) (Steps.cons (Step.root (Root.r9 (s q0) (s q1))) (Steps.cons (Step.root (Root.r7 q1)) (Steps.refl _))))⟩
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
          subst q0
          cases e3
        · rw [ho]
          cases he
      | @left _ t2 _ h2 =>
        exact ⟨(s x1), (Steps.refl _), (Steps.cons (Step.left (m x0 (m t2 (m (s x1) (s x2)))) (Step.left (m (s x1) (s x2)) h2)) (Steps.cons (Step.right (m t2 (m (s x1) (s x2))) (Step.left (m t2 (m (s x1) (s x2))) h2)) (Steps.cons (Step.root (Root.r5 t2 x1 x2)) (Steps.refl _))))⟩
      | @right _ _ t2 h2 =>
        cases h2 with
        | root hr =>
          rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩
          · rw [ho]
            have e0 := (T.m.inj he).1
            have e1 := (T.m.inj he).2
            have e2 := e0.symm
            subst q0
            have e3 := T.s.inj e1
            subst x2
            exact ⟨(s x1), (Steps.refl _), (Steps.cons (Step.left (m x0 (m x0 (s (s x1)))) (Step.right x0 (Step.root (Root.r1 (s x1))))) (Steps.cons (Step.root (Root.r9 x0 (s x1))) (Steps.cons (Step.root (Root.r7 x1)) (Steps.refl _))))⟩
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
            have e2 := T.s.inj e0
            cases e1
          · rw [ho]
            have e0 := (T.m.inj he).1
            have e1 := (T.m.inj he).2
            cases e0
          · rw [ho]
            have e0 := (T.m.inj he).1
            have e1 := (T.m.inj he).2
            have e2 := T.s.inj e0
            cases e1
          · rw [ho]
            cases he
          · rw [ho]
            have e0 := (T.m.inj he).1
            have e1 := (T.m.inj he).2
            have e2 := T.s.inj e0
            cases e1
          · rw [ho]
            have e0 := (T.m.inj he).1
            have e1 := (T.m.inj he).2
            cases e0
          · rw [ho]
            cases he
        | @left _ t3 _ h3 =>
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
              exact ⟨(s q0), (Steps.cons (Step.root (Root.r7 q0)) (Steps.refl _)), (Steps.cons (Step.left (m x0 (m x0 (m (s q0) (s x2)))) (Step.right x0 (Step.left (s x2) (Step.root (Root.r7 q0))))) (Steps.cons (Step.root (Root.r5 x0 q0 x2)) (Steps.refl _)))⟩
            · rw [ho]
              cases he
            · rw [ho]
              cases he
            · rw [ho]
              have e0 := T.s.inj he
              subst x1
              exact ⟨(s (s (s q1))), (Steps.cons (Step.root (Root.r10 q0 q1)) (Steps.refl _)), (Steps.cons (Step.left (m x0 (m x0 (m (s (s (s q1))) (s x2)))) (Step.right x0 (Step.left (s x2) (Step.root (Root.r10 q0 q1))))) (Steps.cons (Step.root (Root.r5 x0 (s (s q1)) x2)) (Steps.refl _)))⟩
          | @underS _ t4 h4 =>
            exact ⟨(s t4), (Steps.cons (Step.underS h4) (Steps.refl _)), (Steps.cons (Step.left (m x0 (m x0 (m (s t4) (s x2)))) (Step.right x0 (Step.left (s x2) (Step.underS h4)))) (Steps.cons (Step.root (Root.r5 x0 t4 x2)) (Steps.refl _)))⟩
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
              exact ⟨(s x1), (Steps.refl _), (Steps.cons (Step.left (m x0 (m x0 (m (s x1) (s q0)))) (Step.right x0 (Step.right (s x1) (Step.root (Root.r7 q0))))) (Steps.cons (Step.root (Root.r5 x0 x1 q0)) (Steps.refl _)))⟩
            · rw [ho]
              cases he
            · rw [ho]
              cases he
            · rw [ho]
              have e0 := T.s.inj he
              subst x2
              exact ⟨(s x1), (Steps.refl _), (Steps.cons (Step.left (m x0 (m x0 (m (s x1) (s (s (s q1)))))) (Step.right x0 (Step.right (s x1) (Step.root (Root.r10 q0 q1))))) (Steps.cons (Step.root (Root.r5 x0 x1 (s (s q1)))) (Steps.refl _)))⟩
          | @underS _ t4 h4 =>
            exact ⟨(s x1), (Steps.refl _), (Steps.cons (Step.left (m x0 (m x0 (m (s x1) (s t4)))) (Step.right x0 (Step.right (s x1) (Step.underS h4)))) (Steps.cons (Step.root (Root.r5 x0 x1 t4)) (Steps.refl _)))⟩
end Austin12857

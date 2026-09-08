import Basic
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace Austin12857
open T
theorem peak6 (x0 : T) (x1 : T) {u : T} (h : Step (m (s x0) (m (s x1) (s x0))) u) : Join (m (s x0) (s (s x1))) u := by
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
      cases e3
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst q0
      have e3 := (T.m.inj e1).1
      have e4 := (T.m.inj e1).2
      have e5 := T.s.inj e3
      subst x1
      exact ⟨(m (s x0) (s q1)), (Steps.cons (Step.right (s x0) (Step.underS (Step.root (Root.r10 x0 q1)))) (Steps.cons (Step.right (s x0) (Step.root (Root.r7 q1))) (Steps.refl _))), (Steps.refl _)⟩
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := T.s.inj e0
      have e3 := (T.m.inj e1).1
      have e4 := (T.m.inj e1).2
      subst x0
      cases e3
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
      have e5 := T.s.inj e3
      subst x1
      exact ⟨(m (s q0) (s (s q1))), (Steps.refl _), (Steps.refl _)⟩
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := T.s.inj e0
      have e3 := (T.m.inj e1).1
      have e4 := (T.m.inj e1).2
      subst x0
      cases e3
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
        exact ⟨(m (s q0) (s (s x1))), (Steps.cons (Step.left (s (s x1)) (Step.root (Root.r7 q0))) (Steps.refl _)), (Steps.cons (Step.right (s q0) (Step.right (s x1) (Step.root (Root.r7 q0)))) (Steps.cons (Step.root (Root.r6 q0 x1)) (Steps.refl _)))⟩
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := T.s.inj he
        subst x0
        exact ⟨(m (s (s (s q1))) (s (s x1))), (Steps.cons (Step.left (s (s x1)) (Step.root (Root.r10 q0 q1))) (Steps.refl _)), (Steps.cons (Step.right (s (s (s q1))) (Step.right (s x1) (Step.root (Root.r10 q0 q1)))) (Steps.cons (Step.root (Root.r6 (s (s q1)) x1)) (Steps.refl _)))⟩
    | @underS _ t1 h1 =>
      exact ⟨(m (s t1) (s (s x1))), (Steps.cons (Step.left (s (s x1)) (Step.underS h1)) (Steps.refl _)), (Steps.cons (Step.right (s t1) (Step.right (s x1) (Step.underS h1))) (Steps.cons (Step.root (Root.r6 t1 x1)) (Steps.refl _)))⟩
  | @right _ _ t0 h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        have e2 := e0.symm
        subst q0
        have e3 := T.s.inj e1
        subst x0
        exact ⟨(m (s x1) (s (s x1))), (Steps.refl _), (Steps.refl _)⟩
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
          subst x1
          exact ⟨(m (s x0) (s (s q0))), (Steps.cons (Step.right (s x0) (Step.root (Root.r7 (s q0)))) (Steps.refl _)), (Steps.cons (Step.root (Root.r6 x0 q0)) (Steps.refl _))⟩
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          have e0 := T.s.inj he
          subst x1
          exact ⟨(m (s x0) (s q1)), (Steps.cons (Step.right (s x0) (Step.underS (Step.root (Root.r10 q0 q1)))) (Steps.cons (Step.right (s x0) (Step.root (Root.r7 q1))) (Steps.refl _))), (Steps.cons (Step.root (Root.r6 x0 (s (s q1)))) (Steps.cons (Step.right (s x0) (Step.root (Root.r7 q1))) (Steps.refl _)))⟩
      | @underS _ t2 h2 =>
        exact ⟨(m (s x0) (s (s t2))), (Steps.cons (Step.right (s x0) (Step.underS (Step.underS h2))) (Steps.refl _)), (Steps.cons (Step.root (Root.r6 x0 t2)) (Steps.refl _))⟩
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
          exact ⟨(m (s q0) (s (s x1))), (Steps.cons (Step.left (s (s x1)) (Step.root (Root.r7 q0))) (Steps.refl _)), (Steps.cons (Step.left (m (s x1) (s q0)) (Step.root (Root.r7 q0))) (Steps.cons (Step.root (Root.r6 q0 x1)) (Steps.refl _)))⟩
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          have e0 := T.s.inj he
          subst x0
          exact ⟨(m (s (s (s q1))) (s (s x1))), (Steps.cons (Step.left (s (s x1)) (Step.root (Root.r10 q0 q1))) (Steps.refl _)), (Steps.cons (Step.left (m (s x1) (s (s (s q1)))) (Step.root (Root.r10 q0 q1))) (Steps.cons (Step.root (Root.r6 (s (s q1)) x1)) (Steps.refl _)))⟩
      | @underS _ t2 h2 =>
        exact ⟨(m (s t2) (s (s x1))), (Steps.cons (Step.left (s (s x1)) (Step.underS h2)) (Steps.refl _)), (Steps.cons (Step.left (m (s x1) (s t2)) (Step.underS h2)) (Steps.cons (Step.root (Root.r6 t2 x1)) (Steps.refl _)))⟩
end Austin12857

import Basic
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin13992
open T
theorem peak2 (x0 : T) (x1 : T) (x2 : T) {u : T} (h : Step (T.m (T.m x0 (T.r x1 x2)) x2) u) : Join (T.c x0 x1 x2) u := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := (T.m.inj e0).1
      have e3 := (T.m.inj e0).2
      subst x2
      subst x0
      have e4 := e3.symm
      have cycle := congrArg size e4
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := (T.m.inj e0).1
      have e3 := (T.m.inj e0).2
      subst x2
      subst x0
      have e4 := (T.r.inj e3).1
      have e5 := (T.r.inj e3).2
      subst x1
      exact ⟨(T.c q0 q1 q2), (Steps.refl _), (Steps.refl _)⟩
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
      have e2 := e0.symm
      subst q0
      have cycle := congrArg size e1
      simp only [size] at cycle
      omega
    · rw [ho]
      cases he
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
      have e2 := (T.m.inj e0).1
      have e3 := (T.m.inj e0).2
      subst x2
      subst x0
      have e4 := e3.symm
      have cycle := congrArg size e4
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
      cases e0
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst q0
      have cycle := congrArg size e1
      simp only [size] at cycle
      omega
  | @left _ t0 _ h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        have e2 := e1.symm
        subst q1
        exact ⟨(T.c (T.m q0 (T.r x1 x2)) x1 x2), (Steps.refl _), (Steps.cons (Step.root (Root.r8 q0 x1 x2)) (Steps.refl _))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        have e2 := e1.symm
        subst q2
        exact ⟨(T.c (T.m q0 (T.r q1 (T.r x1 x2))) x1 x2), (Steps.refl _), (Steps.cons (Step.root (Root.r11 q0 q1 x1 x2)) (Steps.refl _))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        cases e1
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        have e2 := e1.symm
        subst q1
        exact ⟨(T.c (T.r q0 (T.r x1 x2)) x1 x2), (Steps.refl _), (Steps.cons (Step.root (Root.r8 (T.m q0 (T.r x1 x2)) x1 x2)) (Steps.cons (Step.firstC x1 x2 (Step.root (Root.r1 q0 (T.r x1 x2)))) (Steps.refl _)))⟩
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
        have e2 := e1.symm
        subst q2
        exact ⟨(T.c (T.c q0 q1 (T.r x1 x2)) x1 x2), (Steps.refl _), (Steps.cons (Step.root (Root.r8 (T.m q0 (T.r q1 (T.r x1 x2))) x1 x2)) (Steps.cons (Step.firstC x1 x2 (Step.root (Root.r2 q0 q1 (T.r x1 x2)))) (Steps.refl _)))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        have e2 := e1.symm
        subst q2
        exact ⟨(T.c (T.r q0 (T.r q1 (T.r x1 x2))) x1 x2), (Steps.refl _), (Steps.cons (Step.root (Root.r11 (T.m q0 (T.r q1 (T.r x1 x2))) q1 x1 x2)) (Steps.cons (Step.firstC x1 x2 (Step.root (Root.r1 q0 (T.r q1 (T.r x1 x2))))) (Steps.refl _)))⟩
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
        have e2 := e1.symm
        subst q3
        exact ⟨(T.c (T.c q0 q1 (T.r q2 (T.r x1 x2))) x1 x2), (Steps.refl _), (Steps.cons (Step.root (Root.r11 (T.m q0 (T.r q1 (T.r q2 (T.r x1 x2)))) q2 x1 x2)) (Steps.cons (Step.firstC x1 x2 (Step.root (Root.r2 q0 q1 (T.r q2 (T.r x1 x2))))) (Steps.refl _)))⟩
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
    | @left _ t1 _ h1 =>
      exact ⟨(T.c t1 x1 x2), (Steps.cons (Step.firstC x1 x2 h1) (Steps.refl _)), (Steps.cons (Step.root (Root.r2 t1 x1 x2)) (Steps.refl _))⟩
    | @right _ _ t1 h1 =>
      cases h1 with
      | root hr =>
        rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩
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
          have e0 := (T.r.inj he).1
          have e1 := (T.r.inj he).2
          subst x1
          subst x2
          exact ⟨(T.c x0 q0 (T.c q1 q0 q0)), (Steps.refl _), (Steps.cons (Step.root (Root.r9 x0 q0 q1)) (Steps.refl _))⟩
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
      | @leftR _ t2 _ h2 =>
        exact ⟨(T.c x0 t2 x2), (Steps.cons (Step.secondC x0 x2 h2) (Steps.refl _)), (Steps.cons (Step.root (Root.r2 x0 t2 x2)) (Steps.refl _))⟩
      | @rightR _ _ t2 h2 =>
        exact ⟨(T.c x0 x1 t2), (Steps.cons (Step.thirdC x0 x1 h2) (Steps.refl _)), (Steps.cons (Step.right (T.m x0 (T.r x1 t2)) h2) (Steps.cons (Step.root (Root.r2 x0 x1 t2)) (Steps.refl _)))⟩
  | @right _ _ t0 h0 =>
    exact ⟨(T.c x0 x1 t0), (Steps.cons (Step.thirdC x0 x1 h0) (Steps.refl _)), (Steps.cons (Step.left t0 (Step.right x0 (Step.rightR x1 h0))) (Steps.cons (Step.root (Root.r2 x0 x1 t0)) (Steps.refl _)))⟩
end submission.Austin13992

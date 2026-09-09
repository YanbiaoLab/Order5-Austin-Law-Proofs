import Basic
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin13992
open T
theorem peak11 (x0 : T) (x1 : T) (x2 : T) (x3 : T) {u : T} (h : Step (T.m (T.c x0 x1 (T.r x2 x3)) x3) u) : Join (T.c (T.m x0 (T.r x1 (T.r x2 x3))) x2 x3) u := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩
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
      have e2 := (T.c.inj e0).1
      have e3 := (T.c.inj e0).2.1
      have e4 := (T.c.inj e0).2.2
      subst x3
      subst x0
      subst x1
      have e5 := e4.symm
      have cycle := congrArg size e5
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
      have e2 := (T.c.inj e0).1
      have e3 := (T.c.inj e0).2.1
      have e4 := (T.c.inj e0).2.2
      subst x3
      subst x0
      subst x1
      have e5 := (T.r.inj e4).1
      have e6 := (T.r.inj e4).2
      subst x2
      exact ⟨(T.c (T.m q0 (T.r q1 (T.r q2 q3))) q2 q3), (Steps.refl _), (Steps.refl _)⟩
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := (T.c.inj e0).1
      have e3 := (T.c.inj e0).2.1
      have e4 := (T.c.inj e0).2.2
      subst x3
      subst x0
      subst x1
      have e5 := e4.symm
      have cycle := congrArg size e5
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
  | @left _ t0 _ h0 =>
    cases h0 with
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
    | @firstC _ t1 _ _ h1 =>
      exact ⟨(T.c (T.m t1 (T.r x1 (T.r x2 x3))) x2 x3), (Steps.cons (Step.firstC x2 x3 (Step.left (T.r x1 (T.r x2 x3)) h1)) (Steps.refl _)), (Steps.cons (Step.root (Root.r11 t1 x1 x2 x3)) (Steps.refl _))⟩
    | @secondC _ _ t1 _ h1 =>
      exact ⟨(T.c (T.m x0 (T.r t1 (T.r x2 x3))) x2 x3), (Steps.cons (Step.firstC x2 x3 (Step.right x0 (Step.leftR (T.r x2 x3) h1))) (Steps.refl _)), (Steps.cons (Step.root (Root.r11 x0 t1 x2 x3)) (Steps.refl _))⟩
    | @thirdC _ _ _ t1 h1 =>
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
          subst x2
          subst x3
          exact ⟨(T.c (T.m x0 (T.r x1 q0)) q0 (T.c q1 q0 q0)), (Steps.cons (Step.firstC q0 (T.c q1 q0 q0) (Step.right x0 (Step.rightR x1 (Step.root (Root.r6 q0 q1))))) (Steps.refl _)), (Steps.cons (Step.root (Root.r12 x0 x1 q0 q1)) (Steps.refl _))⟩
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
        exact ⟨(T.c (T.m x0 (T.r x1 (T.r t2 x3))) t2 x3), (Steps.cons (Step.firstC x2 x3 (Step.right x0 (Step.rightR x1 (Step.leftR x3 h2)))) (Steps.cons (Step.secondC (T.m x0 (T.r x1 (T.r t2 x3))) x3 h2) (Steps.refl _))), (Steps.cons (Step.root (Root.r11 x0 x1 t2 x3)) (Steps.refl _))⟩
      | @rightR _ _ t2 h2 =>
        exact ⟨(T.c (T.m x0 (T.r x1 (T.r x2 t2))) x2 t2), (Steps.cons (Step.firstC x2 x3 (Step.right x0 (Step.rightR x1 (Step.rightR x2 h2)))) (Steps.cons (Step.thirdC (T.m x0 (T.r x1 (T.r x2 t2))) x2 h2) (Steps.refl _))), (Steps.cons (Step.right (T.c x0 x1 (T.r x2 t2)) h2) (Steps.cons (Step.root (Root.r11 x0 x1 x2 t2)) (Steps.refl _)))⟩
  | @right _ _ t0 h0 =>
    exact ⟨(T.c (T.m x0 (T.r x1 (T.r x2 t0))) x2 t0), (Steps.cons (Step.firstC x2 x3 (Step.right x0 (Step.rightR x1 (Step.rightR x2 h0)))) (Steps.cons (Step.thirdC (T.m x0 (T.r x1 (T.r x2 t0))) x2 h0) (Steps.refl _))), (Steps.cons (Step.left t0 (Step.thirdC x0 x1 (Step.rightR x2 h0))) (Steps.cons (Step.root (Root.r11 x0 x1 x2 t0)) (Steps.refl _)))⟩
end submission.Austin13992

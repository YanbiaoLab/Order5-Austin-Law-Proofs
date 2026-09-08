import Basic
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin13849
open T
theorem peak7 (x0 : T) (x1 : T) (x2 : T) {u : T} (h : Step (T.m (T.c x0 x1 x2) x2) u) : Join (T.r (T.m x0 (T.r x1 x2)) x2) u := by
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
      subst x2
      subst x0
      subst x1
      exact ⟨(T.r (T.m q0 (T.r q1 q2)) q2), (Steps.refl _), (Steps.refl _)⟩
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
      subst x2
      subst x0
      subst x1
      have cycle := congrArg size e4
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := (T.c.inj e0).1
      have e3 := (T.c.inj e0).2.1
      have e4 := (T.c.inj e0).2.2
      subst x2
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
      exact ⟨(T.r (T.m t1 (T.r x1 x2)) x2), (Steps.cons (Step.leftR x2 (Step.left (T.r x1 x2) h1)) (Steps.refl _)), (Steps.cons (Step.root (Root.r7 t1 x1 x2)) (Steps.refl _))⟩
    | @secondC _ _ t1 _ h1 =>
      exact ⟨(T.r (T.m x0 (T.r t1 x2)) x2), (Steps.cons (Step.leftR x2 (Step.right x0 (Step.leftR x2 h1))) (Steps.refl _)), (Steps.cons (Step.root (Root.r7 x0 t1 x2)) (Steps.refl _))⟩
    | @thirdC _ _ _ t1 h1 =>
      exact ⟨(T.r (T.m x0 (T.r x1 t1)) t1), (Steps.cons (Step.leftR x2 (Step.right x0 (Step.rightR x1 h1))) (Steps.cons (Step.rightR (T.m x0 (T.r x1 t1)) h1) (Steps.refl _))), (Steps.cons (Step.right (T.c x0 x1 t1) h1) (Steps.cons (Step.root (Root.r7 x0 x1 t1)) (Steps.refl _)))⟩
  | @right _ _ t0 h0 =>
    exact ⟨(T.r (T.m x0 (T.r x1 t0)) t0), (Steps.cons (Step.leftR x2 (Step.right x0 (Step.rightR x1 h0))) (Steps.cons (Step.rightR (T.m x0 (T.r x1 t0)) h0) (Steps.refl _))), (Steps.cons (Step.left t0 (Step.thirdC x0 x1 h0)) (Steps.cons (Step.root (Root.r7 x0 x1 t0)) (Steps.refl _)))⟩
end submission.Austin13849

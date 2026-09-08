import Basic
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak5 (x0 : T) (x1 : T) {u : T} (h : Step (T.m (T.r x0 x1) x0) u) : Join (T.r x0 (T.m x1 x0)) u := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
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
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      subst e1
      exact ⟨(T.c (T.c (T.c x1 q1 q2) q1 q2) q1 q2), (Steps.cons (Step.root (Root.r7 q1 q2 (T.m x1 (T.d q1 q2)))) (Steps.cons (Step.firstC q1 q2 (Step.firstC q1 q2 (Step.root (Root.r3 x1 q1 q2)))) (Steps.refl _))), (Steps.cons (Step.firstC q1 q2 (Step.root (Root.r7 q1 q2 x1))) (Steps.refl _))⟩
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
      have e2 := (T.r.inj e0).1
      have e3 := (T.r.inj e0).2
      have e4 := e1.symm
      subst e4
      have e5 := e3.symm
      subst e5
      exact ⟨(T.r q0 (T.m q1 q0)), (Steps.refl _), (Steps.refl _)⟩
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      cases e0
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
      cases he
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
      have e2 := e0.symm
      subst e2
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
      cases e0
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      cases e0
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      cases e0
  | @left _ t0 _ h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
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
        have e0 := (T.r.inj he).1
        have e1 := (T.r.inj he).2
        subst e0
        have e2 := e1.symm
        subst e2
        exact ⟨(T.c (T.c (T.c q2 q0 q1) q0 q1) q0 q1), (Steps.cons (Step.root (Root.r7 q0 q1 (T.m q2 (T.d q0 q1)))) (Steps.cons (Step.firstC q0 q1 (Step.firstC q0 q1 (Step.root (Root.r3 q2 q0 q1)))) (Steps.refl _))), (Steps.cons (Step.root (Root.r3 (T.c (T.c q2 q0 q1) q0 q1) q0 q1)) (Steps.refl _))⟩
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.r.inj he).1
        have e1 := (T.r.inj he).2
        subst e0
        have e2 := e1.symm
        subst e2
        exact ⟨q0, (Steps.cons (Step.rightR (T.c q0 q0 q1) (Step.root (Root.r4 q0 q0 q1))) (Steps.cons (Step.root (Root.r9 q0 q1)) (Steps.refl _))), (Steps.cons (Step.root (Root.r4 q0 q0 q1)) (Steps.refl _))⟩
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
    | @leftR _ t1 _ h1 =>
      exact ⟨(T.r t1 (T.m x1 t1)), (Steps.cons (Step.leftR (T.m x1 x0) h1) (Steps.cons (Step.rightR t1 (Step.right x1 h1)) (Steps.refl _))), (Steps.cons (Step.right (T.r t1 x1) h1) (Steps.cons (Step.root (Root.r5 t1 x1)) (Steps.refl _)))⟩
    | @rightR _ _ t1 h1 =>
      exact ⟨(T.r x0 (T.m t1 x0)), (Steps.cons (Step.rightR x0 (Step.left x0 h1)) (Steps.refl _)), (Steps.cons (Step.root (Root.r5 x0 t1)) (Steps.refl _))⟩
  | @right _ _ t0 h0 =>
    exact ⟨(T.r t0 (T.m x1 t0)), (Steps.cons (Step.leftR (T.m x1 x0) h0) (Steps.cons (Step.rightR t0 (Step.right x1 h0)) (Steps.refl _))), (Steps.cons (Step.left t0 (Step.leftR x1 h0)) (Steps.cons (Step.root (Root.r5 t0 x1)) (Steps.refl _)))⟩
end submission.Austin5837

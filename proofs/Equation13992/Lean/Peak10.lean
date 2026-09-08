import Basic
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin13992
open T
theorem peak10 (x0 : T) (x1 : T) (x2 : T) {u : T} (h : Step (T.m (T.r x0 x1) (T.c x2 x1 x1)) u) : Join (T.c (T.m x0 x1) x1 (T.c x2 x1 x1)) u := by
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
      have e3 := (T.c.inj e1).1
      have e4 := (T.c.inj e1).2.1
      have e5 := (T.c.inj e1).2.2
      subst x2
      subst x1
      have cycle := congrArg size e5
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := (T.r.inj e0).1
      have e3 := (T.r.inj e0).2
      have e4 := e1.symm
      subst q1
      subst x0
      have cycle := congrArg size e3
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst q0
      have e3 := (T.c.inj e1).1
      have e4 := (T.c.inj e1).2.1
      have e5 := (T.c.inj e1).2.2
      subst x2
      have cycle := congrArg size e4
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
      have e2 := (T.r.inj e0).1
      have e3 := (T.r.inj e0).2
      have e4 := e1.symm
      subst q2
      subst x0
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
      have e2 := (T.r.inj e0).1
      have e3 := (T.r.inj e0).2
      have e4 := (T.c.inj e1).1
      have e5 := (T.c.inj e1).2.1
      have e6 := (T.c.inj e1).2.2
      subst x0
      subst x1
      subst x2
      exact ⟨(T.c (T.m q0 q1) q1 (T.c q2 q1 q1)), (Steps.refl _), (Steps.refl _)⟩
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
      have e3 := (T.c.inj e1).1
      have e4 := (T.c.inj e1).2.1
      have e5 := (T.c.inj e1).2.2
      subst x2
      have cycle := congrArg size e4
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
        have e0 := (T.r.inj he).1
        have e1 := (T.r.inj he).2
        subst x0
        subst x1
        exact ⟨(T.c q0 (T.c q1 q0 q0) (T.c x2 (T.c q1 q0 q0) (T.c q1 q0 q0))), (Steps.cons (Step.firstC (T.c q1 q0 q0) (T.c x2 (T.c q1 q0 q0) (T.c q1 q0 q0)) (Step.root (Root.r3 q0 q1 q0))) (Steps.refl _)), (Steps.cons (Step.root (Root.r13 q0 x2 q1 q0)) (Steps.refl _))⟩
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
      exact ⟨(T.c (T.m t1 x1) x1 (T.c x2 x1 x1)), (Steps.cons (Step.firstC x1 (T.c x2 x1 x1) (Step.left x1 h1)) (Steps.refl _)), (Steps.cons (Step.root (Root.r10 t1 x1 x2)) (Steps.refl _))⟩
    | @rightR _ _ t1 h1 =>
      exact ⟨(T.c (T.m x0 t1) t1 (T.c x2 t1 t1)), (Steps.cons (Step.firstC x1 (T.c x2 x1 x1) (Step.right x0 h1)) (Steps.cons (Step.secondC (T.m x0 t1) (T.c x2 x1 x1) h1) (Steps.cons (Step.thirdC (T.m x0 t1) t1 (Step.secondC x2 x1 h1)) (Steps.cons (Step.thirdC (T.m x0 t1) t1 (Step.thirdC x2 t1 h1)) (Steps.refl _))))), (Steps.cons (Step.right (T.r x0 t1) (Step.secondC x2 x1 h1)) (Steps.cons (Step.right (T.r x0 t1) (Step.thirdC x2 t1 h1)) (Steps.cons (Step.root (Root.r10 x0 t1 x2)) (Steps.refl _))))⟩
  | @right _ _ t0 h0 =>
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
      exact ⟨(T.c (T.m x0 x1) x1 (T.c t1 x1 x1)), (Steps.cons (Step.thirdC (T.m x0 x1) x1 (Step.firstC x1 x1 h1)) (Steps.refl _)), (Steps.cons (Step.root (Root.r10 x0 x1 t1)) (Steps.refl _))⟩
    | @secondC _ _ t1 _ h1 =>
      exact ⟨(T.c (T.m x0 t1) t1 (T.c x2 t1 t1)), (Steps.cons (Step.firstC x1 (T.c x2 x1 x1) (Step.right x0 h1)) (Steps.cons (Step.secondC (T.m x0 t1) (T.c x2 x1 x1) h1) (Steps.cons (Step.thirdC (T.m x0 t1) t1 (Step.secondC x2 x1 h1)) (Steps.cons (Step.thirdC (T.m x0 t1) t1 (Step.thirdC x2 t1 h1)) (Steps.refl _))))), (Steps.cons (Step.left (T.c x2 t1 x1) (Step.rightR x0 h1)) (Steps.cons (Step.right (T.r x0 t1) (Step.thirdC x2 t1 h1)) (Steps.cons (Step.root (Root.r10 x0 t1 x2)) (Steps.refl _))))⟩
    | @thirdC _ _ _ t1 h1 =>
      exact ⟨(T.c (T.m x0 t1) t1 (T.c x2 t1 t1)), (Steps.cons (Step.firstC x1 (T.c x2 x1 x1) (Step.right x0 h1)) (Steps.cons (Step.secondC (T.m x0 t1) (T.c x2 x1 x1) h1) (Steps.cons (Step.thirdC (T.m x0 t1) t1 (Step.secondC x2 x1 h1)) (Steps.cons (Step.thirdC (T.m x0 t1) t1 (Step.thirdC x2 t1 h1)) (Steps.refl _))))), (Steps.cons (Step.left (T.c x2 x1 t1) (Step.rightR x0 h1)) (Steps.cons (Step.right (T.r x0 t1) (Step.secondC x2 t1 h1)) (Steps.cons (Step.root (Root.r10 x0 t1 x2)) (Steps.refl _))))⟩
end submission.Austin13992

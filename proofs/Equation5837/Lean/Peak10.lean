import Basic
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak10 (x0 : T) (x1 : T) {u : T} (h : Step (T.m (T.c x0 x0 x1) x0) u) : Join (T.d (T.c x0 x0 x1) x0) u := by
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
      exact ⟨(T.d (T.c (T.d q1 q2) (T.d q1 q2) x1) (T.d q1 q2)), (Steps.refl _), (Steps.cons (Step.root (Root.r13 q1 q2 x1)) (Steps.refl _))⟩
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
      have e2 := (T.c.inj e0).1
      have e3 := (T.c.inj e0).2.1
      have e4 := (T.c.inj e0).2.2
      have e5 := e1.symm
      subst e5
      have e6 := e4.symm
      subst e6
      exact ⟨(T.d (T.c q0 q0 q1) q0), (Steps.refl _), (Steps.refl _)⟩
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
      have e2 := (T.c.inj e0).1
      have e3 := (T.c.inj e0).2.1
      have e4 := (T.c.inj e0).2.2
      subst e1
      cases e2
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
        have e0 := (T.c.inj he).1
        have e1 := (T.c.inj he).2.1
        have e2 := (T.c.inj he).2.2
        subst e0
        have e3 := e1.symm
        have cycle := congrArg size e3
        simp only [size] at cycle
        omega
      · rw [ho]
        have e0 := (T.c.inj he).1
        have e1 := (T.c.inj he).2.1
        have e2 := (T.c.inj he).2.2
        have e3 := e0.symm
        subst e3
        have cycle := congrArg size e1
        simp only [size] at cycle
        omega
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
      exact ⟨(T.d (T.c t1 t1 x1) t1), (Steps.cons (Step.leftD x0 (Step.firstC x0 x1 h1)) (Steps.cons (Step.leftD x0 (Step.secondC t1 x1 h1)) (Steps.cons (Step.rightD (T.c t1 t1 x1) h1) (Steps.refl _)))), (Steps.cons (Step.left x0 (Step.secondC t1 x1 h1)) (Steps.cons (Step.right (T.c t1 t1 x1) h1) (Steps.cons (Step.root (Root.r10 t1 x1)) (Steps.refl _))))⟩
    | @secondC _ _ t1 _ h1 =>
      exact ⟨(T.d (T.c t1 t1 x1) t1), (Steps.cons (Step.leftD x0 (Step.firstC x0 x1 h1)) (Steps.cons (Step.leftD x0 (Step.secondC t1 x1 h1)) (Steps.cons (Step.rightD (T.c t1 t1 x1) h1) (Steps.refl _)))), (Steps.cons (Step.left x0 (Step.firstC t1 x1 h1)) (Steps.cons (Step.right (T.c t1 t1 x1) h1) (Steps.cons (Step.root (Root.r10 t1 x1)) (Steps.refl _))))⟩
    | @thirdC _ _ _ t1 h1 =>
      exact ⟨(T.d (T.c x0 x0 t1) x0), (Steps.cons (Step.leftD x0 (Step.thirdC x0 x0 h1)) (Steps.refl _)), (Steps.cons (Step.root (Root.r10 x0 t1)) (Steps.refl _))⟩
  | @right _ _ t0 h0 =>
    exact ⟨(T.d (T.c t0 t0 x1) t0), (Steps.cons (Step.leftD x0 (Step.firstC x0 x1 h0)) (Steps.cons (Step.leftD x0 (Step.secondC t0 x1 h0)) (Steps.cons (Step.rightD (T.c t0 t0 x1) h0) (Steps.refl _)))), (Steps.cons (Step.left t0 (Step.firstC x0 x1 h0)) (Steps.cons (Step.left t0 (Step.secondC t0 x1 h0)) (Steps.cons (Step.root (Root.r10 t0 x1)) (Steps.refl _))))⟩
end submission.Austin5837

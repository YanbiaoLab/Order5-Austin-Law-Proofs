import Basic
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin13992
open T
theorem peak13 (x0 : T) (x1 : T) (x2 : T) (x3 : T) {u : T} (h : Step (T.m x0 (T.c x1 (T.c x2 x0 x3) (T.c x2 x0 x3))) u) : Join (T.c x3 (T.c x2 x0 x3) (T.c x1 (T.c x2 x0 x3) (T.c x2 x0 x3))) u := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩
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
      have e2 := e1.symm
      have cycle := congrArg size e2
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst x0
      have e2 := (T.c.inj e1).1
      have e3 := (T.c.inj e1).2.1
      have e4 := (T.c.inj e1).2.2
      subst x1
      have e5 := e3.symm
      subst q2
      have e6 := e4.symm
      have cycle := congrArg size e6
      simp only [size] at cycle
      omega
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
      have e2 := (T.c.inj e1).1
      have e3 := (T.c.inj e1).2.1
      have e4 := (T.c.inj e1).2.2
      subst x1
      have e5 := e3.symm
      have cycle := congrArg size e5
      simp only [size] at cycle
      omega
    · rw [ho]
      cases he
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
      have e2 := e1.symm
      have cycle := congrArg size e2
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst x0
      have e2 := (T.c.inj e1).1
      have e3 := (T.c.inj e1).2.1
      have e4 := (T.c.inj e1).2.2
      subst x1
      have e5 := e3.symm
      have cycle := congrArg size e5
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst x0
      have e2 := (T.c.inj e1).1
      have e3 := (T.c.inj e1).2.1
      have e4 := (T.c.inj e1).2.2
      subst x1
      have e5 := e3.symm
      have cycle := congrArg size e5
      simp only [size] at cycle
      omega
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
      have e2 := (T.c.inj e1).1
      have e3 := (T.c.inj e1).2.1
      have e4 := (T.c.inj e1).2.2
      subst x1
      have e5 := e3.symm
      have cycle := congrArg size e5
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst x0
      have e2 := (T.c.inj e1).1
      have e3 := (T.c.inj e1).2.1
      have e4 := (T.c.inj e1).2.2
      subst x1
      have e5 := (T.c.inj e3).1
      have e6 := (T.c.inj e3).2.1
      have e7 := (T.c.inj e3).2.2
      have e8 := (T.c.inj e4).1
      have e9 := (T.c.inj e4).2.1
      have e10 := (T.c.inj e4).2.2
      subst x2
      subst x3
      exact ⟨(T.c q3 (T.c q2 q0 q3) (T.c q1 (T.c q2 q0 q3) (T.c q2 q0 q3))), (Steps.refl _), (Steps.refl _)⟩
  | @left _ t0 _ h0 =>
    exact ⟨(T.c x3 (T.c x2 t0 x3) (T.c x1 (T.c x2 t0 x3) (T.c x2 t0 x3))), (Steps.cons (Step.secondC x3 (T.c x1 (T.c x2 x0 x3) (T.c x2 x0 x3)) (Step.secondC x2 x3 h0)) (Steps.cons (Step.thirdC x3 (T.c x2 t0 x3) (Step.secondC x1 (T.c x2 x0 x3) (Step.secondC x2 x3 h0))) (Steps.cons (Step.thirdC x3 (T.c x2 t0 x3) (Step.thirdC x1 (T.c x2 t0 x3) (Step.secondC x2 x3 h0))) (Steps.refl _)))), (Steps.cons (Step.right t0 (Step.secondC x1 (T.c x2 x0 x3) (Step.secondC x2 x3 h0))) (Steps.cons (Step.right t0 (Step.thirdC x1 (T.c x2 t0 x3) (Step.secondC x2 x3 h0))) (Steps.cons (Step.root (Root.r13 t0 x1 x2 x3)) (Steps.refl _))))⟩
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
      exact ⟨(T.c x3 (T.c x2 x0 x3) (T.c t1 (T.c x2 x0 x3) (T.c x2 x0 x3))), (Steps.cons (Step.thirdC x3 (T.c x2 x0 x3) (Step.firstC (T.c x2 x0 x3) (T.c x2 x0 x3) h1)) (Steps.refl _)), (Steps.cons (Step.root (Root.r13 x0 t1 x2 x3)) (Steps.refl _))⟩
    | @secondC _ _ t1 _ h1 =>
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
      | @firstC _ t2 _ _ h2 =>
        exact ⟨(T.c x3 (T.c t2 x0 x3) (T.c x1 (T.c t2 x0 x3) (T.c t2 x0 x3))), (Steps.cons (Step.secondC x3 (T.c x1 (T.c x2 x0 x3) (T.c x2 x0 x3)) (Step.firstC x0 x3 h2)) (Steps.cons (Step.thirdC x3 (T.c t2 x0 x3) (Step.secondC x1 (T.c x2 x0 x3) (Step.firstC x0 x3 h2))) (Steps.cons (Step.thirdC x3 (T.c t2 x0 x3) (Step.thirdC x1 (T.c t2 x0 x3) (Step.firstC x0 x3 h2))) (Steps.refl _)))), (Steps.cons (Step.right x0 (Step.thirdC x1 (T.c t2 x0 x3) (Step.firstC x0 x3 h2))) (Steps.cons (Step.root (Root.r13 x0 x1 t2 x3)) (Steps.refl _)))⟩
      | @secondC _ _ t2 _ h2 =>
        exact ⟨(T.c x3 (T.c x2 t2 x3) (T.c x1 (T.c x2 t2 x3) (T.c x2 t2 x3))), (Steps.cons (Step.secondC x3 (T.c x1 (T.c x2 x0 x3) (T.c x2 x0 x3)) (Step.secondC x2 x3 h2)) (Steps.cons (Step.thirdC x3 (T.c x2 t2 x3) (Step.secondC x1 (T.c x2 x0 x3) (Step.secondC x2 x3 h2))) (Steps.cons (Step.thirdC x3 (T.c x2 t2 x3) (Step.thirdC x1 (T.c x2 t2 x3) (Step.secondC x2 x3 h2))) (Steps.refl _)))), (Steps.cons (Step.left (T.c x1 (T.c x2 t2 x3) (T.c x2 x0 x3)) h2) (Steps.cons (Step.right t2 (Step.thirdC x1 (T.c x2 t2 x3) (Step.secondC x2 x3 h2))) (Steps.cons (Step.root (Root.r13 t2 x1 x2 x3)) (Steps.refl _))))⟩
      | @thirdC _ _ _ t2 h2 =>
        exact ⟨(T.c t2 (T.c x2 x0 t2) (T.c x1 (T.c x2 x0 t2) (T.c x2 x0 t2))), (Steps.cons (Step.firstC (T.c x2 x0 x3) (T.c x1 (T.c x2 x0 x3) (T.c x2 x0 x3)) h2) (Steps.cons (Step.secondC t2 (T.c x1 (T.c x2 x0 x3) (T.c x2 x0 x3)) (Step.thirdC x2 x0 h2)) (Steps.cons (Step.thirdC t2 (T.c x2 x0 t2) (Step.secondC x1 (T.c x2 x0 x3) (Step.thirdC x2 x0 h2))) (Steps.cons (Step.thirdC t2 (T.c x2 x0 t2) (Step.thirdC x1 (T.c x2 x0 t2) (Step.thirdC x2 x0 h2))) (Steps.refl _))))), (Steps.cons (Step.right x0 (Step.thirdC x1 (T.c x2 x0 t2) (Step.thirdC x2 x0 h2))) (Steps.cons (Step.root (Root.r13 x0 x1 x2 t2)) (Steps.refl _)))⟩
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
      | @firstC _ t2 _ _ h2 =>
        exact ⟨(T.c x3 (T.c t2 x0 x3) (T.c x1 (T.c t2 x0 x3) (T.c t2 x0 x3))), (Steps.cons (Step.secondC x3 (T.c x1 (T.c x2 x0 x3) (T.c x2 x0 x3)) (Step.firstC x0 x3 h2)) (Steps.cons (Step.thirdC x3 (T.c t2 x0 x3) (Step.secondC x1 (T.c x2 x0 x3) (Step.firstC x0 x3 h2))) (Steps.cons (Step.thirdC x3 (T.c t2 x0 x3) (Step.thirdC x1 (T.c t2 x0 x3) (Step.firstC x0 x3 h2))) (Steps.refl _)))), (Steps.cons (Step.right x0 (Step.secondC x1 (T.c t2 x0 x3) (Step.firstC x0 x3 h2))) (Steps.cons (Step.root (Root.r13 x0 x1 t2 x3)) (Steps.refl _)))⟩
      | @secondC _ _ t2 _ h2 =>
        exact ⟨(T.c x3 (T.c x2 t2 x3) (T.c x1 (T.c x2 t2 x3) (T.c x2 t2 x3))), (Steps.cons (Step.secondC x3 (T.c x1 (T.c x2 x0 x3) (T.c x2 x0 x3)) (Step.secondC x2 x3 h2)) (Steps.cons (Step.thirdC x3 (T.c x2 t2 x3) (Step.secondC x1 (T.c x2 x0 x3) (Step.secondC x2 x3 h2))) (Steps.cons (Step.thirdC x3 (T.c x2 t2 x3) (Step.thirdC x1 (T.c x2 t2 x3) (Step.secondC x2 x3 h2))) (Steps.refl _)))), (Steps.cons (Step.left (T.c x1 (T.c x2 x0 x3) (T.c x2 t2 x3)) h2) (Steps.cons (Step.right t2 (Step.secondC x1 (T.c x2 t2 x3) (Step.secondC x2 x3 h2))) (Steps.cons (Step.root (Root.r13 t2 x1 x2 x3)) (Steps.refl _))))⟩
      | @thirdC _ _ _ t2 h2 =>
        exact ⟨(T.c t2 (T.c x2 x0 t2) (T.c x1 (T.c x2 x0 t2) (T.c x2 x0 t2))), (Steps.cons (Step.firstC (T.c x2 x0 x3) (T.c x1 (T.c x2 x0 x3) (T.c x2 x0 x3)) h2) (Steps.cons (Step.secondC t2 (T.c x1 (T.c x2 x0 x3) (T.c x2 x0 x3)) (Step.thirdC x2 x0 h2)) (Steps.cons (Step.thirdC t2 (T.c x2 x0 t2) (Step.secondC x1 (T.c x2 x0 x3) (Step.thirdC x2 x0 h2))) (Steps.cons (Step.thirdC t2 (T.c x2 x0 t2) (Step.thirdC x1 (T.c x2 x0 t2) (Step.thirdC x2 x0 h2))) (Steps.refl _))))), (Steps.cons (Step.right x0 (Step.secondC x1 (T.c x2 x0 t2) (Step.thirdC x2 x0 h2))) (Steps.cons (Step.root (Root.r13 x0 x1 x2 t2)) (Steps.refl _)))⟩
end submission.Austin13992

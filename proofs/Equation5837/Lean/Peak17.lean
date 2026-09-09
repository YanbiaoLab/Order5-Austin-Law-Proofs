import Basic
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak17 (x0 : T) (x1 : T) (x2 : T) {u : T} (h : Step (T.m x0 (T.c (T.d x0 x1) (T.d x0 x1) x2)) u) : Join (T.r (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2)) u := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
      have e2 := e1.symm
      have cycle := congrArg size e2
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      cases e1
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      cases e1
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      have e3 := (T.c.inj e1).1
      have e4 := (T.c.inj e1).2.1
      have e5 := (T.c.inj e1).2.2
      have e6 := e3.symm
      subst e6
      have e7 := e4.symm
      have cycle := congrArg size e7
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
      have e2 := e1.symm
      have cycle := congrArg size e2
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
      cases e1
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      have e3 := (T.c.inj e1).1
      have e4 := (T.c.inj e1).2.1
      have e5 := (T.c.inj e1).2.2
      have e6 := e3.symm
      have cycle := congrArg size e6
      simp only [size] at cycle
      omega
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
      have e2 := e1.symm
      have cycle := congrArg size e2
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
      have e2 := e1.symm
      have cycle := congrArg size e2
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
      have e2 := (T.c.inj e1).1
      have e3 := (T.c.inj e1).2.1
      have e4 := (T.c.inj e1).2.2
      cases e2
    · rw [ho]
      cases he
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
      have e2 := (T.c.inj e1).1
      have e3 := (T.c.inj e1).2.1
      have e4 := (T.c.inj e1).2.2
      have e5 := (T.d.inj e2).1
      have e6 := (T.d.inj e2).2
      have e7 := (T.d.inj e3).1
      have e8 := (T.d.inj e3).2
      have e9 := e4.symm
      subst e9
      have e10 := e5.symm
      have cycle := congrArg size e10
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
      have e2 := (T.c.inj e1).1
      have e3 := (T.c.inj e1).2.1
      have e4 := (T.c.inj e1).2.2
      cases e2
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      have e3 := (T.c.inj e1).1
      have e4 := (T.c.inj e1).2.1
      have e5 := (T.c.inj e1).2.2
      have e6 := (T.d.inj e3).1
      have e7 := (T.d.inj e3).2
      have e8 := (T.d.inj e4).1
      have e9 := (T.d.inj e4).2
      have e10 := e5.symm
      subst e10
      have e11 := e7.symm
      subst e11
      exact ⟨(T.r (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2)), (Steps.refl _), (Steps.refl _)⟩
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
      have e2 := (T.c.inj e1).1
      have e3 := (T.c.inj e1).2.1
      have e4 := (T.c.inj e1).2.2
      have e5 := (T.d.inj e2).1
      have e6 := (T.d.inj e2).2
      have e7 := e3.symm
      have cycle := congrArg size e7
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
      have e2 := (T.c.inj e1).1
      have e3 := (T.c.inj e1).2.1
      have e4 := (T.c.inj e1).2.2
      have e5 := (T.d.inj e2).1
      have e6 := (T.d.inj e2).2
      have e7 := e3.symm
      have cycle := congrArg size e7
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
      have e2 := (T.c.inj e1).1
      have e3 := (T.c.inj e1).2.1
      have e4 := (T.c.inj e1).2.2
      cases e2
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
      have e2 := (T.c.inj e1).1
      have e3 := (T.c.inj e1).2.1
      have e4 := (T.c.inj e1).2.2
      cases e2
  | @left _ t0 _ h0 =>
    exact ⟨(T.r (T.c (T.d t0 x1) (T.d t0 x1) x2) (T.c (T.d t0 x1) (T.d t0 x1) x2)), (Steps.cons (Step.leftR (T.c (T.d x0 x1) (T.d x0 x1) x2) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h0))) (Steps.cons (Step.leftR (T.c (T.d x0 x1) (T.d x0 x1) x2) (Step.secondC (T.d t0 x1) x2 (Step.leftD x1 h0))) (Steps.cons (Step.rightR (T.c (T.d t0 x1) (T.d t0 x1) x2) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h0))) (Steps.cons (Step.rightR (T.c (T.d t0 x1) (T.d t0 x1) x2) (Step.secondC (T.d t0 x1) x2 (Step.leftD x1 h0))) (Steps.refl _))))), (Steps.cons (Step.right t0 (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h0))) (Steps.cons (Step.right t0 (Step.secondC (T.d t0 x1) x2 (Step.leftD x1 h0))) (Steps.cons (Step.root (Root.r17 t0 x1 x2)) (Steps.refl _))))⟩
  | @right _ _ t0 h0 =>
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
        cases e0
      · rw [ho]
        have e0 := (T.c.inj he).1
        have e1 := (T.c.inj he).2.1
        have e2 := (T.c.inj he).2.2
        have e3 := e0.symm
        subst e3
        cases e1
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
      cases h1 with
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
      | @leftD _ t2 _ h2 =>
        exact ⟨(T.r (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.c (T.d t2 x1) (T.d t2 x1) x2)), (Steps.cons (Step.leftR (T.c (T.d x0 x1) (T.d x0 x1) x2) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h2))) (Steps.cons (Step.leftR (T.c (T.d x0 x1) (T.d x0 x1) x2) (Step.secondC (T.d t2 x1) x2 (Step.leftD x1 h2))) (Steps.cons (Step.rightR (T.c (T.d t2 x1) (T.d t2 x1) x2) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h2))) (Steps.cons (Step.rightR (T.c (T.d t2 x1) (T.d t2 x1) x2) (Step.secondC (T.d t2 x1) x2 (Step.leftD x1 h2))) (Steps.refl _))))), (Steps.cons (Step.left (T.c (T.d t2 x1) (T.d x0 x1) x2) h2) (Steps.cons (Step.right t2 (Step.secondC (T.d t2 x1) x2 (Step.leftD x1 h2))) (Steps.cons (Step.root (Root.r17 t2 x1 x2)) (Steps.refl _))))⟩
      | @rightD _ _ t2 h2 =>
        exact ⟨(T.r (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.c (T.d x0 t2) (T.d x0 t2) x2)), (Steps.cons (Step.leftR (T.c (T.d x0 x1) (T.d x0 x1) x2) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h2))) (Steps.cons (Step.leftR (T.c (T.d x0 x1) (T.d x0 x1) x2) (Step.secondC (T.d x0 t2) x2 (Step.rightD x0 h2))) (Steps.cons (Step.rightR (T.c (T.d x0 t2) (T.d x0 t2) x2) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h2))) (Steps.cons (Step.rightR (T.c (T.d x0 t2) (T.d x0 t2) x2) (Step.secondC (T.d x0 t2) x2 (Step.rightD x0 h2))) (Steps.refl _))))), (Steps.cons (Step.right x0 (Step.secondC (T.d x0 t2) x2 (Step.rightD x0 h2))) (Steps.cons (Step.root (Root.r17 x0 t2 x2)) (Steps.refl _)))⟩
    | @secondC _ _ t1 _ h1 =>
      cases h1 with
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
      | @leftD _ t2 _ h2 =>
        exact ⟨(T.r (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.c (T.d t2 x1) (T.d t2 x1) x2)), (Steps.cons (Step.leftR (T.c (T.d x0 x1) (T.d x0 x1) x2) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h2))) (Steps.cons (Step.leftR (T.c (T.d x0 x1) (T.d x0 x1) x2) (Step.secondC (T.d t2 x1) x2 (Step.leftD x1 h2))) (Steps.cons (Step.rightR (T.c (T.d t2 x1) (T.d t2 x1) x2) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h2))) (Steps.cons (Step.rightR (T.c (T.d t2 x1) (T.d t2 x1) x2) (Step.secondC (T.d t2 x1) x2 (Step.leftD x1 h2))) (Steps.refl _))))), (Steps.cons (Step.left (T.c (T.d x0 x1) (T.d t2 x1) x2) h2) (Steps.cons (Step.right t2 (Step.firstC (T.d t2 x1) x2 (Step.leftD x1 h2))) (Steps.cons (Step.root (Root.r17 t2 x1 x2)) (Steps.refl _))))⟩
      | @rightD _ _ t2 h2 =>
        exact ⟨(T.r (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.c (T.d x0 t2) (T.d x0 t2) x2)), (Steps.cons (Step.leftR (T.c (T.d x0 x1) (T.d x0 x1) x2) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h2))) (Steps.cons (Step.leftR (T.c (T.d x0 x1) (T.d x0 x1) x2) (Step.secondC (T.d x0 t2) x2 (Step.rightD x0 h2))) (Steps.cons (Step.rightR (T.c (T.d x0 t2) (T.d x0 t2) x2) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h2))) (Steps.cons (Step.rightR (T.c (T.d x0 t2) (T.d x0 t2) x2) (Step.secondC (T.d x0 t2) x2 (Step.rightD x0 h2))) (Steps.refl _))))), (Steps.cons (Step.right x0 (Step.firstC (T.d x0 t2) x2 (Step.rightD x0 h2))) (Steps.cons (Step.root (Root.r17 x0 t2 x2)) (Steps.refl _)))⟩
    | @thirdC _ _ _ t1 h1 =>
      exact ⟨(T.r (T.c (T.d x0 x1) (T.d x0 x1) t1) (T.c (T.d x0 x1) (T.d x0 x1) t1)), (Steps.cons (Step.leftR (T.c (T.d x0 x1) (T.d x0 x1) x2) (Step.thirdC (T.d x0 x1) (T.d x0 x1) h1)) (Steps.cons (Step.rightR (T.c (T.d x0 x1) (T.d x0 x1) t1) (Step.thirdC (T.d x0 x1) (T.d x0 x1) h1)) (Steps.refl _))), (Steps.cons (Step.root (Root.r17 x0 x1 t1)) (Steps.refl _))⟩
end submission.Austin5837

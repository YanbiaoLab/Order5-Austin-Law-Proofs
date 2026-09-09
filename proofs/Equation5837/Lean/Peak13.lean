import Basic
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak13 (x0 : T) (x1 : T) (x2 : T) {u : T} (h : Step (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) x0 x1) u) : Join (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) u := by
  cases h with
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
      have e3 := (T.c.inj e0).1
      have e4 := (T.c.inj e0).2.1
      have e5 := (T.c.inj e0).2.2
      have e6 := e1.symm
      subst e6
      have e7 := e2.symm
      subst e7
      have e8 := e5.symm
      subst e8
      exact ⟨(T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)), (Steps.refl _), (Steps.refl _)⟩
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
  | @firstC _ t0 _ _ h0 =>
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
        exact ⟨(T.d (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.d t2 x1)), (Steps.cons (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h2))) (Steps.cons (Step.leftD (T.d x0 x1) (Step.secondC (T.d t2 x1) x2 (Step.leftD x1 h2))) (Steps.cons (Step.rightD (T.c (T.d t2 x1) (T.d t2 x1) x2) (Step.leftD x1 h2)) (Steps.refl _)))), (Steps.cons (Step.firstC x0 x1 (Step.secondC (T.d t2 x1) x2 (Step.leftD x1 h2))) (Steps.cons (Step.secondC (T.c (T.d t2 x1) (T.d t2 x1) x2) x1 h2) (Steps.cons (Step.root (Root.r13 t2 x1 x2)) (Steps.refl _))))⟩
      | @rightD _ _ t2 h2 =>
        exact ⟨(T.d (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.d x0 t2)), (Steps.cons (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h2))) (Steps.cons (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t2) x2 (Step.rightD x0 h2))) (Steps.cons (Step.rightD (T.c (T.d x0 t2) (T.d x0 t2) x2) (Step.rightD x0 h2)) (Steps.refl _)))), (Steps.cons (Step.firstC x0 x1 (Step.secondC (T.d x0 t2) x2 (Step.rightD x0 h2))) (Steps.cons (Step.thirdC (T.c (T.d x0 t2) (T.d x0 t2) x2) x0 h2) (Steps.cons (Step.root (Root.r13 x0 t2 x2)) (Steps.refl _))))⟩
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
        exact ⟨(T.d (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.d t2 x1)), (Steps.cons (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h2))) (Steps.cons (Step.leftD (T.d x0 x1) (Step.secondC (T.d t2 x1) x2 (Step.leftD x1 h2))) (Steps.cons (Step.rightD (T.c (T.d t2 x1) (T.d t2 x1) x2) (Step.leftD x1 h2)) (Steps.refl _)))), (Steps.cons (Step.firstC x0 x1 (Step.firstC (T.d t2 x1) x2 (Step.leftD x1 h2))) (Steps.cons (Step.secondC (T.c (T.d t2 x1) (T.d t2 x1) x2) x1 h2) (Steps.cons (Step.root (Root.r13 t2 x1 x2)) (Steps.refl _))))⟩
      | @rightD _ _ t2 h2 =>
        exact ⟨(T.d (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.d x0 t2)), (Steps.cons (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h2))) (Steps.cons (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t2) x2 (Step.rightD x0 h2))) (Steps.cons (Step.rightD (T.c (T.d x0 t2) (T.d x0 t2) x2) (Step.rightD x0 h2)) (Steps.refl _)))), (Steps.cons (Step.firstC x0 x1 (Step.firstC (T.d x0 t2) x2 (Step.rightD x0 h2))) (Steps.cons (Step.thirdC (T.c (T.d x0 t2) (T.d x0 t2) x2) x0 h2) (Steps.cons (Step.root (Root.r13 x0 t2 x2)) (Steps.refl _))))⟩
    | @thirdC _ _ _ t1 h1 =>
      exact ⟨(T.d (T.c (T.d x0 x1) (T.d x0 x1) t1) (T.d x0 x1)), (Steps.cons (Step.leftD (T.d x0 x1) (Step.thirdC (T.d x0 x1) (T.d x0 x1) h1)) (Steps.refl _)), (Steps.cons (Step.root (Root.r13 x0 x1 t1)) (Steps.refl _))⟩
  | @secondC _ _ t0 _ h0 =>
    exact ⟨(T.d (T.c (T.d t0 x1) (T.d t0 x1) x2) (T.d t0 x1)), (Steps.cons (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h0))) (Steps.cons (Step.leftD (T.d x0 x1) (Step.secondC (T.d t0 x1) x2 (Step.leftD x1 h0))) (Steps.cons (Step.rightD (T.c (T.d t0 x1) (T.d t0 x1) x2) (Step.leftD x1 h0)) (Steps.refl _)))), (Steps.cons (Step.firstC t0 x1 (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h0))) (Steps.cons (Step.firstC t0 x1 (Step.secondC (T.d t0 x1) x2 (Step.leftD x1 h0))) (Steps.cons (Step.root (Root.r13 t0 x1 x2)) (Steps.refl _))))⟩
  | @thirdC _ _ _ t0 h0 =>
    exact ⟨(T.d (T.c (T.d x0 t0) (T.d x0 t0) x2) (T.d x0 t0)), (Steps.cons (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h0))) (Steps.cons (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t0) x2 (Step.rightD x0 h0))) (Steps.cons (Step.rightD (T.c (T.d x0 t0) (T.d x0 t0) x2) (Step.rightD x0 h0)) (Steps.refl _)))), (Steps.cons (Step.firstC x0 t0 (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h0))) (Steps.cons (Step.firstC x0 t0 (Step.secondC (T.d x0 t0) x2 (Step.rightD x0 h0))) (Steps.cons (Step.root (Root.r13 x0 t0 x2)) (Steps.refl _))))⟩
end submission.Austin5837

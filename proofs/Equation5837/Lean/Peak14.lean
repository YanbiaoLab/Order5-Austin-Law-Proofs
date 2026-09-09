import Basic
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak14 (x0 : T) (x1 : T) (x2 : T) {u : T} (h : Step (T.c x0 (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) u) : Join (T.c (T.d x0 x1) (T.d x0 x1) x2) u := by
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
      have e4 := (T.c.inj e1).1
      have e5 := (T.c.inj e1).2.1
      have e6 := (T.c.inj e1).2.2
      have e7 := (T.d.inj e2).1
      have e8 := (T.d.inj e2).2
      have e9 := (T.d.inj e4).1
      have e10 := (T.d.inj e4).2
      have e11 := (T.d.inj e5).1
      have e12 := (T.d.inj e5).2
      have e13 := e6.symm
      subst e13
      have e14 := e8.symm
      subst e14
      exact ⟨(T.c (T.d q0 q1) (T.d q0 q1) q2), (Steps.refl _), (Steps.refl _)⟩
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
    exact ⟨(T.c (T.d t0 x1) (T.d t0 x1) x2), (Steps.cons (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h0)) (Steps.cons (Step.secondC (T.d t0 x1) x2 (Step.leftD x1 h0)) (Steps.refl _))), (Steps.cons (Step.secondC t0 (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h0))) (Steps.cons (Step.secondC t0 (T.d x0 x1) (Step.secondC (T.d t0 x1) x2 (Step.leftD x1 h0))) (Steps.cons (Step.thirdC t0 (T.c (T.d t0 x1) (T.d t0 x1) x2) (Step.leftD x1 h0)) (Steps.cons (Step.root (Root.r14 t0 x1 x2)) (Steps.refl _)))))⟩
  | @secondC _ _ t0 _ h0 =>
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
        exact ⟨(T.c (T.d t2 x1) (T.d t2 x1) x2), (Steps.cons (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h2)) (Steps.cons (Step.secondC (T.d t2 x1) x2 (Step.leftD x1 h2)) (Steps.refl _))), (Steps.cons (Step.firstC (T.c (T.d t2 x1) (T.d x0 x1) x2) (T.d x0 x1) h2) (Steps.cons (Step.secondC t2 (T.d x0 x1) (Step.secondC (T.d t2 x1) x2 (Step.leftD x1 h2))) (Steps.cons (Step.thirdC t2 (T.c (T.d t2 x1) (T.d t2 x1) x2) (Step.leftD x1 h2)) (Steps.cons (Step.root (Root.r14 t2 x1 x2)) (Steps.refl _)))))⟩
      | @rightD _ _ t2 h2 =>
        exact ⟨(T.c (T.d x0 t2) (T.d x0 t2) x2), (Steps.cons (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h2)) (Steps.cons (Step.secondC (T.d x0 t2) x2 (Step.rightD x0 h2)) (Steps.refl _))), (Steps.cons (Step.secondC x0 (T.d x0 x1) (Step.secondC (T.d x0 t2) x2 (Step.rightD x0 h2))) (Steps.cons (Step.thirdC x0 (T.c (T.d x0 t2) (T.d x0 t2) x2) (Step.rightD x0 h2)) (Steps.cons (Step.root (Root.r14 x0 t2 x2)) (Steps.refl _))))⟩
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
        exact ⟨(T.c (T.d t2 x1) (T.d t2 x1) x2), (Steps.cons (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h2)) (Steps.cons (Step.secondC (T.d t2 x1) x2 (Step.leftD x1 h2)) (Steps.refl _))), (Steps.cons (Step.firstC (T.c (T.d x0 x1) (T.d t2 x1) x2) (T.d x0 x1) h2) (Steps.cons (Step.secondC t2 (T.d x0 x1) (Step.firstC (T.d t2 x1) x2 (Step.leftD x1 h2))) (Steps.cons (Step.thirdC t2 (T.c (T.d t2 x1) (T.d t2 x1) x2) (Step.leftD x1 h2)) (Steps.cons (Step.root (Root.r14 t2 x1 x2)) (Steps.refl _)))))⟩
      | @rightD _ _ t2 h2 =>
        exact ⟨(T.c (T.d x0 t2) (T.d x0 t2) x2), (Steps.cons (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h2)) (Steps.cons (Step.secondC (T.d x0 t2) x2 (Step.rightD x0 h2)) (Steps.refl _))), (Steps.cons (Step.secondC x0 (T.d x0 x1) (Step.firstC (T.d x0 t2) x2 (Step.rightD x0 h2))) (Steps.cons (Step.thirdC x0 (T.c (T.d x0 t2) (T.d x0 t2) x2) (Step.rightD x0 h2)) (Steps.cons (Step.root (Root.r14 x0 t2 x2)) (Steps.refl _))))⟩
    | @thirdC _ _ _ t1 h1 =>
      exact ⟨(T.c (T.d x0 x1) (T.d x0 x1) t1), (Steps.cons (Step.thirdC (T.d x0 x1) (T.d x0 x1) h1) (Steps.refl _)), (Steps.cons (Step.root (Root.r14 x0 x1 t1)) (Steps.refl _))⟩
  | @thirdC _ _ _ t0 h0 =>
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
    | @leftD _ t1 _ h1 =>
      exact ⟨(T.c (T.d t1 x1) (T.d t1 x1) x2), (Steps.cons (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h1)) (Steps.cons (Step.secondC (T.d t1 x1) x2 (Step.leftD x1 h1)) (Steps.refl _))), (Steps.cons (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d t1 x1) h1) (Steps.cons (Step.secondC t1 (T.d t1 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h1))) (Steps.cons (Step.secondC t1 (T.d t1 x1) (Step.secondC (T.d t1 x1) x2 (Step.leftD x1 h1))) (Steps.cons (Step.root (Root.r14 t1 x1 x2)) (Steps.refl _)))))⟩
    | @rightD _ _ t1 h1 =>
      exact ⟨(T.c (T.d x0 t1) (T.d x0 t1) x2), (Steps.cons (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h1)) (Steps.cons (Step.secondC (T.d x0 t1) x2 (Step.rightD x0 h1)) (Steps.refl _))), (Steps.cons (Step.secondC x0 (T.d x0 t1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h1))) (Steps.cons (Step.secondC x0 (T.d x0 t1) (Step.secondC (T.d x0 t1) x2 (Step.rightD x0 h1))) (Steps.cons (Step.root (Root.r14 x0 t1 x2)) (Steps.refl _))))⟩
end submission.Austin5837

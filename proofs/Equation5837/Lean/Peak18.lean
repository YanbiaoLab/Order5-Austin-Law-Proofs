import Basic
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak18 (x0 : T) (x1 : T) (x2 : T) {u : T} (h : Step (T.m (T.d x0 x1) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) u) : Join (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) u := by
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
      have e2 := (T.d.inj e0).1
      have e3 := (T.d.inj e0).2
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
      have e6 := (T.d.inj e3).1
      have e7 := (T.d.inj e3).2
      have e8 := e4.symm
      subst e8
      have e9 := e5.symm
      subst e9
      have e10 := e6.symm
      have cycle := congrArg size e10
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
      have e2 := (T.d.inj e0).1
      have e3 := (T.d.inj e0).2
      have e4 := e1.symm
      subst e4
      have cycle := congrArg size e2
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := (T.d.inj e0).1
      have e3 := (T.d.inj e0).2
      have e4 := (T.c.inj e1).1
      have e5 := (T.c.inj e1).2.1
      have e6 := (T.c.inj e1).2.2
      have e7 := e2.symm
      subst e7
      have e8 := e3.symm
      subst e8
      cases e4
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
      have e2 := (T.d.inj e0).1
      have e3 := (T.d.inj e0).2
      have e4 := (T.c.inj e1).1
      have e5 := (T.c.inj e1).2.1
      have e6 := (T.c.inj e1).2.2
      subst e2
      have e7 := e3.symm
      subst e7
      cases e4
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
      have cycle := congrArg size e4
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := (T.d.inj e0).1
      have e3 := (T.d.inj e0).2
      have e4 := (T.c.inj e1).1
      have e5 := (T.c.inj e1).2.1
      have e6 := (T.c.inj e1).2.2
      have e7 := e2.symm
      subst e7
      have e8 := e3.symm
      subst e8
      have e9 := (T.d.inj e4).1
      have e10 := (T.d.inj e4).2
      have e11 := (T.c.inj e9).1
      have e12 := (T.c.inj e9).2.1
      have e13 := (T.c.inj e9).2.2
      have e14 := e13.symm
      subst e14
      exact ⟨(T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)), (Steps.refl _), (Steps.refl _)⟩
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := (T.d.inj e0).1
      have e3 := (T.d.inj e0).2
      have e4 := (T.c.inj e1).1
      have e5 := (T.c.inj e1).2.1
      have e6 := (T.c.inj e1).2.2
      subst e2
      subst e3
      have e7 := (T.d.inj e4).1
      have e8 := (T.d.inj e4).2
      have e9 := e5.symm
      have cycle := congrArg size e9
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := (T.d.inj e0).1
      have e3 := (T.d.inj e0).2
      have e4 := (T.c.inj e1).1
      have e5 := (T.c.inj e1).2.1
      have e6 := (T.c.inj e1).2.2
      subst e2
      subst e3
      cases e4
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := (T.d.inj e0).1
      have e3 := (T.d.inj e0).2
      have e4 := (T.c.inj e1).1
      have e5 := (T.c.inj e1).2.1
      have e6 := (T.c.inj e1).2.2
      subst e2
      have e7 := e3.symm
      subst e7
      cases e4
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
      exact ⟨(T.d (T.d t1 x1) (T.c (T.d t1 x1) (T.d t1 x1) x2)), (Steps.cons (Step.leftD (T.c (T.d x0 x1) (T.d x0 x1) x2) (Step.leftD x1 h1)) (Steps.cons (Step.rightD (T.d t1 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h1))) (Steps.cons (Step.rightD (T.d t1 x1) (Step.secondC (T.d t1 x1) x2 (Step.leftD x1 h1))) (Steps.refl _)))), (Steps.cons (Step.right (T.d t1 x1) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h1))))) (Steps.cons (Step.right (T.d t1 x1) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.secondC (T.d t1 x1) x2 (Step.leftD x1 h1))))) (Steps.cons (Step.right (T.d t1 x1) (Step.firstC x0 x1 (Step.rightD (T.c (T.d t1 x1) (T.d t1 x1) x2) (Step.leftD x1 h1)))) (Steps.cons (Step.right (T.d t1 x1) (Step.secondC (T.d (T.c (T.d t1 x1) (T.d t1 x1) x2) (T.d t1 x1)) x1 h1)) (Steps.cons (Step.root (Root.r18 t1 x1 x2)) (Steps.refl _))))))⟩
    | @rightD _ _ t1 h1 =>
      exact ⟨(T.d (T.d x0 t1) (T.c (T.d x0 t1) (T.d x0 t1) x2)), (Steps.cons (Step.leftD (T.c (T.d x0 x1) (T.d x0 x1) x2) (Step.rightD x0 h1)) (Steps.cons (Step.rightD (T.d x0 t1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h1))) (Steps.cons (Step.rightD (T.d x0 t1) (Step.secondC (T.d x0 t1) x2 (Step.rightD x0 h1))) (Steps.refl _)))), (Steps.cons (Step.right (T.d x0 t1) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h1))))) (Steps.cons (Step.right (T.d x0 t1) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t1) x2 (Step.rightD x0 h1))))) (Steps.cons (Step.right (T.d x0 t1) (Step.firstC x0 x1 (Step.rightD (T.c (T.d x0 t1) (T.d x0 t1) x2) (Step.rightD x0 h1)))) (Steps.cons (Step.right (T.d x0 t1) (Step.thirdC (T.d (T.c (T.d x0 t1) (T.d x0 t1) x2) (T.d x0 t1)) x0 h1)) (Steps.cons (Step.root (Root.r18 x0 t1 x2)) (Steps.refl _))))))⟩
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
        cases h2 with
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
        | @firstC _ t3 _ _ h3 =>
          cases h3 with
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
          | @leftD _ t4 _ h4 =>
            exact ⟨(T.d (T.d t4 x1) (T.c (T.d t4 x1) (T.d t4 x1) x2)), (Steps.cons (Step.leftD (T.c (T.d x0 x1) (T.d x0 x1) x2) (Step.leftD x1 h4)) (Steps.cons (Step.rightD (T.d t4 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h4))) (Steps.cons (Step.rightD (T.d t4 x1) (Step.secondC (T.d t4 x1) x2 (Step.leftD x1 h4))) (Steps.refl _)))), (Steps.cons (Step.left (T.c (T.d (T.c (T.d t4 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (Step.leftD x1 h4)) (Steps.cons (Step.right (T.d t4 x1) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.secondC (T.d t4 x1) x2 (Step.leftD x1 h4))))) (Steps.cons (Step.right (T.d t4 x1) (Step.firstC x0 x1 (Step.rightD (T.c (T.d t4 x1) (T.d t4 x1) x2) (Step.leftD x1 h4)))) (Steps.cons (Step.right (T.d t4 x1) (Step.secondC (T.d (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.d t4 x1)) x1 h4)) (Steps.cons (Step.root (Root.r18 t4 x1 x2)) (Steps.refl _))))))⟩
          | @rightD _ _ t4 h4 =>
            exact ⟨(T.d (T.d x0 t4) (T.c (T.d x0 t4) (T.d x0 t4) x2)), (Steps.cons (Step.leftD (T.c (T.d x0 x1) (T.d x0 x1) x2) (Step.rightD x0 h4)) (Steps.cons (Step.rightD (T.d x0 t4) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h4))) (Steps.cons (Step.rightD (T.d x0 t4) (Step.secondC (T.d x0 t4) x2 (Step.rightD x0 h4))) (Steps.refl _)))), (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 t4) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (Step.rightD x0 h4)) (Steps.cons (Step.right (T.d x0 t4) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t4) x2 (Step.rightD x0 h4))))) (Steps.cons (Step.right (T.d x0 t4) (Step.firstC x0 x1 (Step.rightD (T.c (T.d x0 t4) (T.d x0 t4) x2) (Step.rightD x0 h4)))) (Steps.cons (Step.right (T.d x0 t4) (Step.thirdC (T.d (T.c (T.d x0 t4) (T.d x0 t4) x2) (T.d x0 t4)) x0 h4)) (Steps.cons (Step.root (Root.r18 x0 t4 x2)) (Steps.refl _))))))⟩
        | @secondC _ _ t3 _ h3 =>
          cases h3 with
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
          | @leftD _ t4 _ h4 =>
            exact ⟨(T.d (T.d t4 x1) (T.c (T.d t4 x1) (T.d t4 x1) x2)), (Steps.cons (Step.leftD (T.c (T.d x0 x1) (T.d x0 x1) x2) (Step.leftD x1 h4)) (Steps.cons (Step.rightD (T.d t4 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h4))) (Steps.cons (Step.rightD (T.d t4 x1) (Step.secondC (T.d t4 x1) x2 (Step.leftD x1 h4))) (Steps.refl _)))), (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 x1) (T.d t4 x1) x2) (T.d x0 x1)) x0 x1) (Step.leftD x1 h4)) (Steps.cons (Step.right (T.d t4 x1) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.firstC (T.d t4 x1) x2 (Step.leftD x1 h4))))) (Steps.cons (Step.right (T.d t4 x1) (Step.firstC x0 x1 (Step.rightD (T.c (T.d t4 x1) (T.d t4 x1) x2) (Step.leftD x1 h4)))) (Steps.cons (Step.right (T.d t4 x1) (Step.secondC (T.d (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.d t4 x1)) x1 h4)) (Steps.cons (Step.root (Root.r18 t4 x1 x2)) (Steps.refl _))))))⟩
          | @rightD _ _ t4 h4 =>
            exact ⟨(T.d (T.d x0 t4) (T.c (T.d x0 t4) (T.d x0 t4) x2)), (Steps.cons (Step.leftD (T.c (T.d x0 x1) (T.d x0 x1) x2) (Step.rightD x0 h4)) (Steps.cons (Step.rightD (T.d x0 t4) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h4))) (Steps.cons (Step.rightD (T.d x0 t4) (Step.secondC (T.d x0 t4) x2 (Step.rightD x0 h4))) (Steps.refl _)))), (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 x1) (T.d x0 t4) x2) (T.d x0 x1)) x0 x1) (Step.rightD x0 h4)) (Steps.cons (Step.right (T.d x0 t4) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 t4) x2 (Step.rightD x0 h4))))) (Steps.cons (Step.right (T.d x0 t4) (Step.firstC x0 x1 (Step.rightD (T.c (T.d x0 t4) (T.d x0 t4) x2) (Step.rightD x0 h4)))) (Steps.cons (Step.right (T.d x0 t4) (Step.thirdC (T.d (T.c (T.d x0 t4) (T.d x0 t4) x2) (T.d x0 t4)) x0 h4)) (Steps.cons (Step.root (Root.r18 x0 t4 x2)) (Steps.refl _))))))⟩
        | @thirdC _ _ _ t3 h3 =>
          exact ⟨(T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) t3)), (Steps.cons (Step.rightD (T.d x0 x1) (Step.thirdC (T.d x0 x1) (T.d x0 x1) h3)) (Steps.refl _)), (Steps.cons (Step.root (Root.r18 x0 x1 t3)) (Steps.refl _))⟩
      | @rightD _ _ t2 h2 =>
        cases h2 with
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
        | @leftD _ t3 _ h3 =>
          exact ⟨(T.d (T.d t3 x1) (T.c (T.d t3 x1) (T.d t3 x1) x2)), (Steps.cons (Step.leftD (T.c (T.d x0 x1) (T.d x0 x1) x2) (Step.leftD x1 h3)) (Steps.cons (Step.rightD (T.d t3 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3))) (Steps.cons (Step.rightD (T.d t3 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3))) (Steps.refl _)))), (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d t3 x1)) x0 x1) (Step.leftD x1 h3)) (Steps.cons (Step.right (T.d t3 x1) (Step.firstC x0 x1 (Step.leftD (T.d t3 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3))))) (Steps.cons (Step.right (T.d t3 x1) (Step.firstC x0 x1 (Step.leftD (T.d t3 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3))))) (Steps.cons (Step.right (T.d t3 x1) (Step.secondC (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) x1 h3)) (Steps.cons (Step.root (Root.r18 t3 x1 x2)) (Steps.refl _))))))⟩
        | @rightD _ _ t3 h3 =>
          exact ⟨(T.d (T.d x0 t3) (T.c (T.d x0 t3) (T.d x0 t3) x2)), (Steps.cons (Step.leftD (T.c (T.d x0 x1) (T.d x0 x1) x2) (Step.rightD x0 h3)) (Steps.cons (Step.rightD (T.d x0 t3) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3))) (Steps.cons (Step.rightD (T.d x0 t3) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3))) (Steps.refl _)))), (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 t3)) x0 x1) (Step.rightD x0 h3)) (Steps.cons (Step.right (T.d x0 t3) (Step.firstC x0 x1 (Step.leftD (T.d x0 t3) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3))))) (Steps.cons (Step.right (T.d x0 t3) (Step.firstC x0 x1 (Step.leftD (T.d x0 t3) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3))))) (Steps.cons (Step.right (T.d x0 t3) (Step.thirdC (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) x0 h3)) (Steps.cons (Step.root (Root.r18 x0 t3 x2)) (Steps.refl _))))))⟩
    | @secondC _ _ t1 _ h1 =>
      exact ⟨(T.d (T.d t1 x1) (T.c (T.d t1 x1) (T.d t1 x1) x2)), (Steps.cons (Step.leftD (T.c (T.d x0 x1) (T.d x0 x1) x2) (Step.leftD x1 h1)) (Steps.cons (Step.rightD (T.d t1 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h1))) (Steps.cons (Step.rightD (T.d t1 x1) (Step.secondC (T.d t1 x1) x2 (Step.leftD x1 h1))) (Steps.refl _)))), (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) t1 x1) (Step.leftD x1 h1)) (Steps.cons (Step.right (T.d t1 x1) (Step.firstC t1 x1 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h1))))) (Steps.cons (Step.right (T.d t1 x1) (Step.firstC t1 x1 (Step.leftD (T.d x0 x1) (Step.secondC (T.d t1 x1) x2 (Step.leftD x1 h1))))) (Steps.cons (Step.right (T.d t1 x1) (Step.firstC t1 x1 (Step.rightD (T.c (T.d t1 x1) (T.d t1 x1) x2) (Step.leftD x1 h1)))) (Steps.cons (Step.root (Root.r18 t1 x1 x2)) (Steps.refl _))))))⟩
    | @thirdC _ _ _ t1 h1 =>
      exact ⟨(T.d (T.d x0 t1) (T.c (T.d x0 t1) (T.d x0 t1) x2)), (Steps.cons (Step.leftD (T.c (T.d x0 x1) (T.d x0 x1) x2) (Step.rightD x0 h1)) (Steps.cons (Step.rightD (T.d x0 t1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h1))) (Steps.cons (Step.rightD (T.d x0 t1) (Step.secondC (T.d x0 t1) x2 (Step.rightD x0 h1))) (Steps.refl _)))), (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 t1) (Step.rightD x0 h1)) (Steps.cons (Step.right (T.d x0 t1) (Step.firstC x0 t1 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h1))))) (Steps.cons (Step.right (T.d x0 t1) (Step.firstC x0 t1 (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t1) x2 (Step.rightD x0 h1))))) (Steps.cons (Step.right (T.d x0 t1) (Step.firstC x0 t1 (Step.rightD (T.c (T.d x0 t1) (T.d x0 t1) x2) (Step.rightD x0 h1)))) (Steps.cons (Step.root (Root.r18 x0 t1 x2)) (Steps.refl _))))))⟩
end submission.Austin5837

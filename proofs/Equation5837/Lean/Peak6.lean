import Basic
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak6 (x0 : T) (x1 : T) {u : T} (h : Step (T.m (T.d x0 x1) (T.r x0 x1)) u) : Join (T.r (T.r x0 x1) x0) u := by
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
      have e3 := (T.r.inj e1).1
      have e4 := (T.r.inj e1).2
      have cycle := congrArg size e3
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
      cases e0
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := (T.d.inj e0).1
      have e3 := (T.d.inj e0).2
      have e4 := (T.r.inj e1).1
      have e5 := (T.r.inj e1).2
      have e6 := e2.symm
      subst e6
      have e7 := e3.symm
      subst e7
      exact ⟨(T.r (T.r q0 q1) q0), (Steps.refl _), (Steps.refl _)⟩
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      cases e1
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
      cases e1
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
      have e2 := (T.d.inj e0).1
      have e3 := (T.d.inj e0).2
      cases e1
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := (T.d.inj e0).1
      have e3 := (T.d.inj e0).2
      cases e1
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := (T.d.inj e0).1
      have e3 := (T.d.inj e0).2
      cases e1
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := (T.d.inj e0).1
      have e3 := (T.d.inj e0).2
      cases e1
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
      exact ⟨(T.r (T.r t1 x1) t1), (Steps.cons (Step.leftR x0 (Step.leftR x1 h1)) (Steps.cons (Step.rightR (T.r t1 x1) h1) (Steps.refl _))), (Steps.cons (Step.right (T.d t1 x1) (Step.leftR x1 h1)) (Steps.cons (Step.root (Root.r6 t1 x1)) (Steps.refl _)))⟩
    | @rightD _ _ t1 h1 =>
      exact ⟨(T.r (T.r x0 t1) x0), (Steps.cons (Step.leftR x0 (Step.rightR x0 h1)) (Steps.refl _)), (Steps.cons (Step.right (T.d x0 t1) (Step.rightR x0 h1)) (Steps.cons (Step.root (Root.r6 x0 t1)) (Steps.refl _)))⟩
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
        have e0 := (T.r.inj he).1
        have e1 := (T.r.inj he).2
        subst e0
        have e2 := e1.symm
        subst e2
        exact ⟨(T.r (T.c (T.c q2 q0 q1) q0 q1) (T.d q0 q1)), (Steps.cons (Step.leftR (T.d q0 q1) (Step.root (Root.r7 q0 q1 q2))) (Steps.refl _)), (Steps.cons (Step.root (Root.r16 q0 q1 q2)) (Steps.refl _))⟩
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.r.inj he).1
        have e1 := (T.r.inj he).2
        subst e0
        have e2 := e1.symm
        subst e2
        exact ⟨(T.r q0 (T.c q0 q0 q1)), (Steps.cons (Step.leftR (T.c q0 q0 q1) (Step.root (Root.r9 q0 q1))) (Steps.refl _)), (Steps.cons (Step.root (Root.r11 q0 q1)) (Steps.refl _))⟩
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
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
      exact ⟨(T.r (T.r t1 x1) t1), (Steps.cons (Step.leftR x0 (Step.leftR x1 h1)) (Steps.cons (Step.rightR (T.r t1 x1) h1) (Steps.refl _))), (Steps.cons (Step.left (T.r t1 x1) (Step.leftD x1 h1)) (Steps.cons (Step.root (Root.r6 t1 x1)) (Steps.refl _)))⟩
    | @rightR _ _ t1 h1 =>
      exact ⟨(T.r (T.r x0 t1) x0), (Steps.cons (Step.leftR x0 (Step.rightR x0 h1)) (Steps.refl _)), (Steps.cons (Step.left (T.r x0 t1) (Step.rightD x0 h1)) (Steps.cons (Step.root (Root.r6 x0 t1)) (Steps.refl _)))⟩
end submission.Austin5837

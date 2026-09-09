import Basic
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin18212
open T
theorem peak14 (x0 : T) (x1 : T) {u : T} (h : Step (T.m (T.r x0 x1) x1) u) : Join (T.r (T.m x0 x1) x1) u := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨he, ho⟩ | ⟨he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩
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
      cases he
    · rw [ho]
      cases he
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
      have e2 := (T.r.inj e0).1
      have e3 := (T.r.inj e0).2
      subst x1
      subst x0
      have e4 := e3.symm
      subst q0
      exact ⟨T.e, (Steps.cons (Step.leftR T.e (Step.root (Root.r1 T.e))) (Steps.cons (Step.root (Root.r6 )) (Steps.refl _))), (Steps.cons (Step.underV (Step.root (Root.r6 ))) (Steps.cons (Step.root (Root.r7 )) (Steps.refl _)))⟩
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := (T.r.inj e0).1
      have e3 := (T.r.inj e0).2
      subst x1
      subst x0
      exact ⟨(T.r (T.m q0 q1) q1), (Steps.refl _), (Steps.refl _)⟩
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
      rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨he, ho⟩ | ⟨he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩
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
        exact ⟨(T.r T.e (T.v q0)), (Steps.cons (Step.leftR (T.v q0) (Step.root (Root.r1 (T.v q0)))) (Steps.refl _)), (Steps.cons (Step.root (Root.r11 q0)) (Steps.refl _))⟩
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.r.inj he).1
        have e1 := (T.r.inj he).2
        subst x0
        subst x1
        exact ⟨T.e, (Steps.cons (Step.leftR T.e (Step.root (Root.r1 T.e))) (Steps.cons (Step.root (Root.r6 )) (Steps.refl _))), (Steps.cons (Step.root (Root.r1 T.e)) (Steps.refl _))⟩
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.r.inj he).1
        have e1 := (T.r.inj he).2
        subst x0
        subst x1
        exact ⟨T.e, (Steps.cons (Step.leftR (T.r T.e q0) (Step.root (Root.r1 (T.r T.e q0)))) (Steps.cons (Step.root (Root.r10 q0)) (Steps.refl _))), (Steps.cons (Step.root (Root.r3 T.e q0)) (Steps.cons (Step.root (Root.r7 )) (Steps.refl _)))⟩
      · rw [ho]
        have e0 := (T.r.inj he).1
        have e1 := (T.r.inj he).2
        subst x0
        subst x1
        exact ⟨T.e, (Steps.cons (Step.leftR (T.r T.e q0) (Step.root (Root.r3 T.e q0))) (Steps.cons (Step.leftR (T.r T.e q0) (Step.root (Root.r7 ))) (Steps.cons (Step.root (Root.r10 q0)) (Steps.refl _)))), (Steps.cons (Step.root (Root.r3 T.e q0)) (Steps.cons (Step.root (Root.r7 )) (Steps.refl _)))⟩
      · rw [ho]
        cases he
      · rw [ho]
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
      exact ⟨(T.r (T.m t1 x1) x1), (Steps.cons (Step.leftR x1 (Step.left x1 h1)) (Steps.refl _)), (Steps.cons (Step.root (Root.r14 t1 x1)) (Steps.refl _))⟩
    | @rightR _ _ t1 h1 =>
      exact ⟨(T.r (T.m x0 t1) t1), (Steps.cons (Step.leftR x1 (Step.right x0 h1)) (Steps.cons (Step.rightR (T.m x0 t1) h1) (Steps.refl _))), (Steps.cons (Step.right (T.r x0 t1) h1) (Steps.cons (Step.root (Root.r14 x0 t1)) (Steps.refl _)))⟩
  | @right _ _ t0 h0 =>
    exact ⟨(T.r (T.m x0 t0) t0), (Steps.cons (Step.leftR x1 (Step.right x0 h0)) (Steps.cons (Step.rightR (T.m x0 t0) h0) (Steps.refl _))), (Steps.cons (Step.left t0 (Step.rightR x0 h0)) (Steps.cons (Step.root (Root.r14 x0 t0)) (Steps.refl _)))⟩
end submission.Austin18212

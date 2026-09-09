import Basic
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin18212
open T
theorem peak2 (x0 : T) (x1 : T) {u : T} (h : Step (T.m (T.m x0 x1) x1) u) : Join (T.r x0 x1) u := by
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
      have e2 := (T.m.inj e0).1
      have e3 := (T.m.inj e0).2
      subst x1
      subst x0
      exact ⟨(T.r q0 q1), (Steps.refl _), (Steps.refl _)⟩
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
      rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨he, ho⟩ | ⟨he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        subst x1
        exact ⟨(T.r q0 q0), (Steps.refl _), (Steps.cons (Step.root (Root.r5 q0)) (Steps.refl _))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        subst x1
        exact ⟨(T.r (T.m q0 q1) q1), (Steps.refl _), (Steps.cons (Step.root (Root.r14 q0 q1)) (Steps.refl _))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        subst x1
        exact ⟨(T.r q0 (T.r q0 q1)), (Steps.refl _), (Steps.cons (Step.root (Root.r15 q0 q1)) (Steps.refl _))⟩
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        subst x1
        exact ⟨(T.r T.e q0), (Steps.refl _), (Steps.cons (Step.root (Root.r14 q0 q0)) (Steps.cons (Step.leftR q0 (Step.root (Root.r1 q0))) (Steps.refl _)))⟩
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        subst x1
        exact ⟨(T.r (T.v q0) q0), (Steps.refl _), (Steps.cons (Step.root (Root.r12 q0)) (Steps.refl _))⟩
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        subst x1
        exact ⟨(T.r q0 (T.v q0)), (Steps.refl _), (Steps.cons (Step.root (Root.r14 T.e (T.v q0))) (Steps.cons (Step.leftR (T.v q0) (Step.root (Root.r5 (T.v q0)))) (Steps.cons (Step.leftR (T.v q0) (Step.root (Root.r4 q0))) (Steps.refl _))))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        subst x1
        exact ⟨(T.r (T.v (T.v q0)) q0), (Steps.refl _), (Steps.cons (Step.root (Root.r14 (T.v q0) q0)) (Steps.cons (Step.leftR q0 (Step.root (Root.r8 q0))) (Steps.refl _)))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        subst x1
        exact ⟨(T.r (T.r T.e q0) T.e), (Steps.refl _), (Steps.cons (Step.root (Root.r16 q0)) (Steps.refl _))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        subst x1
        exact ⟨(T.r (T.r q0 q1) q1), (Steps.refl _), (Steps.cons (Step.root (Root.r14 (T.m q0 q1) q1)) (Steps.cons (Step.leftR q1 (Step.root (Root.r2 q0 q1))) (Steps.refl _)))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        subst x1
        exact ⟨(T.r (T.v q0) (T.r q0 q1)), (Steps.refl _), (Steps.cons (Step.root (Root.r14 q0 (T.r q0 q1))) (Steps.cons (Step.leftR (T.r q0 q1) (Step.root (Root.r3 q0 q1))) (Steps.refl _)))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        subst x1
        exact ⟨(T.r (T.v (T.r T.e q0)) T.e), (Steps.refl _), (Steps.cons (Step.root (Root.r14 (T.r T.e q0) T.e)) (Steps.cons (Step.leftR T.e (Step.root (Root.r13 q0))) (Steps.refl _)))⟩
    | @left _ t1 _ h1 =>
      exact ⟨(T.r t1 x1), (Steps.cons (Step.leftR x1 h1) (Steps.refl _)), (Steps.cons (Step.root (Root.r2 t1 x1)) (Steps.refl _))⟩
    | @right _ _ t1 h1 =>
      exact ⟨(T.r x0 t1), (Steps.cons (Step.rightR x0 h1) (Steps.refl _)), (Steps.cons (Step.right (T.m x0 t1) h1) (Steps.cons (Step.root (Root.r2 x0 t1)) (Steps.refl _)))⟩
  | @right _ _ t0 h0 =>
    exact ⟨(T.r x0 t0), (Steps.cons (Step.rightR x0 h0) (Steps.refl _)), (Steps.cons (Step.left t0 (Step.right x0 h0)) (Steps.cons (Step.root (Root.r2 x0 t0)) (Steps.refl _)))⟩
end submission.Austin18212

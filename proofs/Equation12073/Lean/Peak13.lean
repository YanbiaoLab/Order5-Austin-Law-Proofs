import Basic
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin12073
open T
theorem peak13 (x0 : T) {u : T} (h : Step (T.d x0 (T.d x0 x0)) u) : Join (T.u x0) u := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩
    · rw [ho]
      cases he
    · rw [ho]
      cases he
    · rw [ho]
      cases he
    · rw [ho]
      cases he
    · rw [ho]
      cases he
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.d.inj he).1
      have e1 := (T.d.inj he).2
      have e2 := e0.symm
      subst e2
      cases e1
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.d.inj he).1
      have e1 := (T.d.inj he).2
      subst e0
      have e2 := (T.d.inj e1).1
      have e3 := (T.d.inj e1).2
      cases e2
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.d.inj he).1
      have e1 := (T.d.inj he).2
      subst e0
      cases e1
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.d.inj he).1
      have e1 := (T.d.inj he).2
      have e2 := e0.symm
      subst e2
      exact ⟨(T.u q0), (Steps.refl _), (Steps.refl _)⟩
    · rw [ho]
      cases he
    · rw [ho]
      cases he
    · rw [ho]
      cases he
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.d.inj he).1
      have e1 := (T.d.inj he).2
      subst e0
      have e2 := e1.symm
      have cycle := congrArg size e2
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
  | @leftD _ t0 _ h0 =>
    exact ⟨(T.u t0), (Steps.cons (Step.underU h0) (Steps.refl _)), (Steps.cons (Step.rightD t0 (Step.leftD x0 h0)) (Steps.cons (Step.rightD t0 (Step.rightD t0 h0)) (Steps.cons (Step.root (Root.r13 t0)) (Steps.refl _))))⟩
  | @rightD _ _ t0 h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.d.inj he).1
        have e1 := (T.d.inj he).2
        have e2 := e0.symm
        subst e2
        subst e1
        exact ⟨T.e, (Steps.cons (Step.root (Root.r6 )) (Steps.refl _)), (Steps.cons (Step.root (Root.r7 T.e)) (Steps.refl _))⟩
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.d.inj he).1
        have e1 := (T.d.inj he).2
        subst e0
        exact ⟨(T.u (T.d T.e q0)), (Steps.refl _), (Steps.cons (Step.root (Root.r11 q0)) (Steps.refl _))⟩
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.d.inj he).1
        have e1 := (T.d.inj he).2
        subst e0
        cases e1
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.d.inj he).1
        have e1 := (T.d.inj he).2
        have e2 := e0.symm
        subst e2
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
        have e0 := (T.d.inj he).1
        have e1 := (T.d.inj he).2
        subst e0
        have e2 := e1.symm
        have cycle := congrArg size e2
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
    | @leftD _ t1 _ h1 =>
      exact ⟨(T.u t1), (Steps.cons (Step.underU h1) (Steps.refl _)), (Steps.cons (Step.leftD (T.d t1 x0) h1) (Steps.cons (Step.rightD t1 (Step.rightD t1 h1)) (Steps.cons (Step.root (Root.r13 t1)) (Steps.refl _))))⟩
    | @rightD _ _ t1 h1 =>
      exact ⟨(T.u t1), (Steps.cons (Step.underU h1) (Steps.refl _)), (Steps.cons (Step.leftD (T.d x0 t1) h1) (Steps.cons (Step.rightD t1 (Step.leftD t1 h1)) (Steps.cons (Step.root (Root.r13 t1)) (Steps.refl _))))⟩
end submission.Austin12073

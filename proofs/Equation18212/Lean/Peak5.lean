import Basic
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin18212
open T
theorem peak5 (x0 : T) {u : T} (h : Step (T.m T.e x0) u) : Join (T.r x0 x0) u := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨he, ho⟩ | ⟨he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst q0
      subst x0
      exact ⟨T.e, (Steps.cons (Step.root (Root.r6 )) (Steps.refl _)), (Steps.refl _)⟩
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      cases e0
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst q0
      subst x0
      exact ⟨T.e, (Steps.cons (Step.root (Root.r9 q1)) (Steps.refl _)), (Steps.cons (Step.root (Root.r7 )) (Steps.refl _))⟩
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst x0
      exact ⟨(T.r q0 q0), (Steps.refl _), (Steps.refl _)⟩
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
      subst x0
      exact ⟨T.e, (Steps.cons (Step.root (Root.r4 T.e)) (Steps.refl _)), (Steps.cons (Step.rightR T.e (Step.root (Root.r7 ))) (Steps.cons (Step.root (Root.r6 )) (Steps.refl _)))⟩
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
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
  | @right _ _ t0 h0 =>
    exact ⟨(T.r t0 t0), (Steps.cons (Step.leftR x0 h0) (Steps.cons (Step.rightR t0 h0) (Steps.refl _))), (Steps.cons (Step.root (Root.r5 t0)) (Steps.refl _))⟩
end submission.Austin18212

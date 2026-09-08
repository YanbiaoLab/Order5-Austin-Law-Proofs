import Basic
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin12073
open T
theorem peak7 (x0 : T) {u : T} (h : Step (T.d x0 T.e) u) : Join x0 u := by
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
      exact ⟨q0, (Steps.refl _), (Steps.refl _)⟩
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
      subst e0
      cases e1
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
      subst e2
      exact ⟨T.e, (Steps.cons (Step.rightD T.e (Step.underU (Step.root (Root.r6 )))) (Steps.cons (Step.rightD T.e (Step.root (Root.r6 ))) (Steps.cons (Step.root (Root.r7 T.e)) (Steps.refl _)))), (Steps.cons (Step.underU (Step.rightD T.e (Step.underU (Step.root (Root.r6 ))))) (Steps.cons (Step.underU (Step.rightD T.e (Step.root (Root.r6 )))) (Steps.cons (Step.underU (Step.root (Root.r7 T.e))) (Steps.cons (Step.root (Root.r6 )) (Steps.refl _)))))⟩
    · rw [ho]
      cases he
    · rw [ho]
      cases he
    · rw [ho]
      cases he
    · rw [ho]
      cases he
  | @leftD _ t0 _ h0 =>
    exact ⟨t0, (Steps.cons h0 (Steps.refl _)), (Steps.cons (Step.root (Root.r7 t0)) (Steps.refl _))⟩
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
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
end submission.Austin12073

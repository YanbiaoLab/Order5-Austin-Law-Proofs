import Basic
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin12073
open T
theorem peak2 (x0 : T) {u : T} (h : Step (T.m x0 T.e) u) : Join (T.u x0) u := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      have e3 := e1.symm
      subst e3
      exact ⟨T.e, (Steps.cons (Step.root (Root.r6 )) (Steps.refl _)), (Steps.refl _)⟩
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      exact ⟨(T.u q0), (Steps.refl _), (Steps.refl _)⟩
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
      have e2 := e1.symm
      subst e2
      exact ⟨(T.u (T.u q0)), (Steps.cons (Step.underU (Step.root (Root.r2 q0))) (Steps.refl _)), (Steps.cons (Step.underU (Step.underU (Step.root (Root.r7 q0)))) (Steps.refl _))⟩
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      cases e1
    · rw [ho]
      cases he
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
      have e2 := e1.symm
      subst e2
      exact ⟨T.e, (Steps.cons (Step.root (Root.r6 )) (Steps.refl _)), (Steps.cons (Step.underU (Step.underU (Step.root (Root.r7 T.e)))) (Steps.cons (Step.underU (Step.root (Root.r6 ))) (Steps.cons (Step.root (Root.r6 )) (Steps.refl _))))⟩
    · rw [ho]
      cases he
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
      cases e1
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      cases e1
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
      cases e1
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
      have e2 := e1.symm
      subst e2
      exact ⟨T.e, (Steps.cons (Step.underU (Step.rightD T.e (Step.underU (Step.root (Root.r6 ))))) (Steps.cons (Step.underU (Step.rightD T.e (Step.root (Root.r6 )))) (Steps.cons (Step.underU (Step.root (Root.r7 T.e))) (Steps.cons (Step.root (Root.r6 )) (Steps.refl _))))), (Steps.cons (Step.rightD T.e (Step.underU (Step.root (Root.r6 )))) (Steps.cons (Step.rightD T.e (Step.root (Root.r6 ))) (Steps.cons (Step.root (Root.r7 T.e)) (Steps.refl _))))⟩
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
      have e2 := e1.symm
      subst e2
      exact ⟨T.e, (Steps.cons (Step.root (Root.r3 T.e)) (Steps.refl _)), (Steps.cons (Step.leftD (T.u (T.u T.e)) (Step.underU (Step.root (Root.r6 )))) (Steps.cons (Step.leftD (T.u (T.u T.e)) (Step.root (Root.r6 ))) (Steps.cons (Step.rightD T.e (Step.underU (Step.root (Root.r6 )))) (Steps.cons (Step.rightD T.e (Step.root (Root.r6 ))) (Steps.cons (Step.root (Root.r7 T.e)) (Steps.refl _))))))⟩
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
      have e2 := e1.symm
      subst e2
      exact ⟨q0, (Steps.cons (Step.root (Root.r3 (T.d q0 T.e))) (Steps.cons (Step.root (Root.r7 q0)) (Steps.refl _))), (Steps.cons (Step.underU (Step.underU (Step.root (Root.r7 (T.m q0 T.e))))) (Steps.cons (Step.underU (Step.underU (Step.root (Root.r2 q0)))) (Steps.cons (Step.root (Root.r3 q0)) (Steps.refl _))))⟩
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
      have e2 := e1.symm
      subst e2
      exact ⟨T.e, (Steps.cons (Step.underU (Step.leftD (T.u (T.u T.e)) (Step.underU (Step.root (Root.r6 ))))) (Steps.cons (Step.underU (Step.leftD (T.u (T.u T.e)) (Step.root (Root.r6 )))) (Steps.cons (Step.underU (Step.rightD T.e (Step.underU (Step.root (Root.r6 ))))) (Steps.cons (Step.underU (Step.rightD T.e (Step.root (Root.r6 )))) (Steps.cons (Step.underU (Step.root (Root.r7 T.e))) (Steps.cons (Step.root (Root.r6 )) (Steps.refl _))))))), (Steps.cons (Step.underU (Step.underU (Step.root (Root.r7 (T.u (T.u T.e)))))) (Steps.cons (Step.root (Root.r3 (T.u T.e))) (Steps.cons (Step.root (Root.r6 )) (Steps.refl _))))⟩
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
      cases e1
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      cases e1
  | @left _ t0 _ h0 =>
    exact ⟨(T.u t0), (Steps.cons (Step.underU h0) (Steps.refl _)), (Steps.cons (Step.root (Root.r2 t0)) (Steps.refl _))⟩
  | @right _ _ t0 h0 =>
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

import Basic
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin12073
open T
theorem peak8 (x0 : T) {u : T} (h : Step (T.m T.e x0) u) : Join (T.u (T.u (T.d x0 x0))) u := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      subst e1
      exact ⟨T.e, (Steps.cons (Step.underU (Step.underU (Step.root (Root.r7 T.e)))) (Steps.cons (Step.underU (Step.root (Root.r6 ))) (Steps.cons (Step.root (Root.r6 )) (Steps.refl _)))), (Steps.refl _)⟩
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      subst e1
      exact ⟨T.e, (Steps.cons (Step.underU (Step.underU (Step.root (Root.r7 T.e)))) (Steps.cons (Step.underU (Step.root (Root.r6 ))) (Steps.cons (Step.root (Root.r6 )) (Steps.refl _)))), (Steps.cons (Step.root (Root.r6 )) (Steps.refl _))⟩
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      cases e0
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      subst e1
      exact ⟨q1, (Steps.cons (Step.underU (Step.underU (Step.root (Root.r9 q1)))) (Steps.cons (Step.root (Root.r3 q1)) (Steps.refl _))), (Steps.refl _)⟩
    · rw [ho]
      cases he
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e1.symm
      subst e2
      exact ⟨(T.u (T.u (T.d q0 q0))), (Steps.refl _), (Steps.refl _)⟩
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      cases e0
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      subst e1
      exact ⟨(T.u (T.u (T.d q1 q1))), (Steps.cons (Step.underU (Step.underU (Step.leftD (T.d q1 T.e) (Step.root (Root.r7 q1))))) (Steps.cons (Step.underU (Step.underU (Step.rightD q1 (Step.root (Root.r7 q1))))) (Steps.refl _))), (Steps.cons (Step.underU (Step.underU (Step.rightD q1 (Step.root (Root.r7 q1))))) (Steps.refl _))⟩
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      subst e1
      exact ⟨T.e, (Steps.cons (Step.underU (Step.underU (Step.leftD (T.u T.e) (Step.root (Root.r6 ))))) (Steps.cons (Step.underU (Step.underU (Step.rightD T.e (Step.root (Root.r6 ))))) (Steps.cons (Step.underU (Step.underU (Step.root (Root.r7 T.e)))) (Steps.cons (Step.underU (Step.root (Root.r6 ))) (Steps.cons (Step.root (Root.r6 )) (Steps.refl _)))))), (Steps.cons (Step.root (Root.r7 T.e)) (Steps.refl _))⟩
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
      cases he
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
      have e2 := e0.symm
      subst e2
      subst e1
      exact ⟨T.e, (Steps.cons (Step.underU (Step.underU (Step.leftD (T.u (T.d T.e (T.u (T.u T.e)))) (Step.underU (Step.rightD T.e (Step.underU (Step.root (Root.r6 )))))))) (Steps.cons (Step.underU (Step.underU (Step.leftD (T.u (T.d T.e (T.u (T.u T.e)))) (Step.underU (Step.rightD T.e (Step.root (Root.r6 ))))))) (Steps.cons (Step.underU (Step.underU (Step.leftD (T.u (T.d T.e (T.u (T.u T.e)))) (Step.underU (Step.root (Root.r7 T.e)))))) (Steps.cons (Step.underU (Step.underU (Step.leftD (T.u (T.d T.e (T.u (T.u T.e)))) (Step.root (Root.r6 ))))) (Steps.cons (Step.underU (Step.underU (Step.rightD T.e (Step.underU (Step.rightD T.e (Step.underU (Step.root (Root.r6 )))))))) (Steps.cons (Step.underU (Step.underU (Step.rightD T.e (Step.underU (Step.rightD T.e (Step.root (Root.r6 ))))))) (Steps.cons (Step.underU (Step.underU (Step.rightD T.e (Step.underU (Step.root (Root.r7 T.e)))))) (Steps.cons (Step.underU (Step.underU (Step.rightD T.e (Step.root (Root.r6 ))))) (Steps.cons (Step.underU (Step.underU (Step.root (Root.r7 T.e)))) (Steps.cons (Step.underU (Step.root (Root.r6 ))) (Steps.cons (Step.root (Root.r6 )) (Steps.refl _)))))))))))), (Steps.cons (Step.underU (Step.underU (Step.leftD (T.u (T.d T.e (T.u (T.u T.e)))) (Step.rightD T.e (Step.underU (Step.root (Root.r6 ))))))) (Steps.cons (Step.underU (Step.underU (Step.leftD (T.u (T.d T.e (T.u (T.u T.e)))) (Step.rightD T.e (Step.root (Root.r6 )))))) (Steps.cons (Step.underU (Step.underU (Step.leftD (T.u (T.d T.e (T.u (T.u T.e)))) (Step.root (Root.r7 T.e))))) (Steps.cons (Step.underU (Step.underU (Step.rightD T.e (Step.underU (Step.rightD T.e (Step.underU (Step.root (Root.r6 )))))))) (Steps.cons (Step.underU (Step.underU (Step.rightD T.e (Step.underU (Step.rightD T.e (Step.root (Root.r6 ))))))) (Steps.cons (Step.underU (Step.underU (Step.rightD T.e (Step.underU (Step.root (Root.r7 T.e)))))) (Steps.cons (Step.underU (Step.underU (Step.rightD T.e (Step.root (Root.r6 ))))) (Steps.cons (Step.underU (Step.underU (Step.root (Root.r7 T.e)))) (Steps.cons (Step.underU (Step.root (Root.r6 ))) (Steps.cons (Step.root (Root.r6 )) (Steps.refl _)))))))))))⟩
  | @left _ t0 _ h0 =>
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
  | @right _ _ t0 h0 =>
    exact ⟨(T.u (T.u (T.d t0 t0))), (Steps.cons (Step.underU (Step.underU (Step.leftD x0 h0))) (Steps.cons (Step.underU (Step.underU (Step.rightD t0 h0))) (Steps.refl _))), (Steps.cons (Step.root (Root.r8 t0)) (Steps.refl _))⟩
end submission.Austin12073

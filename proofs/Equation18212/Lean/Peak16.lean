import Basic
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin18212
open T
theorem peak16 (x0 : T) {u : T} (h : Step (T.m (T.v (T.r T.e x0)) T.e) u) : Join (T.r (T.r T.e x0) T.e) u := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨he, ho⟩ | ⟨he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst q0
      cases e1
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      cases e0
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst q0
      cases e1
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
      have e2 := T.v.inj e0
      have e3 := e1.symm
      subst q0
      cases e2
    · rw [ho]
      cases he
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst q0
      cases e1
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := T.v.inj e0
      have e3 := e1.symm
      subst q0
      cases e2
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
      have e2 := T.v.inj e0
      cases e1
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := T.v.inj e0
      have e3 := (T.r.inj e2).1
      have e4 := (T.r.inj e2).2
      subst x0
      exact ⟨(T.r (T.r T.e q0) T.e), (Steps.refl _), (Steps.refl _)⟩
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
        have e0 := T.v.inj he
        cases e0
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
    | @underV _ t1 h1 =>
      cases h1 with
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
          cases e0
        · rw [ho]
          cases he
        · rw [ho]
          have e0 := (T.r.inj he).1
          have e1 := (T.r.inj he).2
          subst x0
          exact ⟨T.e, (Steps.cons (Step.leftR T.e (Step.root (Root.r6 ))) (Steps.cons (Step.root (Root.r6 )) (Steps.refl _))), (Steps.cons (Step.root (Root.r8 T.e)) (Steps.cons (Step.underV (Step.root (Root.r7 ))) (Steps.cons (Step.root (Root.r7 )) (Steps.refl _))))⟩
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          have e0 := (T.r.inj he).1
          have e1 := (T.r.inj he).2
          cases e0
        · rw [ho]
          have e0 := (T.r.inj he).1
          have e1 := (T.r.inj he).2
          subst x0
          exact ⟨T.e, (Steps.cons (Step.leftR T.e (Step.root (Root.r10 q0))) (Steps.cons (Step.root (Root.r6 )) (Steps.refl _))), (Steps.cons (Step.root (Root.r8 T.e)) (Steps.cons (Step.underV (Step.root (Root.r7 ))) (Steps.cons (Step.root (Root.r7 )) (Steps.refl _))))⟩
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
      | @leftR _ t2 _ h2 =>
        cases h2 with
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
      | @rightR _ _ t2 h2 =>
        exact ⟨(T.r (T.r T.e t2) T.e), (Steps.cons (Step.leftR T.e (Step.rightR T.e h2)) (Steps.refl _)), (Steps.cons (Step.root (Root.r16 t2)) (Steps.refl _))⟩
  | @right _ _ t0 h0 =>
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
end submission.Austin18212

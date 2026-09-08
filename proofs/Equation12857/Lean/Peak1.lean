import Basic
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace Austin12857
open T
theorem peak1 (x0 : T) {u : T} (h : Step (m x0 x0) u) : Join (s x0) u := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst x0
      exact ⟨(s q0), (Steps.refl _), (Steps.refl _)⟩
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst x0
      have cycle := congrArg size e1
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst x0
      have cycle := congrArg size e1
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst x0
      cases e1
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst x0
      have e2 := (T.m.inj e1).1
      have e3 := (T.m.inj e1).2
      have e4 := (T.m.inj e3).1
      have e5 := (T.m.inj e3).2
      have e6 := e4.symm
      subst q0
      cases e5
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst x0
      cases e1
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst x0
      cases e1
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst x0
      have e2 := (T.m.inj e1).1
      have e3 := (T.m.inj e1).2
      cases e3
    · rw [ho]
      cases he
  | @left _ t0 _ h0 =>
    exact ⟨(s t0), (Steps.cons (Step.underS h0) (Steps.refl _)), (Steps.cons (Step.right t0 h0) (Steps.cons (Step.root (Root.r1 t0)) (Steps.refl _)))⟩
  | @right _ _ t0 h0 =>
    exact ⟨(s t0), (Steps.cons (Step.underS h0) (Steps.refl _)), (Steps.cons (Step.left t0 h0) (Steps.cons (Step.root (Root.r1 t0)) (Steps.refl _)))⟩
end Austin12857

import Lean.Elab.Tactic.Omega
import JudgeProblem


set_option autoImplicit false
namespace submission.Austin12857
inductive T where
  | a : T
  | b : T
  | s : T → T
  | m : T → T → T
  deriving DecidableEq
open T
@[simp] def size : T → Nat
  | a => 1
  | b => 1
  | s x => size x + 1
  | m x y => size x + size y + 1
theorem size_pos (x : T) : 0 < size x := by
  cases x <;> simp only [size] <;> omega
inductive Root : T → T → Prop where
  | r1 (x) : Root (m x x) (s x)
  | r2 (x y z) : Root (m x (m (m y (m x (s z))) x)) y
  | r3 (x y) : Root (m x (m (s (m x (s y))) x)) (m x (s y))
  | r4 (x y) : Root (m (s x) (m (m y (s (s x))) (s x))) y
  | r5 (x y z) : Root (m (m x (m (s y) (s z))) (m x (m x (m (s y) (s z))))) (s y)
  | r6 (x y) : Root (m (s x) (m (s y) (s x))) (m (s x) (s (s y)))
  | r7 (x) : Root (s (s (s (s x)))) (s x)
  | r8 (x y) : Root (m (s (s (s x))) (m (m y (s x)) (s (s (s x))))) y
  | r9 (x y) : Root (m (m x (s y)) (m x (m x (s y)))) (s (s (s y)))
  | r10 (x y) : Root (s (m (s x) (s y))) (s (s (s y)))
inductive Step : T → T → Prop where
  | root {x y} : Root x y → Step x y
  | underS {x y} : Step x y → Step (s x) (s y)
  | left {x y} (z) : Step x y → Step (m x z) (m y z)
  | right (x) {y z} : Step y z → Step (m x y) (m x z)
inductive Steps : T → T → Prop where
  | refl (x) : Steps x x
  | cons {x y z} : Step x y → Steps y z → Steps x z
namespace Steps
 theorem single {x y} (h : Step x y) : Steps x y := .cons h (.refl _)
 theorem trans {x y z} (h : Steps x y) (k : Steps y z) : Steps x z := by
  induction h with
  | refl => exact k
  | cons h _ ih => exact .cons h (ih k)
 theorem underS {x y} (h : Steps x y) : Steps (s x) (s y) := by
  induction h with
  | refl => exact .refl _
  | cons h _ ih => exact .cons (.underS h) ih
 theorem left {x y} (z) (h : Steps x y) : Steps (m x z) (m y z) := by
  induction h with
  | refl => exact .refl _
  | cons h _ ih => exact .cons (.left z h) ih
 theorem right (x) {y z} (h : Steps y z) : Steps (m x y) (m x z) := by
  induction h with
  | refl => exact .refl _
  | cons h _ ih => exact .cons (.right x h) ih
 theorem both {x y u v} (h : Steps x y) (k : Steps u v) : Steps (m x u) (m y v) :=
  (left u h).trans (right y k)
end Steps
def Join (x y : T) : Prop := ∃ z, Steps x z ∧ Steps y z
namespace Join
 theorem symm {x y} (h : Join x y) : Join y x := by
  obtain ⟨z,h,k⟩ := h
  exact ⟨z,k,h⟩
 theorem underS {x y} (h : Join x y) : Join (s x) (s y) := by
  obtain ⟨z,h,k⟩ := h
  exact ⟨s z,h.underS,k.underS⟩
 theorem left {x y} (z) (h : Join x y) : Join (m x z) (m y z) := by
  obtain ⟨w,h,k⟩ := h
  exact ⟨m w z,h.left z,k.left z⟩
 theorem right (x) {y z} (h : Join y z) : Join (m x y) (m x z) := by
  obtain ⟨w,h,k⟩ := h
  exact ⟨m x w,h.right x,k.right x⟩
end Join
theorem root_decreases {x y} (h : Root x y) : size y < size x := by
  cases h <;> simp only [size]
  all_goals first | omega | (rename_i x; have hp := size_pos x; omega)
theorem step_decreases {x y} (h : Step x y) : size y < size x := by
  induction h with
  | root h => exact root_decreases h
  | underS _ ih => simp only [size]; omega
  | left _ _ ih => simp only [size]; omega
  | right _ _ ih => simp only [size]; omega
theorem root_cases {u v : T} (h : Root u v) :
    (∃ v0, u = (m v0 v0) ∧ v = (s v0)) ∨
    (∃ v0 v1 v2, u = (m v0 (m (m v1 (m v0 (s v2))) v0)) ∧ v = v1) ∨
    (∃ v0 v1, u = (m v0 (m (s (m v0 (s v1))) v0)) ∧ v = (m v0 (s v1))) ∨
    (∃ v0 v1, u = (m (s v0) (m (m v1 (s (s v0))) (s v0))) ∧ v = v1) ∨
    (∃ v0 v1 v2, u = (m (m v0 (m (s v1) (s v2))) (m v0 (m v0 (m (s v1) (s v2))))) ∧ v = (s v1)) ∨
    (∃ v0 v1, u = (m (s v0) (m (s v1) (s v0))) ∧ v = (m (s v0) (s (s v1)))) ∨
    (∃ v0, u = (s (s (s (s v0)))) ∧ v = (s v0)) ∨
    (∃ v0 v1, u = (m (s (s (s v0))) (m (m v1 (s v0)) (s (s (s v0))))) ∧ v = v1) ∨
    (∃ v0 v1, u = (m (m v0 (s v1)) (m v0 (m v0 (s v1)))) ∧ v = (s (s (s v1)))) ∨
    (∃ v0 v1, u = (s (m (s v0) (s v1))) ∧ v = (s (s (s v1)))) := by
  cases h with
  | r1 => exact (Or.inl ⟨_, rfl, rfl⟩)
  | r2 => exact (Or.inr (Or.inl ⟨_, _, _, rfl, rfl⟩))
  | r3 => exact (Or.inr (Or.inr (Or.inl ⟨_, _, rfl, rfl⟩)))
  | r4 => exact (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, rfl, rfl⟩))))
  | r5 => exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, rfl, rfl⟩)))))
  | r6 => exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, rfl, rfl⟩))))))
  | r7 => exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl, rfl⟩)))))))
  | r8 => exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, rfl, rfl⟩))))))))
  | r9 => exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, rfl, rfl⟩)))))))))
  | r10 => exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨_, _, rfl, rfl⟩)))))))))
end submission.Austin12857

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin12857
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
end submission.Austin12857

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin12857
open T
theorem peak2 (x0 : T) (x1 : T) (x2 : T) {u : T} (h : Step (m x0 (m (m x1 (m x0 (s x2))) x0)) u) : Join x1 u := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst x0
      have e2 := e1.symm
      have cycle := congrArg size e2
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst x0
      have e2 := (T.m.inj e1).1
      have e3 := (T.m.inj e1).2
      have e4 := (T.m.inj e2).1
      have e5 := (T.m.inj e2).2
      subst x1
      have e6 := (T.m.inj e5).1
      have e7 := (T.m.inj e5).2
      have e8 := T.s.inj e7
      subst x2
      exact ⟨q1, (Steps.refl _), (Steps.refl _)⟩
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst x0
      have e2 := (T.m.inj e1).1
      have e3 := (T.m.inj e1).2
      cases e2
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst x0
      have e2 := (T.m.inj e1).1
      have e3 := (T.m.inj e1).2
      have e4 := (T.m.inj e2).1
      have e5 := (T.m.inj e2).2
      subst x1
      cases e5
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst x0
      have e2 := (T.m.inj e1).1
      have e3 := (T.m.inj e1).2
      have e4 := e2.symm
      have cycle := congrArg size e4
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst x0
      have e2 := (T.m.inj e1).1
      have e3 := (T.m.inj e1).2
      cases e2
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst x0
      have e2 := (T.m.inj e1).1
      have e3 := (T.m.inj e1).2
      have e4 := (T.m.inj e2).1
      have e5 := (T.m.inj e2).2
      subst x1
      cases e5
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst x0
      have e2 := (T.m.inj e1).1
      have e3 := (T.m.inj e1).2
      have e4 := e2.symm
      have cycle := congrArg size e4
      simp only [size] at cycle
      omega
    · rw [ho]
      cases he
  | @left _ t0 _ h0 =>
    exact ⟨x1, (Steps.refl _), (Steps.cons (Step.right t0 (Step.left x0 (Step.right x1 (Step.left (s x2) h0)))) (Steps.cons (Step.right t0 (Step.right (m x1 (m t0 (s x2))) h0)) (Steps.cons (Step.root (Root.r2 t0 x1 x2)) (Steps.refl _))))⟩
  | @right _ _ t0 h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩
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
        have e2 := e0.symm
        subst q0
        have cycle := congrArg size e1
        simp only [size] at cycle
        omega
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
        have e2 := (T.m.inj e0).1
        have e3 := (T.m.inj e0).2
        subst x0
        subst x1
        have e4 := (T.m.inj e3).1
        have e5 := (T.m.inj e3).2
        cases e4
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
        have e2 := (T.m.inj e0).1
        have e3 := (T.m.inj e0).2
        subst x0
        subst x1
        cases e3
      · rw [ho]
        cases he
    | @left _ t1 _ h1 =>
      cases h1 with
      | root hr =>
        rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩
        · rw [ho]
          have e0 := (T.m.inj he).1
          have e1 := (T.m.inj he).2
          subst x1
          have e2 := e1.symm
          subst q0
          exact ⟨(m x0 (s x2)), (Steps.refl _), (Steps.cons (Step.root (Root.r3 x0 x2)) (Steps.refl _))⟩
        · rw [ho]
          have e0 := (T.m.inj he).1
          have e1 := (T.m.inj he).2
          subst x1
          have e2 := (T.m.inj e1).1
          have e3 := (T.m.inj e1).2
          subst x0
          have e4 := e3.symm
          subst q0
          exact ⟨(s x2), (Steps.refl _), (Steps.cons (Step.root (Root.r5 q1 x2 q2)) (Steps.refl _))⟩
        · rw [ho]
          have e0 := (T.m.inj he).1
          have e1 := (T.m.inj he).2
          subst x1
          have e2 := (T.m.inj e1).1
          have e3 := (T.m.inj e1).2
          subst x0
          have e4 := e3.symm
          subst q0
          exact ⟨(s x2), (Steps.refl _), (Steps.cons (Step.left (m (m (s x2) (s q1)) (s (m (s x2) (s q1)))) (Step.root (Root.r10 x2 q1))) (Steps.cons (Step.right (s (s (s q1))) (Step.right (m (s x2) (s q1)) (Step.root (Root.r10 x2 q1)))) (Steps.cons (Step.root (Root.r8 q1 (s x2))) (Steps.refl _))))⟩
        · rw [ho]
          have e0 := (T.m.inj he).1
          have e1 := (T.m.inj he).2
          subst x1
          have e2 := (T.m.inj e1).1
          have e3 := (T.m.inj e1).2
          subst x0
          have e4 := T.s.inj e3
          subst x2
          exact ⟨(s q0), (Steps.refl _), (Steps.cons (Step.root (Root.r9 q1 (s q0))) (Steps.cons (Step.root (Root.r7 q0)) (Steps.refl _)))⟩
        · rw [ho]
          have e0 := (T.m.inj he).1
          have e1 := (T.m.inj he).2
          subst x1
          have e2 := (T.m.inj e1).1
          have e3 := (T.m.inj e1).2
          subst x0
          cases e3
        · rw [ho]
          have e0 := (T.m.inj he).1
          have e1 := (T.m.inj he).2
          subst x1
          have e2 := (T.m.inj e1).1
          have e3 := (T.m.inj e1).2
          subst x0
          have e4 := T.s.inj e3
          subst x2
          exact ⟨(s q0), (Steps.refl _), (Steps.cons (Step.root (Root.r4 q1 (s q0))) (Steps.refl _))⟩
        · rw [ho]
          cases he
        · rw [ho]
          have e0 := (T.m.inj he).1
          have e1 := (T.m.inj he).2
          subst x1
          have e2 := (T.m.inj e1).1
          have e3 := (T.m.inj e1).2
          subst x0
          have e4 := T.s.inj e3
          subst x2
          exact ⟨(s (s (s q0))), (Steps.refl _), (Steps.cons (Step.root (Root.r9 q1 q0)) (Steps.refl _))⟩
        · rw [ho]
          have e0 := (T.m.inj he).1
          have e1 := (T.m.inj he).2
          subst x1
          have e2 := (T.m.inj e1).1
          have e3 := (T.m.inj e1).2
          subst x0
          cases e3
        · rw [ho]
          cases he
      | @left _ t2 _ h2 =>
        exact ⟨t2, (Steps.cons h2 (Steps.refl _)), (Steps.cons (Step.root (Root.r2 x0 t2 x2)) (Steps.refl _))⟩
      | @right _ _ t2 h2 =>
        cases h2 with
        | root hr =>
          rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩
          · rw [ho]
            have e0 := (T.m.inj he).1
            have e1 := (T.m.inj he).2
            subst x0
            have e2 := e1.symm
            subst q0
            exact ⟨x1, (Steps.refl _), (Steps.cons (Step.root (Root.r4 x2 x1)) (Steps.refl _))⟩
          · rw [ho]
            have e0 := (T.m.inj he).1
            have e1 := (T.m.inj he).2
            subst x0
            cases e1
          · rw [ho]
            have e0 := (T.m.inj he).1
            have e1 := (T.m.inj he).2
            subst x0
            cases e1
          · rw [ho]
            have e0 := (T.m.inj he).1
            have e1 := (T.m.inj he).2
            subst x0
            cases e1
          · rw [ho]
            have e0 := (T.m.inj he).1
            have e1 := (T.m.inj he).2
            subst x0
            cases e1
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
            cases e1
          · rw [ho]
            cases he
        | @left _ t3 _ h3 =>
          exact ⟨x1, (Steps.refl _), (Steps.cons (Step.left (m (m x1 (m t3 (s x2))) x0) h3) (Steps.cons (Step.right t3 (Step.right (m x1 (m t3 (s x2))) h3)) (Steps.cons (Step.root (Root.r2 t3 x1 x2)) (Steps.refl _))))⟩
        | @right _ _ t3 h3 =>
          cases h3 with
          | root hr =>
            rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩
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
              have e0 := T.s.inj he
              subst x2
              exact ⟨x1, (Steps.refl _), (Steps.cons (Step.root (Root.r2 x0 x1 q0)) (Steps.refl _))⟩
            · rw [ho]
              cases he
            · rw [ho]
              cases he
            · rw [ho]
              have e0 := T.s.inj he
              subst x2
              exact ⟨x1, (Steps.refl _), (Steps.cons (Step.root (Root.r2 x0 x1 (s (s q1)))) (Steps.refl _))⟩
          | @underS _ t4 h4 =>
            exact ⟨x1, (Steps.refl _), (Steps.cons (Step.root (Root.r2 x0 x1 t4)) (Steps.refl _))⟩
    | @right _ _ t1 h1 =>
      exact ⟨x1, (Steps.refl _), (Steps.cons (Step.left (m (m x1 (m x0 (s x2))) t1) h1) (Steps.cons (Step.right t1 (Step.left t1 (Step.right x1 (Step.left (s x2) h1)))) (Steps.cons (Step.root (Root.r2 t1 x1 x2)) (Steps.refl _))))⟩
end submission.Austin12857

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin12857
open T
theorem peak3 (x0 : T) (x1 : T) {u : T} (h : Step (m x0 (m (s (m x0 (s x1))) x0)) u) : Join (m x0 (s x1)) u := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst x0
      have e2 := e1.symm
      have cycle := congrArg size e2
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst x0
      have e2 := (T.m.inj e1).1
      have e3 := (T.m.inj e1).2
      cases e2
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst x0
      have e2 := (T.m.inj e1).1
      have e3 := (T.m.inj e1).2
      have e4 := T.s.inj e2
      have e5 := (T.m.inj e4).1
      have e6 := (T.m.inj e4).2
      have e7 := T.s.inj e6
      subst x1
      exact ⟨(m q0 (s q1)), (Steps.refl _), (Steps.refl _)⟩
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst x0
      have e2 := (T.m.inj e1).1
      have e3 := (T.m.inj e1).2
      cases e2
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst x0
      have e2 := (T.m.inj e1).1
      have e3 := (T.m.inj e1).2
      have e4 := e2.symm
      have cycle := congrArg size e4
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst x0
      have e2 := (T.m.inj e1).1
      have e3 := (T.m.inj e1).2
      have e4 := T.s.inj e2
      have e5 := e4.symm
      subst q1
      exact ⟨(m (s q0) (s x1)), (Steps.refl _), (Steps.cons (Step.right (s q0) (Step.underS (Step.root (Root.r10 q0 x1)))) (Steps.cons (Step.right (s q0) (Step.root (Root.r7 x1))) (Steps.refl _)))⟩
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst x0
      have e2 := (T.m.inj e1).1
      have e3 := (T.m.inj e1).2
      cases e2
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst x0
      have e2 := (T.m.inj e1).1
      have e3 := (T.m.inj e1).2
      have e4 := e2.symm
      have cycle := congrArg size e4
      simp only [size] at cycle
      omega
    · rw [ho]
      cases he
  | @left _ t0 _ h0 =>
    exact ⟨(m t0 (s x1)), (Steps.cons (Step.left (s x1) h0) (Steps.refl _)), (Steps.cons (Step.right t0 (Step.left x0 (Step.underS (Step.left (s x1) h0)))) (Steps.cons (Step.right t0 (Step.right (s (m t0 (s x1))) h0)) (Steps.cons (Step.root (Root.r3 t0 x1)) (Steps.refl _))))⟩
  | @right _ _ t0 h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩
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
        have e2 := e0.symm
        subst q0
        have cycle := congrArg size e1
        simp only [size] at cycle
        omega
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
        have e2 := T.s.inj e0
        subst x0
        have e3 := e2.symm
        have cycle := congrArg size e3
        simp only [size] at cycle
        omega
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        cases e0
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        have e2 := T.s.inj e0
        subst x0
        have e3 := e2.symm
        have cycle := congrArg size e3
        simp only [size] at cycle
        omega
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        have e2 := T.s.inj e0
        subst x0
        cases e2
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        cases e0
      · rw [ho]
        cases he
    | @left _ t1 _ h1 =>
      cases h1 with
      | root hr =>
        rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩
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
          have e0 := T.s.inj he
          cases e0
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          have e0 := T.s.inj he
          have e1 := (T.m.inj e0).1
          have e2 := (T.m.inj e0).2
          subst x0
          have e3 := T.s.inj e2
          subst x1
          exact ⟨(m (s q0) (s q1)), (Steps.refl _), (Steps.cons (Step.root (Root.r6 q0 (s (s q1)))) (Steps.cons (Step.right (s q0) (Step.root (Root.r7 q1))) (Steps.refl _)))⟩
      | @underS _ t2 h2 =>
        cases h2 with
        | root hr =>
          rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩
          · rw [ho]
            have e0 := (T.m.inj he).1
            have e1 := (T.m.inj he).2
            subst x0
            have e2 := e1.symm
            subst q0
            exact ⟨(s (s x1)), (Steps.cons (Step.root (Root.r1 (s x1))) (Steps.refl _)), (Steps.cons (Step.root (Root.r6 x1 (s (s x1)))) (Steps.cons (Step.right (s x1) (Step.root (Root.r7 x1))) (Steps.cons (Step.root (Root.r1 (s x1))) (Steps.refl _))))⟩
          · rw [ho]
            have e0 := (T.m.inj he).1
            have e1 := (T.m.inj he).2
            subst x0
            cases e1
          · rw [ho]
            have e0 := (T.m.inj he).1
            have e1 := (T.m.inj he).2
            subst x0
            cases e1
          · rw [ho]
            have e0 := (T.m.inj he).1
            have e1 := (T.m.inj he).2
            subst x0
            cases e1
          · rw [ho]
            have e0 := (T.m.inj he).1
            have e1 := (T.m.inj he).2
            subst x0
            cases e1
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
            cases e1
          · rw [ho]
            cases he
        | @left _ t3 _ h3 =>
          exact ⟨(m t3 (s x1)), (Steps.cons (Step.left (s x1) h3) (Steps.refl _)), (Steps.cons (Step.left (m (s (m t3 (s x1))) x0) h3) (Steps.cons (Step.right t3 (Step.right (s (m t3 (s x1))) h3)) (Steps.cons (Step.root (Root.r3 t3 x1)) (Steps.refl _))))⟩
        | @right _ _ t3 h3 =>
          cases h3 with
          | root hr =>
            rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩
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
              have e0 := T.s.inj he
              subst x1
              exact ⟨(m x0 (s q0)), (Steps.cons (Step.right x0 (Step.root (Root.r7 q0))) (Steps.refl _)), (Steps.cons (Step.root (Root.r3 x0 q0)) (Steps.refl _))⟩
            · rw [ho]
              cases he
            · rw [ho]
              cases he
            · rw [ho]
              have e0 := T.s.inj he
              subst x1
              exact ⟨(m x0 (s (s (s q1)))), (Steps.cons (Step.right x0 (Step.root (Root.r10 q0 q1))) (Steps.refl _)), (Steps.cons (Step.root (Root.r3 x0 (s (s q1)))) (Steps.refl _))⟩
          | @underS _ t4 h4 =>
            exact ⟨(m x0 (s t4)), (Steps.cons (Step.right x0 (Step.underS h4)) (Steps.refl _)), (Steps.cons (Step.root (Root.r3 x0 t4)) (Steps.refl _))⟩
    | @right _ _ t1 h1 =>
      exact ⟨(m t1 (s x1)), (Steps.cons (Step.left (s x1) h1) (Steps.refl _)), (Steps.cons (Step.left (m (s (m x0 (s x1))) t1) h1) (Steps.cons (Step.right t1 (Step.left t1 (Step.underS (Step.left (s x1) h1)))) (Steps.cons (Step.root (Root.r3 t1 x1)) (Steps.refl _))))⟩
end submission.Austin12857

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin12857
open T
theorem peak4 (x0 : T) (x1 : T) {u : T} (h : Step (m (s x0) (m (m x1 (s (s x0))) (s x0))) u) : Join x1 u := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst q0
      cases e1
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst q0
      have e3 := (T.m.inj e1).1
      have e4 := (T.m.inj e1).2
      have e5 := (T.m.inj e3).1
      have e6 := (T.m.inj e3).2
      subst x1
      cases e6
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst q0
      have e3 := (T.m.inj e1).1
      have e4 := (T.m.inj e1).2
      cases e3
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := T.s.inj e0
      have e3 := (T.m.inj e1).1
      have e4 := (T.m.inj e1).2
      subst x0
      have e5 := (T.m.inj e3).1
      have e6 := (T.m.inj e3).2
      subst x1
      exact ⟨q1, (Steps.refl _), (Steps.refl _)⟩
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      cases e0
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := T.s.inj e0
      have e3 := (T.m.inj e1).1
      have e4 := (T.m.inj e1).2
      subst x0
      cases e3
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := T.s.inj e0
      have e3 := (T.m.inj e1).1
      have e4 := (T.m.inj e1).2
      subst x0
      have e5 := (T.m.inj e3).1
      have e6 := (T.m.inj e3).2
      subst x1
      have e7 := T.s.inj e6
      have e8 := e7.symm
      have cycle := congrArg size e8
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      cases e0
    · rw [ho]
      cases he
  | @left _ t0 _ h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩
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
        have e0 := T.s.inj he
        subst x0
        exact ⟨x1, (Steps.refl _), (Steps.cons (Step.right (s q0) (Step.left (s (s (s (s q0)))) (Step.right x1 (Step.root (Root.r7 (s q0)))))) (Steps.cons (Step.right (s q0) (Step.right (m x1 (s (s q0))) (Step.root (Root.r7 q0)))) (Steps.cons (Step.root (Root.r4 q0 x1)) (Steps.refl _))))⟩
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := T.s.inj he
        subst x0
        exact ⟨x1, (Steps.refl _), (Steps.cons (Step.right (s (s (s q1))) (Step.left (s (m (s q0) (s q1))) (Step.right x1 (Step.underS (Step.root (Root.r10 q0 q1)))))) (Steps.cons (Step.right (s (s (s q1))) (Step.left (s (m (s q0) (s q1))) (Step.right x1 (Step.root (Root.r7 q1))))) (Steps.cons (Step.right (s (s (s q1))) (Step.right (m x1 (s q1)) (Step.root (Root.r10 q0 q1)))) (Steps.cons (Step.root (Root.r8 q1 x1)) (Steps.refl _)))))⟩
    | @underS _ t1 h1 =>
      exact ⟨x1, (Steps.refl _), (Steps.cons (Step.right (s t1) (Step.left (s x0) (Step.right x1 (Step.underS (Step.underS h1))))) (Steps.cons (Step.right (s t1) (Step.right (m x1 (s (s t1))) (Step.underS h1))) (Steps.cons (Step.root (Root.r4 t1 x1)) (Steps.refl _))))⟩
  | @right _ _ t0 h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        have e2 := e0.symm
        subst q0
        cases e1
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        have e2 := e0.symm
        subst q0
        cases e1
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
        have e2 := (T.m.inj e0).1
        have e3 := (T.m.inj e0).2
        cases e1
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
        have e2 := (T.m.inj e0).1
        have e3 := (T.m.inj e0).2
        cases e1
      · rw [ho]
        cases he
    | @left _ t1 _ h1 =>
      cases h1 with
      | root hr =>
        rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩
        · rw [ho]
          have e0 := (T.m.inj he).1
          have e1 := (T.m.inj he).2
          subst x1
          have e2 := e1.symm
          subst q0
          exact ⟨(s (s x0)), (Steps.refl _), (Steps.cons (Step.root (Root.r6 x0 (s (s x0)))) (Steps.cons (Step.right (s x0) (Step.root (Root.r7 x0))) (Steps.cons (Step.root (Root.r1 (s x0))) (Steps.refl _))))⟩
        · rw [ho]
          have e0 := (T.m.inj he).1
          have e1 := (T.m.inj he).2
          subst x1
          cases e1
        · rw [ho]
          have e0 := (T.m.inj he).1
          have e1 := (T.m.inj he).2
          subst x1
          cases e1
        · rw [ho]
          have e0 := (T.m.inj he).1
          have e1 := (T.m.inj he).2
          subst x1
          cases e1
        · rw [ho]
          have e0 := (T.m.inj he).1
          have e1 := (T.m.inj he).2
          subst x1
          cases e1
        · rw [ho]
          have e0 := (T.m.inj he).1
          have e1 := (T.m.inj he).2
          subst x1
          cases e1
        · rw [ho]
          cases he
        · rw [ho]
          have e0 := (T.m.inj he).1
          have e1 := (T.m.inj he).2
          subst x1
          cases e1
        · rw [ho]
          have e0 := (T.m.inj he).1
          have e1 := (T.m.inj he).2
          subst x1
          cases e1
        · rw [ho]
          cases he
      | @left _ t2 _ h2 =>
        exact ⟨t2, (Steps.cons h2 (Steps.refl _)), (Steps.cons (Step.root (Root.r4 x0 t2)) (Steps.refl _))⟩
      | @right _ _ t2 h2 =>
        cases h2 with
        | root hr =>
          rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩
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
            have e0 := T.s.inj he
            have e1 := T.s.inj e0
            subst x0
            exact ⟨x1, (Steps.refl _), (Steps.cons (Step.root (Root.r8 q0 x1)) (Steps.refl _))⟩
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            have e0 := T.s.inj he
            cases e0
        | @underS _ t3 h3 =>
          cases h3 with
          | root hr =>
            rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩
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
              have e0 := T.s.inj he
              subst x0
              exact ⟨x1, (Steps.refl _), (Steps.cons (Step.root (Root.r8 (s q0) x1)) (Steps.refl _))⟩
            · rw [ho]
              cases he
            · rw [ho]
              cases he
            · rw [ho]
              have e0 := T.s.inj he
              subst x0
              exact ⟨x1, (Steps.refl _), (Steps.cons (Step.left (m (m x1 (s (s (s (s q1))))) (s (m (s q0) (s q1)))) (Step.root (Root.r10 q0 q1))) (Steps.cons (Step.right (s (s (s q1))) (Step.left (s (m (s q0) (s q1))) (Step.right x1 (Step.root (Root.r7 q1))))) (Steps.cons (Step.right (s (s (s q1))) (Step.right (m x1 (s q1)) (Step.root (Root.r10 q0 q1)))) (Steps.cons (Step.root (Root.r8 q1 x1)) (Steps.refl _)))))⟩
          | @underS _ t4 h4 =>
            exact ⟨x1, (Steps.refl _), (Steps.cons (Step.left (m (m x1 (s (s t4))) (s x0)) (Step.underS h4)) (Steps.cons (Step.right (s t4) (Step.right (m x1 (s (s t4))) (Step.underS h4))) (Steps.cons (Step.root (Root.r4 t4 x1)) (Steps.refl _))))⟩
    | @right _ _ t1 h1 =>
      cases h1 with
      | root hr =>
        rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩
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
          have e0 := T.s.inj he
          subst x0
          exact ⟨x1, (Steps.refl _), (Steps.cons (Step.left (m (m x1 (s (s (s (s (s q0)))))) (s q0)) (Step.root (Root.r7 q0))) (Steps.cons (Step.right (s q0) (Step.left (s q0) (Step.right x1 (Step.root (Root.r7 (s q0)))))) (Steps.cons (Step.root (Root.r4 q0 x1)) (Steps.refl _))))⟩
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          have e0 := T.s.inj he
          subst x0
          exact ⟨x1, (Steps.refl _), (Steps.cons (Step.left (m (m x1 (s (s (m (s q0) (s q1))))) (s (s (s q1)))) (Step.root (Root.r10 q0 q1))) (Steps.cons (Step.right (s (s (s q1))) (Step.left (s (s (s q1))) (Step.right x1 (Step.underS (Step.root (Root.r10 q0 q1)))))) (Steps.cons (Step.root (Root.r4 (s (s q1)) x1)) (Steps.refl _))))⟩
      | @underS _ t2 h2 =>
        exact ⟨x1, (Steps.refl _), (Steps.cons (Step.left (m (m x1 (s (s x0))) (s t2)) (Step.underS h2)) (Steps.cons (Step.right (s t2) (Step.left (s t2) (Step.right x1 (Step.underS (Step.underS h2))))) (Steps.cons (Step.root (Root.r4 t2 x1)) (Steps.refl _))))⟩
end submission.Austin12857

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin12857
open T
theorem peak5 (x0 : T) (x1 : T) (x2 : T) {u : T} (h : Step (m (m x0 (m (s x1) (s x2))) (m x0 (m x0 (m (s x1) (s x2))))) u) : Join (s x1) u := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst q0
      have e3 := (T.m.inj e1).1
      have e4 := (T.m.inj e1).2
      have e5 := (T.m.inj e4).1
      have e6 := (T.m.inj e4).2
      subst x0
      cases e6
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst q0
      have e3 := (T.m.inj e1).1
      have e4 := (T.m.inj e1).2
      have cycle := congrArg size e3
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst q0
      have e3 := (T.m.inj e1).1
      have e4 := (T.m.inj e1).2
      have cycle := congrArg size e3
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      cases e0
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := (T.m.inj e0).1
      have e3 := (T.m.inj e0).2
      have e4 := (T.m.inj e1).1
      have e5 := (T.m.inj e1).2
      subst x0
      have e6 := (T.m.inj e3).1
      have e7 := (T.m.inj e3).2
      have e8 := (T.m.inj e5).1
      have e9 := (T.m.inj e5).2
      have e10 := T.s.inj e6
      have e11 := T.s.inj e7
      have e12 := (T.m.inj e9).1
      have e13 := (T.m.inj e9).2
      subst x1
      subst x2
      exact ⟨(s q1), (Steps.refl _), (Steps.refl _)⟩
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
      have e2 := (T.m.inj e0).1
      have e3 := (T.m.inj e0).2
      have e4 := (T.m.inj e1).1
      have e5 := (T.m.inj e1).2
      subst x0
      cases e3
    · rw [ho]
      cases he
  | @left _ t0 _ h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        have e2 := e1.symm
        subst q0
        exact ⟨(s x1), (Steps.refl _), (Steps.cons (Step.left (m (m (s x1) (s x2)) (m (m (s x1) (s x2)) (m (s x1) (s x2)))) (Step.root (Root.r10 x1 x2))) (Steps.cons (Step.right (s (s (s x2))) (Step.right (m (s x1) (s x2)) (Step.root (Root.r1 (m (s x1) (s x2)))))) (Steps.cons (Step.right (s (s (s x2))) (Step.right (m (s x1) (s x2)) (Step.root (Root.r10 x1 x2)))) (Steps.cons (Step.root (Root.r8 x2 (s x1))) (Steps.refl _)))))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        have e2 := (T.m.inj e1).1
        have e3 := (T.m.inj e1).2
        cases e2
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        have e2 := (T.m.inj e1).1
        have e3 := (T.m.inj e1).2
        have e4 := T.s.inj e2
        have e5 := e3.symm
        subst q0
        subst x1
        exact ⟨(s (s (s q1))), (Steps.cons (Step.root (Root.r10 x2 q1)) (Steps.refl _)), (Steps.cons (Step.right (m (s x2) (s q1)) (Step.right (s x2) (Step.root (Root.r3 (s x2) q1)))) (Steps.cons (Step.root (Root.r9 (s x2) q1)) (Steps.refl _)))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        have e2 := (T.m.inj e1).1
        have e3 := (T.m.inj e1).2
        cases e2
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        have e2 := (T.m.inj e1).1
        have e3 := (T.m.inj e1).2
        have e4 := e2.symm
        subst q0
        cases e3
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        have e2 := (T.m.inj e1).1
        have e3 := (T.m.inj e1).2
        have e4 := T.s.inj e2
        have e5 := T.s.inj e3
        subst x1
        subst x2
        exact ⟨(s q1), (Steps.refl _), (Steps.cons (Step.right (m (s q0) (s (s q1))) (Step.right (s q0) (Step.root (Root.r6 q0 q1)))) (Steps.cons (Step.root (Root.r9 (s q0) (s q1))) (Steps.cons (Step.root (Root.r7 q1)) (Steps.refl _))))⟩
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        have e2 := (T.m.inj e1).1
        have e3 := (T.m.inj e1).2
        cases e2
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        have e2 := (T.m.inj e1).1
        have e3 := (T.m.inj e1).2
        have e4 := e2.symm
        subst q0
        cases e3
      · rw [ho]
        cases he
    | @left _ t1 _ h1 =>
      exact ⟨(s x1), (Steps.refl _), (Steps.cons (Step.right (m t1 (m (s x1) (s x2))) (Step.left (m x0 (m (s x1) (s x2))) h1)) (Steps.cons (Step.right (m t1 (m (s x1) (s x2))) (Step.right t1 (Step.left (m (s x1) (s x2)) h1))) (Steps.cons (Step.root (Root.r5 t1 x1 x2)) (Steps.refl _))))⟩
    | @right _ _ t1 h1 =>
      cases h1 with
      | root hr =>
        rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩
        · rw [ho]
          have e0 := (T.m.inj he).1
          have e1 := (T.m.inj he).2
          have e2 := e0.symm
          subst q0
          have e3 := T.s.inj e1
          subst x2
          exact ⟨(s x1), (Steps.refl _), (Steps.cons (Step.right (m x0 (s (s x1))) (Step.right x0 (Step.right x0 (Step.root (Root.r1 (s x1)))))) (Steps.cons (Step.root (Root.r9 x0 (s x1))) (Steps.cons (Step.root (Root.r7 x1)) (Steps.refl _))))⟩
        · rw [ho]
          have e0 := (T.m.inj he).1
          have e1 := (T.m.inj he).2
          have e2 := e0.symm
          subst q0
          cases e1
        · rw [ho]
          have e0 := (T.m.inj he).1
          have e1 := (T.m.inj he).2
          have e2 := e0.symm
          subst q0
          cases e1
        · rw [ho]
          have e0 := (T.m.inj he).1
          have e1 := (T.m.inj he).2
          have e2 := T.s.inj e0
          cases e1
        · rw [ho]
          have e0 := (T.m.inj he).1
          have e1 := (T.m.inj he).2
          cases e0
        · rw [ho]
          have e0 := (T.m.inj he).1
          have e1 := (T.m.inj he).2
          have e2 := T.s.inj e0
          cases e1
        · rw [ho]
          cases he
        · rw [ho]
          have e0 := (T.m.inj he).1
          have e1 := (T.m.inj he).2
          have e2 := T.s.inj e0
          cases e1
        · rw [ho]
          have e0 := (T.m.inj he).1
          have e1 := (T.m.inj he).2
          cases e0
        · rw [ho]
          cases he
      | @left _ t2 _ h2 =>
        cases h2 with
        | root hr =>
          rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩
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
            have e0 := T.s.inj he
            subst x1
            exact ⟨(s q0), (Steps.cons (Step.root (Root.r7 q0)) (Steps.refl _)), (Steps.cons (Step.right (m x0 (m (s q0) (s x2))) (Step.right x0 (Step.right x0 (Step.left (s x2) (Step.root (Root.r7 q0)))))) (Steps.cons (Step.root (Root.r5 x0 q0 x2)) (Steps.refl _)))⟩
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            have e0 := T.s.inj he
            subst x1
            exact ⟨(s (s (s q1))), (Steps.cons (Step.root (Root.r10 q0 q1)) (Steps.refl _)), (Steps.cons (Step.right (m x0 (m (s (s (s q1))) (s x2))) (Step.right x0 (Step.right x0 (Step.left (s x2) (Step.root (Root.r10 q0 q1)))))) (Steps.cons (Step.root (Root.r5 x0 (s (s q1)) x2)) (Steps.refl _)))⟩
        | @underS _ t3 h3 =>
          exact ⟨(s t3), (Steps.cons (Step.underS h3) (Steps.refl _)), (Steps.cons (Step.right (m x0 (m (s t3) (s x2))) (Step.right x0 (Step.right x0 (Step.left (s x2) (Step.underS h3))))) (Steps.cons (Step.root (Root.r5 x0 t3 x2)) (Steps.refl _)))⟩
      | @right _ _ t2 h2 =>
        cases h2 with
        | root hr =>
          rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩
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
            have e0 := T.s.inj he
            subst x2
            exact ⟨(s x1), (Steps.refl _), (Steps.cons (Step.right (m x0 (m (s x1) (s q0))) (Step.right x0 (Step.right x0 (Step.right (s x1) (Step.root (Root.r7 q0)))))) (Steps.cons (Step.root (Root.r5 x0 x1 q0)) (Steps.refl _)))⟩
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            have e0 := T.s.inj he
            subst x2
            exact ⟨(s x1), (Steps.refl _), (Steps.cons (Step.right (m x0 (m (s x1) (s (s (s q1))))) (Step.right x0 (Step.right x0 (Step.right (s x1) (Step.root (Root.r10 q0 q1)))))) (Steps.cons (Step.root (Root.r5 x0 x1 (s (s q1)))) (Steps.refl _)))⟩
        | @underS _ t3 h3 =>
          exact ⟨(s x1), (Steps.refl _), (Steps.cons (Step.right (m x0 (m (s x1) (s t3))) (Step.right x0 (Step.right x0 (Step.right (s x1) (Step.underS h3))))) (Steps.cons (Step.root (Root.r5 x0 x1 t3)) (Steps.refl _)))⟩
  | @right _ _ t0 h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        have e2 := e1.symm
        have cycle := congrArg size e2
        simp only [size] at cycle
        omega
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        have e2 := (T.m.inj e1).1
        have e3 := (T.m.inj e1).2
        have cycle := congrArg size e2
        simp only [size] at cycle
        omega
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        have e2 := (T.m.inj e1).1
        have e3 := (T.m.inj e1).2
        have cycle := congrArg size e2
        simp only [size] at cycle
        omega
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        have e2 := (T.m.inj e1).1
        have e3 := (T.m.inj e1).2
        cases e2
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        have e2 := (T.m.inj e1).1
        have e3 := (T.m.inj e1).2
        have e4 := e2.symm
        have cycle := congrArg size e4
        simp only [size] at cycle
        omega
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        have e2 := (T.m.inj e1).1
        have e3 := (T.m.inj e1).2
        have e4 := T.s.inj e2
        cases e3
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        have e2 := (T.m.inj e1).1
        have e3 := (T.m.inj e1).2
        cases e2
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        have e2 := (T.m.inj e1).1
        have e3 := (T.m.inj e1).2
        have e4 := e2.symm
        have cycle := congrArg size e4
        simp only [size] at cycle
        omega
      · rw [ho]
        cases he
    | @left _ t1 _ h1 =>
      exact ⟨(s x1), (Steps.refl _), (Steps.cons (Step.left (m t1 (m x0 (m (s x1) (s x2)))) (Step.left (m (s x1) (s x2)) h1)) (Steps.cons (Step.right (m t1 (m (s x1) (s x2))) (Step.right t1 (Step.left (m (s x1) (s x2)) h1))) (Steps.cons (Step.root (Root.r5 t1 x1 x2)) (Steps.refl _))))⟩
    | @right _ _ t1 h1 =>
      cases h1 with
      | root hr =>
        rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩
        · rw [ho]
          have e0 := (T.m.inj he).1
          have e1 := (T.m.inj he).2
          subst x0
          have e2 := e1.symm
          subst q0
          exact ⟨(s x1), (Steps.refl _), (Steps.cons (Step.left (m (m (s x1) (s x2)) (s (m (s x1) (s x2)))) (Step.root (Root.r1 (m (s x1) (s x2))))) (Steps.cons (Step.left (m (m (s x1) (s x2)) (s (m (s x1) (s x2)))) (Step.root (Root.r10 x1 x2))) (Steps.cons (Step.right (s (s (s x2))) (Step.right (m (s x1) (s x2)) (Step.root (Root.r10 x1 x2)))) (Steps.cons (Step.root (Root.r8 x2 (s x1))) (Steps.refl _)))))⟩
        · rw [ho]
          have e0 := (T.m.inj he).1
          have e1 := (T.m.inj he).2
          subst x0
          have e2 := (T.m.inj e1).1
          have e3 := (T.m.inj e1).2
          cases e2
        · rw [ho]
          have e0 := (T.m.inj he).1
          have e1 := (T.m.inj he).2
          subst x0
          have e2 := (T.m.inj e1).1
          have e3 := (T.m.inj e1).2
          have e4 := T.s.inj e2
          have e5 := e3.symm
          subst q0
          subst x1
          exact ⟨(s (s (s q1))), (Steps.cons (Step.root (Root.r10 x2 q1)) (Steps.refl _)), (Steps.cons (Step.left (m (s x2) (m (s x2) (s q1))) (Step.root (Root.r3 (s x2) q1))) (Steps.cons (Step.root (Root.r9 (s x2) q1)) (Steps.refl _)))⟩
        · rw [ho]
          have e0 := (T.m.inj he).1
          have e1 := (T.m.inj he).2
          subst x0
          have e2 := (T.m.inj e1).1
          have e3 := (T.m.inj e1).2
          cases e2
        · rw [ho]
          have e0 := (T.m.inj he).1
          have e1 := (T.m.inj he).2
          subst x0
          have e2 := (T.m.inj e1).1
          have e3 := (T.m.inj e1).2
          have e4 := e2.symm
          subst q0
          cases e3
        · rw [ho]
          have e0 := (T.m.inj he).1
          have e1 := (T.m.inj he).2
          subst x0
          have e2 := (T.m.inj e1).1
          have e3 := (T.m.inj e1).2
          have e4 := T.s.inj e2
          have e5 := T.s.inj e3
          subst x1
          subst x2
          exact ⟨(s q1), (Steps.refl _), (Steps.cons (Step.left (m (s q0) (m (s q0) (s (s q1)))) (Step.root (Root.r6 q0 q1))) (Steps.cons (Step.root (Root.r9 (s q0) (s q1))) (Steps.cons (Step.root (Root.r7 q1)) (Steps.refl _))))⟩
        · rw [ho]
          cases he
        · rw [ho]
          have e0 := (T.m.inj he).1
          have e1 := (T.m.inj he).2
          subst x0
          have e2 := (T.m.inj e1).1
          have e3 := (T.m.inj e1).2
          cases e2
        · rw [ho]
          have e0 := (T.m.inj he).1
          have e1 := (T.m.inj he).2
          subst x0
          have e2 := (T.m.inj e1).1
          have e3 := (T.m.inj e1).2
          have e4 := e2.symm
          subst q0
          cases e3
        · rw [ho]
          cases he
      | @left _ t2 _ h2 =>
        exact ⟨(s x1), (Steps.refl _), (Steps.cons (Step.left (m x0 (m t2 (m (s x1) (s x2)))) (Step.left (m (s x1) (s x2)) h2)) (Steps.cons (Step.right (m t2 (m (s x1) (s x2))) (Step.left (m t2 (m (s x1) (s x2))) h2)) (Steps.cons (Step.root (Root.r5 t2 x1 x2)) (Steps.refl _))))⟩
      | @right _ _ t2 h2 =>
        cases h2 with
        | root hr =>
          rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩
          · rw [ho]
            have e0 := (T.m.inj he).1
            have e1 := (T.m.inj he).2
            have e2 := e0.symm
            subst q0
            have e3 := T.s.inj e1
            subst x2
            exact ⟨(s x1), (Steps.refl _), (Steps.cons (Step.left (m x0 (m x0 (s (s x1)))) (Step.right x0 (Step.root (Root.r1 (s x1))))) (Steps.cons (Step.root (Root.r9 x0 (s x1))) (Steps.cons (Step.root (Root.r7 x1)) (Steps.refl _))))⟩
          · rw [ho]
            have e0 := (T.m.inj he).1
            have e1 := (T.m.inj he).2
            have e2 := e0.symm
            subst q0
            cases e1
          · rw [ho]
            have e0 := (T.m.inj he).1
            have e1 := (T.m.inj he).2
            have e2 := e0.symm
            subst q0
            cases e1
          · rw [ho]
            have e0 := (T.m.inj he).1
            have e1 := (T.m.inj he).2
            have e2 := T.s.inj e0
            cases e1
          · rw [ho]
            have e0 := (T.m.inj he).1
            have e1 := (T.m.inj he).2
            cases e0
          · rw [ho]
            have e0 := (T.m.inj he).1
            have e1 := (T.m.inj he).2
            have e2 := T.s.inj e0
            cases e1
          · rw [ho]
            cases he
          · rw [ho]
            have e0 := (T.m.inj he).1
            have e1 := (T.m.inj he).2
            have e2 := T.s.inj e0
            cases e1
          · rw [ho]
            have e0 := (T.m.inj he).1
            have e1 := (T.m.inj he).2
            cases e0
          · rw [ho]
            cases he
        | @left _ t3 _ h3 =>
          cases h3 with
          | root hr =>
            rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩
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
              have e0 := T.s.inj he
              subst x1
              exact ⟨(s q0), (Steps.cons (Step.root (Root.r7 q0)) (Steps.refl _)), (Steps.cons (Step.left (m x0 (m x0 (m (s q0) (s x2)))) (Step.right x0 (Step.left (s x2) (Step.root (Root.r7 q0))))) (Steps.cons (Step.root (Root.r5 x0 q0 x2)) (Steps.refl _)))⟩
            · rw [ho]
              cases he
            · rw [ho]
              cases he
            · rw [ho]
              have e0 := T.s.inj he
              subst x1
              exact ⟨(s (s (s q1))), (Steps.cons (Step.root (Root.r10 q0 q1)) (Steps.refl _)), (Steps.cons (Step.left (m x0 (m x0 (m (s (s (s q1))) (s x2)))) (Step.right x0 (Step.left (s x2) (Step.root (Root.r10 q0 q1))))) (Steps.cons (Step.root (Root.r5 x0 (s (s q1)) x2)) (Steps.refl _)))⟩
          | @underS _ t4 h4 =>
            exact ⟨(s t4), (Steps.cons (Step.underS h4) (Steps.refl _)), (Steps.cons (Step.left (m x0 (m x0 (m (s t4) (s x2)))) (Step.right x0 (Step.left (s x2) (Step.underS h4)))) (Steps.cons (Step.root (Root.r5 x0 t4 x2)) (Steps.refl _)))⟩
        | @right _ _ t3 h3 =>
          cases h3 with
          | root hr =>
            rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩
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
              have e0 := T.s.inj he
              subst x2
              exact ⟨(s x1), (Steps.refl _), (Steps.cons (Step.left (m x0 (m x0 (m (s x1) (s q0)))) (Step.right x0 (Step.right (s x1) (Step.root (Root.r7 q0))))) (Steps.cons (Step.root (Root.r5 x0 x1 q0)) (Steps.refl _)))⟩
            · rw [ho]
              cases he
            · rw [ho]
              cases he
            · rw [ho]
              have e0 := T.s.inj he
              subst x2
              exact ⟨(s x1), (Steps.refl _), (Steps.cons (Step.left (m x0 (m x0 (m (s x1) (s (s (s q1)))))) (Step.right x0 (Step.right (s x1) (Step.root (Root.r10 q0 q1))))) (Steps.cons (Step.root (Root.r5 x0 x1 (s (s q1)))) (Steps.refl _)))⟩
          | @underS _ t4 h4 =>
            exact ⟨(s x1), (Steps.refl _), (Steps.cons (Step.left (m x0 (m x0 (m (s x1) (s t4)))) (Step.right x0 (Step.right (s x1) (Step.underS h4)))) (Steps.cons (Step.root (Root.r5 x0 x1 t4)) (Steps.refl _)))⟩
end submission.Austin12857

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin12857
open T
theorem peak6 (x0 : T) (x1 : T) {u : T} (h : Step (m (s x0) (m (s x1) (s x0))) u) : Join (m (s x0) (s (s x1))) u := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst q0
      cases e1
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst q0
      have e3 := (T.m.inj e1).1
      have e4 := (T.m.inj e1).2
      cases e3
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst q0
      have e3 := (T.m.inj e1).1
      have e4 := (T.m.inj e1).2
      have e5 := T.s.inj e3
      subst x1
      exact ⟨(m (s x0) (s q1)), (Steps.cons (Step.right (s x0) (Step.underS (Step.root (Root.r10 x0 q1)))) (Steps.cons (Step.right (s x0) (Step.root (Root.r7 q1))) (Steps.refl _))), (Steps.refl _)⟩
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := T.s.inj e0
      have e3 := (T.m.inj e1).1
      have e4 := (T.m.inj e1).2
      subst x0
      cases e3
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      cases e0
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := T.s.inj e0
      have e3 := (T.m.inj e1).1
      have e4 := (T.m.inj e1).2
      subst x0
      have e5 := T.s.inj e3
      subst x1
      exact ⟨(m (s q0) (s (s q1))), (Steps.refl _), (Steps.refl _)⟩
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := T.s.inj e0
      have e3 := (T.m.inj e1).1
      have e4 := (T.m.inj e1).2
      subst x0
      cases e3
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      cases e0
    · rw [ho]
      cases he
  | @left _ t0 _ h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩
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
        have e0 := T.s.inj he
        subst x0
        exact ⟨(m (s q0) (s (s x1))), (Steps.cons (Step.left (s (s x1)) (Step.root (Root.r7 q0))) (Steps.refl _)), (Steps.cons (Step.right (s q0) (Step.right (s x1) (Step.root (Root.r7 q0)))) (Steps.cons (Step.root (Root.r6 q0 x1)) (Steps.refl _)))⟩
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := T.s.inj he
        subst x0
        exact ⟨(m (s (s (s q1))) (s (s x1))), (Steps.cons (Step.left (s (s x1)) (Step.root (Root.r10 q0 q1))) (Steps.refl _)), (Steps.cons (Step.right (s (s (s q1))) (Step.right (s x1) (Step.root (Root.r10 q0 q1)))) (Steps.cons (Step.root (Root.r6 (s (s q1)) x1)) (Steps.refl _)))⟩
    | @underS _ t1 h1 =>
      exact ⟨(m (s t1) (s (s x1))), (Steps.cons (Step.left (s (s x1)) (Step.underS h1)) (Steps.refl _)), (Steps.cons (Step.right (s t1) (Step.right (s x1) (Step.underS h1))) (Steps.cons (Step.root (Root.r6 t1 x1)) (Steps.refl _)))⟩
  | @right _ _ t0 h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        have e2 := e0.symm
        subst q0
        have e3 := T.s.inj e1
        subst x0
        exact ⟨(m (s x1) (s (s x1))), (Steps.refl _), (Steps.refl _)⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        have e2 := e0.symm
        subst q0
        cases e1
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        have e2 := e0.symm
        subst q0
        cases e1
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        have e2 := T.s.inj e0
        cases e1
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        cases e0
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        have e2 := T.s.inj e0
        cases e1
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        have e2 := T.s.inj e0
        cases e1
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        cases e0
      · rw [ho]
        cases he
    | @left _ t1 _ h1 =>
      cases h1 with
      | root hr =>
        rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩
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
          have e0 := T.s.inj he
          subst x1
          exact ⟨(m (s x0) (s (s q0))), (Steps.cons (Step.right (s x0) (Step.root (Root.r7 (s q0)))) (Steps.refl _)), (Steps.cons (Step.root (Root.r6 x0 q0)) (Steps.refl _))⟩
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          have e0 := T.s.inj he
          subst x1
          exact ⟨(m (s x0) (s q1)), (Steps.cons (Step.right (s x0) (Step.underS (Step.root (Root.r10 q0 q1)))) (Steps.cons (Step.right (s x0) (Step.root (Root.r7 q1))) (Steps.refl _))), (Steps.cons (Step.root (Root.r6 x0 (s (s q1)))) (Steps.cons (Step.right (s x0) (Step.root (Root.r7 q1))) (Steps.refl _)))⟩
      | @underS _ t2 h2 =>
        exact ⟨(m (s x0) (s (s t2))), (Steps.cons (Step.right (s x0) (Step.underS (Step.underS h2))) (Steps.refl _)), (Steps.cons (Step.root (Root.r6 x0 t2)) (Steps.refl _))⟩
    | @right _ _ t1 h1 =>
      cases h1 with
      | root hr =>
        rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩
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
          have e0 := T.s.inj he
          subst x0
          exact ⟨(m (s q0) (s (s x1))), (Steps.cons (Step.left (s (s x1)) (Step.root (Root.r7 q0))) (Steps.refl _)), (Steps.cons (Step.left (m (s x1) (s q0)) (Step.root (Root.r7 q0))) (Steps.cons (Step.root (Root.r6 q0 x1)) (Steps.refl _)))⟩
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          have e0 := T.s.inj he
          subst x0
          exact ⟨(m (s (s (s q1))) (s (s x1))), (Steps.cons (Step.left (s (s x1)) (Step.root (Root.r10 q0 q1))) (Steps.refl _)), (Steps.cons (Step.left (m (s x1) (s (s (s q1)))) (Step.root (Root.r10 q0 q1))) (Steps.cons (Step.root (Root.r6 (s (s q1)) x1)) (Steps.refl _)))⟩
      | @underS _ t2 h2 =>
        exact ⟨(m (s t2) (s (s x1))), (Steps.cons (Step.left (s (s x1)) (Step.underS h2)) (Steps.refl _)), (Steps.cons (Step.left (m (s x1) (s t2)) (Step.underS h2)) (Steps.cons (Step.root (Root.r6 t2 x1)) (Steps.refl _)))⟩
end submission.Austin12857

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin12857
open T
theorem peak7 (x0 : T) {u : T} (h : Step (s (s (s (s x0)))) u) : Join (s x0) u := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩
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
      have e0 := T.s.inj he
      have e1 := T.s.inj e0
      have e2 := T.s.inj e1
      have e3 := T.s.inj e2
      subst x0
      exact ⟨(s q0), (Steps.refl _), (Steps.refl _)⟩
    · rw [ho]
      cases he
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := T.s.inj he
      cases e0
  | @underS _ t0 h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩
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
        have e0 := T.s.inj he
        have e1 := T.s.inj e0
        have e2 := T.s.inj e1
        subst x0
        exact ⟨(s (s q0)), (Steps.refl _), (Steps.refl _)⟩
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := T.s.inj he
        cases e0
    | @underS _ t1 h1 =>
      cases h1 with
      | root hr =>
        rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩
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
          have e0 := T.s.inj he
          have e1 := T.s.inj e0
          subst x0
          exact ⟨(s (s (s q0))), (Steps.refl _), (Steps.refl _)⟩
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          have e0 := T.s.inj he
          cases e0
      | @underS _ t2 h2 =>
        cases h2 with
        | root hr =>
          rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩
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
            have e0 := T.s.inj he
            subst x0
            exact ⟨(s q0), (Steps.cons (Step.root (Root.r7 q0)) (Steps.refl _)), (Steps.cons (Step.root (Root.r7 q0)) (Steps.refl _))⟩
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            have e0 := T.s.inj he
            subst x0
            exact ⟨(s (s (s q1))), (Steps.cons (Step.root (Root.r10 q0 q1)) (Steps.refl _)), (Steps.cons (Step.root (Root.r7 (s (s q1)))) (Steps.refl _))⟩
        | @underS _ t3 h3 =>
          exact ⟨(s t3), (Steps.cons (Step.underS h3) (Steps.refl _)), (Steps.cons (Step.root (Root.r7 t3)) (Steps.refl _))⟩
end submission.Austin12857

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin12857
open T
theorem peak8 (x0 : T) (x1 : T) {u : T} (h : Step (m (s (s (s x0))) (m (m x1 (s x0)) (s (s (s x0))))) u) : Join x1 u := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst q0
      cases e1
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst q0
      have e3 := (T.m.inj e1).1
      have e4 := (T.m.inj e1).2
      have e5 := (T.m.inj e3).1
      have e6 := (T.m.inj e3).2
      subst x1
      cases e6
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst q0
      have e3 := (T.m.inj e1).1
      have e4 := (T.m.inj e1).2
      cases e3
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := T.s.inj e0
      have e3 := (T.m.inj e1).1
      have e4 := (T.m.inj e1).2
      have e5 := e2.symm
      subst q0
      have e6 := (T.m.inj e3).1
      have e7 := (T.m.inj e3).2
      subst x1
      have e8 := T.s.inj e7
      have cycle := congrArg size e8
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      cases e0
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := T.s.inj e0
      have e3 := (T.m.inj e1).1
      have e4 := (T.m.inj e1).2
      have e5 := e2.symm
      subst q0
      cases e3
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := T.s.inj e0
      have e3 := (T.m.inj e1).1
      have e4 := (T.m.inj e1).2
      have e5 := T.s.inj e2
      have e6 := (T.m.inj e3).1
      have e7 := (T.m.inj e3).2
      have e8 := T.s.inj e4
      have e9 := T.s.inj e5
      subst x1
      have e10 := T.s.inj e7
      have e11 := T.s.inj e8
      subst x0
      exact ⟨q1, (Steps.refl _), (Steps.refl _)⟩
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      cases e0
    · rw [ho]
      cases he
  | @left _ t0 _ h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩
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
        have e0 := T.s.inj he
        have e1 := T.s.inj e0
        have e2 := T.s.inj e1
        subst x0
        exact ⟨x1, (Steps.refl _), (Steps.cons (Step.right (s q0) (Step.right (m x1 (s (s q0))) (Step.root (Root.r7 q0)))) (Steps.cons (Step.root (Root.r4 q0 x1)) (Steps.refl _)))⟩
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := T.s.inj he
        cases e0
    | @underS _ t1 h1 =>
      cases h1 with
      | root hr =>
        rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩
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
          have e0 := T.s.inj he
          have e1 := T.s.inj e0
          subst x0
          exact ⟨x1, (Steps.refl _), (Steps.cons (Step.right (s (s q0)) (Step.right (m x1 (s (s (s q0)))) (Step.root (Root.r7 (s q0))))) (Steps.cons (Step.root (Root.r4 (s q0) x1)) (Steps.refl _)))⟩
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          have e0 := T.s.inj he
          cases e0
      | @underS _ t2 h2 =>
        cases h2 with
        | root hr =>
          rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩
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
            have e0 := T.s.inj he
            subst x0
            exact ⟨x1, (Steps.refl _), (Steps.cons (Step.right (s (s (s q0))) (Step.left (s (s (s (s (s (s q0)))))) (Step.right x1 (Step.root (Root.r7 q0))))) (Steps.cons (Step.right (s (s (s q0))) (Step.right (m x1 (s q0)) (Step.root (Root.r7 (s (s q0)))))) (Steps.cons (Step.root (Root.r8 q0 x1)) (Steps.refl _))))⟩
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            have e0 := T.s.inj he
            subst x0
            exact ⟨x1, (Steps.refl _), (Steps.cons (Step.left (m (m x1 (s (m (s q0) (s q1)))) (s (s (s (m (s q0) (s q1)))))) (Step.root (Root.r7 (s q1)))) (Steps.cons (Step.right (s (s q1)) (Step.left (s (s (s (m (s q0) (s q1))))) (Step.right x1 (Step.root (Root.r10 q0 q1))))) (Steps.cons (Step.right (s (s q1)) (Step.right (m x1 (s (s (s q1)))) (Step.underS (Step.underS (Step.root (Root.r10 q0 q1)))))) (Steps.cons (Step.right (s (s q1)) (Step.right (m x1 (s (s (s q1)))) (Step.root (Root.r7 (s q1))))) (Steps.cons (Step.root (Root.r4 (s q1) x1)) (Steps.refl _))))))⟩
        | @underS _ t3 h3 =>
          exact ⟨x1, (Steps.refl _), (Steps.cons (Step.right (s (s (s t3))) (Step.left (s (s (s x0))) (Step.right x1 (Step.underS h3)))) (Steps.cons (Step.right (s (s (s t3))) (Step.right (m x1 (s t3)) (Step.underS (Step.underS (Step.underS h3))))) (Steps.cons (Step.root (Root.r8 t3 x1)) (Steps.refl _))))⟩
  | @right _ _ t0 h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        have e2 := e0.symm
        subst q0
        cases e1
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        have e2 := e0.symm
        subst q0
        cases e1
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
        have e2 := (T.m.inj e0).1
        have e3 := (T.m.inj e0).2
        cases e1
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
        have e2 := (T.m.inj e0).1
        have e3 := (T.m.inj e0).2
        cases e1
      · rw [ho]
        cases he
    | @left _ t1 _ h1 =>
      cases h1 with
      | root hr =>
        rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩
        · rw [ho]
          have e0 := (T.m.inj he).1
          have e1 := (T.m.inj he).2
          subst x1
          have e2 := e1.symm
          subst q0
          exact ⟨(s x0), (Steps.refl _), (Steps.cons (Step.root (Root.r6 (s (s x0)) (s x0))) (Steps.cons (Step.root (Root.r1 (s (s (s x0))))) (Steps.cons (Step.root (Root.r7 x0)) (Steps.refl _))))⟩
        · rw [ho]
          have e0 := (T.m.inj he).1
          have e1 := (T.m.inj he).2
          subst x1
          cases e1
        · rw [ho]
          have e0 := (T.m.inj he).1
          have e1 := (T.m.inj he).2
          subst x1
          cases e1
        · rw [ho]
          have e0 := (T.m.inj he).1
          have e1 := (T.m.inj he).2
          subst x1
          cases e1
        · rw [ho]
          have e0 := (T.m.inj he).1
          have e1 := (T.m.inj he).2
          subst x1
          cases e1
        · rw [ho]
          have e0 := (T.m.inj he).1
          have e1 := (T.m.inj he).2
          subst x1
          cases e1
        · rw [ho]
          cases he
        · rw [ho]
          have e0 := (T.m.inj he).1
          have e1 := (T.m.inj he).2
          subst x1
          cases e1
        · rw [ho]
          have e0 := (T.m.inj he).1
          have e1 := (T.m.inj he).2
          subst x1
          cases e1
        · rw [ho]
          cases he
      | @left _ t2 _ h2 =>
        exact ⟨t2, (Steps.cons h2 (Steps.refl _)), (Steps.cons (Step.root (Root.r8 x0 t2)) (Steps.refl _))⟩
      | @right _ _ t2 h2 =>
        cases h2 with
        | root hr =>
          rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩
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
            have e0 := T.s.inj he
            subst x0
            exact ⟨x1, (Steps.refl _), (Steps.cons (Step.left (m (m x1 (s q0)) (s (s (s (s (s (s q0))))))) (Step.root (Root.r7 (s (s q0))))) (Steps.cons (Step.right (s (s (s q0))) (Step.right (m x1 (s q0)) (Step.root (Root.r7 (s (s q0)))))) (Steps.cons (Step.root (Root.r8 q0 x1)) (Steps.refl _))))⟩
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            have e0 := T.s.inj he
            subst x0
            exact ⟨x1, (Steps.refl _), (Steps.cons (Step.left (m (m x1 (s (s (s q1)))) (s (s (s (m (s q0) (s q1)))))) (Step.underS (Step.underS (Step.root (Root.r10 q0 q1))))) (Steps.cons (Step.left (m (m x1 (s (s (s q1)))) (s (s (s (m (s q0) (s q1)))))) (Step.root (Root.r7 (s q1)))) (Steps.cons (Step.right (s (s q1)) (Step.right (m x1 (s (s (s q1)))) (Step.underS (Step.underS (Step.root (Root.r10 q0 q1)))))) (Steps.cons (Step.right (s (s q1)) (Step.right (m x1 (s (s (s q1)))) (Step.root (Root.r7 (s q1))))) (Steps.cons (Step.root (Root.r4 (s q1) x1)) (Steps.refl _))))))⟩
        | @underS _ t3 h3 =>
          exact ⟨x1, (Steps.refl _), (Steps.cons (Step.left (m (m x1 (s t3)) (s (s (s x0)))) (Step.underS (Step.underS (Step.underS h3)))) (Steps.cons (Step.right (s (s (s t3))) (Step.right (m x1 (s t3)) (Step.underS (Step.underS (Step.underS h3))))) (Steps.cons (Step.root (Root.r8 t3 x1)) (Steps.refl _))))⟩
    | @right _ _ t1 h1 =>
      cases h1 with
      | root hr =>
        rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩
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
          have e0 := T.s.inj he
          have e1 := T.s.inj e0
          have e2 := T.s.inj e1
          subst x0
          exact ⟨x1, (Steps.refl _), (Steps.cons (Step.left (m (m x1 (s (s q0))) (s q0)) (Step.root (Root.r7 q0))) (Steps.cons (Step.root (Root.r4 q0 x1)) (Steps.refl _)))⟩
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          have e0 := T.s.inj he
          cases e0
      | @underS _ t2 h2 =>
        cases h2 with
        | root hr =>
          rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩
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
            have e0 := T.s.inj he
            have e1 := T.s.inj e0
            subst x0
            exact ⟨x1, (Steps.refl _), (Steps.cons (Step.left (m (m x1 (s (s (s q0)))) (s (s q0))) (Step.root (Root.r7 (s q0)))) (Steps.cons (Step.root (Root.r4 (s q0) x1)) (Steps.refl _)))⟩
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            have e0 := T.s.inj he
            cases e0
        | @underS _ t3 h3 =>
          cases h3 with
          | root hr =>
            rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩
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
              have e0 := T.s.inj he
              subst x0
              exact ⟨x1, (Steps.refl _), (Steps.cons (Step.left (m (m x1 (s (s (s (s q0))))) (s (s (s q0)))) (Step.root (Root.r7 (s (s q0))))) (Steps.cons (Step.root (Root.r4 (s (s q0)) x1)) (Steps.refl _)))⟩
            · rw [ho]
              cases he
            · rw [ho]
              cases he
            · rw [ho]
              have e0 := T.s.inj he
              subst x0
              exact ⟨x1, (Steps.refl _), (Steps.cons (Step.left (m (m x1 (s (m (s q0) (s q1)))) (s (s (s (s (s q1)))))) (Step.underS (Step.underS (Step.root (Root.r10 q0 q1))))) (Steps.cons (Step.left (m (m x1 (s (m (s q0) (s q1)))) (s (s (s (s (s q1)))))) (Step.root (Root.r7 (s q1)))) (Steps.cons (Step.right (s (s q1)) (Step.left (s (s (s (s (s q1))))) (Step.right x1 (Step.root (Root.r10 q0 q1))))) (Steps.cons (Step.right (s (s q1)) (Step.right (m x1 (s (s (s q1)))) (Step.root (Root.r7 (s q1))))) (Steps.cons (Step.root (Root.r4 (s q1) x1)) (Steps.refl _))))))⟩
          | @underS _ t4 h4 =>
            exact ⟨x1, (Steps.refl _), (Steps.cons (Step.left (m (m x1 (s x0)) (s (s (s t4)))) (Step.underS (Step.underS (Step.underS h4)))) (Steps.cons (Step.right (s (s (s t4))) (Step.left (s (s (s t4))) (Step.right x1 (Step.underS h4)))) (Steps.cons (Step.root (Root.r8 t4 x1)) (Steps.refl _))))⟩
end submission.Austin12857

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin12857
open T
theorem peak9 (x0 : T) (x1 : T) {u : T} (h : Step (m (m x0 (s x1)) (m x0 (m x0 (s x1)))) u) : Join (s (s (s x1))) u := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst q0
      have e3 := (T.m.inj e1).1
      have e4 := (T.m.inj e1).2
      cases e4
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst q0
      have e3 := (T.m.inj e1).1
      have e4 := (T.m.inj e1).2
      have cycle := congrArg size e3
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst q0
      have e3 := (T.m.inj e1).1
      have e4 := (T.m.inj e1).2
      have cycle := congrArg size e3
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      cases e0
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := (T.m.inj e0).1
      have e3 := (T.m.inj e0).2
      have e4 := (T.m.inj e1).1
      have e5 := (T.m.inj e1).2
      subst x0
      cases e3
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
      have e2 := (T.m.inj e0).1
      have e3 := (T.m.inj e0).2
      have e4 := (T.m.inj e1).1
      have e5 := (T.m.inj e1).2
      subst x0
      have e6 := T.s.inj e3
      have e7 := (T.m.inj e5).1
      have e8 := (T.m.inj e5).2
      subst x1
      exact ⟨(s (s (s q1))), (Steps.refl _), (Steps.refl _)⟩
    · rw [ho]
      cases he
  | @left _ t0 _ h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        have e2 := e1.symm
        subst q0
        exact ⟨(s (s (s x1))), (Steps.refl _), (Steps.cons (Step.right (s (s x1)) (Step.root (Root.r6 x1 x1))) (Steps.cons (Step.root (Root.r6 (s x1) x1)) (Steps.cons (Step.root (Root.r1 (s (s x1)))) (Steps.refl _))))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        cases e1
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        cases e1
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        cases e1
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        cases e1
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
        cases e1
      · rw [ho]
        cases he
    | @left _ t1 _ h1 =>
      exact ⟨(s (s (s x1))), (Steps.refl _), (Steps.cons (Step.right (m t1 (s x1)) (Step.left (m x0 (s x1)) h1)) (Steps.cons (Step.right (m t1 (s x1)) (Step.right t1 (Step.left (s x1) h1))) (Steps.cons (Step.root (Root.r9 t1 x1)) (Steps.refl _))))⟩
    | @right _ _ t1 h1 =>
      cases h1 with
      | root hr =>
        rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩
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
          have e0 := T.s.inj he
          subst x1
          exact ⟨(s (s (s q0))), (Steps.cons (Step.root (Root.r7 (s (s q0)))) (Steps.refl _)), (Steps.cons (Step.right (m x0 (s q0)) (Step.right x0 (Step.right x0 (Step.root (Root.r7 q0))))) (Steps.cons (Step.root (Root.r9 x0 q0)) (Steps.refl _)))⟩
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          have e0 := T.s.inj he
          subst x1
          exact ⟨(s (s q1)), (Steps.cons (Step.underS (Step.underS (Step.root (Root.r10 q0 q1)))) (Steps.cons (Step.root (Root.r7 (s q1))) (Steps.refl _))), (Steps.cons (Step.right (m x0 (s (s (s q1)))) (Step.right x0 (Step.right x0 (Step.root (Root.r10 q0 q1))))) (Steps.cons (Step.root (Root.r9 x0 (s (s q1)))) (Steps.cons (Step.root (Root.r7 (s q1))) (Steps.refl _))))⟩
      | @underS _ t2 h2 =>
        exact ⟨(s (s (s t2))), (Steps.cons (Step.underS (Step.underS (Step.underS h2))) (Steps.refl _)), (Steps.cons (Step.right (m x0 (s t2)) (Step.right x0 (Step.right x0 (Step.underS h2)))) (Steps.cons (Step.root (Root.r9 x0 t2)) (Steps.refl _)))⟩
  | @right _ _ t0 h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        have e2 := e1.symm
        have cycle := congrArg size e2
        simp only [size] at cycle
        omega
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        have e2 := (T.m.inj e1).1
        have e3 := (T.m.inj e1).2
        have cycle := congrArg size e2
        simp only [size] at cycle
        omega
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        have e2 := (T.m.inj e1).1
        have e3 := (T.m.inj e1).2
        have cycle := congrArg size e2
        simp only [size] at cycle
        omega
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        have e2 := (T.m.inj e1).1
        have e3 := (T.m.inj e1).2
        cases e2
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        have e2 := (T.m.inj e1).1
        have e3 := (T.m.inj e1).2
        have e4 := e2.symm
        have cycle := congrArg size e4
        simp only [size] at cycle
        omega
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        have e2 := (T.m.inj e1).1
        have e3 := (T.m.inj e1).2
        have e4 := T.s.inj e2
        have e5 := T.s.inj e3
        subst q0
        subst x1
        exact ⟨(s (s (s q1))), (Steps.refl _), (Steps.cons (Step.left (m (s q1) (s (s q1))) (Step.root (Root.r1 (s q1)))) (Steps.cons (Step.root (Root.r6 (s q1) q1)) (Steps.cons (Step.root (Root.r1 (s (s q1)))) (Steps.refl _))))⟩
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        have e2 := (T.m.inj e1).1
        have e3 := (T.m.inj e1).2
        cases e2
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        have e2 := (T.m.inj e1).1
        have e3 := (T.m.inj e1).2
        have e4 := e2.symm
        have cycle := congrArg size e4
        simp only [size] at cycle
        omega
      · rw [ho]
        cases he
    | @left _ t1 _ h1 =>
      exact ⟨(s (s (s x1))), (Steps.refl _), (Steps.cons (Step.left (m t1 (m x0 (s x1))) (Step.left (s x1) h1)) (Steps.cons (Step.right (m t1 (s x1)) (Step.right t1 (Step.left (s x1) h1))) (Steps.cons (Step.root (Root.r9 t1 x1)) (Steps.refl _))))⟩
    | @right _ _ t1 h1 =>
      cases h1 with
      | root hr =>
        rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩
        · rw [ho]
          have e0 := (T.m.inj he).1
          have e1 := (T.m.inj he).2
          subst x0
          have e2 := e1.symm
          subst q0
          exact ⟨(s (s (s x1))), (Steps.refl _), (Steps.cons (Step.left (m (s x1) (s (s x1))) (Step.root (Root.r1 (s x1)))) (Steps.cons (Step.root (Root.r6 (s x1) x1)) (Steps.cons (Step.root (Root.r1 (s (s x1)))) (Steps.refl _))))⟩
        · rw [ho]
          have e0 := (T.m.inj he).1
          have e1 := (T.m.inj he).2
          subst x0
          cases e1
        · rw [ho]
          have e0 := (T.m.inj he).1
          have e1 := (T.m.inj he).2
          subst x0
          cases e1
        · rw [ho]
          have e0 := (T.m.inj he).1
          have e1 := (T.m.inj he).2
          subst x0
          cases e1
        · rw [ho]
          have e0 := (T.m.inj he).1
          have e1 := (T.m.inj he).2
          subst x0
          cases e1
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
          cases e1
        · rw [ho]
          cases he
      | @left _ t2 _ h2 =>
        exact ⟨(s (s (s x1))), (Steps.refl _), (Steps.cons (Step.left (m x0 (m t2 (s x1))) (Step.left (s x1) h2)) (Steps.cons (Step.right (m t2 (s x1)) (Step.left (m t2 (s x1)) h2)) (Steps.cons (Step.root (Root.r9 t2 x1)) (Steps.refl _))))⟩
      | @right _ _ t2 h2 =>
        cases h2 with
        | root hr =>
          rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩
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
            have e0 := T.s.inj he
            subst x1
            exact ⟨(s (s (s q0))), (Steps.cons (Step.root (Root.r7 (s (s q0)))) (Steps.refl _)), (Steps.cons (Step.left (m x0 (m x0 (s q0))) (Step.right x0 (Step.root (Root.r7 q0)))) (Steps.cons (Step.root (Root.r9 x0 q0)) (Steps.refl _)))⟩
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            have e0 := T.s.inj he
            subst x1
            exact ⟨(s (s q1)), (Steps.cons (Step.underS (Step.underS (Step.root (Root.r10 q0 q1)))) (Steps.cons (Step.root (Root.r7 (s q1))) (Steps.refl _))), (Steps.cons (Step.left (m x0 (m x0 (s (s (s q1))))) (Step.right x0 (Step.root (Root.r10 q0 q1)))) (Steps.cons (Step.root (Root.r9 x0 (s (s q1)))) (Steps.cons (Step.root (Root.r7 (s q1))) (Steps.refl _))))⟩
        | @underS _ t3 h3 =>
          exact ⟨(s (s (s t3))), (Steps.cons (Step.underS (Step.underS (Step.underS h3))) (Steps.refl _)), (Steps.cons (Step.left (m x0 (m x0 (s t3))) (Step.right x0 (Step.underS h3))) (Steps.cons (Step.root (Root.r9 x0 t3)) (Steps.refl _)))⟩
end submission.Austin12857

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin12857
open T
theorem peak10 (x0 : T) (x1 : T) {u : T} (h : Step (s (m (s x0) (s x1))) u) : Join (s (s (s x1))) u := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩
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
      have e0 := T.s.inj he
      cases e0
    · rw [ho]
      cases he
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := T.s.inj he
      have e1 := (T.m.inj e0).1
      have e2 := (T.m.inj e0).2
      have e3 := T.s.inj e1
      have e4 := T.s.inj e2
      subst x0
      subst x1
      exact ⟨(s (s (s q1))), (Steps.refl _), (Steps.refl _)⟩
  | @underS _ t0 h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        have e2 := e0.symm
        subst q0
        have e3 := T.s.inj e1
        subst x1
        exact ⟨(s (s (s x0))), (Steps.refl _), (Steps.refl _)⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        have e2 := e0.symm
        subst q0
        cases e1
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        have e2 := e0.symm
        subst q0
        cases e1
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        have e2 := T.s.inj e0
        cases e1
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        cases e0
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        have e2 := T.s.inj e0
        cases e1
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        have e2 := T.s.inj e0
        cases e1
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        cases e0
      · rw [ho]
        cases he
    | @left _ t1 _ h1 =>
      cases h1 with
      | root hr =>
        rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩
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
          have e0 := T.s.inj he
          subst x0
          exact ⟨(s (s (s x1))), (Steps.refl _), (Steps.cons (Step.root (Root.r10 q0 x1)) (Steps.refl _))⟩
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          have e0 := T.s.inj he
          subst x0
          exact ⟨(s (s (s x1))), (Steps.refl _), (Steps.cons (Step.root (Root.r10 (s (s q1)) x1)) (Steps.refl _))⟩
      | @underS _ t2 h2 =>
        exact ⟨(s (s (s x1))), (Steps.refl _), (Steps.cons (Step.root (Root.r10 t2 x1)) (Steps.refl _))⟩
    | @right _ _ t1 h1 =>
      cases h1 with
      | root hr =>
        rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩
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
          have e0 := T.s.inj he
          subst x1
          exact ⟨(s (s (s q0))), (Steps.cons (Step.root (Root.r7 (s (s q0)))) (Steps.refl _)), (Steps.cons (Step.root (Root.r10 x0 q0)) (Steps.refl _))⟩
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          have e0 := T.s.inj he
          subst x1
          exact ⟨(s (s q1)), (Steps.cons (Step.underS (Step.underS (Step.root (Root.r10 q0 q1)))) (Steps.cons (Step.root (Root.r7 (s q1))) (Steps.refl _))), (Steps.cons (Step.root (Root.r10 x0 (s (s q1)))) (Steps.cons (Step.root (Root.r7 (s q1))) (Steps.refl _)))⟩
      | @underS _ t2 h2 =>
        exact ⟨(s (s (s t2))), (Steps.cons (Step.underS (Step.underS (Step.underS h2))) (Steps.refl _)), (Steps.cons (Step.root (Root.r10 x0 t2)) (Steps.refl _))⟩
end submission.Austin12857

set_option autoImplicit false
namespace submission.Austin12857
open T

theorem root_step {x y z : T} (h : Root x y) (k : Step x z) : Join y z := by
  cases h with
  | r1 x => exact peak1 x k
  | r2 x y z => exact peak2 x y z k
  | r3 x y => exact peak3 x y k
  | r4 x y => exact peak4 x y k
  | r5 x y z => exact peak5 x y z k
  | r6 x y => exact peak6 x y k
  | r7 x => exact peak7 x k
  | r8 x y => exact peak8 x y k
  | r9 x y => exact peak9 x y k
  | r10 x y => exact peak10 x y k

theorem local_join {x y z : T} (h : Step x y) (k : Step x z) : Join y z := by
  induction h generalizing z with
  | root hr => exact root_step hr k
  | underS h ih =>
    cases k with
    | root hr => exact (root_step hr (.underS h)).symm
    | underS k => exact (ih k).underS
  | left c h ih =>
    cases k with
    | root hr => exact (root_step hr (.left c h)).symm
    | left _ k => exact (ih k).left c
    | @right x _ z k =>
      exact ⟨m _ z, Steps.single (.right _ k), Steps.single (.left z h)⟩
  | right c h ih =>
    cases k with
    | root hr => exact (root_step hr (.right c h)).symm
    | @left x y _ k =>
      exact ⟨m y _, Steps.single (.left _ k), Steps.single (.right y h)⟩
    | right _ k => exact (ih k).right c

def Normal (x : T) : Prop := ∀ {y : T}, Step x y → False

theorem normal_exists (x : T) : ∃ y, Steps x y ∧ Normal y := by
  classical
  have aux : ∀ n x, size x = n → ∃ y, Steps x y ∧ Normal y := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro x hx
      by_cases h : ∃ y, Step x y
      · obtain ⟨y, hxy⟩ := h
        obtain ⟨z, hyz, hz⟩ := ih (size y) (hx ▸ step_decreases hxy) y rfl
        exact ⟨z, .cons hxy hyz, hz⟩
      · exact ⟨x, .refl x, fun k => h ⟨_, k⟩⟩
  exact aux (size x) x rfl

theorem normal_steps_eq {x y : T} (hx : Normal x) (h : Steps x y) : x = y := by
  cases h with
  | refl => rfl
  | cons h _ => exact False.elim (hx h)

/-- Newman's argument specialized to the strictly decreasing node count. -/
theorem normal_unique {x y z : T} (hy : Normal y) (hz : Normal z)
    (hxy : Steps x y) (hxz : Steps x z) : y = z := by
  have aux : ∀ n x, size x = n → ∀ y z, Normal y → Normal z →
      Steps x y → Steps x z → y = z := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro x hx y z hy hz hxy hxz
      cases hxy with
      | refl => exact normal_steps_eq hy hxz
      | @cons _ p _ hxp hpy =>
        cases hxz with
        | refl => exact (normal_steps_eq hz (.cons hxp hpy)).symm
        | @cons _ q _ hxq hqz =>
          obtain ⟨d, hpd, hqd⟩ := local_join hxp hxq
          obtain ⟨e, hde, he⟩ := normal_exists d
          have hye := ih (size p) (hx ▸ step_decreases hxp) p rfl y e
            hy he hpy (hpd.trans hde)
          have hze := ih (size q) (hx ▸ step_decreases hxq) q rfl z e
            hz he hqz (hqd.trans hde)
          exact hye.trans hze.symm
  exact aux (size x) x rfl y z hy hz hxy hxz

noncomputable def norm (x : T) : T := Classical.choose (normal_exists x)
theorem steps_norm (x : T) : Steps x (norm x) := (Classical.choose_spec (normal_exists x)).1
theorem norm_normal (x : T) : Normal (norm x) := (Classical.choose_spec (normal_exists x)).2

theorem norm_of_normal {x : T} (h : Normal x) : norm x = x :=
  (normal_steps_eq h (steps_norm x)).symm

theorem norm_steps {x y : T} (h : Steps x y) : norm x = norm y :=
  normal_unique (norm_normal x) (norm_normal y) (steps_norm x) (h.trans (steps_norm y))

theorem confluent {x y z : T} (hy : Steps x y) (hz : Steps x z) : Join y z := by
  have h : norm y = norm z := (norm_steps hy).symm.trans (norm_steps hz)
  exact ⟨norm y, steps_norm y, h ▸ steps_norm z⟩

theorem norm_m (x y : T) : norm (m (norm x) (norm y)) = norm (m x y) :=
  (norm_steps (Steps.both (steps_norm x) (steps_norm y))).symm
end submission.Austin12857

set_option autoImplicit false
namespace submission.Austin12857
open T

def Carrier := {x : T // Normal x}
noncomputable def mul (x y : Carrier) : Carrier :=
  ⟨norm (m x.val y.val), norm_normal _⟩

theorem mul_val (x y : Carrier) : (mul x y).val = norm (m x.val y.val) := rfl

theorem equation12857 (x y z : Carrier) :
    mul y (mul (mul x (mul y (mul z z))) y) = x := by
  apply Subtype.ext
  change norm (m y.val (norm (m (norm (m x.val (norm (m y.val
    (norm (m z.val z.val)))))) y.val))) = x.val
  have nx := norm_of_normal x.property
  have ny := norm_of_normal y.property
  have nz := norm_of_normal z.property
  have hl : norm (m y.val (m (m x.val (m y.val (m z.val z.val))) y.val)) = x.val := by
    have h : Steps (m y.val (m (m x.val (m y.val (m z.val z.val))) y.val)) x.val :=
      .cons (.right _ (.left _ (.right _ (.right _ (.root (.r1 z.val))))))
        (.single (.root (.r2 y.val x.val z.val)))
    exact (norm_steps h).trans nx
  -- Replace the fixed normal inputs by their normalizations to apply congruence.
  have left_norm (p q : T) : norm (m p (norm q)) = norm (m p q) := by
    exact (norm_steps (Steps.right p (steps_norm q))).symm
  have right_norm (p q : T) : norm (m (norm p) q) = norm (m p q) := by
    exact (norm_steps (Steps.left q (steps_norm p))).symm
  simp only [left_norm, right_norm]
  exact hl

def clean : T → Prop
  | a => True
  | b => True
  | s _ => False
  | m x y => clean x ∧ clean y

theorem clean_root {x y : T} (h : Root x y) (hc : clean x) : ∃ t, x = m t t := by
  cases h <;> simp only [clean, and_false, false_and] at hc
  exact ⟨_, rfl⟩

def tower : Nat → T
  | 0 => b
  | n+1 => m a (tower n)

theorem tower_clean (n : Nat) : clean (tower n) := by
  induction n with
  | zero => exact True.intro
  | succ n ih => exact ⟨True.intro, ih⟩

theorem tower_ne_a (n : Nat) : tower n ≠ a := by
  cases n <;> simp only [tower] <;> intro h <;> cases h

theorem normal_a : Normal a := by
  intro y h
  cases h with
  | root h => cases h

theorem tower_normal (n : Nat) : Normal (tower n) := by
  induction n with
  | zero =>
    intro y h
    cases h with
    | root h => cases h
  | succ n ih =>
    intro y h
    cases h with
    | root h =>
      obtain ⟨t, ht⟩ := clean_root h (tower_clean (n+1))
      have h1 := (T.m.inj ht).1
      have h2 := (T.m.inj ht).2
      exact tower_ne_a n (h2.trans h1.symm)
    | left _ h => exact normal_a h
    | right _ h => exact ih h

theorem tower_size (n : Nat) : size (tower n) = 2*n+1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [tower, size, ih]; omega

def embed (n : Nat) : Carrier := ⟨tower n, tower_normal n⟩

theorem embed_injective (n k : Nat) (h : embed n = embed k) : n = k := by
  have hh := congrArg (fun x : Carrier => size x.val) h
  change size (tower n) = size (tower k) at hh
  rw [tower_size, tower_size] at hh
  omega

noncomputable def opposite (x y : Carrier) : Carrier := mul y x

theorem equation33436 (x y z : Carrier) :
    opposite (opposite y (opposite (opposite (opposite z z) y) x)) y = x :=
  equation12857 x y z

/-- Explicit injection of Nat, in addition to the universally quantified law. -/
theorem infinite_model : ∃ (A : Type) (op : A → A → A) (f : Nat → A),
    (∀ x y z, op y (op (op x (op y (op z z))) y) = x) ∧
    (∀ n k, f n = f k → n = k) :=
  ⟨Carrier, mul, embed, equation12857, embed_injective⟩
end submission.Austin12857


namespace submission
abbrev CM := submission.Austin12857.Carrier
namespace CM
/-- An explicit injection of the natural numbers into the model carrier. -/
theorem tower_injective (n k : Nat)
    (h : submission.Austin12857.embed n = submission.Austin12857.embed k) : n = k :=
  submission.Austin12857.embed_injective n k h
end CM
noncomputable instance modelMagma : Magma CM := ⟨submission.Austin12857.opposite⟩
end submission

/-- The exact archived source equation has a nontrivial, explicitly infinite model. -/
theorem submission : Goal := by
  refine ⟨submission.CM, submission.modelMagma, ?_, ?_⟩
  · intro x y z
    exact (submission.Austin12857.equation33436 x y z).symm
  · intro h
    have bad : 0 = 1 := submission.Austin12857.embed_injective 0 1
      (h (submission.Austin12857.embed 0) (submission.Austin12857.embed 1))
    exact Nat.noConfusion bad

example : Goal := submission
#print axioms submission
#print axioms submission.CM.tower_injective

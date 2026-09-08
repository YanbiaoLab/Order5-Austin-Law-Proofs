import Lean.Elab.Tactic.Omega
import JudgeProblem


set_option autoImplicit false
namespace submission.Austin13992
inductive T where
  | a : T
  | e : T
  | k : T → T
  | v : T → T
  | r : T → T → T
  | c : T → T → T → T
  | m : T → T → T
  deriving DecidableEq
open T
@[simp] def size : T → Nat
  | a => 1
  | e => 1
  | k x => size x + 1
  | v x => size x + 1
  | r x y => size x + size y + 1
  | c x y z => size x + size y + size z + 1
  | m x y => 3 * size x + 2 * size y + 1
theorem size_pos (x : T) : 0 < size x := by
  cases x <;> simp only [size] <;> omega
inductive Root : T → T → Prop where
  | r1 (v0 v1) : Root (T.m (T.m v0 v1) v1) (T.r v0 v1)
  | r2 (v0 v1 v2) : Root (T.m (T.m v0 (T.r v1 v2)) v2) (T.c v0 v1 v2)
  | r3 (v0 v1 v2) : Root (T.m v0 (T.c v1 v2 v0)) v2
  | r4 (v0 v1) : Root (T.m (T.r v0 v1) v1) (T.r (T.m v0 v1) v1)
  | r5 (v0 v1 v2) : Root (T.m v0 (T.c v1 v0 v2)) (T.r v2 (T.c v1 v0 v2))
  | r6 (v0 v1) : Root (T.r v0 (T.c v1 v0 v0)) v0
  | r7 (v0 v1 v2) : Root (T.m (T.c v0 v1 v2) v2) (T.r (T.m v0 (T.r v1 v2)) v2)
  | r8 (v0 v1 v2) : Root (T.m (T.r v0 (T.r v1 v2)) v2) (T.c (T.m v0 (T.r v1 v2)) v1 v2)
  | r9 (v0 v1 v2) : Root (T.m (T.m v0 v1) (T.c v2 v1 v1)) (T.c v0 v1 (T.c v2 v1 v1))
  | r10 (v0 v1 v2) : Root (T.m (T.r v0 v1) (T.c v2 v1 v1)) (T.c (T.m v0 v1) v1 (T.c v2 v1 v1))
  | r11 (v0 v1 v2 v3) : Root (T.m (T.c v0 v1 (T.r v2 v3)) v3) (T.c (T.m v0 (T.r v1 (T.r v2 v3))) v2 v3)
  | r12 (v0 v1 v2 v3) : Root (T.m (T.c v0 v1 v2) (T.c v3 v2 v2)) (T.c (T.m v0 (T.r v1 v2)) v2 (T.c v3 v2 v2))
  | r13 (v0 v1 v2 v3) : Root (T.m v0 (T.c v1 (T.c v2 v0 v3) (T.c v2 v0 v3))) (T.c v3 (T.c v2 v0 v3) (T.c v1 (T.c v2 v0 v3) (T.c v2 v0 v3)))
inductive Step : T → T → Prop where
  | root {x y} : Root x y → Step x y
  | underK {x y} : Step x y → Step (k x) (k y)
  | underV {x y} : Step x y → Step (v x) (v y)
  | left {x y} (z) : Step x y → Step (m x z) (m y z)
  | right (x) {y z} : Step y z → Step (m x y) (m x z)
  | leftR {x y} (z) : Step x y → Step (r x z) (r y z)
  | rightR (x) {y z} : Step y z → Step (r x y) (r x z)
  | firstC {x y} (z w) : Step x y → Step (c x z w) (c y z w)
  | secondC (x) {y z} (w) : Step y z → Step (c x y w) (c x z w)
  | thirdC (x y) {z w} : Step z w → Step (c x y z) (c x y w)
inductive Steps : T → T → Prop where
  | refl (x) : Steps x x
  | cons {x y z} : Step x y → Steps y z → Steps x z
namespace Steps
 theorem single {x y} (h : Step x y) : Steps x y := .cons h (.refl _)
 theorem trans {x y z} (h : Steps x y) (k : Steps y z) : Steps x z := by
  induction h with
  | refl => exact k
  | cons h _ ih => exact .cons h (ih k)
 theorem underK {x y} (h : Steps x y) : Steps (k x) (k y) := by
  induction h with
  | refl => exact .refl _
  | cons h _ ih => exact .cons (.underK h) ih
 theorem underV {x y} (h : Steps x y) : Steps (v x) (v y) := by
  induction h with
  | refl => exact .refl _
  | cons h _ ih => exact .cons (.underV h) ih
 theorem left {x y} (z) (h : Steps x y) : Steps (m x z) (m y z) := by
  induction h with
  | refl => exact .refl _
  | cons h _ ih => exact .cons (.left z h) ih
 theorem right (x) {y z} (h : Steps y z) : Steps (m x y) (m x z) := by
  induction h with
  | refl => exact .refl _
  | cons h _ ih => exact .cons (.right x h) ih
 theorem leftR {x y} (z) (h : Steps x y) : Steps (r x z) (r y z) := by
  induction h with
  | refl => exact .refl _
  | cons h _ ih => exact .cons (.leftR z h) ih
 theorem rightR (x) {y z} (h : Steps y z) : Steps (r x y) (r x z) := by
  induction h with
  | refl => exact .refl _
  | cons h _ ih => exact .cons (.rightR x h) ih
 theorem firstC {x y} (z w) (h : Steps x y) : Steps (c x z w) (c y z w) := by
  induction h with
  | refl => exact .refl _
  | cons h _ ih => exact .cons (.firstC z w h) ih
 theorem secondC (x) {y z} (w) (h : Steps y z) : Steps (c x y w) (c x z w) := by
  induction h with
  | refl => exact .refl _
  | cons h _ ih => exact .cons (.secondC x w h) ih
 theorem thirdC (x y) {z w} (h : Steps z w) : Steps (c x y z) (c x y w) := by
  induction h with
  | refl => exact .refl _
  | cons h _ ih => exact .cons (.thirdC x y h) ih
 theorem both {x y u v} (h : Steps x y) (k : Steps u v) : Steps (m x u) (m y v) :=
  (left u h).trans (right y k)
end Steps
def Join (x y : T) : Prop := ∃ z, Steps x z ∧ Steps y z
namespace Join
 theorem symm {x y} (h : Join x y) : Join y x := by
  obtain ⟨z,h,k⟩ := h
  exact ⟨z,k,h⟩
 theorem underK {x y} (h : Join x y) : Join (k x) (k y) := by
  obtain ⟨w,h,k⟩ := h
  exact ⟨T.k w, h.underK, k.underK⟩
 theorem underV {x y} (h : Join x y) : Join (v x) (v y) := by
  obtain ⟨w,h,k⟩ := h
  exact ⟨T.v w, h.underV, k.underV⟩
 theorem left {x y} (z) (h : Join x y) : Join (m x z) (m y z) := by
  obtain ⟨w,h,k⟩ := h
  exact ⟨T.m w z, h.left z, k.left z⟩
 theorem right (x) {y z} (h : Join y z) : Join (m x y) (m x z) := by
  obtain ⟨w,h,k⟩ := h
  exact ⟨T.m x w, h.right x, k.right x⟩
 theorem leftR {x y} (z) (h : Join x y) : Join (r x z) (r y z) := by
  obtain ⟨w,h,k⟩ := h
  exact ⟨T.r w z, h.leftR z, k.leftR z⟩
 theorem rightR (x) {y z} (h : Join y z) : Join (r x y) (r x z) := by
  obtain ⟨w,h,k⟩ := h
  exact ⟨T.r x w, h.rightR x, k.rightR x⟩
 theorem firstC {x y} (z w) (h : Join x y) : Join (c x z w) (c y z w) := by
  obtain ⟨u,h,k⟩ := h
  exact ⟨c u z w,h.firstC z w,k.firstC z w⟩
 theorem secondC (x) {y z} (w) (h : Join y z) : Join (c x y w) (c x z w) := by
  obtain ⟨u,h,k⟩ := h
  exact ⟨c x u w,h.secondC x w,k.secondC x w⟩
 theorem thirdC (x y) {z w} (h : Join z w) : Join (c x y z) (c x y w) := by
  obtain ⟨u,h,k⟩ := h
  exact ⟨c x y u,h.thirdC x y,k.thirdC x y⟩
end Join
theorem root_decreases {x y} (h : Root x y) : size y < size x := by
  cases h <;> simp only [size]
  all_goals first | omega | (rename_i t; have hp := size_pos t; omega) | (rename_i t u; have ht := size_pos t; have hu := size_pos u; omega)
theorem step_decreases {x y} (h : Step x y) : size y < size x := by
  induction h with
  | root h => exact root_decreases h
  | underK _ ih => simp only [size]; omega
  | underV _ ih => simp only [size]; omega
  | left _ _ ih => simp only [size]; omega
  | right _ _ ih => simp only [size]; omega
  | leftR _ _ ih => simp only [size]; omega
  | rightR _ _ ih => simp only [size]; omega
  | firstC _ _ _ ih => simp only [size]; omega
  | secondC _ _ _ ih => simp only [size]; omega
  | thirdC _ _ _ ih => simp only [size]; omega
theorem root_cases {u v : T} (h : Root u v) :
    (∃ v0 v1, u = (T.m (T.m v0 v1) v1) ∧ v = (T.r v0 v1)) ∨
    (∃ v0 v1 v2, u = (T.m (T.m v0 (T.r v1 v2)) v2) ∧ v = (T.c v0 v1 v2)) ∨
    (∃ v0 v1 v2, u = (T.m v0 (T.c v1 v2 v0)) ∧ v = v2) ∨
    (∃ v0 v1, u = (T.m (T.r v0 v1) v1) ∧ v = (T.r (T.m v0 v1) v1)) ∨
    (∃ v0 v1 v2, u = (T.m v0 (T.c v1 v0 v2)) ∧ v = (T.r v2 (T.c v1 v0 v2))) ∨
    (∃ v0 v1, u = (T.r v0 (T.c v1 v0 v0)) ∧ v = v0) ∨
    (∃ v0 v1 v2, u = (T.m (T.c v0 v1 v2) v2) ∧ v = (T.r (T.m v0 (T.r v1 v2)) v2)) ∨
    (∃ v0 v1 v2, u = (T.m (T.r v0 (T.r v1 v2)) v2) ∧ v = (T.c (T.m v0 (T.r v1 v2)) v1 v2)) ∨
    (∃ v0 v1 v2, u = (T.m (T.m v0 v1) (T.c v2 v1 v1)) ∧ v = (T.c v0 v1 (T.c v2 v1 v1))) ∨
    (∃ v0 v1 v2, u = (T.m (T.r v0 v1) (T.c v2 v1 v1)) ∧ v = (T.c (T.m v0 v1) v1 (T.c v2 v1 v1))) ∨
    (∃ v0 v1 v2 v3, u = (T.m (T.c v0 v1 (T.r v2 v3)) v3) ∧ v = (T.c (T.m v0 (T.r v1 (T.r v2 v3))) v2 v3)) ∨
    (∃ v0 v1 v2 v3, u = (T.m (T.c v0 v1 v2) (T.c v3 v2 v2)) ∧ v = (T.c (T.m v0 (T.r v1 v2)) v2 (T.c v3 v2 v2))) ∨
    (∃ v0 v1 v2 v3, u = (T.m v0 (T.c v1 (T.c v2 v0 v3) (T.c v2 v0 v3))) ∧ v = (T.c v3 (T.c v2 v0 v3) (T.c v1 (T.c v2 v0 v3) (T.c v2 v0 v3)))) := by
  cases h with
  | r1 => exact (Or.inl ⟨_, _, rfl, rfl⟩)
  | r2 => exact (Or.inr (Or.inl ⟨_, _, _, rfl, rfl⟩))
  | r3 => exact (Or.inr (Or.inr (Or.inl ⟨_, _, _, rfl, rfl⟩)))
  | r4 => exact (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, rfl, rfl⟩))))
  | r5 => exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, rfl, rfl⟩)))))
  | r6 => exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, rfl, rfl⟩))))))
  | r7 => exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, rfl, rfl⟩)))))))
  | r8 => exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, rfl, rfl⟩))))))))
  | r9 => exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, rfl, rfl⟩)))))))))
  | r10 => exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, rfl, rfl⟩))))))))))
  | r11 => exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, _, rfl, rfl⟩)))))))))))
  | r12 => exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, _, rfl, rfl⟩))))))))))))
  | r13 => exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨_, _, _, _, rfl, rfl⟩))))))))))))

end submission.Austin13992

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin13992
open T
theorem peak1 (x0 : T) (x1 : T) {u : T} (h : Step (T.m (T.m x0 x1) x1) u) : Join (T.r x0 x1) u := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩
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
      have e2 := (T.m.inj e0).1
      have e3 := (T.m.inj e0).2
      subst x1
      subst x0
      have cycle := congrArg size e3
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
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      cases e0
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := (T.m.inj e0).1
      have e3 := (T.m.inj e0).2
      subst x1
      subst x0
      have e4 := e3.symm
      have cycle := congrArg size e4
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
      have e2 := e0.symm
      subst q0
      have cycle := congrArg size e1
      simp only [size] at cycle
      omega
  | @left _ t0 _ h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        subst x1
        exact ⟨(T.r (T.m q0 q1) q1), (Steps.refl _), (Steps.cons (Step.root (Root.r4 q0 q1)) (Steps.refl _))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        subst x1
        exact ⟨(T.r (T.m q0 (T.r q1 q2)) q2), (Steps.refl _), (Steps.cons (Step.root (Root.r7 q0 q1 q2)) (Steps.refl _))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        subst x1
        exact ⟨(T.r q0 (T.c q1 q2 q0)), (Steps.refl _), (Steps.cons (Step.root (Root.r5 q2 q1 q0)) (Steps.refl _))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        subst x1
        exact ⟨(T.r (T.r q0 q1) q1), (Steps.refl _), (Steps.cons (Step.root (Root.r4 (T.m q0 q1) q1)) (Steps.cons (Step.leftR q1 (Step.root (Root.r1 q0 q1))) (Steps.refl _)))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        subst x1
        exact ⟨(T.r q0 (T.c q1 q0 q2)), (Steps.refl _), (Steps.cons (Step.root (Root.r4 q2 (T.c q1 q0 q2))) (Steps.cons (Step.leftR (T.c q1 q0 q2) (Step.root (Root.r3 q2 q1 q0))) (Steps.refl _)))⟩
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        subst x1
        exact ⟨(T.r (T.c q0 q1 q2) q2), (Steps.refl _), (Steps.cons (Step.root (Root.r4 (T.m q0 (T.r q1 q2)) q2)) (Steps.cons (Step.leftR q2 (Step.root (Root.r2 q0 q1 q2))) (Steps.refl _)))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        subst x1
        exact ⟨(T.r (T.r q0 (T.r q1 q2)) q2), (Steps.refl _), (Steps.cons (Step.root (Root.r7 (T.m q0 (T.r q1 q2)) q1 q2)) (Steps.cons (Step.leftR q2 (Step.root (Root.r1 q0 (T.r q1 q2)))) (Steps.refl _)))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        subst x1
        exact ⟨(T.r (T.m q0 q1) (T.c q2 q1 q1)), (Steps.refl _), (Steps.cons (Step.root (Root.r7 q0 q1 (T.c q2 q1 q1))) (Steps.cons (Step.leftR (T.c q2 q1 q1) (Step.right q0 (Step.root (Root.r6 q1 q2)))) (Steps.refl _)))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        subst x1
        exact ⟨(T.r (T.r q0 q1) (T.c q2 q1 q1)), (Steps.refl _), (Steps.cons (Step.root (Root.r7 (T.m q0 q1) q1 (T.c q2 q1 q1))) (Steps.cons (Step.leftR (T.c q2 q1 q1) (Step.right (T.m q0 q1) (Step.root (Root.r6 q1 q2)))) (Steps.cons (Step.leftR (T.c q2 q1 q1) (Step.root (Root.r1 q0 q1))) (Steps.refl _))))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        subst x1
        exact ⟨(T.r (T.c q0 q1 (T.r q2 q3)) q3), (Steps.refl _), (Steps.cons (Step.root (Root.r7 (T.m q0 (T.r q1 (T.r q2 q3))) q2 q3)) (Steps.cons (Step.leftR q3 (Step.root (Root.r2 q0 q1 (T.r q2 q3)))) (Steps.refl _)))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        subst x1
        exact ⟨(T.r (T.c q0 q1 q2) (T.c q3 q2 q2)), (Steps.refl _), (Steps.cons (Step.root (Root.r7 (T.m q0 (T.r q1 q2)) q2 (T.c q3 q2 q2))) (Steps.cons (Step.leftR (T.c q3 q2 q2) (Step.right (T.m q0 (T.r q1 q2)) (Step.root (Root.r6 q2 q3)))) (Steps.cons (Step.leftR (T.c q3 q2 q2) (Step.root (Root.r2 q0 q1 q2))) (Steps.refl _))))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        subst x1
        exact ⟨(T.r q0 (T.c q1 (T.c q2 q0 q3) (T.c q2 q0 q3))), (Steps.refl _), (Steps.cons (Step.root (Root.r7 q3 (T.c q2 q0 q3) (T.c q1 (T.c q2 q0 q3) (T.c q2 q0 q3)))) (Steps.cons (Step.leftR (T.c q1 (T.c q2 q0 q3) (T.c q2 q0 q3)) (Step.right q3 (Step.root (Root.r6 (T.c q2 q0 q3) q1)))) (Steps.cons (Step.leftR (T.c q1 (T.c q2 q0 q3) (T.c q2 q0 q3)) (Step.root (Root.r3 q3 q2 q0))) (Steps.refl _))))⟩
    | @left _ t1 _ h1 =>
      exact ⟨(T.r t1 x1), (Steps.cons (Step.leftR x1 h1) (Steps.refl _)), (Steps.cons (Step.root (Root.r1 t1 x1)) (Steps.refl _))⟩
    | @right _ _ t1 h1 =>
      exact ⟨(T.r x0 t1), (Steps.cons (Step.rightR x0 h1) (Steps.refl _)), (Steps.cons (Step.right (T.m x0 t1) h1) (Steps.cons (Step.root (Root.r1 x0 t1)) (Steps.refl _)))⟩
  | @right _ _ t0 h0 =>
    exact ⟨(T.r x0 t0), (Steps.cons (Step.rightR x0 h0) (Steps.refl _)), (Steps.cons (Step.left t0 (Step.right x0 h0)) (Steps.cons (Step.root (Root.r1 x0 t0)) (Steps.refl _)))⟩
end submission.Austin13992

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin13992
open T
theorem peak2 (x0 : T) (x1 : T) (x2 : T) {u : T} (h : Step (T.m (T.m x0 (T.r x1 x2)) x2) u) : Join (T.c x0 x1 x2) u := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := (T.m.inj e0).1
      have e3 := (T.m.inj e0).2
      subst x2
      subst x0
      have e4 := e3.symm
      have cycle := congrArg size e4
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := (T.m.inj e0).1
      have e3 := (T.m.inj e0).2
      subst x2
      subst x0
      have e4 := (T.r.inj e3).1
      have e5 := (T.r.inj e3).2
      subst x1
      exact ⟨(T.c q0 q1 q2), (Steps.refl _), (Steps.refl _)⟩
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
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      cases e0
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := (T.m.inj e0).1
      have e3 := (T.m.inj e0).2
      subst x2
      subst x0
      have e4 := e3.symm
      have cycle := congrArg size e4
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
      have e2 := e0.symm
      subst q0
      have cycle := congrArg size e1
      simp only [size] at cycle
      omega
  | @left _ t0 _ h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        have e2 := e1.symm
        subst q1
        exact ⟨(T.c (T.m q0 (T.r x1 x2)) x1 x2), (Steps.refl _), (Steps.cons (Step.root (Root.r8 q0 x1 x2)) (Steps.refl _))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        have e2 := e1.symm
        subst q2
        exact ⟨(T.c (T.m q0 (T.r q1 (T.r x1 x2))) x1 x2), (Steps.refl _), (Steps.cons (Step.root (Root.r11 q0 q1 x1 x2)) (Steps.refl _))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        cases e1
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        have e2 := e1.symm
        subst q1
        exact ⟨(T.c (T.r q0 (T.r x1 x2)) x1 x2), (Steps.refl _), (Steps.cons (Step.root (Root.r8 (T.m q0 (T.r x1 x2)) x1 x2)) (Steps.cons (Step.firstC x1 x2 (Step.root (Root.r1 q0 (T.r x1 x2)))) (Steps.refl _)))⟩
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
        have e2 := e1.symm
        subst q2
        exact ⟨(T.c (T.c q0 q1 (T.r x1 x2)) x1 x2), (Steps.refl _), (Steps.cons (Step.root (Root.r8 (T.m q0 (T.r q1 (T.r x1 x2))) x1 x2)) (Steps.cons (Step.firstC x1 x2 (Step.root (Root.r2 q0 q1 (T.r x1 x2)))) (Steps.refl _)))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        have e2 := e1.symm
        subst q2
        exact ⟨(T.c (T.r q0 (T.r q1 (T.r x1 x2))) x1 x2), (Steps.refl _), (Steps.cons (Step.root (Root.r11 (T.m q0 (T.r q1 (T.r x1 x2))) q1 x1 x2)) (Steps.cons (Step.firstC x1 x2 (Step.root (Root.r1 q0 (T.r q1 (T.r x1 x2))))) (Steps.refl _)))⟩
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
        have e2 := e1.symm
        subst q3
        exact ⟨(T.c (T.c q0 q1 (T.r q2 (T.r x1 x2))) x1 x2), (Steps.refl _), (Steps.cons (Step.root (Root.r11 (T.m q0 (T.r q1 (T.r q2 (T.r x1 x2)))) q2 x1 x2)) (Steps.cons (Step.firstC x1 x2 (Step.root (Root.r2 q0 q1 (T.r q2 (T.r x1 x2))))) (Steps.refl _)))⟩
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
    | @left _ t1 _ h1 =>
      exact ⟨(T.c t1 x1 x2), (Steps.cons (Step.firstC x1 x2 h1) (Steps.refl _)), (Steps.cons (Step.root (Root.r2 t1 x1 x2)) (Steps.refl _))⟩
    | @right _ _ t1 h1 =>
      cases h1 with
      | root hr =>
        rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩
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
          have e0 := (T.r.inj he).1
          have e1 := (T.r.inj he).2
          subst x1
          subst x2
          exact ⟨(T.c x0 q0 (T.c q1 q0 q0)), (Steps.refl _), (Steps.cons (Step.root (Root.r9 x0 q0 q1)) (Steps.refl _))⟩
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
      | @leftR _ t2 _ h2 =>
        exact ⟨(T.c x0 t2 x2), (Steps.cons (Step.secondC x0 x2 h2) (Steps.refl _)), (Steps.cons (Step.root (Root.r2 x0 t2 x2)) (Steps.refl _))⟩
      | @rightR _ _ t2 h2 =>
        exact ⟨(T.c x0 x1 t2), (Steps.cons (Step.thirdC x0 x1 h2) (Steps.refl _)), (Steps.cons (Step.right (T.m x0 (T.r x1 t2)) h2) (Steps.cons (Step.root (Root.r2 x0 x1 t2)) (Steps.refl _)))⟩
  | @right _ _ t0 h0 =>
    exact ⟨(T.c x0 x1 t0), (Steps.cons (Step.thirdC x0 x1 h0) (Steps.refl _)), (Steps.cons (Step.left t0 (Step.right x0 (Step.rightR x1 h0))) (Steps.cons (Step.root (Root.r2 x0 x1 t0)) (Steps.refl _)))⟩
end submission.Austin13992

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin13992
open T
theorem peak3 (x0 : T) (x1 : T) (x2 : T) {u : T} (h : Step (T.m x0 (T.c x1 x2 x0)) u) : Join x2 u := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩
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
      have e2 := e1.symm
      have cycle := congrArg size e2
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst x0
      have e2 := (T.c.inj e1).1
      have e3 := (T.c.inj e1).2.1
      have e4 := (T.c.inj e1).2.2
      subst x1
      subst x2
      exact ⟨q2, (Steps.refl _), (Steps.refl _)⟩
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
      have e2 := (T.c.inj e1).1
      have e3 := (T.c.inj e1).2.1
      have e4 := (T.c.inj e1).2.2
      subst x1
      subst x2
      subst q0
      exact ⟨q2, (Steps.refl _), (Steps.cons (Step.root (Root.r6 q2 q1)) (Steps.refl _))⟩
    · rw [ho]
      cases he
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
      have e2 := e1.symm
      have cycle := congrArg size e2
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst x0
      have e2 := (T.c.inj e1).1
      have e3 := (T.c.inj e1).2.1
      have e4 := (T.c.inj e1).2.2
      subst x1
      subst x2
      have e5 := e4.symm
      have cycle := congrArg size e5
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst x0
      have e2 := (T.c.inj e1).1
      have e3 := (T.c.inj e1).2.1
      have e4 := (T.c.inj e1).2.2
      subst x1
      subst x2
      have e5 := e4.symm
      have cycle := congrArg size e5
      simp only [size] at cycle
      omega
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
      have e2 := (T.c.inj e1).1
      have e3 := (T.c.inj e1).2.1
      have e4 := (T.c.inj e1).2.2
      subst x1
      subst x2
      have e5 := e4.symm
      have cycle := congrArg size e5
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst x0
      have e2 := (T.c.inj e1).1
      have e3 := (T.c.inj e1).2.1
      have e4 := (T.c.inj e1).2.2
      subst x1
      subst x2
      have cycle := congrArg size e4
      simp only [size] at cycle
      omega
  | @left _ t0 _ h0 =>
    exact ⟨x2, (Steps.refl _), (Steps.cons (Step.right t0 (Step.thirdC x1 x2 h0)) (Steps.cons (Step.root (Root.r3 t0 x1 x2)) (Steps.refl _)))⟩
  | @right _ _ t0 h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩
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
    | @firstC _ t1 _ _ h1 =>
      exact ⟨x2, (Steps.refl _), (Steps.cons (Step.root (Root.r3 x0 t1 x2)) (Steps.refl _))⟩
    | @secondC _ _ t1 _ h1 =>
      exact ⟨t1, (Steps.cons h1 (Steps.refl _)), (Steps.cons (Step.root (Root.r3 x0 x1 t1)) (Steps.refl _))⟩
    | @thirdC _ _ _ t1 h1 =>
      exact ⟨x2, (Steps.refl _), (Steps.cons (Step.left (T.c x1 x2 t1) h1) (Steps.cons (Step.root (Root.r3 t1 x1 x2)) (Steps.refl _)))⟩
end submission.Austin13992

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin13992
open T
theorem peak4 (x0 : T) (x1 : T) {u : T} (h : Step (T.m (T.r x0 x1) x1) u) : Join (T.r (T.m x0 x1) x1) u := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩
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
      subst q0
      have cycle := congrArg size e1
      simp only [size] at cycle
      omega
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
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := (T.r.inj e0).1
      have e3 := (T.r.inj e0).2
      subst x1
      subst x0
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
      have e2 := (T.r.inj e0).1
      have e3 := (T.r.inj e0).2
      subst x1
      subst x0
      have e4 := e3.symm
      have cycle := congrArg size e4
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
      have e2 := e0.symm
      subst q0
      have cycle := congrArg size e1
      simp only [size] at cycle
      omega
  | @left _ t0 _ h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩
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
        have e0 := (T.r.inj he).1
        have e1 := (T.r.inj he).2
        subst x0
        subst x1
        exact ⟨q0, (Steps.cons (Step.leftR (T.c q1 q0 q0) (Step.root (Root.r3 q0 q1 q0))) (Steps.cons (Step.root (Root.r6 q0 q1)) (Steps.refl _))), (Steps.cons (Step.root (Root.r3 q0 q1 q0)) (Steps.refl _))⟩
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
    | @leftR _ t1 _ h1 =>
      exact ⟨(T.r (T.m t1 x1) x1), (Steps.cons (Step.leftR x1 (Step.left x1 h1)) (Steps.refl _)), (Steps.cons (Step.root (Root.r4 t1 x1)) (Steps.refl _))⟩
    | @rightR _ _ t1 h1 =>
      exact ⟨(T.r (T.m x0 t1) t1), (Steps.cons (Step.leftR x1 (Step.right x0 h1)) (Steps.cons (Step.rightR (T.m x0 t1) h1) (Steps.refl _))), (Steps.cons (Step.right (T.r x0 t1) h1) (Steps.cons (Step.root (Root.r4 x0 t1)) (Steps.refl _)))⟩
  | @right _ _ t0 h0 =>
    exact ⟨(T.r (T.m x0 t0) t0), (Steps.cons (Step.leftR x1 (Step.right x0 h0)) (Steps.cons (Step.rightR (T.m x0 t0) h0) (Steps.refl _))), (Steps.cons (Step.left t0 (Step.rightR x0 h0)) (Steps.cons (Step.root (Root.r4 x0 t0)) (Steps.refl _)))⟩
end submission.Austin13992

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin13992
open T
theorem peak5 (x0 : T) (x1 : T) (x2 : T) {u : T} (h : Step (T.m x0 (T.c x1 x0 x2)) u) : Join (T.r x2 (T.c x1 x0 x2)) u := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩
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
      have e2 := e1.symm
      have cycle := congrArg size e2
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst x0
      have e2 := (T.c.inj e1).1
      have e3 := (T.c.inj e1).2.1
      have e4 := (T.c.inj e1).2.2
      subst x1
      subst q0
      subst x2
      exact ⟨q2, (Steps.cons (Step.root (Root.r6 q2 q1)) (Steps.refl _)), (Steps.refl _)⟩
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
      have e2 := (T.c.inj e1).1
      have e3 := (T.c.inj e1).2.1
      have e4 := (T.c.inj e1).2.2
      subst x1
      subst x2
      exact ⟨(T.r q2 (T.c q1 q0 q2)), (Steps.refl _), (Steps.refl _)⟩
    · rw [ho]
      cases he
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
      have e2 := e1.symm
      have cycle := congrArg size e2
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst x0
      have e2 := (T.c.inj e1).1
      have e3 := (T.c.inj e1).2.1
      have e4 := (T.c.inj e1).2.2
      subst x1
      have e5 := e3.symm
      have cycle := congrArg size e5
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst x0
      have e2 := (T.c.inj e1).1
      have e3 := (T.c.inj e1).2.1
      have e4 := (T.c.inj e1).2.2
      subst x1
      have e5 := e3.symm
      have cycle := congrArg size e5
      simp only [size] at cycle
      omega
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
      have e2 := (T.c.inj e1).1
      have e3 := (T.c.inj e1).2.1
      have e4 := (T.c.inj e1).2.2
      subst x1
      have e5 := e3.symm
      have cycle := congrArg size e5
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst x0
      have e2 := (T.c.inj e1).1
      have e3 := (T.c.inj e1).2.1
      have e4 := (T.c.inj e1).2.2
      subst x1
      have cycle := congrArg size e3
      simp only [size] at cycle
      omega
  | @left _ t0 _ h0 =>
    exact ⟨(T.r x2 (T.c x1 t0 x2)), (Steps.cons (Step.rightR x2 (Step.secondC x1 x2 h0)) (Steps.refl _)), (Steps.cons (Step.right t0 (Step.secondC x1 x2 h0)) (Steps.cons (Step.root (Root.r5 t0 x1 x2)) (Steps.refl _)))⟩
  | @right _ _ t0 h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩
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
    | @firstC _ t1 _ _ h1 =>
      exact ⟨(T.r x2 (T.c t1 x0 x2)), (Steps.cons (Step.rightR x2 (Step.firstC x0 x2 h1)) (Steps.refl _)), (Steps.cons (Step.root (Root.r5 x0 t1 x2)) (Steps.refl _))⟩
    | @secondC _ _ t1 _ h1 =>
      exact ⟨(T.r x2 (T.c x1 t1 x2)), (Steps.cons (Step.rightR x2 (Step.secondC x1 x2 h1)) (Steps.refl _)), (Steps.cons (Step.left (T.c x1 t1 x2) h1) (Steps.cons (Step.root (Root.r5 t1 x1 x2)) (Steps.refl _)))⟩
    | @thirdC _ _ _ t1 h1 =>
      exact ⟨(T.r t1 (T.c x1 x0 t1)), (Steps.cons (Step.leftR (T.c x1 x0 x2) h1) (Steps.cons (Step.rightR t1 (Step.thirdC x1 x0 h1)) (Steps.refl _))), (Steps.cons (Step.root (Root.r5 x0 x1 t1)) (Steps.refl _))⟩
end submission.Austin13992

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin13992
open T
theorem peak6 (x0 : T) (x1 : T) {u : T} (h : Step (T.r x0 (T.c x1 x0 x0)) u) : Join x0 u := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩
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
      have e0 := (T.r.inj he).1
      have e1 := (T.r.inj he).2
      subst x0
      have e2 := (T.c.inj e1).1
      have e3 := (T.c.inj e1).2.1
      have e4 := (T.c.inj e1).2.2
      subst x1
      exact ⟨q0, (Steps.refl _), (Steps.refl _)⟩
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
  | @leftR _ t0 _ h0 =>
    exact ⟨t0, (Steps.cons h0 (Steps.refl _)), (Steps.cons (Step.rightR t0 (Step.secondC x1 x0 h0)) (Steps.cons (Step.rightR t0 (Step.thirdC x1 t0 h0)) (Steps.cons (Step.root (Root.r6 t0 x1)) (Steps.refl _))))⟩
  | @rightR _ _ t0 h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩
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
    | @firstC _ t1 _ _ h1 =>
      exact ⟨x0, (Steps.refl _), (Steps.cons (Step.root (Root.r6 x0 t1)) (Steps.refl _))⟩
    | @secondC _ _ t1 _ h1 =>
      exact ⟨t1, (Steps.cons h1 (Steps.refl _)), (Steps.cons (Step.leftR (T.c x1 t1 x0) h1) (Steps.cons (Step.rightR t1 (Step.thirdC x1 t1 h1)) (Steps.cons (Step.root (Root.r6 t1 x1)) (Steps.refl _))))⟩
    | @thirdC _ _ _ t1 h1 =>
      exact ⟨t1, (Steps.cons h1 (Steps.refl _)), (Steps.cons (Step.leftR (T.c x1 x0 t1) h1) (Steps.cons (Step.rightR t1 (Step.secondC x1 t1 h1)) (Steps.cons (Step.root (Root.r6 t1 x1)) (Steps.refl _))))⟩
end submission.Austin13992

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin13992
open T
theorem peak7 (x0 : T) (x1 : T) (x2 : T) {u : T} (h : Step (T.m (T.c x0 x1 x2) x2) u) : Join (T.r (T.m x0 (T.r x1 x2)) x2) u := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩
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
      have e2 := (T.c.inj e0).1
      have e3 := (T.c.inj e0).2.1
      have e4 := (T.c.inj e0).2.2
      subst x2
      subst x0
      subst x1
      exact ⟨(T.r (T.m q0 (T.r q1 q2)) q2), (Steps.refl _), (Steps.refl _)⟩
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
      have e2 := (T.c.inj e0).1
      have e3 := (T.c.inj e0).2.1
      have e4 := (T.c.inj e0).2.2
      subst x2
      subst x0
      subst x1
      have cycle := congrArg size e4
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := (T.c.inj e0).1
      have e3 := (T.c.inj e0).2.1
      have e4 := (T.c.inj e0).2.2
      subst x2
      subst x0
      subst x1
      have e5 := e4.symm
      have cycle := congrArg size e5
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
  | @left _ t0 _ h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩
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
    | @firstC _ t1 _ _ h1 =>
      exact ⟨(T.r (T.m t1 (T.r x1 x2)) x2), (Steps.cons (Step.leftR x2 (Step.left (T.r x1 x2) h1)) (Steps.refl _)), (Steps.cons (Step.root (Root.r7 t1 x1 x2)) (Steps.refl _))⟩
    | @secondC _ _ t1 _ h1 =>
      exact ⟨(T.r (T.m x0 (T.r t1 x2)) x2), (Steps.cons (Step.leftR x2 (Step.right x0 (Step.leftR x2 h1))) (Steps.refl _)), (Steps.cons (Step.root (Root.r7 x0 t1 x2)) (Steps.refl _))⟩
    | @thirdC _ _ _ t1 h1 =>
      exact ⟨(T.r (T.m x0 (T.r x1 t1)) t1), (Steps.cons (Step.leftR x2 (Step.right x0 (Step.rightR x1 h1))) (Steps.cons (Step.rightR (T.m x0 (T.r x1 t1)) h1) (Steps.refl _))), (Steps.cons (Step.right (T.c x0 x1 t1) h1) (Steps.cons (Step.root (Root.r7 x0 x1 t1)) (Steps.refl _)))⟩
  | @right _ _ t0 h0 =>
    exact ⟨(T.r (T.m x0 (T.r x1 t0)) t0), (Steps.cons (Step.leftR x2 (Step.right x0 (Step.rightR x1 h0))) (Steps.cons (Step.rightR (T.m x0 (T.r x1 t0)) h0) (Steps.refl _))), (Steps.cons (Step.left t0 (Step.thirdC x0 x1 h0)) (Steps.cons (Step.root (Root.r7 x0 x1 t0)) (Steps.refl _)))⟩
end submission.Austin13992

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin13992
open T
theorem peak8 (x0 : T) (x1 : T) (x2 : T) {u : T} (h : Step (T.m (T.r x0 (T.r x1 x2)) x2) u) : Join (T.c (T.m x0 (T.r x1 x2)) x1 x2) u := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩
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
      subst q0
      have cycle := congrArg size e1
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := (T.r.inj e0).1
      have e3 := (T.r.inj e0).2
      subst x2
      subst x0
      have e4 := e3.symm
      have cycle := congrArg size e4
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
      cases he
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      cases e0
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := (T.r.inj e0).1
      have e3 := (T.r.inj e0).2
      subst x2
      subst x0
      have e4 := (T.r.inj e3).1
      have e5 := (T.r.inj e3).2
      subst x1
      exact ⟨(T.c (T.m q0 (T.r q1 q2)) q1 q2), (Steps.refl _), (Steps.refl _)⟩
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      cases e0
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := (T.r.inj e0).1
      have e3 := (T.r.inj e0).2
      subst x2
      subst x0
      have e4 := e3.symm
      have cycle := congrArg size e4
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
      have e2 := e0.symm
      subst q0
      have cycle := congrArg size e1
      simp only [size] at cycle
      omega
  | @left _ t0 _ h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩
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
        have e0 := (T.r.inj he).1
        have e1 := (T.r.inj he).2
        subst x0
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
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
    | @leftR _ t1 _ h1 =>
      exact ⟨(T.c (T.m t1 (T.r x1 x2)) x1 x2), (Steps.cons (Step.firstC x1 x2 (Step.left (T.r x1 x2) h1)) (Steps.refl _)), (Steps.cons (Step.root (Root.r8 t1 x1 x2)) (Steps.refl _))⟩
    | @rightR _ _ t1 h1 =>
      cases h1 with
      | root hr =>
        rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩
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
          have e0 := (T.r.inj he).1
          have e1 := (T.r.inj he).2
          subst x1
          subst x2
          exact ⟨(T.c (T.m x0 q0) q0 (T.c q1 q0 q0)), (Steps.cons (Step.firstC q0 (T.c q1 q0 q0) (Step.right x0 (Step.root (Root.r6 q0 q1)))) (Steps.refl _)), (Steps.cons (Step.root (Root.r10 x0 q0 q1)) (Steps.refl _))⟩
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
      | @leftR _ t2 _ h2 =>
        exact ⟨(T.c (T.m x0 (T.r t2 x2)) t2 x2), (Steps.cons (Step.firstC x1 x2 (Step.right x0 (Step.leftR x2 h2))) (Steps.cons (Step.secondC (T.m x0 (T.r t2 x2)) x2 h2) (Steps.refl _))), (Steps.cons (Step.root (Root.r8 x0 t2 x2)) (Steps.refl _))⟩
      | @rightR _ _ t2 h2 =>
        exact ⟨(T.c (T.m x0 (T.r x1 t2)) x1 t2), (Steps.cons (Step.firstC x1 x2 (Step.right x0 (Step.rightR x1 h2))) (Steps.cons (Step.thirdC (T.m x0 (T.r x1 t2)) x1 h2) (Steps.refl _))), (Steps.cons (Step.right (T.r x0 (T.r x1 t2)) h2) (Steps.cons (Step.root (Root.r8 x0 x1 t2)) (Steps.refl _)))⟩
  | @right _ _ t0 h0 =>
    exact ⟨(T.c (T.m x0 (T.r x1 t0)) x1 t0), (Steps.cons (Step.firstC x1 x2 (Step.right x0 (Step.rightR x1 h0))) (Steps.cons (Step.thirdC (T.m x0 (T.r x1 t0)) x1 h0) (Steps.refl _))), (Steps.cons (Step.left t0 (Step.rightR x0 (Step.rightR x1 h0))) (Steps.cons (Step.root (Root.r8 x0 x1 t0)) (Steps.refl _)))⟩
end submission.Austin13992

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin13992
open T
theorem peak9 (x0 : T) (x1 : T) (x2 : T) {u : T} (h : Step (T.m (T.m x0 x1) (T.c x2 x1 x1)) u) : Join (T.c x0 x1 (T.c x2 x1 x1)) u := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := (T.m.inj e0).1
      have e3 := (T.m.inj e0).2
      have e4 := e1.symm
      subst q1
      subst x0
      have cycle := congrArg size e3
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := (T.m.inj e0).1
      have e3 := (T.m.inj e0).2
      have e4 := e1.symm
      subst q2
      subst x0
      have cycle := congrArg size e3
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst q0
      have e3 := (T.c.inj e1).1
      have e4 := (T.c.inj e1).2.1
      have e5 := (T.c.inj e1).2.2
      subst x2
      subst x1
      have cycle := congrArg size e5
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
      have e3 := (T.c.inj e1).1
      have e4 := (T.c.inj e1).2.1
      have e5 := (T.c.inj e1).2.2
      subst x2
      have cycle := congrArg size e4
      simp only [size] at cycle
      omega
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
      have e2 := (T.m.inj e0).1
      have e3 := (T.m.inj e0).2
      have e4 := (T.c.inj e1).1
      have e5 := (T.c.inj e1).2.1
      have e6 := (T.c.inj e1).2.2
      subst x0
      subst x1
      subst x2
      exact ⟨(T.c q0 q1 (T.c q2 q1 q1)), (Steps.refl _), (Steps.refl _)⟩
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
      subst q0
      have e3 := (T.c.inj e1).1
      have e4 := (T.c.inj e1).2.1
      have e5 := (T.c.inj e1).2.2
      subst x2
      have cycle := congrArg size e4
      simp only [size] at cycle
      omega
  | @left _ t0 _ h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        subst x1
        exact ⟨(T.c (T.m q0 q1) q1 (T.c x2 q1 q1)), (Steps.refl _), (Steps.cons (Step.root (Root.r10 q0 q1 x2)) (Steps.refl _))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        subst x1
        exact ⟨(T.c (T.m q0 (T.r q1 q2)) q2 (T.c x2 q2 q2)), (Steps.refl _), (Steps.cons (Step.root (Root.r12 q0 q1 q2 x2)) (Steps.refl _))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        subst x1
        exact ⟨(T.c q0 (T.c q1 q2 q0) (T.c x2 (T.c q1 q2 q0) (T.c q1 q2 q0))), (Steps.refl _), (Steps.cons (Step.root (Root.r13 q2 x2 q1 q0)) (Steps.refl _))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        subst x1
        exact ⟨(T.c (T.r q0 q1) q1 (T.c x2 q1 q1)), (Steps.refl _), (Steps.cons (Step.root (Root.r10 (T.m q0 q1) q1 x2)) (Steps.cons (Step.firstC q1 (T.c x2 q1 q1) (Step.root (Root.r1 q0 q1))) (Steps.refl _)))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        subst x1
        exact ⟨(T.c q0 (T.c q1 q0 q2) (T.c x2 (T.c q1 q0 q2) (T.c q1 q0 q2))), (Steps.refl _), (Steps.cons (Step.root (Root.r10 q2 (T.c q1 q0 q2) x2)) (Steps.cons (Step.firstC (T.c q1 q0 q2) (T.c x2 (T.c q1 q0 q2) (T.c q1 q0 q2)) (Step.root (Root.r3 q2 q1 q0))) (Steps.refl _)))⟩
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        subst x1
        exact ⟨(T.c (T.c q0 q1 q2) q2 (T.c x2 q2 q2)), (Steps.refl _), (Steps.cons (Step.root (Root.r10 (T.m q0 (T.r q1 q2)) q2 x2)) (Steps.cons (Step.firstC q2 (T.c x2 q2 q2) (Step.root (Root.r2 q0 q1 q2))) (Steps.refl _)))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        subst x1
        exact ⟨(T.c (T.r q0 (T.r q1 q2)) q2 (T.c x2 q2 q2)), (Steps.refl _), (Steps.cons (Step.root (Root.r12 (T.m q0 (T.r q1 q2)) q1 q2 x2)) (Steps.cons (Step.firstC q2 (T.c x2 q2 q2) (Step.root (Root.r1 q0 (T.r q1 q2)))) (Steps.refl _)))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        subst x1
        exact ⟨(T.c (T.m q0 q1) (T.c q2 q1 q1) (T.c x2 (T.c q2 q1 q1) (T.c q2 q1 q1))), (Steps.refl _), (Steps.cons (Step.root (Root.r12 q0 q1 (T.c q2 q1 q1) x2)) (Steps.cons (Step.firstC (T.c q2 q1 q1) (T.c x2 (T.c q2 q1 q1) (T.c q2 q1 q1)) (Step.right q0 (Step.root (Root.r6 q1 q2)))) (Steps.refl _)))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        subst x1
        exact ⟨(T.c (T.r q0 q1) (T.c q2 q1 q1) (T.c x2 (T.c q2 q1 q1) (T.c q2 q1 q1))), (Steps.refl _), (Steps.cons (Step.root (Root.r12 (T.m q0 q1) q1 (T.c q2 q1 q1) x2)) (Steps.cons (Step.firstC (T.c q2 q1 q1) (T.c x2 (T.c q2 q1 q1) (T.c q2 q1 q1)) (Step.right (T.m q0 q1) (Step.root (Root.r6 q1 q2)))) (Steps.cons (Step.firstC (T.c q2 q1 q1) (T.c x2 (T.c q2 q1 q1) (T.c q2 q1 q1)) (Step.root (Root.r1 q0 q1))) (Steps.refl _))))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        subst x1
        exact ⟨(T.c (T.c q0 q1 (T.r q2 q3)) q3 (T.c x2 q3 q3)), (Steps.refl _), (Steps.cons (Step.root (Root.r12 (T.m q0 (T.r q1 (T.r q2 q3))) q2 q3 x2)) (Steps.cons (Step.firstC q3 (T.c x2 q3 q3) (Step.root (Root.r2 q0 q1 (T.r q2 q3)))) (Steps.refl _)))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        subst x1
        exact ⟨(T.c (T.c q0 q1 q2) (T.c q3 q2 q2) (T.c x2 (T.c q3 q2 q2) (T.c q3 q2 q2))), (Steps.refl _), (Steps.cons (Step.root (Root.r12 (T.m q0 (T.r q1 q2)) q2 (T.c q3 q2 q2) x2)) (Steps.cons (Step.firstC (T.c q3 q2 q2) (T.c x2 (T.c q3 q2 q2) (T.c q3 q2 q2)) (Step.right (T.m q0 (T.r q1 q2)) (Step.root (Root.r6 q2 q3)))) (Steps.cons (Step.firstC (T.c q3 q2 q2) (T.c x2 (T.c q3 q2 q2) (T.c q3 q2 q2)) (Step.root (Root.r2 q0 q1 q2))) (Steps.refl _))))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst x0
        subst x1
        exact ⟨(T.c q0 (T.c q1 (T.c q2 q0 q3) (T.c q2 q0 q3)) (T.c x2 (T.c q1 (T.c q2 q0 q3) (T.c q2 q0 q3)) (T.c q1 (T.c q2 q0 q3) (T.c q2 q0 q3)))), (Steps.refl _), (Steps.cons (Step.root (Root.r12 q3 (T.c q2 q0 q3) (T.c q1 (T.c q2 q0 q3) (T.c q2 q0 q3)) x2)) (Steps.cons (Step.firstC (T.c q1 (T.c q2 q0 q3) (T.c q2 q0 q3)) (T.c x2 (T.c q1 (T.c q2 q0 q3) (T.c q2 q0 q3)) (T.c q1 (T.c q2 q0 q3) (T.c q2 q0 q3))) (Step.right q3 (Step.root (Root.r6 (T.c q2 q0 q3) q1)))) (Steps.cons (Step.firstC (T.c q1 (T.c q2 q0 q3) (T.c q2 q0 q3)) (T.c x2 (T.c q1 (T.c q2 q0 q3) (T.c q2 q0 q3)) (T.c q1 (T.c q2 q0 q3) (T.c q2 q0 q3))) (Step.root (Root.r3 q3 q2 q0))) (Steps.refl _))))⟩
    | @left _ t1 _ h1 =>
      exact ⟨(T.c t1 x1 (T.c x2 x1 x1)), (Steps.cons (Step.firstC x1 (T.c x2 x1 x1) h1) (Steps.refl _)), (Steps.cons (Step.root (Root.r9 t1 x1 x2)) (Steps.refl _))⟩
    | @right _ _ t1 h1 =>
      exact ⟨(T.c x0 t1 (T.c x2 t1 t1)), (Steps.cons (Step.secondC x0 (T.c x2 x1 x1) h1) (Steps.cons (Step.thirdC x0 t1 (Step.secondC x2 x1 h1)) (Steps.cons (Step.thirdC x0 t1 (Step.thirdC x2 t1 h1)) (Steps.refl _)))), (Steps.cons (Step.right (T.m x0 t1) (Step.secondC x2 x1 h1)) (Steps.cons (Step.right (T.m x0 t1) (Step.thirdC x2 t1 h1)) (Steps.cons (Step.root (Root.r9 x0 t1 x2)) (Steps.refl _))))⟩
  | @right _ _ t0 h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩
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
    | @firstC _ t1 _ _ h1 =>
      exact ⟨(T.c x0 x1 (T.c t1 x1 x1)), (Steps.cons (Step.thirdC x0 x1 (Step.firstC x1 x1 h1)) (Steps.refl _)), (Steps.cons (Step.root (Root.r9 x0 x1 t1)) (Steps.refl _))⟩
    | @secondC _ _ t1 _ h1 =>
      exact ⟨(T.c x0 t1 (T.c x2 t1 t1)), (Steps.cons (Step.secondC x0 (T.c x2 x1 x1) h1) (Steps.cons (Step.thirdC x0 t1 (Step.secondC x2 x1 h1)) (Steps.cons (Step.thirdC x0 t1 (Step.thirdC x2 t1 h1)) (Steps.refl _)))), (Steps.cons (Step.left (T.c x2 t1 x1) (Step.right x0 h1)) (Steps.cons (Step.right (T.m x0 t1) (Step.thirdC x2 t1 h1)) (Steps.cons (Step.root (Root.r9 x0 t1 x2)) (Steps.refl _))))⟩
    | @thirdC _ _ _ t1 h1 =>
      exact ⟨(T.c x0 t1 (T.c x2 t1 t1)), (Steps.cons (Step.secondC x0 (T.c x2 x1 x1) h1) (Steps.cons (Step.thirdC x0 t1 (Step.secondC x2 x1 h1)) (Steps.cons (Step.thirdC x0 t1 (Step.thirdC x2 t1 h1)) (Steps.refl _)))), (Steps.cons (Step.left (T.c x2 x1 t1) (Step.right x0 h1)) (Steps.cons (Step.right (T.m x0 t1) (Step.secondC x2 t1 h1)) (Steps.cons (Step.root (Root.r9 x0 t1 x2)) (Steps.refl _))))⟩
end submission.Austin13992

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin13992
open T
theorem peak10 (x0 : T) (x1 : T) (x2 : T) {u : T} (h : Step (T.m (T.r x0 x1) (T.c x2 x1 x1)) u) : Join (T.c (T.m x0 x1) x1 (T.c x2 x1 x1)) u := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩
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
      subst q0
      have e3 := (T.c.inj e1).1
      have e4 := (T.c.inj e1).2.1
      have e5 := (T.c.inj e1).2.2
      subst x2
      subst x1
      have cycle := congrArg size e5
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := (T.r.inj e0).1
      have e3 := (T.r.inj e0).2
      have e4 := e1.symm
      subst q1
      subst x0
      have cycle := congrArg size e3
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst q0
      have e3 := (T.c.inj e1).1
      have e4 := (T.c.inj e1).2.1
      have e5 := (T.c.inj e1).2.2
      subst x2
      have cycle := congrArg size e4
      simp only [size] at cycle
      omega
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      cases e0
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := (T.r.inj e0).1
      have e3 := (T.r.inj e0).2
      have e4 := e1.symm
      subst q2
      subst x0
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
      have e2 := (T.r.inj e0).1
      have e3 := (T.r.inj e0).2
      have e4 := (T.c.inj e1).1
      have e5 := (T.c.inj e1).2.1
      have e6 := (T.c.inj e1).2.2
      subst x0
      subst x1
      subst x2
      exact ⟨(T.c (T.m q0 q1) q1 (T.c q2 q1 q1)), (Steps.refl _), (Steps.refl _)⟩
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
      subst q0
      have e3 := (T.c.inj e1).1
      have e4 := (T.c.inj e1).2.1
      have e5 := (T.c.inj e1).2.2
      subst x2
      have cycle := congrArg size e4
      simp only [size] at cycle
      omega
  | @left _ t0 _ h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩
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
        have e0 := (T.r.inj he).1
        have e1 := (T.r.inj he).2
        subst x0
        subst x1
        exact ⟨(T.c q0 (T.c q1 q0 q0) (T.c x2 (T.c q1 q0 q0) (T.c q1 q0 q0))), (Steps.cons (Step.firstC (T.c q1 q0 q0) (T.c x2 (T.c q1 q0 q0) (T.c q1 q0 q0)) (Step.root (Root.r3 q0 q1 q0))) (Steps.refl _)), (Steps.cons (Step.root (Root.r13 q0 x2 q1 q0)) (Steps.refl _))⟩
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
    | @leftR _ t1 _ h1 =>
      exact ⟨(T.c (T.m t1 x1) x1 (T.c x2 x1 x1)), (Steps.cons (Step.firstC x1 (T.c x2 x1 x1) (Step.left x1 h1)) (Steps.refl _)), (Steps.cons (Step.root (Root.r10 t1 x1 x2)) (Steps.refl _))⟩
    | @rightR _ _ t1 h1 =>
      exact ⟨(T.c (T.m x0 t1) t1 (T.c x2 t1 t1)), (Steps.cons (Step.firstC x1 (T.c x2 x1 x1) (Step.right x0 h1)) (Steps.cons (Step.secondC (T.m x0 t1) (T.c x2 x1 x1) h1) (Steps.cons (Step.thirdC (T.m x0 t1) t1 (Step.secondC x2 x1 h1)) (Steps.cons (Step.thirdC (T.m x0 t1) t1 (Step.thirdC x2 t1 h1)) (Steps.refl _))))), (Steps.cons (Step.right (T.r x0 t1) (Step.secondC x2 x1 h1)) (Steps.cons (Step.right (T.r x0 t1) (Step.thirdC x2 t1 h1)) (Steps.cons (Step.root (Root.r10 x0 t1 x2)) (Steps.refl _))))⟩
  | @right _ _ t0 h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩
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
    | @firstC _ t1 _ _ h1 =>
      exact ⟨(T.c (T.m x0 x1) x1 (T.c t1 x1 x1)), (Steps.cons (Step.thirdC (T.m x0 x1) x1 (Step.firstC x1 x1 h1)) (Steps.refl _)), (Steps.cons (Step.root (Root.r10 x0 x1 t1)) (Steps.refl _))⟩
    | @secondC _ _ t1 _ h1 =>
      exact ⟨(T.c (T.m x0 t1) t1 (T.c x2 t1 t1)), (Steps.cons (Step.firstC x1 (T.c x2 x1 x1) (Step.right x0 h1)) (Steps.cons (Step.secondC (T.m x0 t1) (T.c x2 x1 x1) h1) (Steps.cons (Step.thirdC (T.m x0 t1) t1 (Step.secondC x2 x1 h1)) (Steps.cons (Step.thirdC (T.m x0 t1) t1 (Step.thirdC x2 t1 h1)) (Steps.refl _))))), (Steps.cons (Step.left (T.c x2 t1 x1) (Step.rightR x0 h1)) (Steps.cons (Step.right (T.r x0 t1) (Step.thirdC x2 t1 h1)) (Steps.cons (Step.root (Root.r10 x0 t1 x2)) (Steps.refl _))))⟩
    | @thirdC _ _ _ t1 h1 =>
      exact ⟨(T.c (T.m x0 t1) t1 (T.c x2 t1 t1)), (Steps.cons (Step.firstC x1 (T.c x2 x1 x1) (Step.right x0 h1)) (Steps.cons (Step.secondC (T.m x0 t1) (T.c x2 x1 x1) h1) (Steps.cons (Step.thirdC (T.m x0 t1) t1 (Step.secondC x2 x1 h1)) (Steps.cons (Step.thirdC (T.m x0 t1) t1 (Step.thirdC x2 t1 h1)) (Steps.refl _))))), (Steps.cons (Step.left (T.c x2 x1 t1) (Step.rightR x0 h1)) (Steps.cons (Step.right (T.r x0 t1) (Step.secondC x2 t1 h1)) (Steps.cons (Step.root (Root.r10 x0 t1 x2)) (Steps.refl _))))⟩
end submission.Austin13992

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin13992
open T
theorem peak11 (x0 : T) (x1 : T) (x2 : T) (x3 : T) {u : T} (h : Step (T.m (T.c x0 x1 (T.r x2 x3)) x3) u) : Join (T.c (T.m x0 (T.r x1 (T.r x2 x3))) x2 x3) u := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩
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
      have e2 := (T.c.inj e0).1
      have e3 := (T.c.inj e0).2.1
      have e4 := (T.c.inj e0).2.2
      subst x3
      subst x0
      subst x1
      have e5 := e4.symm
      have cycle := congrArg size e5
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
      have e2 := (T.c.inj e0).1
      have e3 := (T.c.inj e0).2.1
      have e4 := (T.c.inj e0).2.2
      subst x3
      subst x0
      subst x1
      have e5 := (T.r.inj e4).1
      have e6 := (T.r.inj e4).2
      subst x2
      exact ⟨(T.c (T.m q0 (T.r q1 (T.r q2 q3))) q2 q3), (Steps.refl _), (Steps.refl _)⟩
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := (T.c.inj e0).1
      have e3 := (T.c.inj e0).2.1
      have e4 := (T.c.inj e0).2.2
      subst x3
      subst x0
      subst x1
      have e5 := e4.symm
      have cycle := congrArg size e5
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
  | @left _ t0 _ h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩
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
    | @firstC _ t1 _ _ h1 =>
      exact ⟨(T.c (T.m t1 (T.r x1 (T.r x2 x3))) x2 x3), (Steps.cons (Step.firstC x2 x3 (Step.left (T.r x1 (T.r x2 x3)) h1)) (Steps.refl _)), (Steps.cons (Step.root (Root.r11 t1 x1 x2 x3)) (Steps.refl _))⟩
    | @secondC _ _ t1 _ h1 =>
      exact ⟨(T.c (T.m x0 (T.r t1 (T.r x2 x3))) x2 x3), (Steps.cons (Step.firstC x2 x3 (Step.right x0 (Step.leftR (T.r x2 x3) h1))) (Steps.refl _)), (Steps.cons (Step.root (Root.r11 x0 t1 x2 x3)) (Steps.refl _))⟩
    | @thirdC _ _ _ t1 h1 =>
      cases h1 with
      | root hr =>
        rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩
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
          have e0 := (T.r.inj he).1
          have e1 := (T.r.inj he).2
          subst x2
          subst x3
          exact ⟨(T.c (T.m x0 (T.r x1 q0)) q0 (T.c q1 q0 q0)), (Steps.cons (Step.firstC q0 (T.c q1 q0 q0) (Step.right x0 (Step.rightR x1 (Step.root (Root.r6 q0 q1))))) (Steps.refl _)), (Steps.cons (Step.root (Root.r12 x0 x1 q0 q1)) (Steps.refl _))⟩
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
      | @leftR _ t2 _ h2 =>
        exact ⟨(T.c (T.m x0 (T.r x1 (T.r t2 x3))) t2 x3), (Steps.cons (Step.firstC x2 x3 (Step.right x0 (Step.rightR x1 (Step.leftR x3 h2)))) (Steps.cons (Step.secondC (T.m x0 (T.r x1 (T.r t2 x3))) x3 h2) (Steps.refl _))), (Steps.cons (Step.root (Root.r11 x0 x1 t2 x3)) (Steps.refl _))⟩
      | @rightR _ _ t2 h2 =>
        exact ⟨(T.c (T.m x0 (T.r x1 (T.r x2 t2))) x2 t2), (Steps.cons (Step.firstC x2 x3 (Step.right x0 (Step.rightR x1 (Step.rightR x2 h2)))) (Steps.cons (Step.thirdC (T.m x0 (T.r x1 (T.r x2 t2))) x2 h2) (Steps.refl _))), (Steps.cons (Step.right (T.c x0 x1 (T.r x2 t2)) h2) (Steps.cons (Step.root (Root.r11 x0 x1 x2 t2)) (Steps.refl _)))⟩
  | @right _ _ t0 h0 =>
    exact ⟨(T.c (T.m x0 (T.r x1 (T.r x2 t0))) x2 t0), (Steps.cons (Step.firstC x2 x3 (Step.right x0 (Step.rightR x1 (Step.rightR x2 h0)))) (Steps.cons (Step.thirdC (T.m x0 (T.r x1 (T.r x2 t0))) x2 h0) (Steps.refl _))), (Steps.cons (Step.left t0 (Step.thirdC x0 x1 (Step.rightR x2 h0))) (Steps.cons (Step.root (Root.r11 x0 x1 x2 t0)) (Steps.refl _)))⟩
end submission.Austin13992

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin13992
open T
theorem peak12 (x0 : T) (x1 : T) (x2 : T) (x3 : T) {u : T} (h : Step (T.m (T.c x0 x1 x2) (T.c x3 x2 x2)) u) : Join (T.c (T.m x0 (T.r x1 x2)) x2 (T.c x3 x2 x2)) u := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩
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
      subst q0
      have e3 := (T.c.inj e1).1
      have e4 := (T.c.inj e1).2.1
      have e5 := (T.c.inj e1).2.2
      subst x3
      subst x2
      have cycle := congrArg size e5
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
      have e3 := (T.c.inj e1).1
      have e4 := (T.c.inj e1).2.1
      have e5 := (T.c.inj e1).2.2
      subst x3
      have cycle := congrArg size e4
      simp only [size] at cycle
      omega
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := (T.c.inj e0).1
      have e3 := (T.c.inj e0).2.1
      have e4 := (T.c.inj e0).2.2
      have e5 := e1.symm
      subst q2
      subst x0
      subst x1
      have cycle := congrArg size e4
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
      have e2 := (T.c.inj e0).1
      have e3 := (T.c.inj e0).2.1
      have e4 := (T.c.inj e0).2.2
      have e5 := e1.symm
      subst q3
      subst x0
      subst x1
      have cycle := congrArg size e4
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := (T.c.inj e0).1
      have e3 := (T.c.inj e0).2.1
      have e4 := (T.c.inj e0).2.2
      have e5 := (T.c.inj e1).1
      have e6 := (T.c.inj e1).2.1
      have e7 := (T.c.inj e1).2.2
      subst x0
      subst x1
      subst x2
      subst x3
      exact ⟨(T.c (T.m q0 (T.r q1 q2)) q2 (T.c q3 q2 q2)), (Steps.refl _), (Steps.refl _)⟩
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst q0
      have e3 := (T.c.inj e1).1
      have e4 := (T.c.inj e1).2.1
      have e5 := (T.c.inj e1).2.2
      subst x3
      have cycle := congrArg size e4
      simp only [size] at cycle
      omega
  | @left _ t0 _ h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩
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
    | @firstC _ t1 _ _ h1 =>
      exact ⟨(T.c (T.m t1 (T.r x1 x2)) x2 (T.c x3 x2 x2)), (Steps.cons (Step.firstC x2 (T.c x3 x2 x2) (Step.left (T.r x1 x2) h1)) (Steps.refl _)), (Steps.cons (Step.root (Root.r12 t1 x1 x2 x3)) (Steps.refl _))⟩
    | @secondC _ _ t1 _ h1 =>
      exact ⟨(T.c (T.m x0 (T.r t1 x2)) x2 (T.c x3 x2 x2)), (Steps.cons (Step.firstC x2 (T.c x3 x2 x2) (Step.right x0 (Step.leftR x2 h1))) (Steps.refl _)), (Steps.cons (Step.root (Root.r12 x0 t1 x2 x3)) (Steps.refl _))⟩
    | @thirdC _ _ _ t1 h1 =>
      exact ⟨(T.c (T.m x0 (T.r x1 t1)) t1 (T.c x3 t1 t1)), (Steps.cons (Step.firstC x2 (T.c x3 x2 x2) (Step.right x0 (Step.rightR x1 h1))) (Steps.cons (Step.secondC (T.m x0 (T.r x1 t1)) (T.c x3 x2 x2) h1) (Steps.cons (Step.thirdC (T.m x0 (T.r x1 t1)) t1 (Step.secondC x3 x2 h1)) (Steps.cons (Step.thirdC (T.m x0 (T.r x1 t1)) t1 (Step.thirdC x3 t1 h1)) (Steps.refl _))))), (Steps.cons (Step.right (T.c x0 x1 t1) (Step.secondC x3 x2 h1)) (Steps.cons (Step.right (T.c x0 x1 t1) (Step.thirdC x3 t1 h1)) (Steps.cons (Step.root (Root.r12 x0 x1 t1 x3)) (Steps.refl _))))⟩
  | @right _ _ t0 h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩
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
    | @firstC _ t1 _ _ h1 =>
      exact ⟨(T.c (T.m x0 (T.r x1 x2)) x2 (T.c t1 x2 x2)), (Steps.cons (Step.thirdC (T.m x0 (T.r x1 x2)) x2 (Step.firstC x2 x2 h1)) (Steps.refl _)), (Steps.cons (Step.root (Root.r12 x0 x1 x2 t1)) (Steps.refl _))⟩
    | @secondC _ _ t1 _ h1 =>
      exact ⟨(T.c (T.m x0 (T.r x1 t1)) t1 (T.c x3 t1 t1)), (Steps.cons (Step.firstC x2 (T.c x3 x2 x2) (Step.right x0 (Step.rightR x1 h1))) (Steps.cons (Step.secondC (T.m x0 (T.r x1 t1)) (T.c x3 x2 x2) h1) (Steps.cons (Step.thirdC (T.m x0 (T.r x1 t1)) t1 (Step.secondC x3 x2 h1)) (Steps.cons (Step.thirdC (T.m x0 (T.r x1 t1)) t1 (Step.thirdC x3 t1 h1)) (Steps.refl _))))), (Steps.cons (Step.left (T.c x3 t1 x2) (Step.thirdC x0 x1 h1)) (Steps.cons (Step.right (T.c x0 x1 t1) (Step.thirdC x3 t1 h1)) (Steps.cons (Step.root (Root.r12 x0 x1 t1 x3)) (Steps.refl _))))⟩
    | @thirdC _ _ _ t1 h1 =>
      exact ⟨(T.c (T.m x0 (T.r x1 t1)) t1 (T.c x3 t1 t1)), (Steps.cons (Step.firstC x2 (T.c x3 x2 x2) (Step.right x0 (Step.rightR x1 h1))) (Steps.cons (Step.secondC (T.m x0 (T.r x1 t1)) (T.c x3 x2 x2) h1) (Steps.cons (Step.thirdC (T.m x0 (T.r x1 t1)) t1 (Step.secondC x3 x2 h1)) (Steps.cons (Step.thirdC (T.m x0 (T.r x1 t1)) t1 (Step.thirdC x3 t1 h1)) (Steps.refl _))))), (Steps.cons (Step.left (T.c x3 x2 t1) (Step.thirdC x0 x1 h1)) (Steps.cons (Step.right (T.c x0 x1 t1) (Step.secondC x3 t1 h1)) (Steps.cons (Step.root (Root.r12 x0 x1 t1 x3)) (Steps.refl _))))⟩
end submission.Austin13992

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin13992
open T
theorem peak13 (x0 : T) (x1 : T) (x2 : T) (x3 : T) {u : T} (h : Step (T.m x0 (T.c x1 (T.c x2 x0 x3) (T.c x2 x0 x3))) u) : Join (T.c x3 (T.c x2 x0 x3) (T.c x1 (T.c x2 x0 x3) (T.c x2 x0 x3))) u := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩
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
      have e2 := e1.symm
      have cycle := congrArg size e2
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst x0
      have e2 := (T.c.inj e1).1
      have e3 := (T.c.inj e1).2.1
      have e4 := (T.c.inj e1).2.2
      subst x1
      have e5 := e3.symm
      subst q2
      have e6 := e4.symm
      have cycle := congrArg size e6
      simp only [size] at cycle
      omega
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
      have e2 := (T.c.inj e1).1
      have e3 := (T.c.inj e1).2.1
      have e4 := (T.c.inj e1).2.2
      subst x1
      have e5 := e3.symm
      have cycle := congrArg size e5
      simp only [size] at cycle
      omega
    · rw [ho]
      cases he
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
      have e2 := e1.symm
      have cycle := congrArg size e2
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst x0
      have e2 := (T.c.inj e1).1
      have e3 := (T.c.inj e1).2.1
      have e4 := (T.c.inj e1).2.2
      subst x1
      have e5 := e3.symm
      have cycle := congrArg size e5
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst x0
      have e2 := (T.c.inj e1).1
      have e3 := (T.c.inj e1).2.1
      have e4 := (T.c.inj e1).2.2
      subst x1
      have e5 := e3.symm
      have cycle := congrArg size e5
      simp only [size] at cycle
      omega
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
      have e2 := (T.c.inj e1).1
      have e3 := (T.c.inj e1).2.1
      have e4 := (T.c.inj e1).2.2
      subst x1
      have e5 := e3.symm
      have cycle := congrArg size e5
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst x0
      have e2 := (T.c.inj e1).1
      have e3 := (T.c.inj e1).2.1
      have e4 := (T.c.inj e1).2.2
      subst x1
      have e5 := (T.c.inj e3).1
      have e6 := (T.c.inj e3).2.1
      have e7 := (T.c.inj e3).2.2
      have e8 := (T.c.inj e4).1
      have e9 := (T.c.inj e4).2.1
      have e10 := (T.c.inj e4).2.2
      subst x2
      subst x3
      exact ⟨(T.c q3 (T.c q2 q0 q3) (T.c q1 (T.c q2 q0 q3) (T.c q2 q0 q3))), (Steps.refl _), (Steps.refl _)⟩
  | @left _ t0 _ h0 =>
    exact ⟨(T.c x3 (T.c x2 t0 x3) (T.c x1 (T.c x2 t0 x3) (T.c x2 t0 x3))), (Steps.cons (Step.secondC x3 (T.c x1 (T.c x2 x0 x3) (T.c x2 x0 x3)) (Step.secondC x2 x3 h0)) (Steps.cons (Step.thirdC x3 (T.c x2 t0 x3) (Step.secondC x1 (T.c x2 x0 x3) (Step.secondC x2 x3 h0))) (Steps.cons (Step.thirdC x3 (T.c x2 t0 x3) (Step.thirdC x1 (T.c x2 t0 x3) (Step.secondC x2 x3 h0))) (Steps.refl _)))), (Steps.cons (Step.right t0 (Step.secondC x1 (T.c x2 x0 x3) (Step.secondC x2 x3 h0))) (Steps.cons (Step.right t0 (Step.thirdC x1 (T.c x2 t0 x3) (Step.secondC x2 x3 h0))) (Steps.cons (Step.root (Root.r13 t0 x1 x2 x3)) (Steps.refl _))))⟩
  | @right _ _ t0 h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩
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
    | @firstC _ t1 _ _ h1 =>
      exact ⟨(T.c x3 (T.c x2 x0 x3) (T.c t1 (T.c x2 x0 x3) (T.c x2 x0 x3))), (Steps.cons (Step.thirdC x3 (T.c x2 x0 x3) (Step.firstC (T.c x2 x0 x3) (T.c x2 x0 x3) h1)) (Steps.refl _)), (Steps.cons (Step.root (Root.r13 x0 t1 x2 x3)) (Steps.refl _))⟩
    | @secondC _ _ t1 _ h1 =>
      cases h1 with
      | root hr =>
        rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩
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
      | @firstC _ t2 _ _ h2 =>
        exact ⟨(T.c x3 (T.c t2 x0 x3) (T.c x1 (T.c t2 x0 x3) (T.c t2 x0 x3))), (Steps.cons (Step.secondC x3 (T.c x1 (T.c x2 x0 x3) (T.c x2 x0 x3)) (Step.firstC x0 x3 h2)) (Steps.cons (Step.thirdC x3 (T.c t2 x0 x3) (Step.secondC x1 (T.c x2 x0 x3) (Step.firstC x0 x3 h2))) (Steps.cons (Step.thirdC x3 (T.c t2 x0 x3) (Step.thirdC x1 (T.c t2 x0 x3) (Step.firstC x0 x3 h2))) (Steps.refl _)))), (Steps.cons (Step.right x0 (Step.thirdC x1 (T.c t2 x0 x3) (Step.firstC x0 x3 h2))) (Steps.cons (Step.root (Root.r13 x0 x1 t2 x3)) (Steps.refl _)))⟩
      | @secondC _ _ t2 _ h2 =>
        exact ⟨(T.c x3 (T.c x2 t2 x3) (T.c x1 (T.c x2 t2 x3) (T.c x2 t2 x3))), (Steps.cons (Step.secondC x3 (T.c x1 (T.c x2 x0 x3) (T.c x2 x0 x3)) (Step.secondC x2 x3 h2)) (Steps.cons (Step.thirdC x3 (T.c x2 t2 x3) (Step.secondC x1 (T.c x2 x0 x3) (Step.secondC x2 x3 h2))) (Steps.cons (Step.thirdC x3 (T.c x2 t2 x3) (Step.thirdC x1 (T.c x2 t2 x3) (Step.secondC x2 x3 h2))) (Steps.refl _)))), (Steps.cons (Step.left (T.c x1 (T.c x2 t2 x3) (T.c x2 x0 x3)) h2) (Steps.cons (Step.right t2 (Step.thirdC x1 (T.c x2 t2 x3) (Step.secondC x2 x3 h2))) (Steps.cons (Step.root (Root.r13 t2 x1 x2 x3)) (Steps.refl _))))⟩
      | @thirdC _ _ _ t2 h2 =>
        exact ⟨(T.c t2 (T.c x2 x0 t2) (T.c x1 (T.c x2 x0 t2) (T.c x2 x0 t2))), (Steps.cons (Step.firstC (T.c x2 x0 x3) (T.c x1 (T.c x2 x0 x3) (T.c x2 x0 x3)) h2) (Steps.cons (Step.secondC t2 (T.c x1 (T.c x2 x0 x3) (T.c x2 x0 x3)) (Step.thirdC x2 x0 h2)) (Steps.cons (Step.thirdC t2 (T.c x2 x0 t2) (Step.secondC x1 (T.c x2 x0 x3) (Step.thirdC x2 x0 h2))) (Steps.cons (Step.thirdC t2 (T.c x2 x0 t2) (Step.thirdC x1 (T.c x2 x0 t2) (Step.thirdC x2 x0 h2))) (Steps.refl _))))), (Steps.cons (Step.right x0 (Step.thirdC x1 (T.c x2 x0 t2) (Step.thirdC x2 x0 h2))) (Steps.cons (Step.root (Root.r13 x0 x1 x2 t2)) (Steps.refl _)))⟩
    | @thirdC _ _ _ t1 h1 =>
      cases h1 with
      | root hr =>
        rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩ | ⟨q0, q1, q2, q3, he, ho⟩
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
      | @firstC _ t2 _ _ h2 =>
        exact ⟨(T.c x3 (T.c t2 x0 x3) (T.c x1 (T.c t2 x0 x3) (T.c t2 x0 x3))), (Steps.cons (Step.secondC x3 (T.c x1 (T.c x2 x0 x3) (T.c x2 x0 x3)) (Step.firstC x0 x3 h2)) (Steps.cons (Step.thirdC x3 (T.c t2 x0 x3) (Step.secondC x1 (T.c x2 x0 x3) (Step.firstC x0 x3 h2))) (Steps.cons (Step.thirdC x3 (T.c t2 x0 x3) (Step.thirdC x1 (T.c t2 x0 x3) (Step.firstC x0 x3 h2))) (Steps.refl _)))), (Steps.cons (Step.right x0 (Step.secondC x1 (T.c t2 x0 x3) (Step.firstC x0 x3 h2))) (Steps.cons (Step.root (Root.r13 x0 x1 t2 x3)) (Steps.refl _)))⟩
      | @secondC _ _ t2 _ h2 =>
        exact ⟨(T.c x3 (T.c x2 t2 x3) (T.c x1 (T.c x2 t2 x3) (T.c x2 t2 x3))), (Steps.cons (Step.secondC x3 (T.c x1 (T.c x2 x0 x3) (T.c x2 x0 x3)) (Step.secondC x2 x3 h2)) (Steps.cons (Step.thirdC x3 (T.c x2 t2 x3) (Step.secondC x1 (T.c x2 x0 x3) (Step.secondC x2 x3 h2))) (Steps.cons (Step.thirdC x3 (T.c x2 t2 x3) (Step.thirdC x1 (T.c x2 t2 x3) (Step.secondC x2 x3 h2))) (Steps.refl _)))), (Steps.cons (Step.left (T.c x1 (T.c x2 x0 x3) (T.c x2 t2 x3)) h2) (Steps.cons (Step.right t2 (Step.secondC x1 (T.c x2 t2 x3) (Step.secondC x2 x3 h2))) (Steps.cons (Step.root (Root.r13 t2 x1 x2 x3)) (Steps.refl _))))⟩
      | @thirdC _ _ _ t2 h2 =>
        exact ⟨(T.c t2 (T.c x2 x0 t2) (T.c x1 (T.c x2 x0 t2) (T.c x2 x0 t2))), (Steps.cons (Step.firstC (T.c x2 x0 x3) (T.c x1 (T.c x2 x0 x3) (T.c x2 x0 x3)) h2) (Steps.cons (Step.secondC t2 (T.c x1 (T.c x2 x0 x3) (T.c x2 x0 x3)) (Step.thirdC x2 x0 h2)) (Steps.cons (Step.thirdC t2 (T.c x2 x0 t2) (Step.secondC x1 (T.c x2 x0 x3) (Step.thirdC x2 x0 h2))) (Steps.cons (Step.thirdC t2 (T.c x2 x0 t2) (Step.thirdC x1 (T.c x2 x0 t2) (Step.thirdC x2 x0 h2))) (Steps.refl _))))), (Steps.cons (Step.right x0 (Step.secondC x1 (T.c x2 x0 t2) (Step.thirdC x2 x0 h2))) (Steps.cons (Step.root (Root.r13 x0 x1 x2 t2)) (Steps.refl _)))⟩
end submission.Austin13992

set_option autoImplicit false
namespace submission.Austin13992
open T
theorem root_step {x y z : T} (h : Root x y) (k : Step x z) : Join y z := by
  cases h with
  | r1 => exact peak1 _ _ k
  | r2 => exact peak2 _ _ _ k
  | r3 => exact peak3 _ _ _ k
  | r4 => exact peak4 _ _ k
  | r5 => exact peak5 _ _ _ k
  | r6 => exact peak6 _ _ k
  | r7 => exact peak7 _ _ _ k
  | r8 => exact peak8 _ _ _ k
  | r9 => exact peak9 _ _ _ k
  | r10 => exact peak10 _ _ _ k
  | r11 => exact peak11 _ _ _ _ k
  | r12 => exact peak12 _ _ _ _ k
  | r13 => exact peak13 _ _ _ _ k
theorem local_join {x y z : T} (h : Step x y) (k : Step x z) : Join y z := by
  induction h generalizing z with
  | root hr => exact root_step hr k
  | underK h ih =>
    cases k with
    | root hr => exact (root_step hr (.underK h)).symm
    | underK k => exact (ih k).underK
  | underV h ih =>
    cases k with
    | root hr => exact (root_step hr (.underV h)).symm
    | underV k => exact (ih k).underV
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
  | leftR c h ih =>
    cases k with
    | root hr => exact (root_step hr (.leftR c h)).symm
    | leftR _ k => exact (ih k).leftR c
    | @rightR x _ z k =>
      exact ⟨r _ z, Steps.single (.rightR _ k), Steps.single (.leftR z h)⟩
  | rightR c h ih =>
    cases k with
    | root hr => exact (root_step hr (.rightR c h)).symm
    | @leftR x y _ k =>
      exact ⟨r y _, Steps.single (.leftR _ k), Steps.single (.rightR y h)⟩
    | rightR _ k => exact (ih k).rightR c
  | firstC b d h ih =>
    cases k with
    | root hr => exact (root_step hr (.firstC b d h)).symm
    | firstC _ _ k => exact (ih k).firstC b d
    | @secondC _ _ b2 _ k =>
      exact ⟨c _ b2 d, Steps.single (.secondC _ d k), Steps.single (.firstC b2 d h)⟩
    | @thirdC _ _ _ d2 k =>
      exact ⟨c _ b d2, Steps.single (.thirdC _ b k), Steps.single (.firstC b d2 h)⟩
  | secondC aa d h ih =>
    cases k with
    | root hr => exact (root_step hr (.secondC aa d h)).symm
    | @firstC _ a2 _ _ k =>
      exact ⟨c a2 _ d, Steps.single (.firstC _ d k), Steps.single (.secondC a2 d h)⟩
    | secondC _ _ k => exact (ih k).secondC aa d
    | @thirdC _ _ _ d2 k =>
      exact ⟨c aa _ d2, Steps.single (.thirdC aa _ k), Steps.single (.secondC aa d2 h)⟩
  | thirdC aa b h ih =>
    cases k with
    | root hr => exact (root_step hr (.thirdC aa b h)).symm
    | @firstC _ a2 _ _ k =>
      exact ⟨c a2 b _, Steps.single (.firstC b _ k), Steps.single (.thirdC a2 b h)⟩
    | @secondC _ _ b2 _ k =>
      exact ⟨c aa b2 _, Steps.single (.secondC aa _ k), Steps.single (.thirdC aa b2 h)⟩
    | thirdC _ _ k => exact (ih k).thirdC aa b
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

/-- Newman's argument specialized to the strictly decreasing positive weighted tree size. -/
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
          obtain ⟨normalTarget, hde, he⟩ := normal_exists d
          have hye := ih (size p) (hx ▸ step_decreases hxp) p rfl y normalTarget
            hy he hpy (hpd.trans hde)
          have hze := ih (size q) (hx ▸ step_decreases hxq) q rfl z normalTarget
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

theorem norm_m_left (p q : T) : norm (m (norm p) q) = norm (m p q) :=
  (norm_steps (Steps.left q (steps_norm p))).symm
theorem norm_m_right (p q : T) : norm (m p (norm q)) = norm (m p q) :=
  (norm_steps (Steps.right p (steps_norm q))).symm
end submission.Austin13992

set_option autoImplicit false
namespace submission.Austin13992
open T
def Carrier := {x : T // Normal x}
noncomputable def mul (x y : Carrier) : Carrier :=
  ⟨norm (m x.val y.val), norm_normal _⟩
theorem equation13992 (x y z : Carrier) :
    (mul y (mul (mul z (mul (mul x y) y)) y)) = x := by
  apply Subtype.ext
  change (norm (T.m y.val (norm (T.m (norm (T.m z.val (norm (T.m (norm (T.m x.val y.val)) y.val)))) y.val)))) = x.val
  simp only [norm_m_left, norm_m_right]
  have h : Steps (T.m y.val (T.m (T.m z.val (T.m (T.m x.val y.val) y.val)) y.val)) x.val :=
    (Steps.cons (Step.right y.val (Step.left y.val (Step.right z.val (Step.root (Root.r1 x.val y.val))))) (Steps.cons (Step.right y.val (Step.root (Root.r2 z.val x.val y.val))) (Steps.cons (Step.root (Root.r3 y.val z.val x.val)) (Steps.refl _))))
  exact (norm_steps h).trans (norm_of_normal x.property)
def tower : Nat → T
  | 0 => a
  | n+1 => k (tower n)
theorem tower_normal (n : Nat) : Normal (tower n) := by
  induction n with
  | zero =>
    intro y h
    cases h with
    | root h => cases h
  | succ n ih =>
    intro y h
    cases h with
    | root h => cases h
    | underK h => exact ih h
theorem tower_size (n : Nat) : size (tower n) = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [tower, size, ih] <;> omega
def embed (n : Nat) : Carrier := ⟨tower n, tower_normal n⟩
theorem embed_injective (n j : Nat) (h : embed n = embed j) : n = j := by
  have hh := congrArg (fun x : Carrier => size x.val) h
  change size (tower n) = size (tower j) at hh
  rw [tower_size, tower_size] at hh
  omega
noncomputable def opposite (x y : Carrier) : Carrier := mul y x
theorem equation32280 (x y z : Carrier) :
    (opposite (opposite y (opposite (opposite y (opposite y x)) z)) y) = x :=
  equation13992 x y z
theorem infinite_model : ∃ (A : Type) (op : A → A → A) (f : Nat → A),
    (∀ x y z, (op y (op (op z (op (op x y) y)) y)) = x) ∧
    (∀ n j, f n = f j → n = j) :=
  ⟨Carrier, mul, embed, equation13992, embed_injective⟩
end submission.Austin13992

namespace submission
abbrev CM := Austin13992.Carrier
namespace CM
/-- The model contains an injective image of every natural number. -/
theorem tower_injective (n j : Nat)
    (h : Austin13992.embed n = Austin13992.embed j) : n = j :=
  Austin13992.embed_injective n j h
end CM
noncomputable instance modelMagma : Magma CM := ⟨Austin13992.opposite⟩
end submission

theorem submission : Goal := by
  refine ⟨submission.CM, submission.modelMagma, ?_, ?_⟩
  · intro x y z
    exact (submission.Austin13992.equation32280 x y z).symm
  · intro h
    have bad : 0 = 1 := submission.Austin13992.embed_injective 0 1
      (h (submission.Austin13992.embed 0) (submission.Austin13992.embed 1))
    exact Nat.noConfusion bad
example : Goal := submission
#print axioms submission
#print axioms submission.CM.tower_injective


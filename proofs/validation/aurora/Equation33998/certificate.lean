import Lean.Elab.Tactic.Omega
import JudgeProblem


set_option autoImplicit false
namespace submission.Austin12073
inductive T where
  | a : T
  | e : T
  | k : T → T
  | v : T → T
  | r : T → T → T
  | u : T → T
  | d : T → T → T
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
  | u x => size x + 1
  | d x y => size x + size y + 1
  | c x y z => size x + size y + size z + 1
  | m x y => 3 * size x + 2 * size y + 1
theorem size_pos (x : T) : 0 < size x := by
  cases x <;> simp only [size] <;> omega
inductive Root : T → T → Prop where
  | r1 (v0) : Root (T.m v0 v0) T.e
  | r2 (v0) : Root (T.m v0 T.e) (T.u v0)
  | r3 (v0) : Root (T.u (T.u (T.u v0))) v0
  | r4 (v0 v1) : Root (T.m (T.m v0 v1) v1) (T.u (T.u (T.d v0 v1)))
  | r5 (v0 v1) : Root (T.m v0 (T.d v0 v1)) v1
  | r6 : Root (T.u T.e) T.e
  | r7 (v0) : Root (T.d v0 T.e) v0
  | r8 (v0) : Root (T.m T.e v0) (T.u (T.u (T.d v0 v0)))
  | r9 (v0) : Root (T.d (T.d T.e v0) (T.d T.e v0)) (T.u v0)
  | r10 (v0) : Root (T.m (T.d T.e v0) (T.u v0)) (T.d T.e v0)
  | r11 (v0) : Root (T.d (T.d T.e v0) (T.u v0)) (T.u (T.d T.e v0))
  | r12 (v0 v1) : Root (T.m v0 (T.d v1 v0)) (T.u (T.u (T.d v1 (T.d v1 v0))))
  | r13 (v0) : Root (T.d v0 (T.d v0 v0)) (T.u v0)
  | r14 (v0) : Root (T.m v0 (T.u v0)) (T.d v0 v0)
  | r15 (v0) : Root (T.m (T.d v0 v0) (T.u v0)) (T.u (T.u (T.d v0 (T.u v0))))
  | r16 (v0) : Root (T.m (T.d T.e (T.u (T.u v0))) v0) (T.d T.e (T.u (T.u v0)))
  | r17 (v0) : Root (T.m (T.u (T.u v0)) v0) (T.d (T.u (T.u v0)) (T.u (T.u v0)))
  | r18 (v0) : Root (T.d (T.d T.e (T.u (T.u v0))) v0) (T.u (T.d T.e (T.u (T.u v0))))
  | r19 (v0 v1) : Root (T.m (T.u (T.u (T.d v0 v1))) v1) (T.u (T.u (T.d (T.m v0 v1) v1)))
  | r20 (v0) : Root (T.m (T.d (T.u (T.u v0)) (T.u (T.u v0))) v0) (T.u (T.u (T.d (T.u (T.u v0)) v0)))
  | r21 (v0) : Root (T.m (T.u v0) (T.u (T.d T.e v0))) (T.u (T.u (T.d (T.d T.e v0) (T.u (T.d T.e v0)))))
  | r22 (v0) : Root (T.m v0 (T.u (T.d T.e (T.u (T.u v0))))) (T.u (T.u (T.d (T.d T.e (T.u (T.u v0))) (T.u (T.d T.e (T.u (T.u v0)))))))
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
  | underU {x y} : Step x y → Step (u x) (u y)
  | leftD {x y} (z) : Step x y → Step (d x z) (d y z)
  | rightD (x) {y z} : Step y z → Step (d x y) (d x z)
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
 theorem underU {x y} (h : Steps x y) : Steps (u x) (u y) := by
  induction h with
  | refl => exact .refl _
  | cons h _ ih => exact .cons (.underU h) ih
 theorem leftD {x y} (z) (h : Steps x y) : Steps (d x z) (d y z) := by
  induction h with
  | refl => exact .refl _
  | cons h _ ih => exact .cons (.leftD z h) ih
 theorem rightD (x) {y z} (h : Steps y z) : Steps (d x y) (d x z) := by
  induction h with
  | refl => exact .refl _
  | cons h _ ih => exact .cons (.rightD x h) ih
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
 theorem underU {x y} (h : Join x y) : Join (u x) (u y) := by
  obtain ⟨w,h,k⟩ := h
  exact ⟨T.u w, h.underU, k.underU⟩
 theorem leftD {x y} (z) (h : Join x y) : Join (d x z) (d y z) := by
  obtain ⟨w,h,k⟩ := h
  exact ⟨T.d w z, h.leftD z, k.leftD z⟩
 theorem rightD (x) {y z} (h : Join y z) : Join (d x y) (d x z) := by
  obtain ⟨w,h,k⟩ := h
  exact ⟨T.d x w, h.rightD x, k.rightD x⟩
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
  | underU _ ih => simp only [size]; omega
  | leftD _ _ ih => simp only [size]; omega
  | rightD _ _ ih => simp only [size]; omega
  | firstC _ _ _ ih => simp only [size]; omega
  | secondC _ _ _ ih => simp only [size]; omega
  | thirdC _ _ _ ih => simp only [size]; omega
theorem root_cases {u v : T} (h : Root u v) :
    (∃ v0, u = (T.m v0 v0) ∧ v = T.e) ∨
    (∃ v0, u = (T.m v0 T.e) ∧ v = (T.u v0)) ∨
    (∃ v0, u = (T.u (T.u (T.u v0))) ∧ v = v0) ∨
    (∃ v0 v1, u = (T.m (T.m v0 v1) v1) ∧ v = (T.u (T.u (T.d v0 v1)))) ∨
    (∃ v0 v1, u = (T.m v0 (T.d v0 v1)) ∧ v = v1) ∨
    (u = (T.u T.e) ∧ v = T.e) ∨
    (∃ v0, u = (T.d v0 T.e) ∧ v = v0) ∨
    (∃ v0, u = (T.m T.e v0) ∧ v = (T.u (T.u (T.d v0 v0)))) ∨
    (∃ v0, u = (T.d (T.d T.e v0) (T.d T.e v0)) ∧ v = (T.u v0)) ∨
    (∃ v0, u = (T.m (T.d T.e v0) (T.u v0)) ∧ v = (T.d T.e v0)) ∨
    (∃ v0, u = (T.d (T.d T.e v0) (T.u v0)) ∧ v = (T.u (T.d T.e v0))) ∨
    (∃ v0 v1, u = (T.m v0 (T.d v1 v0)) ∧ v = (T.u (T.u (T.d v1 (T.d v1 v0))))) ∨
    (∃ v0, u = (T.d v0 (T.d v0 v0)) ∧ v = (T.u v0)) ∨
    (∃ v0, u = (T.m v0 (T.u v0)) ∧ v = (T.d v0 v0)) ∨
    (∃ v0, u = (T.m (T.d v0 v0) (T.u v0)) ∧ v = (T.u (T.u (T.d v0 (T.u v0))))) ∨
    (∃ v0, u = (T.m (T.d T.e (T.u (T.u v0))) v0) ∧ v = (T.d T.e (T.u (T.u v0)))) ∨
    (∃ v0, u = (T.m (T.u (T.u v0)) v0) ∧ v = (T.d (T.u (T.u v0)) (T.u (T.u v0)))) ∨
    (∃ v0, u = (T.d (T.d T.e (T.u (T.u v0))) v0) ∧ v = (T.u (T.d T.e (T.u (T.u v0))))) ∨
    (∃ v0 v1, u = (T.m (T.u (T.u (T.d v0 v1))) v1) ∧ v = (T.u (T.u (T.d (T.m v0 v1) v1)))) ∨
    (∃ v0, u = (T.m (T.d (T.u (T.u v0)) (T.u (T.u v0))) v0) ∧ v = (T.u (T.u (T.d (T.u (T.u v0)) v0)))) ∨
    (∃ v0, u = (T.m (T.u v0) (T.u (T.d T.e v0))) ∧ v = (T.u (T.u (T.d (T.d T.e v0) (T.u (T.d T.e v0)))))) ∨
    (∃ v0, u = (T.m v0 (T.u (T.d T.e (T.u (T.u v0))))) ∧ v = (T.u (T.u (T.d (T.d T.e (T.u (T.u v0))) (T.u (T.d T.e (T.u (T.u v0)))))))) := by
  cases h with
  | r1 => exact (Or.inl ⟨_, rfl, rfl⟩)
  | r2 => exact (Or.inr (Or.inl ⟨_, rfl, rfl⟩))
  | r3 => exact (Or.inr (Or.inr (Or.inl ⟨_, rfl, rfl⟩)))
  | r4 => exact (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, rfl, rfl⟩))))
  | r5 => exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, rfl, rfl⟩)))))
  | r6 => exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))))
  | r7 => exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl, rfl⟩)))))))
  | r8 => exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl, rfl⟩))))))))
  | r9 => exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl, rfl⟩)))))))))
  | r10 => exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl, rfl⟩))))))))))
  | r11 => exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl, rfl⟩)))))))))))
  | r12 => exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, rfl, rfl⟩))))))))))))
  | r13 => exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl, rfl⟩)))))))))))))
  | r14 => exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl, rfl⟩))))))))))))))
  | r15 => exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl, rfl⟩)))))))))))))))
  | r16 => exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl, rfl⟩))))))))))))))))
  | r17 => exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl, rfl⟩)))))))))))))))))
  | r18 => exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl, rfl⟩))))))))))))))))))
  | r19 => exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, rfl, rfl⟩)))))))))))))))))))
  | r20 => exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl, rfl⟩))))))))))))))))))))
  | r21 => exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl, rfl⟩)))))))))))))))))))))
  | r22 => exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨_, rfl, rfl⟩)))))))))))))))))))))

end submission.Austin12073

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin12073
open T
theorem peak1 (x0 : T) {u : T} (h : Step (T.m x0 x0) u) : Join T.e u := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      exact ⟨T.e, (Steps.refl _), (Steps.refl _)⟩
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      subst e1
      exact ⟨T.e, (Steps.refl _), (Steps.cons (Step.root (Root.r6 )) (Steps.refl _))⟩
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
      have e2 := e1.symm
      have cycle := congrArg size e2
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
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
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
      have e2 := e1.symm
      subst e2
      exact ⟨T.e, (Steps.refl _), (Steps.cons (Step.underU (Step.underU (Step.root (Root.r7 T.e)))) (Steps.cons (Step.underU (Step.root (Root.r6 ))) (Steps.cons (Step.root (Root.r6 )) (Steps.refl _))))⟩
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
      have cycle := congrArg size e1
      simp only [size] at cycle
      omega
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      have cycle := congrArg size e1
      simp only [size] at cycle
      omega
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
      have cycle := congrArg size e2
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
      have e2 := e1.symm
      have cycle := congrArg size e2
      simp only [size] at cycle
      omega
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
      have e2 := e1.symm
      have cycle := congrArg size e2
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
      have e2 := e1.symm
      have cycle := congrArg size e2
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
      have e2 := T.u.inj e1
      have cycle := congrArg size e2
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      have cycle := congrArg size e1
      simp only [size] at cycle
      omega
  | @left _ t0 _ h0 =>
    exact ⟨T.e, (Steps.refl _), (Steps.cons (Step.right t0 h0) (Steps.cons (Step.root (Root.r1 t0)) (Steps.refl _)))⟩
  | @right _ _ t0 h0 =>
    exact ⟨T.e, (Steps.refl _), (Steps.cons (Step.left t0 h0) (Steps.cons (Step.root (Root.r1 t0)) (Steps.refl _)))⟩
end submission.Austin12073

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

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin12073
open T
theorem peak3 (x0 : T) {u : T} (h : Step (T.u (T.u (T.u x0))) u) : Join x0 u := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩
    · rw [ho]
      cases he
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := T.u.inj he
      have e1 := T.u.inj e0
      have e2 := T.u.inj e1
      have e3 := e2.symm
      subst e3
      exact ⟨q0, (Steps.refl _), (Steps.refl _)⟩
    · rw [ho]
      cases he
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := T.u.inj he
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
    · rw [ho]
      cases he
    · rw [ho]
      cases he
    · rw [ho]
      cases he
    · rw [ho]
      cases he
    · rw [ho]
      cases he
    · rw [ho]
      cases he
    · rw [ho]
      cases he
  | @underU _ t0 h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := T.u.inj he
        have e1 := T.u.inj e0
        subst e1
        exact ⟨(T.u q0), (Steps.refl _), (Steps.refl _)⟩
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := T.u.inj he
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
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
    | @underU _ t1 h1 =>
      cases h1 with
      | root hr =>
        rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          have e0 := T.u.inj he
          subst e0
          exact ⟨(T.u (T.u q0)), (Steps.refl _), (Steps.refl _)⟩
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          have e0 := T.u.inj he
          subst e0
          exact ⟨T.e, (Steps.refl _), (Steps.cons (Step.underU (Step.root (Root.r6 ))) (Steps.cons (Step.root (Root.r6 )) (Steps.refl _)))⟩
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
      | @underU _ t2 h2 =>
        exact ⟨t2, (Steps.cons h2 (Steps.refl _)), (Steps.cons (Step.root (Root.r3 t2)) (Steps.refl _))⟩
end submission.Austin12073

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin12073
open T
theorem peak4 (x0 : T) (x1 : T) {u : T} (h : Step (T.m (T.m x0 x1) x1) u) : Join (T.u (T.u (T.d x0 x1))) u := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      have cycle := congrArg size e1
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      subst e1
      exact ⟨(T.u (T.u x0)), (Steps.cons (Step.underU (Step.underU (Step.root (Root.r7 x0)))) (Steps.refl _)), (Steps.cons (Step.underU (Step.root (Root.r2 x0))) (Steps.refl _))⟩
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := (T.m.inj e0).1
      have e3 := (T.m.inj e0).2
      have e4 := e1.symm
      subst e4
      have e5 := e2.symm
      subst e5
      exact ⟨(T.u (T.u (T.d q0 q1))), (Steps.refl _), (Steps.refl _)⟩
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
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
      cases he
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      have cycle := congrArg size e1
      simp only [size] at cycle
      omega
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
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
      have cycle := congrArg size e1
      simp only [size] at cycle
      omega
  | @left _ t0 _ h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        have e2 := e0.symm
        subst e2
        have e3 := e1.symm
        subst e3
        exact ⟨(T.u (T.u (T.d q0 q0))), (Steps.refl _), (Steps.cons (Step.root (Root.r8 q0)) (Steps.refl _))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        have e2 := e0.symm
        subst e2
        subst e1
        exact ⟨(T.u (T.u q0)), (Steps.cons (Step.underU (Step.underU (Step.root (Root.r7 q0)))) (Steps.refl _)), (Steps.cons (Step.root (Root.r2 (T.u q0))) (Steps.refl _))⟩
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst e0
        have e2 := e1.symm
        subst e2
        exact ⟨(T.u (T.u (T.d (T.m q0 q1) q1))), (Steps.refl _), (Steps.cons (Step.root (Root.r19 q0 q1)) (Steps.refl _))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        have e2 := e0.symm
        subst e2
        subst e1
        exact ⟨(T.u (T.u (T.d q0 (T.d q0 q1)))), (Steps.refl _), (Steps.cons (Step.root (Root.r12 q1 q0)) (Steps.refl _))⟩
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
        exact ⟨(T.u (T.u (T.d T.e q0))), (Steps.refl _), (Steps.cons (Step.root (Root.r19 q0 q0)) (Steps.cons (Step.underU (Step.underU (Step.leftD q0 (Step.root (Root.r1 q0))))) (Steps.refl _)))⟩
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst e0
        subst e1
        exact ⟨(T.d T.e q0), (Steps.cons (Step.underU (Step.underU (Step.root (Root.r11 q0)))) (Steps.cons (Step.root (Root.r3 (T.d T.e q0))) (Steps.refl _))), (Steps.cons (Step.root (Root.r10 q0)) (Steps.refl _))⟩
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        have e2 := e0.symm
        subst e2
        subst e1
        exact ⟨(T.u (T.u (T.d q0 (T.d q1 q0)))), (Steps.refl _), (Steps.cons (Step.root (Root.r19 q1 (T.d q1 q0))) (Steps.cons (Step.underU (Step.underU (Step.leftD (T.d q1 q0) (Step.root (Root.r5 q1 q0))))) (Steps.refl _)))⟩
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        have e2 := e0.symm
        subst e2
        subst e1
        exact ⟨(T.u (T.u (T.d q0 (T.u q0)))), (Steps.refl _), (Steps.cons (Step.root (Root.r15 q0)) (Steps.refl _))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst e0
        subst e1
        exact ⟨(T.u (T.u (T.d (T.d q0 q0) (T.u q0)))), (Steps.refl _), (Steps.cons (Step.root (Root.r19 q0 (T.u q0))) (Steps.cons (Step.underU (Step.underU (Step.leftD (T.u q0) (Step.root (Root.r14 q0))))) (Steps.refl _)))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst e0
        have e2 := e1.symm
        subst e2
        exact ⟨(T.d T.e (T.u (T.u q0))), (Steps.cons (Step.underU (Step.underU (Step.root (Root.r18 q0)))) (Steps.cons (Step.root (Root.r3 (T.d T.e (T.u (T.u q0))))) (Steps.refl _))), (Steps.cons (Step.root (Root.r16 q0)) (Steps.refl _))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst e0
        have e2 := e1.symm
        subst e2
        exact ⟨(T.u (T.u (T.d (T.u (T.u q0)) q0))), (Steps.refl _), (Steps.cons (Step.root (Root.r20 q0)) (Steps.refl _))⟩
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst e0
        have e2 := e1.symm
        subst e2
        exact ⟨(T.u (T.u (T.d (T.u (T.u (T.d q0 q1))) q1))), (Steps.refl _), (Steps.cons (Step.root (Root.r19 (T.m q0 q1) q1)) (Steps.cons (Step.underU (Step.underU (Step.leftD q1 (Step.root (Root.r4 q0 q1))))) (Steps.refl _)))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst e0
        have e2 := e1.symm
        subst e2
        exact ⟨(T.u (T.u (T.d (T.d (T.u (T.u q0)) (T.u (T.u q0))) q0))), (Steps.refl _), (Steps.cons (Step.root (Root.r19 (T.u (T.u q0)) q0)) (Steps.cons (Step.underU (Step.underU (Step.leftD q0 (Step.root (Root.r17 q0))))) (Steps.refl _)))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst e0
        subst e1
        exact ⟨(T.u (T.u (T.d (T.u q0) (T.u (T.d T.e q0))))), (Steps.refl _), (Steps.cons (Step.root (Root.r19 (T.d T.e q0) (T.u (T.d T.e q0)))) (Steps.cons (Step.underU (Step.underU (Step.leftD (T.u (T.d T.e q0)) (Step.root (Root.r14 (T.d T.e q0)))))) (Steps.cons (Step.underU (Step.underU (Step.leftD (T.u (T.d T.e q0)) (Step.root (Root.r9 q0))))) (Steps.refl _))))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        have e2 := e0.symm
        subst e2
        subst e1
        exact ⟨(T.u (T.u (T.d q0 (T.u (T.d T.e (T.u (T.u q0))))))), (Steps.refl _), (Steps.cons (Step.root (Root.r19 (T.d T.e (T.u (T.u q0))) (T.u (T.d T.e (T.u (T.u q0)))))) (Steps.cons (Step.underU (Step.underU (Step.leftD (T.u (T.d T.e (T.u (T.u q0)))) (Step.root (Root.r14 (T.d T.e (T.u (T.u q0)))))))) (Steps.cons (Step.underU (Step.underU (Step.leftD (T.u (T.d T.e (T.u (T.u q0)))) (Step.root (Root.r9 (T.u (T.u q0))))))) (Steps.cons (Step.underU (Step.underU (Step.leftD (T.u (T.d T.e (T.u (T.u q0)))) (Step.root (Root.r3 q0))))) (Steps.refl _)))))⟩
    | @left _ t1 _ h1 =>
      exact ⟨(T.u (T.u (T.d t1 x1))), (Steps.cons (Step.underU (Step.underU (Step.leftD x1 h1))) (Steps.refl _)), (Steps.cons (Step.root (Root.r4 t1 x1)) (Steps.refl _))⟩
    | @right _ _ t1 h1 =>
      exact ⟨(T.u (T.u (T.d x0 t1))), (Steps.cons (Step.underU (Step.underU (Step.rightD x0 h1))) (Steps.refl _)), (Steps.cons (Step.right (T.m x0 t1) h1) (Steps.cons (Step.root (Root.r4 x0 t1)) (Steps.refl _)))⟩
  | @right _ _ t0 h0 =>
    exact ⟨(T.u (T.u (T.d x0 t0))), (Steps.cons (Step.underU (Step.underU (Step.rightD x0 h0))) (Steps.refl _)), (Steps.cons (Step.left t0 (Step.right x0 h0)) (Steps.cons (Step.root (Root.r4 x0 t0)) (Steps.refl _)))⟩
end submission.Austin12073

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin12073
open T
theorem peak5 (x0 : T) (x1 : T) {u : T} (h : Step (T.m x0 (T.d x0 x1)) u) : Join x1 u := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      have e3 := e1.symm
      have cycle := congrArg size e3
      simp only [size] at cycle
      omega
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
      subst e0
      have e2 := e1.symm
      have cycle := congrArg size e2
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      have e3 := (T.d.inj e1).1
      have e4 := (T.d.inj e1).2
      have e5 := e4.symm
      subst e5
      exact ⟨q1, (Steps.refl _), (Steps.refl _)⟩
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
      exact ⟨x1, (Steps.refl _), (Steps.cons (Step.underU (Step.underU (Step.root (Root.r9 x1)))) (Steps.cons (Step.root (Root.r3 x1)) (Steps.refl _)))⟩
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
      have e3 := (T.d.inj e1).1
      have e4 := (T.d.inj e1).2
      have e5 := e3.symm
      subst e5
      have e6 := e4.symm
      subst e6
      exact ⟨q1, (Steps.refl _), (Steps.cons (Step.underU (Step.underU (Step.root (Root.r13 q1)))) (Steps.cons (Step.root (Root.r3 q1)) (Steps.refl _)))⟩
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
      have cycle := congrArg size e2
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
      have e2 := e1.symm
      have cycle := congrArg size e2
      simp only [size] at cycle
      omega
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
      have e2 := e1.symm
      have cycle := congrArg size e2
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
      have e2 := e1.symm
      have cycle := congrArg size e2
      simp only [size] at cycle
      omega
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
    exact ⟨x1, (Steps.refl _), (Steps.cons (Step.right t0 (Step.leftD x1 h0)) (Steps.cons (Step.root (Root.r5 t0 x1)) (Steps.refl _)))⟩
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
        have e0 := (T.d.inj he).1
        have e1 := (T.d.inj he).2
        have e2 := e0.symm
        subst e2
        subst e1
        exact ⟨T.e, (Steps.refl _), (Steps.cons (Step.root (Root.r1 q0)) (Steps.refl _))⟩
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.d.inj he).1
        have e1 := (T.d.inj he).2
        subst e0
        subst e1
        exact ⟨(T.d T.e q0), (Steps.refl _), (Steps.cons (Step.root (Root.r10 q0)) (Steps.refl _))⟩
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.d.inj he).1
        have e1 := (T.d.inj he).2
        subst e0
        subst e1
        exact ⟨(T.u q0), (Steps.refl _), (Steps.cons (Step.root (Root.r14 (T.d T.e q0))) (Steps.cons (Step.root (Root.r9 q0)) (Steps.refl _)))⟩
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.d.inj he).1
        have e1 := (T.d.inj he).2
        have e2 := e0.symm
        subst e2
        subst e1
        exact ⟨(T.d q0 q0), (Steps.refl _), (Steps.cons (Step.root (Root.r14 q0)) (Steps.refl _))⟩
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
        exact ⟨q0, (Steps.refl _), (Steps.cons (Step.root (Root.r14 (T.d T.e (T.u (T.u q0))))) (Steps.cons (Step.root (Root.r9 (T.u (T.u q0)))) (Steps.cons (Step.root (Root.r3 q0)) (Steps.refl _))))⟩
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
    | @leftD _ t1 _ h1 =>
      exact ⟨x1, (Steps.refl _), (Steps.cons (Step.left (T.d t1 x1) h1) (Steps.cons (Step.root (Root.r5 t1 x1)) (Steps.refl _)))⟩
    | @rightD _ _ t1 h1 =>
      exact ⟨t1, (Steps.cons h1 (Steps.refl _)), (Steps.cons (Step.root (Root.r5 x0 t1)) (Steps.refl _))⟩
end submission.Austin12073

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin12073
open T
theorem peak6  {u : T} (h : Step (T.u T.e) u) : Join T.e u := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩
    · rw [ho]
      cases he
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := T.u.inj he
      cases e0
    · rw [ho]
      cases he
    · rw [ho]
      cases he
    · rw [ho]
      exact ⟨T.e, (Steps.refl _), (Steps.refl _)⟩
    · rw [ho]
      cases he
    · rw [ho]
      cases he
    · rw [ho]
      cases he
    · rw [ho]
      cases he
    · rw [ho]
      cases he
    · rw [ho]
      cases he
    · rw [ho]
      cases he
    · rw [ho]
      cases he
    · rw [ho]
      cases he
    · rw [ho]
      cases he
    · rw [ho]
      cases he
    · rw [ho]
      cases he
    · rw [ho]
      cases he
    · rw [ho]
      cases he
    · rw [ho]
      cases he
    · rw [ho]
      cases he
  | @underU _ t0 h0 =>
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

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin12073
open T
theorem peak9 (x0 : T) {u : T} (h : Step (T.d (T.d T.e x0) (T.d T.e x0)) u) : Join (T.u x0) u := by
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
      have e2 := (T.d.inj e0).1
      have e3 := (T.d.inj e0).2
      have e4 := (T.d.inj e1).1
      have e5 := (T.d.inj e1).2
      have e6 := e3.symm
      subst e6
      exact ⟨(T.u q0), (Steps.refl _), (Steps.refl _)⟩
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.d.inj he).1
      have e1 := (T.d.inj he).2
      have e2 := (T.d.inj e0).1
      have e3 := (T.d.inj e0).2
      cases e1
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.d.inj he).1
      have e1 := (T.d.inj he).2
      have e2 := e0.symm
      subst e2
      have e3 := (T.d.inj e1).1
      have e4 := (T.d.inj e1).2
      cases e3
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
      have e2 := (T.d.inj e0).1
      have e3 := (T.d.inj e0).2
      have e4 := e1.symm
      subst e4
      have cycle := congrArg size e3
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
        exact ⟨T.e, (Steps.cons (Step.root (Root.r6 )) (Steps.refl _)), (Steps.cons (Step.root (Root.r13 T.e)) (Steps.cons (Step.root (Root.r6 )) (Steps.refl _)))⟩
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.d.inj he).1
        have e1 := (T.d.inj he).2
        cases e0
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.d.inj he).1
        have e1 := (T.d.inj he).2
        cases e0
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.d.inj he).1
        have e1 := (T.d.inj he).2
        have e2 := e0.symm
        subst e2
        subst e1
        exact ⟨T.e, (Steps.cons (Step.underU (Step.root (Root.r7 T.e))) (Steps.cons (Step.root (Root.r6 )) (Steps.refl _))), (Steps.cons (Step.leftD (T.d T.e (T.d T.e T.e)) (Step.root (Root.r6 ))) (Steps.cons (Step.rightD T.e (Step.root (Root.r13 T.e))) (Steps.cons (Step.rightD T.e (Step.root (Root.r6 ))) (Steps.cons (Step.root (Root.r7 T.e)) (Steps.refl _)))))⟩
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
        cases e0
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
    | @leftD _ t1 _ h1 =>
      cases h1 with
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
    | @rightD _ _ t1 h1 =>
      exact ⟨(T.u t1), (Steps.cons (Step.underU h1) (Steps.refl _)), (Steps.cons (Step.rightD (T.d T.e t1) (Step.rightD T.e h1)) (Steps.cons (Step.root (Root.r9 t1)) (Steps.refl _)))⟩
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
        exact ⟨T.e, (Steps.cons (Step.root (Root.r6 )) (Steps.refl _)), (Steps.cons (Step.root (Root.r7 (T.d T.e T.e))) (Steps.cons (Step.root (Root.r7 T.e)) (Steps.refl _)))⟩
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.d.inj he).1
        have e1 := (T.d.inj he).2
        cases e0
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.d.inj he).1
        have e1 := (T.d.inj he).2
        cases e0
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.d.inj he).1
        have e1 := (T.d.inj he).2
        have e2 := e0.symm
        subst e2
        subst e1
        exact ⟨T.e, (Steps.cons (Step.underU (Step.root (Root.r7 T.e))) (Steps.cons (Step.root (Root.r6 )) (Steps.refl _))), (Steps.cons (Step.leftD (T.u T.e) (Step.root (Root.r13 T.e))) (Steps.cons (Step.leftD (T.u T.e) (Step.root (Root.r6 ))) (Steps.cons (Step.rightD T.e (Step.root (Root.r6 ))) (Steps.cons (Step.root (Root.r7 T.e)) (Steps.refl _)))))⟩
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
        cases e0
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
    | @leftD _ t1 _ h1 =>
      cases h1 with
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
    | @rightD _ _ t1 h1 =>
      exact ⟨(T.u t1), (Steps.cons (Step.underU h1) (Steps.refl _)), (Steps.cons (Step.leftD (T.d T.e t1) (Step.rightD T.e h1)) (Steps.cons (Step.root (Root.r9 t1)) (Steps.refl _)))⟩
end submission.Austin12073

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin12073
open T
theorem peak10 (x0 : T) {u : T} (h : Step (T.m (T.d T.e x0) (T.u x0)) u) : Join (T.d T.e x0) u := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      cases e1
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
      cases e0
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
      cases e0
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := (T.d.inj e0).1
      have e3 := (T.d.inj e0).2
      have e4 := T.u.inj e1
      have e5 := e3.symm
      subst e5
      exact ⟨(T.d T.e q0), (Steps.refl _), (Steps.refl _)⟩
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
      have e3 := T.u.inj e1
      have cycle := congrArg size e3
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := (T.d.inj e0).1
      have e3 := (T.d.inj e0).2
      have e4 := T.u.inj e1
      have e5 := e2.symm
      subst e5
      subst e3
      exact ⟨T.e, (Steps.cons (Step.root (Root.r7 T.e)) (Steps.refl _)), (Steps.cons (Step.underU (Step.underU (Step.rightD T.e (Step.root (Root.r6 ))))) (Steps.cons (Step.underU (Step.underU (Step.root (Root.r7 T.e)))) (Steps.cons (Step.underU (Step.root (Root.r6 ))) (Steps.cons (Step.root (Root.r6 )) (Steps.refl _)))))⟩
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := (T.d.inj e0).1
      have e3 := (T.d.inj e0).2
      have e4 := e1.symm
      subst e4
      have cycle := congrArg size e3
      simp only [size] at cycle
      omega
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
      have e2 := (T.d.inj e0).1
      have e3 := (T.d.inj e0).2
      have e4 := e1.symm
      subst e4
      cases e2
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      cases e0
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      have e3 := T.u.inj e1
      have cycle := congrArg size e3
      simp only [size] at cycle
      omega
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
        have e0 := (T.d.inj he).1
        have e1 := (T.d.inj he).2
        have e2 := e0.symm
        subst e2
        subst e1
        exact ⟨T.e, (Steps.cons (Step.root (Root.r7 T.e)) (Steps.refl _)), (Steps.cons (Step.root (Root.r8 (T.u T.e))) (Steps.cons (Step.underU (Step.underU (Step.leftD (T.u T.e) (Step.root (Root.r6 ))))) (Steps.cons (Step.underU (Step.underU (Step.rightD T.e (Step.root (Root.r6 ))))) (Steps.cons (Step.underU (Step.underU (Step.root (Root.r7 T.e)))) (Steps.cons (Step.underU (Step.root (Root.r6 ))) (Steps.cons (Step.root (Root.r6 )) (Steps.refl _)))))))⟩
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.d.inj he).1
        have e1 := (T.d.inj he).2
        cases e0
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.d.inj he).1
        have e1 := (T.d.inj he).2
        cases e0
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.d.inj he).1
        have e1 := (T.d.inj he).2
        have e2 := e0.symm
        subst e2
        subst e1
        exact ⟨T.e, (Steps.cons (Step.root (Root.r13 T.e)) (Steps.cons (Step.root (Root.r6 )) (Steps.refl _))), (Steps.cons (Step.root (Root.r21 T.e)) (Steps.cons (Step.underU (Step.underU (Step.leftD (T.u (T.d T.e T.e)) (Step.root (Root.r7 T.e))))) (Steps.cons (Step.underU (Step.underU (Step.rightD T.e (Step.underU (Step.root (Root.r7 T.e)))))) (Steps.cons (Step.underU (Step.underU (Step.rightD T.e (Step.root (Root.r6 ))))) (Steps.cons (Step.underU (Step.underU (Step.root (Root.r7 T.e)))) (Steps.cons (Step.underU (Step.root (Root.r6 ))) (Steps.cons (Step.root (Root.r6 )) (Steps.refl _))))))))⟩
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
        cases e0
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
    | @leftD _ t1 _ h1 =>
      cases h1 with
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
    | @rightD _ _ t1 h1 =>
      exact ⟨(T.d T.e t1), (Steps.cons (Step.rightD T.e h1) (Steps.refl _)), (Steps.cons (Step.right (T.d T.e t1) (Step.underU h1)) (Steps.cons (Step.root (Root.r10 t1)) (Steps.refl _)))⟩
  | @right _ _ t0 h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := T.u.inj he
        subst e0
        exact ⟨(T.d T.e (T.u (T.u q0))), (Steps.refl _), (Steps.cons (Step.root (Root.r16 q0)) (Steps.refl _))⟩
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := T.u.inj he
        subst e0
        exact ⟨T.e, (Steps.cons (Step.root (Root.r7 T.e)) (Steps.refl _)), (Steps.cons (Step.root (Root.r2 (T.d T.e T.e))) (Steps.cons (Step.underU (Step.root (Root.r7 T.e))) (Steps.cons (Step.root (Root.r6 )) (Steps.refl _))))⟩
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
    | @underU _ t1 h1 =>
      exact ⟨(T.d T.e t1), (Steps.cons (Step.rightD T.e h1) (Steps.refl _)), (Steps.cons (Step.left (T.u t1) (Step.rightD T.e h1)) (Steps.cons (Step.root (Root.r10 t1)) (Steps.refl _)))⟩
end submission.Austin12073

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin12073
open T
theorem peak11 (x0 : T) {u : T} (h : Step (T.d (T.d T.e x0) (T.u x0)) u) : Join (T.u (T.d T.e x0)) u := by
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
      have e2 := (T.d.inj e0).1
      have e3 := (T.d.inj e0).2
      cases e1
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.d.inj he).1
      have e1 := (T.d.inj he).2
      have e2 := (T.d.inj e0).1
      have e3 := (T.d.inj e0).2
      have e4 := T.u.inj e1
      have e5 := e3.symm
      subst e5
      exact ⟨(T.u (T.d T.e q0)), (Steps.refl _), (Steps.refl _)⟩
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
      have e2 := (T.d.inj e0).1
      have e3 := (T.d.inj e0).2
      have e4 := e1.symm
      subst e4
      have cycle := congrArg size e3
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
        exact ⟨T.e, (Steps.cons (Step.underU (Step.root (Root.r7 T.e))) (Steps.cons (Step.root (Root.r6 )) (Steps.refl _))), (Steps.cons (Step.rightD T.e (Step.root (Root.r6 ))) (Steps.cons (Step.root (Root.r7 T.e)) (Steps.refl _)))⟩
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.d.inj he).1
        have e1 := (T.d.inj he).2
        cases e0
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.d.inj he).1
        have e1 := (T.d.inj he).2
        cases e0
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.d.inj he).1
        have e1 := (T.d.inj he).2
        have e2 := e0.symm
        subst e2
        subst e1
        exact ⟨T.e, (Steps.cons (Step.underU (Step.root (Root.r13 T.e))) (Steps.cons (Step.underU (Step.root (Root.r6 ))) (Steps.cons (Step.root (Root.r6 )) (Steps.refl _)))), (Steps.cons (Step.leftD (T.u (T.d T.e T.e)) (Step.root (Root.r6 ))) (Steps.cons (Step.rightD T.e (Step.underU (Step.root (Root.r7 T.e)))) (Steps.cons (Step.rightD T.e (Step.root (Root.r6 ))) (Steps.cons (Step.root (Root.r7 T.e)) (Steps.refl _)))))⟩
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
        cases e0
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
    | @leftD _ t1 _ h1 =>
      cases h1 with
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
    | @rightD _ _ t1 h1 =>
      exact ⟨(T.u (T.d T.e t1)), (Steps.cons (Step.underU (Step.rightD T.e h1)) (Steps.refl _)), (Steps.cons (Step.rightD (T.d T.e t1) (Step.underU h1)) (Steps.cons (Step.root (Root.r11 t1)) (Steps.refl _)))⟩
  | @rightD _ _ t0 h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := T.u.inj he
        subst e0
        exact ⟨(T.u (T.d T.e (T.u (T.u q0)))), (Steps.refl _), (Steps.cons (Step.root (Root.r18 q0)) (Steps.refl _))⟩
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := T.u.inj he
        subst e0
        exact ⟨T.e, (Steps.cons (Step.underU (Step.root (Root.r7 T.e))) (Steps.cons (Step.root (Root.r6 )) (Steps.refl _))), (Steps.cons (Step.root (Root.r7 (T.d T.e T.e))) (Steps.cons (Step.root (Root.r7 T.e)) (Steps.refl _)))⟩
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
    | @underU _ t1 h1 =>
      exact ⟨(T.u (T.d T.e t1)), (Steps.cons (Step.underU (Step.rightD T.e h1)) (Steps.refl _)), (Steps.cons (Step.leftD (T.u t1) (Step.rightD T.e h1)) (Steps.cons (Step.root (Root.r11 t1)) (Steps.refl _)))⟩
end submission.Austin12073

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin12073
open T
theorem peak12 (x0 : T) (x1 : T) {u : T} (h : Step (T.m x0 (T.d x1 x0)) u) : Join (T.u (T.u (T.d x1 (T.d x1 x0)))) u := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      have e3 := e1.symm
      have cycle := congrArg size e3
      simp only [size] at cycle
      omega
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
      subst e0
      have e2 := e1.symm
      have cycle := congrArg size e2
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      have e3 := (T.d.inj e1).1
      have e4 := (T.d.inj e1).2
      have e5 := e3.symm
      subst e5
      have e6 := e4.symm
      subst e6
      exact ⟨q1, (Steps.cons (Step.underU (Step.underU (Step.root (Root.r13 q1)))) (Steps.cons (Step.root (Root.r3 q1)) (Steps.refl _))), (Steps.refl _)⟩
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
      exact ⟨(T.u (T.u (T.d x1 x1))), (Steps.cons (Step.underU (Step.underU (Step.rightD x1 (Step.root (Root.r7 x1))))) (Steps.refl _)), (Steps.cons (Step.underU (Step.underU (Step.leftD (T.d x1 T.e) (Step.root (Root.r7 x1))))) (Steps.cons (Step.underU (Step.underU (Step.rightD x1 (Step.root (Root.r7 x1))))) (Steps.refl _)))⟩
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
      have e3 := (T.d.inj e1).1
      have e4 := (T.d.inj e1).2
      have e5 := e3.symm
      subst e5
      exact ⟨(T.u (T.u (T.d q1 (T.d q1 q0)))), (Steps.refl _), (Steps.refl _)⟩
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
      have cycle := congrArg size e2
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
      have e2 := e1.symm
      have cycle := congrArg size e2
      simp only [size] at cycle
      omega
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
      have e2 := e1.symm
      have cycle := congrArg size e2
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
      have e2 := e1.symm
      have cycle := congrArg size e2
      simp only [size] at cycle
      omega
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
    exact ⟨(T.u (T.u (T.d x1 (T.d x1 t0)))), (Steps.cons (Step.underU (Step.underU (Step.rightD x1 (Step.rightD x1 h0)))) (Steps.refl _)), (Steps.cons (Step.right t0 (Step.rightD x1 h0)) (Steps.cons (Step.root (Root.r12 t0 x1)) (Steps.refl _)))⟩
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
        have e0 := (T.d.inj he).1
        have e1 := (T.d.inj he).2
        have e2 := e0.symm
        subst e2
        subst e1
        exact ⟨(T.u (T.u (T.d q0 q0))), (Steps.cons (Step.underU (Step.underU (Step.rightD q0 (Step.root (Root.r7 q0))))) (Steps.refl _)), (Steps.cons (Step.root (Root.r8 q0)) (Steps.refl _))⟩
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.d.inj he).1
        have e1 := (T.d.inj he).2
        subst e0
        subst e1
        exact ⟨(T.d T.e q0), (Steps.cons (Step.underU (Step.underU (Step.root (Root.r13 (T.d T.e q0))))) (Steps.cons (Step.root (Root.r3 (T.d T.e q0))) (Steps.refl _))), (Steps.cons (Step.root (Root.r10 q0)) (Steps.refl _))⟩
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.d.inj he).1
        have e1 := (T.d.inj he).2
        subst e0
        subst e1
        exact ⟨(T.u (T.u (T.d (T.d T.e q0) (T.u (T.d T.e q0))))), (Steps.cons (Step.underU (Step.underU (Step.rightD (T.d T.e q0) (Step.root (Root.r11 q0))))) (Steps.refl _)), (Steps.cons (Step.root (Root.r21 q0)) (Steps.refl _))⟩
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.d.inj he).1
        have e1 := (T.d.inj he).2
        have e2 := e0.symm
        subst e2
        subst e1
        exact ⟨(T.u (T.u (T.d q0 (T.u q0)))), (Steps.cons (Step.underU (Step.underU (Step.rightD q0 (Step.root (Root.r13 q0))))) (Steps.refl _)), (Steps.cons (Step.root (Root.r15 q0)) (Steps.refl _))⟩
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
        exact ⟨(T.u (T.u (T.d (T.d T.e (T.u (T.u q0))) (T.u (T.d T.e (T.u (T.u q0))))))), (Steps.cons (Step.underU (Step.underU (Step.rightD (T.d T.e (T.u (T.u q0))) (Step.root (Root.r18 q0))))) (Steps.refl _)), (Steps.cons (Step.root (Root.r22 q0)) (Steps.refl _))⟩
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
    | @leftD _ t1 _ h1 =>
      exact ⟨(T.u (T.u (T.d t1 (T.d t1 x0)))), (Steps.cons (Step.underU (Step.underU (Step.leftD (T.d x1 x0) h1))) (Steps.cons (Step.underU (Step.underU (Step.rightD t1 (Step.leftD x0 h1)))) (Steps.refl _))), (Steps.cons (Step.root (Root.r12 x0 t1)) (Steps.refl _))⟩
    | @rightD _ _ t1 h1 =>
      exact ⟨(T.u (T.u (T.d x1 (T.d x1 t1)))), (Steps.cons (Step.underU (Step.underU (Step.rightD x1 (Step.rightD x1 h1)))) (Steps.refl _)), (Steps.cons (Step.left (T.d x1 t1) h1) (Steps.cons (Step.root (Root.r12 t1 x1)) (Steps.refl _)))⟩
end submission.Austin12073

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

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin12073
open T
theorem peak14 (x0 : T) {u : T} (h : Step (T.m x0 (T.u x0)) u) : Join (T.d x0 x0) u := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      have e3 := e1.symm
      have cycle := congrArg size e3
      simp only [size] at cycle
      omega
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
      subst e0
      have e2 := e1.symm
      have cycle := congrArg size e2
      simp only [size] at cycle
      omega
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
      exact ⟨T.e, (Steps.cons (Step.root (Root.r7 T.e)) (Steps.refl _)), (Steps.cons (Step.underU (Step.underU (Step.leftD (T.u T.e) (Step.root (Root.r6 ))))) (Steps.cons (Step.underU (Step.underU (Step.rightD T.e (Step.root (Root.r6 ))))) (Steps.cons (Step.underU (Step.underU (Step.root (Root.r7 T.e)))) (Steps.cons (Step.underU (Step.root (Root.r6 ))) (Steps.cons (Step.root (Root.r6 )) (Steps.refl _))))))⟩
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
      have e2 := T.u.inj e1
      have e3 := e2.symm
      have cycle := congrArg size e3
      simp only [size] at cycle
      omega
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
      exact ⟨(T.d q0 q0), (Steps.refl _), (Steps.refl _)⟩
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
      have e2 := T.u.inj e1
      have e3 := e2.symm
      have cycle := congrArg size e3
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
      have e2 := e1.symm
      have cycle := congrArg size e2
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
      have e2 := e1.symm
      have cycle := congrArg size e2
      simp only [size] at cycle
      omega
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
      have e2 := e1.symm
      have cycle := congrArg size e2
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
      have e2 := e1.symm
      have cycle := congrArg size e2
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
      have e2 := T.u.inj e1
      cases e2
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      have e3 := T.u.inj e1
      have cycle := congrArg size e3
      simp only [size] at cycle
      omega
  | @left _ t0 _ h0 =>
    exact ⟨(T.d t0 t0), (Steps.cons (Step.leftD x0 h0) (Steps.cons (Step.rightD t0 h0) (Steps.refl _))), (Steps.cons (Step.right t0 (Step.underU h0)) (Steps.cons (Step.root (Root.r14 t0)) (Steps.refl _)))⟩
  | @right _ _ t0 h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := T.u.inj he
        subst e0
        exact ⟨(T.d (T.u (T.u q0)) (T.u (T.u q0))), (Steps.refl _), (Steps.cons (Step.root (Root.r17 q0)) (Steps.refl _))⟩
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := T.u.inj he
        subst e0
        exact ⟨T.e, (Steps.cons (Step.root (Root.r7 T.e)) (Steps.refl _)), (Steps.cons (Step.root (Root.r1 T.e)) (Steps.refl _))⟩
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
    | @underU _ t1 h1 =>
      exact ⟨(T.d t1 t1), (Steps.cons (Step.leftD x0 h1) (Steps.cons (Step.rightD t1 h1) (Steps.refl _))), (Steps.cons (Step.left (T.u t1) h1) (Steps.cons (Step.root (Root.r14 t1)) (Steps.refl _)))⟩
end submission.Austin12073

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin12073
open T
theorem peak15 (x0 : T) {u : T} (h : Step (T.m (T.d x0 x0) (T.u x0)) u) : Join (T.u (T.u (T.d x0 (T.u x0)))) u := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      cases e1
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
      cases e0
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
      cases e0
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := (T.d.inj e0).1
      have e3 := (T.d.inj e0).2
      have e4 := T.u.inj e1
      subst e2
      have e5 := e3.symm
      subst e5
      exact ⟨T.e, (Steps.cons (Step.underU (Step.underU (Step.rightD T.e (Step.root (Root.r6 ))))) (Steps.cons (Step.underU (Step.underU (Step.root (Root.r7 T.e)))) (Steps.cons (Step.underU (Step.root (Root.r6 ))) (Steps.cons (Step.root (Root.r6 )) (Steps.refl _))))), (Steps.cons (Step.root (Root.r7 T.e)) (Steps.refl _))⟩
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
      have e3 := T.u.inj e1
      have cycle := congrArg size e3
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := (T.d.inj e0).1
      have e3 := (T.d.inj e0).2
      have e4 := T.u.inj e1
      have e5 := e2.symm
      subst e5
      exact ⟨(T.u (T.u (T.d q0 (T.u q0)))), (Steps.refl _), (Steps.refl _)⟩
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := (T.d.inj e0).1
      have e3 := (T.d.inj e0).2
      have e4 := e1.symm
      subst e4
      subst e2
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
      have e2 := (T.d.inj e0).1
      have e3 := (T.d.inj e0).2
      have e4 := e1.symm
      subst e4
      have cycle := congrArg size e2
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
      subst e2
      have e3 := T.u.inj e1
      have cycle := congrArg size e3
      simp only [size] at cycle
      omega
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
        have e0 := (T.d.inj he).1
        have e1 := (T.d.inj he).2
        have e2 := e0.symm
        subst e2
        subst e1
        exact ⟨T.e, (Steps.cons (Step.underU (Step.underU (Step.rightD T.e (Step.root (Root.r6 ))))) (Steps.cons (Step.underU (Step.underU (Step.root (Root.r7 T.e)))) (Steps.cons (Step.underU (Step.root (Root.r6 ))) (Steps.cons (Step.root (Root.r6 )) (Steps.refl _))))), (Steps.cons (Step.root (Root.r8 (T.u T.e))) (Steps.cons (Step.underU (Step.underU (Step.leftD (T.u T.e) (Step.root (Root.r6 ))))) (Steps.cons (Step.underU (Step.underU (Step.rightD T.e (Step.root (Root.r6 ))))) (Steps.cons (Step.underU (Step.underU (Step.root (Root.r7 T.e)))) (Steps.cons (Step.underU (Step.root (Root.r6 ))) (Steps.cons (Step.root (Root.r6 )) (Steps.refl _)))))))⟩
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.d.inj he).1
        have e1 := (T.d.inj he).2
        subst e0
        exact ⟨(T.u (T.u (T.d (T.d T.e q0) (T.u (T.d T.e q0))))), (Steps.refl _), (Steps.cons (Step.root (Root.r21 q0)) (Steps.refl _))⟩
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
      exact ⟨(T.u (T.u (T.d t1 (T.u t1)))), (Steps.cons (Step.underU (Step.underU (Step.leftD (T.u x0) h1))) (Steps.cons (Step.underU (Step.underU (Step.rightD t1 (Step.underU h1)))) (Steps.refl _))), (Steps.cons (Step.left (T.u x0) (Step.rightD t1 h1)) (Steps.cons (Step.right (T.d t1 t1) (Step.underU h1)) (Steps.cons (Step.root (Root.r15 t1)) (Steps.refl _))))⟩
    | @rightD _ _ t1 h1 =>
      exact ⟨(T.u (T.u (T.d t1 (T.u t1)))), (Steps.cons (Step.underU (Step.underU (Step.leftD (T.u x0) h1))) (Steps.cons (Step.underU (Step.underU (Step.rightD t1 (Step.underU h1)))) (Steps.refl _))), (Steps.cons (Step.left (T.u x0) (Step.leftD t1 h1)) (Steps.cons (Step.right (T.d t1 t1) (Step.underU h1)) (Steps.cons (Step.root (Root.r15 t1)) (Steps.refl _))))⟩
  | @right _ _ t0 h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := T.u.inj he
        subst e0
        exact ⟨(T.u (T.u (T.d (T.u (T.u q0)) q0))), (Steps.cons (Step.underU (Step.underU (Step.rightD (T.u (T.u q0)) (Step.root (Root.r3 q0))))) (Steps.refl _)), (Steps.cons (Step.root (Root.r20 q0)) (Steps.refl _))⟩
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := T.u.inj he
        subst e0
        exact ⟨T.e, (Steps.cons (Step.underU (Step.underU (Step.rightD T.e (Step.root (Root.r6 ))))) (Steps.cons (Step.underU (Step.underU (Step.root (Root.r7 T.e)))) (Steps.cons (Step.underU (Step.root (Root.r6 ))) (Steps.cons (Step.root (Root.r6 )) (Steps.refl _))))), (Steps.cons (Step.root (Root.r2 (T.d T.e T.e))) (Steps.cons (Step.underU (Step.root (Root.r7 T.e))) (Steps.cons (Step.root (Root.r6 )) (Steps.refl _))))⟩
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
    | @underU _ t1 h1 =>
      exact ⟨(T.u (T.u (T.d t1 (T.u t1)))), (Steps.cons (Step.underU (Step.underU (Step.leftD (T.u x0) h1))) (Steps.cons (Step.underU (Step.underU (Step.rightD t1 (Step.underU h1)))) (Steps.refl _))), (Steps.cons (Step.left (T.u t1) (Step.leftD x0 h1)) (Steps.cons (Step.left (T.u t1) (Step.rightD t1 h1)) (Steps.cons (Step.root (Root.r15 t1)) (Steps.refl _))))⟩
end submission.Austin12073

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin12073
open T
theorem peak16 (x0 : T) {u : T} (h : Step (T.m (T.d T.e (T.u (T.u x0))) x0) u) : Join (T.d T.e (T.u (T.u x0))) u := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      have cycle := congrArg size e1
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      subst e1
      exact ⟨T.e, (Steps.cons (Step.rightD T.e (Step.underU (Step.root (Root.r6 )))) (Steps.cons (Step.rightD T.e (Step.root (Root.r6 ))) (Steps.cons (Step.root (Root.r7 T.e)) (Steps.refl _)))), (Steps.cons (Step.underU (Step.rightD T.e (Step.underU (Step.root (Root.r6 ))))) (Steps.cons (Step.underU (Step.rightD T.e (Step.root (Root.r6 )))) (Steps.cons (Step.underU (Step.root (Root.r7 T.e))) (Steps.cons (Step.root (Root.r6 )) (Steps.refl _)))))⟩
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
      have cycle := congrArg size e1
      simp only [size] at cycle
      omega
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
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := (T.d.inj e0).1
      have e3 := (T.d.inj e0).2
      subst e1
      have e4 := e3.symm
      have cycle := congrArg size e4
      simp only [size] at cycle
      omega
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      have cycle := congrArg size e1
      simp only [size] at cycle
      omega
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      have cycle := congrArg size e1
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := (T.d.inj e0).1
      have e3 := (T.d.inj e0).2
      subst e1
      have e4 := e2.symm
      subst e4
      cases e3
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := (T.d.inj e0).1
      have e3 := (T.d.inj e0).2
      have e4 := e1.symm
      subst e4
      exact ⟨(T.d T.e (T.u (T.u q0))), (Steps.refl _), (Steps.refl _)⟩
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
      have e2 := (T.d.inj e0).1
      have e3 := (T.d.inj e0).2
      have e4 := e1.symm
      subst e4
      cases e2
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      cases e0
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      have cycle := congrArg size e1
      simp only [size] at cycle
      omega
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
        cases e0
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.d.inj he).1
        have e1 := (T.d.inj he).2
        cases e0
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
        cases e0
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
    | @leftD _ t1 _ h1 =>
      cases h1 with
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
    | @rightD _ _ t1 h1 =>
      cases h1 with
      | root hr =>
        rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          have e0 := T.u.inj he
          have e1 := T.u.inj e0
          subst e1
          exact ⟨(T.d T.e q0), (Steps.cons (Step.rightD T.e (Step.root (Root.r3 q0))) (Steps.refl _)), (Steps.cons (Step.root (Root.r10 q0)) (Steps.refl _))⟩
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          have e0 := T.u.inj he
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
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
      | @underU _ t2 h2 =>
        cases h2 with
        | root hr =>
          rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            have e0 := T.u.inj he
            subst e0
            exact ⟨(T.d T.e (T.u q0)), (Steps.cons (Step.rightD T.e (Step.root (Root.r3 (T.u q0)))) (Steps.refl _)), (Steps.cons (Step.root (Root.r10 (T.u q0))) (Steps.refl _))⟩
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            have e0 := T.u.inj he
            subst e0
            exact ⟨T.e, (Steps.cons (Step.rightD T.e (Step.underU (Step.root (Root.r6 )))) (Steps.cons (Step.rightD T.e (Step.root (Root.r6 ))) (Steps.cons (Step.root (Root.r7 T.e)) (Steps.refl _)))), (Steps.cons (Step.root (Root.r2 (T.d T.e (T.u T.e)))) (Steps.cons (Step.underU (Step.rightD T.e (Step.root (Root.r6 )))) (Steps.cons (Step.underU (Step.root (Root.r7 T.e))) (Steps.cons (Step.root (Root.r6 )) (Steps.refl _)))))⟩
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
        | @underU _ t3 h3 =>
          exact ⟨(T.d T.e (T.u (T.u t3))), (Steps.cons (Step.rightD T.e (Step.underU (Step.underU h3))) (Steps.refl _)), (Steps.cons (Step.right (T.d T.e (T.u (T.u t3))) h3) (Steps.cons (Step.root (Root.r16 t3)) (Steps.refl _)))⟩
  | @right _ _ t0 h0 =>
    exact ⟨(T.d T.e (T.u (T.u t0))), (Steps.cons (Step.rightD T.e (Step.underU (Step.underU h0))) (Steps.refl _)), (Steps.cons (Step.left t0 (Step.rightD T.e (Step.underU (Step.underU h0)))) (Steps.cons (Step.root (Root.r16 t0)) (Steps.refl _)))⟩
end submission.Austin12073

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin12073
open T
theorem peak17 (x0 : T) {u : T} (h : Step (T.m (T.u (T.u x0)) x0) u) : Join (T.d (T.u (T.u x0)) (T.u (T.u x0))) u := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      have cycle := congrArg size e1
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      subst e1
      exact ⟨T.e, (Steps.cons (Step.leftD (T.u (T.u T.e)) (Step.underU (Step.root (Root.r6 )))) (Steps.cons (Step.leftD (T.u (T.u T.e)) (Step.root (Root.r6 ))) (Steps.cons (Step.rightD T.e (Step.underU (Step.root (Root.r6 )))) (Steps.cons (Step.rightD T.e (Step.root (Root.r6 ))) (Steps.cons (Step.root (Root.r7 T.e)) (Steps.refl _)))))), (Steps.cons (Step.root (Root.r3 T.e)) (Steps.refl _))⟩
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
      have cycle := congrArg size e1
      simp only [size] at cycle
      omega
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
      have cycle := congrArg size e1
      simp only [size] at cycle
      omega
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
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
      have e2 := T.u.inj e0
      have e3 := e1.symm
      subst e3
      exact ⟨(T.d (T.u (T.u q0)) (T.u (T.u q0))), (Steps.refl _), (Steps.refl _)⟩
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := T.u.inj e0
      have e3 := e1.symm
      subst e3
      have e4 := T.u.inj e2
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
      have e2 := T.u.inj e0
      subst e1
      have e3 := e2.symm
      have cycle := congrArg size e3
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      have cycle := congrArg size e1
      simp only [size] at cycle
      omega
  | @left _ t0 _ h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := T.u.inj he
        have e1 := T.u.inj e0
        subst e1
        exact ⟨(T.d q0 q0), (Steps.cons (Step.leftD (T.u (T.u (T.u q0))) (Step.root (Root.r3 q0))) (Steps.cons (Step.rightD q0 (Step.root (Root.r3 q0))) (Steps.refl _))), (Steps.cons (Step.root (Root.r14 q0)) (Steps.refl _))⟩
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := T.u.inj he
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
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
    | @underU _ t1 h1 =>
      cases h1 with
      | root hr =>
        rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          have e0 := T.u.inj he
          subst e0
          exact ⟨(T.d (T.u q0) (T.u q0)), (Steps.cons (Step.leftD (T.u (T.u (T.u (T.u q0)))) (Step.root (Root.r3 (T.u q0)))) (Steps.cons (Step.rightD (T.u q0) (Step.root (Root.r3 (T.u q0)))) (Steps.refl _))), (Steps.cons (Step.root (Root.r14 (T.u q0))) (Steps.refl _))⟩
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          have e0 := T.u.inj he
          subst e0
          exact ⟨T.e, (Steps.cons (Step.leftD (T.u (T.u T.e)) (Step.underU (Step.root (Root.r6 )))) (Steps.cons (Step.leftD (T.u (T.u T.e)) (Step.root (Root.r6 ))) (Steps.cons (Step.rightD T.e (Step.underU (Step.root (Root.r6 )))) (Steps.cons (Step.rightD T.e (Step.root (Root.r6 ))) (Steps.cons (Step.root (Root.r7 T.e)) (Steps.refl _)))))), (Steps.cons (Step.root (Root.r2 (T.u T.e))) (Steps.cons (Step.underU (Step.root (Root.r6 ))) (Steps.cons (Step.root (Root.r6 )) (Steps.refl _))))⟩
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
      | @underU _ t2 h2 =>
        exact ⟨(T.d (T.u (T.u t2)) (T.u (T.u t2))), (Steps.cons (Step.leftD (T.u (T.u x0)) (Step.underU (Step.underU h2))) (Steps.cons (Step.rightD (T.u (T.u t2)) (Step.underU (Step.underU h2))) (Steps.refl _))), (Steps.cons (Step.right (T.u (T.u t2)) h2) (Steps.cons (Step.root (Root.r17 t2)) (Steps.refl _)))⟩
  | @right _ _ t0 h0 =>
    exact ⟨(T.d (T.u (T.u t0)) (T.u (T.u t0))), (Steps.cons (Step.leftD (T.u (T.u x0)) (Step.underU (Step.underU h0))) (Steps.cons (Step.rightD (T.u (T.u t0)) (Step.underU (Step.underU h0))) (Steps.refl _))), (Steps.cons (Step.left t0 (Step.underU (Step.underU h0))) (Steps.cons (Step.root (Root.r17 t0)) (Steps.refl _)))⟩
end submission.Austin12073

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin12073
open T
theorem peak18 (x0 : T) {u : T} (h : Step (T.d (T.d T.e (T.u (T.u x0))) x0) u) : Join (T.u (T.d T.e (T.u (T.u x0)))) u := by
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
      subst e1
      exact ⟨T.e, (Steps.cons (Step.underU (Step.rightD T.e (Step.underU (Step.root (Root.r6 ))))) (Steps.cons (Step.underU (Step.rightD T.e (Step.root (Root.r6 )))) (Steps.cons (Step.underU (Step.root (Root.r7 T.e))) (Steps.cons (Step.root (Root.r6 )) (Steps.refl _))))), (Steps.cons (Step.rightD T.e (Step.underU (Step.root (Root.r6 )))) (Steps.cons (Step.rightD T.e (Step.root (Root.r6 ))) (Steps.cons (Step.root (Root.r7 T.e)) (Steps.refl _))))⟩
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.d.inj he).1
      have e1 := (T.d.inj he).2
      have e2 := (T.d.inj e0).1
      have e3 := (T.d.inj e0).2
      subst e1
      have e4 := e3.symm
      have cycle := congrArg size e4
      simp only [size] at cycle
      omega
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.d.inj he).1
      have e1 := (T.d.inj he).2
      have e2 := (T.d.inj e0).1
      have e3 := (T.d.inj e0).2
      subst e1
      have e4 := e3.symm
      have cycle := congrArg size e4
      simp only [size] at cycle
      omega
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
      have e2 := (T.d.inj e0).1
      have e3 := (T.d.inj e0).2
      have e4 := e1.symm
      subst e4
      exact ⟨(T.u (T.d T.e (T.u (T.u q0)))), (Steps.refl _), (Steps.refl _)⟩
    · rw [ho]
      cases he
    · rw [ho]
      cases he
    · rw [ho]
      cases he
    · rw [ho]
      cases he
  | @leftD _ t0 _ h0 =>
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
        cases e1
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.d.inj he).1
        have e1 := (T.d.inj he).2
        cases e0
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.d.inj he).1
        have e1 := (T.d.inj he).2
        cases e0
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
        cases e0
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
    | @leftD _ t1 _ h1 =>
      cases h1 with
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
    | @rightD _ _ t1 h1 =>
      cases h1 with
      | root hr =>
        rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          have e0 := T.u.inj he
          have e1 := T.u.inj e0
          subst e1
          exact ⟨(T.u (T.d T.e q0)), (Steps.cons (Step.underU (Step.rightD T.e (Step.root (Root.r3 q0)))) (Steps.refl _)), (Steps.cons (Step.root (Root.r11 q0)) (Steps.refl _))⟩
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          have e0 := T.u.inj he
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
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
      | @underU _ t2 h2 =>
        cases h2 with
        | root hr =>
          rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            have e0 := T.u.inj he
            subst e0
            exact ⟨(T.u (T.d T.e (T.u q0))), (Steps.cons (Step.underU (Step.rightD T.e (Step.root (Root.r3 (T.u q0))))) (Steps.refl _)), (Steps.cons (Step.root (Root.r11 (T.u q0))) (Steps.refl _))⟩
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            have e0 := T.u.inj he
            subst e0
            exact ⟨T.e, (Steps.cons (Step.underU (Step.rightD T.e (Step.underU (Step.root (Root.r6 ))))) (Steps.cons (Step.underU (Step.rightD T.e (Step.root (Root.r6 )))) (Steps.cons (Step.underU (Step.root (Root.r7 T.e))) (Steps.cons (Step.root (Root.r6 )) (Steps.refl _))))), (Steps.cons (Step.root (Root.r7 (T.d T.e (T.u T.e)))) (Steps.cons (Step.rightD T.e (Step.root (Root.r6 ))) (Steps.cons (Step.root (Root.r7 T.e)) (Steps.refl _))))⟩
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
        | @underU _ t3 h3 =>
          exact ⟨(T.u (T.d T.e (T.u (T.u t3)))), (Steps.cons (Step.underU (Step.rightD T.e (Step.underU (Step.underU h3)))) (Steps.refl _)), (Steps.cons (Step.rightD (T.d T.e (T.u (T.u t3))) h3) (Steps.cons (Step.root (Root.r18 t3)) (Steps.refl _)))⟩
  | @rightD _ _ t0 h0 =>
    exact ⟨(T.u (T.d T.e (T.u (T.u t0)))), (Steps.cons (Step.underU (Step.rightD T.e (Step.underU (Step.underU h0)))) (Steps.refl _)), (Steps.cons (Step.leftD t0 (Step.rightD T.e (Step.underU (Step.underU h0)))) (Steps.cons (Step.root (Root.r18 t0)) (Steps.refl _)))⟩
end submission.Austin12073

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin12073
open T
theorem peak19 (x0 : T) (x1 : T) {u : T} (h : Step (T.m (T.u (T.u (T.d x0 x1))) x1) u) : Join (T.u (T.u (T.d (T.m x0 x1) x1))) u := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      have cycle := congrArg size e1
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      subst e1
      exact ⟨x0, (Steps.cons (Step.underU (Step.underU (Step.root (Root.r7 (T.m x0 T.e))))) (Steps.cons (Step.underU (Step.underU (Step.root (Root.r2 x0)))) (Steps.cons (Step.root (Root.r3 x0)) (Steps.refl _)))), (Steps.cons (Step.root (Root.r3 (T.d x0 T.e))) (Steps.cons (Step.root (Root.r7 x0)) (Steps.refl _)))⟩
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
      have cycle := congrArg size e1
      simp only [size] at cycle
      omega
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
      have cycle := congrArg size e1
      simp only [size] at cycle
      omega
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
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
      have e2 := T.u.inj e0
      have e3 := e1.symm
      subst e3
      have e4 := T.u.inj e2
      have e5 := e4.symm
      have cycle := congrArg size e5
      simp only [size] at cycle
      omega
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := T.u.inj e0
      have e3 := e1.symm
      subst e3
      have e4 := T.u.inj e2
      have e5 := (T.d.inj e4).1
      have e6 := (T.d.inj e4).2
      have e7 := e5.symm
      subst e7
      exact ⟨(T.u (T.u (T.d (T.m q0 q1) q1))), (Steps.refl _), (Steps.refl _)⟩
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      cases e0
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := T.u.inj e0
      subst e1
      have e3 := e2.symm
      have cycle := congrArg size e3
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      have cycle := congrArg size e1
      simp only [size] at cycle
      omega
  | @left _ t0 _ h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := T.u.inj he
        have e1 := T.u.inj e0
        cases e1
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := T.u.inj he
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
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
    | @underU _ t1 h1 =>
      cases h1 with
      | root hr =>
        rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          have e0 := T.u.inj he
          cases e0
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          have e0 := T.u.inj he
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
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
      | @underU _ t2 h2 =>
        cases h2 with
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
            exact ⟨q0, (Steps.cons (Step.underU (Step.underU (Step.root (Root.r7 (T.m q0 T.e))))) (Steps.cons (Step.underU (Step.underU (Step.root (Root.r2 q0)))) (Steps.cons (Step.root (Root.r3 q0)) (Steps.refl _)))), (Steps.cons (Step.root (Root.r2 (T.u (T.u q0)))) (Steps.cons (Step.root (Root.r3 q0)) (Steps.refl _)))⟩
          · rw [ho]
            cases he
          · rw [ho]
            have e0 := (T.d.inj he).1
            have e1 := (T.d.inj he).2
            subst e0
            subst e1
            exact ⟨(T.u (T.u (T.d T.e (T.d T.e q0)))), (Steps.cons (Step.underU (Step.underU (Step.leftD (T.d T.e q0) (Step.root (Root.r1 (T.d T.e q0)))))) (Steps.refl _)), (Steps.cons (Step.left (T.d T.e q0) (Step.root (Root.r3 q0))) (Steps.cons (Step.root (Root.r12 q0 T.e)) (Steps.refl _)))⟩
          · rw [ho]
            cases he
          · rw [ho]
            have e0 := (T.d.inj he).1
            have e1 := (T.d.inj he).2
            subst e0
            subst e1
            exact ⟨(T.d T.e q0), (Steps.cons (Step.underU (Step.underU (Step.leftD (T.u q0) (Step.root (Root.r10 q0))))) (Steps.cons (Step.underU (Step.underU (Step.root (Root.r11 q0)))) (Steps.cons (Step.root (Root.r3 (T.d T.e q0))) (Steps.refl _)))), (Steps.cons (Step.left (T.u q0) (Step.root (Root.r3 (T.d T.e q0)))) (Steps.cons (Step.root (Root.r10 q0)) (Steps.refl _)))⟩
          · rw [ho]
            cases he
          · rw [ho]
            have e0 := (T.d.inj he).1
            have e1 := (T.d.inj he).2
            have e2 := e0.symm
            subst e2
            subst e1
            exact ⟨q0, (Steps.cons (Step.underU (Step.underU (Step.leftD (T.d q0 q0) (Step.root (Root.r5 q0 q0))))) (Steps.cons (Step.underU (Step.underU (Step.root (Root.r13 q0)))) (Steps.cons (Step.root (Root.r3 q0)) (Steps.refl _)))), (Steps.cons (Step.left (T.d q0 q0) (Step.root (Root.r3 q0))) (Steps.cons (Step.root (Root.r5 q0 q0)) (Steps.refl _)))⟩
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
            exact ⟨(T.d T.e (T.u (T.u q0))), (Steps.cons (Step.underU (Step.underU (Step.leftD q0 (Step.root (Root.r16 q0))))) (Steps.cons (Step.underU (Step.underU (Step.root (Root.r18 q0)))) (Steps.cons (Step.root (Root.r3 (T.d T.e (T.u (T.u q0))))) (Steps.refl _)))), (Steps.cons (Step.left q0 (Step.root (Root.r3 (T.d T.e (T.u (T.u q0)))))) (Steps.cons (Step.root (Root.r16 q0)) (Steps.refl _)))⟩
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
        | @leftD _ t3 _ h3 =>
          exact ⟨(T.u (T.u (T.d (T.m t3 x1) x1))), (Steps.cons (Step.underU (Step.underU (Step.leftD x1 (Step.left x1 h3)))) (Steps.refl _)), (Steps.cons (Step.root (Root.r19 t3 x1)) (Steps.refl _))⟩
        | @rightD _ _ t3 h3 =>
          exact ⟨(T.u (T.u (T.d (T.m x0 t3) t3))), (Steps.cons (Step.underU (Step.underU (Step.leftD x1 (Step.right x0 h3)))) (Steps.cons (Step.underU (Step.underU (Step.rightD (T.m x0 t3) h3))) (Steps.refl _))), (Steps.cons (Step.right (T.u (T.u (T.d x0 t3))) h3) (Steps.cons (Step.root (Root.r19 x0 t3)) (Steps.refl _)))⟩
  | @right _ _ t0 h0 =>
    exact ⟨(T.u (T.u (T.d (T.m x0 t0) t0))), (Steps.cons (Step.underU (Step.underU (Step.leftD x1 (Step.right x0 h0)))) (Steps.cons (Step.underU (Step.underU (Step.rightD (T.m x0 t0) h0))) (Steps.refl _))), (Steps.cons (Step.left t0 (Step.underU (Step.underU (Step.rightD x0 h0)))) (Steps.cons (Step.root (Root.r19 x0 t0)) (Steps.refl _)))⟩
end submission.Austin12073

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin12073
open T
theorem peak20 (x0 : T) {u : T} (h : Step (T.m (T.d (T.u (T.u x0)) (T.u (T.u x0))) x0) u) : Join (T.u (T.u (T.d (T.u (T.u x0)) x0))) u := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      have cycle := congrArg size e1
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      subst e1
      exact ⟨T.e, (Steps.cons (Step.underU (Step.underU (Step.root (Root.r7 (T.u (T.u T.e)))))) (Steps.cons (Step.root (Root.r3 (T.u T.e))) (Steps.cons (Step.root (Root.r6 )) (Steps.refl _)))), (Steps.cons (Step.underU (Step.leftD (T.u (T.u T.e)) (Step.underU (Step.root (Root.r6 ))))) (Steps.cons (Step.underU (Step.leftD (T.u (T.u T.e)) (Step.root (Root.r6 )))) (Steps.cons (Step.underU (Step.rightD T.e (Step.underU (Step.root (Root.r6 ))))) (Steps.cons (Step.underU (Step.rightD T.e (Step.root (Root.r6 )))) (Steps.cons (Step.underU (Step.root (Root.r7 T.e))) (Steps.cons (Step.root (Root.r6 )) (Steps.refl _)))))))⟩
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
      have cycle := congrArg size e1
      simp only [size] at cycle
      omega
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
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := (T.d.inj e0).1
      have e3 := (T.d.inj e0).2
      subst e1
      cases e2
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      have cycle := congrArg size e1
      simp only [size] at cycle
      omega
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      have cycle := congrArg size e1
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := (T.d.inj e0).1
      have e3 := (T.d.inj e0).2
      subst e1
      have e4 := e2.symm
      have cycle := congrArg size e4
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := (T.d.inj e0).1
      have e3 := (T.d.inj e0).2
      have e4 := e1.symm
      subst e4
      cases e2
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
      have e2 := (T.d.inj e0).1
      have e3 := (T.d.inj e0).2
      have e4 := e1.symm
      subst e4
      exact ⟨(T.u (T.u (T.d (T.u (T.u q0)) q0))), (Steps.refl _), (Steps.refl _)⟩
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      cases e0
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      have cycle := congrArg size e1
      simp only [size] at cycle
      omega
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
        cases e0
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.d.inj he).1
        have e1 := (T.d.inj he).2
        cases e0
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
        cases e0
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
    | @leftD _ t1 _ h1 =>
      cases h1 with
      | root hr =>
        rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          have e0 := T.u.inj he
          have e1 := T.u.inj e0
          subst e1
          exact ⟨(T.u (T.u (T.d q0 (T.u q0)))), (Steps.cons (Step.underU (Step.underU (Step.leftD (T.u q0) (Step.root (Root.r3 q0))))) (Steps.refl _)), (Steps.cons (Step.left (T.u q0) (Step.rightD q0 (Step.root (Root.r3 q0)))) (Steps.cons (Step.root (Root.r15 q0)) (Steps.refl _)))⟩
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          have e0 := T.u.inj he
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
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
      | @underU _ t2 h2 =>
        cases h2 with
        | root hr =>
          rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            have e0 := T.u.inj he
            subst e0
            exact ⟨(T.u (T.u (T.d (T.u q0) (T.u (T.u q0))))), (Steps.cons (Step.underU (Step.underU (Step.leftD (T.u (T.u q0)) (Step.root (Root.r3 (T.u q0)))))) (Steps.refl _)), (Steps.cons (Step.left (T.u (T.u q0)) (Step.rightD (T.u q0) (Step.root (Root.r3 (T.u q0))))) (Steps.cons (Step.root (Root.r15 (T.u q0))) (Steps.refl _)))⟩
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            have e0 := T.u.inj he
            subst e0
            exact ⟨T.e, (Steps.cons (Step.underU (Step.underU (Step.root (Root.r7 (T.u (T.u T.e)))))) (Steps.cons (Step.root (Root.r3 (T.u T.e))) (Steps.cons (Step.root (Root.r6 )) (Steps.refl _)))), (Steps.cons (Step.root (Root.r2 (T.d (T.u T.e) (T.u (T.u T.e))))) (Steps.cons (Step.underU (Step.leftD (T.u (T.u T.e)) (Step.root (Root.r6 )))) (Steps.cons (Step.underU (Step.rightD T.e (Step.underU (Step.root (Root.r6 ))))) (Steps.cons (Step.underU (Step.rightD T.e (Step.root (Root.r6 )))) (Steps.cons (Step.underU (Step.root (Root.r7 T.e))) (Steps.cons (Step.root (Root.r6 )) (Steps.refl _)))))))⟩
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
        | @underU _ t3 h3 =>
          exact ⟨(T.u (T.u (T.d (T.u (T.u t3)) t3))), (Steps.cons (Step.underU (Step.underU (Step.leftD x0 (Step.underU (Step.underU h3))))) (Steps.cons (Step.underU (Step.underU (Step.rightD (T.u (T.u t3)) h3))) (Steps.refl _))), (Steps.cons (Step.left x0 (Step.rightD (T.u (T.u t3)) (Step.underU (Step.underU h3)))) (Steps.cons (Step.right (T.d (T.u (T.u t3)) (T.u (T.u t3))) h3) (Steps.cons (Step.root (Root.r20 t3)) (Steps.refl _))))⟩
    | @rightD _ _ t1 h1 =>
      cases h1 with
      | root hr =>
        rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          have e0 := T.u.inj he
          have e1 := T.u.inj e0
          subst e1
          exact ⟨(T.u (T.u (T.d q0 (T.u q0)))), (Steps.cons (Step.underU (Step.underU (Step.leftD (T.u q0) (Step.root (Root.r3 q0))))) (Steps.refl _)), (Steps.cons (Step.left (T.u q0) (Step.leftD q0 (Step.root (Root.r3 q0)))) (Steps.cons (Step.root (Root.r15 q0)) (Steps.refl _)))⟩
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          have e0 := T.u.inj he
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
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
      | @underU _ t2 h2 =>
        cases h2 with
        | root hr =>
          rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            have e0 := T.u.inj he
            subst e0
            exact ⟨(T.u (T.u (T.d (T.u q0) (T.u (T.u q0))))), (Steps.cons (Step.underU (Step.underU (Step.leftD (T.u (T.u q0)) (Step.root (Root.r3 (T.u q0)))))) (Steps.refl _)), (Steps.cons (Step.left (T.u (T.u q0)) (Step.leftD (T.u q0) (Step.root (Root.r3 (T.u q0))))) (Steps.cons (Step.root (Root.r15 (T.u q0))) (Steps.refl _)))⟩
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            have e0 := T.u.inj he
            subst e0
            exact ⟨T.e, (Steps.cons (Step.underU (Step.underU (Step.root (Root.r7 (T.u (T.u T.e)))))) (Steps.cons (Step.root (Root.r3 (T.u T.e))) (Steps.cons (Step.root (Root.r6 )) (Steps.refl _)))), (Steps.cons (Step.root (Root.r2 (T.d (T.u (T.u T.e)) (T.u T.e)))) (Steps.cons (Step.underU (Step.leftD (T.u T.e) (Step.underU (Step.root (Root.r6 ))))) (Steps.cons (Step.underU (Step.leftD (T.u T.e) (Step.root (Root.r6 )))) (Steps.cons (Step.underU (Step.rightD T.e (Step.root (Root.r6 )))) (Steps.cons (Step.underU (Step.root (Root.r7 T.e))) (Steps.cons (Step.root (Root.r6 )) (Steps.refl _)))))))⟩
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
        | @underU _ t3 h3 =>
          exact ⟨(T.u (T.u (T.d (T.u (T.u t3)) t3))), (Steps.cons (Step.underU (Step.underU (Step.leftD x0 (Step.underU (Step.underU h3))))) (Steps.cons (Step.underU (Step.underU (Step.rightD (T.u (T.u t3)) h3))) (Steps.refl _))), (Steps.cons (Step.left x0 (Step.leftD (T.u (T.u t3)) (Step.underU (Step.underU h3)))) (Steps.cons (Step.right (T.d (T.u (T.u t3)) (T.u (T.u t3))) h3) (Steps.cons (Step.root (Root.r20 t3)) (Steps.refl _))))⟩
  | @right _ _ t0 h0 =>
    exact ⟨(T.u (T.u (T.d (T.u (T.u t0)) t0))), (Steps.cons (Step.underU (Step.underU (Step.leftD x0 (Step.underU (Step.underU h0))))) (Steps.cons (Step.underU (Step.underU (Step.rightD (T.u (T.u t0)) h0))) (Steps.refl _))), (Steps.cons (Step.left t0 (Step.leftD (T.u (T.u x0)) (Step.underU (Step.underU h0)))) (Steps.cons (Step.left t0 (Step.rightD (T.u (T.u t0)) (Step.underU (Step.underU h0)))) (Steps.cons (Step.root (Root.r20 t0)) (Steps.refl _))))⟩
end submission.Austin12073

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin12073
open T
theorem peak21 (x0 : T) {u : T} (h : Step (T.m (T.u x0) (T.u (T.d T.e x0))) u) : Join (T.u (T.u (T.d (T.d T.e x0) (T.u (T.d T.e x0))))) u := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      have e3 := T.u.inj e1
      have e4 := e3.symm
      have cycle := congrArg size e4
      simp only [size] at cycle
      omega
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
      cases e0
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
      cases e0
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
      cases e1
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      have e3 := T.u.inj e1
      cases e3
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
      have e2 := T.u.inj e0
      have e3 := e1.symm
      subst e3
      have cycle := congrArg size e2
      simp only [size] at cycle
      omega
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := T.u.inj e0
      have e3 := e1.symm
      subst e3
      have cycle := congrArg size e2
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      cases e0
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := T.u.inj e0
      have e3 := T.u.inj e1
      have e4 := e2.symm
      subst e4
      exact ⟨(T.u (T.u (T.d (T.d T.e q0) (T.u (T.d T.e q0))))), (Steps.refl _), (Steps.refl _)⟩
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      have e3 := T.u.inj e1
      have e4 := (T.d.inj e3).1
      have e5 := (T.d.inj e3).2
      have cycle := congrArg size e5
      simp only [size] at cycle
      omega
  | @left _ t0 _ h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := T.u.inj he
        subst e0
        exact ⟨(T.u (T.u (T.d (T.d T.e (T.u (T.u q0))) (T.u (T.d T.e (T.u (T.u q0))))))), (Steps.refl _), (Steps.cons (Step.root (Root.r22 q0)) (Steps.refl _))⟩
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := T.u.inj he
        subst e0
        exact ⟨T.e, (Steps.cons (Step.underU (Step.underU (Step.leftD (T.u (T.d T.e T.e)) (Step.root (Root.r7 T.e))))) (Steps.cons (Step.underU (Step.underU (Step.rightD T.e (Step.underU (Step.root (Root.r7 T.e)))))) (Steps.cons (Step.underU (Step.underU (Step.rightD T.e (Step.root (Root.r6 ))))) (Steps.cons (Step.underU (Step.underU (Step.root (Root.r7 T.e)))) (Steps.cons (Step.underU (Step.root (Root.r6 ))) (Steps.cons (Step.root (Root.r6 )) (Steps.refl _))))))), (Steps.cons (Step.root (Root.r8 (T.u (T.d T.e T.e)))) (Steps.cons (Step.underU (Step.underU (Step.leftD (T.u (T.d T.e T.e)) (Step.underU (Step.root (Root.r7 T.e)))))) (Steps.cons (Step.underU (Step.underU (Step.leftD (T.u (T.d T.e T.e)) (Step.root (Root.r6 ))))) (Steps.cons (Step.underU (Step.underU (Step.rightD T.e (Step.underU (Step.root (Root.r7 T.e)))))) (Steps.cons (Step.underU (Step.underU (Step.rightD T.e (Step.root (Root.r6 ))))) (Steps.cons (Step.underU (Step.underU (Step.root (Root.r7 T.e)))) (Steps.cons (Step.underU (Step.root (Root.r6 ))) (Steps.cons (Step.root (Root.r6 )) (Steps.refl _)))))))))⟩
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
    | @underU _ t1 h1 =>
      exact ⟨(T.u (T.u (T.d (T.d T.e t1) (T.u (T.d T.e t1))))), (Steps.cons (Step.underU (Step.underU (Step.leftD (T.u (T.d T.e x0)) (Step.rightD T.e h1)))) (Steps.cons (Step.underU (Step.underU (Step.rightD (T.d T.e t1) (Step.underU (Step.rightD T.e h1))))) (Steps.refl _))), (Steps.cons (Step.right (T.u t1) (Step.underU (Step.rightD T.e h1))) (Steps.cons (Step.root (Root.r21 t1)) (Steps.refl _)))⟩
  | @right _ _ t0 h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := T.u.inj he
        cases e0
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := T.u.inj he
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
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
    | @underU _ t1 h1 =>
      cases h1 with
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
          exact ⟨T.e, (Steps.cons (Step.underU (Step.underU (Step.leftD (T.u (T.d T.e T.e)) (Step.root (Root.r7 T.e))))) (Steps.cons (Step.underU (Step.underU (Step.rightD T.e (Step.underU (Step.root (Root.r7 T.e)))))) (Steps.cons (Step.underU (Step.underU (Step.rightD T.e (Step.root (Root.r6 ))))) (Steps.cons (Step.underU (Step.underU (Step.root (Root.r7 T.e)))) (Steps.cons (Step.underU (Step.root (Root.r6 ))) (Steps.cons (Step.root (Root.r6 )) (Steps.refl _))))))), (Steps.cons (Step.root (Root.r1 (T.u T.e))) (Steps.refl _))⟩
        · rw [ho]
          cases he
        · rw [ho]
          have e0 := (T.d.inj he).1
          have e1 := (T.d.inj he).2
          cases e0
        · rw [ho]
          cases he
        · rw [ho]
          have e0 := (T.d.inj he).1
          have e1 := (T.d.inj he).2
          cases e0
        · rw [ho]
          cases he
        · rw [ho]
          have e0 := (T.d.inj he).1
          have e1 := (T.d.inj he).2
          have e2 := e0.symm
          subst e2
          subst e1
          exact ⟨T.e, (Steps.cons (Step.underU (Step.underU (Step.leftD (T.u (T.d T.e (T.d T.e T.e))) (Step.root (Root.r13 T.e))))) (Steps.cons (Step.underU (Step.underU (Step.leftD (T.u (T.d T.e (T.d T.e T.e))) (Step.root (Root.r6 ))))) (Steps.cons (Step.underU (Step.underU (Step.rightD T.e (Step.underU (Step.root (Root.r13 T.e)))))) (Steps.cons (Step.underU (Step.underU (Step.rightD T.e (Step.underU (Step.root (Root.r6 )))))) (Steps.cons (Step.underU (Step.underU (Step.rightD T.e (Step.root (Root.r6 ))))) (Steps.cons (Step.underU (Step.underU (Step.root (Root.r7 T.e)))) (Steps.cons (Step.underU (Step.root (Root.r6 ))) (Steps.cons (Step.root (Root.r6 )) (Steps.refl _))))))))), (Steps.cons (Step.left (T.u (T.u T.e)) (Step.underU (Step.root (Root.r7 T.e)))) (Steps.cons (Step.root (Root.r14 (T.u T.e))) (Steps.cons (Step.leftD (T.u T.e) (Step.root (Root.r6 ))) (Steps.cons (Step.rightD T.e (Step.root (Root.r6 ))) (Steps.cons (Step.root (Root.r7 T.e)) (Steps.refl _))))))⟩
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
          cases e0
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
      | @leftD _ t2 _ h2 =>
        cases h2 with
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
      | @rightD _ _ t2 h2 =>
        exact ⟨(T.u (T.u (T.d (T.d T.e t2) (T.u (T.d T.e t2))))), (Steps.cons (Step.underU (Step.underU (Step.leftD (T.u (T.d T.e x0)) (Step.rightD T.e h2)))) (Steps.cons (Step.underU (Step.underU (Step.rightD (T.d T.e t2) (Step.underU (Step.rightD T.e h2))))) (Steps.refl _))), (Steps.cons (Step.left (T.u (T.d T.e t2)) (Step.underU h2)) (Steps.cons (Step.root (Root.r21 t2)) (Steps.refl _)))⟩
end submission.Austin12073

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin12073
open T
theorem peak22 (x0 : T) {u : T} (h : Step (T.m x0 (T.u (T.d T.e (T.u (T.u x0))))) u) : Join (T.u (T.u (T.d (T.d T.e (T.u (T.u x0))) (T.u (T.d T.e (T.u (T.u x0))))))) u := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      have e3 := e1.symm
      have cycle := congrArg size e3
      simp only [size] at cycle
      omega
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
      subst e0
      have e2 := e1.symm
      have cycle := congrArg size e2
      simp only [size] at cycle
      omega
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
      exact ⟨T.e, (Steps.cons (Step.underU (Step.underU (Step.leftD (T.u (T.d T.e (T.u (T.u T.e)))) (Step.rightD T.e (Step.underU (Step.root (Root.r6 ))))))) (Steps.cons (Step.underU (Step.underU (Step.leftD (T.u (T.d T.e (T.u (T.u T.e)))) (Step.rightD T.e (Step.root (Root.r6 )))))) (Steps.cons (Step.underU (Step.underU (Step.leftD (T.u (T.d T.e (T.u (T.u T.e)))) (Step.root (Root.r7 T.e))))) (Steps.cons (Step.underU (Step.underU (Step.rightD T.e (Step.underU (Step.rightD T.e (Step.underU (Step.root (Root.r6 )))))))) (Steps.cons (Step.underU (Step.underU (Step.rightD T.e (Step.underU (Step.rightD T.e (Step.root (Root.r6 ))))))) (Steps.cons (Step.underU (Step.underU (Step.rightD T.e (Step.underU (Step.root (Root.r7 T.e)))))) (Steps.cons (Step.underU (Step.underU (Step.rightD T.e (Step.root (Root.r6 ))))) (Steps.cons (Step.underU (Step.underU (Step.root (Root.r7 T.e)))) (Steps.cons (Step.underU (Step.root (Root.r6 ))) (Steps.cons (Step.root (Root.r6 )) (Steps.refl _))))))))))), (Steps.cons (Step.underU (Step.underU (Step.leftD (T.u (T.d T.e (T.u (T.u T.e)))) (Step.underU (Step.rightD T.e (Step.underU (Step.root (Root.r6 )))))))) (Steps.cons (Step.underU (Step.underU (Step.leftD (T.u (T.d T.e (T.u (T.u T.e)))) (Step.underU (Step.rightD T.e (Step.root (Root.r6 ))))))) (Steps.cons (Step.underU (Step.underU (Step.leftD (T.u (T.d T.e (T.u (T.u T.e)))) (Step.underU (Step.root (Root.r7 T.e)))))) (Steps.cons (Step.underU (Step.underU (Step.leftD (T.u (T.d T.e (T.u (T.u T.e)))) (Step.root (Root.r6 ))))) (Steps.cons (Step.underU (Step.underU (Step.rightD T.e (Step.underU (Step.rightD T.e (Step.underU (Step.root (Root.r6 )))))))) (Steps.cons (Step.underU (Step.underU (Step.rightD T.e (Step.underU (Step.rightD T.e (Step.root (Root.r6 ))))))) (Steps.cons (Step.underU (Step.underU (Step.rightD T.e (Step.underU (Step.root (Root.r7 T.e)))))) (Steps.cons (Step.underU (Step.underU (Step.rightD T.e (Step.root (Root.r6 ))))) (Steps.cons (Step.underU (Step.underU (Step.root (Root.r7 T.e)))) (Steps.cons (Step.underU (Step.root (Root.r6 ))) (Steps.cons (Step.root (Root.r6 )) (Steps.refl _))))))))))))⟩
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
      have e2 := T.u.inj e1
      have e3 := e2.symm
      have cycle := congrArg size e3
      simp only [size] at cycle
      omega
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
      have e3 := T.u.inj e1
      have e4 := e3.symm
      have cycle := congrArg size e4
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
      have e2 := T.u.inj e1
      have e3 := e2.symm
      have cycle := congrArg size e3
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
      have e2 := e1.symm
      have cycle := congrArg size e2
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
      have e2 := e1.symm
      have cycle := congrArg size e2
      simp only [size] at cycle
      omega
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
      have e2 := e1.symm
      have cycle := congrArg size e2
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
      have e2 := e1.symm
      have cycle := congrArg size e2
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
      have e2 := T.u.inj e1
      have e3 := (T.d.inj e2).1
      have e4 := (T.d.inj e2).2
      have e5 := e4.symm
      have cycle := congrArg size e5
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      exact ⟨(T.u (T.u (T.d (T.d T.e (T.u (T.u q0))) (T.u (T.d T.e (T.u (T.u q0))))))), (Steps.refl _), (Steps.refl _)⟩
  | @left _ t0 _ h0 =>
    exact ⟨(T.u (T.u (T.d (T.d T.e (T.u (T.u t0))) (T.u (T.d T.e (T.u (T.u t0))))))), (Steps.cons (Step.underU (Step.underU (Step.leftD (T.u (T.d T.e (T.u (T.u x0)))) (Step.rightD T.e (Step.underU (Step.underU h0)))))) (Steps.cons (Step.underU (Step.underU (Step.rightD (T.d T.e (T.u (T.u t0))) (Step.underU (Step.rightD T.e (Step.underU (Step.underU h0))))))) (Steps.refl _))), (Steps.cons (Step.right t0 (Step.underU (Step.rightD T.e (Step.underU (Step.underU h0))))) (Steps.cons (Step.root (Root.r22 t0)) (Steps.refl _)))⟩
  | @right _ _ t0 h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := T.u.inj he
        cases e0
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := T.u.inj he
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
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
    | @underU _ t1 h1 =>
      cases h1 with
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
          cases e0
        · rw [ho]
          cases he
        · rw [ho]
          have e0 := (T.d.inj he).1
          have e1 := (T.d.inj he).2
          cases e0
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
          cases e0
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
      | @leftD _ t2 _ h2 =>
        cases h2 with
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
      | @rightD _ _ t2 h2 =>
        cases h2 with
        | root hr =>
          rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            have e0 := T.u.inj he
            have e1 := T.u.inj e0
            subst e1
            exact ⟨(T.u (T.u (T.d (T.d T.e q0) (T.u (T.d T.e q0))))), (Steps.cons (Step.underU (Step.underU (Step.leftD (T.u (T.d T.e (T.u (T.u (T.u q0))))) (Step.rightD T.e (Step.root (Root.r3 q0)))))) (Steps.cons (Step.underU (Step.underU (Step.rightD (T.d T.e q0) (Step.underU (Step.rightD T.e (Step.root (Root.r3 q0))))))) (Steps.refl _))), (Steps.cons (Step.root (Root.r21 q0)) (Steps.refl _))⟩
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            have e0 := T.u.inj he
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
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
        | @underU _ t3 h3 =>
          cases h3 with
          | root hr =>
            rcases root_cases hr with ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩ | ⟨q0, he, ho⟩
            · rw [ho]
              cases he
            · rw [ho]
              cases he
            · rw [ho]
              have e0 := T.u.inj he
              subst e0
              exact ⟨(T.u (T.u (T.d (T.d T.e (T.u q0)) (T.u (T.d T.e (T.u q0)))))), (Steps.cons (Step.underU (Step.underU (Step.leftD (T.u (T.d T.e (T.u (T.u (T.u (T.u q0)))))) (Step.rightD T.e (Step.root (Root.r3 (T.u q0))))))) (Steps.cons (Step.underU (Step.underU (Step.rightD (T.d T.e (T.u q0)) (Step.underU (Step.rightD T.e (Step.root (Root.r3 (T.u q0)))))))) (Steps.refl _))), (Steps.cons (Step.root (Root.r21 (T.u q0))) (Steps.refl _))⟩
            · rw [ho]
              cases he
            · rw [ho]
              cases he
            · rw [ho]
              have e0 := T.u.inj he
              subst e0
              exact ⟨T.e, (Steps.cons (Step.underU (Step.underU (Step.leftD (T.u (T.d T.e (T.u (T.u T.e)))) (Step.rightD T.e (Step.underU (Step.root (Root.r6 ))))))) (Steps.cons (Step.underU (Step.underU (Step.leftD (T.u (T.d T.e (T.u (T.u T.e)))) (Step.rightD T.e (Step.root (Root.r6 )))))) (Steps.cons (Step.underU (Step.underU (Step.leftD (T.u (T.d T.e (T.u (T.u T.e)))) (Step.root (Root.r7 T.e))))) (Steps.cons (Step.underU (Step.underU (Step.rightD T.e (Step.underU (Step.rightD T.e (Step.underU (Step.root (Root.r6 )))))))) (Steps.cons (Step.underU (Step.underU (Step.rightD T.e (Step.underU (Step.rightD T.e (Step.root (Root.r6 ))))))) (Steps.cons (Step.underU (Step.underU (Step.rightD T.e (Step.underU (Step.root (Root.r7 T.e)))))) (Steps.cons (Step.underU (Step.underU (Step.rightD T.e (Step.root (Root.r6 ))))) (Steps.cons (Step.underU (Step.underU (Step.root (Root.r7 T.e)))) (Steps.cons (Step.underU (Step.root (Root.r6 ))) (Steps.cons (Step.root (Root.r6 )) (Steps.refl _))))))))))), (Steps.cons (Step.root (Root.r8 (T.u (T.d T.e (T.u T.e))))) (Steps.cons (Step.underU (Step.underU (Step.leftD (T.u (T.d T.e (T.u T.e))) (Step.underU (Step.rightD T.e (Step.root (Root.r6 ))))))) (Steps.cons (Step.underU (Step.underU (Step.leftD (T.u (T.d T.e (T.u T.e))) (Step.underU (Step.root (Root.r7 T.e)))))) (Steps.cons (Step.underU (Step.underU (Step.leftD (T.u (T.d T.e (T.u T.e))) (Step.root (Root.r6 ))))) (Steps.cons (Step.underU (Step.underU (Step.rightD T.e (Step.underU (Step.rightD T.e (Step.root (Root.r6 ))))))) (Steps.cons (Step.underU (Step.underU (Step.rightD T.e (Step.underU (Step.root (Root.r7 T.e)))))) (Steps.cons (Step.underU (Step.underU (Step.rightD T.e (Step.root (Root.r6 ))))) (Steps.cons (Step.underU (Step.underU (Step.root (Root.r7 T.e)))) (Steps.cons (Step.underU (Step.root (Root.r6 ))) (Steps.cons (Step.root (Root.r6 )) (Steps.refl _)))))))))))⟩
            · rw [ho]
              cases he
            · rw [ho]
              cases he
            · rw [ho]
              cases he
            · rw [ho]
              cases he
            · rw [ho]
              cases he
            · rw [ho]
              cases he
            · rw [ho]
              cases he
            · rw [ho]
              cases he
            · rw [ho]
              cases he
            · rw [ho]
              cases he
            · rw [ho]
              cases he
            · rw [ho]
              cases he
            · rw [ho]
              cases he
            · rw [ho]
              cases he
            · rw [ho]
              cases he
            · rw [ho]
              cases he
          | @underU _ t4 h4 =>
            exact ⟨(T.u (T.u (T.d (T.d T.e (T.u (T.u t4))) (T.u (T.d T.e (T.u (T.u t4))))))), (Steps.cons (Step.underU (Step.underU (Step.leftD (T.u (T.d T.e (T.u (T.u x0)))) (Step.rightD T.e (Step.underU (Step.underU h4)))))) (Steps.cons (Step.underU (Step.underU (Step.rightD (T.d T.e (T.u (T.u t4))) (Step.underU (Step.rightD T.e (Step.underU (Step.underU h4))))))) (Steps.refl _))), (Steps.cons (Step.left (T.u (T.d T.e (T.u (T.u t4)))) h4) (Steps.cons (Step.root (Root.r22 t4)) (Steps.refl _)))⟩
end submission.Austin12073

set_option autoImplicit false
namespace submission.Austin12073
open T
theorem root_step {x y z : T} (h : Root x y) (k : Step x z) : Join y z := by
  cases h with
  | r1 => exact peak1 _ k
  | r2 => exact peak2 _ k
  | r3 => exact peak3 _ k
  | r4 => exact peak4 _ _ k
  | r5 => exact peak5 _ _ k
  | r6 => exact peak6 k
  | r7 => exact peak7 _ k
  | r8 => exact peak8 _ k
  | r9 => exact peak9 _ k
  | r10 => exact peak10 _ k
  | r11 => exact peak11 _ k
  | r12 => exact peak12 _ _ k
  | r13 => exact peak13 _ k
  | r14 => exact peak14 _ k
  | r15 => exact peak15 _ k
  | r16 => exact peak16 _ k
  | r17 => exact peak17 _ k
  | r18 => exact peak18 _ k
  | r19 => exact peak19 _ _ k
  | r20 => exact peak20 _ k
  | r21 => exact peak21 _ k
  | r22 => exact peak22 _ k
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
  | underU h ih =>
    cases k with
    | root hr => exact (root_step hr (.underU h)).symm
    | underU k => exact (ih k).underU
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
  | leftD c h ih =>
    cases k with
    | root hr => exact (root_step hr (.leftD c h)).symm
    | leftD _ k => exact (ih k).leftD c
    | @rightD x _ z k =>
      exact ⟨d _ z, Steps.single (.rightD _ k), Steps.single (.leftD z h)⟩
  | rightD c h ih =>
    cases k with
    | root hr => exact (root_step hr (.rightD c h)).symm
    | @leftD x y _ k =>
      exact ⟨d y _, Steps.single (.leftD _ k), Steps.single (.rightD y h)⟩
    | rightD _ k => exact (ih k).rightD c
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
end submission.Austin12073

set_option autoImplicit false
namespace submission.Austin12073
open T
def Carrier := {x : T // Normal x}
noncomputable def mul (x y : Carrier) : Carrier :=
  ⟨norm (m x.val y.val), norm_normal _⟩
theorem equation12073 (x y z : Carrier) :
    (mul y (mul (mul (mul y x) x) (mul z z))) = x := by
  apply Subtype.ext
  change (norm (T.m y.val (norm (T.m (norm (T.m (norm (T.m y.val x.val)) x.val)) (norm (T.m z.val z.val)))))) = x.val
  simp only [norm_m_left, norm_m_right]
  have h : Steps (T.m y.val (T.m (T.m (T.m y.val x.val) x.val) (T.m z.val z.val))) x.val :=
    (Steps.cons (Step.right y.val (Step.left (T.m z.val z.val) (Step.root (Root.r4 y.val x.val)))) (Steps.cons (Step.right y.val (Step.right (T.u (T.u (T.d y.val x.val))) (Step.root (Root.r1 z.val)))) (Steps.cons (Step.right y.val (Step.root (Root.r2 (T.u (T.u (T.d y.val x.val)))))) (Steps.cons (Step.right y.val (Step.root (Root.r3 (T.d y.val x.val)))) (Steps.cons (Step.root (Root.r5 y.val x.val)) (Steps.refl _))))))
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
theorem equation33998 (x y z : Carrier) :
    (opposite (opposite (opposite y y) (opposite x (opposite x z))) z) = x :=
  equation12073 x z y
theorem infinite_model : ∃ (A : Type) (op : A → A → A) (f : Nat → A),
    (∀ x y z, (op y (op (op (op y x) x) (op z z))) = x) ∧
    (∀ n j, f n = f j → n = j) :=
  ⟨Carrier, mul, embed, equation12073, embed_injective⟩
end submission.Austin12073

namespace submission
abbrev CM := Austin12073.Carrier
namespace CM
/-- The model contains an injective image of every natural number. -/
theorem tower_injective (n j : Nat)
    (h : Austin12073.embed n = Austin12073.embed j) : n = j :=
  Austin12073.embed_injective n j h
end CM
noncomputable instance modelMagma : Magma CM := ⟨Austin12073.opposite⟩
end submission

theorem submission : Goal := by
  refine ⟨submission.CM, submission.modelMagma, ?_, ?_⟩
  · intro x y z
    exact (submission.Austin12073.equation33998 x y z).symm
  · intro h
    have bad : 0 = 1 := submission.Austin12073.embed_injective 0 1
      (h (submission.Austin12073.embed 0) (submission.Austin12073.embed 1))
    exact Nat.noConfusion bad
example : Goal := submission
#print axioms submission
#print axioms submission.CM.tower_injective


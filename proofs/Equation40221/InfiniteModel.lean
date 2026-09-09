import Lean.Elab.Tactic.Omega
import JudgeProblem


set_option autoImplicit false
namespace submission.Austin5837
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
  | r x y => 2 * size x + size y + 5
  | u x => size x + 1
  | d x y => size x + size y + 1
  | c x y z => size x + size y + size z + 3
  | m x y => 2 * size x + 3 * size y + 4
theorem size_pos (x : T) : 0 < size x := by
  cases x <;> simp only [size] <;> omega
inductive Root : T → T → Prop where
  | r1 (v0 v1) : Root (T.m (T.m v0 v1) v1) (T.r v1 v0)
  | r2 (v0 v1) : Root (T.m v0 (T.r v0 v1)) (T.d v0 v1)
  | r3 (v0 v1 v2) : Root (T.m v0 (T.d v1 v2)) (T.c v0 v1 v2)
  | r4 (v0 v1 v2) : Root (T.m v0 (T.c v1 v0 v2)) v1
  | r5 (v0 v1) : Root (T.m (T.r v0 v1) v0) (T.r v0 (T.m v1 v0))
  | r6 (v0 v1) : Root (T.m (T.d v0 v1) (T.r v0 v1)) (T.r (T.r v0 v1) v0)
  | r7 (v0 v1 v2) : Root (T.r (T.d v0 v1) v2) (T.c (T.c v2 v0 v1) v0 v1)
  | r8 (v0 v1 v2) : Root (T.m v0 (T.c v0 v1 v2)) (T.r (T.c v0 v1 v2) v1)
  | r9 (v0 v1) : Root (T.r (T.c v0 v0 v1) v0) v0
  | r10 (v0 v1) : Root (T.m (T.c v0 v0 v1) v0) (T.d (T.c v0 v0 v1) v0)
  | r11 (v0 v1) : Root (T.m (T.d (T.c v0 v0 v1) v0) v0) (T.r v0 (T.c v0 v0 v1))
  | r12 (v0 v1 v2) : Root (T.m (T.d v0 v1) (T.c (T.c v2 v0 v1) v0 v1)) (T.d (T.d v0 v1) v2)
  | r13 (v0 v1 v2) : Root (T.c (T.c (T.d v0 v1) (T.d v0 v1) v2) v0 v1) (T.d (T.c (T.d v0 v1) (T.d v0 v1) v2) (T.d v0 v1))
  | r14 (v0 v1 v2) : Root (T.c v0 (T.c (T.d v0 v1) (T.d v0 v1) v2) (T.d v0 v1)) (T.c (T.d v0 v1) (T.d v0 v1) v2)
  | r15 (v0 v1 v2) : Root (T.m (T.c (T.d v0 v1) (T.d v0 v1) v2) (T.c (T.d v0 v1) (T.d v0 v1) v2)) v0
  | r16 (v0 v1 v2) : Root (T.m (T.d (T.d v0 v1) v2) (T.c (T.c v2 v0 v1) v0 v1)) (T.r (T.c (T.c v2 v0 v1) v0 v1) (T.d v0 v1))
  | r17 (v0 v1 v2) : Root (T.m v0 (T.c (T.d v0 v1) (T.d v0 v1) v2)) (T.r (T.c (T.d v0 v1) (T.d v0 v1) v2) (T.c (T.d v0 v1) (T.d v0 v1) v2))
  | r18 (v0 v1 v2) : Root (T.m (T.d v0 v1) (T.c (T.d (T.c (T.d v0 v1) (T.d v0 v1) v2) (T.d v0 v1)) v0 v1)) (T.d (T.d v0 v1) (T.c (T.d v0 v1) (T.d v0 v1) v2))
  | r19 (v0 v1 v2) : Root (T.m (T.d (T.d v0 v1) (T.c (T.d v0 v1) (T.d v0 v1) v2)) (T.c (T.d (T.c (T.d v0 v1) (T.d v0 v1) v2) (T.d v0 v1)) v0 v1)) (T.r (T.c (T.d (T.c (T.d v0 v1) (T.d v0 v1) v2) (T.d v0 v1)) v0 v1) (T.d v0 v1))
  | r20 (v0 v1 v2) : Root (T.m (T.d (T.c (T.d v0 v1) (T.d v0 v1) v2) (T.d v0 v1)) (T.c (T.c (T.d v0 v1) (T.d v0 v1) v2) (T.c (T.d v0 v1) (T.d v0 v1) v2) (T.d v0 v1))) (T.d (T.d (T.c (T.d v0 v1) (T.d v0 v1) v2) (T.d v0 v1)) v0)
  | r21 (v0 v1 v2) : Root (T.m (T.d (T.d (T.c (T.d v0 v1) (T.d v0 v1) v2) (T.d v0 v1)) v0) (T.c (T.c (T.d v0 v1) (T.d v0 v1) v2) (T.c (T.d v0 v1) (T.d v0 v1) v2) (T.d v0 v1))) (T.r (T.c (T.c (T.d v0 v1) (T.d v0 v1) v2) (T.c (T.d v0 v1) (T.d v0 v1) v2) (T.d v0 v1)) (T.d (T.c (T.d v0 v1) (T.d v0 v1) v2) (T.d v0 v1)))
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
  have hpy := size_pos y
  cases h with
  | r1 v0 v1 =>
    have hp0 := size_pos v0
    have hp1 := size_pos v1
    simp only [size]
    omega
  | r2 v0 v1 =>
    have hp0 := size_pos v0
    have hp1 := size_pos v1
    simp only [size]
    omega
  | r3 v0 v1 v2 =>
    have hp0 := size_pos v0
    have hp1 := size_pos v1
    have hp2 := size_pos v2
    simp only [size]
    omega
  | r4 v0 v1 v2 =>
    have hp0 := size_pos v0
    have hp2 := size_pos v2
    simp only [size]
    omega
  | r5 v0 v1 =>
    have hp0 := size_pos v0
    have hp1 := size_pos v1
    simp only [size]
    omega
  | r6 v0 v1 =>
    have hp0 := size_pos v0
    have hp1 := size_pos v1
    simp only [size]
    omega
  | r7 v0 v1 v2 =>
    have hp0 := size_pos v0
    have hp1 := size_pos v1
    have hp2 := size_pos v2
    simp only [size]
    omega
  | r8 v0 v1 v2 =>
    have hp0 := size_pos v0
    have hp1 := size_pos v1
    have hp2 := size_pos v2
    simp only [size]
    omega
  | r9 v0 v1 =>
    have hp1 := size_pos v1
    simp only [size]
    omega
  | r10 v0 v1 =>
    have hp0 := size_pos v0
    have hp1 := size_pos v1
    simp only [size]
    omega
  | r11 v0 v1 =>
    have hp0 := size_pos v0
    have hp1 := size_pos v1
    simp only [size]
    omega
  | r12 v0 v1 v2 =>
    have hp0 := size_pos v0
    have hp1 := size_pos v1
    have hp2 := size_pos v2
    simp only [size]
    omega
  | r13 v0 v1 v2 =>
    have hp0 := size_pos v0
    have hp1 := size_pos v1
    have hp2 := size_pos v2
    simp only [size]
    omega
  | r14 v0 v1 v2 =>
    have hp0 := size_pos v0
    have hp1 := size_pos v1
    have hp2 := size_pos v2
    simp only [size]
    omega
  | r15 v0 v1 v2 =>
    have hp1 := size_pos v1
    have hp2 := size_pos v2
    simp only [size]
    omega
  | r16 v0 v1 v2 =>
    have hp0 := size_pos v0
    have hp1 := size_pos v1
    have hp2 := size_pos v2
    simp only [size]
    omega
  | r17 v0 v1 v2 =>
    have hp0 := size_pos v0
    have hp1 := size_pos v1
    have hp2 := size_pos v2
    simp only [size]
    omega
  | r18 v0 v1 v2 =>
    have hp0 := size_pos v0
    have hp1 := size_pos v1
    have hp2 := size_pos v2
    simp only [size]
    omega
  | r19 v0 v1 v2 =>
    have hp0 := size_pos v0
    have hp1 := size_pos v1
    have hp2 := size_pos v2
    simp only [size]
    omega
  | r20 v0 v1 v2 =>
    have hp0 := size_pos v0
    have hp1 := size_pos v1
    have hp2 := size_pos v2
    simp only [size]
    omega
  | r21 v0 v1 v2 =>
    have hp0 := size_pos v0
    have hp1 := size_pos v1
    have hp2 := size_pos v2
    simp only [size]
    omega
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
    (∃ v0 v1, u = (T.m (T.m v0 v1) v1) ∧ v = (T.r v1 v0)) ∨
    (∃ v0 v1, u = (T.m v0 (T.r v0 v1)) ∧ v = (T.d v0 v1)) ∨
    (∃ v0 v1 v2, u = (T.m v0 (T.d v1 v2)) ∧ v = (T.c v0 v1 v2)) ∨
    (∃ v0 v1 v2, u = (T.m v0 (T.c v1 v0 v2)) ∧ v = v1) ∨
    (∃ v0 v1, u = (T.m (T.r v0 v1) v0) ∧ v = (T.r v0 (T.m v1 v0))) ∨
    (∃ v0 v1, u = (T.m (T.d v0 v1) (T.r v0 v1)) ∧ v = (T.r (T.r v0 v1) v0)) ∨
    (∃ v0 v1 v2, u = (T.r (T.d v0 v1) v2) ∧ v = (T.c (T.c v2 v0 v1) v0 v1)) ∨
    (∃ v0 v1 v2, u = (T.m v0 (T.c v0 v1 v2)) ∧ v = (T.r (T.c v0 v1 v2) v1)) ∨
    (∃ v0 v1, u = (T.r (T.c v0 v0 v1) v0) ∧ v = v0) ∨
    (∃ v0 v1, u = (T.m (T.c v0 v0 v1) v0) ∧ v = (T.d (T.c v0 v0 v1) v0)) ∨
    (∃ v0 v1, u = (T.m (T.d (T.c v0 v0 v1) v0) v0) ∧ v = (T.r v0 (T.c v0 v0 v1))) ∨
    (∃ v0 v1 v2, u = (T.m (T.d v0 v1) (T.c (T.c v2 v0 v1) v0 v1)) ∧ v = (T.d (T.d v0 v1) v2)) ∨
    (∃ v0 v1 v2, u = (T.c (T.c (T.d v0 v1) (T.d v0 v1) v2) v0 v1) ∧ v = (T.d (T.c (T.d v0 v1) (T.d v0 v1) v2) (T.d v0 v1))) ∨
    (∃ v0 v1 v2, u = (T.c v0 (T.c (T.d v0 v1) (T.d v0 v1) v2) (T.d v0 v1)) ∧ v = (T.c (T.d v0 v1) (T.d v0 v1) v2)) ∨
    (∃ v0 v1 v2, u = (T.m (T.c (T.d v0 v1) (T.d v0 v1) v2) (T.c (T.d v0 v1) (T.d v0 v1) v2)) ∧ v = v0) ∨
    (∃ v0 v1 v2, u = (T.m (T.d (T.d v0 v1) v2) (T.c (T.c v2 v0 v1) v0 v1)) ∧ v = (T.r (T.c (T.c v2 v0 v1) v0 v1) (T.d v0 v1))) ∨
    (∃ v0 v1 v2, u = (T.m v0 (T.c (T.d v0 v1) (T.d v0 v1) v2)) ∧ v = (T.r (T.c (T.d v0 v1) (T.d v0 v1) v2) (T.c (T.d v0 v1) (T.d v0 v1) v2))) ∨
    (∃ v0 v1 v2, u = (T.m (T.d v0 v1) (T.c (T.d (T.c (T.d v0 v1) (T.d v0 v1) v2) (T.d v0 v1)) v0 v1)) ∧ v = (T.d (T.d v0 v1) (T.c (T.d v0 v1) (T.d v0 v1) v2))) ∨
    (∃ v0 v1 v2, u = (T.m (T.d (T.d v0 v1) (T.c (T.d v0 v1) (T.d v0 v1) v2)) (T.c (T.d (T.c (T.d v0 v1) (T.d v0 v1) v2) (T.d v0 v1)) v0 v1)) ∧ v = (T.r (T.c (T.d (T.c (T.d v0 v1) (T.d v0 v1) v2) (T.d v0 v1)) v0 v1) (T.d v0 v1))) ∨
    (∃ v0 v1 v2, u = (T.m (T.d (T.c (T.d v0 v1) (T.d v0 v1) v2) (T.d v0 v1)) (T.c (T.c (T.d v0 v1) (T.d v0 v1) v2) (T.c (T.d v0 v1) (T.d v0 v1) v2) (T.d v0 v1))) ∧ v = (T.d (T.d (T.c (T.d v0 v1) (T.d v0 v1) v2) (T.d v0 v1)) v0)) ∨
    (∃ v0 v1 v2, u = (T.m (T.d (T.d (T.c (T.d v0 v1) (T.d v0 v1) v2) (T.d v0 v1)) v0) (T.c (T.c (T.d v0 v1) (T.d v0 v1) v2) (T.c (T.d v0 v1) (T.d v0 v1) v2) (T.d v0 v1))) ∧ v = (T.r (T.c (T.c (T.d v0 v1) (T.d v0 v1) v2) (T.c (T.d v0 v1) (T.d v0 v1) v2) (T.d v0 v1)) (T.d (T.c (T.d v0 v1) (T.d v0 v1) v2) (T.d v0 v1)))) := by
  cases h with
  | r1 => exact (Or.inl ⟨_, _, rfl, rfl⟩)
  | r2 => exact (Or.inr (Or.inl ⟨_, _, rfl, rfl⟩))
  | r3 => exact (Or.inr (Or.inr (Or.inl ⟨_, _, _, rfl, rfl⟩)))
  | r4 => exact (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, rfl, rfl⟩))))
  | r5 => exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, rfl, rfl⟩)))))
  | r6 => exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, rfl, rfl⟩))))))
  | r7 => exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, rfl, rfl⟩)))))))
  | r8 => exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, rfl, rfl⟩))))))))
  | r9 => exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, rfl, rfl⟩)))))))))
  | r10 => exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, rfl, rfl⟩))))))))))
  | r11 => exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, rfl, rfl⟩)))))))))))
  | r12 => exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, rfl, rfl⟩))))))))))))
  | r13 => exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, rfl, rfl⟩)))))))))))))
  | r14 => exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, rfl, rfl⟩))))))))))))))
  | r15 => exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, rfl, rfl⟩)))))))))))))))
  | r16 => exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, rfl, rfl⟩))))))))))))))))
  | r17 => exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, rfl, rfl⟩)))))))))))))))))
  | r18 => exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, rfl, rfl⟩))))))))))))))))))
  | r19 => exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, rfl, rfl⟩)))))))))))))))))))
  | r20 => exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, rfl, rfl⟩))))))))))))))))))))
  | r21 => exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨_, _, _, rfl, rfl⟩))))))))))))))))))))

end submission.Austin5837

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak1 (x0 : T) (x1 : T) {u : T} (h : Step (T.m (T.m x0 x1) x1) u) : Join (T.r x1 x0) u := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := (T.m.inj e0).1
      have e3 := (T.m.inj e0).2
      have e4 := e1.symm
      subst e4
      have e5 := e2.symm
      subst e5
      exact ⟨(T.r q1 q0), (Steps.refl _), (Steps.refl _)⟩
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
      exact ⟨(T.c (T.c x0 q1 q2) q1 q2), (Steps.cons (Step.root (Root.r7 q1 q2 x0)) (Steps.refl _)), (Steps.cons (Step.firstC q1 q2 (Step.root (Root.r3 x0 q1 q2))) (Steps.refl _))⟩
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
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      cases e0
  | @left _ t0 _ h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst e0
        have e2 := e1.symm
        subst e2
        exact ⟨(T.r q1 (T.m q0 q1)), (Steps.refl _), (Steps.cons (Step.root (Root.r5 q1 q0)) (Steps.refl _))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        have e2 := e0.symm
        subst e2
        subst e1
        exact ⟨(T.r (T.r q0 q1) q0), (Steps.refl _), (Steps.cons (Step.root (Root.r6 q0 q1)) (Steps.refl _))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        have e2 := e0.symm
        subst e2
        subst e1
        exact ⟨(T.c (T.c q0 q1 q2) q1 q2), (Steps.cons (Step.root (Root.r7 q1 q2 q0)) (Steps.refl _)), (Steps.cons (Step.root (Root.r3 (T.c q0 q1 q2) q1 q2)) (Steps.refl _))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        have e2 := e0.symm
        subst e2
        subst e1
        exact ⟨(T.r (T.c q1 q0 q2) q0), (Steps.refl _), (Steps.cons (Step.root (Root.r8 q1 q0 q2)) (Steps.refl _))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst e0
        have e2 := e1.symm
        subst e2
        exact ⟨(T.r q0 (T.r q0 q1)), (Steps.refl _), (Steps.cons (Step.root (Root.r5 q0 (T.m q1 q0))) (Steps.cons (Step.rightR q0 (Step.root (Root.r1 q1 q0))) (Steps.refl _)))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst e0
        subst e1
        exact ⟨(T.r (T.r q0 q1) (T.d q0 q1)), (Steps.refl _), (Steps.cons (Step.root (Root.r5 (T.r q0 q1) q0)) (Steps.cons (Step.rightR (T.r q0 q1) (Step.root (Root.r2 q0 q1))) (Steps.refl _)))⟩
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        have e2 := e0.symm
        subst e2
        subst e1
        exact ⟨(T.r (T.c q0 q1 q2) q0), (Steps.refl _), (Steps.cons (Step.root (Root.r5 (T.c q0 q1 q2) q1)) (Steps.cons (Step.rightR (T.c q0 q1 q2) (Step.root (Root.r4 q1 q0 q2))) (Steps.refl _)))⟩
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst e0
        have e2 := e1.symm
        subst e2
        exact ⟨(T.r q0 (T.c q0 q0 q1)), (Steps.refl _), (Steps.cons (Step.root (Root.r11 q0 q1)) (Steps.refl _))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst e0
        have e2 := e1.symm
        subst e2
        exact ⟨(T.r q0 (T.d (T.c q0 q0 q1) q0)), (Steps.refl _), (Steps.cons (Step.root (Root.r5 q0 (T.c q0 q0 q1))) (Steps.cons (Step.rightR q0 (Step.root (Root.r10 q0 q1))) (Steps.refl _)))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst e0
        subst e1
        exact ⟨(T.r (T.c (T.c q2 q0 q1) q0 q1) (T.d q0 q1)), (Steps.refl _), (Steps.cons (Step.root (Root.r16 q0 q1 q2)) (Steps.refl _))⟩
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst e0
        subst e1
        exact ⟨(T.r (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2)), (Steps.refl _), (Steps.cons (Step.root (Root.r17 q0 q1 q2)) (Steps.refl _))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst e0
        subst e1
        exact ⟨(T.r (T.c (T.c q2 q0 q1) q0 q1) (T.d (T.d q0 q1) q2)), (Steps.refl _), (Steps.cons (Step.root (Root.r5 (T.c (T.c q2 q0 q1) q0 q1) (T.d q0 q1))) (Steps.cons (Step.rightR (T.c (T.c q2 q0 q1) q0 q1) (Step.root (Root.r12 q0 q1 q2))) (Steps.refl _)))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        have e2 := e0.symm
        subst e2
        subst e1
        exact ⟨(T.r (T.c (T.d q0 q1) (T.d q0 q1) q2) q0), (Steps.refl _), (Steps.cons (Step.root (Root.r5 (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2))) (Steps.cons (Step.rightR (T.c (T.d q0 q1) (T.d q0 q1) q2) (Step.root (Root.r15 q0 q1 q2))) (Steps.refl _)))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst e0
        subst e1
        exact ⟨(T.r (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1) (T.d q0 q1)), (Steps.refl _), (Steps.cons (Step.root (Root.r19 q0 q1 q2)) (Steps.refl _))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst e0
        subst e1
        exact ⟨(T.r (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1) (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2))), (Steps.refl _), (Steps.cons (Step.root (Root.r5 (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1) (T.d q0 q1))) (Steps.cons (Step.rightR (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1) (Step.root (Root.r18 q0 q1 q2))) (Steps.refl _)))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst e0
        subst e1
        exact ⟨(T.r (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))), (Steps.refl _), (Steps.cons (Step.root (Root.r21 q0 q1 q2)) (Steps.refl _))⟩
      · rw [ho]
        have e0 := (T.m.inj he).1
        have e1 := (T.m.inj he).2
        subst e0
        subst e1
        exact ⟨(T.r (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0)), (Steps.refl _), (Steps.cons (Step.root (Root.r5 (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) (Steps.cons (Step.rightR (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (Step.root (Root.r20 q0 q1 q2))) (Steps.refl _)))⟩
    | @left _ t1 _ h1 =>
      exact ⟨(T.r x1 t1), (Steps.cons (Step.rightR x1 h1) (Steps.refl _)), (Steps.cons (Step.root (Root.r1 t1 x1)) (Steps.refl _))⟩
    | @right _ _ t1 h1 =>
      exact ⟨(T.r t1 x0), (Steps.cons (Step.leftR x0 h1) (Steps.refl _)), (Steps.cons (Step.right (T.m x0 t1) h1) (Steps.cons (Step.root (Root.r1 x0 t1)) (Steps.refl _)))⟩
  | @right _ _ t0 h0 =>
    exact ⟨(T.r t0 x0), (Steps.cons (Step.leftR x0 h0) (Steps.refl _)), (Steps.cons (Step.left t0 (Step.right x0 h0)) (Steps.cons (Step.root (Root.r1 x0 t0)) (Steps.refl _)))⟩
end submission.Austin5837

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak2 (x0 : T) (x1 : T) {u : T} (h : Step (T.m x0 (T.r x0 x1)) u) : Join (T.d x0 x1) u := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
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
      have e3 := (T.r.inj e1).1
      have e4 := (T.r.inj e1).2
      have e5 := e4.symm
      subst e5
      exact ⟨(T.d q0 q1), (Steps.refl _), (Steps.refl _)⟩
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
      have e2 := (T.r.inj e1).1
      have e3 := (T.r.inj e1).2
      have e4 := e2.symm
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
      cases he
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
      cases e1
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
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
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
      cases e1
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
      cases e1
  | @left _ t0 _ h0 =>
    exact ⟨(T.d t0 x1), (Steps.cons (Step.leftD x1 h0) (Steps.refl _)), (Steps.cons (Step.right t0 (Step.leftR x1 h0)) (Steps.cons (Step.root (Root.r2 t0 x1)) (Steps.refl _)))⟩
  | @right _ _ t0 h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
      · rw [ho]
        cases he
      · rw [ho]
        cases he
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
        subst e0
        have e2 := e1.symm
        subst e2
        exact ⟨(T.d (T.d q0 q1) q2), (Steps.refl _), (Steps.cons (Step.root (Root.r12 q0 q1 q2)) (Steps.refl _))⟩
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.r.inj he).1
        have e1 := (T.r.inj he).2
        subst e0
        have e2 := e1.symm
        subst e2
        exact ⟨(T.d (T.c q0 q0 q1) q0), (Steps.refl _), (Steps.cons (Step.root (Root.r10 q0 q1)) (Steps.refl _))⟩
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
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
      exact ⟨(T.d t1 x1), (Steps.cons (Step.leftD x1 h1) (Steps.refl _)), (Steps.cons (Step.left (T.r t1 x1) h1) (Steps.cons (Step.root (Root.r2 t1 x1)) (Steps.refl _)))⟩
    | @rightR _ _ t1 h1 =>
      exact ⟨(T.d x0 t1), (Steps.cons (Step.rightD x0 h1) (Steps.refl _)), (Steps.cons (Step.root (Root.r2 x0 t1)) (Steps.refl _))⟩
end submission.Austin5837

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak3 (x0 : T) (x1 : T) (x2 : T) {u : T} (h : Step (T.m x0 (T.d x1 x2)) u) : Join (T.c x0 x1 x2) u := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
      have e2 := e1.symm
      subst e2
      exact ⟨(T.c (T.c q0 x1 x2) x1 x2), (Steps.cons (Step.firstC x1 x2 (Step.root (Root.r3 q0 x1 x2))) (Steps.refl _)), (Steps.cons (Step.root (Root.r7 x1 x2 q0)) (Steps.refl _))⟩
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
      have e3 := (T.d.inj e1).1
      have e4 := (T.d.inj e1).2
      have e5 := e3.symm
      subst e5
      have e6 := e4.symm
      subst e6
      exact ⟨(T.c q0 q1 q2), (Steps.refl _), (Steps.refl _)⟩
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
      have e2 := e1.symm
      subst e2
      exact ⟨(T.c (T.c (T.c q1 x1 x2) x1 x2) x1 x2), (Steps.cons (Step.firstC x1 x2 (Step.root (Root.r7 x1 x2 q1))) (Steps.refl _)), (Steps.cons (Step.root (Root.r7 x1 x2 (T.m q1 (T.d x1 x2)))) (Steps.cons (Step.firstC x1 x2 (Step.firstC x1 x2 (Step.root (Root.r3 q1 x1 x2)))) (Steps.refl _)))⟩
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
      subst e0
      have e2 := e1.symm
      subst e2
      exact ⟨(T.d (T.c (T.d x1 x2) (T.d x1 x2) q1) (T.d x1 x2)), (Steps.cons (Step.root (Root.r13 x1 x2 q1)) (Steps.refl _)), (Steps.refl _)⟩
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
      have e2 := e1.symm
      subst e2
      exact ⟨(T.c (T.d (T.c (T.d x1 x2) (T.d x1 x2) q1) (T.d x1 x2)) x1 x2), (Steps.refl _), (Steps.cons (Step.root (Root.r7 x1 x2 (T.c (T.d x1 x2) (T.d x1 x2) q1))) (Steps.cons (Step.firstC x1 x2 (Step.root (Root.r13 x1 x2 q1))) (Steps.refl _)))⟩
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
      cases e1
    · rw [ho]
      cases he
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
      cases e1
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
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
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
      cases e1
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
      cases e1
  | @left _ t0 _ h0 =>
    exact ⟨(T.c t0 x1 x2), (Steps.cons (Step.firstC x1 x2 h0) (Steps.refl _)), (Steps.cons (Step.root (Root.r3 t0 x1 x2)) (Steps.refl _))⟩
  | @right _ _ t0 h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
    | @leftD _ t1 _ h1 =>
      exact ⟨(T.c x0 t1 x2), (Steps.cons (Step.secondC x0 x2 h1) (Steps.refl _)), (Steps.cons (Step.root (Root.r3 x0 t1 x2)) (Steps.refl _))⟩
    | @rightD _ _ t1 h1 =>
      exact ⟨(T.c x0 x1 t1), (Steps.cons (Step.thirdC x0 x1 h1) (Steps.refl _)), (Steps.cons (Step.root (Root.r3 x0 x1 t1)) (Steps.refl _))⟩
end submission.Austin5837

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak4 (x0 : T) (x1 : T) (x2 : T) {u : T} (h : Step (T.m x0 (T.c x1 x0 x2)) u) : Join x1 u := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
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
      have e3 := (T.c.inj e1).1
      have e4 := (T.c.inj e1).2.1
      have e5 := (T.c.inj e1).2.2
      have e6 := e3.symm
      subst e6
      have e7 := e5.symm
      subst e7
      exact ⟨q1, (Steps.refl _), (Steps.refl _)⟩
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
      cases he
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      have e3 := (T.c.inj e1).1
      have e4 := (T.c.inj e1).2.1
      have e5 := (T.c.inj e1).2.2
      have e6 := e3.symm
      subst e6
      have e7 := e4.symm
      subst e7
      have e8 := e5.symm
      subst e8
      exact ⟨q1, (Steps.refl _), (Steps.cons (Step.root (Root.r9 q1 q2)) (Steps.refl _))⟩
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
      have e2 := (T.c.inj e1).1
      have e3 := (T.c.inj e1).2.1
      have e4 := (T.c.inj e1).2.2
      subst e2
      have e5 := e3.symm
      have cycle := congrArg size e5
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
      have e2 := (T.c.inj e1).1
      have e3 := (T.c.inj e1).2.1
      have e4 := (T.c.inj e1).2.2
      subst e2
      cases e3
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
      have e2 := (T.c.inj e1).1
      have e3 := (T.c.inj e1).2.1
      have e4 := (T.c.inj e1).2.2
      subst e2
      have e5 := e3.symm
      have cycle := congrArg size e5
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      have e3 := (T.c.inj e1).1
      have e4 := (T.c.inj e1).2.1
      have e5 := (T.c.inj e1).2.2
      subst e3
      have cycle := congrArg size e4
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
      have e2 := (T.c.inj e1).1
      have e3 := (T.c.inj e1).2.1
      have e4 := (T.c.inj e1).2.2
      subst e2
      have e5 := e3.symm
      have cycle := congrArg size e5
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
      have e2 := (T.c.inj e1).1
      have e3 := (T.c.inj e1).2.1
      have e4 := (T.c.inj e1).2.2
      subst e2
      have e5 := e3.symm
      have cycle := congrArg size e5
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
      have e2 := (T.c.inj e1).1
      have e3 := (T.c.inj e1).2.1
      have e4 := (T.c.inj e1).2.2
      subst e2
      cases e3
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
      have e2 := (T.c.inj e1).1
      have e3 := (T.c.inj e1).2.1
      have e4 := (T.c.inj e1).2.2
      subst e2
      cases e3
  | @left _ t0 _ h0 =>
    exact ⟨x1, (Steps.refl _), (Steps.cons (Step.right t0 (Step.secondC x1 x2 h0)) (Steps.cons (Step.root (Root.r4 t0 x1 x2)) (Steps.refl _)))⟩
  | @right _ _ t0 h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.c.inj he).1
        have e1 := (T.c.inj he).2.1
        have e2 := (T.c.inj he).2.2
        subst e0
        have e3 := e1.symm
        subst e3
        have e4 := e2.symm
        subst e4
        exact ⟨(T.c (T.d q0 q1) (T.d q0 q1) q2), (Steps.refl _), (Steps.cons (Step.root (Root.r3 q0 (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) (Steps.cons (Step.root (Root.r14 q0 q1 q2)) (Steps.refl _)))⟩
      · rw [ho]
        have e0 := (T.c.inj he).1
        have e1 := (T.c.inj he).2.1
        have e2 := (T.c.inj he).2.2
        have e3 := e0.symm
        subst e3
        subst e1
        subst e2
        exact ⟨q0, (Steps.refl _), (Steps.cons (Step.root (Root.r15 q0 q1 q2)) (Steps.refl _))⟩
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
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
      exact ⟨t1, (Steps.cons h1 (Steps.refl _)), (Steps.cons (Step.root (Root.r4 x0 t1 x2)) (Steps.refl _))⟩
    | @secondC _ _ t1 _ h1 =>
      exact ⟨x1, (Steps.refl _), (Steps.cons (Step.left (T.c x1 t1 x2) h1) (Steps.cons (Step.root (Root.r4 t1 x1 x2)) (Steps.refl _)))⟩
    | @thirdC _ _ _ t1 h1 =>
      exact ⟨x1, (Steps.refl _), (Steps.cons (Step.root (Root.r4 x0 x1 t1)) (Steps.refl _))⟩
end submission.Austin5837

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak5 (x0 : T) (x1 : T) {u : T} (h : Step (T.m (T.r x0 x1) x0) u) : Join (T.r x0 (T.m x1 x0)) u := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
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
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      subst e1
      exact ⟨(T.c (T.c (T.c x1 q1 q2) q1 q2) q1 q2), (Steps.cons (Step.root (Root.r7 q1 q2 (T.m x1 (T.d q1 q2)))) (Steps.cons (Step.firstC q1 q2 (Step.firstC q1 q2 (Step.root (Root.r3 x1 q1 q2)))) (Steps.refl _))), (Steps.cons (Step.firstC q1 q2 (Step.root (Root.r7 q1 q2 x1))) (Steps.refl _))⟩
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
      have e2 := (T.r.inj e0).1
      have e3 := (T.r.inj e0).2
      have e4 := e1.symm
      subst e4
      have e5 := e3.symm
      subst e5
      exact ⟨(T.r q0 (T.m q1 q0)), (Steps.refl _), (Steps.refl _)⟩
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
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      cases e0
  | @left _ t0 _ h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
      · rw [ho]
        cases he
      · rw [ho]
        cases he
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
        subst e0
        have e2 := e1.symm
        subst e2
        exact ⟨(T.c (T.c (T.c q2 q0 q1) q0 q1) q0 q1), (Steps.cons (Step.root (Root.r7 q0 q1 (T.m q2 (T.d q0 q1)))) (Steps.cons (Step.firstC q0 q1 (Step.firstC q0 q1 (Step.root (Root.r3 q2 q0 q1)))) (Steps.refl _))), (Steps.cons (Step.root (Root.r3 (T.c (T.c q2 q0 q1) q0 q1) q0 q1)) (Steps.refl _))⟩
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.r.inj he).1
        have e1 := (T.r.inj he).2
        subst e0
        have e2 := e1.symm
        subst e2
        exact ⟨q0, (Steps.cons (Step.rightR (T.c q0 q0 q1) (Step.root (Root.r4 q0 q0 q1))) (Steps.cons (Step.root (Root.r9 q0 q1)) (Steps.refl _))), (Steps.cons (Step.root (Root.r4 q0 q0 q1)) (Steps.refl _))⟩
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
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
      exact ⟨(T.r t1 (T.m x1 t1)), (Steps.cons (Step.leftR (T.m x1 x0) h1) (Steps.cons (Step.rightR t1 (Step.right x1 h1)) (Steps.refl _))), (Steps.cons (Step.right (T.r t1 x1) h1) (Steps.cons (Step.root (Root.r5 t1 x1)) (Steps.refl _)))⟩
    | @rightR _ _ t1 h1 =>
      exact ⟨(T.r x0 (T.m t1 x0)), (Steps.cons (Step.rightR x0 (Step.left x0 h1)) (Steps.refl _)), (Steps.cons (Step.root (Root.r5 x0 t1)) (Steps.refl _))⟩
  | @right _ _ t0 h0 =>
    exact ⟨(T.r t0 (T.m x1 t0)), (Steps.cons (Step.leftR (T.m x1 x0) h0) (Steps.cons (Step.rightR t0 (Step.right x1 h0)) (Steps.refl _))), (Steps.cons (Step.left t0 (Step.leftR x1 h0)) (Steps.cons (Step.root (Root.r5 t0 x1)) (Steps.refl _)))⟩
end submission.Austin5837

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak6 (x0 : T) (x1 : T) {u : T} (h : Step (T.m (T.d x0 x1) (T.r x0 x1)) u) : Join (T.r (T.r x0 x1) x0) u := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      cases e0
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      have e3 := (T.r.inj e1).1
      have e4 := (T.r.inj e1).2
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
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      cases e1
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      cases e0
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := (T.d.inj e0).1
      have e3 := (T.d.inj e0).2
      have e4 := (T.r.inj e1).1
      have e5 := (T.r.inj e1).2
      have e6 := e2.symm
      subst e6
      have e7 := e3.symm
      subst e7
      exact ⟨(T.r (T.r q0 q1) q0), (Steps.refl _), (Steps.refl _)⟩
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
      have e2 := (T.d.inj e0).1
      have e3 := (T.d.inj e0).2
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
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := (T.d.inj e0).1
      have e3 := (T.d.inj e0).2
      cases e1
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      cases e1
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := (T.d.inj e0).1
      have e3 := (T.d.inj e0).2
      cases e1
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := (T.d.inj e0).1
      have e3 := (T.d.inj e0).2
      cases e1
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := (T.d.inj e0).1
      have e3 := (T.d.inj e0).2
      cases e1
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := (T.d.inj e0).1
      have e3 := (T.d.inj e0).2
      cases e1
  | @left _ t0 _ h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
    | @leftD _ t1 _ h1 =>
      exact ⟨(T.r (T.r t1 x1) t1), (Steps.cons (Step.leftR x0 (Step.leftR x1 h1)) (Steps.cons (Step.rightR (T.r t1 x1) h1) (Steps.refl _))), (Steps.cons (Step.right (T.d t1 x1) (Step.leftR x1 h1)) (Steps.cons (Step.root (Root.r6 t1 x1)) (Steps.refl _)))⟩
    | @rightD _ _ t1 h1 =>
      exact ⟨(T.r (T.r x0 t1) x0), (Steps.cons (Step.leftR x0 (Step.rightR x0 h1)) (Steps.refl _)), (Steps.cons (Step.right (T.d x0 t1) (Step.rightR x0 h1)) (Steps.cons (Step.root (Root.r6 x0 t1)) (Steps.refl _)))⟩
  | @right _ _ t0 h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
      · rw [ho]
        cases he
      · rw [ho]
        cases he
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
        subst e0
        have e2 := e1.symm
        subst e2
        exact ⟨(T.r (T.c (T.c q2 q0 q1) q0 q1) (T.d q0 q1)), (Steps.cons (Step.leftR (T.d q0 q1) (Step.root (Root.r7 q0 q1 q2))) (Steps.refl _)), (Steps.cons (Step.root (Root.r16 q0 q1 q2)) (Steps.refl _))⟩
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.r.inj he).1
        have e1 := (T.r.inj he).2
        subst e0
        have e2 := e1.symm
        subst e2
        exact ⟨(T.r q0 (T.c q0 q0 q1)), (Steps.cons (Step.leftR (T.c q0 q0 q1) (Step.root (Root.r9 q0 q1))) (Steps.refl _)), (Steps.cons (Step.root (Root.r11 q0 q1)) (Steps.refl _))⟩
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
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
      exact ⟨(T.r (T.r t1 x1) t1), (Steps.cons (Step.leftR x0 (Step.leftR x1 h1)) (Steps.cons (Step.rightR (T.r t1 x1) h1) (Steps.refl _))), (Steps.cons (Step.left (T.r t1 x1) (Step.leftD x1 h1)) (Steps.cons (Step.root (Root.r6 t1 x1)) (Steps.refl _)))⟩
    | @rightR _ _ t1 h1 =>
      exact ⟨(T.r (T.r x0 t1) x0), (Steps.cons (Step.leftR x0 (Step.rightR x0 h1)) (Steps.refl _)), (Steps.cons (Step.left (T.r x0 t1) (Step.rightD x0 h1)) (Steps.cons (Step.root (Root.r6 x0 t1)) (Steps.refl _)))⟩
end submission.Austin5837

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak7 (x0 : T) (x1 : T) (x2 : T) {u : T} (h : Step (T.r (T.d x0 x1) x2) u) : Join (T.c (T.c x2 x0 x1) x0 x1) u := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
    · rw [ho]
      cases he
    · rw [ho]
      cases he
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
      have e2 := (T.d.inj e0).1
      have e3 := (T.d.inj e0).2
      have e4 := e1.symm
      subst e4
      have e5 := e2.symm
      subst e5
      have e6 := e3.symm
      subst e6
      exact ⟨(T.c (T.c q2 q0 q1) q0 q1), (Steps.refl _), (Steps.refl _)⟩
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.r.inj he).1
      have e1 := (T.r.inj he).2
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
  | @leftR _ t0 _ h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
    | @leftD _ t1 _ h1 =>
      exact ⟨(T.c (T.c x2 t1 x1) t1 x1), (Steps.cons (Step.firstC x0 x1 (Step.secondC x2 x1 h1)) (Steps.cons (Step.secondC (T.c x2 t1 x1) x1 h1) (Steps.refl _))), (Steps.cons (Step.root (Root.r7 t1 x1 x2)) (Steps.refl _))⟩
    | @rightD _ _ t1 h1 =>
      exact ⟨(T.c (T.c x2 x0 t1) x0 t1), (Steps.cons (Step.firstC x0 x1 (Step.thirdC x2 x0 h1)) (Steps.cons (Step.thirdC (T.c x2 x0 t1) x0 h1) (Steps.refl _))), (Steps.cons (Step.root (Root.r7 x0 t1 x2)) (Steps.refl _))⟩
  | @rightR _ _ t0 h0 =>
    exact ⟨(T.c (T.c t0 x0 x1) x0 x1), (Steps.cons (Step.firstC x0 x1 (Step.firstC x0 x1 h0)) (Steps.refl _)), (Steps.cons (Step.root (Root.r7 x0 x1 t0)) (Steps.refl _))⟩
end submission.Austin5837

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak8 (x0 : T) (x1 : T) (x2 : T) {u : T} (h : Step (T.m x0 (T.c x0 x1 x2)) u) : Join (T.r (T.c x0 x1 x2) x1) u := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
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
      have e3 := (T.c.inj e1).1
      have e4 := (T.c.inj e1).2.1
      have e5 := (T.c.inj e1).2.2
      have e6 := e3.symm
      subst e6
      have e7 := e4.symm
      subst e7
      have e8 := e5.symm
      subst e8
      exact ⟨q1, (Steps.cons (Step.root (Root.r9 q1 q2)) (Steps.refl _)), (Steps.refl _)⟩
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
      cases he
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      have e3 := (T.c.inj e1).1
      have e4 := (T.c.inj e1).2.1
      have e5 := (T.c.inj e1).2.2
      have e6 := e4.symm
      subst e6
      have e7 := e5.symm
      subst e7
      exact ⟨(T.r (T.c q0 q1 q2) q1), (Steps.refl _), (Steps.refl _)⟩
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
      have e2 := (T.c.inj e1).1
      have e3 := (T.c.inj e1).2.1
      have e4 := (T.c.inj e1).2.2
      cases e2
    · rw [ho]
      cases he
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
      have e2 := (T.c.inj e1).1
      have e3 := (T.c.inj e1).2.1
      have e4 := (T.c.inj e1).2.2
      cases e2
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
      have e2 := (T.c.inj e1).1
      have e3 := (T.c.inj e1).2.1
      have e4 := (T.c.inj e1).2.2
      cases e2
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      have e3 := (T.c.inj e1).1
      have e4 := (T.c.inj e1).2.1
      have e5 := (T.c.inj e1).2.2
      have cycle := congrArg size e3
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
      have e2 := (T.c.inj e1).1
      have e3 := (T.c.inj e1).2.1
      have e4 := (T.c.inj e1).2.2
      have e5 := (T.d.inj e2).1
      have e6 := (T.d.inj e2).2
      have e7 := e3.symm
      subst e7
      have e8 := e4.symm
      subst e8
      have cycle := congrArg size e5
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
      have e2 := (T.c.inj e1).1
      have e3 := (T.c.inj e1).2.1
      have e4 := (T.c.inj e1).2.2
      have e5 := (T.d.inj e2).1
      have e6 := (T.d.inj e2).2
      have e7 := e3.symm
      subst e7
      have e8 := e4.symm
      subst e8
      cases e5
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
      have e2 := (T.c.inj e1).1
      have e3 := (T.c.inj e1).2.1
      have e4 := (T.c.inj e1).2.2
      cases e2
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
      have e2 := (T.c.inj e1).1
      have e3 := (T.c.inj e1).2.1
      have e4 := (T.c.inj e1).2.2
      cases e2
  | @left _ t0 _ h0 =>
    exact ⟨(T.r (T.c t0 x1 x2) x1), (Steps.cons (Step.leftR x1 (Step.firstC x1 x2 h0)) (Steps.refl _)), (Steps.cons (Step.right t0 (Step.firstC x1 x2 h0)) (Steps.cons (Step.root (Root.r8 t0 x1 x2)) (Steps.refl _)))⟩
  | @right _ _ t0 h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.c.inj he).1
        have e1 := (T.c.inj he).2.1
        have e2 := (T.c.inj he).2.2
        subst e0
        have e3 := e1.symm
        subst e3
        have e4 := e2.symm
        subst e4
        exact ⟨(T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)), (Steps.cons (Step.leftR q0 (Step.root (Root.r13 q0 q1 q2))) (Steps.cons (Step.root (Root.r7 (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1) q0)) (Steps.cons (Step.firstC (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1) (Step.root (Root.r14 q0 q1 q2))) (Steps.refl _)))), (Steps.cons (Step.root (Root.r3 (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) (Steps.refl _))⟩
      · rw [ho]
        have e0 := (T.c.inj he).1
        have e1 := (T.c.inj he).2.1
        have e2 := (T.c.inj he).2.2
        have e3 := e0.symm
        subst e3
        subst e1
        subst e2
        exact ⟨(T.r (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2)), (Steps.cons (Step.leftR (T.c (T.d q0 q1) (T.d q0 q1) q2) (Step.root (Root.r14 q0 q1 q2))) (Steps.refl _)), (Steps.cons (Step.root (Root.r17 q0 q1 q2)) (Steps.refl _))⟩
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
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
      exact ⟨(T.r (T.c t1 x1 x2) x1), (Steps.cons (Step.leftR x1 (Step.firstC x1 x2 h1)) (Steps.refl _)), (Steps.cons (Step.left (T.c t1 x1 x2) h1) (Steps.cons (Step.root (Root.r8 t1 x1 x2)) (Steps.refl _)))⟩
    | @secondC _ _ t1 _ h1 =>
      exact ⟨(T.r (T.c x0 t1 x2) t1), (Steps.cons (Step.leftR x1 (Step.secondC x0 x2 h1)) (Steps.cons (Step.rightR (T.c x0 t1 x2) h1) (Steps.refl _))), (Steps.cons (Step.root (Root.r8 x0 t1 x2)) (Steps.refl _))⟩
    | @thirdC _ _ _ t1 h1 =>
      exact ⟨(T.r (T.c x0 x1 t1) x1), (Steps.cons (Step.leftR x1 (Step.thirdC x0 x1 h1)) (Steps.refl _)), (Steps.cons (Step.root (Root.r8 x0 x1 t1)) (Steps.refl _))⟩
end submission.Austin5837

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak9 (x0 : T) (x1 : T) {u : T} (h : Step (T.r (T.c x0 x0 x1) x0) u) : Join x0 u := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
    · rw [ho]
      cases he
    · rw [ho]
      cases he
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
      cases e0
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.r.inj he).1
      have e1 := (T.r.inj he).2
      have e2 := (T.c.inj e0).1
      have e3 := (T.c.inj e0).2.1
      have e4 := (T.c.inj e0).2.2
      have e5 := e1.symm
      subst e5
      have e6 := e4.symm
      subst e6
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
    · rw [ho]
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
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.c.inj he).1
        have e1 := (T.c.inj he).2.1
        have e2 := (T.c.inj he).2.2
        subst e0
        have e3 := e1.symm
        have cycle := congrArg size e3
        simp only [size] at cycle
        omega
      · rw [ho]
        have e0 := (T.c.inj he).1
        have e1 := (T.c.inj he).2.1
        have e2 := (T.c.inj he).2.2
        have e3 := e0.symm
        subst e3
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
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
    | @firstC _ t1 _ _ h1 =>
      exact ⟨t1, (Steps.cons h1 (Steps.refl _)), (Steps.cons (Step.leftR x0 (Step.secondC t1 x1 h1)) (Steps.cons (Step.rightR (T.c t1 t1 x1) h1) (Steps.cons (Step.root (Root.r9 t1 x1)) (Steps.refl _))))⟩
    | @secondC _ _ t1 _ h1 =>
      exact ⟨t1, (Steps.cons h1 (Steps.refl _)), (Steps.cons (Step.leftR x0 (Step.firstC t1 x1 h1)) (Steps.cons (Step.rightR (T.c t1 t1 x1) h1) (Steps.cons (Step.root (Root.r9 t1 x1)) (Steps.refl _))))⟩
    | @thirdC _ _ _ t1 h1 =>
      exact ⟨x0, (Steps.refl _), (Steps.cons (Step.root (Root.r9 x0 t1)) (Steps.refl _))⟩
  | @rightR _ _ t0 h0 =>
    exact ⟨t0, (Steps.cons h0 (Steps.refl _)), (Steps.cons (Step.leftR t0 (Step.firstC x0 x1 h0)) (Steps.cons (Step.leftR t0 (Step.secondC t0 x1 h0)) (Steps.cons (Step.root (Root.r9 t0 x1)) (Steps.refl _))))⟩
end submission.Austin5837

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak10 (x0 : T) (x1 : T) {u : T} (h : Step (T.m (T.c x0 x0 x1) x0) u) : Join (T.d (T.c x0 x0 x1) x0) u := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
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
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      subst e1
      exact ⟨(T.d (T.c (T.d q1 q2) (T.d q1 q2) x1) (T.d q1 q2)), (Steps.refl _), (Steps.cons (Step.root (Root.r13 q1 q2 x1)) (Steps.refl _))⟩
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
      have e2 := (T.c.inj e0).1
      have e3 := (T.c.inj e0).2.1
      have e4 := (T.c.inj e0).2.2
      have e5 := e1.symm
      subst e5
      have e6 := e4.symm
      subst e6
      exact ⟨(T.d (T.c q0 q0 q1) q0), (Steps.refl _), (Steps.refl _)⟩
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
      cases he
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := (T.c.inj e0).1
      have e3 := (T.c.inj e0).2.1
      have e4 := (T.c.inj e0).2.2
      subst e1
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
      rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.c.inj he).1
        have e1 := (T.c.inj he).2.1
        have e2 := (T.c.inj he).2.2
        subst e0
        have e3 := e1.symm
        have cycle := congrArg size e3
        simp only [size] at cycle
        omega
      · rw [ho]
        have e0 := (T.c.inj he).1
        have e1 := (T.c.inj he).2.1
        have e2 := (T.c.inj he).2.2
        have e3 := e0.symm
        subst e3
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
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
    | @firstC _ t1 _ _ h1 =>
      exact ⟨(T.d (T.c t1 t1 x1) t1), (Steps.cons (Step.leftD x0 (Step.firstC x0 x1 h1)) (Steps.cons (Step.leftD x0 (Step.secondC t1 x1 h1)) (Steps.cons (Step.rightD (T.c t1 t1 x1) h1) (Steps.refl _)))), (Steps.cons (Step.left x0 (Step.secondC t1 x1 h1)) (Steps.cons (Step.right (T.c t1 t1 x1) h1) (Steps.cons (Step.root (Root.r10 t1 x1)) (Steps.refl _))))⟩
    | @secondC _ _ t1 _ h1 =>
      exact ⟨(T.d (T.c t1 t1 x1) t1), (Steps.cons (Step.leftD x0 (Step.firstC x0 x1 h1)) (Steps.cons (Step.leftD x0 (Step.secondC t1 x1 h1)) (Steps.cons (Step.rightD (T.c t1 t1 x1) h1) (Steps.refl _)))), (Steps.cons (Step.left x0 (Step.firstC t1 x1 h1)) (Steps.cons (Step.right (T.c t1 t1 x1) h1) (Steps.cons (Step.root (Root.r10 t1 x1)) (Steps.refl _))))⟩
    | @thirdC _ _ _ t1 h1 =>
      exact ⟨(T.d (T.c x0 x0 t1) x0), (Steps.cons (Step.leftD x0 (Step.thirdC x0 x0 h1)) (Steps.refl _)), (Steps.cons (Step.root (Root.r10 x0 t1)) (Steps.refl _))⟩
  | @right _ _ t0 h0 =>
    exact ⟨(T.d (T.c t0 t0 x1) t0), (Steps.cons (Step.leftD x0 (Step.firstC x0 x1 h0)) (Steps.cons (Step.leftD x0 (Step.secondC t0 x1 h0)) (Steps.cons (Step.rightD (T.c t0 t0 x1) h0) (Steps.refl _)))), (Steps.cons (Step.left t0 (Step.firstC x0 x1 h0)) (Steps.cons (Step.left t0 (Step.secondC t0 x1 h0)) (Steps.cons (Step.root (Root.r10 t0 x1)) (Steps.refl _))))⟩
end submission.Austin5837

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak11 (x0 : T) (x1 : T) {u : T} (h : Step (T.m (T.d (T.c x0 x0 x1) x0) x0) u) : Join (T.r x0 (T.c x0 x0 x1)) u := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
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
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      subst e1
      exact ⟨(T.c (T.d (T.c (T.d q1 q2) (T.d q1 q2) x1) (T.d q1 q2)) q1 q2), (Steps.cons (Step.root (Root.r7 q1 q2 (T.c (T.d q1 q2) (T.d q1 q2) x1))) (Steps.cons (Step.firstC q1 q2 (Step.root (Root.r13 q1 q2 x1))) (Steps.refl _))), (Steps.refl _)⟩
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
      have e2 := (T.d.inj e0).1
      have e3 := (T.d.inj e0).2
      subst e1
      have e4 := e2.symm
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
      cases e0
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := (T.d.inj e0).1
      have e3 := (T.d.inj e0).2
      have e4 := e1.symm
      subst e4
      have e5 := (T.c.inj e2).1
      have e6 := (T.c.inj e2).2.1
      have e7 := (T.c.inj e2).2.2
      have e8 := e7.symm
      subst e8
      exact ⟨(T.r q0 (T.c q0 q0 q1)), (Steps.refl _), (Steps.refl _)⟩
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
      cases he
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
      subst e1
      cases e2
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
      subst e1
      cases e2
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := (T.d.inj e0).1
      have e3 := (T.d.inj e0).2
      subst e1
      have e4 := (T.c.inj e2).1
      have e5 := (T.c.inj e2).2.1
      have e6 := (T.c.inj e2).2.2
      cases e3
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := (T.d.inj e0).1
      have e3 := (T.d.inj e0).2
      subst e1
      cases e2
  | @left _ t0 _ h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
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
        rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          have e0 := (T.c.inj he).1
          have e1 := (T.c.inj he).2.1
          have e2 := (T.c.inj he).2.2
          subst e0
          have e3 := e1.symm
          have cycle := congrArg size e3
          simp only [size] at cycle
          omega
        · rw [ho]
          have e0 := (T.c.inj he).1
          have e1 := (T.c.inj he).2.1
          have e2 := (T.c.inj he).2.2
          have e3 := e0.symm
          subst e3
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
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
      | @firstC _ t2 _ _ h2 =>
        exact ⟨(T.r t2 (T.c t2 t2 x1)), (Steps.cons (Step.leftR (T.c x0 x0 x1) h2) (Steps.cons (Step.rightR t2 (Step.firstC x0 x1 h2)) (Steps.cons (Step.rightR t2 (Step.secondC t2 x1 h2)) (Steps.refl _)))), (Steps.cons (Step.left x0 (Step.leftD x0 (Step.secondC t2 x1 h2))) (Steps.cons (Step.left x0 (Step.rightD (T.c t2 t2 x1) h2)) (Steps.cons (Step.right (T.d (T.c t2 t2 x1) t2) h2) (Steps.cons (Step.root (Root.r11 t2 x1)) (Steps.refl _)))))⟩
      | @secondC _ _ t2 _ h2 =>
        exact ⟨(T.r t2 (T.c t2 t2 x1)), (Steps.cons (Step.leftR (T.c x0 x0 x1) h2) (Steps.cons (Step.rightR t2 (Step.firstC x0 x1 h2)) (Steps.cons (Step.rightR t2 (Step.secondC t2 x1 h2)) (Steps.refl _)))), (Steps.cons (Step.left x0 (Step.leftD x0 (Step.firstC t2 x1 h2))) (Steps.cons (Step.left x0 (Step.rightD (T.c t2 t2 x1) h2)) (Steps.cons (Step.right (T.d (T.c t2 t2 x1) t2) h2) (Steps.cons (Step.root (Root.r11 t2 x1)) (Steps.refl _)))))⟩
      | @thirdC _ _ _ t2 h2 =>
        exact ⟨(T.r x0 (T.c x0 x0 t2)), (Steps.cons (Step.rightR x0 (Step.thirdC x0 x0 h2)) (Steps.refl _)), (Steps.cons (Step.root (Root.r11 x0 t2)) (Steps.refl _))⟩
    | @rightD _ _ t1 h1 =>
      exact ⟨(T.r t1 (T.c t1 t1 x1)), (Steps.cons (Step.leftR (T.c x0 x0 x1) h1) (Steps.cons (Step.rightR t1 (Step.firstC x0 x1 h1)) (Steps.cons (Step.rightR t1 (Step.secondC t1 x1 h1)) (Steps.refl _)))), (Steps.cons (Step.left x0 (Step.leftD t1 (Step.firstC x0 x1 h1))) (Steps.cons (Step.left x0 (Step.leftD t1 (Step.secondC t1 x1 h1))) (Steps.cons (Step.right (T.d (T.c t1 t1 x1) t1) h1) (Steps.cons (Step.root (Root.r11 t1 x1)) (Steps.refl _)))))⟩
  | @right _ _ t0 h0 =>
    exact ⟨(T.r t0 (T.c t0 t0 x1)), (Steps.cons (Step.leftR (T.c x0 x0 x1) h0) (Steps.cons (Step.rightR t0 (Step.firstC x0 x1 h0)) (Steps.cons (Step.rightR t0 (Step.secondC t0 x1 h0)) (Steps.refl _)))), (Steps.cons (Step.left t0 (Step.leftD x0 (Step.firstC x0 x1 h0))) (Steps.cons (Step.left t0 (Step.leftD x0 (Step.secondC t0 x1 h0))) (Steps.cons (Step.left t0 (Step.rightD (T.c t0 t0 x1) h0)) (Steps.cons (Step.root (Root.r11 t0 x1)) (Steps.refl _)))))⟩
end submission.Austin5837

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak12 (x0 : T) (x1 : T) (x2 : T) {u : T} (h : Step (T.m (T.d x0 x1) (T.c (T.c x2 x0 x1) x0 x1)) u) : Join (T.d (T.d x0 x1) x2) u := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
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
      have e3 := (T.c.inj e1).1
      have e4 := (T.c.inj e1).2.1
      have e5 := (T.c.inj e1).2.2
      have e6 := e3.symm
      subst e6
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
      have e2 := (T.d.inj e0).1
      have e3 := (T.d.inj e0).2
      cases e1
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      have e3 := (T.c.inj e1).1
      have e4 := (T.c.inj e1).2.1
      have e5 := (T.c.inj e1).2.2
      cases e3
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
      have e2 := (T.d.inj e0).1
      have e3 := (T.d.inj e0).2
      have e4 := (T.c.inj e1).1
      have e5 := (T.c.inj e1).2.1
      have e6 := (T.c.inj e1).2.2
      have e7 := e2.symm
      subst e7
      have e8 := e3.symm
      subst e8
      have e9 := (T.c.inj e4).1
      have e10 := (T.c.inj e4).2.1
      have e11 := (T.c.inj e4).2.2
      have e12 := e9.symm
      subst e12
      exact ⟨(T.d (T.d q0 q1) q2), (Steps.refl _), (Steps.refl _)⟩
    · rw [ho]
      cases he
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
      have e4 := (T.c.inj e1).1
      have e5 := (T.c.inj e1).2.1
      have e6 := (T.c.inj e1).2.2
      subst e2
      have e7 := e3.symm
      subst e7
      have e8 := (T.c.inj e4).1
      have e9 := (T.c.inj e4).2.1
      have e10 := (T.c.inj e4).2.2
      have e11 := e5.symm
      have cycle := congrArg size e11
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      have e3 := (T.c.inj e1).1
      have e4 := (T.c.inj e1).2.1
      have e5 := (T.c.inj e1).2.2
      cases e3
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := (T.d.inj e0).1
      have e3 := (T.d.inj e0).2
      have e4 := (T.c.inj e1).1
      have e5 := (T.c.inj e1).2.1
      have e6 := (T.c.inj e1).2.2
      have e7 := e2.symm
      subst e7
      have e8 := e3.symm
      subst e8
      cases e4
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := (T.d.inj e0).1
      have e3 := (T.d.inj e0).2
      have e4 := (T.c.inj e1).1
      have e5 := (T.c.inj e1).2.1
      have e6 := (T.c.inj e1).2.2
      subst e2
      subst e3
      cases e4
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := (T.d.inj e0).1
      have e3 := (T.d.inj e0).2
      have e4 := (T.c.inj e1).1
      have e5 := (T.c.inj e1).2.1
      have e6 := (T.c.inj e1).2.2
      subst e2
      subst e3
      have e7 := (T.c.inj e4).1
      have e8 := (T.c.inj e4).2.1
      have e9 := (T.c.inj e4).2.2
      subst e7
      cases e8
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := (T.d.inj e0).1
      have e3 := (T.d.inj e0).2
      have e4 := (T.c.inj e1).1
      have e5 := (T.c.inj e1).2.1
      have e6 := (T.c.inj e1).2.2
      subst e2
      have e7 := e3.symm
      subst e7
      have e8 := (T.c.inj e4).1
      have e9 := (T.c.inj e4).2.1
      have e10 := (T.c.inj e4).2.2
      cases e5
  | @left _ t0 _ h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
    | @leftD _ t1 _ h1 =>
      exact ⟨(T.d (T.d t1 x1) x2), (Steps.cons (Step.leftD x2 (Step.leftD x1 h1)) (Steps.refl _)), (Steps.cons (Step.right (T.d t1 x1) (Step.firstC x0 x1 (Step.secondC x2 x1 h1))) (Steps.cons (Step.right (T.d t1 x1) (Step.secondC (T.c x2 t1 x1) x1 h1)) (Steps.cons (Step.root (Root.r12 t1 x1 x2)) (Steps.refl _))))⟩
    | @rightD _ _ t1 h1 =>
      exact ⟨(T.d (T.d x0 t1) x2), (Steps.cons (Step.leftD x2 (Step.rightD x0 h1)) (Steps.refl _)), (Steps.cons (Step.right (T.d x0 t1) (Step.firstC x0 x1 (Step.thirdC x2 x0 h1))) (Steps.cons (Step.right (T.d x0 t1) (Step.thirdC (T.c x2 x0 t1) x0 h1)) (Steps.cons (Step.root (Root.r12 x0 t1 x2)) (Steps.refl _))))⟩
  | @right _ _ t0 h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.c.inj he).1
        have e1 := (T.c.inj he).2.1
        have e2 := (T.c.inj he).2.2
        have e3 := (T.c.inj e0).1
        have e4 := (T.c.inj e0).2.1
        have e5 := (T.c.inj e0).2.2
        have e6 := e1.symm
        subst e6
        have e7 := e2.symm
        subst e7
        subst e3
        have cycle := congrArg size e4
        simp only [size] at cycle
        omega
      · rw [ho]
        have e0 := (T.c.inj he).1
        have e1 := (T.c.inj he).2.1
        have e2 := (T.c.inj he).2.2
        have e3 := e0.symm
        subst e3
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
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
    | @firstC _ t1 _ _ h1 =>
      cases h1 with
      | root hr =>
        rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          have e0 := (T.c.inj he).1
          have e1 := (T.c.inj he).2.1
          have e2 := (T.c.inj he).2.2
          subst e0
          have e3 := e1.symm
          subst e3
          have e4 := e2.symm
          subst e4
          exact ⟨(T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)), (Steps.refl _), (Steps.cons (Step.root (Root.r18 q0 q1 q2)) (Steps.refl _))⟩
        · rw [ho]
          have e0 := (T.c.inj he).1
          have e1 := (T.c.inj he).2.1
          have e2 := (T.c.inj he).2.2
          have e3 := e0.symm
          subst e3
          subst e1
          subst e2
          exact ⟨(T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0), (Steps.refl _), (Steps.cons (Step.root (Root.r20 q0 q1 q2)) (Steps.refl _))⟩
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
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
        exact ⟨(T.d (T.d x0 x1) t2), (Steps.cons (Step.rightD (T.d x0 x1) h2) (Steps.refl _)), (Steps.cons (Step.root (Root.r12 x0 x1 t2)) (Steps.refl _))⟩
      | @secondC _ _ t2 _ h2 =>
        exact ⟨(T.d (T.d t2 x1) x2), (Steps.cons (Step.leftD x2 (Step.leftD x1 h2)) (Steps.refl _)), (Steps.cons (Step.left (T.c (T.c x2 t2 x1) x0 x1) (Step.leftD x1 h2)) (Steps.cons (Step.right (T.d t2 x1) (Step.secondC (T.c x2 t2 x1) x1 h2)) (Steps.cons (Step.root (Root.r12 t2 x1 x2)) (Steps.refl _))))⟩
      | @thirdC _ _ _ t2 h2 =>
        exact ⟨(T.d (T.d x0 t2) x2), (Steps.cons (Step.leftD x2 (Step.rightD x0 h2)) (Steps.refl _)), (Steps.cons (Step.left (T.c (T.c x2 x0 t2) x0 x1) (Step.rightD x0 h2)) (Steps.cons (Step.right (T.d x0 t2) (Step.thirdC (T.c x2 x0 t2) x0 h2)) (Steps.cons (Step.root (Root.r12 x0 t2 x2)) (Steps.refl _))))⟩
    | @secondC _ _ t1 _ h1 =>
      exact ⟨(T.d (T.d t1 x1) x2), (Steps.cons (Step.leftD x2 (Step.leftD x1 h1)) (Steps.refl _)), (Steps.cons (Step.left (T.c (T.c x2 x0 x1) t1 x1) (Step.leftD x1 h1)) (Steps.cons (Step.right (T.d t1 x1) (Step.firstC t1 x1 (Step.secondC x2 x1 h1))) (Steps.cons (Step.root (Root.r12 t1 x1 x2)) (Steps.refl _))))⟩
    | @thirdC _ _ _ t1 h1 =>
      exact ⟨(T.d (T.d x0 t1) x2), (Steps.cons (Step.leftD x2 (Step.rightD x0 h1)) (Steps.refl _)), (Steps.cons (Step.left (T.c (T.c x2 x0 x1) x0 t1) (Step.rightD x0 h1)) (Steps.cons (Step.right (T.d x0 t1) (Step.firstC x0 t1 (Step.thirdC x2 x0 h1))) (Steps.cons (Step.root (Root.r12 x0 t1 x2)) (Steps.refl _))))⟩
end submission.Austin5837

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak13 (x0 : T) (x1 : T) (x2 : T) {u : T} (h : Step (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) x0 x1) u) : Join (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) u := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
    · rw [ho]
      cases he
    · rw [ho]
      cases he
    · rw [ho]
      cases he
    · rw [ho]
      cases he
    · rw [ho]
      cases he
    · rw [ho]
      cases he
    · rw [ho]
      cases he
    · rw [ho]
      cases he
    · rw [ho]
      cases he
    · rw [ho]
      cases he
    · rw [ho]
      cases he
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.c.inj he).1
      have e1 := (T.c.inj he).2.1
      have e2 := (T.c.inj he).2.2
      have e3 := (T.c.inj e0).1
      have e4 := (T.c.inj e0).2.1
      have e5 := (T.c.inj e0).2.2
      have e6 := e1.symm
      subst e6
      have e7 := e2.symm
      subst e7
      have e8 := e5.symm
      subst e8
      exact ⟨(T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)), (Steps.refl _), (Steps.refl _)⟩
    · rw [ho]
      have e0 := (T.c.inj he).1
      have e1 := (T.c.inj he).2.1
      have e2 := (T.c.inj he).2.2
      have e3 := e0.symm
      subst e3
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
      cases he
    · rw [ho]
      cases he
    · rw [ho]
      cases he
  | @firstC _ t0 _ _ h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.c.inj he).1
        have e1 := (T.c.inj he).2.1
        have e2 := (T.c.inj he).2.2
        cases e0
      · rw [ho]
        have e0 := (T.c.inj he).1
        have e1 := (T.c.inj he).2.1
        have e2 := (T.c.inj he).2.2
        have e3 := e0.symm
        subst e3
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
    | @firstC _ t1 _ _ h1 =>
      cases h1 with
      | root hr =>
        rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
      | @leftD _ t2 _ h2 =>
        exact ⟨(T.d (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.d t2 x1)), (Steps.cons (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h2))) (Steps.cons (Step.leftD (T.d x0 x1) (Step.secondC (T.d t2 x1) x2 (Step.leftD x1 h2))) (Steps.cons (Step.rightD (T.c (T.d t2 x1) (T.d t2 x1) x2) (Step.leftD x1 h2)) (Steps.refl _)))), (Steps.cons (Step.firstC x0 x1 (Step.secondC (T.d t2 x1) x2 (Step.leftD x1 h2))) (Steps.cons (Step.secondC (T.c (T.d t2 x1) (T.d t2 x1) x2) x1 h2) (Steps.cons (Step.root (Root.r13 t2 x1 x2)) (Steps.refl _))))⟩
      | @rightD _ _ t2 h2 =>
        exact ⟨(T.d (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.d x0 t2)), (Steps.cons (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h2))) (Steps.cons (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t2) x2 (Step.rightD x0 h2))) (Steps.cons (Step.rightD (T.c (T.d x0 t2) (T.d x0 t2) x2) (Step.rightD x0 h2)) (Steps.refl _)))), (Steps.cons (Step.firstC x0 x1 (Step.secondC (T.d x0 t2) x2 (Step.rightD x0 h2))) (Steps.cons (Step.thirdC (T.c (T.d x0 t2) (T.d x0 t2) x2) x0 h2) (Steps.cons (Step.root (Root.r13 x0 t2 x2)) (Steps.refl _))))⟩
    | @secondC _ _ t1 _ h1 =>
      cases h1 with
      | root hr =>
        rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
      | @leftD _ t2 _ h2 =>
        exact ⟨(T.d (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.d t2 x1)), (Steps.cons (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h2))) (Steps.cons (Step.leftD (T.d x0 x1) (Step.secondC (T.d t2 x1) x2 (Step.leftD x1 h2))) (Steps.cons (Step.rightD (T.c (T.d t2 x1) (T.d t2 x1) x2) (Step.leftD x1 h2)) (Steps.refl _)))), (Steps.cons (Step.firstC x0 x1 (Step.firstC (T.d t2 x1) x2 (Step.leftD x1 h2))) (Steps.cons (Step.secondC (T.c (T.d t2 x1) (T.d t2 x1) x2) x1 h2) (Steps.cons (Step.root (Root.r13 t2 x1 x2)) (Steps.refl _))))⟩
      | @rightD _ _ t2 h2 =>
        exact ⟨(T.d (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.d x0 t2)), (Steps.cons (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h2))) (Steps.cons (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t2) x2 (Step.rightD x0 h2))) (Steps.cons (Step.rightD (T.c (T.d x0 t2) (T.d x0 t2) x2) (Step.rightD x0 h2)) (Steps.refl _)))), (Steps.cons (Step.firstC x0 x1 (Step.firstC (T.d x0 t2) x2 (Step.rightD x0 h2))) (Steps.cons (Step.thirdC (T.c (T.d x0 t2) (T.d x0 t2) x2) x0 h2) (Steps.cons (Step.root (Root.r13 x0 t2 x2)) (Steps.refl _))))⟩
    | @thirdC _ _ _ t1 h1 =>
      exact ⟨(T.d (T.c (T.d x0 x1) (T.d x0 x1) t1) (T.d x0 x1)), (Steps.cons (Step.leftD (T.d x0 x1) (Step.thirdC (T.d x0 x1) (T.d x0 x1) h1)) (Steps.refl _)), (Steps.cons (Step.root (Root.r13 x0 x1 t1)) (Steps.refl _))⟩
  | @secondC _ _ t0 _ h0 =>
    exact ⟨(T.d (T.c (T.d t0 x1) (T.d t0 x1) x2) (T.d t0 x1)), (Steps.cons (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h0))) (Steps.cons (Step.leftD (T.d x0 x1) (Step.secondC (T.d t0 x1) x2 (Step.leftD x1 h0))) (Steps.cons (Step.rightD (T.c (T.d t0 x1) (T.d t0 x1) x2) (Step.leftD x1 h0)) (Steps.refl _)))), (Steps.cons (Step.firstC t0 x1 (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h0))) (Steps.cons (Step.firstC t0 x1 (Step.secondC (T.d t0 x1) x2 (Step.leftD x1 h0))) (Steps.cons (Step.root (Root.r13 t0 x1 x2)) (Steps.refl _))))⟩
  | @thirdC _ _ _ t0 h0 =>
    exact ⟨(T.d (T.c (T.d x0 t0) (T.d x0 t0) x2) (T.d x0 t0)), (Steps.cons (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h0))) (Steps.cons (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t0) x2 (Step.rightD x0 h0))) (Steps.cons (Step.rightD (T.c (T.d x0 t0) (T.d x0 t0) x2) (Step.rightD x0 h0)) (Steps.refl _)))), (Steps.cons (Step.firstC x0 t0 (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h0))) (Steps.cons (Step.firstC x0 t0 (Step.secondC (T.d x0 t0) x2 (Step.rightD x0 h0))) (Steps.cons (Step.root (Root.r13 x0 t0 x2)) (Steps.refl _))))⟩
end submission.Austin5837

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak14 (x0 : T) (x1 : T) (x2 : T) {u : T} (h : Step (T.c x0 (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) u) : Join (T.c (T.d x0 x1) (T.d x0 x1) x2) u := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
    · rw [ho]
      cases he
    · rw [ho]
      cases he
    · rw [ho]
      cases he
    · rw [ho]
      cases he
    · rw [ho]
      cases he
    · rw [ho]
      cases he
    · rw [ho]
      cases he
    · rw [ho]
      cases he
    · rw [ho]
      cases he
    · rw [ho]
      cases he
    · rw [ho]
      cases he
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.c.inj he).1
      have e1 := (T.c.inj he).2.1
      have e2 := (T.c.inj he).2.2
      subst e0
      have e3 := e1.symm
      have cycle := congrArg size e3
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.c.inj he).1
      have e1 := (T.c.inj he).2.1
      have e2 := (T.c.inj he).2.2
      have e3 := e0.symm
      subst e3
      have e4 := (T.c.inj e1).1
      have e5 := (T.c.inj e1).2.1
      have e6 := (T.c.inj e1).2.2
      have e7 := (T.d.inj e2).1
      have e8 := (T.d.inj e2).2
      have e9 := (T.d.inj e4).1
      have e10 := (T.d.inj e4).2
      have e11 := (T.d.inj e5).1
      have e12 := (T.d.inj e5).2
      have e13 := e6.symm
      subst e13
      have e14 := e8.symm
      subst e14
      exact ⟨(T.c (T.d q0 q1) (T.d q0 q1) q2), (Steps.refl _), (Steps.refl _)⟩
    · rw [ho]
      cases he
    · rw [ho]
      cases he
    · rw [ho]
      cases he
    · rw [ho]
      cases he
    · rw [ho]
      cases he
    · rw [ho]
      cases he
    · rw [ho]
      cases he
  | @firstC _ t0 _ _ h0 =>
    exact ⟨(T.c (T.d t0 x1) (T.d t0 x1) x2), (Steps.cons (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h0)) (Steps.cons (Step.secondC (T.d t0 x1) x2 (Step.leftD x1 h0)) (Steps.refl _))), (Steps.cons (Step.secondC t0 (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h0))) (Steps.cons (Step.secondC t0 (T.d x0 x1) (Step.secondC (T.d t0 x1) x2 (Step.leftD x1 h0))) (Steps.cons (Step.thirdC t0 (T.c (T.d t0 x1) (T.d t0 x1) x2) (Step.leftD x1 h0)) (Steps.cons (Step.root (Root.r14 t0 x1 x2)) (Steps.refl _)))))⟩
  | @secondC _ _ t0 _ h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.c.inj he).1
        have e1 := (T.c.inj he).2.1
        have e2 := (T.c.inj he).2.2
        cases e0
      · rw [ho]
        have e0 := (T.c.inj he).1
        have e1 := (T.c.inj he).2.1
        have e2 := (T.c.inj he).2.2
        have e3 := e0.symm
        subst e3
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
    | @firstC _ t1 _ _ h1 =>
      cases h1 with
      | root hr =>
        rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
      | @leftD _ t2 _ h2 =>
        exact ⟨(T.c (T.d t2 x1) (T.d t2 x1) x2), (Steps.cons (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h2)) (Steps.cons (Step.secondC (T.d t2 x1) x2 (Step.leftD x1 h2)) (Steps.refl _))), (Steps.cons (Step.firstC (T.c (T.d t2 x1) (T.d x0 x1) x2) (T.d x0 x1) h2) (Steps.cons (Step.secondC t2 (T.d x0 x1) (Step.secondC (T.d t2 x1) x2 (Step.leftD x1 h2))) (Steps.cons (Step.thirdC t2 (T.c (T.d t2 x1) (T.d t2 x1) x2) (Step.leftD x1 h2)) (Steps.cons (Step.root (Root.r14 t2 x1 x2)) (Steps.refl _)))))⟩
      | @rightD _ _ t2 h2 =>
        exact ⟨(T.c (T.d x0 t2) (T.d x0 t2) x2), (Steps.cons (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h2)) (Steps.cons (Step.secondC (T.d x0 t2) x2 (Step.rightD x0 h2)) (Steps.refl _))), (Steps.cons (Step.secondC x0 (T.d x0 x1) (Step.secondC (T.d x0 t2) x2 (Step.rightD x0 h2))) (Steps.cons (Step.thirdC x0 (T.c (T.d x0 t2) (T.d x0 t2) x2) (Step.rightD x0 h2)) (Steps.cons (Step.root (Root.r14 x0 t2 x2)) (Steps.refl _))))⟩
    | @secondC _ _ t1 _ h1 =>
      cases h1 with
      | root hr =>
        rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
      | @leftD _ t2 _ h2 =>
        exact ⟨(T.c (T.d t2 x1) (T.d t2 x1) x2), (Steps.cons (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h2)) (Steps.cons (Step.secondC (T.d t2 x1) x2 (Step.leftD x1 h2)) (Steps.refl _))), (Steps.cons (Step.firstC (T.c (T.d x0 x1) (T.d t2 x1) x2) (T.d x0 x1) h2) (Steps.cons (Step.secondC t2 (T.d x0 x1) (Step.firstC (T.d t2 x1) x2 (Step.leftD x1 h2))) (Steps.cons (Step.thirdC t2 (T.c (T.d t2 x1) (T.d t2 x1) x2) (Step.leftD x1 h2)) (Steps.cons (Step.root (Root.r14 t2 x1 x2)) (Steps.refl _)))))⟩
      | @rightD _ _ t2 h2 =>
        exact ⟨(T.c (T.d x0 t2) (T.d x0 t2) x2), (Steps.cons (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h2)) (Steps.cons (Step.secondC (T.d x0 t2) x2 (Step.rightD x0 h2)) (Steps.refl _))), (Steps.cons (Step.secondC x0 (T.d x0 x1) (Step.firstC (T.d x0 t2) x2 (Step.rightD x0 h2))) (Steps.cons (Step.thirdC x0 (T.c (T.d x0 t2) (T.d x0 t2) x2) (Step.rightD x0 h2)) (Steps.cons (Step.root (Root.r14 x0 t2 x2)) (Steps.refl _))))⟩
    | @thirdC _ _ _ t1 h1 =>
      exact ⟨(T.c (T.d x0 x1) (T.d x0 x1) t1), (Steps.cons (Step.thirdC (T.d x0 x1) (T.d x0 x1) h1) (Steps.refl _)), (Steps.cons (Step.root (Root.r14 x0 x1 t1)) (Steps.refl _))⟩
  | @thirdC _ _ _ t0 h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
    | @leftD _ t1 _ h1 =>
      exact ⟨(T.c (T.d t1 x1) (T.d t1 x1) x2), (Steps.cons (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h1)) (Steps.cons (Step.secondC (T.d t1 x1) x2 (Step.leftD x1 h1)) (Steps.refl _))), (Steps.cons (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d t1 x1) h1) (Steps.cons (Step.secondC t1 (T.d t1 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h1))) (Steps.cons (Step.secondC t1 (T.d t1 x1) (Step.secondC (T.d t1 x1) x2 (Step.leftD x1 h1))) (Steps.cons (Step.root (Root.r14 t1 x1 x2)) (Steps.refl _)))))⟩
    | @rightD _ _ t1 h1 =>
      exact ⟨(T.c (T.d x0 t1) (T.d x0 t1) x2), (Steps.cons (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h1)) (Steps.cons (Step.secondC (T.d x0 t1) x2 (Step.rightD x0 h1)) (Steps.refl _))), (Steps.cons (Step.secondC x0 (T.d x0 t1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h1))) (Steps.cons (Step.secondC x0 (T.d x0 t1) (Step.secondC (T.d x0 t1) x2 (Step.rightD x0 h1))) (Steps.cons (Step.root (Root.r14 x0 t1 x2)) (Steps.refl _))))⟩
end submission.Austin5837

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak15 (x0 : T) (x1 : T) (x2 : T) {u : T} (h : Step (T.m (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2)) u) : Join x0 u := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
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
      have e3 := (T.c.inj e1).1
      have e4 := (T.c.inj e1).2.1
      have e5 := (T.c.inj e1).2.2
      have e6 := e3.symm
      subst e6
      cases e4
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
      have e2 := e0.symm
      subst e2
      have e3 := (T.c.inj e1).1
      have e4 := (T.c.inj e1).2.1
      have e5 := (T.c.inj e1).2.2
      cases e3
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := (T.c.inj e0).1
      have e3 := (T.c.inj e0).2.1
      have e4 := (T.c.inj e0).2.2
      have e5 := e1.symm
      subst e5
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
      cases he
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := (T.c.inj e0).1
      have e3 := (T.c.inj e0).2.1
      have e4 := (T.c.inj e0).2.2
      have e5 := (T.c.inj e1).1
      have e6 := (T.c.inj e1).2.1
      have e7 := (T.c.inj e1).2.2
      have e8 := (T.d.inj e2).1
      have e9 := (T.d.inj e2).2
      have e10 := (T.d.inj e3).1
      have e11 := (T.d.inj e3).2
      have e12 := e4.symm
      subst e12
      have e13 := (T.d.inj e5).1
      have e14 := (T.d.inj e5).2
      have e15 := (T.d.inj e6).1
      have e16 := (T.d.inj e6).2
      have e17 := e8.symm
      subst e17
      have e18 := e9.symm
      subst e18
      exact ⟨q0, (Steps.refl _), (Steps.refl _)⟩
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      cases e0
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      have e3 := (T.c.inj e1).1
      have e4 := (T.c.inj e1).2.1
      have e5 := (T.c.inj e1).2.2
      have e6 := (T.d.inj e3).1
      have e7 := (T.d.inj e3).2
      have e8 := (T.d.inj e4).1
      have e9 := (T.d.inj e4).2
      have e10 := e5.symm
      subst e10
      have cycle := congrArg size e6
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
      cases e0
  | @left _ t0 _ h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.c.inj he).1
        have e1 := (T.c.inj he).2.1
        have e2 := (T.c.inj he).2.2
        cases e0
      · rw [ho]
        have e0 := (T.c.inj he).1
        have e1 := (T.c.inj he).2.1
        have e2 := (T.c.inj he).2.2
        have e3 := e0.symm
        subst e3
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
    | @firstC _ t1 _ _ h1 =>
      cases h1 with
      | root hr =>
        rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
      | @leftD _ t2 _ h2 =>
        exact ⟨t2, (Steps.cons h2 (Steps.refl _)), (Steps.cons (Step.left (T.c (T.d x0 x1) (T.d x0 x1) x2) (Step.secondC (T.d t2 x1) x2 (Step.leftD x1 h2))) (Steps.cons (Step.right (T.c (T.d t2 x1) (T.d t2 x1) x2) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h2))) (Steps.cons (Step.right (T.c (T.d t2 x1) (T.d t2 x1) x2) (Step.secondC (T.d t2 x1) x2 (Step.leftD x1 h2))) (Steps.cons (Step.root (Root.r15 t2 x1 x2)) (Steps.refl _)))))⟩
      | @rightD _ _ t2 h2 =>
        exact ⟨x0, (Steps.refl _), (Steps.cons (Step.left (T.c (T.d x0 x1) (T.d x0 x1) x2) (Step.secondC (T.d x0 t2) x2 (Step.rightD x0 h2))) (Steps.cons (Step.right (T.c (T.d x0 t2) (T.d x0 t2) x2) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h2))) (Steps.cons (Step.right (T.c (T.d x0 t2) (T.d x0 t2) x2) (Step.secondC (T.d x0 t2) x2 (Step.rightD x0 h2))) (Steps.cons (Step.root (Root.r15 x0 t2 x2)) (Steps.refl _)))))⟩
    | @secondC _ _ t1 _ h1 =>
      cases h1 with
      | root hr =>
        rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
      | @leftD _ t2 _ h2 =>
        exact ⟨t2, (Steps.cons h2 (Steps.refl _)), (Steps.cons (Step.left (T.c (T.d x0 x1) (T.d x0 x1) x2) (Step.firstC (T.d t2 x1) x2 (Step.leftD x1 h2))) (Steps.cons (Step.right (T.c (T.d t2 x1) (T.d t2 x1) x2) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h2))) (Steps.cons (Step.right (T.c (T.d t2 x1) (T.d t2 x1) x2) (Step.secondC (T.d t2 x1) x2 (Step.leftD x1 h2))) (Steps.cons (Step.root (Root.r15 t2 x1 x2)) (Steps.refl _)))))⟩
      | @rightD _ _ t2 h2 =>
        exact ⟨x0, (Steps.refl _), (Steps.cons (Step.left (T.c (T.d x0 x1) (T.d x0 x1) x2) (Step.firstC (T.d x0 t2) x2 (Step.rightD x0 h2))) (Steps.cons (Step.right (T.c (T.d x0 t2) (T.d x0 t2) x2) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h2))) (Steps.cons (Step.right (T.c (T.d x0 t2) (T.d x0 t2) x2) (Step.secondC (T.d x0 t2) x2 (Step.rightD x0 h2))) (Steps.cons (Step.root (Root.r15 x0 t2 x2)) (Steps.refl _)))))⟩
    | @thirdC _ _ _ t1 h1 =>
      exact ⟨x0, (Steps.refl _), (Steps.cons (Step.right (T.c (T.d x0 x1) (T.d x0 x1) t1) (Step.thirdC (T.d x0 x1) (T.d x0 x1) h1)) (Steps.cons (Step.root (Root.r15 x0 x1 t1)) (Steps.refl _)))⟩
  | @right _ _ t0 h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.c.inj he).1
        have e1 := (T.c.inj he).2.1
        have e2 := (T.c.inj he).2.2
        cases e0
      · rw [ho]
        have e0 := (T.c.inj he).1
        have e1 := (T.c.inj he).2.1
        have e2 := (T.c.inj he).2.2
        have e3 := e0.symm
        subst e3
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
    | @firstC _ t1 _ _ h1 =>
      cases h1 with
      | root hr =>
        rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
      | @leftD _ t2 _ h2 =>
        exact ⟨t2, (Steps.cons h2 (Steps.refl _)), (Steps.cons (Step.left (T.c (T.d t2 x1) (T.d x0 x1) x2) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h2))) (Steps.cons (Step.left (T.c (T.d t2 x1) (T.d x0 x1) x2) (Step.secondC (T.d t2 x1) x2 (Step.leftD x1 h2))) (Steps.cons (Step.right (T.c (T.d t2 x1) (T.d t2 x1) x2) (Step.secondC (T.d t2 x1) x2 (Step.leftD x1 h2))) (Steps.cons (Step.root (Root.r15 t2 x1 x2)) (Steps.refl _)))))⟩
      | @rightD _ _ t2 h2 =>
        exact ⟨x0, (Steps.refl _), (Steps.cons (Step.left (T.c (T.d x0 t2) (T.d x0 x1) x2) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h2))) (Steps.cons (Step.left (T.c (T.d x0 t2) (T.d x0 x1) x2) (Step.secondC (T.d x0 t2) x2 (Step.rightD x0 h2))) (Steps.cons (Step.right (T.c (T.d x0 t2) (T.d x0 t2) x2) (Step.secondC (T.d x0 t2) x2 (Step.rightD x0 h2))) (Steps.cons (Step.root (Root.r15 x0 t2 x2)) (Steps.refl _)))))⟩
    | @secondC _ _ t1 _ h1 =>
      cases h1 with
      | root hr =>
        rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
      | @leftD _ t2 _ h2 =>
        exact ⟨t2, (Steps.cons h2 (Steps.refl _)), (Steps.cons (Step.left (T.c (T.d x0 x1) (T.d t2 x1) x2) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h2))) (Steps.cons (Step.left (T.c (T.d x0 x1) (T.d t2 x1) x2) (Step.secondC (T.d t2 x1) x2 (Step.leftD x1 h2))) (Steps.cons (Step.right (T.c (T.d t2 x1) (T.d t2 x1) x2) (Step.firstC (T.d t2 x1) x2 (Step.leftD x1 h2))) (Steps.cons (Step.root (Root.r15 t2 x1 x2)) (Steps.refl _)))))⟩
      | @rightD _ _ t2 h2 =>
        exact ⟨x0, (Steps.refl _), (Steps.cons (Step.left (T.c (T.d x0 x1) (T.d x0 t2) x2) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h2))) (Steps.cons (Step.left (T.c (T.d x0 x1) (T.d x0 t2) x2) (Step.secondC (T.d x0 t2) x2 (Step.rightD x0 h2))) (Steps.cons (Step.right (T.c (T.d x0 t2) (T.d x0 t2) x2) (Step.firstC (T.d x0 t2) x2 (Step.rightD x0 h2))) (Steps.cons (Step.root (Root.r15 x0 t2 x2)) (Steps.refl _)))))⟩
    | @thirdC _ _ _ t1 h1 =>
      exact ⟨x0, (Steps.refl _), (Steps.cons (Step.left (T.c (T.d x0 x1) (T.d x0 x1) t1) (Step.thirdC (T.d x0 x1) (T.d x0 x1) h1)) (Steps.cons (Step.root (Root.r15 x0 x1 t1)) (Steps.refl _)))⟩
end submission.Austin5837

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak16 (x0 : T) (x1 : T) (x2 : T) {u : T} (h : Step (T.m (T.d (T.d x0 x1) x2) (T.c (T.c x2 x0 x1) x0 x1)) u) : Join (T.r (T.c (T.c x2 x0 x1) x0 x1) (T.d x0 x1)) u := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
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
      have e3 := (T.c.inj e1).1
      have e4 := (T.c.inj e1).2.1
      have e5 := (T.c.inj e1).2.2
      have e6 := e3.symm
      subst e6
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
      have e2 := (T.d.inj e0).1
      have e3 := (T.d.inj e0).2
      cases e1
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      have e3 := (T.c.inj e1).1
      have e4 := (T.c.inj e1).2.1
      have e5 := (T.c.inj e1).2.2
      cases e3
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
      have e2 := (T.d.inj e0).1
      have e3 := (T.d.inj e0).2
      have e4 := (T.c.inj e1).1
      have e5 := (T.c.inj e1).2.1
      have e6 := (T.c.inj e1).2.2
      have e7 := e2.symm
      subst e7
      have e8 := e3.symm
      subst e8
      have e9 := (T.c.inj e4).1
      have e10 := (T.c.inj e4).2.1
      have e11 := (T.c.inj e4).2.2
      have cycle := congrArg size e5
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
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := (T.d.inj e0).1
      have e3 := (T.d.inj e0).2
      have e4 := (T.c.inj e1).1
      have e5 := (T.c.inj e1).2.1
      have e6 := (T.c.inj e1).2.2
      have e7 := (T.d.inj e2).1
      have e8 := (T.d.inj e2).2
      have e9 := e3.symm
      subst e9
      have e10 := (T.c.inj e4).1
      have e11 := (T.c.inj e4).2.1
      have e12 := (T.c.inj e4).2.2
      have e13 := e5.symm
      subst e13
      have e14 := e6.symm
      subst e14
      exact ⟨(T.r (T.c (T.c q2 q0 q1) q0 q1) (T.d q0 q1)), (Steps.refl _), (Steps.refl _)⟩
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      have e3 := (T.c.inj e1).1
      have e4 := (T.c.inj e1).2.1
      have e5 := (T.c.inj e1).2.2
      cases e3
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := (T.d.inj e0).1
      have e3 := (T.d.inj e0).2
      have e4 := (T.c.inj e1).1
      have e5 := (T.c.inj e1).2.1
      have e6 := (T.c.inj e1).2.2
      have e7 := e2.symm
      subst e7
      have e8 := e3.symm
      subst e8
      cases e4
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := (T.d.inj e0).1
      have e3 := (T.d.inj e0).2
      have e4 := (T.c.inj e1).1
      have e5 := (T.c.inj e1).2.1
      have e6 := (T.c.inj e1).2.2
      have e7 := (T.d.inj e2).1
      have e8 := (T.d.inj e2).2
      subst e3
      cases e4
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := (T.d.inj e0).1
      have e3 := (T.d.inj e0).2
      have e4 := (T.c.inj e1).1
      have e5 := (T.c.inj e1).2.1
      have e6 := (T.c.inj e1).2.2
      cases e2
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := (T.d.inj e0).1
      have e3 := (T.d.inj e0).2
      have e4 := (T.c.inj e1).1
      have e5 := (T.c.inj e1).2.1
      have e6 := (T.c.inj e1).2.2
      have e7 := (T.d.inj e2).1
      have e8 := (T.d.inj e2).2
      have e9 := e3.symm
      subst e9
      have e10 := (T.c.inj e4).1
      have e11 := (T.c.inj e4).2.1
      have e12 := (T.c.inj e4).2.2
      subst e5
      subst e6
      have cycle := congrArg size e10
      simp only [size] at cycle
      omega
  | @left _ t0 _ h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
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
        rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
      | @leftD _ t2 _ h2 =>
        exact ⟨(T.r (T.c (T.c x2 t2 x1) t2 x1) (T.d t2 x1)), (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.secondC x2 x1 h2))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.secondC (T.c x2 t2 x1) x1 h2)) (Steps.cons (Step.rightR (T.c (T.c x2 t2 x1) t2 x1) (Step.leftD x1 h2)) (Steps.refl _)))), (Steps.cons (Step.right (T.d (T.d t2 x1) x2) (Step.firstC x0 x1 (Step.secondC x2 x1 h2))) (Steps.cons (Step.right (T.d (T.d t2 x1) x2) (Step.secondC (T.c x2 t2 x1) x1 h2)) (Steps.cons (Step.root (Root.r16 t2 x1 x2)) (Steps.refl _))))⟩
      | @rightD _ _ t2 h2 =>
        exact ⟨(T.r (T.c (T.c x2 x0 t2) x0 t2) (T.d x0 t2)), (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.thirdC x2 x0 h2))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.thirdC (T.c x2 x0 t2) x0 h2)) (Steps.cons (Step.rightR (T.c (T.c x2 x0 t2) x0 t2) (Step.rightD x0 h2)) (Steps.refl _)))), (Steps.cons (Step.right (T.d (T.d x0 t2) x2) (Step.firstC x0 x1 (Step.thirdC x2 x0 h2))) (Steps.cons (Step.right (T.d (T.d x0 t2) x2) (Step.thirdC (T.c x2 x0 t2) x0 h2)) (Steps.cons (Step.root (Root.r16 x0 t2 x2)) (Steps.refl _))))⟩
    | @rightD _ _ t1 h1 =>
      exact ⟨(T.r (T.c (T.c t1 x0 x1) x0 x1) (T.d x0 x1)), (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.firstC x0 x1 h1))) (Steps.refl _)), (Steps.cons (Step.right (T.d (T.d x0 x1) t1) (Step.firstC x0 x1 (Step.firstC x0 x1 h1))) (Steps.cons (Step.root (Root.r16 x0 x1 t1)) (Steps.refl _)))⟩
  | @right _ _ t0 h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.c.inj he).1
        have e1 := (T.c.inj he).2.1
        have e2 := (T.c.inj he).2.2
        have e3 := (T.c.inj e0).1
        have e4 := (T.c.inj e0).2.1
        have e5 := (T.c.inj e0).2.2
        have e6 := e1.symm
        subst e6
        have e7 := e2.symm
        subst e7
        subst e3
        have cycle := congrArg size e4
        simp only [size] at cycle
        omega
      · rw [ho]
        have e0 := (T.c.inj he).1
        have e1 := (T.c.inj he).2.1
        have e2 := (T.c.inj he).2.2
        have e3 := e0.symm
        subst e3
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
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
    | @firstC _ t1 _ _ h1 =>
      cases h1 with
      | root hr =>
        rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          have e0 := (T.c.inj he).1
          have e1 := (T.c.inj he).2.1
          have e2 := (T.c.inj he).2.2
          subst e0
          have e3 := e1.symm
          subst e3
          have e4 := e2.symm
          subst e4
          exact ⟨(T.r (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1) (T.d q0 q1)), (Steps.cons (Step.leftR (T.d q0 q1) (Step.firstC q0 q1 (Step.root (Root.r13 q0 q1 q2)))) (Steps.refl _)), (Steps.cons (Step.root (Root.r19 q0 q1 q2)) (Steps.refl _))⟩
        · rw [ho]
          have e0 := (T.c.inj he).1
          have e1 := (T.c.inj he).2.1
          have e2 := (T.c.inj he).2.2
          have e3 := e0.symm
          subst e3
          subst e1
          subst e2
          exact ⟨(T.r (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))), (Steps.cons (Step.leftR (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (Step.firstC (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1) (Step.root (Root.r14 q0 q1 q2)))) (Steps.refl _)), (Steps.cons (Step.root (Root.r21 q0 q1 q2)) (Steps.refl _))⟩
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
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
        exact ⟨(T.r (T.c (T.c t2 x0 x1) x0 x1) (T.d x0 x1)), (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.firstC x0 x1 h2))) (Steps.refl _)), (Steps.cons (Step.left (T.c (T.c t2 x0 x1) x0 x1) (Step.rightD (T.d x0 x1) h2)) (Steps.cons (Step.root (Root.r16 x0 x1 t2)) (Steps.refl _)))⟩
      | @secondC _ _ t2 _ h2 =>
        exact ⟨(T.r (T.c (T.c x2 t2 x1) t2 x1) (T.d t2 x1)), (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.secondC x2 x1 h2))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.secondC (T.c x2 t2 x1) x1 h2)) (Steps.cons (Step.rightR (T.c (T.c x2 t2 x1) t2 x1) (Step.leftD x1 h2)) (Steps.refl _)))), (Steps.cons (Step.left (T.c (T.c x2 t2 x1) x0 x1) (Step.leftD x2 (Step.leftD x1 h2))) (Steps.cons (Step.right (T.d (T.d t2 x1) x2) (Step.secondC (T.c x2 t2 x1) x1 h2)) (Steps.cons (Step.root (Root.r16 t2 x1 x2)) (Steps.refl _))))⟩
      | @thirdC _ _ _ t2 h2 =>
        exact ⟨(T.r (T.c (T.c x2 x0 t2) x0 t2) (T.d x0 t2)), (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.thirdC x2 x0 h2))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.thirdC (T.c x2 x0 t2) x0 h2)) (Steps.cons (Step.rightR (T.c (T.c x2 x0 t2) x0 t2) (Step.rightD x0 h2)) (Steps.refl _)))), (Steps.cons (Step.left (T.c (T.c x2 x0 t2) x0 x1) (Step.leftD x2 (Step.rightD x0 h2))) (Steps.cons (Step.right (T.d (T.d x0 t2) x2) (Step.thirdC (T.c x2 x0 t2) x0 h2)) (Steps.cons (Step.root (Root.r16 x0 t2 x2)) (Steps.refl _))))⟩
    | @secondC _ _ t1 _ h1 =>
      exact ⟨(T.r (T.c (T.c x2 t1 x1) t1 x1) (T.d t1 x1)), (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.secondC x2 x1 h1))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.secondC (T.c x2 t1 x1) x1 h1)) (Steps.cons (Step.rightR (T.c (T.c x2 t1 x1) t1 x1) (Step.leftD x1 h1)) (Steps.refl _)))), (Steps.cons (Step.left (T.c (T.c x2 x0 x1) t1 x1) (Step.leftD x2 (Step.leftD x1 h1))) (Steps.cons (Step.right (T.d (T.d t1 x1) x2) (Step.firstC t1 x1 (Step.secondC x2 x1 h1))) (Steps.cons (Step.root (Root.r16 t1 x1 x2)) (Steps.refl _))))⟩
    | @thirdC _ _ _ t1 h1 =>
      exact ⟨(T.r (T.c (T.c x2 x0 t1) x0 t1) (T.d x0 t1)), (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.thirdC x2 x0 h1))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.thirdC (T.c x2 x0 t1) x0 h1)) (Steps.cons (Step.rightR (T.c (T.c x2 x0 t1) x0 t1) (Step.rightD x0 h1)) (Steps.refl _)))), (Steps.cons (Step.left (T.c (T.c x2 x0 x1) x0 t1) (Step.leftD x2 (Step.rightD x0 h1))) (Steps.cons (Step.right (T.d (T.d x0 t1) x2) (Step.firstC x0 t1 (Step.thirdC x2 x0 h1))) (Steps.cons (Step.root (Root.r16 x0 t1 x2)) (Steps.refl _))))⟩
end submission.Austin5837

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak17 (x0 : T) (x1 : T) (x2 : T) {u : T} (h : Step (T.m x0 (T.c (T.d x0 x1) (T.d x0 x1) x2)) u) : Join (T.r (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2)) u := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
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
      have e3 := (T.c.inj e1).1
      have e4 := (T.c.inj e1).2.1
      have e5 := (T.c.inj e1).2.2
      have e6 := e3.symm
      subst e6
      have e7 := e4.symm
      have cycle := congrArg size e7
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
      cases he
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      have e3 := (T.c.inj e1).1
      have e4 := (T.c.inj e1).2.1
      have e5 := (T.c.inj e1).2.2
      have e6 := e3.symm
      have cycle := congrArg size e6
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
      have e2 := (T.c.inj e1).1
      have e3 := (T.c.inj e1).2.1
      have e4 := (T.c.inj e1).2.2
      cases e2
    · rw [ho]
      cases he
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
      have e2 := (T.c.inj e1).1
      have e3 := (T.c.inj e1).2.1
      have e4 := (T.c.inj e1).2.2
      have e5 := (T.d.inj e2).1
      have e6 := (T.d.inj e2).2
      have e7 := (T.d.inj e3).1
      have e8 := (T.d.inj e3).2
      have e9 := e4.symm
      subst e9
      have e10 := e5.symm
      have cycle := congrArg size e10
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
      have e2 := (T.c.inj e1).1
      have e3 := (T.c.inj e1).2.1
      have e4 := (T.c.inj e1).2.2
      cases e2
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      have e3 := (T.c.inj e1).1
      have e4 := (T.c.inj e1).2.1
      have e5 := (T.c.inj e1).2.2
      have e6 := (T.d.inj e3).1
      have e7 := (T.d.inj e3).2
      have e8 := (T.d.inj e4).1
      have e9 := (T.d.inj e4).2
      have e10 := e5.symm
      subst e10
      have e11 := e7.symm
      subst e11
      exact ⟨(T.r (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2)), (Steps.refl _), (Steps.refl _)⟩
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
      have e2 := (T.c.inj e1).1
      have e3 := (T.c.inj e1).2.1
      have e4 := (T.c.inj e1).2.2
      have e5 := (T.d.inj e2).1
      have e6 := (T.d.inj e2).2
      have e7 := e3.symm
      have cycle := congrArg size e7
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
      have e2 := (T.c.inj e1).1
      have e3 := (T.c.inj e1).2.1
      have e4 := (T.c.inj e1).2.2
      have e5 := (T.d.inj e2).1
      have e6 := (T.d.inj e2).2
      have e7 := e3.symm
      have cycle := congrArg size e7
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
      have e2 := (T.c.inj e1).1
      have e3 := (T.c.inj e1).2.1
      have e4 := (T.c.inj e1).2.2
      cases e2
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      subst e0
      have e2 := (T.c.inj e1).1
      have e3 := (T.c.inj e1).2.1
      have e4 := (T.c.inj e1).2.2
      cases e2
  | @left _ t0 _ h0 =>
    exact ⟨(T.r (T.c (T.d t0 x1) (T.d t0 x1) x2) (T.c (T.d t0 x1) (T.d t0 x1) x2)), (Steps.cons (Step.leftR (T.c (T.d x0 x1) (T.d x0 x1) x2) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h0))) (Steps.cons (Step.leftR (T.c (T.d x0 x1) (T.d x0 x1) x2) (Step.secondC (T.d t0 x1) x2 (Step.leftD x1 h0))) (Steps.cons (Step.rightR (T.c (T.d t0 x1) (T.d t0 x1) x2) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h0))) (Steps.cons (Step.rightR (T.c (T.d t0 x1) (T.d t0 x1) x2) (Step.secondC (T.d t0 x1) x2 (Step.leftD x1 h0))) (Steps.refl _))))), (Steps.cons (Step.right t0 (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h0))) (Steps.cons (Step.right t0 (Step.secondC (T.d t0 x1) x2 (Step.leftD x1 h0))) (Steps.cons (Step.root (Root.r17 t0 x1 x2)) (Steps.refl _))))⟩
  | @right _ _ t0 h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.c.inj he).1
        have e1 := (T.c.inj he).2.1
        have e2 := (T.c.inj he).2.2
        cases e0
      · rw [ho]
        have e0 := (T.c.inj he).1
        have e1 := (T.c.inj he).2.1
        have e2 := (T.c.inj he).2.2
        have e3 := e0.symm
        subst e3
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
    | @firstC _ t1 _ _ h1 =>
      cases h1 with
      | root hr =>
        rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
      | @leftD _ t2 _ h2 =>
        exact ⟨(T.r (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.c (T.d t2 x1) (T.d t2 x1) x2)), (Steps.cons (Step.leftR (T.c (T.d x0 x1) (T.d x0 x1) x2) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h2))) (Steps.cons (Step.leftR (T.c (T.d x0 x1) (T.d x0 x1) x2) (Step.secondC (T.d t2 x1) x2 (Step.leftD x1 h2))) (Steps.cons (Step.rightR (T.c (T.d t2 x1) (T.d t2 x1) x2) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h2))) (Steps.cons (Step.rightR (T.c (T.d t2 x1) (T.d t2 x1) x2) (Step.secondC (T.d t2 x1) x2 (Step.leftD x1 h2))) (Steps.refl _))))), (Steps.cons (Step.left (T.c (T.d t2 x1) (T.d x0 x1) x2) h2) (Steps.cons (Step.right t2 (Step.secondC (T.d t2 x1) x2 (Step.leftD x1 h2))) (Steps.cons (Step.root (Root.r17 t2 x1 x2)) (Steps.refl _))))⟩
      | @rightD _ _ t2 h2 =>
        exact ⟨(T.r (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.c (T.d x0 t2) (T.d x0 t2) x2)), (Steps.cons (Step.leftR (T.c (T.d x0 x1) (T.d x0 x1) x2) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h2))) (Steps.cons (Step.leftR (T.c (T.d x0 x1) (T.d x0 x1) x2) (Step.secondC (T.d x0 t2) x2 (Step.rightD x0 h2))) (Steps.cons (Step.rightR (T.c (T.d x0 t2) (T.d x0 t2) x2) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h2))) (Steps.cons (Step.rightR (T.c (T.d x0 t2) (T.d x0 t2) x2) (Step.secondC (T.d x0 t2) x2 (Step.rightD x0 h2))) (Steps.refl _))))), (Steps.cons (Step.right x0 (Step.secondC (T.d x0 t2) x2 (Step.rightD x0 h2))) (Steps.cons (Step.root (Root.r17 x0 t2 x2)) (Steps.refl _)))⟩
    | @secondC _ _ t1 _ h1 =>
      cases h1 with
      | root hr =>
        rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
      | @leftD _ t2 _ h2 =>
        exact ⟨(T.r (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.c (T.d t2 x1) (T.d t2 x1) x2)), (Steps.cons (Step.leftR (T.c (T.d x0 x1) (T.d x0 x1) x2) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h2))) (Steps.cons (Step.leftR (T.c (T.d x0 x1) (T.d x0 x1) x2) (Step.secondC (T.d t2 x1) x2 (Step.leftD x1 h2))) (Steps.cons (Step.rightR (T.c (T.d t2 x1) (T.d t2 x1) x2) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h2))) (Steps.cons (Step.rightR (T.c (T.d t2 x1) (T.d t2 x1) x2) (Step.secondC (T.d t2 x1) x2 (Step.leftD x1 h2))) (Steps.refl _))))), (Steps.cons (Step.left (T.c (T.d x0 x1) (T.d t2 x1) x2) h2) (Steps.cons (Step.right t2 (Step.firstC (T.d t2 x1) x2 (Step.leftD x1 h2))) (Steps.cons (Step.root (Root.r17 t2 x1 x2)) (Steps.refl _))))⟩
      | @rightD _ _ t2 h2 =>
        exact ⟨(T.r (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.c (T.d x0 t2) (T.d x0 t2) x2)), (Steps.cons (Step.leftR (T.c (T.d x0 x1) (T.d x0 x1) x2) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h2))) (Steps.cons (Step.leftR (T.c (T.d x0 x1) (T.d x0 x1) x2) (Step.secondC (T.d x0 t2) x2 (Step.rightD x0 h2))) (Steps.cons (Step.rightR (T.c (T.d x0 t2) (T.d x0 t2) x2) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h2))) (Steps.cons (Step.rightR (T.c (T.d x0 t2) (T.d x0 t2) x2) (Step.secondC (T.d x0 t2) x2 (Step.rightD x0 h2))) (Steps.refl _))))), (Steps.cons (Step.right x0 (Step.firstC (T.d x0 t2) x2 (Step.rightD x0 h2))) (Steps.cons (Step.root (Root.r17 x0 t2 x2)) (Steps.refl _)))⟩
    | @thirdC _ _ _ t1 h1 =>
      exact ⟨(T.r (T.c (T.d x0 x1) (T.d x0 x1) t1) (T.c (T.d x0 x1) (T.d x0 x1) t1)), (Steps.cons (Step.leftR (T.c (T.d x0 x1) (T.d x0 x1) x2) (Step.thirdC (T.d x0 x1) (T.d x0 x1) h1)) (Steps.cons (Step.rightR (T.c (T.d x0 x1) (T.d x0 x1) t1) (Step.thirdC (T.d x0 x1) (T.d x0 x1) h1)) (Steps.refl _))), (Steps.cons (Step.root (Root.r17 x0 x1 t1)) (Steps.refl _))⟩
end submission.Austin5837

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak18 (x0 : T) (x1 : T) (x2 : T) {u : T} (h : Step (T.m (T.d x0 x1) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) u) : Join (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) u := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
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
      have e3 := (T.c.inj e1).1
      have e4 := (T.c.inj e1).2.1
      have e5 := (T.c.inj e1).2.2
      have e6 := e3.symm
      subst e6
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
      have e2 := (T.d.inj e0).1
      have e3 := (T.d.inj e0).2
      cases e1
    · rw [ho]
      cases he
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      have e3 := (T.c.inj e1).1
      have e4 := (T.c.inj e1).2.1
      have e5 := (T.c.inj e1).2.2
      have e6 := (T.d.inj e3).1
      have e7 := (T.d.inj e3).2
      have e8 := e4.symm
      subst e8
      have e9 := e5.symm
      subst e9
      have e10 := e6.symm
      have cycle := congrArg size e10
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
      have e2 := (T.d.inj e0).1
      have e3 := (T.d.inj e0).2
      have e4 := (T.c.inj e1).1
      have e5 := (T.c.inj e1).2.1
      have e6 := (T.c.inj e1).2.2
      have e7 := e2.symm
      subst e7
      have e8 := e3.symm
      subst e8
      cases e4
    · rw [ho]
      cases he
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
      have e4 := (T.c.inj e1).1
      have e5 := (T.c.inj e1).2.1
      have e6 := (T.c.inj e1).2.2
      subst e2
      have e7 := e3.symm
      subst e7
      cases e4
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := e0.symm
      subst e2
      have e3 := (T.c.inj e1).1
      have e4 := (T.c.inj e1).2.1
      have e5 := (T.c.inj e1).2.2
      have e6 := (T.d.inj e3).1
      have e7 := (T.d.inj e3).2
      have cycle := congrArg size e4
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := (T.d.inj e0).1
      have e3 := (T.d.inj e0).2
      have e4 := (T.c.inj e1).1
      have e5 := (T.c.inj e1).2.1
      have e6 := (T.c.inj e1).2.2
      have e7 := e2.symm
      subst e7
      have e8 := e3.symm
      subst e8
      have e9 := (T.d.inj e4).1
      have e10 := (T.d.inj e4).2
      have e11 := (T.c.inj e9).1
      have e12 := (T.c.inj e9).2.1
      have e13 := (T.c.inj e9).2.2
      have e14 := e13.symm
      subst e14
      exact ⟨(T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)), (Steps.refl _), (Steps.refl _)⟩
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := (T.d.inj e0).1
      have e3 := (T.d.inj e0).2
      have e4 := (T.c.inj e1).1
      have e5 := (T.c.inj e1).2.1
      have e6 := (T.c.inj e1).2.2
      subst e2
      subst e3
      have e7 := (T.d.inj e4).1
      have e8 := (T.d.inj e4).2
      have e9 := e5.symm
      have cycle := congrArg size e9
      simp only [size] at cycle
      omega
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := (T.d.inj e0).1
      have e3 := (T.d.inj e0).2
      have e4 := (T.c.inj e1).1
      have e5 := (T.c.inj e1).2.1
      have e6 := (T.c.inj e1).2.2
      subst e2
      subst e3
      cases e4
    · rw [ho]
      have e0 := (T.m.inj he).1
      have e1 := (T.m.inj he).2
      have e2 := (T.d.inj e0).1
      have e3 := (T.d.inj e0).2
      have e4 := (T.c.inj e1).1
      have e5 := (T.c.inj e1).2.1
      have e6 := (T.c.inj e1).2.2
      subst e2
      have e7 := e3.symm
      subst e7
      cases e4
  | @left _ t0 _ h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
    | @leftD _ t1 _ h1 =>
      exact ⟨(T.d (T.d t1 x1) (T.c (T.d t1 x1) (T.d t1 x1) x2)), (Steps.cons (Step.leftD (T.c (T.d x0 x1) (T.d x0 x1) x2) (Step.leftD x1 h1)) (Steps.cons (Step.rightD (T.d t1 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h1))) (Steps.cons (Step.rightD (T.d t1 x1) (Step.secondC (T.d t1 x1) x2 (Step.leftD x1 h1))) (Steps.refl _)))), (Steps.cons (Step.right (T.d t1 x1) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h1))))) (Steps.cons (Step.right (T.d t1 x1) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.secondC (T.d t1 x1) x2 (Step.leftD x1 h1))))) (Steps.cons (Step.right (T.d t1 x1) (Step.firstC x0 x1 (Step.rightD (T.c (T.d t1 x1) (T.d t1 x1) x2) (Step.leftD x1 h1)))) (Steps.cons (Step.right (T.d t1 x1) (Step.secondC (T.d (T.c (T.d t1 x1) (T.d t1 x1) x2) (T.d t1 x1)) x1 h1)) (Steps.cons (Step.root (Root.r18 t1 x1 x2)) (Steps.refl _))))))⟩
    | @rightD _ _ t1 h1 =>
      exact ⟨(T.d (T.d x0 t1) (T.c (T.d x0 t1) (T.d x0 t1) x2)), (Steps.cons (Step.leftD (T.c (T.d x0 x1) (T.d x0 x1) x2) (Step.rightD x0 h1)) (Steps.cons (Step.rightD (T.d x0 t1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h1))) (Steps.cons (Step.rightD (T.d x0 t1) (Step.secondC (T.d x0 t1) x2 (Step.rightD x0 h1))) (Steps.refl _)))), (Steps.cons (Step.right (T.d x0 t1) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h1))))) (Steps.cons (Step.right (T.d x0 t1) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t1) x2 (Step.rightD x0 h1))))) (Steps.cons (Step.right (T.d x0 t1) (Step.firstC x0 x1 (Step.rightD (T.c (T.d x0 t1) (T.d x0 t1) x2) (Step.rightD x0 h1)))) (Steps.cons (Step.right (T.d x0 t1) (Step.thirdC (T.d (T.c (T.d x0 t1) (T.d x0 t1) x2) (T.d x0 t1)) x0 h1)) (Steps.cons (Step.root (Root.r18 x0 t1 x2)) (Steps.refl _))))))⟩
  | @right _ _ t0 h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        have e0 := (T.c.inj he).1
        have e1 := (T.c.inj he).2.1
        have e2 := (T.c.inj he).2.2
        cases e0
      · rw [ho]
        have e0 := (T.c.inj he).1
        have e1 := (T.c.inj he).2.1
        have e2 := (T.c.inj he).2.2
        have e3 := e0.symm
        subst e3
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
        cases he
      · rw [ho]
        cases he
      · rw [ho]
        cases he
    | @firstC _ t1 _ _ h1 =>
      cases h1 with
      | root hr =>
        rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
        · rw [ho]
          cases he
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
          rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            have e0 := (T.c.inj he).1
            have e1 := (T.c.inj he).2.1
            have e2 := (T.c.inj he).2.2
            cases e0
          · rw [ho]
            have e0 := (T.c.inj he).1
            have e1 := (T.c.inj he).2.1
            have e2 := (T.c.inj he).2.2
            have e3 := e0.symm
            subst e3
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
        | @firstC _ t3 _ _ h3 =>
          cases h3 with
          | root hr =>
            rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
            · rw [ho]
              cases he
            · rw [ho]
              cases he
            · rw [ho]
              cases he
            · rw [ho]
              cases he
            · rw [ho]
              cases he
            · rw [ho]
              cases he
            · rw [ho]
              cases he
            · rw [ho]
              cases he
            · rw [ho]
              cases he
            · rw [ho]
              cases he
            · rw [ho]
              cases he
            · rw [ho]
              cases he
            · rw [ho]
              cases he
            · rw [ho]
              cases he
            · rw [ho]
              cases he
            · rw [ho]
              cases he
            · rw [ho]
              cases he
            · rw [ho]
              cases he
            · rw [ho]
              cases he
            · rw [ho]
              cases he
            · rw [ho]
              cases he
          | @leftD _ t4 _ h4 =>
            exact ⟨(T.d (T.d t4 x1) (T.c (T.d t4 x1) (T.d t4 x1) x2)), (Steps.cons (Step.leftD (T.c (T.d x0 x1) (T.d x0 x1) x2) (Step.leftD x1 h4)) (Steps.cons (Step.rightD (T.d t4 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h4))) (Steps.cons (Step.rightD (T.d t4 x1) (Step.secondC (T.d t4 x1) x2 (Step.leftD x1 h4))) (Steps.refl _)))), (Steps.cons (Step.left (T.c (T.d (T.c (T.d t4 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (Step.leftD x1 h4)) (Steps.cons (Step.right (T.d t4 x1) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.secondC (T.d t4 x1) x2 (Step.leftD x1 h4))))) (Steps.cons (Step.right (T.d t4 x1) (Step.firstC x0 x1 (Step.rightD (T.c (T.d t4 x1) (T.d t4 x1) x2) (Step.leftD x1 h4)))) (Steps.cons (Step.right (T.d t4 x1) (Step.secondC (T.d (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.d t4 x1)) x1 h4)) (Steps.cons (Step.root (Root.r18 t4 x1 x2)) (Steps.refl _))))))⟩
          | @rightD _ _ t4 h4 =>
            exact ⟨(T.d (T.d x0 t4) (T.c (T.d x0 t4) (T.d x0 t4) x2)), (Steps.cons (Step.leftD (T.c (T.d x0 x1) (T.d x0 x1) x2) (Step.rightD x0 h4)) (Steps.cons (Step.rightD (T.d x0 t4) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h4))) (Steps.cons (Step.rightD (T.d x0 t4) (Step.secondC (T.d x0 t4) x2 (Step.rightD x0 h4))) (Steps.refl _)))), (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 t4) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (Step.rightD x0 h4)) (Steps.cons (Step.right (T.d x0 t4) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t4) x2 (Step.rightD x0 h4))))) (Steps.cons (Step.right (T.d x0 t4) (Step.firstC x0 x1 (Step.rightD (T.c (T.d x0 t4) (T.d x0 t4) x2) (Step.rightD x0 h4)))) (Steps.cons (Step.right (T.d x0 t4) (Step.thirdC (T.d (T.c (T.d x0 t4) (T.d x0 t4) x2) (T.d x0 t4)) x0 h4)) (Steps.cons (Step.root (Root.r18 x0 t4 x2)) (Steps.refl _))))))⟩
        | @secondC _ _ t3 _ h3 =>
          cases h3 with
          | root hr =>
            rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
            · rw [ho]
              cases he
            · rw [ho]
              cases he
            · rw [ho]
              cases he
            · rw [ho]
              cases he
            · rw [ho]
              cases he
            · rw [ho]
              cases he
            · rw [ho]
              cases he
            · rw [ho]
              cases he
            · rw [ho]
              cases he
            · rw [ho]
              cases he
            · rw [ho]
              cases he
            · rw [ho]
              cases he
            · rw [ho]
              cases he
            · rw [ho]
              cases he
            · rw [ho]
              cases he
            · rw [ho]
              cases he
            · rw [ho]
              cases he
            · rw [ho]
              cases he
            · rw [ho]
              cases he
            · rw [ho]
              cases he
            · rw [ho]
              cases he
          | @leftD _ t4 _ h4 =>
            exact ⟨(T.d (T.d t4 x1) (T.c (T.d t4 x1) (T.d t4 x1) x2)), (Steps.cons (Step.leftD (T.c (T.d x0 x1) (T.d x0 x1) x2) (Step.leftD x1 h4)) (Steps.cons (Step.rightD (T.d t4 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h4))) (Steps.cons (Step.rightD (T.d t4 x1) (Step.secondC (T.d t4 x1) x2 (Step.leftD x1 h4))) (Steps.refl _)))), (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 x1) (T.d t4 x1) x2) (T.d x0 x1)) x0 x1) (Step.leftD x1 h4)) (Steps.cons (Step.right (T.d t4 x1) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.firstC (T.d t4 x1) x2 (Step.leftD x1 h4))))) (Steps.cons (Step.right (T.d t4 x1) (Step.firstC x0 x1 (Step.rightD (T.c (T.d t4 x1) (T.d t4 x1) x2) (Step.leftD x1 h4)))) (Steps.cons (Step.right (T.d t4 x1) (Step.secondC (T.d (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.d t4 x1)) x1 h4)) (Steps.cons (Step.root (Root.r18 t4 x1 x2)) (Steps.refl _))))))⟩
          | @rightD _ _ t4 h4 =>
            exact ⟨(T.d (T.d x0 t4) (T.c (T.d x0 t4) (T.d x0 t4) x2)), (Steps.cons (Step.leftD (T.c (T.d x0 x1) (T.d x0 x1) x2) (Step.rightD x0 h4)) (Steps.cons (Step.rightD (T.d x0 t4) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h4))) (Steps.cons (Step.rightD (T.d x0 t4) (Step.secondC (T.d x0 t4) x2 (Step.rightD x0 h4))) (Steps.refl _)))), (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 x1) (T.d x0 t4) x2) (T.d x0 x1)) x0 x1) (Step.rightD x0 h4)) (Steps.cons (Step.right (T.d x0 t4) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 t4) x2 (Step.rightD x0 h4))))) (Steps.cons (Step.right (T.d x0 t4) (Step.firstC x0 x1 (Step.rightD (T.c (T.d x0 t4) (T.d x0 t4) x2) (Step.rightD x0 h4)))) (Steps.cons (Step.right (T.d x0 t4) (Step.thirdC (T.d (T.c (T.d x0 t4) (T.d x0 t4) x2) (T.d x0 t4)) x0 h4)) (Steps.cons (Step.root (Root.r18 x0 t4 x2)) (Steps.refl _))))))⟩
        | @thirdC _ _ _ t3 h3 =>
          exact ⟨(T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) t3)), (Steps.cons (Step.rightD (T.d x0 x1) (Step.thirdC (T.d x0 x1) (T.d x0 x1) h3)) (Steps.refl _)), (Steps.cons (Step.root (Root.r18 x0 x1 t3)) (Steps.refl _))⟩
      | @rightD _ _ t2 h2 =>
        cases h2 with
        | root hr =>
          rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
          · rw [ho]
            cases he
        | @leftD _ t3 _ h3 =>
          exact ⟨(T.d (T.d t3 x1) (T.c (T.d t3 x1) (T.d t3 x1) x2)), (Steps.cons (Step.leftD (T.c (T.d x0 x1) (T.d x0 x1) x2) (Step.leftD x1 h3)) (Steps.cons (Step.rightD (T.d t3 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3))) (Steps.cons (Step.rightD (T.d t3 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3))) (Steps.refl _)))), (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d t3 x1)) x0 x1) (Step.leftD x1 h3)) (Steps.cons (Step.right (T.d t3 x1) (Step.firstC x0 x1 (Step.leftD (T.d t3 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3))))) (Steps.cons (Step.right (T.d t3 x1) (Step.firstC x0 x1 (Step.leftD (T.d t3 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3))))) (Steps.cons (Step.right (T.d t3 x1) (Step.secondC (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) x1 h3)) (Steps.cons (Step.root (Root.r18 t3 x1 x2)) (Steps.refl _))))))⟩
        | @rightD _ _ t3 h3 =>
          exact ⟨(T.d (T.d x0 t3) (T.c (T.d x0 t3) (T.d x0 t3) x2)), (Steps.cons (Step.leftD (T.c (T.d x0 x1) (T.d x0 x1) x2) (Step.rightD x0 h3)) (Steps.cons (Step.rightD (T.d x0 t3) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3))) (Steps.cons (Step.rightD (T.d x0 t3) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3))) (Steps.refl _)))), (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 t3)) x0 x1) (Step.rightD x0 h3)) (Steps.cons (Step.right (T.d x0 t3) (Step.firstC x0 x1 (Step.leftD (T.d x0 t3) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3))))) (Steps.cons (Step.right (T.d x0 t3) (Step.firstC x0 x1 (Step.leftD (T.d x0 t3) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3))))) (Steps.cons (Step.right (T.d x0 t3) (Step.thirdC (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) x0 h3)) (Steps.cons (Step.root (Root.r18 x0 t3 x2)) (Steps.refl _))))))⟩
    | @secondC _ _ t1 _ h1 =>
      exact ⟨(T.d (T.d t1 x1) (T.c (T.d t1 x1) (T.d t1 x1) x2)), (Steps.cons (Step.leftD (T.c (T.d x0 x1) (T.d x0 x1) x2) (Step.leftD x1 h1)) (Steps.cons (Step.rightD (T.d t1 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h1))) (Steps.cons (Step.rightD (T.d t1 x1) (Step.secondC (T.d t1 x1) x2 (Step.leftD x1 h1))) (Steps.refl _)))), (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) t1 x1) (Step.leftD x1 h1)) (Steps.cons (Step.right (T.d t1 x1) (Step.firstC t1 x1 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h1))))) (Steps.cons (Step.right (T.d t1 x1) (Step.firstC t1 x1 (Step.leftD (T.d x0 x1) (Step.secondC (T.d t1 x1) x2 (Step.leftD x1 h1))))) (Steps.cons (Step.right (T.d t1 x1) (Step.firstC t1 x1 (Step.rightD (T.c (T.d t1 x1) (T.d t1 x1) x2) (Step.leftD x1 h1)))) (Steps.cons (Step.root (Root.r18 t1 x1 x2)) (Steps.refl _))))))⟩
    | @thirdC _ _ _ t1 h1 =>
      exact ⟨(T.d (T.d x0 t1) (T.c (T.d x0 t1) (T.d x0 t1) x2)), (Steps.cons (Step.leftD (T.c (T.d x0 x1) (T.d x0 x1) x2) (Step.rightD x0 h1)) (Steps.cons (Step.rightD (T.d x0 t1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h1))) (Steps.cons (Step.rightD (T.d x0 t1) (Step.secondC (T.d x0 t1) x2 (Step.rightD x0 h1))) (Steps.refl _)))), (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 t1) (Step.rightD x0 h1)) (Steps.cons (Step.right (T.d x0 t1) (Step.firstC x0 t1 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h1))))) (Steps.cons (Step.right (T.d x0 t1) (Step.firstC x0 t1 (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t1) x2 (Step.rightD x0 h1))))) (Steps.cons (Step.right (T.d x0 t1) (Step.firstC x0 t1 (Step.rightD (T.c (T.d x0 t1) (T.d x0 t1) x2) (Step.rightD x0 h1)))) (Steps.cons (Step.root (Root.r18 x0 t1 x2)) (Steps.refl _))))))⟩
end submission.Austin5837

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak19_root0 {q0 q1 x0 x1 x2 : T} (he : (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) = (T.m (T.m q0 q1) q1)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.r q1 q0) := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  cases e0

theorem peak19_root1 {q0 q1 x0 x1 x2 : T} (he : (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) = (T.m q0 (T.r q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.d q0 q1) := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  have e2 := e0.symm
  subst e2
  cases e1

theorem peak19_root2 {q0 q1 q2 x0 x1 x2 : T} (he : (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) = (T.m q0 (T.d q1 q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.c q0 q1 q2) := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  have e2 := e0.symm
  subst e2
  cases e1

theorem peak19_root3 {q0 q1 q2 x0 x1 x2 : T} (he : (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) = (T.m q0 (T.c q1 q0 q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) q1 := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  have e2 := e0.symm
  subst e2
  have e3 := (T.c.inj e1).1
  have e4 := (T.c.inj e1).2.1
  have e5 := (T.c.inj e1).2.2
  have e6 := e3.symm
  subst e6
  have cycle := congrArg size e4
  simp only [size] at cycle
  omega

theorem peak19_root4 {q0 q1 x0 x1 x2 : T} (he : (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) = (T.m (T.r q0 q1) q0)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.r q0 (T.m q1 q0)) := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  cases e0

theorem peak19_root5 {q0 q1 x0 x1 x2 : T} (he : (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) = (T.m (T.d q0 q1) (T.r q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.r (T.r q0 q1) q0) := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  have e2 := (T.d.inj e0).1
  have e3 := (T.d.inj e0).2
  cases e1

theorem peak19_root6 {q0 q1 q2 x0 x1 x2 : T} (he : (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) = (T.r (T.d q0 q1) q2)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.c (T.c q2 q0 q1) q0 q1) := by
  cases he

theorem peak19_root7 {q0 q1 q2 x0 x1 x2 : T} (he : (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) = (T.m q0 (T.c q0 q1 q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.r (T.c q0 q1 q2) q1) := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  have e2 := e0.symm
  subst e2
  have e3 := (T.c.inj e1).1
  have e4 := (T.c.inj e1).2.1
  have e5 := (T.c.inj e1).2.2
  have e6 := (T.d.inj e3).1
  have e7 := (T.d.inj e3).2
  have e8 := e4.symm
  subst e8
  have e9 := e5.symm
  subst e9
  cases e6

theorem peak19_root8 {q0 q1 x0 x1 x2 : T} (he : (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) = (T.r (T.c q0 q0 q1) q0)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) q0 := by
  cases he

theorem peak19_root9 {q0 q1 x0 x1 x2 : T} (he : (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) = (T.m (T.c q0 q0 q1) q0)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.d (T.c q0 q0 q1) q0) := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  cases e0

theorem peak19_root10 {q0 q1 x0 x1 x2 : T} (he : (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) = (T.m (T.d (T.c q0 q0 q1) q0) q0)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.r q0 (T.c q0 q0 q1)) := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  have e2 := (T.d.inj e0).1
  have e3 := (T.d.inj e0).2
  have e4 := e1.symm
  subst e4
  cases e2

theorem peak19_root11 {q0 q1 q2 x0 x1 x2 : T} (he : (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) = (T.m (T.d q0 q1) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.d (T.d q0 q1) q2) := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  have e2 := (T.d.inj e0).1
  have e3 := (T.d.inj e0).2
  have e4 := (T.c.inj e1).1
  have e5 := (T.c.inj e1).2.1
  have e6 := (T.c.inj e1).2.2
  have e7 := e2.symm
  subst e7
  have e8 := e3.symm
  subst e8
  cases e4

theorem peak19_root12 {q0 q1 q2 x0 x1 x2 : T} (he : (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) = (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) q0 q1)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) := by
  cases he

theorem peak19_root13 {q0 q1 q2 x0 x1 x2 : T} (he : (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) = (T.c q0 (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.c (T.d q0 q1) (T.d q0 q1) q2) := by
  cases he

theorem peak19_root14 {q0 q1 q2 x0 x1 x2 : T} (he : (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) = (T.m (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) q0 := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  cases e0

theorem peak19_root15 {q0 q1 q2 x0 x1 x2 : T} (he : (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) = (T.m (T.d (T.d q0 q1) q2) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.r (T.c (T.c q2 q0 q1) q0 q1) (T.d q0 q1)) := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  have e2 := (T.d.inj e0).1
  have e3 := (T.d.inj e0).2
  have e4 := (T.c.inj e1).1
  have e5 := (T.c.inj e1).2.1
  have e6 := (T.c.inj e1).2.2
  have e7 := (T.d.inj e2).1
  have e8 := (T.d.inj e2).2
  have e9 := e3.symm
  subst e9
  cases e4

theorem peak19_root16 {q0 q1 q2 x0 x1 x2 : T} (he : (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) = (T.m q0 (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.r (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2)) := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  have e2 := e0.symm
  subst e2
  have e3 := (T.c.inj e1).1
  have e4 := (T.c.inj e1).2.1
  have e5 := (T.c.inj e1).2.2
  have e6 := (T.d.inj e3).1
  have e7 := (T.d.inj e3).2
  have cycle := congrArg size e4
  simp only [size] at cycle
  omega

theorem peak19_root17 {q0 q1 q2 x0 x1 x2 : T} (he : (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) = (T.m (T.d q0 q1) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  have e2 := (T.d.inj e0).1
  have e3 := (T.d.inj e0).2
  have e4 := (T.c.inj e1).1
  have e5 := (T.c.inj e1).2.1
  have e6 := (T.c.inj e1).2.2
  have e7 := e2.symm
  subst e7
  have e8 := e3.symm
  subst e8
  have e9 := (T.d.inj e4).1
  have e10 := (T.d.inj e4).2
  have cycle := congrArg size e5
  simp only [size] at cycle
  omega

theorem peak19_root18 {q0 q1 q2 x0 x1 x2 : T} (he : (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) = (T.m (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.r (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1) (T.d q0 q1)) := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  have e2 := (T.d.inj e0).1
  have e3 := (T.d.inj e0).2
  have e4 := (T.c.inj e1).1
  have e5 := (T.c.inj e1).2.1
  have e6 := (T.c.inj e1).2.2
  have e7 := (T.d.inj e2).1
  have e8 := (T.d.inj e2).2
  have e9 := (T.c.inj e3).1
  have e10 := (T.c.inj e3).2.1
  have e11 := (T.c.inj e3).2.2
  have e12 := (T.d.inj e4).1
  have e13 := (T.d.inj e4).2
  have e14 := e5.symm
  subst e14
  have e15 := e6.symm
  subst e15
  have e16 := e11.symm
  subst e16
  exact ⟨(T.r (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1) (T.d q0 q1)), (Steps.refl _), (Steps.refl _)⟩

theorem peak19_root19 {q0 q1 q2 x0 x1 x2 : T} (he : (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) = (T.m (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  have e2 := (T.d.inj e0).1
  have e3 := (T.d.inj e0).2
  have e4 := (T.c.inj e1).1
  have e5 := (T.c.inj e1).2.1
  have e6 := (T.c.inj e1).2.2
  cases e2

theorem peak19_root20 {q0 q1 q2 x0 x1 x2 : T} (he : (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) = (T.m (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.r (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  have e2 := (T.d.inj e0).1
  have e3 := (T.d.inj e0).2
  have e4 := (T.c.inj e1).1
  have e5 := (T.c.inj e1).2.1
  have e6 := (T.c.inj e1).2.2
  have e7 := (T.d.inj e2).1
  have e8 := (T.d.inj e2).2
  have e9 := e3.symm
  subst e9
  cases e4

end submission.Austin5837

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak19_root21 {q0 q1 x0 x1 x2 : T} (he : (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) = (T.m (T.m q0 q1) q1)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.r q1 q0) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root22 {q0 q1 x0 x1 x2 : T} (he : (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) = (T.m q0 (T.r q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d q0 q1) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root23 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) = (T.m q0 (T.d q1 q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.c q0 q1 q2) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root24 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) = (T.m q0 (T.c q1 q0 q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m q1 (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root25 {q0 q1 x0 x1 x2 : T} (he : (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) = (T.m (T.r q0 q1) q0)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.r q0 (T.m q1 q0)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root26 {q0 q1 x0 x1 x2 : T} (he : (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) = (T.m (T.d q0 q1) (T.r q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.r (T.r q0 q1) q0) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root27 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) = (T.r (T.d q0 q1) q2)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.c (T.c q2 q0 q1) q0 q1) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root28 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) = (T.m q0 (T.c q0 q1 q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.r (T.c q0 q1 q2) q1) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root29 {q0 q1 x0 x1 x2 : T} (he : (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) = (T.r (T.c q0 q0 q1) q0)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m q0 (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root30 {q0 q1 x0 x1 x2 : T} (he : (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) = (T.m (T.c q0 q0 q1) q0)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.c q0 q0 q1) q0) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root31 {q0 q1 x0 x1 x2 : T} (he : (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) = (T.m (T.d (T.c q0 q0 q1) q0) q0)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.r q0 (T.c q0 q0 q1)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root32 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) = (T.m (T.d q0 q1) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d q0 q1) q2) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root33 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) = (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) q0 q1)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root34 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) = (T.c q0 (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root35 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) = (T.m (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m q0 (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root36 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) = (T.m (T.d (T.d q0 q1) q2) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.r (T.c (T.c q2 q0 q1) q0 q1) (T.d q0 q1)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root37 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) = (T.m q0 (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.r (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root38 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) = (T.m (T.d q0 q1) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root39 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) = (T.m (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.r (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1) (T.d q0 q1)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root40 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) = (T.m (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root41 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) = (T.m (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.r (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

end submission.Austin5837

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak19_root42 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.m q0 q1) q1)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.r q1 q0) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root43 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.r q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d q0 q1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root44 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.d q1 q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.c q0 q1 q2) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root45 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.c q1 q0 q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d q1 (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root46 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.r q0 q1) q0)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.r q0 (T.m q1 q0)) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root47 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d q0 q1) (T.r q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.r (T.r q0 q1) q0) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root48 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.r (T.d q0 q1) q2)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.c (T.c q2 q0 q1) q0 q1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root49 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.c q0 q1 q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.r (T.c q0 q1 q2) q1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root50 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.r (T.c q0 q0 q1) q0)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d q0 (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root51 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.c q0 q0 q1) q0)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d (T.c q0 q0 q1) q0) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root52 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.c q0 q0 q1) q0) q0)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.r q0 (T.c q0 q0 q1)) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root53 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d q0 q1) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d (T.d q0 q1) q2) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root54 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) q0 q1)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root55 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.c q0 (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root56 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d q0 (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root57 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.d q0 q1) q2) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.r (T.c (T.c q2 q0 q1) q0 q1) (T.d q0 q1)) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root58 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.r (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root59 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d q0 q1) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root60 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.r (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1) (T.d q0 q1)) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root61 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root62 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.r (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

end submission.Austin5837

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak19_root63 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.m q0 q1) q1)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.r q1 q0)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root64 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m q0 (T.r q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.d q0 q1)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root65 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m q0 (T.d q1 q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c q0 q1 q2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root66 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m q0 (T.c q1 q0 q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) q1) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root67 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.r q0 q1) q0)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.r q0 (T.m q1 q0))) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root68 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.d q0 q1) (T.r q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.r (T.r q0 q1) q0)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root69 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.r (T.d q0 q1) q2)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.c q2 q0 q1) q0 q1)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root70 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m q0 (T.c q0 q1 q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.r (T.c q0 q1 q2) q1)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root71 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.r (T.c q0 q0 q1) q0)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) q0) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root72 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.c q0 q0 q1) q0)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.d (T.c q0 q0 q1) q0)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root73 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.d (T.c q0 q0 q1) q0) q0)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.r q0 (T.c q0 q0 q1))) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root74 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.d q0 q1) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.d (T.d q0 q1) q2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root75 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) q0 q1)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  have e0 := (T.c.inj he).1
  have e1 := (T.c.inj he).2.1
  have e2 := (T.c.inj he).2.2
  cases e0

theorem peak19_root76 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.c q0 (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  have e0 := (T.c.inj he).1
  have e1 := (T.c.inj he).2.1
  have e2 := (T.c.inj he).2.2
  have e3 := e0.symm
  subst e3
  cases e1

theorem peak19_root77 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) q0) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root78 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.d (T.d q0 q1) q2) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.r (T.c (T.c q2 q0 q1) q0 q1) (T.d q0 q1))) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root79 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m q0 (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.r (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2))) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root80 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.d q0 q1) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2))) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root81 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.r (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1) (T.d q0 q1))) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root82 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root83 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.r (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

end submission.Austin5837

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak19_root84 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.m q0 q1) q1)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.r q1 q0) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root85 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.r q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d q0 q1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root86 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.d q1 q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.c q0 q1 q2) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root87 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.c q1 q0 q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c q1 (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root88 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.r q0 q1) q0)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.r q0 (T.m q1 q0)) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root89 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d q0 q1) (T.r q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.r (T.r q0 q1) q0) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root90 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.r (T.d q0 q1) q2)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.c (T.c q2 q0 q1) q0 q1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root91 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.c q0 q1 q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.r (T.c q0 q1 q2) q1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root92 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.r (T.c q0 q0 q1) q0)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c q0 (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root93 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.c q0 q0 q1) q0)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d (T.c q0 q0 q1) q0) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root94 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.c q0 q0 q1) q0) q0)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.r q0 (T.c q0 q0 q1)) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root95 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d q0 q1) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d (T.d q0 q1) q2) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root96 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) q0 q1)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root97 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.c q0 (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root98 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c q0 (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root99 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.d q0 q1) q2) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.r (T.c (T.c q2 q0 q1) q0 q1) (T.d q0 q1)) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root100 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.r (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root101 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d q0 q1) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root102 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.r (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1) (T.d q0 q1)) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root103 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root104 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.r (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

end submission.Austin5837

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak19_root105 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.m q0 q1) q1)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.r q1 q0) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root106 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.r q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d q0 q1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root107 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.d q1 q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.c q0 q1 q2) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root108 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.c q1 q0 q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) q1 x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root109 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.r q0 q1) q0)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.r q0 (T.m q1 q0)) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root110 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d q0 q1) (T.r q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.r (T.r q0 q1) q0) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root111 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.r (T.d q0 q1) q2)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.c (T.c q2 q0 q1) q0 q1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root112 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.c q0 q1 q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.r (T.c q0 q1 q2) q1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root113 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.r (T.c q0 q0 q1) q0)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) q0 x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root114 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.c q0 q0 q1) q0)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d (T.c q0 q0 q1) q0) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root115 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.c q0 q0 q1) q0) q0)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.r q0 (T.c q0 q0 q1)) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root116 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d q0 q1) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d (T.d q0 q1) q2) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root117 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) q0 q1)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root118 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.c q0 (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.c (T.d q0 q1) (T.d q0 q1) q2) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root119 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) q0 x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root120 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.d q0 q1) q2) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.r (T.c (T.c q2 q0 q1) q0 q1) (T.d q0 q1)) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root121 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.r (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2)) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root122 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d q0 q1) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root123 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.r (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1) (T.d q0 q1)) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root124 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root125 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.r (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

end submission.Austin5837

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak19_root126 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) = (T.m (T.m q0 q1) q1)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.r q1 q0)) := by
  cases he

theorem peak19_root127 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) = (T.m q0 (T.r q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.d q0 q1)) := by
  cases he

theorem peak19_root128 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) = (T.m q0 (T.d q1 q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c q0 q1 q2)) := by
  cases he

theorem peak19_root129 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) = (T.m q0 (T.c q1 q0 q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) q1) := by
  cases he

theorem peak19_root130 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) = (T.m (T.r q0 q1) q0)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.r q0 (T.m q1 q0))) := by
  cases he

theorem peak19_root131 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) = (T.m (T.d q0 q1) (T.r q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.r (T.r q0 q1) q0)) := by
  cases he

theorem peak19_root132 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) = (T.r (T.d q0 q1) q2)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.c q2 q0 q1) q0 q1)) := by
  cases he

theorem peak19_root133 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) = (T.m q0 (T.c q0 q1 q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.r (T.c q0 q1 q2) q1)) := by
  cases he

theorem peak19_root134 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) = (T.r (T.c q0 q0 q1) q0)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) q0) := by
  cases he

theorem peak19_root135 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) = (T.m (T.c q0 q0 q1) q0)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.d (T.c q0 q0 q1) q0)) := by
  cases he

theorem peak19_root136 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) = (T.m (T.d (T.c q0 q0 q1) q0) q0)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.r q0 (T.c q0 q0 q1))) := by
  cases he

theorem peak19_root137 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) = (T.m (T.d q0 q1) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.d (T.d q0 q1) q2)) := by
  cases he

theorem peak19_root138 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) = (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) q0 q1)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) := by
  have e0 := (T.c.inj he).1
  have e1 := (T.c.inj he).2.1
  have e2 := (T.c.inj he).2.2
  cases e0

theorem peak19_root139 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) = (T.c q0 (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d q0 q1) (T.d q0 q1) q2)) := by
  have e0 := (T.c.inj he).1
  have e1 := (T.c.inj he).2.1
  have e2 := (T.c.inj he).2.2
  have e3 := e0.symm
  subst e3
  have cycle := congrArg size e1
  simp only [size] at cycle
  omega

theorem peak19_root140 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) = (T.m (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) q0) := by
  cases he

theorem peak19_root141 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) = (T.m (T.d (T.d q0 q1) q2) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.r (T.c (T.c q2 q0 q1) q0 q1) (T.d q0 q1))) := by
  cases he

theorem peak19_root142 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) = (T.m q0 (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.r (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2))) := by
  cases he

theorem peak19_root143 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) = (T.m (T.d q0 q1) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2))) := by
  cases he

theorem peak19_root144 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) = (T.m (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.r (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1) (T.d q0 q1))) := by
  cases he

theorem peak19_root145 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) = (T.m (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0)) := by
  cases he

theorem peak19_root146 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) = (T.m (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.r (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) := by
  cases he

end submission.Austin5837

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak19_root147 {q0 q1 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m (T.m q0 q1) q1)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.r q1 q0) x0 x1)) := by
  cases he

theorem peak19_root148 {q0 q1 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m q0 (T.r q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d q0 q1) x0 x1)) := by
  cases he

theorem peak19_root149 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m q0 (T.d q1 q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.c q0 q1 q2) x0 x1)) := by
  cases he

theorem peak19_root150 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m q0 (T.c q1 q0 q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c q1 x0 x1)) := by
  cases he

theorem peak19_root151 {q0 q1 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m (T.r q0 q1) q0)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.r q0 (T.m q1 q0)) x0 x1)) := by
  cases he

theorem peak19_root152 {q0 q1 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m (T.d q0 q1) (T.r q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.r (T.r q0 q1) q0) x0 x1)) := by
  cases he

theorem peak19_root153 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.r (T.d q0 q1) q2)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.c (T.c q2 q0 q1) q0 q1) x0 x1)) := by
  cases he

theorem peak19_root154 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m q0 (T.c q0 q1 q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.r (T.c q0 q1 q2) q1) x0 x1)) := by
  cases he

theorem peak19_root155 {q0 q1 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.r (T.c q0 q0 q1) q0)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c q0 x0 x1)) := by
  cases he

theorem peak19_root156 {q0 q1 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m (T.c q0 q0 q1) q0)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c q0 q0 q1) q0) x0 x1)) := by
  cases he

theorem peak19_root157 {q0 q1 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m (T.d (T.c q0 q0 q1) q0) q0)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.r q0 (T.c q0 q0 q1)) x0 x1)) := by
  cases he

theorem peak19_root158 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m (T.d q0 q1) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.d q0 q1) q2) x0 x1)) := by
  cases he

theorem peak19_root159 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) q0 q1)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) x0 x1)) := by
  cases he

theorem peak19_root160 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.c q0 (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) x0 x1)) := by
  cases he

theorem peak19_root161 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c q0 x0 x1)) := by
  cases he

theorem peak19_root162 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m (T.d (T.d q0 q1) q2) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.r (T.c (T.c q2 q0 q1) q0 q1) (T.d q0 q1)) x0 x1)) := by
  cases he

theorem peak19_root163 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m q0 (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.r (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2)) x0 x1)) := by
  cases he

theorem peak19_root164 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m (T.d q0 q1) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) x0 x1)) := by
  cases he

theorem peak19_root165 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.r (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1) (T.d q0 q1)) x0 x1)) := by
  cases he

theorem peak19_root166 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) x0 x1)) := by
  cases he

theorem peak19_root167 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.r (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) x0 x1)) := by
  cases he

end submission.Austin5837

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak19_root168 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.m q0 q1) q1)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.r q1 q0) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root169 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m q0 (T.r q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.d q0 q1) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root170 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m q0 (T.d q1 q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c q0 q1 q2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root171 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m q0 (T.c q1 q0 q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d q1 (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root172 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.r q0 q1) q0)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.r q0 (T.m q1 q0)) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root173 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.d q0 q1) (T.r q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.r (T.r q0 q1) q0) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root174 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.r (T.d q0 q1) q2)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.c q2 q0 q1) q0 q1) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root175 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m q0 (T.c q0 q1 q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.r (T.c q0 q1 q2) q1) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root176 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.r (T.c q0 q0 q1) q0)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d q0 (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root177 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.c q0 q0 q1) q0)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.d (T.c q0 q0 q1) q0) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root178 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.d (T.c q0 q0 q1) q0) q0)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.r q0 (T.c q0 q0 q1)) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root179 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.d q0 q1) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.d (T.d q0 q1) q2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root180 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) q0 q1)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.d x0 x1)) x0 x1)) := by
  have e0 := (T.c.inj he).1
  have e1 := (T.c.inj he).2.1
  have e2 := (T.c.inj he).2.2
  cases e0

theorem peak19_root181 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.c q0 (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d x0 x1)) x0 x1)) := by
  have e0 := (T.c.inj he).1
  have e1 := (T.c.inj he).2.1
  have e2 := (T.c.inj he).2.2
  have e3 := e0.symm
  subst e3
  cases e1

theorem peak19_root182 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d q0 (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root183 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.d (T.d q0 q1) q2) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.r (T.c (T.c q2 q0 q1) q0 q1) (T.d q0 q1)) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root184 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m q0 (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.r (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root185 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.d q0 q1) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root186 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.r (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1) (T.d q0 q1)) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root187 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root188 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.r (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) (T.d x0 x1)) x0 x1)) := by
  cases he

end submission.Austin5837

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak19_root189 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.m q0 q1) q1)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.r q1 q0) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root190 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.r q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d q0 q1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root191 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.d q1 q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.c q0 q1 q2) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root192 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.c q1 q0 q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c q1 (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root193 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.r q0 q1) q0)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.r q0 (T.m q1 q0)) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root194 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d q0 q1) (T.r q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.r (T.r q0 q1) q0) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root195 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.r (T.d q0 q1) q2)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.c (T.c q2 q0 q1) q0 q1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root196 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.c q0 q1 q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.r (T.c q0 q1 q2) q1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root197 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.r (T.c q0 q0 q1) q0)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c q0 (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root198 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.c q0 q0 q1) q0)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d (T.c q0 q0 q1) q0) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root199 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.c q0 q0 q1) q0) q0)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.r q0 (T.c q0 q0 q1)) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root200 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d q0 q1) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d (T.d q0 q1) q2) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root201 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) q0 q1)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root202 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.c q0 (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root203 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c q0 (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root204 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.d q0 q1) q2) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.r (T.c (T.c q2 q0 q1) q0 q1) (T.d q0 q1)) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root205 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.r (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root206 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d q0 q1) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root207 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.r (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1) (T.d q0 q1)) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root208 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root209 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.r (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

end submission.Austin5837

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak19_root210 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.m q0 q1) q1)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.r q1 q0) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root211 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.r q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d q0 q1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root212 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.d q1 q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.c q0 q1 q2) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root213 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.c q1 q0 q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) q1 x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root214 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.r q0 q1) q0)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.r q0 (T.m q1 q0)) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root215 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d q0 q1) (T.r q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.r (T.r q0 q1) q0) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root216 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.r (T.d q0 q1) q2)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.c (T.c q2 q0 q1) q0 q1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root217 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.c q0 q1 q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.r (T.c q0 q1 q2) q1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root218 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.r (T.c q0 q0 q1) q0)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) q0 x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root219 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.c q0 q0 q1) q0)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d (T.c q0 q0 q1) q0) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root220 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.c q0 q0 q1) q0) q0)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.r q0 (T.c q0 q0 q1)) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root221 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d q0 q1) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d (T.d q0 q1) q2) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root222 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) q0 q1)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root223 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.c q0 (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.c (T.d q0 q1) (T.d q0 q1) q2) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root224 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) q0 x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root225 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.d q0 q1) q2) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.r (T.c (T.c q2 q0 q1) q0 q1) (T.d q0 q1)) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root226 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.r (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2)) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root227 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d q0 q1) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root228 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.r (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1) (T.d q0 q1)) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root229 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root230 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.r (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

end submission.Austin5837

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak19_root231 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.m q0 q1) q1)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.r q1 q0)) x0 x1)) := by
  cases he

theorem peak19_root232 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.r q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d q0 q1)) x0 x1)) := by
  cases he

theorem peak19_root233 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.d q1 q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c q0 q1 q2)) x0 x1)) := by
  cases he

theorem peak19_root234 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.c q1 q0 q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) q1) x0 x1)) := by
  cases he

theorem peak19_root235 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.r q0 q1) q0)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.r q0 (T.m q1 q0))) x0 x1)) := by
  cases he

theorem peak19_root236 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d q0 q1) (T.r q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.r (T.r q0 q1) q0)) x0 x1)) := by
  cases he

theorem peak19_root237 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.r (T.d q0 q1) q2)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.c q2 q0 q1) q0 q1)) x0 x1)) := by
  cases he

theorem peak19_root238 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.c q0 q1 q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.r (T.c q0 q1 q2) q1)) x0 x1)) := by
  cases he

theorem peak19_root239 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.r (T.c q0 q0 q1) q0)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) q0) x0 x1)) := by
  cases he

theorem peak19_root240 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.c q0 q0 q1) q0)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d (T.c q0 q0 q1) q0)) x0 x1)) := by
  cases he

theorem peak19_root241 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.c q0 q0 q1) q0) q0)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.r q0 (T.c q0 q0 q1))) x0 x1)) := by
  cases he

theorem peak19_root242 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d q0 q1) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d (T.d q0 q1) q2)) x0 x1)) := by
  cases he

theorem peak19_root243 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) q0 q1)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) x0 x1)) := by
  cases he

theorem peak19_root244 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.c q0 (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d q0 q1) (T.d q0 q1) q2)) x0 x1)) := by
  cases he

theorem peak19_root245 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) q0) x0 x1)) := by
  cases he

theorem peak19_root246 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.d q0 q1) q2) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.r (T.c (T.c q2 q0 q1) q0 q1) (T.d q0 q1))) x0 x1)) := by
  cases he

theorem peak19_root247 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.r (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2))) x0 x1)) := by
  cases he

theorem peak19_root248 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d q0 q1) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2))) x0 x1)) := by
  cases he

theorem peak19_root249 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.r (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1) (T.d q0 q1))) x0 x1)) := by
  cases he

theorem peak19_root250 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0)) x0 x1)) := by
  cases he

theorem peak19_root251 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.r (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) x0 x1)) := by
  cases he

end submission.Austin5837

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak19 (x0 : T) (x1 : T) (x2 : T) {u : T} (h : Step (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) u) : Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) u := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
    · rw [ho]
      exact peak19_root0 he
    · rw [ho]
      exact peak19_root1 he
    · rw [ho]
      exact peak19_root2 he
    · rw [ho]
      exact peak19_root3 he
    · rw [ho]
      exact peak19_root4 he
    · rw [ho]
      exact peak19_root5 he
    · rw [ho]
      exact peak19_root6 he
    · rw [ho]
      exact peak19_root7 he
    · rw [ho]
      exact peak19_root8 he
    · rw [ho]
      exact peak19_root9 he
    · rw [ho]
      exact peak19_root10 he
    · rw [ho]
      exact peak19_root11 he
    · rw [ho]
      exact peak19_root12 he
    · rw [ho]
      exact peak19_root13 he
    · rw [ho]
      exact peak19_root14 he
    · rw [ho]
      exact peak19_root15 he
    · rw [ho]
      exact peak19_root16 he
    · rw [ho]
      exact peak19_root17 he
    · rw [ho]
      exact peak19_root18 he
    · rw [ho]
      exact peak19_root19 he
    · rw [ho]
      exact peak19_root20 he
  | @left _ t0 _ h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
      · rw [ho]
        exact peak19_root21 he
      · rw [ho]
        exact peak19_root22 he
      · rw [ho]
        exact peak19_root23 he
      · rw [ho]
        exact peak19_root24 he
      · rw [ho]
        exact peak19_root25 he
      · rw [ho]
        exact peak19_root26 he
      · rw [ho]
        exact peak19_root27 he
      · rw [ho]
        exact peak19_root28 he
      · rw [ho]
        exact peak19_root29 he
      · rw [ho]
        exact peak19_root30 he
      · rw [ho]
        exact peak19_root31 he
      · rw [ho]
        exact peak19_root32 he
      · rw [ho]
        exact peak19_root33 he
      · rw [ho]
        exact peak19_root34 he
      · rw [ho]
        exact peak19_root35 he
      · rw [ho]
        exact peak19_root36 he
      · rw [ho]
        exact peak19_root37 he
      · rw [ho]
        exact peak19_root38 he
      · rw [ho]
        exact peak19_root39 he
      · rw [ho]
        exact peak19_root40 he
      · rw [ho]
        exact peak19_root41 he
    | @leftD _ t1 _ h1 =>
      cases h1 with
      | root hr =>
        rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
        · rw [ho]
          exact peak19_root42 he
        · rw [ho]
          exact peak19_root43 he
        · rw [ho]
          exact peak19_root44 he
        · rw [ho]
          exact peak19_root45 he
        · rw [ho]
          exact peak19_root46 he
        · rw [ho]
          exact peak19_root47 he
        · rw [ho]
          exact peak19_root48 he
        · rw [ho]
          exact peak19_root49 he
        · rw [ho]
          exact peak19_root50 he
        · rw [ho]
          exact peak19_root51 he
        · rw [ho]
          exact peak19_root52 he
        · rw [ho]
          exact peak19_root53 he
        · rw [ho]
          exact peak19_root54 he
        · rw [ho]
          exact peak19_root55 he
        · rw [ho]
          exact peak19_root56 he
        · rw [ho]
          exact peak19_root57 he
        · rw [ho]
          exact peak19_root58 he
        · rw [ho]
          exact peak19_root59 he
        · rw [ho]
          exact peak19_root60 he
        · rw [ho]
          exact peak19_root61 he
        · rw [ho]
          exact peak19_root62 he
      | @leftD _ t2 _ h2 =>
        exact ⟨(T.r (T.c (T.d (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.d t2 x1)) t2 x1) (T.d t2 x1)), (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h2))))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.secondC (T.d t2 x1) x2 (Step.leftD x1 h2))))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.rightD (T.c (T.d t2 x1) (T.d t2 x1) x2) (Step.leftD x1 h2)))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.secondC (T.d (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.d t2 x1)) x1 h2)) (Steps.cons (Step.rightR (T.c (T.d (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.d t2 x1)) t2 x1) (Step.leftD x1 h2)) (Steps.refl _)))))), (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (Step.rightD (T.d t2 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h2)))) (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (Step.rightD (T.d t2 x1) (Step.secondC (T.d t2 x1) x2 (Step.leftD x1 h2)))) (Steps.cons (Step.right (T.d (T.d t2 x1) (T.c (T.d t2 x1) (T.d t2 x1) x2)) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h2))))) (Steps.cons (Step.right (T.d (T.d t2 x1) (T.c (T.d t2 x1) (T.d t2 x1) x2)) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.secondC (T.d t2 x1) x2 (Step.leftD x1 h2))))) (Steps.cons (Step.right (T.d (T.d t2 x1) (T.c (T.d t2 x1) (T.d t2 x1) x2)) (Step.firstC x0 x1 (Step.rightD (T.c (T.d t2 x1) (T.d t2 x1) x2) (Step.leftD x1 h2)))) (Steps.cons (Step.right (T.d (T.d t2 x1) (T.c (T.d t2 x1) (T.d t2 x1) x2)) (Step.secondC (T.d (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.d t2 x1)) x1 h2)) (Steps.cons (Step.root (Root.r19 t2 x1 x2)) (Steps.refl _))))))))⟩
      | @rightD _ _ t2 h2 =>
        exact ⟨(T.r (T.c (T.d (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.d x0 t2)) x0 t2) (T.d x0 t2)), (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h2))))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t2) x2 (Step.rightD x0 h2))))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.rightD (T.c (T.d x0 t2) (T.d x0 t2) x2) (Step.rightD x0 h2)))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.thirdC (T.d (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.d x0 t2)) x0 h2)) (Steps.cons (Step.rightR (T.c (T.d (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.d x0 t2)) x0 t2) (Step.rightD x0 h2)) (Steps.refl _)))))), (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (Step.rightD (T.d x0 t2) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h2)))) (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (Step.rightD (T.d x0 t2) (Step.secondC (T.d x0 t2) x2 (Step.rightD x0 h2)))) (Steps.cons (Step.right (T.d (T.d x0 t2) (T.c (T.d x0 t2) (T.d x0 t2) x2)) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h2))))) (Steps.cons (Step.right (T.d (T.d x0 t2) (T.c (T.d x0 t2) (T.d x0 t2) x2)) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t2) x2 (Step.rightD x0 h2))))) (Steps.cons (Step.right (T.d (T.d x0 t2) (T.c (T.d x0 t2) (T.d x0 t2) x2)) (Step.firstC x0 x1 (Step.rightD (T.c (T.d x0 t2) (T.d x0 t2) x2) (Step.rightD x0 h2)))) (Steps.cons (Step.right (T.d (T.d x0 t2) (T.c (T.d x0 t2) (T.d x0 t2) x2)) (Step.thirdC (T.d (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.d x0 t2)) x0 h2)) (Steps.cons (Step.root (Root.r19 x0 t2 x2)) (Steps.refl _))))))))⟩
    | @rightD _ _ t1 h1 =>
      cases h1 with
      | root hr =>
        rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
        · rw [ho]
          exact peak19_root63 he
        · rw [ho]
          exact peak19_root64 he
        · rw [ho]
          exact peak19_root65 he
        · rw [ho]
          exact peak19_root66 he
        · rw [ho]
          exact peak19_root67 he
        · rw [ho]
          exact peak19_root68 he
        · rw [ho]
          exact peak19_root69 he
        · rw [ho]
          exact peak19_root70 he
        · rw [ho]
          exact peak19_root71 he
        · rw [ho]
          exact peak19_root72 he
        · rw [ho]
          exact peak19_root73 he
        · rw [ho]
          exact peak19_root74 he
        · rw [ho]
          exact peak19_root75 he
        · rw [ho]
          exact peak19_root76 he
        · rw [ho]
          exact peak19_root77 he
        · rw [ho]
          exact peak19_root78 he
        · rw [ho]
          exact peak19_root79 he
        · rw [ho]
          exact peak19_root80 he
        · rw [ho]
          exact peak19_root81 he
        · rw [ho]
          exact peak19_root82 he
        · rw [ho]
          exact peak19_root83 he
      | @firstC _ t2 _ _ h2 =>
        cases h2 with
        | root hr =>
          rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
          · rw [ho]
            exact peak19_root84 he
          · rw [ho]
            exact peak19_root85 he
          · rw [ho]
            exact peak19_root86 he
          · rw [ho]
            exact peak19_root87 he
          · rw [ho]
            exact peak19_root88 he
          · rw [ho]
            exact peak19_root89 he
          · rw [ho]
            exact peak19_root90 he
          · rw [ho]
            exact peak19_root91 he
          · rw [ho]
            exact peak19_root92 he
          · rw [ho]
            exact peak19_root93 he
          · rw [ho]
            exact peak19_root94 he
          · rw [ho]
            exact peak19_root95 he
          · rw [ho]
            exact peak19_root96 he
          · rw [ho]
            exact peak19_root97 he
          · rw [ho]
            exact peak19_root98 he
          · rw [ho]
            exact peak19_root99 he
          · rw [ho]
            exact peak19_root100 he
          · rw [ho]
            exact peak19_root101 he
          · rw [ho]
            exact peak19_root102 he
          · rw [ho]
            exact peak19_root103 he
          · rw [ho]
            exact peak19_root104 he
        | @leftD _ t3 _ h3 =>
          exact ⟨(T.r (T.c (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) t3 x1) (T.d t3 x1)), (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3))))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3))))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.rightD (T.c (T.d t3 x1) (T.d t3 x1) x2) (Step.leftD x1 h3)))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.secondC (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) x1 h3)) (Steps.cons (Step.rightR (T.c (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) t3 x1) (Step.leftD x1 h3)) (Steps.refl _)))))), (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (Step.leftD (T.c (T.d t3 x1) (T.d x0 x1) x2) (Step.leftD x1 h3))) (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (Step.rightD (T.d t3 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.right (T.d (T.d t3 x1) (T.c (T.d t3 x1) (T.d t3 x1) x2)) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3))))) (Steps.cons (Step.right (T.d (T.d t3 x1) (T.c (T.d t3 x1) (T.d t3 x1) x2)) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3))))) (Steps.cons (Step.right (T.d (T.d t3 x1) (T.c (T.d t3 x1) (T.d t3 x1) x2)) (Step.firstC x0 x1 (Step.rightD (T.c (T.d t3 x1) (T.d t3 x1) x2) (Step.leftD x1 h3)))) (Steps.cons (Step.right (T.d (T.d t3 x1) (T.c (T.d t3 x1) (T.d t3 x1) x2)) (Step.secondC (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) x1 h3)) (Steps.cons (Step.root (Root.r19 t3 x1 x2)) (Steps.refl _))))))))⟩
        | @rightD _ _ t3 h3 =>
          exact ⟨(T.r (T.c (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) x0 t3) (T.d x0 t3)), (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3))))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3))))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.rightD (T.c (T.d x0 t3) (T.d x0 t3) x2) (Step.rightD x0 h3)))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.thirdC (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) x0 h3)) (Steps.cons (Step.rightR (T.c (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) x0 t3) (Step.rightD x0 h3)) (Steps.refl _)))))), (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (Step.leftD (T.c (T.d x0 t3) (T.d x0 x1) x2) (Step.rightD x0 h3))) (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (Step.rightD (T.d x0 t3) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.d x0 t3) (T.c (T.d x0 t3) (T.d x0 t3) x2)) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3))))) (Steps.cons (Step.right (T.d (T.d x0 t3) (T.c (T.d x0 t3) (T.d x0 t3) x2)) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3))))) (Steps.cons (Step.right (T.d (T.d x0 t3) (T.c (T.d x0 t3) (T.d x0 t3) x2)) (Step.firstC x0 x1 (Step.rightD (T.c (T.d x0 t3) (T.d x0 t3) x2) (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.d x0 t3) (T.c (T.d x0 t3) (T.d x0 t3) x2)) (Step.thirdC (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) x0 h3)) (Steps.cons (Step.root (Root.r19 x0 t3 x2)) (Steps.refl _))))))))⟩
      | @secondC _ _ t2 _ h2 =>
        cases h2 with
        | root hr =>
          rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
          · rw [ho]
            exact peak19_root105 he
          · rw [ho]
            exact peak19_root106 he
          · rw [ho]
            exact peak19_root107 he
          · rw [ho]
            exact peak19_root108 he
          · rw [ho]
            exact peak19_root109 he
          · rw [ho]
            exact peak19_root110 he
          · rw [ho]
            exact peak19_root111 he
          · rw [ho]
            exact peak19_root112 he
          · rw [ho]
            exact peak19_root113 he
          · rw [ho]
            exact peak19_root114 he
          · rw [ho]
            exact peak19_root115 he
          · rw [ho]
            exact peak19_root116 he
          · rw [ho]
            exact peak19_root117 he
          · rw [ho]
            exact peak19_root118 he
          · rw [ho]
            exact peak19_root119 he
          · rw [ho]
            exact peak19_root120 he
          · rw [ho]
            exact peak19_root121 he
          · rw [ho]
            exact peak19_root122 he
          · rw [ho]
            exact peak19_root123 he
          · rw [ho]
            exact peak19_root124 he
          · rw [ho]
            exact peak19_root125 he
        | @leftD _ t3 _ h3 =>
          exact ⟨(T.r (T.c (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) t3 x1) (T.d t3 x1)), (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3))))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3))))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.rightD (T.c (T.d t3 x1) (T.d t3 x1) x2) (Step.leftD x1 h3)))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.secondC (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) x1 h3)) (Steps.cons (Step.rightR (T.c (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) t3 x1) (Step.leftD x1 h3)) (Steps.refl _)))))), (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (Step.leftD (T.c (T.d x0 x1) (T.d t3 x1) x2) (Step.leftD x1 h3))) (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (Step.rightD (T.d t3 x1) (Step.firstC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.right (T.d (T.d t3 x1) (T.c (T.d t3 x1) (T.d t3 x1) x2)) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3))))) (Steps.cons (Step.right (T.d (T.d t3 x1) (T.c (T.d t3 x1) (T.d t3 x1) x2)) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3))))) (Steps.cons (Step.right (T.d (T.d t3 x1) (T.c (T.d t3 x1) (T.d t3 x1) x2)) (Step.firstC x0 x1 (Step.rightD (T.c (T.d t3 x1) (T.d t3 x1) x2) (Step.leftD x1 h3)))) (Steps.cons (Step.right (T.d (T.d t3 x1) (T.c (T.d t3 x1) (T.d t3 x1) x2)) (Step.secondC (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) x1 h3)) (Steps.cons (Step.root (Root.r19 t3 x1 x2)) (Steps.refl _))))))))⟩
        | @rightD _ _ t3 h3 =>
          exact ⟨(T.r (T.c (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) x0 t3) (T.d x0 t3)), (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3))))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3))))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.rightD (T.c (T.d x0 t3) (T.d x0 t3) x2) (Step.rightD x0 h3)))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.thirdC (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) x0 h3)) (Steps.cons (Step.rightR (T.c (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) x0 t3) (Step.rightD x0 h3)) (Steps.refl _)))))), (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (Step.leftD (T.c (T.d x0 x1) (T.d x0 t3) x2) (Step.rightD x0 h3))) (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (Step.rightD (T.d x0 t3) (Step.firstC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.d x0 t3) (T.c (T.d x0 t3) (T.d x0 t3) x2)) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3))))) (Steps.cons (Step.right (T.d (T.d x0 t3) (T.c (T.d x0 t3) (T.d x0 t3) x2)) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3))))) (Steps.cons (Step.right (T.d (T.d x0 t3) (T.c (T.d x0 t3) (T.d x0 t3) x2)) (Step.firstC x0 x1 (Step.rightD (T.c (T.d x0 t3) (T.d x0 t3) x2) (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.d x0 t3) (T.c (T.d x0 t3) (T.d x0 t3) x2)) (Step.thirdC (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) x0 h3)) (Steps.cons (Step.root (Root.r19 x0 t3 x2)) (Steps.refl _))))))))⟩
      | @thirdC _ _ _ t2 h2 =>
        exact ⟨(T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) t2) (T.d x0 x1)) x0 x1) (T.d x0 x1)), (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.thirdC (T.d x0 x1) (T.d x0 x1) h2)))) (Steps.refl _)), (Steps.cons (Step.right (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) t2)) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.thirdC (T.d x0 x1) (T.d x0 x1) h2)))) (Steps.cons (Step.root (Root.r19 x0 x1 t2)) (Steps.refl _)))⟩
  | @right _ _ t0 h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
      · rw [ho]
        exact peak19_root126 he
      · rw [ho]
        exact peak19_root127 he
      · rw [ho]
        exact peak19_root128 he
      · rw [ho]
        exact peak19_root129 he
      · rw [ho]
        exact peak19_root130 he
      · rw [ho]
        exact peak19_root131 he
      · rw [ho]
        exact peak19_root132 he
      · rw [ho]
        exact peak19_root133 he
      · rw [ho]
        exact peak19_root134 he
      · rw [ho]
        exact peak19_root135 he
      · rw [ho]
        exact peak19_root136 he
      · rw [ho]
        exact peak19_root137 he
      · rw [ho]
        exact peak19_root138 he
      · rw [ho]
        exact peak19_root139 he
      · rw [ho]
        exact peak19_root140 he
      · rw [ho]
        exact peak19_root141 he
      · rw [ho]
        exact peak19_root142 he
      · rw [ho]
        exact peak19_root143 he
      · rw [ho]
        exact peak19_root144 he
      · rw [ho]
        exact peak19_root145 he
      · rw [ho]
        exact peak19_root146 he
    | @firstC _ t1 _ _ h1 =>
      cases h1 with
      | root hr =>
        rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
        · rw [ho]
          exact peak19_root147 he
        · rw [ho]
          exact peak19_root148 he
        · rw [ho]
          exact peak19_root149 he
        · rw [ho]
          exact peak19_root150 he
        · rw [ho]
          exact peak19_root151 he
        · rw [ho]
          exact peak19_root152 he
        · rw [ho]
          exact peak19_root153 he
        · rw [ho]
          exact peak19_root154 he
        · rw [ho]
          exact peak19_root155 he
        · rw [ho]
          exact peak19_root156 he
        · rw [ho]
          exact peak19_root157 he
        · rw [ho]
          exact peak19_root158 he
        · rw [ho]
          exact peak19_root159 he
        · rw [ho]
          exact peak19_root160 he
        · rw [ho]
          exact peak19_root161 he
        · rw [ho]
          exact peak19_root162 he
        · rw [ho]
          exact peak19_root163 he
        · rw [ho]
          exact peak19_root164 he
        · rw [ho]
          exact peak19_root165 he
        · rw [ho]
          exact peak19_root166 he
        · rw [ho]
          exact peak19_root167 he
      | @leftD _ t2 _ h2 =>
        cases h2 with
        | root hr =>
          rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
          · rw [ho]
            exact peak19_root168 he
          · rw [ho]
            exact peak19_root169 he
          · rw [ho]
            exact peak19_root170 he
          · rw [ho]
            exact peak19_root171 he
          · rw [ho]
            exact peak19_root172 he
          · rw [ho]
            exact peak19_root173 he
          · rw [ho]
            exact peak19_root174 he
          · rw [ho]
            exact peak19_root175 he
          · rw [ho]
            exact peak19_root176 he
          · rw [ho]
            exact peak19_root177 he
          · rw [ho]
            exact peak19_root178 he
          · rw [ho]
            exact peak19_root179 he
          · rw [ho]
            exact peak19_root180 he
          · rw [ho]
            exact peak19_root181 he
          · rw [ho]
            exact peak19_root182 he
          · rw [ho]
            exact peak19_root183 he
          · rw [ho]
            exact peak19_root184 he
          · rw [ho]
            exact peak19_root185 he
          · rw [ho]
            exact peak19_root186 he
          · rw [ho]
            exact peak19_root187 he
          · rw [ho]
            exact peak19_root188 he
        | @firstC _ t3 _ _ h3 =>
          cases h3 with
          | root hr =>
            rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
            · rw [ho]
              exact peak19_root189 he
            · rw [ho]
              exact peak19_root190 he
            · rw [ho]
              exact peak19_root191 he
            · rw [ho]
              exact peak19_root192 he
            · rw [ho]
              exact peak19_root193 he
            · rw [ho]
              exact peak19_root194 he
            · rw [ho]
              exact peak19_root195 he
            · rw [ho]
              exact peak19_root196 he
            · rw [ho]
              exact peak19_root197 he
            · rw [ho]
              exact peak19_root198 he
            · rw [ho]
              exact peak19_root199 he
            · rw [ho]
              exact peak19_root200 he
            · rw [ho]
              exact peak19_root201 he
            · rw [ho]
              exact peak19_root202 he
            · rw [ho]
              exact peak19_root203 he
            · rw [ho]
              exact peak19_root204 he
            · rw [ho]
              exact peak19_root205 he
            · rw [ho]
              exact peak19_root206 he
            · rw [ho]
              exact peak19_root207 he
            · rw [ho]
              exact peak19_root208 he
            · rw [ho]
              exact peak19_root209 he
          | @leftD _ t4 _ h4 =>
            exact ⟨(T.r (T.c (T.d (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.d t4 x1)) t4 x1) (T.d t4 x1)), (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h4))))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.secondC (T.d t4 x1) x2 (Step.leftD x1 h4))))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.rightD (T.c (T.d t4 x1) (T.d t4 x1) x2) (Step.leftD x1 h4)))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.secondC (T.d (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.d t4 x1)) x1 h4)) (Steps.cons (Step.rightR (T.c (T.d (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.d t4 x1)) t4 x1) (Step.leftD x1 h4)) (Steps.refl _)))))), (Steps.cons (Step.left (T.c (T.d (T.c (T.d t4 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (Step.leftD (T.c (T.d x0 x1) (T.d x0 x1) x2) (Step.leftD x1 h4))) (Steps.cons (Step.left (T.c (T.d (T.c (T.d t4 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (Step.rightD (T.d t4 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h4)))) (Steps.cons (Step.left (T.c (T.d (T.c (T.d t4 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (Step.rightD (T.d t4 x1) (Step.secondC (T.d t4 x1) x2 (Step.leftD x1 h4)))) (Steps.cons (Step.right (T.d (T.d t4 x1) (T.c (T.d t4 x1) (T.d t4 x1) x2)) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.secondC (T.d t4 x1) x2 (Step.leftD x1 h4))))) (Steps.cons (Step.right (T.d (T.d t4 x1) (T.c (T.d t4 x1) (T.d t4 x1) x2)) (Step.firstC x0 x1 (Step.rightD (T.c (T.d t4 x1) (T.d t4 x1) x2) (Step.leftD x1 h4)))) (Steps.cons (Step.right (T.d (T.d t4 x1) (T.c (T.d t4 x1) (T.d t4 x1) x2)) (Step.secondC (T.d (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.d t4 x1)) x1 h4)) (Steps.cons (Step.root (Root.r19 t4 x1 x2)) (Steps.refl _))))))))⟩
          | @rightD _ _ t4 h4 =>
            exact ⟨(T.r (T.c (T.d (T.c (T.d x0 t4) (T.d x0 t4) x2) (T.d x0 t4)) x0 t4) (T.d x0 t4)), (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h4))))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t4) x2 (Step.rightD x0 h4))))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.rightD (T.c (T.d x0 t4) (T.d x0 t4) x2) (Step.rightD x0 h4)))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.thirdC (T.d (T.c (T.d x0 t4) (T.d x0 t4) x2) (T.d x0 t4)) x0 h4)) (Steps.cons (Step.rightR (T.c (T.d (T.c (T.d x0 t4) (T.d x0 t4) x2) (T.d x0 t4)) x0 t4) (Step.rightD x0 h4)) (Steps.refl _)))))), (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 t4) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (Step.leftD (T.c (T.d x0 x1) (T.d x0 x1) x2) (Step.rightD x0 h4))) (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 t4) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (Step.rightD (T.d x0 t4) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h4)))) (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 t4) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (Step.rightD (T.d x0 t4) (Step.secondC (T.d x0 t4) x2 (Step.rightD x0 h4)))) (Steps.cons (Step.right (T.d (T.d x0 t4) (T.c (T.d x0 t4) (T.d x0 t4) x2)) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t4) x2 (Step.rightD x0 h4))))) (Steps.cons (Step.right (T.d (T.d x0 t4) (T.c (T.d x0 t4) (T.d x0 t4) x2)) (Step.firstC x0 x1 (Step.rightD (T.c (T.d x0 t4) (T.d x0 t4) x2) (Step.rightD x0 h4)))) (Steps.cons (Step.right (T.d (T.d x0 t4) (T.c (T.d x0 t4) (T.d x0 t4) x2)) (Step.thirdC (T.d (T.c (T.d x0 t4) (T.d x0 t4) x2) (T.d x0 t4)) x0 h4)) (Steps.cons (Step.root (Root.r19 x0 t4 x2)) (Steps.refl _))))))))⟩
        | @secondC _ _ t3 _ h3 =>
          cases h3 with
          | root hr =>
            rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
            · rw [ho]
              exact peak19_root210 he
            · rw [ho]
              exact peak19_root211 he
            · rw [ho]
              exact peak19_root212 he
            · rw [ho]
              exact peak19_root213 he
            · rw [ho]
              exact peak19_root214 he
            · rw [ho]
              exact peak19_root215 he
            · rw [ho]
              exact peak19_root216 he
            · rw [ho]
              exact peak19_root217 he
            · rw [ho]
              exact peak19_root218 he
            · rw [ho]
              exact peak19_root219 he
            · rw [ho]
              exact peak19_root220 he
            · rw [ho]
              exact peak19_root221 he
            · rw [ho]
              exact peak19_root222 he
            · rw [ho]
              exact peak19_root223 he
            · rw [ho]
              exact peak19_root224 he
            · rw [ho]
              exact peak19_root225 he
            · rw [ho]
              exact peak19_root226 he
            · rw [ho]
              exact peak19_root227 he
            · rw [ho]
              exact peak19_root228 he
            · rw [ho]
              exact peak19_root229 he
            · rw [ho]
              exact peak19_root230 he
          | @leftD _ t4 _ h4 =>
            exact ⟨(T.r (T.c (T.d (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.d t4 x1)) t4 x1) (T.d t4 x1)), (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h4))))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.secondC (T.d t4 x1) x2 (Step.leftD x1 h4))))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.rightD (T.c (T.d t4 x1) (T.d t4 x1) x2) (Step.leftD x1 h4)))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.secondC (T.d (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.d t4 x1)) x1 h4)) (Steps.cons (Step.rightR (T.c (T.d (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.d t4 x1)) t4 x1) (Step.leftD x1 h4)) (Steps.refl _)))))), (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 x1) (T.d t4 x1) x2) (T.d x0 x1)) x0 x1) (Step.leftD (T.c (T.d x0 x1) (T.d x0 x1) x2) (Step.leftD x1 h4))) (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 x1) (T.d t4 x1) x2) (T.d x0 x1)) x0 x1) (Step.rightD (T.d t4 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h4)))) (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 x1) (T.d t4 x1) x2) (T.d x0 x1)) x0 x1) (Step.rightD (T.d t4 x1) (Step.secondC (T.d t4 x1) x2 (Step.leftD x1 h4)))) (Steps.cons (Step.right (T.d (T.d t4 x1) (T.c (T.d t4 x1) (T.d t4 x1) x2)) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.firstC (T.d t4 x1) x2 (Step.leftD x1 h4))))) (Steps.cons (Step.right (T.d (T.d t4 x1) (T.c (T.d t4 x1) (T.d t4 x1) x2)) (Step.firstC x0 x1 (Step.rightD (T.c (T.d t4 x1) (T.d t4 x1) x2) (Step.leftD x1 h4)))) (Steps.cons (Step.right (T.d (T.d t4 x1) (T.c (T.d t4 x1) (T.d t4 x1) x2)) (Step.secondC (T.d (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.d t4 x1)) x1 h4)) (Steps.cons (Step.root (Root.r19 t4 x1 x2)) (Steps.refl _))))))))⟩
          | @rightD _ _ t4 h4 =>
            exact ⟨(T.r (T.c (T.d (T.c (T.d x0 t4) (T.d x0 t4) x2) (T.d x0 t4)) x0 t4) (T.d x0 t4)), (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h4))))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t4) x2 (Step.rightD x0 h4))))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.rightD (T.c (T.d x0 t4) (T.d x0 t4) x2) (Step.rightD x0 h4)))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.thirdC (T.d (T.c (T.d x0 t4) (T.d x0 t4) x2) (T.d x0 t4)) x0 h4)) (Steps.cons (Step.rightR (T.c (T.d (T.c (T.d x0 t4) (T.d x0 t4) x2) (T.d x0 t4)) x0 t4) (Step.rightD x0 h4)) (Steps.refl _)))))), (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 x1) (T.d x0 t4) x2) (T.d x0 x1)) x0 x1) (Step.leftD (T.c (T.d x0 x1) (T.d x0 x1) x2) (Step.rightD x0 h4))) (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 x1) (T.d x0 t4) x2) (T.d x0 x1)) x0 x1) (Step.rightD (T.d x0 t4) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h4)))) (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 x1) (T.d x0 t4) x2) (T.d x0 x1)) x0 x1) (Step.rightD (T.d x0 t4) (Step.secondC (T.d x0 t4) x2 (Step.rightD x0 h4)))) (Steps.cons (Step.right (T.d (T.d x0 t4) (T.c (T.d x0 t4) (T.d x0 t4) x2)) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 t4) x2 (Step.rightD x0 h4))))) (Steps.cons (Step.right (T.d (T.d x0 t4) (T.c (T.d x0 t4) (T.d x0 t4) x2)) (Step.firstC x0 x1 (Step.rightD (T.c (T.d x0 t4) (T.d x0 t4) x2) (Step.rightD x0 h4)))) (Steps.cons (Step.right (T.d (T.d x0 t4) (T.c (T.d x0 t4) (T.d x0 t4) x2)) (Step.thirdC (T.d (T.c (T.d x0 t4) (T.d x0 t4) x2) (T.d x0 t4)) x0 h4)) (Steps.cons (Step.root (Root.r19 x0 t4 x2)) (Steps.refl _))))))))⟩
        | @thirdC _ _ _ t3 h3 =>
          exact ⟨(T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) t3) (T.d x0 x1)) x0 x1) (T.d x0 x1)), (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.thirdC (T.d x0 x1) (T.d x0 x1) h3)))) (Steps.refl _)), (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) t3) (T.d x0 x1)) x0 x1) (Step.rightD (T.d x0 x1) (Step.thirdC (T.d x0 x1) (T.d x0 x1) h3))) (Steps.cons (Step.root (Root.r19 x0 x1 t3)) (Steps.refl _)))⟩
      | @rightD _ _ t2 h2 =>
        cases h2 with
        | root hr =>
          rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
          · rw [ho]
            exact peak19_root231 he
          · rw [ho]
            exact peak19_root232 he
          · rw [ho]
            exact peak19_root233 he
          · rw [ho]
            exact peak19_root234 he
          · rw [ho]
            exact peak19_root235 he
          · rw [ho]
            exact peak19_root236 he
          · rw [ho]
            exact peak19_root237 he
          · rw [ho]
            exact peak19_root238 he
          · rw [ho]
            exact peak19_root239 he
          · rw [ho]
            exact peak19_root240 he
          · rw [ho]
            exact peak19_root241 he
          · rw [ho]
            exact peak19_root242 he
          · rw [ho]
            exact peak19_root243 he
          · rw [ho]
            exact peak19_root244 he
          · rw [ho]
            exact peak19_root245 he
          · rw [ho]
            exact peak19_root246 he
          · rw [ho]
            exact peak19_root247 he
          · rw [ho]
            exact peak19_root248 he
          · rw [ho]
            exact peak19_root249 he
          · rw [ho]
            exact peak19_root250 he
          · rw [ho]
            exact peak19_root251 he
        | @leftD _ t3 _ h3 =>
          exact ⟨(T.r (T.c (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) t3 x1) (T.d t3 x1)), (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3))))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3))))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.rightD (T.c (T.d t3 x1) (T.d t3 x1) x2) (Step.leftD x1 h3)))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.secondC (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) x1 h3)) (Steps.cons (Step.rightR (T.c (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) t3 x1) (Step.leftD x1 h3)) (Steps.refl _)))))), (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d t3 x1)) x0 x1) (Step.leftD (T.c (T.d x0 x1) (T.d x0 x1) x2) (Step.leftD x1 h3))) (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d t3 x1)) x0 x1) (Step.rightD (T.d t3 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d t3 x1)) x0 x1) (Step.rightD (T.d t3 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.right (T.d (T.d t3 x1) (T.c (T.d t3 x1) (T.d t3 x1) x2)) (Step.firstC x0 x1 (Step.leftD (T.d t3 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3))))) (Steps.cons (Step.right (T.d (T.d t3 x1) (T.c (T.d t3 x1) (T.d t3 x1) x2)) (Step.firstC x0 x1 (Step.leftD (T.d t3 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3))))) (Steps.cons (Step.right (T.d (T.d t3 x1) (T.c (T.d t3 x1) (T.d t3 x1) x2)) (Step.secondC (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) x1 h3)) (Steps.cons (Step.root (Root.r19 t3 x1 x2)) (Steps.refl _))))))))⟩
        | @rightD _ _ t3 h3 =>
          exact ⟨(T.r (T.c (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) x0 t3) (T.d x0 t3)), (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3))))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3))))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.rightD (T.c (T.d x0 t3) (T.d x0 t3) x2) (Step.rightD x0 h3)))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.thirdC (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) x0 h3)) (Steps.cons (Step.rightR (T.c (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) x0 t3) (Step.rightD x0 h3)) (Steps.refl _)))))), (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 t3)) x0 x1) (Step.leftD (T.c (T.d x0 x1) (T.d x0 x1) x2) (Step.rightD x0 h3))) (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 t3)) x0 x1) (Step.rightD (T.d x0 t3) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 t3)) x0 x1) (Step.rightD (T.d x0 t3) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.d x0 t3) (T.c (T.d x0 t3) (T.d x0 t3) x2)) (Step.firstC x0 x1 (Step.leftD (T.d x0 t3) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3))))) (Steps.cons (Step.right (T.d (T.d x0 t3) (T.c (T.d x0 t3) (T.d x0 t3) x2)) (Step.firstC x0 x1 (Step.leftD (T.d x0 t3) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3))))) (Steps.cons (Step.right (T.d (T.d x0 t3) (T.c (T.d x0 t3) (T.d x0 t3) x2)) (Step.thirdC (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) x0 h3)) (Steps.cons (Step.root (Root.r19 x0 t3 x2)) (Steps.refl _))))))))⟩
    | @secondC _ _ t1 _ h1 =>
      exact ⟨(T.r (T.c (T.d (T.c (T.d t1 x1) (T.d t1 x1) x2) (T.d t1 x1)) t1 x1) (T.d t1 x1)), (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h1))))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.secondC (T.d t1 x1) x2 (Step.leftD x1 h1))))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.rightD (T.c (T.d t1 x1) (T.d t1 x1) x2) (Step.leftD x1 h1)))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.secondC (T.d (T.c (T.d t1 x1) (T.d t1 x1) x2) (T.d t1 x1)) x1 h1)) (Steps.cons (Step.rightR (T.c (T.d (T.c (T.d t1 x1) (T.d t1 x1) x2) (T.d t1 x1)) t1 x1) (Step.leftD x1 h1)) (Steps.refl _)))))), (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) t1 x1) (Step.leftD (T.c (T.d x0 x1) (T.d x0 x1) x2) (Step.leftD x1 h1))) (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) t1 x1) (Step.rightD (T.d t1 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h1)))) (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) t1 x1) (Step.rightD (T.d t1 x1) (Step.secondC (T.d t1 x1) x2 (Step.leftD x1 h1)))) (Steps.cons (Step.right (T.d (T.d t1 x1) (T.c (T.d t1 x1) (T.d t1 x1) x2)) (Step.firstC t1 x1 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h1))))) (Steps.cons (Step.right (T.d (T.d t1 x1) (T.c (T.d t1 x1) (T.d t1 x1) x2)) (Step.firstC t1 x1 (Step.leftD (T.d x0 x1) (Step.secondC (T.d t1 x1) x2 (Step.leftD x1 h1))))) (Steps.cons (Step.right (T.d (T.d t1 x1) (T.c (T.d t1 x1) (T.d t1 x1) x2)) (Step.firstC t1 x1 (Step.rightD (T.c (T.d t1 x1) (T.d t1 x1) x2) (Step.leftD x1 h1)))) (Steps.cons (Step.root (Root.r19 t1 x1 x2)) (Steps.refl _))))))))⟩
    | @thirdC _ _ _ t1 h1 =>
      exact ⟨(T.r (T.c (T.d (T.c (T.d x0 t1) (T.d x0 t1) x2) (T.d x0 t1)) x0 t1) (T.d x0 t1)), (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h1))))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t1) x2 (Step.rightD x0 h1))))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.firstC x0 x1 (Step.rightD (T.c (T.d x0 t1) (T.d x0 t1) x2) (Step.rightD x0 h1)))) (Steps.cons (Step.leftR (T.d x0 x1) (Step.thirdC (T.d (T.c (T.d x0 t1) (T.d x0 t1) x2) (T.d x0 t1)) x0 h1)) (Steps.cons (Step.rightR (T.c (T.d (T.c (T.d x0 t1) (T.d x0 t1) x2) (T.d x0 t1)) x0 t1) (Step.rightD x0 h1)) (Steps.refl _)))))), (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 t1) (Step.leftD (T.c (T.d x0 x1) (T.d x0 x1) x2) (Step.rightD x0 h1))) (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 t1) (Step.rightD (T.d x0 t1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h1)))) (Steps.cons (Step.left (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 t1) (Step.rightD (T.d x0 t1) (Step.secondC (T.d x0 t1) x2 (Step.rightD x0 h1)))) (Steps.cons (Step.right (T.d (T.d x0 t1) (T.c (T.d x0 t1) (T.d x0 t1) x2)) (Step.firstC x0 t1 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h1))))) (Steps.cons (Step.right (T.d (T.d x0 t1) (T.c (T.d x0 t1) (T.d x0 t1) x2)) (Step.firstC x0 t1 (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t1) x2 (Step.rightD x0 h1))))) (Steps.cons (Step.right (T.d (T.d x0 t1) (T.c (T.d x0 t1) (T.d x0 t1) x2)) (Step.firstC x0 t1 (Step.rightD (T.c (T.d x0 t1) (T.d x0 t1) x2) (Step.rightD x0 h1)))) (Steps.cons (Step.root (Root.r19 x0 t1 x2)) (Steps.refl _))))))))⟩
end submission.Austin5837

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak20_root0 {q0 q1 x0 x1 x2 : T} (he : (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.m (T.m q0 q1) q1)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.r q1 q0) := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  cases e0

theorem peak20_root1 {q0 q1 x0 x1 x2 : T} (he : (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.m q0 (T.r q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.d q0 q1) := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  have e2 := e0.symm
  subst e2
  cases e1

theorem peak20_root2 {q0 q1 q2 x0 x1 x2 : T} (he : (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.m q0 (T.d q1 q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c q0 q1 q2) := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  have e2 := e0.symm
  subst e2
  cases e1

theorem peak20_root3 {q0 q1 q2 x0 x1 x2 : T} (he : (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.m q0 (T.c q1 q0 q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) q1 := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  have e2 := e0.symm
  subst e2
  have e3 := (T.c.inj e1).1
  have e4 := (T.c.inj e1).2.1
  have e5 := (T.c.inj e1).2.2
  have e6 := e3.symm
  subst e6
  cases e4

theorem peak20_root4 {q0 q1 x0 x1 x2 : T} (he : (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.m (T.r q0 q1) q0)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.r q0 (T.m q1 q0)) := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  cases e0

theorem peak20_root5 {q0 q1 x0 x1 x2 : T} (he : (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.m (T.d q0 q1) (T.r q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.r (T.r q0 q1) q0) := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  have e2 := (T.d.inj e0).1
  have e3 := (T.d.inj e0).2
  cases e1

theorem peak20_root6 {q0 q1 q2 x0 x1 x2 : T} (he : (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.r (T.d q0 q1) q2)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c q2 q0 q1) q0 q1) := by
  cases he

theorem peak20_root7 {q0 q1 q2 x0 x1 x2 : T} (he : (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.m q0 (T.c q0 q1 q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.r (T.c q0 q1 q2) q1) := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  have e2 := e0.symm
  subst e2
  have e3 := (T.c.inj e1).1
  have e4 := (T.c.inj e1).2.1
  have e5 := (T.c.inj e1).2.2
  cases e3

theorem peak20_root8 {q0 q1 x0 x1 x2 : T} (he : (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.r (T.c q0 q0 q1) q0)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) q0 := by
  cases he

theorem peak20_root9 {q0 q1 x0 x1 x2 : T} (he : (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.m (T.c q0 q0 q1) q0)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.d (T.c q0 q0 q1) q0) := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  cases e0

theorem peak20_root10 {q0 q1 x0 x1 x2 : T} (he : (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.m (T.d (T.c q0 q0 q1) q0) q0)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.r q0 (T.c q0 q0 q1)) := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  have e2 := (T.d.inj e0).1
  have e3 := (T.d.inj e0).2
  have e4 := e1.symm
  subst e4
  have e5 := (T.c.inj e2).1
  have e6 := (T.c.inj e2).2.1
  have e7 := (T.c.inj e2).2.2
  cases e3

theorem peak20_root11 {q0 q1 q2 x0 x1 x2 : T} (he : (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.m (T.d q0 q1) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.d (T.d q0 q1) q2) := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  have e2 := (T.d.inj e0).1
  have e3 := (T.d.inj e0).2
  have e4 := (T.c.inj e1).1
  have e5 := (T.c.inj e1).2.1
  have e6 := (T.c.inj e1).2.2
  have e7 := e2.symm
  subst e7
  have e8 := e3.symm
  subst e8
  have e9 := (T.c.inj e4).1
  have e10 := (T.c.inj e4).2.1
  have e11 := (T.c.inj e4).2.2
  have e12 := e9.symm
  subst e12
  cases e10

theorem peak20_root12 {q0 q1 q2 x0 x1 x2 : T} (he : (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) q0 q1)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) := by
  cases he

theorem peak20_root13 {q0 q1 q2 x0 x1 x2 : T} (he : (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.c q0 (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.d q0 q1) (T.d q0 q1) q2) := by
  cases he

theorem peak20_root14 {q0 q1 q2 x0 x1 x2 : T} (he : (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.m (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) q0 := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  cases e0

theorem peak20_root15 {q0 q1 q2 x0 x1 x2 : T} (he : (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.m (T.d (T.d q0 q1) q2) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.r (T.c (T.c q2 q0 q1) q0 q1) (T.d q0 q1)) := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  have e2 := (T.d.inj e0).1
  have e3 := (T.d.inj e0).2
  have e4 := (T.c.inj e1).1
  have e5 := (T.c.inj e1).2.1
  have e6 := (T.c.inj e1).2.2
  cases e2

theorem peak20_root16 {q0 q1 q2 x0 x1 x2 : T} (he : (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.m q0 (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.r (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2)) := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  have e2 := e0.symm
  subst e2
  have e3 := (T.c.inj e1).1
  have e4 := (T.c.inj e1).2.1
  have e5 := (T.c.inj e1).2.2
  cases e3

theorem peak20_root17 {q0 q1 q2 x0 x1 x2 : T} (he : (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.m (T.d q0 q1) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  have e2 := (T.d.inj e0).1
  have e3 := (T.d.inj e0).2
  have e4 := (T.c.inj e1).1
  have e5 := (T.c.inj e1).2.1
  have e6 := (T.c.inj e1).2.2
  have e7 := e2.symm
  subst e7
  have e8 := e3.symm
  subst e8
  cases e4

theorem peak20_root18 {q0 q1 q2 x0 x1 x2 : T} (he : (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.m (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.r (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1) (T.d q0 q1)) := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  have e2 := (T.d.inj e0).1
  have e3 := (T.d.inj e0).2
  have e4 := (T.c.inj e1).1
  have e5 := (T.c.inj e1).2.1
  have e6 := (T.c.inj e1).2.2
  cases e2

theorem peak20_root19 {q0 q1 q2 x0 x1 x2 : T} (he : (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.m (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  have e2 := (T.d.inj e0).1
  have e3 := (T.d.inj e0).2
  have e4 := (T.c.inj e1).1
  have e5 := (T.c.inj e1).2.1
  have e6 := (T.c.inj e1).2.2
  have e7 := (T.c.inj e2).1
  have e8 := (T.c.inj e2).2.1
  have e9 := (T.c.inj e2).2.2
  have e10 := (T.d.inj e3).1
  have e11 := (T.d.inj e3).2
  have e12 := (T.c.inj e4).1
  have e13 := (T.c.inj e4).2.1
  have e14 := (T.c.inj e4).2.2
  have e15 := (T.c.inj e5).1
  have e16 := (T.c.inj e5).2.1
  have e17 := (T.c.inj e5).2.2
  have e18 := (T.d.inj e6).1
  have e19 := (T.d.inj e6).2
  have e20 := (T.d.inj e7).1
  have e21 := (T.d.inj e7).2
  have e22 := (T.d.inj e8).1
  have e23 := (T.d.inj e8).2
  have e24 := e9.symm
  subst e24
  have e25 := e10.symm
  subst e25
  have e26 := e11.symm
  subst e26
  exact ⟨(T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0), (Steps.refl _), (Steps.refl _)⟩

theorem peak20_root20 {q0 q1 q2 x0 x1 x2 : T} (he : (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.m (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.r (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  have e2 := (T.d.inj e0).1
  have e3 := (T.d.inj e0).2
  have e4 := (T.c.inj e1).1
  have e5 := (T.c.inj e1).2.1
  have e6 := (T.c.inj e1).2.2
  cases e2

end submission.Austin5837

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak20_root21 {q0 q1 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m (T.m q0 q1) q1)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.r q1 q0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root22 {q0 q1 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m q0 (T.r q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d q0 q1) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root23 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m q0 (T.d q1 q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.c q0 q1 q2) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root24 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m q0 (T.c q1 q0 q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m q1 (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root25 {q0 q1 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m (T.r q0 q1) q0)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.r q0 (T.m q1 q0)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root26 {q0 q1 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m (T.d q0 q1) (T.r q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.r (T.r q0 q1) q0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root27 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.r (T.d q0 q1) q2)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.c (T.c q2 q0 q1) q0 q1) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root28 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m q0 (T.c q0 q1 q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.r (T.c q0 q1 q2) q1) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root29 {q0 q1 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.r (T.c q0 q0 q1) q0)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m q0 (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root30 {q0 q1 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m (T.c q0 q0 q1) q0)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c q0 q0 q1) q0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root31 {q0 q1 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m (T.d (T.c q0 q0 q1) q0) q0)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.r q0 (T.c q0 q0 q1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root32 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m (T.d q0 q1) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.d q0 q1) q2) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root33 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) q0 q1)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root34 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.c q0 (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root35 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m q0 (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root36 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m (T.d (T.d q0 q1) q2) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.r (T.c (T.c q2 q0 q1) q0 q1) (T.d q0 q1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root37 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m q0 (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.r (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root38 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m (T.d q0 q1) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root39 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.r (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1) (T.d q0 q1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root40 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root41 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.r (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

end submission.Austin5837

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak20_root42 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.m q0 q1) q1)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.r q1 q0) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root43 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m q0 (T.r q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.d q0 q1) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root44 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m q0 (T.d q1 q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c q0 q1 q2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root45 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m q0 (T.c q1 q0 q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d q1 (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root46 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.r q0 q1) q0)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.r q0 (T.m q1 q0)) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root47 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.d q0 q1) (T.r q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.r (T.r q0 q1) q0) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root48 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.r (T.d q0 q1) q2)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.c q2 q0 q1) q0 q1) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root49 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m q0 (T.c q0 q1 q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.r (T.c q0 q1 q2) q1) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root50 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.r (T.c q0 q0 q1) q0)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d q0 (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root51 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.c q0 q0 q1) q0)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.d (T.c q0 q0 q1) q0) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root52 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.d (T.c q0 q0 q1) q0) q0)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.r q0 (T.c q0 q0 q1)) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root53 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.d q0 q1) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.d (T.d q0 q1) q2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root54 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) q0 q1)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  have e0 := (T.c.inj he).1
  have e1 := (T.c.inj he).2.1
  have e2 := (T.c.inj he).2.2
  cases e0

theorem peak20_root55 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.c q0 (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  have e0 := (T.c.inj he).1
  have e1 := (T.c.inj he).2.1
  have e2 := (T.c.inj he).2.2
  have e3 := e0.symm
  subst e3
  cases e1

theorem peak20_root56 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d q0 (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root57 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.d (T.d q0 q1) q2) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.r (T.c (T.c q2 q0 q1) q0 q1) (T.d q0 q1)) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root58 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m q0 (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.r (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root59 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.d q0 q1) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root60 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.r (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1) (T.d q0 q1)) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root61 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root62 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.r (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

end submission.Austin5837

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak20_root63 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.m q0 q1) q1)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.r q1 q0) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root64 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.r q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d q0 q1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root65 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.d q1 q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.c q0 q1 q2) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root66 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.c q1 q0 q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c q1 (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root67 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.r q0 q1) q0)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.r q0 (T.m q1 q0)) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root68 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d q0 q1) (T.r q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.r (T.r q0 q1) q0) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root69 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.r (T.d q0 q1) q2)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.c (T.c q2 q0 q1) q0 q1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root70 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.c q0 q1 q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.r (T.c q0 q1 q2) q1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root71 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.r (T.c q0 q0 q1) q0)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c q0 (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root72 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.c q0 q0 q1) q0)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d (T.c q0 q0 q1) q0) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root73 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.c q0 q0 q1) q0) q0)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.r q0 (T.c q0 q0 q1)) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root74 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d q0 q1) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d (T.d q0 q1) q2) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root75 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) q0 q1)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root76 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.c q0 (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root77 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c q0 (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root78 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.d q0 q1) q2) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.r (T.c (T.c q2 q0 q1) q0 q1) (T.d q0 q1)) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root79 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.r (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root80 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d q0 q1) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root81 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.r (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1) (T.d q0 q1)) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root82 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root83 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.r (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

end submission.Austin5837

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak20_root84 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.m q0 q1) q1)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.r q1 q0) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root85 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.r q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d q0 q1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root86 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.d q1 q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.c q0 q1 q2) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root87 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.c q1 q0 q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) q1 x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root88 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.r q0 q1) q0)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.r q0 (T.m q1 q0)) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root89 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d q0 q1) (T.r q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.r (T.r q0 q1) q0) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root90 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.r (T.d q0 q1) q2)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.c (T.c q2 q0 q1) q0 q1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root91 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.c q0 q1 q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.r (T.c q0 q1 q2) q1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root92 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.r (T.c q0 q0 q1) q0)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) q0 x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root93 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.c q0 q0 q1) q0)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d (T.c q0 q0 q1) q0) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root94 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.c q0 q0 q1) q0) q0)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.r q0 (T.c q0 q0 q1)) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root95 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d q0 q1) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d (T.d q0 q1) q2) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root96 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) q0 q1)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root97 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.c q0 (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.c (T.d q0 q1) (T.d q0 q1) q2) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root98 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) q0 x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root99 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.d q0 q1) q2) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.r (T.c (T.c q2 q0 q1) q0 q1) (T.d q0 q1)) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root100 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.r (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2)) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root101 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d q0 q1) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root102 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.r (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1) (T.d q0 q1)) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root103 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root104 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.r (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

end submission.Austin5837

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak20_root105 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.m q0 q1) q1)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.r q1 q0)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root106 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.r q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d q0 q1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root107 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.d q1 q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c q0 q1 q2)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root108 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.c q1 q0 q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) q1) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root109 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.r q0 q1) q0)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.r q0 (T.m q1 q0))) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root110 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d q0 q1) (T.r q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.r (T.r q0 q1) q0)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root111 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.r (T.d q0 q1) q2)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.c q2 q0 q1) q0 q1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root112 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.c q0 q1 q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.r (T.c q0 q1 q2) q1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root113 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.r (T.c q0 q0 q1) q0)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) q0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root114 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.c q0 q0 q1) q0)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d (T.c q0 q0 q1) q0)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root115 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.c q0 q0 q1) q0) q0)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.r q0 (T.c q0 q0 q1))) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root116 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d q0 q1) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d (T.d q0 q1) q2)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root117 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) q0 q1)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root118 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.c q0 (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root119 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) q0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root120 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.d q0 q1) q2) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.r (T.c (T.c q2 q0 q1) q0 q1) (T.d q0 q1))) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root121 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.r (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2))) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root122 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d q0 q1) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2))) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root123 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.r (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1) (T.d q0 q1))) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root124 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root125 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.r (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

end submission.Austin5837

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak20_root126 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m (T.m q0 q1) q1)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.r q1 q0)) := by
  cases he

theorem peak20_root127 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m q0 (T.r q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d q0 q1)) := by
  cases he

theorem peak20_root128 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m q0 (T.d q1 q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c q0 q1 q2)) := by
  cases he

theorem peak20_root129 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m q0 (T.c q1 q0 q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) q1) := by
  cases he

theorem peak20_root130 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m (T.r q0 q1) q0)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.r q0 (T.m q1 q0))) := by
  cases he

theorem peak20_root131 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m (T.d q0 q1) (T.r q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.r (T.r q0 q1) q0)) := by
  cases he

theorem peak20_root132 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.r (T.d q0 q1) q2)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c q2 q0 q1) q0 q1)) := by
  cases he

theorem peak20_root133 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m q0 (T.c q0 q1 q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.r (T.c q0 q1 q2) q1)) := by
  cases he

theorem peak20_root134 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.r (T.c q0 q0 q1) q0)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) q0) := by
  cases he

theorem peak20_root135 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m (T.c q0 q0 q1) q0)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c q0 q0 q1) q0)) := by
  cases he

theorem peak20_root136 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m (T.d (T.c q0 q0 q1) q0) q0)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.r q0 (T.c q0 q0 q1))) := by
  cases he

theorem peak20_root137 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m (T.d q0 q1) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.d q0 q1) q2)) := by
  cases he

theorem peak20_root138 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) q0 q1)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) := by
  have e0 := (T.c.inj he).1
  have e1 := (T.c.inj he).2.1
  have e2 := (T.c.inj he).2.2
  have e3 := (T.c.inj e0).1
  have e4 := (T.c.inj e0).2.1
  have e5 := (T.c.inj e0).2.2
  have e6 := e1.symm
  subst e6
  have e7 := e2.symm
  subst e7
  have e8 := (T.d.inj e3).1
  have e9 := (T.d.inj e3).2
  have e10 := (T.d.inj e4).1
  have e11 := (T.d.inj e4).2
  have e12 := e5.symm
  subst e12
  have cycle := congrArg size e8
  simp only [size] at cycle
  omega

theorem peak20_root139 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.c q0 (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.d q0 q1) (T.d q0 q1) q2)) := by
  have e0 := (T.c.inj he).1
  have e1 := (T.c.inj he).2.1
  have e2 := (T.c.inj he).2.2
  have e3 := e0.symm
  subst e3
  have e4 := (T.c.inj e1).1
  have e5 := (T.c.inj e1).2.1
  have e6 := (T.c.inj e1).2.2
  have e7 := (T.d.inj e2).1
  have e8 := (T.d.inj e2).2
  have e9 := (T.d.inj e4).1
  have e10 := (T.d.inj e4).2
  have e11 := (T.d.inj e5).1
  have e12 := (T.d.inj e5).2
  have e13 := e6.symm
  subst e13
  have cycle := congrArg size e7
  simp only [size] at cycle
  omega

theorem peak20_root140 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) q0) := by
  cases he

theorem peak20_root141 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m (T.d (T.d q0 q1) q2) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.r (T.c (T.c q2 q0 q1) q0 q1) (T.d q0 q1))) := by
  cases he

theorem peak20_root142 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m q0 (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.r (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2))) := by
  cases he

theorem peak20_root143 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m (T.d q0 q1) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2))) := by
  cases he

theorem peak20_root144 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.r (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1) (T.d q0 q1))) := by
  cases he

theorem peak20_root145 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0)) := by
  cases he

theorem peak20_root146 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.r (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) := by
  cases he

end submission.Austin5837

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak20_root147 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.m q0 q1) q1)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.r q1 q0) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root148 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m q0 (T.r q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.d q0 q1) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root149 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m q0 (T.d q1 q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c q0 q1 q2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root150 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m q0 (T.c q1 q0 q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c q1 (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root151 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.r q0 q1) q0)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.r q0 (T.m q1 q0)) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root152 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.d q0 q1) (T.r q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.r (T.r q0 q1) q0) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root153 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.r (T.d q0 q1) q2)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.c q2 q0 q1) q0 q1) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root154 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m q0 (T.c q0 q1 q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.r (T.c q0 q1 q2) q1) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root155 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.r (T.c q0 q0 q1) q0)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c q0 (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root156 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.c q0 q0 q1) q0)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.d (T.c q0 q0 q1) q0) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root157 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.d (T.c q0 q0 q1) q0) q0)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.r q0 (T.c q0 q0 q1)) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root158 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.d q0 q1) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.d (T.d q0 q1) q2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root159 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) q0 q1)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  have e0 := (T.c.inj he).1
  have e1 := (T.c.inj he).2.1
  have e2 := (T.c.inj he).2.2
  cases e0

theorem peak20_root160 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.c q0 (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  have e0 := (T.c.inj he).1
  have e1 := (T.c.inj he).2.1
  have e2 := (T.c.inj he).2.2
  have e3 := e0.symm
  subst e3
  cases e1

theorem peak20_root161 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c q0 (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root162 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.d (T.d q0 q1) q2) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.r (T.c (T.c q2 q0 q1) q0 q1) (T.d q0 q1)) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root163 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m q0 (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.r (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root164 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.d q0 q1) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root165 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.r (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1) (T.d q0 q1)) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root166 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root167 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.r (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

end submission.Austin5837

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak20_root168 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.m q0 q1) q1)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.r q1 q0) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root169 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.r q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d q0 q1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root170 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.d q1 q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.c q0 q1 q2) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root171 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.c q1 q0 q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c q1 (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root172 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.r q0 q1) q0)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.r q0 (T.m q1 q0)) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root173 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d q0 q1) (T.r q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.r (T.r q0 q1) q0) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root174 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.r (T.d q0 q1) q2)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.c (T.c q2 q0 q1) q0 q1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root175 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.c q0 q1 q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.r (T.c q0 q1 q2) q1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root176 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.r (T.c q0 q0 q1) q0)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c q0 (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root177 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.c q0 q0 q1) q0)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d (T.c q0 q0 q1) q0) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root178 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.c q0 q0 q1) q0) q0)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.r q0 (T.c q0 q0 q1)) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root179 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d q0 q1) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d (T.d q0 q1) q2) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root180 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) q0 q1)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root181 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.c q0 (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root182 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c q0 (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root183 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.d q0 q1) q2) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.r (T.c (T.c q2 q0 q1) q0 q1) (T.d q0 q1)) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root184 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.r (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root185 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d q0 q1) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root186 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.r (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1) (T.d q0 q1)) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root187 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root188 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.r (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

end submission.Austin5837

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak20_root189 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.m q0 q1) q1)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.r q1 q0) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root190 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.r q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d q0 q1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root191 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.d q1 q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.c q0 q1 q2) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root192 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.c q1 q0 q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) q1 x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root193 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.r q0 q1) q0)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.r q0 (T.m q1 q0)) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root194 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d q0 q1) (T.r q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.r (T.r q0 q1) q0) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root195 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.r (T.d q0 q1) q2)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.c (T.c q2 q0 q1) q0 q1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root196 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.c q0 q1 q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.r (T.c q0 q1 q2) q1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root197 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.r (T.c q0 q0 q1) q0)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) q0 x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root198 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.c q0 q0 q1) q0)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d (T.c q0 q0 q1) q0) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root199 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.c q0 q0 q1) q0) q0)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.r q0 (T.c q0 q0 q1)) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root200 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d q0 q1) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d (T.d q0 q1) q2) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root201 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) q0 q1)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root202 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.c q0 (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.c (T.d q0 q1) (T.d q0 q1) q2) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root203 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) q0 x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root204 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.d q0 q1) q2) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.r (T.c (T.c q2 q0 q1) q0 q1) (T.d q0 q1)) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root205 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.r (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2)) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root206 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d q0 q1) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root207 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.r (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1) (T.d q0 q1)) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root208 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root209 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.r (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

end submission.Austin5837

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak20_root210 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.m q0 q1) q1)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.r q1 q0) (T.d x0 x1))) := by
  cases he

theorem peak20_root211 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m q0 (T.r q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d q0 q1) (T.d x0 x1))) := by
  cases he

theorem peak20_root212 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m q0 (T.d q1 q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c q0 q1 q2) (T.d x0 x1))) := by
  cases he

theorem peak20_root213 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m q0 (T.c q1 q0 q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) q1 (T.d x0 x1))) := by
  cases he

theorem peak20_root214 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.r q0 q1) q0)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.r q0 (T.m q1 q0)) (T.d x0 x1))) := by
  cases he

theorem peak20_root215 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.d q0 q1) (T.r q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.r (T.r q0 q1) q0) (T.d x0 x1))) := by
  cases he

theorem peak20_root216 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.r (T.d q0 q1) q2)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.c q2 q0 q1) q0 q1) (T.d x0 x1))) := by
  cases he

theorem peak20_root217 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m q0 (T.c q0 q1 q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.r (T.c q0 q1 q2) q1) (T.d x0 x1))) := by
  cases he

theorem peak20_root218 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.r (T.c q0 q0 q1) q0)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) q0 (T.d x0 x1))) := by
  cases he

theorem peak20_root219 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.c q0 q0 q1) q0)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d (T.c q0 q0 q1) q0) (T.d x0 x1))) := by
  cases he

theorem peak20_root220 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.d (T.c q0 q0 q1) q0) q0)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.r q0 (T.c q0 q0 q1)) (T.d x0 x1))) := by
  cases he

theorem peak20_root221 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.d q0 q1) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d (T.d q0 q1) q2) (T.d x0 x1))) := by
  cases he

theorem peak20_root222 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) q0 q1)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.d x0 x1))) := by
  have e0 := (T.c.inj he).1
  have e1 := (T.c.inj he).2.1
  have e2 := (T.c.inj he).2.2
  cases e0

theorem peak20_root223 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.c q0 (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d x0 x1))) := by
  have e0 := (T.c.inj he).1
  have e1 := (T.c.inj he).2.1
  have e2 := (T.c.inj he).2.2
  have e3 := e0.symm
  subst e3
  cases e1

theorem peak20_root224 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) q0 (T.d x0 x1))) := by
  cases he

theorem peak20_root225 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.d (T.d q0 q1) q2) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.r (T.c (T.c q2 q0 q1) q0 q1) (T.d q0 q1)) (T.d x0 x1))) := by
  cases he

theorem peak20_root226 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m q0 (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.r (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.d x0 x1))) := by
  cases he

theorem peak20_root227 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.d q0 q1) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.d x0 x1))) := by
  cases he

theorem peak20_root228 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.r (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1) (T.d q0 q1)) (T.d x0 x1))) := by
  cases he

theorem peak20_root229 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) (T.d x0 x1))) := by
  cases he

theorem peak20_root230 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.r (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) (T.d x0 x1))) := by
  cases he

end submission.Austin5837

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak20_root231 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.m q0 q1) q1)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.r q1 q0) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root232 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.r q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d q0 q1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root233 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.d q1 q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.c q0 q1 q2) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root234 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.c q1 q0 q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c q1 (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root235 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.r q0 q1) q0)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.r q0 (T.m q1 q0)) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root236 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d q0 q1) (T.r q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.r (T.r q0 q1) q0) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root237 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.r (T.d q0 q1) q2)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.c (T.c q2 q0 q1) q0 q1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root238 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.c q0 q1 q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.r (T.c q0 q1 q2) q1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root239 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.r (T.c q0 q0 q1) q0)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c q0 (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root240 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.c q0 q0 q1) q0)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d (T.c q0 q0 q1) q0) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root241 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.c q0 q0 q1) q0) q0)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.r q0 (T.c q0 q0 q1)) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root242 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d q0 q1) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d (T.d q0 q1) q2) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root243 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) q0 q1)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root244 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.c q0 (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root245 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c q0 (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root246 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.d q0 q1) q2) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.r (T.c (T.c q2 q0 q1) q0 q1) (T.d q0 q1)) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root247 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.r (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root248 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d q0 q1) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root249 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.r (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1) (T.d q0 q1)) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root250 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root251 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.r (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

end submission.Austin5837

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak20_root252 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.m q0 q1) q1)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.r q1 q0) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root253 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.r q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d q0 q1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root254 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.d q1 q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.c q0 q1 q2) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root255 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.c q1 q0 q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) q1 x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root256 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.r q0 q1) q0)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.r q0 (T.m q1 q0)) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root257 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d q0 q1) (T.r q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.r (T.r q0 q1) q0) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root258 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.r (T.d q0 q1) q2)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.c (T.c q2 q0 q1) q0 q1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root259 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.c q0 q1 q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.r (T.c q0 q1 q2) q1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root260 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.r (T.c q0 q0 q1) q0)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) q0 x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root261 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.c q0 q0 q1) q0)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d (T.c q0 q0 q1) q0) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root262 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.c q0 q0 q1) q0) q0)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.r q0 (T.c q0 q0 q1)) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root263 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d q0 q1) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d (T.d q0 q1) q2) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root264 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) q0 q1)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root265 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.c q0 (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.c (T.d q0 q1) (T.d q0 q1) q2) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root266 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) q0 x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root267 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.d q0 q1) q2) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.r (T.c (T.c q2 q0 q1) q0 q1) (T.d q0 q1)) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root268 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.r (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2)) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root269 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d q0 q1) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root270 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.r (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1) (T.d q0 q1)) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root271 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root272 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.r (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) x2) (T.d x0 x1))) := by
  cases he

end submission.Austin5837

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak20_root273 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.m q0 q1) q1)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.r q1 q0))) := by
  cases he

theorem peak20_root274 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.r q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d q0 q1))) := by
  cases he

theorem peak20_root275 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.d q1 q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c q0 q1 q2))) := by
  cases he

theorem peak20_root276 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.c q1 q0 q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) q1)) := by
  cases he

theorem peak20_root277 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.r q0 q1) q0)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.r q0 (T.m q1 q0)))) := by
  cases he

theorem peak20_root278 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d q0 q1) (T.r q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.r (T.r q0 q1) q0))) := by
  cases he

theorem peak20_root279 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.r (T.d q0 q1) q2)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.c q2 q0 q1) q0 q1))) := by
  cases he

theorem peak20_root280 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.c q0 q1 q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.r (T.c q0 q1 q2) q1))) := by
  cases he

theorem peak20_root281 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.r (T.c q0 q0 q1) q0)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) q0)) := by
  cases he

theorem peak20_root282 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.c q0 q0 q1) q0)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d (T.c q0 q0 q1) q0))) := by
  cases he

theorem peak20_root283 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.c q0 q0 q1) q0) q0)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.r q0 (T.c q0 q0 q1)))) := by
  cases he

theorem peak20_root284 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d q0 q1) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d (T.d q0 q1) q2))) := by
  cases he

theorem peak20_root285 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) q0 q1)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) := by
  cases he

theorem peak20_root286 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.c q0 (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d q0 q1) (T.d q0 q1) q2))) := by
  cases he

theorem peak20_root287 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) q0)) := by
  cases he

theorem peak20_root288 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.d q0 q1) q2) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.r (T.c (T.c q2 q0 q1) q0 q1) (T.d q0 q1)))) := by
  cases he

theorem peak20_root289 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.r (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2)))) := by
  cases he

theorem peak20_root290 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d q0 q1) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)))) := by
  cases he

theorem peak20_root291 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.r (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1) (T.d q0 q1)))) := by
  cases he

theorem peak20_root292 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0))) := by
  cases he

theorem peak20_root293 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.r (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))))) := by
  cases he

end submission.Austin5837

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak20 (x0 : T) (x1 : T) (x2 : T) {u : T} (h : Step (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) u) : Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) u := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
    · rw [ho]
      exact peak20_root0 he
    · rw [ho]
      exact peak20_root1 he
    · rw [ho]
      exact peak20_root2 he
    · rw [ho]
      exact peak20_root3 he
    · rw [ho]
      exact peak20_root4 he
    · rw [ho]
      exact peak20_root5 he
    · rw [ho]
      exact peak20_root6 he
    · rw [ho]
      exact peak20_root7 he
    · rw [ho]
      exact peak20_root8 he
    · rw [ho]
      exact peak20_root9 he
    · rw [ho]
      exact peak20_root10 he
    · rw [ho]
      exact peak20_root11 he
    · rw [ho]
      exact peak20_root12 he
    · rw [ho]
      exact peak20_root13 he
    · rw [ho]
      exact peak20_root14 he
    · rw [ho]
      exact peak20_root15 he
    · rw [ho]
      exact peak20_root16 he
    · rw [ho]
      exact peak20_root17 he
    · rw [ho]
      exact peak20_root18 he
    · rw [ho]
      exact peak20_root19 he
    · rw [ho]
      exact peak20_root20 he
  | @left _ t0 _ h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
      · rw [ho]
        exact peak20_root21 he
      · rw [ho]
        exact peak20_root22 he
      · rw [ho]
        exact peak20_root23 he
      · rw [ho]
        exact peak20_root24 he
      · rw [ho]
        exact peak20_root25 he
      · rw [ho]
        exact peak20_root26 he
      · rw [ho]
        exact peak20_root27 he
      · rw [ho]
        exact peak20_root28 he
      · rw [ho]
        exact peak20_root29 he
      · rw [ho]
        exact peak20_root30 he
      · rw [ho]
        exact peak20_root31 he
      · rw [ho]
        exact peak20_root32 he
      · rw [ho]
        exact peak20_root33 he
      · rw [ho]
        exact peak20_root34 he
      · rw [ho]
        exact peak20_root35 he
      · rw [ho]
        exact peak20_root36 he
      · rw [ho]
        exact peak20_root37 he
      · rw [ho]
        exact peak20_root38 he
      · rw [ho]
        exact peak20_root39 he
      · rw [ho]
        exact peak20_root40 he
      · rw [ho]
        exact peak20_root41 he
    | @leftD _ t1 _ h1 =>
      cases h1 with
      | root hr =>
        rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
        · rw [ho]
          exact peak20_root42 he
        · rw [ho]
          exact peak20_root43 he
        · rw [ho]
          exact peak20_root44 he
        · rw [ho]
          exact peak20_root45 he
        · rw [ho]
          exact peak20_root46 he
        · rw [ho]
          exact peak20_root47 he
        · rw [ho]
          exact peak20_root48 he
        · rw [ho]
          exact peak20_root49 he
        · rw [ho]
          exact peak20_root50 he
        · rw [ho]
          exact peak20_root51 he
        · rw [ho]
          exact peak20_root52 he
        · rw [ho]
          exact peak20_root53 he
        · rw [ho]
          exact peak20_root54 he
        · rw [ho]
          exact peak20_root55 he
        · rw [ho]
          exact peak20_root56 he
        · rw [ho]
          exact peak20_root57 he
        · rw [ho]
          exact peak20_root58 he
        · rw [ho]
          exact peak20_root59 he
        · rw [ho]
          exact peak20_root60 he
        · rw [ho]
          exact peak20_root61 he
        · rw [ho]
          exact peak20_root62 he
      | @firstC _ t2 _ _ h2 =>
        cases h2 with
        | root hr =>
          rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
          · rw [ho]
            exact peak20_root63 he
          · rw [ho]
            exact peak20_root64 he
          · rw [ho]
            exact peak20_root65 he
          · rw [ho]
            exact peak20_root66 he
          · rw [ho]
            exact peak20_root67 he
          · rw [ho]
            exact peak20_root68 he
          · rw [ho]
            exact peak20_root69 he
          · rw [ho]
            exact peak20_root70 he
          · rw [ho]
            exact peak20_root71 he
          · rw [ho]
            exact peak20_root72 he
          · rw [ho]
            exact peak20_root73 he
          · rw [ho]
            exact peak20_root74 he
          · rw [ho]
            exact peak20_root75 he
          · rw [ho]
            exact peak20_root76 he
          · rw [ho]
            exact peak20_root77 he
          · rw [ho]
            exact peak20_root78 he
          · rw [ho]
            exact peak20_root79 he
          · rw [ho]
            exact peak20_root80 he
          · rw [ho]
            exact peak20_root81 he
          · rw [ho]
            exact peak20_root82 he
          · rw [ho]
            exact peak20_root83 he
        | @leftD _ t3 _ h3 =>
          exact ⟨(T.d (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) t3), (Steps.cons (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.leftD x0 (Step.rightD (T.c (T.d t3 x1) (T.d t3 x1) x2) (Step.leftD x1 h3))) (Steps.cons (Step.rightD (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) h3) (Steps.refl _))))), (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.rightD (T.c (T.d t3 x1) (T.d t3 x1) x2) (Step.leftD x1 h3))) (Steps.cons (Step.right (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.right (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.right (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (Step.secondC (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.right (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (Step.secondC (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.right (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (Step.thirdC (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.c (T.d t3 x1) (T.d t3 x1) x2) (Step.leftD x1 h3))) (Steps.cons (Step.root (Root.r20 t3 x1 x2)) (Steps.refl _)))))))))⟩
        | @rightD _ _ t3 h3 =>
          exact ⟨(T.d (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) x0), (Steps.cons (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.leftD x0 (Step.rightD (T.c (T.d x0 t3) (T.d x0 t3) x2) (Step.rightD x0 h3))) (Steps.refl _)))), (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.rightD (T.c (T.d x0 t3) (T.d x0 t3) x2) (Step.rightD x0 h3))) (Steps.cons (Step.right (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (Step.secondC (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (Step.secondC (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (Step.thirdC (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.c (T.d x0 t3) (T.d x0 t3) x2) (Step.rightD x0 h3))) (Steps.cons (Step.root (Root.r20 x0 t3 x2)) (Steps.refl _)))))))))⟩
      | @secondC _ _ t2 _ h2 =>
        cases h2 with
        | root hr =>
          rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
          · rw [ho]
            exact peak20_root84 he
          · rw [ho]
            exact peak20_root85 he
          · rw [ho]
            exact peak20_root86 he
          · rw [ho]
            exact peak20_root87 he
          · rw [ho]
            exact peak20_root88 he
          · rw [ho]
            exact peak20_root89 he
          · rw [ho]
            exact peak20_root90 he
          · rw [ho]
            exact peak20_root91 he
          · rw [ho]
            exact peak20_root92 he
          · rw [ho]
            exact peak20_root93 he
          · rw [ho]
            exact peak20_root94 he
          · rw [ho]
            exact peak20_root95 he
          · rw [ho]
            exact peak20_root96 he
          · rw [ho]
            exact peak20_root97 he
          · rw [ho]
            exact peak20_root98 he
          · rw [ho]
            exact peak20_root99 he
          · rw [ho]
            exact peak20_root100 he
          · rw [ho]
            exact peak20_root101 he
          · rw [ho]
            exact peak20_root102 he
          · rw [ho]
            exact peak20_root103 he
          · rw [ho]
            exact peak20_root104 he
        | @leftD _ t3 _ h3 =>
          exact ⟨(T.d (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) t3), (Steps.cons (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.leftD x0 (Step.rightD (T.c (T.d t3 x1) (T.d t3 x1) x2) (Step.leftD x1 h3))) (Steps.cons (Step.rightD (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) h3) (Steps.refl _))))), (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD (T.d x0 x1) (Step.firstC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.rightD (T.c (T.d t3 x1) (T.d t3 x1) x2) (Step.leftD x1 h3))) (Steps.cons (Step.right (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.right (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.right (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (Step.secondC (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.right (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (Step.secondC (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.right (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (Step.thirdC (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.c (T.d t3 x1) (T.d t3 x1) x2) (Step.leftD x1 h3))) (Steps.cons (Step.root (Root.r20 t3 x1 x2)) (Steps.refl _)))))))))⟩
        | @rightD _ _ t3 h3 =>
          exact ⟨(T.d (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) x0), (Steps.cons (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.leftD x0 (Step.rightD (T.c (T.d x0 t3) (T.d x0 t3) x2) (Step.rightD x0 h3))) (Steps.refl _)))), (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.rightD (T.c (T.d x0 t3) (T.d x0 t3) x2) (Step.rightD x0 h3))) (Steps.cons (Step.right (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (Step.secondC (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (Step.secondC (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (Step.thirdC (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.c (T.d x0 t3) (T.d x0 t3) x2) (Step.rightD x0 h3))) (Steps.cons (Step.root (Root.r20 x0 t3 x2)) (Steps.refl _)))))))))⟩
      | @thirdC _ _ _ t2 h2 =>
        exact ⟨(T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) t2) (T.d x0 x1)) x0), (Steps.cons (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.thirdC (T.d x0 x1) (T.d x0 x1) h2))) (Steps.refl _)), (Steps.cons (Step.right (T.d (T.c (T.d x0 x1) (T.d x0 x1) t2) (T.d x0 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.thirdC (T.d x0 x1) (T.d x0 x1) h2))) (Steps.cons (Step.right (T.d (T.c (T.d x0 x1) (T.d x0 x1) t2) (T.d x0 x1)) (Step.secondC (T.c (T.d x0 x1) (T.d x0 x1) t2) (T.d x0 x1) (Step.thirdC (T.d x0 x1) (T.d x0 x1) h2))) (Steps.cons (Step.root (Root.r20 x0 x1 t2)) (Steps.refl _))))⟩
    | @rightD _ _ t1 h1 =>
      cases h1 with
      | root hr =>
        rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
        · rw [ho]
          exact peak20_root105 he
        · rw [ho]
          exact peak20_root106 he
        · rw [ho]
          exact peak20_root107 he
        · rw [ho]
          exact peak20_root108 he
        · rw [ho]
          exact peak20_root109 he
        · rw [ho]
          exact peak20_root110 he
        · rw [ho]
          exact peak20_root111 he
        · rw [ho]
          exact peak20_root112 he
        · rw [ho]
          exact peak20_root113 he
        · rw [ho]
          exact peak20_root114 he
        · rw [ho]
          exact peak20_root115 he
        · rw [ho]
          exact peak20_root116 he
        · rw [ho]
          exact peak20_root117 he
        · rw [ho]
          exact peak20_root118 he
        · rw [ho]
          exact peak20_root119 he
        · rw [ho]
          exact peak20_root120 he
        · rw [ho]
          exact peak20_root121 he
        · rw [ho]
          exact peak20_root122 he
        · rw [ho]
          exact peak20_root123 he
        · rw [ho]
          exact peak20_root124 he
        · rw [ho]
          exact peak20_root125 he
      | @leftD _ t2 _ h2 =>
        exact ⟨(T.d (T.d (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.d t2 x1)) t2), (Steps.cons (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h2)))) (Steps.cons (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.secondC (T.d t2 x1) x2 (Step.leftD x1 h2)))) (Steps.cons (Step.leftD x0 (Step.rightD (T.c (T.d t2 x1) (T.d t2 x1) x2) (Step.leftD x1 h2))) (Steps.cons (Step.rightD (T.d (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.d t2 x1)) h2) (Steps.refl _))))), (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD (T.d t2 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h2)))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD (T.d t2 x1) (Step.secondC (T.d t2 x1) x2 (Step.leftD x1 h2)))) (Steps.cons (Step.right (T.d (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.d t2 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h2)))) (Steps.cons (Step.right (T.d (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.d t2 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.secondC (T.d t2 x1) x2 (Step.leftD x1 h2)))) (Steps.cons (Step.right (T.d (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.d t2 x1)) (Step.secondC (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h2)))) (Steps.cons (Step.right (T.d (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.d t2 x1)) (Step.secondC (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.d x0 x1) (Step.secondC (T.d t2 x1) x2 (Step.leftD x1 h2)))) (Steps.cons (Step.right (T.d (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.d t2 x1)) (Step.thirdC (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.c (T.d t2 x1) (T.d t2 x1) x2) (Step.leftD x1 h2))) (Steps.cons (Step.root (Root.r20 t2 x1 x2)) (Steps.refl _)))))))))⟩
      | @rightD _ _ t2 h2 =>
        exact ⟨(T.d (T.d (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.d x0 t2)) x0), (Steps.cons (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h2)))) (Steps.cons (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t2) x2 (Step.rightD x0 h2)))) (Steps.cons (Step.leftD x0 (Step.rightD (T.c (T.d x0 t2) (T.d x0 t2) x2) (Step.rightD x0 h2))) (Steps.refl _)))), (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD (T.d x0 t2) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h2)))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD (T.d x0 t2) (Step.secondC (T.d x0 t2) x2 (Step.rightD x0 h2)))) (Steps.cons (Step.right (T.d (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.d x0 t2)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h2)))) (Steps.cons (Step.right (T.d (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.d x0 t2)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.secondC (T.d x0 t2) x2 (Step.rightD x0 h2)))) (Steps.cons (Step.right (T.d (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.d x0 t2)) (Step.secondC (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h2)))) (Steps.cons (Step.right (T.d (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.d x0 t2)) (Step.secondC (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.d x0 x1) (Step.secondC (T.d x0 t2) x2 (Step.rightD x0 h2)))) (Steps.cons (Step.right (T.d (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.d x0 t2)) (Step.thirdC (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.c (T.d x0 t2) (T.d x0 t2) x2) (Step.rightD x0 h2))) (Steps.cons (Step.root (Root.r20 x0 t2 x2)) (Steps.refl _)))))))))⟩
  | @right _ _ t0 h0 =>
    cases h0 with
    | root hr =>
      rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
      · rw [ho]
        exact peak20_root126 he
      · rw [ho]
        exact peak20_root127 he
      · rw [ho]
        exact peak20_root128 he
      · rw [ho]
        exact peak20_root129 he
      · rw [ho]
        exact peak20_root130 he
      · rw [ho]
        exact peak20_root131 he
      · rw [ho]
        exact peak20_root132 he
      · rw [ho]
        exact peak20_root133 he
      · rw [ho]
        exact peak20_root134 he
      · rw [ho]
        exact peak20_root135 he
      · rw [ho]
        exact peak20_root136 he
      · rw [ho]
        exact peak20_root137 he
      · rw [ho]
        exact peak20_root138 he
      · rw [ho]
        exact peak20_root139 he
      · rw [ho]
        exact peak20_root140 he
      · rw [ho]
        exact peak20_root141 he
      · rw [ho]
        exact peak20_root142 he
      · rw [ho]
        exact peak20_root143 he
      · rw [ho]
        exact peak20_root144 he
      · rw [ho]
        exact peak20_root145 he
      · rw [ho]
        exact peak20_root146 he
    | @firstC _ t1 _ _ h1 =>
      cases h1 with
      | root hr =>
        rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
        · rw [ho]
          exact peak20_root147 he
        · rw [ho]
          exact peak20_root148 he
        · rw [ho]
          exact peak20_root149 he
        · rw [ho]
          exact peak20_root150 he
        · rw [ho]
          exact peak20_root151 he
        · rw [ho]
          exact peak20_root152 he
        · rw [ho]
          exact peak20_root153 he
        · rw [ho]
          exact peak20_root154 he
        · rw [ho]
          exact peak20_root155 he
        · rw [ho]
          exact peak20_root156 he
        · rw [ho]
          exact peak20_root157 he
        · rw [ho]
          exact peak20_root158 he
        · rw [ho]
          exact peak20_root159 he
        · rw [ho]
          exact peak20_root160 he
        · rw [ho]
          exact peak20_root161 he
        · rw [ho]
          exact peak20_root162 he
        · rw [ho]
          exact peak20_root163 he
        · rw [ho]
          exact peak20_root164 he
        · rw [ho]
          exact peak20_root165 he
        · rw [ho]
          exact peak20_root166 he
        · rw [ho]
          exact peak20_root167 he
      | @firstC _ t2 _ _ h2 =>
        cases h2 with
        | root hr =>
          rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
          · rw [ho]
            exact peak20_root168 he
          · rw [ho]
            exact peak20_root169 he
          · rw [ho]
            exact peak20_root170 he
          · rw [ho]
            exact peak20_root171 he
          · rw [ho]
            exact peak20_root172 he
          · rw [ho]
            exact peak20_root173 he
          · rw [ho]
            exact peak20_root174 he
          · rw [ho]
            exact peak20_root175 he
          · rw [ho]
            exact peak20_root176 he
          · rw [ho]
            exact peak20_root177 he
          · rw [ho]
            exact peak20_root178 he
          · rw [ho]
            exact peak20_root179 he
          · rw [ho]
            exact peak20_root180 he
          · rw [ho]
            exact peak20_root181 he
          · rw [ho]
            exact peak20_root182 he
          · rw [ho]
            exact peak20_root183 he
          · rw [ho]
            exact peak20_root184 he
          · rw [ho]
            exact peak20_root185 he
          · rw [ho]
            exact peak20_root186 he
          · rw [ho]
            exact peak20_root187 he
          · rw [ho]
            exact peak20_root188 he
        | @leftD _ t3 _ h3 =>
          exact ⟨(T.d (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) t3), (Steps.cons (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.leftD x0 (Step.rightD (T.c (T.d t3 x1) (T.d t3 x1) x2) (Step.leftD x1 h3))) (Steps.cons (Step.rightD (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) h3) (Steps.refl _))))), (Steps.cons (Step.left (T.c (T.c (T.d t3 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.left (T.c (T.c (T.d t3 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.left (T.c (T.c (T.d t3 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.rightD (T.c (T.d t3 x1) (T.d t3 x1) x2) (Step.leftD x1 h3))) (Steps.cons (Step.right (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.right (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (Step.secondC (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.right (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (Step.secondC (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.right (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (Step.thirdC (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.c (T.d t3 x1) (T.d t3 x1) x2) (Step.leftD x1 h3))) (Steps.cons (Step.root (Root.r20 t3 x1 x2)) (Steps.refl _)))))))))⟩
        | @rightD _ _ t3 h3 =>
          exact ⟨(T.d (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) x0), (Steps.cons (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.leftD x0 (Step.rightD (T.c (T.d x0 t3) (T.d x0 t3) x2) (Step.rightD x0 h3))) (Steps.refl _)))), (Steps.cons (Step.left (T.c (T.c (T.d x0 t3) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.left (T.c (T.c (T.d x0 t3) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.left (T.c (T.c (T.d x0 t3) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.rightD (T.c (T.d x0 t3) (T.d x0 t3) x2) (Step.rightD x0 h3))) (Steps.cons (Step.right (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (Step.secondC (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (Step.secondC (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (Step.thirdC (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.c (T.d x0 t3) (T.d x0 t3) x2) (Step.rightD x0 h3))) (Steps.cons (Step.root (Root.r20 x0 t3 x2)) (Steps.refl _)))))))))⟩
      | @secondC _ _ t2 _ h2 =>
        cases h2 with
        | root hr =>
          rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
          · rw [ho]
            exact peak20_root189 he
          · rw [ho]
            exact peak20_root190 he
          · rw [ho]
            exact peak20_root191 he
          · rw [ho]
            exact peak20_root192 he
          · rw [ho]
            exact peak20_root193 he
          · rw [ho]
            exact peak20_root194 he
          · rw [ho]
            exact peak20_root195 he
          · rw [ho]
            exact peak20_root196 he
          · rw [ho]
            exact peak20_root197 he
          · rw [ho]
            exact peak20_root198 he
          · rw [ho]
            exact peak20_root199 he
          · rw [ho]
            exact peak20_root200 he
          · rw [ho]
            exact peak20_root201 he
          · rw [ho]
            exact peak20_root202 he
          · rw [ho]
            exact peak20_root203 he
          · rw [ho]
            exact peak20_root204 he
          · rw [ho]
            exact peak20_root205 he
          · rw [ho]
            exact peak20_root206 he
          · rw [ho]
            exact peak20_root207 he
          · rw [ho]
            exact peak20_root208 he
          · rw [ho]
            exact peak20_root209 he
        | @leftD _ t3 _ h3 =>
          exact ⟨(T.d (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) t3), (Steps.cons (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.leftD x0 (Step.rightD (T.c (T.d t3 x1) (T.d t3 x1) x2) (Step.leftD x1 h3))) (Steps.cons (Step.rightD (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) h3) (Steps.refl _))))), (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d t3 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d t3 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d t3 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.rightD (T.c (T.d t3 x1) (T.d t3 x1) x2) (Step.leftD x1 h3))) (Steps.cons (Step.right (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.firstC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.right (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (Step.secondC (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.right (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (Step.secondC (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.right (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (Step.thirdC (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.c (T.d t3 x1) (T.d t3 x1) x2) (Step.leftD x1 h3))) (Steps.cons (Step.root (Root.r20 t3 x1 x2)) (Steps.refl _)))))))))⟩
        | @rightD _ _ t3 h3 =>
          exact ⟨(T.d (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) x0), (Steps.cons (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.leftD x0 (Step.rightD (T.c (T.d x0 t3) (T.d x0 t3) x2) (Step.rightD x0 h3))) (Steps.refl _)))), (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 t3) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 t3) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 t3) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.rightD (T.c (T.d x0 t3) (T.d x0 t3) x2) (Step.rightD x0 h3))) (Steps.cons (Step.right (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (Step.secondC (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (Step.secondC (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (Step.thirdC (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.c (T.d x0 t3) (T.d x0 t3) x2) (Step.rightD x0 h3))) (Steps.cons (Step.root (Root.r20 x0 t3 x2)) (Steps.refl _)))))))))⟩
      | @thirdC _ _ _ t2 h2 =>
        exact ⟨(T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) t2) (T.d x0 x1)) x0), (Steps.cons (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.thirdC (T.d x0 x1) (T.d x0 x1) h2))) (Steps.refl _)), (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) t2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD (T.d x0 x1) (Step.thirdC (T.d x0 x1) (T.d x0 x1) h2))) (Steps.cons (Step.right (T.d (T.c (T.d x0 x1) (T.d x0 x1) t2) (T.d x0 x1)) (Step.secondC (T.c (T.d x0 x1) (T.d x0 x1) t2) (T.d x0 x1) (Step.thirdC (T.d x0 x1) (T.d x0 x1) h2))) (Steps.cons (Step.root (Root.r20 x0 x1 t2)) (Steps.refl _))))⟩
    | @secondC _ _ t1 _ h1 =>
      cases h1 with
      | root hr =>
        rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
        · rw [ho]
          exact peak20_root210 he
        · rw [ho]
          exact peak20_root211 he
        · rw [ho]
          exact peak20_root212 he
        · rw [ho]
          exact peak20_root213 he
        · rw [ho]
          exact peak20_root214 he
        · rw [ho]
          exact peak20_root215 he
        · rw [ho]
          exact peak20_root216 he
        · rw [ho]
          exact peak20_root217 he
        · rw [ho]
          exact peak20_root218 he
        · rw [ho]
          exact peak20_root219 he
        · rw [ho]
          exact peak20_root220 he
        · rw [ho]
          exact peak20_root221 he
        · rw [ho]
          exact peak20_root222 he
        · rw [ho]
          exact peak20_root223 he
        · rw [ho]
          exact peak20_root224 he
        · rw [ho]
          exact peak20_root225 he
        · rw [ho]
          exact peak20_root226 he
        · rw [ho]
          exact peak20_root227 he
        · rw [ho]
          exact peak20_root228 he
        · rw [ho]
          exact peak20_root229 he
        · rw [ho]
          exact peak20_root230 he
      | @firstC _ t2 _ _ h2 =>
        cases h2 with
        | root hr =>
          rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
          · rw [ho]
            exact peak20_root231 he
          · rw [ho]
            exact peak20_root232 he
          · rw [ho]
            exact peak20_root233 he
          · rw [ho]
            exact peak20_root234 he
          · rw [ho]
            exact peak20_root235 he
          · rw [ho]
            exact peak20_root236 he
          · rw [ho]
            exact peak20_root237 he
          · rw [ho]
            exact peak20_root238 he
          · rw [ho]
            exact peak20_root239 he
          · rw [ho]
            exact peak20_root240 he
          · rw [ho]
            exact peak20_root241 he
          · rw [ho]
            exact peak20_root242 he
          · rw [ho]
            exact peak20_root243 he
          · rw [ho]
            exact peak20_root244 he
          · rw [ho]
            exact peak20_root245 he
          · rw [ho]
            exact peak20_root246 he
          · rw [ho]
            exact peak20_root247 he
          · rw [ho]
            exact peak20_root248 he
          · rw [ho]
            exact peak20_root249 he
          · rw [ho]
            exact peak20_root250 he
          · rw [ho]
            exact peak20_root251 he
        | @leftD _ t3 _ h3 =>
          exact ⟨(T.d (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) t3), (Steps.cons (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.leftD x0 (Step.rightD (T.c (T.d t3 x1) (T.d t3 x1) x2) (Step.leftD x1 h3))) (Steps.cons (Step.rightD (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) h3) (Steps.refl _))))), (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d t3 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d t3 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d t3 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.rightD (T.c (T.d t3 x1) (T.d t3 x1) x2) (Step.leftD x1 h3))) (Steps.cons (Step.right (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (Step.firstC (T.c (T.d t3 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.right (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (Step.firstC (T.c (T.d t3 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.right (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (Step.secondC (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.right (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (Step.thirdC (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.c (T.d t3 x1) (T.d t3 x1) x2) (Step.leftD x1 h3))) (Steps.cons (Step.root (Root.r20 t3 x1 x2)) (Steps.refl _)))))))))⟩
        | @rightD _ _ t3 h3 =>
          exact ⟨(T.d (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) x0), (Steps.cons (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.leftD x0 (Step.rightD (T.c (T.d x0 t3) (T.d x0 t3) x2) (Step.rightD x0 h3))) (Steps.refl _)))), (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 t3) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 t3) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 t3) (T.d x0 x1) x2) (T.d x0 x1)) (Step.rightD (T.c (T.d x0 t3) (T.d x0 t3) x2) (Step.rightD x0 h3))) (Steps.cons (Step.right (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (Step.firstC (T.c (T.d x0 t3) (T.d x0 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (Step.firstC (T.c (T.d x0 t3) (T.d x0 x1) x2) (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (Step.secondC (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (Step.thirdC (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.c (T.d x0 t3) (T.d x0 t3) x2) (Step.rightD x0 h3))) (Steps.cons (Step.root (Root.r20 x0 t3 x2)) (Steps.refl _)))))))))⟩
      | @secondC _ _ t2 _ h2 =>
        cases h2 with
        | root hr =>
          rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
          · rw [ho]
            exact peak20_root252 he
          · rw [ho]
            exact peak20_root253 he
          · rw [ho]
            exact peak20_root254 he
          · rw [ho]
            exact peak20_root255 he
          · rw [ho]
            exact peak20_root256 he
          · rw [ho]
            exact peak20_root257 he
          · rw [ho]
            exact peak20_root258 he
          · rw [ho]
            exact peak20_root259 he
          · rw [ho]
            exact peak20_root260 he
          · rw [ho]
            exact peak20_root261 he
          · rw [ho]
            exact peak20_root262 he
          · rw [ho]
            exact peak20_root263 he
          · rw [ho]
            exact peak20_root264 he
          · rw [ho]
            exact peak20_root265 he
          · rw [ho]
            exact peak20_root266 he
          · rw [ho]
            exact peak20_root267 he
          · rw [ho]
            exact peak20_root268 he
          · rw [ho]
            exact peak20_root269 he
          · rw [ho]
            exact peak20_root270 he
          · rw [ho]
            exact peak20_root271 he
          · rw [ho]
            exact peak20_root272 he
        | @leftD _ t3 _ h3 =>
          exact ⟨(T.d (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) t3), (Steps.cons (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.leftD x0 (Step.rightD (T.c (T.d t3 x1) (T.d t3 x1) x2) (Step.leftD x1 h3))) (Steps.cons (Step.rightD (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) h3) (Steps.refl _))))), (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d t3 x1) x2) (T.d x0 x1)) (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d t3 x1) x2) (T.d x0 x1)) (Step.leftD (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d t3 x1) x2) (T.d x0 x1)) (Step.rightD (T.c (T.d t3 x1) (T.d t3 x1) x2) (Step.leftD x1 h3))) (Steps.cons (Step.right (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d t3 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.right (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d t3 x1) x2) (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.right (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (Step.secondC (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d x0 x1) (Step.firstC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.right (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (Step.thirdC (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.c (T.d t3 x1) (T.d t3 x1) x2) (Step.leftD x1 h3))) (Steps.cons (Step.root (Root.r20 t3 x1 x2)) (Steps.refl _)))))))))⟩
        | @rightD _ _ t3 h3 =>
          exact ⟨(T.d (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) x0), (Steps.cons (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.leftD x0 (Step.rightD (T.c (T.d x0 t3) (T.d x0 t3) x2) (Step.rightD x0 h3))) (Steps.refl _)))), (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 t3) x2) (T.d x0 x1)) (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 t3) x2) (T.d x0 x1)) (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 t3) x2) (T.d x0 x1)) (Step.rightD (T.c (T.d x0 t3) (T.d x0 t3) x2) (Step.rightD x0 h3))) (Steps.cons (Step.right (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 t3) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 t3) x2) (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (Step.secondC (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 x1) (Step.firstC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (Step.thirdC (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.c (T.d x0 t3) (T.d x0 t3) x2) (Step.rightD x0 h3))) (Steps.cons (Step.root (Root.r20 x0 t3 x2)) (Steps.refl _)))))))))⟩
      | @thirdC _ _ _ t2 h2 =>
        exact ⟨(T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) t2) (T.d x0 x1)) x0), (Steps.cons (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.thirdC (T.d x0 x1) (T.d x0 x1) h2))) (Steps.refl _)), (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) t2) (T.d x0 x1)) (Step.leftD (T.d x0 x1) (Step.thirdC (T.d x0 x1) (T.d x0 x1) h2))) (Steps.cons (Step.right (T.d (T.c (T.d x0 x1) (T.d x0 x1) t2) (T.d x0 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) t2) (T.d x0 x1) (Step.thirdC (T.d x0 x1) (T.d x0 x1) h2))) (Steps.cons (Step.root (Root.r20 x0 x1 t2)) (Steps.refl _))))⟩
    | @thirdC _ _ _ t1 h1 =>
      cases h1 with
      | root hr =>
        rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
        · rw [ho]
          exact peak20_root273 he
        · rw [ho]
          exact peak20_root274 he
        · rw [ho]
          exact peak20_root275 he
        · rw [ho]
          exact peak20_root276 he
        · rw [ho]
          exact peak20_root277 he
        · rw [ho]
          exact peak20_root278 he
        · rw [ho]
          exact peak20_root279 he
        · rw [ho]
          exact peak20_root280 he
        · rw [ho]
          exact peak20_root281 he
        · rw [ho]
          exact peak20_root282 he
        · rw [ho]
          exact peak20_root283 he
        · rw [ho]
          exact peak20_root284 he
        · rw [ho]
          exact peak20_root285 he
        · rw [ho]
          exact peak20_root286 he
        · rw [ho]
          exact peak20_root287 he
        · rw [ho]
          exact peak20_root288 he
        · rw [ho]
          exact peak20_root289 he
        · rw [ho]
          exact peak20_root290 he
        · rw [ho]
          exact peak20_root291 he
        · rw [ho]
          exact peak20_root292 he
        · rw [ho]
          exact peak20_root293 he
      | @leftD _ t2 _ h2 =>
        exact ⟨(T.d (T.d (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.d t2 x1)) t2), (Steps.cons (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h2)))) (Steps.cons (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.secondC (T.d t2 x1) x2 (Step.leftD x1 h2)))) (Steps.cons (Step.leftD x0 (Step.rightD (T.c (T.d t2 x1) (T.d t2 x1) x2) (Step.leftD x1 h2))) (Steps.cons (Step.rightD (T.d (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.d t2 x1)) h2) (Steps.refl _))))), (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d t2 x1)) (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h2)))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d t2 x1)) (Step.leftD (T.d x0 x1) (Step.secondC (T.d t2 x1) x2 (Step.leftD x1 h2)))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d t2 x1)) (Step.rightD (T.c (T.d t2 x1) (T.d t2 x1) x2) (Step.leftD x1 h2))) (Steps.cons (Step.right (T.d (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.d t2 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d t2 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h2)))) (Steps.cons (Step.right (T.d (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.d t2 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d t2 x1) (Step.secondC (T.d t2 x1) x2 (Step.leftD x1 h2)))) (Steps.cons (Step.right (T.d (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.d t2 x1)) (Step.secondC (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.d t2 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h2)))) (Steps.cons (Step.right (T.d (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.d t2 x1)) (Step.secondC (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.d t2 x1) (Step.secondC (T.d t2 x1) x2 (Step.leftD x1 h2)))) (Steps.cons (Step.root (Root.r20 t2 x1 x2)) (Steps.refl _)))))))))⟩
      | @rightD _ _ t2 h2 =>
        exact ⟨(T.d (T.d (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.d x0 t2)) x0), (Steps.cons (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h2)))) (Steps.cons (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t2) x2 (Step.rightD x0 h2)))) (Steps.cons (Step.leftD x0 (Step.rightD (T.c (T.d x0 t2) (T.d x0 t2) x2) (Step.rightD x0 h2))) (Steps.refl _)))), (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 t2)) (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h2)))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 t2)) (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t2) x2 (Step.rightD x0 h2)))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 t2)) (Step.rightD (T.c (T.d x0 t2) (T.d x0 t2) x2) (Step.rightD x0 h2))) (Steps.cons (Step.right (T.d (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.d x0 t2)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 t2) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h2)))) (Steps.cons (Step.right (T.d (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.d x0 t2)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 t2) (Step.secondC (T.d x0 t2) x2 (Step.rightD x0 h2)))) (Steps.cons (Step.right (T.d (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.d x0 t2)) (Step.secondC (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.d x0 t2) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h2)))) (Steps.cons (Step.right (T.d (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.d x0 t2)) (Step.secondC (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.d x0 t2) (Step.secondC (T.d x0 t2) x2 (Step.rightD x0 h2)))) (Steps.cons (Step.root (Root.r20 x0 t2 x2)) (Steps.refl _)))))))))⟩
end submission.Austin5837

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak21_root0 {q0 q1 x0 x1 x2 : T} (he : (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.m (T.m q0 q1) q1)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.r q1 q0) := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  cases e0

theorem peak21_root1 {q0 q1 x0 x1 x2 : T} (he : (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.m q0 (T.r q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.d q0 q1) := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  have e2 := e0.symm
  subst e2
  cases e1

theorem peak21_root2 {q0 q1 q2 x0 x1 x2 : T} (he : (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.m q0 (T.d q1 q2))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.c q0 q1 q2) := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  have e2 := e0.symm
  subst e2
  cases e1

theorem peak21_root3 {q0 q1 q2 x0 x1 x2 : T} (he : (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.m q0 (T.c q1 q0 q2))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) q1 := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  have e2 := e0.symm
  subst e2
  have e3 := (T.c.inj e1).1
  have e4 := (T.c.inj e1).2.1
  have e5 := (T.c.inj e1).2.2
  have e6 := e3.symm
  subst e6
  cases e4

theorem peak21_root4 {q0 q1 x0 x1 x2 : T} (he : (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.m (T.r q0 q1) q0)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.r q0 (T.m q1 q0)) := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  cases e0

theorem peak21_root5 {q0 q1 x0 x1 x2 : T} (he : (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.m (T.d q0 q1) (T.r q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.r (T.r q0 q1) q0) := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  have e2 := (T.d.inj e0).1
  have e3 := (T.d.inj e0).2
  cases e1

theorem peak21_root6 {q0 q1 q2 x0 x1 x2 : T} (he : (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.r (T.d q0 q1) q2)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.c (T.c q2 q0 q1) q0 q1) := by
  cases he

theorem peak21_root7 {q0 q1 q2 x0 x1 x2 : T} (he : (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.m q0 (T.c q0 q1 q2))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.r (T.c q0 q1 q2) q1) := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  have e2 := e0.symm
  subst e2
  have e3 := (T.c.inj e1).1
  have e4 := (T.c.inj e1).2.1
  have e5 := (T.c.inj e1).2.2
  cases e3

theorem peak21_root8 {q0 q1 x0 x1 x2 : T} (he : (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.r (T.c q0 q0 q1) q0)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) q0 := by
  cases he

theorem peak21_root9 {q0 q1 x0 x1 x2 : T} (he : (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.m (T.c q0 q0 q1) q0)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.d (T.c q0 q0 q1) q0) := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  cases e0

theorem peak21_root10 {q0 q1 x0 x1 x2 : T} (he : (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.m (T.d (T.c q0 q0 q1) q0) q0)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.r q0 (T.c q0 q0 q1)) := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  have e2 := (T.d.inj e0).1
  have e3 := (T.d.inj e0).2
  have e4 := e1.symm
  subst e4
  cases e2

theorem peak21_root11 {q0 q1 q2 x0 x1 x2 : T} (he : (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.m (T.d q0 q1) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.d (T.d q0 q1) q2) := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  have e2 := (T.d.inj e0).1
  have e3 := (T.d.inj e0).2
  have e4 := (T.c.inj e1).1
  have e5 := (T.c.inj e1).2.1
  have e6 := (T.c.inj e1).2.2
  have e7 := e2.symm
  subst e7
  have e8 := e3.symm
  subst e8
  have e9 := (T.c.inj e4).1
  have e10 := (T.c.inj e4).2.1
  have e11 := (T.c.inj e4).2.2
  cases e5

theorem peak21_root12 {q0 q1 q2 x0 x1 x2 : T} (he : (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) q0 q1)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) := by
  cases he

theorem peak21_root13 {q0 q1 q2 x0 x1 x2 : T} (he : (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.c q0 (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.c (T.d q0 q1) (T.d q0 q1) q2) := by
  cases he

theorem peak21_root14 {q0 q1 q2 x0 x1 x2 : T} (he : (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.m (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) q0 := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  cases e0

theorem peak21_root15 {q0 q1 q2 x0 x1 x2 : T} (he : (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.m (T.d (T.d q0 q1) q2) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.r (T.c (T.c q2 q0 q1) q0 q1) (T.d q0 q1)) := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  have e2 := (T.d.inj e0).1
  have e3 := (T.d.inj e0).2
  have e4 := (T.c.inj e1).1
  have e5 := (T.c.inj e1).2.1
  have e6 := (T.c.inj e1).2.2
  have e7 := (T.d.inj e2).1
  have e8 := (T.d.inj e2).2
  have e9 := e3.symm
  subst e9
  have e10 := (T.c.inj e4).1
  have e11 := (T.c.inj e4).2.1
  have e12 := (T.c.inj e4).2.2
  have e13 := e5.symm
  subst e13
  have e14 := e6.symm
  subst e14
  have e15 := e10.symm
  have cycle := congrArg size e15
  simp only [size] at cycle
  omega

theorem peak21_root16 {q0 q1 q2 x0 x1 x2 : T} (he : (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.m q0 (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.r (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2)) := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  have e2 := e0.symm
  subst e2
  have e3 := (T.c.inj e1).1
  have e4 := (T.c.inj e1).2.1
  have e5 := (T.c.inj e1).2.2
  cases e3

theorem peak21_root17 {q0 q1 q2 x0 x1 x2 : T} (he : (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.m (T.d q0 q1) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  have e2 := (T.d.inj e0).1
  have e3 := (T.d.inj e0).2
  have e4 := (T.c.inj e1).1
  have e5 := (T.c.inj e1).2.1
  have e6 := (T.c.inj e1).2.2
  have e7 := e2.symm
  subst e7
  have e8 := e3.symm
  subst e8
  cases e4

theorem peak21_root18 {q0 q1 q2 x0 x1 x2 : T} (he : (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.m (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.r (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1) (T.d q0 q1)) := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  have e2 := (T.d.inj e0).1
  have e3 := (T.d.inj e0).2
  have e4 := (T.c.inj e1).1
  have e5 := (T.c.inj e1).2.1
  have e6 := (T.c.inj e1).2.2
  have e7 := (T.d.inj e2).1
  have e8 := (T.d.inj e2).2
  subst e3
  cases e4

theorem peak21_root19 {q0 q1 q2 x0 x1 x2 : T} (he : (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.m (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  have e2 := (T.d.inj e0).1
  have e3 := (T.d.inj e0).2
  have e4 := (T.c.inj e1).1
  have e5 := (T.c.inj e1).2.1
  have e6 := (T.c.inj e1).2.2
  cases e2

theorem peak21_root20 {q0 q1 q2 x0 x1 x2 : T} (he : (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.m (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.r (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  have e2 := (T.d.inj e0).1
  have e3 := (T.d.inj e0).2
  have e4 := (T.c.inj e1).1
  have e5 := (T.c.inj e1).2.1
  have e6 := (T.c.inj e1).2.2
  have e7 := (T.d.inj e2).1
  have e8 := (T.d.inj e2).2
  have e9 := e3.symm
  subst e9
  have e10 := (T.c.inj e4).1
  have e11 := (T.c.inj e4).2.1
  have e12 := (T.c.inj e4).2.2
  have e13 := (T.c.inj e5).1
  have e14 := (T.c.inj e5).2.1
  have e15 := (T.c.inj e5).2.2
  have e16 := (T.d.inj e6).1
  have e17 := (T.d.inj e6).2
  have e18 := (T.c.inj e7).1
  have e19 := (T.c.inj e7).2.1
  have e20 := (T.c.inj e7).2.2
  have e21 := (T.d.inj e8).1
  have e22 := (T.d.inj e8).2
  have e23 := (T.d.inj e10).1
  have e24 := (T.d.inj e10).2
  have e25 := (T.d.inj e11).1
  have e26 := (T.d.inj e11).2
  have e27 := e12.symm
  subst e27
  have e28 := (T.d.inj e13).1
  have e29 := (T.d.inj e13).2
  have e30 := (T.d.inj e14).1
  have e31 := (T.d.inj e14).2
  have e32 := e17.symm
  subst e32
  exact ⟨(T.r (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))), (Steps.refl _), (Steps.refl _)⟩

end submission.Austin5837

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak21_root21 {q0 q1 x0 x1 x2 : T} (he : (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) = (T.m (T.m q0 q1) q1)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.r q1 q0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root22 {q0 q1 x0 x1 x2 : T} (he : (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) = (T.m q0 (T.r q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d q0 q1) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root23 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) = (T.m q0 (T.d q1 q2))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.c q0 q1 q2) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root24 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) = (T.m q0 (T.c q1 q0 q2))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m q1 (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root25 {q0 q1 x0 x1 x2 : T} (he : (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) = (T.m (T.r q0 q1) q0)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.r q0 (T.m q1 q0)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root26 {q0 q1 x0 x1 x2 : T} (he : (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) = (T.m (T.d q0 q1) (T.r q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.r (T.r q0 q1) q0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root27 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) = (T.r (T.d q0 q1) q2)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.c (T.c q2 q0 q1) q0 q1) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root28 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) = (T.m q0 (T.c q0 q1 q2))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.r (T.c q0 q1 q2) q1) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root29 {q0 q1 x0 x1 x2 : T} (he : (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) = (T.r (T.c q0 q0 q1) q0)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m q0 (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root30 {q0 q1 x0 x1 x2 : T} (he : (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) = (T.m (T.c q0 q0 q1) q0)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.c q0 q0 q1) q0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root31 {q0 q1 x0 x1 x2 : T} (he : (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) = (T.m (T.d (T.c q0 q0 q1) q0) q0)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.r q0 (T.c q0 q0 q1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root32 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) = (T.m (T.d q0 q1) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d q0 q1) q2) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root33 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) = (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) q0 q1)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root34 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) = (T.c q0 (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root35 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) = (T.m (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m q0 (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root36 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) = (T.m (T.d (T.d q0 q1) q2) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.r (T.c (T.c q2 q0 q1) q0 q1) (T.d q0 q1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root37 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) = (T.m q0 (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.r (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root38 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) = (T.m (T.d q0 q1) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root39 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) = (T.m (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.r (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1) (T.d q0 q1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root40 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) = (T.m (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root41 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) = (T.m (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.r (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

end submission.Austin5837

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak21_root42 {q0 q1 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m (T.m q0 q1) q1)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.r q1 q0) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root43 {q0 q1 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m q0 (T.r q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d q0 q1) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root44 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m q0 (T.d q1 q2))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.c q0 q1 q2) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root45 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m q0 (T.c q1 q0 q2))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d q1 x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root46 {q0 q1 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m (T.r q0 q1) q0)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.r q0 (T.m q1 q0)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root47 {q0 q1 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m (T.d q0 q1) (T.r q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.r (T.r q0 q1) q0) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root48 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.r (T.d q0 q1) q2)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.c (T.c q2 q0 q1) q0 q1) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root49 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m q0 (T.c q0 q1 q2))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.r (T.c q0 q1 q2) q1) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root50 {q0 q1 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.r (T.c q0 q0 q1) q0)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d q0 x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root51 {q0 q1 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m (T.c q0 q0 q1) q0)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c q0 q0 q1) q0) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root52 {q0 q1 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m (T.d (T.c q0 q0 q1) q0) q0)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.r q0 (T.c q0 q0 q1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root53 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m (T.d q0 q1) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.d q0 q1) q2) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root54 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) q0 q1)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root55 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.c q0 (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root56 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d q0 x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root57 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m (T.d (T.d q0 q1) q2) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.r (T.c (T.c q2 q0 q1) q0 q1) (T.d q0 q1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root58 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m q0 (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.r (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root59 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m (T.d q0 q1) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root60 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.r (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1) (T.d q0 q1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root61 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root62 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.r (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

end submission.Austin5837

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak21_root63 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.m q0 q1) q1)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.r q1 q0) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root64 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m q0 (T.r q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.d q0 q1) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root65 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m q0 (T.d q1 q2))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c q0 q1 q2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root66 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m q0 (T.c q1 q0 q2))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d q1 (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root67 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.r q0 q1) q0)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.r q0 (T.m q1 q0)) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root68 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.d q0 q1) (T.r q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.r (T.r q0 q1) q0) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root69 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.r (T.d q0 q1) q2)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.c q2 q0 q1) q0 q1) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root70 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m q0 (T.c q0 q1 q2))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.r (T.c q0 q1 q2) q1) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root71 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.r (T.c q0 q0 q1) q0)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d q0 (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root72 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.c q0 q0 q1) q0)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.d (T.c q0 q0 q1) q0) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root73 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.d (T.c q0 q0 q1) q0) q0)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.r q0 (T.c q0 q0 q1)) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root74 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.d q0 q1) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.d (T.d q0 q1) q2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root75 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) q0 q1)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  have e0 := (T.c.inj he).1
  have e1 := (T.c.inj he).2.1
  have e2 := (T.c.inj he).2.2
  cases e0

theorem peak21_root76 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.c q0 (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  have e0 := (T.c.inj he).1
  have e1 := (T.c.inj he).2.1
  have e2 := (T.c.inj he).2.2
  have e3 := e0.symm
  subst e3
  cases e1

theorem peak21_root77 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d q0 (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root78 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.d (T.d q0 q1) q2) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.r (T.c (T.c q2 q0 q1) q0 q1) (T.d q0 q1)) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root79 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m q0 (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.r (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root80 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.d q0 q1) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root81 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.r (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1) (T.d q0 q1)) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root82 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root83 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.r (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

end submission.Austin5837

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak21_root84 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.m q0 q1) q1)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.r q1 q0) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root85 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.r q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d q0 q1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root86 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.d q1 q2))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.c q0 q1 q2) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root87 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.c q1 q0 q2))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c q1 (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root88 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.r q0 q1) q0)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.r q0 (T.m q1 q0)) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root89 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d q0 q1) (T.r q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.r (T.r q0 q1) q0) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root90 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.r (T.d q0 q1) q2)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.c (T.c q2 q0 q1) q0 q1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root91 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.c q0 q1 q2))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.r (T.c q0 q1 q2) q1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root92 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.r (T.c q0 q0 q1) q0)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c q0 (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root93 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.c q0 q0 q1) q0)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d (T.c q0 q0 q1) q0) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root94 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.c q0 q0 q1) q0) q0)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.r q0 (T.c q0 q0 q1)) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root95 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d q0 q1) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d (T.d q0 q1) q2) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root96 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) q0 q1)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root97 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.c q0 (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root98 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c q0 (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root99 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.d q0 q1) q2) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.r (T.c (T.c q2 q0 q1) q0 q1) (T.d q0 q1)) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root100 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.r (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root101 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d q0 q1) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root102 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.r (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1) (T.d q0 q1)) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root103 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root104 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.r (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

end submission.Austin5837

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak21_root105 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.m q0 q1) q1)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.r q1 q0) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root106 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.r q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d q0 q1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root107 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.d q1 q2))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.c q0 q1 q2) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root108 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.c q1 q0 q2))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) q1 x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root109 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.r q0 q1) q0)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.r q0 (T.m q1 q0)) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root110 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d q0 q1) (T.r q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.r (T.r q0 q1) q0) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root111 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.r (T.d q0 q1) q2)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.c (T.c q2 q0 q1) q0 q1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root112 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.c q0 q1 q2))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.r (T.c q0 q1 q2) q1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root113 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.r (T.c q0 q0 q1) q0)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) q0 x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root114 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.c q0 q0 q1) q0)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d (T.c q0 q0 q1) q0) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root115 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.c q0 q0 q1) q0) q0)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.r q0 (T.c q0 q0 q1)) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root116 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d q0 q1) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d (T.d q0 q1) q2) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root117 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) q0 q1)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root118 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.c q0 (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.c (T.d q0 q1) (T.d q0 q1) q2) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root119 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) q0 x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root120 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.d q0 q1) q2) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.r (T.c (T.c q2 q0 q1) q0 q1) (T.d q0 q1)) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root121 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.r (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2)) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root122 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d q0 q1) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root123 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.r (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1) (T.d q0 q1)) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root124 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root125 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.r (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

end submission.Austin5837

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak21_root126 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.m q0 q1) q1)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.r q1 q0)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root127 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.r q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d q0 q1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root128 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.d q1 q2))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c q0 q1 q2)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root129 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.c q1 q0 q2))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) q1) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root130 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.r q0 q1) q0)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.r q0 (T.m q1 q0))) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root131 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d q0 q1) (T.r q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.r (T.r q0 q1) q0)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root132 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.r (T.d q0 q1) q2)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.c q2 q0 q1) q0 q1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root133 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.c q0 q1 q2))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.r (T.c q0 q1 q2) q1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root134 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.r (T.c q0 q0 q1) q0)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) q0) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root135 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.c q0 q0 q1) q0)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d (T.c q0 q0 q1) q0)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root136 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.c q0 q0 q1) q0) q0)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.r q0 (T.c q0 q0 q1))) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root137 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d q0 q1) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d (T.d q0 q1) q2)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root138 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) q0 q1)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root139 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.c q0 (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d q0 q1) (T.d q0 q1) q2)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root140 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) q0) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root141 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.d q0 q1) q2) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.r (T.c (T.c q2 q0 q1) q0 q1) (T.d q0 q1))) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root142 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.r (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2))) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root143 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d q0 q1) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2))) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root144 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.r (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1) (T.d q0 q1))) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root145 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root146 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.r (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

end submission.Austin5837

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak21_root147 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m (T.m q0 q1) q1)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.r q1 q0)) := by
  cases he

theorem peak21_root148 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m q0 (T.r q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.d q0 q1)) := by
  cases he

theorem peak21_root149 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m q0 (T.d q1 q2))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c q0 q1 q2)) := by
  cases he

theorem peak21_root150 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m q0 (T.c q1 q0 q2))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) q1) := by
  cases he

theorem peak21_root151 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m (T.r q0 q1) q0)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.r q0 (T.m q1 q0))) := by
  cases he

theorem peak21_root152 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m (T.d q0 q1) (T.r q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.r (T.r q0 q1) q0)) := by
  cases he

theorem peak21_root153 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.r (T.d q0 q1) q2)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c q2 q0 q1) q0 q1)) := by
  cases he

theorem peak21_root154 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m q0 (T.c q0 q1 q2))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.r (T.c q0 q1 q2) q1)) := by
  cases he

theorem peak21_root155 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.r (T.c q0 q0 q1) q0)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) q0) := by
  cases he

theorem peak21_root156 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m (T.c q0 q0 q1) q0)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.d (T.c q0 q0 q1) q0)) := by
  cases he

theorem peak21_root157 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m (T.d (T.c q0 q0 q1) q0) q0)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.r q0 (T.c q0 q0 q1))) := by
  cases he

theorem peak21_root158 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m (T.d q0 q1) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.d (T.d q0 q1) q2)) := by
  cases he

theorem peak21_root159 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) q0 q1)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) := by
  have e0 := (T.c.inj he).1
  have e1 := (T.c.inj he).2.1
  have e2 := (T.c.inj he).2.2
  have e3 := (T.c.inj e0).1
  have e4 := (T.c.inj e0).2.1
  have e5 := (T.c.inj e0).2.2
  have e6 := e1.symm
  subst e6
  have e7 := e2.symm
  subst e7
  have e8 := (T.d.inj e3).1
  have e9 := (T.d.inj e3).2
  have e10 := (T.d.inj e4).1
  have e11 := (T.d.inj e4).2
  have e12 := e5.symm
  subst e12
  have cycle := congrArg size e8
  simp only [size] at cycle
  omega

theorem peak21_root160 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.c q0 (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.d q0 q1) (T.d q0 q1) q2)) := by
  have e0 := (T.c.inj he).1
  have e1 := (T.c.inj he).2.1
  have e2 := (T.c.inj he).2.2
  have e3 := e0.symm
  subst e3
  have e4 := (T.c.inj e1).1
  have e5 := (T.c.inj e1).2.1
  have e6 := (T.c.inj e1).2.2
  have e7 := (T.d.inj e2).1
  have e8 := (T.d.inj e2).2
  have e9 := (T.d.inj e4).1
  have e10 := (T.d.inj e4).2
  have e11 := (T.d.inj e5).1
  have e12 := (T.d.inj e5).2
  have e13 := e6.symm
  subst e13
  have cycle := congrArg size e7
  simp only [size] at cycle
  omega

theorem peak21_root161 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) q0) := by
  cases he

theorem peak21_root162 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m (T.d (T.d q0 q1) q2) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.r (T.c (T.c q2 q0 q1) q0 q1) (T.d q0 q1))) := by
  cases he

theorem peak21_root163 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m q0 (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.r (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2))) := by
  cases he

theorem peak21_root164 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m (T.d q0 q1) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2))) := by
  cases he

theorem peak21_root165 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.r (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1) (T.d q0 q1))) := by
  cases he

theorem peak21_root166 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0)) := by
  cases he

theorem peak21_root167 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.r (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) := by
  cases he

end submission.Austin5837

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak21_root168 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.m q0 q1) q1)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.r q1 q0) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root169 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m q0 (T.r q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.d q0 q1) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root170 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m q0 (T.d q1 q2))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c q0 q1 q2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root171 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m q0 (T.c q1 q0 q2))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c q1 (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root172 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.r q0 q1) q0)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.r q0 (T.m q1 q0)) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root173 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.d q0 q1) (T.r q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.r (T.r q0 q1) q0) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root174 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.r (T.d q0 q1) q2)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.c q2 q0 q1) q0 q1) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root175 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m q0 (T.c q0 q1 q2))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.r (T.c q0 q1 q2) q1) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root176 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.r (T.c q0 q0 q1) q0)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c q0 (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root177 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.c q0 q0 q1) q0)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.d (T.c q0 q0 q1) q0) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root178 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.d (T.c q0 q0 q1) q0) q0)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.r q0 (T.c q0 q0 q1)) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root179 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.d q0 q1) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.d (T.d q0 q1) q2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root180 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) q0 q1)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  have e0 := (T.c.inj he).1
  have e1 := (T.c.inj he).2.1
  have e2 := (T.c.inj he).2.2
  cases e0

theorem peak21_root181 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.c q0 (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  have e0 := (T.c.inj he).1
  have e1 := (T.c.inj he).2.1
  have e2 := (T.c.inj he).2.2
  have e3 := e0.symm
  subst e3
  cases e1

theorem peak21_root182 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c q0 (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root183 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.d (T.d q0 q1) q2) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.r (T.c (T.c q2 q0 q1) q0 q1) (T.d q0 q1)) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root184 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m q0 (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.r (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root185 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.d q0 q1) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root186 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.r (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1) (T.d q0 q1)) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root187 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root188 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.r (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

end submission.Austin5837

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak21_root189 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.m q0 q1) q1)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.r q1 q0) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root190 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.r q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d q0 q1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root191 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.d q1 q2))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.c q0 q1 q2) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root192 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.c q1 q0 q2))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c q1 (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root193 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.r q0 q1) q0)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.r q0 (T.m q1 q0)) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root194 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d q0 q1) (T.r q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.r (T.r q0 q1) q0) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root195 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.r (T.d q0 q1) q2)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.c (T.c q2 q0 q1) q0 q1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root196 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.c q0 q1 q2))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.r (T.c q0 q1 q2) q1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root197 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.r (T.c q0 q0 q1) q0)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c q0 (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root198 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.c q0 q0 q1) q0)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d (T.c q0 q0 q1) q0) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root199 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.c q0 q0 q1) q0) q0)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.r q0 (T.c q0 q0 q1)) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root200 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d q0 q1) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d (T.d q0 q1) q2) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root201 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) q0 q1)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root202 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.c q0 (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root203 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c q0 (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root204 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.d q0 q1) q2) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.r (T.c (T.c q2 q0 q1) q0 q1) (T.d q0 q1)) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root205 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.r (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root206 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d q0 q1) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root207 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.r (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1) (T.d q0 q1)) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root208 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root209 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.r (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

end submission.Austin5837

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak21_root210 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.m q0 q1) q1)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.r q1 q0) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root211 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.r q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d q0 q1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root212 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.d q1 q2))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.c q0 q1 q2) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root213 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.c q1 q0 q2))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) q1 x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root214 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.r q0 q1) q0)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.r q0 (T.m q1 q0)) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root215 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d q0 q1) (T.r q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.r (T.r q0 q1) q0) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root216 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.r (T.d q0 q1) q2)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.c (T.c q2 q0 q1) q0 q1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root217 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.c q0 q1 q2))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.r (T.c q0 q1 q2) q1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root218 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.r (T.c q0 q0 q1) q0)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) q0 x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root219 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.c q0 q0 q1) q0)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d (T.c q0 q0 q1) q0) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root220 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.c q0 q0 q1) q0) q0)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.r q0 (T.c q0 q0 q1)) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root221 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d q0 q1) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d (T.d q0 q1) q2) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root222 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) q0 q1)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root223 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.c q0 (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.c (T.d q0 q1) (T.d q0 q1) q2) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root224 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) q0 x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root225 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.d q0 q1) q2) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.r (T.c (T.c q2 q0 q1) q0 q1) (T.d q0 q1)) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root226 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.r (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2)) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root227 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d q0 q1) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root228 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.r (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1) (T.d q0 q1)) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root229 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root230 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.r (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

end submission.Austin5837

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak21_root231 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.m q0 q1) q1)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.r q1 q0) (T.d x0 x1))) := by
  cases he

theorem peak21_root232 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m q0 (T.r q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d q0 q1) (T.d x0 x1))) := by
  cases he

theorem peak21_root233 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m q0 (T.d q1 q2))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c q0 q1 q2) (T.d x0 x1))) := by
  cases he

theorem peak21_root234 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m q0 (T.c q1 q0 q2))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) q1 (T.d x0 x1))) := by
  cases he

theorem peak21_root235 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.r q0 q1) q0)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.r q0 (T.m q1 q0)) (T.d x0 x1))) := by
  cases he

theorem peak21_root236 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.d q0 q1) (T.r q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.r (T.r q0 q1) q0) (T.d x0 x1))) := by
  cases he

theorem peak21_root237 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.r (T.d q0 q1) q2)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.c q2 q0 q1) q0 q1) (T.d x0 x1))) := by
  cases he

theorem peak21_root238 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m q0 (T.c q0 q1 q2))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.r (T.c q0 q1 q2) q1) (T.d x0 x1))) := by
  cases he

theorem peak21_root239 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.r (T.c q0 q0 q1) q0)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) q0 (T.d x0 x1))) := by
  cases he

theorem peak21_root240 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.c q0 q0 q1) q0)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d (T.c q0 q0 q1) q0) (T.d x0 x1))) := by
  cases he

theorem peak21_root241 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.d (T.c q0 q0 q1) q0) q0)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.r q0 (T.c q0 q0 q1)) (T.d x0 x1))) := by
  cases he

theorem peak21_root242 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.d q0 q1) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d (T.d q0 q1) q2) (T.d x0 x1))) := by
  cases he

theorem peak21_root243 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) q0 q1)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.d x0 x1))) := by
  have e0 := (T.c.inj he).1
  have e1 := (T.c.inj he).2.1
  have e2 := (T.c.inj he).2.2
  cases e0

theorem peak21_root244 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.c q0 (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d x0 x1))) := by
  have e0 := (T.c.inj he).1
  have e1 := (T.c.inj he).2.1
  have e2 := (T.c.inj he).2.2
  have e3 := e0.symm
  subst e3
  cases e1

theorem peak21_root245 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) q0 (T.d x0 x1))) := by
  cases he

theorem peak21_root246 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.d (T.d q0 q1) q2) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.r (T.c (T.c q2 q0 q1) q0 q1) (T.d q0 q1)) (T.d x0 x1))) := by
  cases he

theorem peak21_root247 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m q0 (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.r (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.d x0 x1))) := by
  cases he

theorem peak21_root248 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.d q0 q1) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.d x0 x1))) := by
  cases he

theorem peak21_root249 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.r (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1) (T.d q0 q1)) (T.d x0 x1))) := by
  cases he

theorem peak21_root250 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) (T.d x0 x1))) := by
  cases he

theorem peak21_root251 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.r (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) (T.d x0 x1))) := by
  cases he

end submission.Austin5837

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak21_root252 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.m q0 q1) q1)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.r q1 q0) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root253 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.r q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d q0 q1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root254 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.d q1 q2))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.c q0 q1 q2) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root255 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.c q1 q0 q2))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c q1 (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root256 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.r q0 q1) q0)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.r q0 (T.m q1 q0)) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root257 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d q0 q1) (T.r q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.r (T.r q0 q1) q0) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root258 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.r (T.d q0 q1) q2)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.c (T.c q2 q0 q1) q0 q1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root259 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.c q0 q1 q2))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.r (T.c q0 q1 q2) q1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root260 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.r (T.c q0 q0 q1) q0)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c q0 (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root261 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.c q0 q0 q1) q0)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d (T.c q0 q0 q1) q0) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root262 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.c q0 q0 q1) q0) q0)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.r q0 (T.c q0 q0 q1)) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root263 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d q0 q1) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d (T.d q0 q1) q2) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root264 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) q0 q1)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root265 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.c q0 (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root266 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c q0 (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root267 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.d q0 q1) q2) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.r (T.c (T.c q2 q0 q1) q0 q1) (T.d q0 q1)) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root268 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.r (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root269 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d q0 q1) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root270 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.r (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1) (T.d q0 q1)) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root271 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root272 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.r (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

end submission.Austin5837

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak21_root273 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.m q0 q1) q1)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.r q1 q0) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root274 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.r q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d q0 q1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root275 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.d q1 q2))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.c q0 q1 q2) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root276 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.c q1 q0 q2))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) q1 x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root277 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.r q0 q1) q0)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.r q0 (T.m q1 q0)) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root278 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d q0 q1) (T.r q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.r (T.r q0 q1) q0) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root279 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.r (T.d q0 q1) q2)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.c (T.c q2 q0 q1) q0 q1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root280 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.c q0 q1 q2))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.r (T.c q0 q1 q2) q1) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root281 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.r (T.c q0 q0 q1) q0)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) q0 x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root282 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.c q0 q0 q1) q0)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d (T.c q0 q0 q1) q0) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root283 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.c q0 q0 q1) q0) q0)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.r q0 (T.c q0 q0 q1)) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root284 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d q0 q1) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d (T.d q0 q1) q2) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root285 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) q0 q1)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root286 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.c q0 (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.c (T.d q0 q1) (T.d q0 q1) q2) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root287 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) q0 x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root288 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.d q0 q1) q2) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.r (T.c (T.c q2 q0 q1) q0 q1) (T.d q0 q1)) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root289 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.r (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2)) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root290 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d q0 q1) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root291 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.r (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1) (T.d q0 q1)) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root292 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) x2) (T.d x0 x1))) := by
  cases he

theorem peak21_root293 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.r (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) x2) (T.d x0 x1))) := by
  cases he

end submission.Austin5837

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak21_root294 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.m q0 q1) q1)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.r q1 q0))) := by
  cases he

theorem peak21_root295 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.r q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d q0 q1))) := by
  cases he

theorem peak21_root296 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.d q1 q2))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c q0 q1 q2))) := by
  cases he

theorem peak21_root297 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.c q1 q0 q2))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) q1)) := by
  cases he

theorem peak21_root298 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.r q0 q1) q0)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.r q0 (T.m q1 q0)))) := by
  cases he

theorem peak21_root299 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d q0 q1) (T.r q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.r (T.r q0 q1) q0))) := by
  cases he

theorem peak21_root300 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.r (T.d q0 q1) q2)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.c q2 q0 q1) q0 q1))) := by
  cases he

theorem peak21_root301 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.c q0 q1 q2))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.r (T.c q0 q1 q2) q1))) := by
  cases he

theorem peak21_root302 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.r (T.c q0 q0 q1) q0)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) q0)) := by
  cases he

theorem peak21_root303 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.c q0 q0 q1) q0)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d (T.c q0 q0 q1) q0))) := by
  cases he

theorem peak21_root304 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.c q0 q0 q1) q0) q0)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.r q0 (T.c q0 q0 q1)))) := by
  cases he

theorem peak21_root305 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d q0 q1) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d (T.d q0 q1) q2))) := by
  cases he

theorem peak21_root306 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) q0 q1)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) := by
  cases he

theorem peak21_root307 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.c q0 (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d q0 q1) (T.d q0 q1) q2))) := by
  cases he

theorem peak21_root308 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) q0)) := by
  cases he

theorem peak21_root309 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.d q0 q1) q2) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.r (T.c (T.c q2 q0 q1) q0 q1) (T.d q0 q1)))) := by
  cases he

theorem peak21_root310 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.r (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2)))) := by
  cases he

theorem peak21_root311 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d q0 q1) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)))) := by
  cases he

theorem peak21_root312 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.r (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1) (T.d q0 q1)))) := by
  cases he

theorem peak21_root313 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0))) := by
  cases he

theorem peak21_root314 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.r (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))))) := by
  cases he

end submission.Austin5837

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak21_context_1111 {x0 x1 x2 u : T} (h : Step (T.d x0 x1) u) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c u (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
    · rw [ho]
      exact peak21_root84 he
    · rw [ho]
      exact peak21_root85 he
    · rw [ho]
      exact peak21_root86 he
    · rw [ho]
      exact peak21_root87 he
    · rw [ho]
      exact peak21_root88 he
    · rw [ho]
      exact peak21_root89 he
    · rw [ho]
      exact peak21_root90 he
    · rw [ho]
      exact peak21_root91 he
    · rw [ho]
      exact peak21_root92 he
    · rw [ho]
      exact peak21_root93 he
    · rw [ho]
      exact peak21_root94 he
    · rw [ho]
      exact peak21_root95 he
    · rw [ho]
      exact peak21_root96 he
    · rw [ho]
      exact peak21_root97 he
    · rw [ho]
      exact peak21_root98 he
    · rw [ho]
      exact peak21_root99 he
    · rw [ho]
      exact peak21_root100 he
    · rw [ho]
      exact peak21_root101 he
    · rw [ho]
      exact peak21_root102 he
    · rw [ho]
      exact peak21_root103 he
    · rw [ho]
      exact peak21_root104 he
  | @leftD _ t4 _ h4 =>
    exact ⟨(T.r (T.c (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.d t4 x1)) (T.d (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.d t4 x1))), (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h4)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.secondC (T.d t4 x1) x2 (Step.leftD x1 h4)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.secondC (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h4)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.secondC (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.d x0 x1) (Step.secondC (T.d t4 x1) x2 (Step.leftD x1 h4)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.thirdC (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.c (T.d t4 x1) (T.d t4 x1) x2) (Step.leftD x1 h4))) (Steps.cons (Step.rightR (T.c (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.d t4 x1)) (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h4)))) (Steps.cons (Step.rightR (T.c (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.d t4 x1)) (Step.leftD (T.d x0 x1) (Step.secondC (T.d t4 x1) x2 (Step.leftD x1 h4)))) (Steps.cons (Step.rightR (T.c (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.d t4 x1)) (Step.rightD (T.c (T.d t4 x1) (T.d t4 x1) x2) (Step.leftD x1 h4))) (Steps.refl _))))))))), (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.secondC (T.d t4 x1) x2 (Step.leftD x1 h4))))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD x0 (Step.rightD (T.c (T.d t4 x1) (T.d t4 x1) x2) (Step.leftD x1 h4)))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.rightD (T.d (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.d t4 x1)) h4)) (Steps.cons (Step.right (T.d (T.d (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.d t4 x1)) t4) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h4)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.d t4 x1)) t4) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.secondC (T.d t4 x1) x2 (Step.leftD x1 h4)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.d t4 x1)) t4) (Step.secondC (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h4)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.d t4 x1)) t4) (Step.secondC (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.d x0 x1) (Step.secondC (T.d t4 x1) x2 (Step.leftD x1 h4)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.d t4 x1)) t4) (Step.thirdC (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.c (T.d t4 x1) (T.d t4 x1) x2) (Step.leftD x1 h4))) (Steps.cons (Step.root (Root.r21 t4 x1 x2)) (Steps.refl _))))))))))⟩
  | @rightD _ _ t4 h4 =>
    exact ⟨(T.r (T.c (T.c (T.d x0 t4) (T.d x0 t4) x2) (T.c (T.d x0 t4) (T.d x0 t4) x2) (T.d x0 t4)) (T.d (T.c (T.d x0 t4) (T.d x0 t4) x2) (T.d x0 t4))), (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h4)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.secondC (T.d x0 t4) x2 (Step.rightD x0 h4)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.secondC (T.c (T.d x0 t4) (T.d x0 t4) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h4)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.secondC (T.c (T.d x0 t4) (T.d x0 t4) x2) (T.d x0 x1) (Step.secondC (T.d x0 t4) x2 (Step.rightD x0 h4)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.thirdC (T.c (T.d x0 t4) (T.d x0 t4) x2) (T.c (T.d x0 t4) (T.d x0 t4) x2) (Step.rightD x0 h4))) (Steps.cons (Step.rightR (T.c (T.c (T.d x0 t4) (T.d x0 t4) x2) (T.c (T.d x0 t4) (T.d x0 t4) x2) (T.d x0 t4)) (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h4)))) (Steps.cons (Step.rightR (T.c (T.c (T.d x0 t4) (T.d x0 t4) x2) (T.c (T.d x0 t4) (T.d x0 t4) x2) (T.d x0 t4)) (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t4) x2 (Step.rightD x0 h4)))) (Steps.cons (Step.rightR (T.c (T.c (T.d x0 t4) (T.d x0 t4) x2) (T.c (T.d x0 t4) (T.d x0 t4) x2) (T.d x0 t4)) (Step.rightD (T.c (T.d x0 t4) (T.d x0 t4) x2) (Step.rightD x0 h4))) (Steps.refl _))))))))), (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t4) x2 (Step.rightD x0 h4))))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD x0 (Step.rightD (T.c (T.d x0 t4) (T.d x0 t4) x2) (Step.rightD x0 h4)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d x0 t4) (T.d x0 t4) x2) (T.d x0 t4)) x0) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h4)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d x0 t4) (T.d x0 t4) x2) (T.d x0 t4)) x0) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.secondC (T.d x0 t4) x2 (Step.rightD x0 h4)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d x0 t4) (T.d x0 t4) x2) (T.d x0 t4)) x0) (Step.secondC (T.c (T.d x0 t4) (T.d x0 t4) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h4)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d x0 t4) (T.d x0 t4) x2) (T.d x0 t4)) x0) (Step.secondC (T.c (T.d x0 t4) (T.d x0 t4) x2) (T.d x0 x1) (Step.secondC (T.d x0 t4) x2 (Step.rightD x0 h4)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d x0 t4) (T.d x0 t4) x2) (T.d x0 t4)) x0) (Step.thirdC (T.c (T.d x0 t4) (T.d x0 t4) x2) (T.c (T.d x0 t4) (T.d x0 t4) x2) (Step.rightD x0 h4))) (Steps.cons (Step.root (Root.r21 x0 t4 x2)) (Steps.refl _)))))))))⟩
end submission.Austin5837

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak21_context_1112 {x0 x1 x2 u : T} (h : Step (T.d x0 x1) u) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) u x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
    · rw [ho]
      exact peak21_root105 he
    · rw [ho]
      exact peak21_root106 he
    · rw [ho]
      exact peak21_root107 he
    · rw [ho]
      exact peak21_root108 he
    · rw [ho]
      exact peak21_root109 he
    · rw [ho]
      exact peak21_root110 he
    · rw [ho]
      exact peak21_root111 he
    · rw [ho]
      exact peak21_root112 he
    · rw [ho]
      exact peak21_root113 he
    · rw [ho]
      exact peak21_root114 he
    · rw [ho]
      exact peak21_root115 he
    · rw [ho]
      exact peak21_root116 he
    · rw [ho]
      exact peak21_root117 he
    · rw [ho]
      exact peak21_root118 he
    · rw [ho]
      exact peak21_root119 he
    · rw [ho]
      exact peak21_root120 he
    · rw [ho]
      exact peak21_root121 he
    · rw [ho]
      exact peak21_root122 he
    · rw [ho]
      exact peak21_root123 he
    · rw [ho]
      exact peak21_root124 he
    · rw [ho]
      exact peak21_root125 he
  | @leftD _ t4 _ h4 =>
    exact ⟨(T.r (T.c (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.d t4 x1)) (T.d (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.d t4 x1))), (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h4)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.secondC (T.d t4 x1) x2 (Step.leftD x1 h4)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.secondC (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h4)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.secondC (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.d x0 x1) (Step.secondC (T.d t4 x1) x2 (Step.leftD x1 h4)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.thirdC (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.c (T.d t4 x1) (T.d t4 x1) x2) (Step.leftD x1 h4))) (Steps.cons (Step.rightR (T.c (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.d t4 x1)) (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h4)))) (Steps.cons (Step.rightR (T.c (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.d t4 x1)) (Step.leftD (T.d x0 x1) (Step.secondC (T.d t4 x1) x2 (Step.leftD x1 h4)))) (Steps.cons (Step.rightR (T.c (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.d t4 x1)) (Step.rightD (T.c (T.d t4 x1) (T.d t4 x1) x2) (Step.leftD x1 h4))) (Steps.refl _))))))))), (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.firstC (T.d t4 x1) x2 (Step.leftD x1 h4))))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD x0 (Step.rightD (T.c (T.d t4 x1) (T.d t4 x1) x2) (Step.leftD x1 h4)))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.rightD (T.d (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.d t4 x1)) h4)) (Steps.cons (Step.right (T.d (T.d (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.d t4 x1)) t4) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h4)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.d t4 x1)) t4) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.secondC (T.d t4 x1) x2 (Step.leftD x1 h4)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.d t4 x1)) t4) (Step.secondC (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h4)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.d t4 x1)) t4) (Step.secondC (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.d x0 x1) (Step.secondC (T.d t4 x1) x2 (Step.leftD x1 h4)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.d t4 x1)) t4) (Step.thirdC (T.c (T.d t4 x1) (T.d t4 x1) x2) (T.c (T.d t4 x1) (T.d t4 x1) x2) (Step.leftD x1 h4))) (Steps.cons (Step.root (Root.r21 t4 x1 x2)) (Steps.refl _))))))))))⟩
  | @rightD _ _ t4 h4 =>
    exact ⟨(T.r (T.c (T.c (T.d x0 t4) (T.d x0 t4) x2) (T.c (T.d x0 t4) (T.d x0 t4) x2) (T.d x0 t4)) (T.d (T.c (T.d x0 t4) (T.d x0 t4) x2) (T.d x0 t4))), (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h4)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.secondC (T.d x0 t4) x2 (Step.rightD x0 h4)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.secondC (T.c (T.d x0 t4) (T.d x0 t4) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h4)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.secondC (T.c (T.d x0 t4) (T.d x0 t4) x2) (T.d x0 x1) (Step.secondC (T.d x0 t4) x2 (Step.rightD x0 h4)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.thirdC (T.c (T.d x0 t4) (T.d x0 t4) x2) (T.c (T.d x0 t4) (T.d x0 t4) x2) (Step.rightD x0 h4))) (Steps.cons (Step.rightR (T.c (T.c (T.d x0 t4) (T.d x0 t4) x2) (T.c (T.d x0 t4) (T.d x0 t4) x2) (T.d x0 t4)) (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h4)))) (Steps.cons (Step.rightR (T.c (T.c (T.d x0 t4) (T.d x0 t4) x2) (T.c (T.d x0 t4) (T.d x0 t4) x2) (T.d x0 t4)) (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t4) x2 (Step.rightD x0 h4)))) (Steps.cons (Step.rightR (T.c (T.c (T.d x0 t4) (T.d x0 t4) x2) (T.c (T.d x0 t4) (T.d x0 t4) x2) (T.d x0 t4)) (Step.rightD (T.c (T.d x0 t4) (T.d x0 t4) x2) (Step.rightD x0 h4))) (Steps.refl _))))))))), (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 t4) x2 (Step.rightD x0 h4))))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD x0 (Step.rightD (T.c (T.d x0 t4) (T.d x0 t4) x2) (Step.rightD x0 h4)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d x0 t4) (T.d x0 t4) x2) (T.d x0 t4)) x0) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h4)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d x0 t4) (T.d x0 t4) x2) (T.d x0 t4)) x0) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.secondC (T.d x0 t4) x2 (Step.rightD x0 h4)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d x0 t4) (T.d x0 t4) x2) (T.d x0 t4)) x0) (Step.secondC (T.c (T.d x0 t4) (T.d x0 t4) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h4)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d x0 t4) (T.d x0 t4) x2) (T.d x0 t4)) x0) (Step.secondC (T.c (T.d x0 t4) (T.d x0 t4) x2) (T.d x0 x1) (Step.secondC (T.d x0 t4) x2 (Step.rightD x0 h4)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d x0 t4) (T.d x0 t4) x2) (T.d x0 t4)) x0) (Step.thirdC (T.c (T.d x0 t4) (T.d x0 t4) x2) (T.c (T.d x0 t4) (T.d x0 t4) x2) (Step.rightD x0 h4))) (Steps.cons (Step.root (Root.r21 x0 t4 x2)) (Steps.refl _)))))))))⟩
end submission.Austin5837

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak21_context_111 {x0 x1 x2 u : T} (h : Step (T.c (T.d x0 x1) (T.d x0 x1) x2) u) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d u (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
    · rw [ho]
      exact peak21_root63 he
    · rw [ho]
      exact peak21_root64 he
    · rw [ho]
      exact peak21_root65 he
    · rw [ho]
      exact peak21_root66 he
    · rw [ho]
      exact peak21_root67 he
    · rw [ho]
      exact peak21_root68 he
    · rw [ho]
      exact peak21_root69 he
    · rw [ho]
      exact peak21_root70 he
    · rw [ho]
      exact peak21_root71 he
    · rw [ho]
      exact peak21_root72 he
    · rw [ho]
      exact peak21_root73 he
    · rw [ho]
      exact peak21_root74 he
    · rw [ho]
      exact peak21_root75 he
    · rw [ho]
      exact peak21_root76 he
    · rw [ho]
      exact peak21_root77 he
    · rw [ho]
      exact peak21_root78 he
    · rw [ho]
      exact peak21_root79 he
    · rw [ho]
      exact peak21_root80 he
    · rw [ho]
      exact peak21_root81 he
    · rw [ho]
      exact peak21_root82 he
    · rw [ho]
      exact peak21_root83 he
  | @firstC _ t3 _ _ h3 =>
    exact peak21_context_1111 h3
  | @secondC _ _ t3 _ h3 =>
    exact peak21_context_1112 h3
  | @thirdC _ _ _ t3 h3 =>
    exact ⟨(T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) t3) (T.c (T.d x0 x1) (T.d x0 x1) t3) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) t3) (T.d x0 x1))), (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.thirdC (T.d x0 x1) (T.d x0 x1) h3))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.secondC (T.c (T.d x0 x1) (T.d x0 x1) t3) (T.d x0 x1) (Step.thirdC (T.d x0 x1) (T.d x0 x1) h3))) (Steps.cons (Step.rightR (T.c (T.c (T.d x0 x1) (T.d x0 x1) t3) (T.c (T.d x0 x1) (T.d x0 x1) t3) (T.d x0 x1)) (Step.leftD (T.d x0 x1) (Step.thirdC (T.d x0 x1) (T.d x0 x1) h3))) (Steps.refl _)))), (Steps.cons (Step.right (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) t3) (T.d x0 x1)) x0) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.thirdC (T.d x0 x1) (T.d x0 x1) h3))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) t3) (T.d x0 x1)) x0) (Step.secondC (T.c (T.d x0 x1) (T.d x0 x1) t3) (T.d x0 x1) (Step.thirdC (T.d x0 x1) (T.d x0 x1) h3))) (Steps.cons (Step.root (Root.r21 x0 x1 t3)) (Steps.refl _))))⟩
end submission.Austin5837

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak21_context_112 {x0 x1 x2 u : T} (h : Step (T.d x0 x1) u) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) u) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
    · rw [ho]
      exact peak21_root126 he
    · rw [ho]
      exact peak21_root127 he
    · rw [ho]
      exact peak21_root128 he
    · rw [ho]
      exact peak21_root129 he
    · rw [ho]
      exact peak21_root130 he
    · rw [ho]
      exact peak21_root131 he
    · rw [ho]
      exact peak21_root132 he
    · rw [ho]
      exact peak21_root133 he
    · rw [ho]
      exact peak21_root134 he
    · rw [ho]
      exact peak21_root135 he
    · rw [ho]
      exact peak21_root136 he
    · rw [ho]
      exact peak21_root137 he
    · rw [ho]
      exact peak21_root138 he
    · rw [ho]
      exact peak21_root139 he
    · rw [ho]
      exact peak21_root140 he
    · rw [ho]
      exact peak21_root141 he
    · rw [ho]
      exact peak21_root142 he
    · rw [ho]
      exact peak21_root143 he
    · rw [ho]
      exact peak21_root144 he
    · rw [ho]
      exact peak21_root145 he
    · rw [ho]
      exact peak21_root146 he
  | @leftD _ t3 _ h3 =>
    exact ⟨(T.r (T.c (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1))), (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.secondC (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.secondC (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.thirdC (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.c (T.d t3 x1) (T.d t3 x1) x2) (Step.leftD x1 h3))) (Steps.cons (Step.rightR (T.c (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.rightR (T.c (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (Step.leftD (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.rightR (T.c (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (Step.rightD (T.c (T.d t3 x1) (T.d t3 x1) x2) (Step.leftD x1 h3))) (Steps.refl _))))))))), (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD x0 (Step.leftD (T.d t3 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3))))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD x0 (Step.leftD (T.d t3 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3))))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.rightD (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) h3)) (Steps.cons (Step.right (T.d (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) t3) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) t3) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) t3) (Step.secondC (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) t3) (Step.secondC (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) t3) (Step.thirdC (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.c (T.d t3 x1) (T.d t3 x1) x2) (Step.leftD x1 h3))) (Steps.cons (Step.root (Root.r21 t3 x1 x2)) (Steps.refl _))))))))))⟩
  | @rightD _ _ t3 h3 =>
    exact ⟨(T.r (T.c (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3))), (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.secondC (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.secondC (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.thirdC (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.c (T.d x0 t3) (T.d x0 t3) x2) (Step.rightD x0 h3))) (Steps.cons (Step.rightR (T.c (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.rightR (T.c (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.rightR (T.c (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (Step.rightD (T.c (T.d x0 t3) (T.d x0 t3) x2) (Step.rightD x0 h3))) (Steps.refl _))))))))), (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD x0 (Step.leftD (T.d x0 t3) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3))))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD x0 (Step.leftD (T.d x0 t3) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3))))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) x0) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) x0) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) x0) (Step.secondC (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) x0) (Step.secondC (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) x0) (Step.thirdC (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.c (T.d x0 t3) (T.d x0 t3) x2) (Step.rightD x0 h3))) (Steps.cons (Step.root (Root.r21 x0 t3 x2)) (Steps.refl _)))))))))⟩
end submission.Austin5837

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak21_context_11 {x0 x1 x2 u : T} (h : Step (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) u) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d u x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
    · rw [ho]
      exact peak21_root42 he
    · rw [ho]
      exact peak21_root43 he
    · rw [ho]
      exact peak21_root44 he
    · rw [ho]
      exact peak21_root45 he
    · rw [ho]
      exact peak21_root46 he
    · rw [ho]
      exact peak21_root47 he
    · rw [ho]
      exact peak21_root48 he
    · rw [ho]
      exact peak21_root49 he
    · rw [ho]
      exact peak21_root50 he
    · rw [ho]
      exact peak21_root51 he
    · rw [ho]
      exact peak21_root52 he
    · rw [ho]
      exact peak21_root53 he
    · rw [ho]
      exact peak21_root54 he
    · rw [ho]
      exact peak21_root55 he
    · rw [ho]
      exact peak21_root56 he
    · rw [ho]
      exact peak21_root57 he
    · rw [ho]
      exact peak21_root58 he
    · rw [ho]
      exact peak21_root59 he
    · rw [ho]
      exact peak21_root60 he
    · rw [ho]
      exact peak21_root61 he
    · rw [ho]
      exact peak21_root62 he
  | @leftD _ t2 _ h2 =>
    exact peak21_context_111 h2
  | @rightD _ _ t2 h2 =>
    exact peak21_context_112 h2
end submission.Austin5837

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak21_context_1 {x0 x1 x2 u : T} (h : Step (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) u) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m u (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
    · rw [ho]
      exact peak21_root21 he
    · rw [ho]
      exact peak21_root22 he
    · rw [ho]
      exact peak21_root23 he
    · rw [ho]
      exact peak21_root24 he
    · rw [ho]
      exact peak21_root25 he
    · rw [ho]
      exact peak21_root26 he
    · rw [ho]
      exact peak21_root27 he
    · rw [ho]
      exact peak21_root28 he
    · rw [ho]
      exact peak21_root29 he
    · rw [ho]
      exact peak21_root30 he
    · rw [ho]
      exact peak21_root31 he
    · rw [ho]
      exact peak21_root32 he
    · rw [ho]
      exact peak21_root33 he
    · rw [ho]
      exact peak21_root34 he
    · rw [ho]
      exact peak21_root35 he
    · rw [ho]
      exact peak21_root36 he
    · rw [ho]
      exact peak21_root37 he
    · rw [ho]
      exact peak21_root38 he
    · rw [ho]
      exact peak21_root39 he
    · rw [ho]
      exact peak21_root40 he
    · rw [ho]
      exact peak21_root41 he
  | @leftD _ t1 _ h1 =>
    exact peak21_context_11 h1
  | @rightD _ _ t1 h1 =>
    exact ⟨(T.r (T.c (T.c (T.d t1 x1) (T.d t1 x1) x2) (T.c (T.d t1 x1) (T.d t1 x1) x2) (T.d t1 x1)) (T.d (T.c (T.d t1 x1) (T.d t1 x1) x2) (T.d t1 x1))), (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h1)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.secondC (T.d t1 x1) x2 (Step.leftD x1 h1)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.secondC (T.c (T.d t1 x1) (T.d t1 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h1)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.secondC (T.c (T.d t1 x1) (T.d t1 x1) x2) (T.d x0 x1) (Step.secondC (T.d t1 x1) x2 (Step.leftD x1 h1)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.thirdC (T.c (T.d t1 x1) (T.d t1 x1) x2) (T.c (T.d t1 x1) (T.d t1 x1) x2) (Step.leftD x1 h1))) (Steps.cons (Step.rightR (T.c (T.c (T.d t1 x1) (T.d t1 x1) x2) (T.c (T.d t1 x1) (T.d t1 x1) x2) (T.d t1 x1)) (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h1)))) (Steps.cons (Step.rightR (T.c (T.c (T.d t1 x1) (T.d t1 x1) x2) (T.c (T.d t1 x1) (T.d t1 x1) x2) (T.d t1 x1)) (Step.leftD (T.d x0 x1) (Step.secondC (T.d t1 x1) x2 (Step.leftD x1 h1)))) (Steps.cons (Step.rightR (T.c (T.c (T.d t1 x1) (T.d t1 x1) x2) (T.c (T.d t1 x1) (T.d t1 x1) x2) (T.d t1 x1)) (Step.rightD (T.c (T.d t1 x1) (T.d t1 x1) x2) (Step.leftD x1 h1))) (Steps.refl _))))))))), (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD t1 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h1))))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD t1 (Step.leftD (T.d x0 x1) (Step.secondC (T.d t1 x1) x2 (Step.leftD x1 h1))))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD t1 (Step.rightD (T.c (T.d t1 x1) (T.d t1 x1) x2) (Step.leftD x1 h1)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d t1 x1) (T.d t1 x1) x2) (T.d t1 x1)) t1) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h1)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d t1 x1) (T.d t1 x1) x2) (T.d t1 x1)) t1) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.secondC (T.d t1 x1) x2 (Step.leftD x1 h1)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d t1 x1) (T.d t1 x1) x2) (T.d t1 x1)) t1) (Step.secondC (T.c (T.d t1 x1) (T.d t1 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h1)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d t1 x1) (T.d t1 x1) x2) (T.d t1 x1)) t1) (Step.secondC (T.c (T.d t1 x1) (T.d t1 x1) x2) (T.d x0 x1) (Step.secondC (T.d t1 x1) x2 (Step.leftD x1 h1)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d t1 x1) (T.d t1 x1) x2) (T.d t1 x1)) t1) (Step.thirdC (T.c (T.d t1 x1) (T.d t1 x1) x2) (T.c (T.d t1 x1) (T.d t1 x1) x2) (Step.leftD x1 h1))) (Steps.cons (Step.root (Root.r21 t1 x1 x2)) (Steps.refl _))))))))))⟩
end submission.Austin5837

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak21_context_211 {x0 x1 x2 u : T} (h : Step (T.d x0 x1) u) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c u (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
    · rw [ho]
      exact peak21_root189 he
    · rw [ho]
      exact peak21_root190 he
    · rw [ho]
      exact peak21_root191 he
    · rw [ho]
      exact peak21_root192 he
    · rw [ho]
      exact peak21_root193 he
    · rw [ho]
      exact peak21_root194 he
    · rw [ho]
      exact peak21_root195 he
    · rw [ho]
      exact peak21_root196 he
    · rw [ho]
      exact peak21_root197 he
    · rw [ho]
      exact peak21_root198 he
    · rw [ho]
      exact peak21_root199 he
    · rw [ho]
      exact peak21_root200 he
    · rw [ho]
      exact peak21_root201 he
    · rw [ho]
      exact peak21_root202 he
    · rw [ho]
      exact peak21_root203 he
    · rw [ho]
      exact peak21_root204 he
    · rw [ho]
      exact peak21_root205 he
    · rw [ho]
      exact peak21_root206 he
    · rw [ho]
      exact peak21_root207 he
    · rw [ho]
      exact peak21_root208 he
    · rw [ho]
      exact peak21_root209 he
  | @leftD _ t3 _ h3 =>
    exact ⟨(T.r (T.c (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1))), (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.secondC (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.secondC (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.thirdC (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.c (T.d t3 x1) (T.d t3 x1) x2) (Step.leftD x1 h3))) (Steps.cons (Step.rightR (T.c (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.rightR (T.c (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (Step.leftD (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.rightR (T.c (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (Step.rightD (T.c (T.d t3 x1) (T.d t3 x1) x2) (Step.leftD x1 h3))) (Steps.refl _))))))))), (Steps.cons (Step.left (T.c (T.c (T.d t3 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3))))) (Steps.cons (Step.left (T.c (T.c (T.d t3 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3))))) (Steps.cons (Step.left (T.c (T.c (T.d t3 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD x0 (Step.rightD (T.c (T.d t3 x1) (T.d t3 x1) x2) (Step.leftD x1 h3)))) (Steps.cons (Step.left (T.c (T.c (T.d t3 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.rightD (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) h3)) (Steps.cons (Step.right (T.d (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) t3) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) t3) (Step.secondC (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) t3) (Step.secondC (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) t3) (Step.thirdC (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.c (T.d t3 x1) (T.d t3 x1) x2) (Step.leftD x1 h3))) (Steps.cons (Step.root (Root.r21 t3 x1 x2)) (Steps.refl _))))))))))⟩
  | @rightD _ _ t3 h3 =>
    exact ⟨(T.r (T.c (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3))), (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.secondC (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.secondC (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.thirdC (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.c (T.d x0 t3) (T.d x0 t3) x2) (Step.rightD x0 h3))) (Steps.cons (Step.rightR (T.c (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.rightR (T.c (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.rightR (T.c (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (Step.rightD (T.c (T.d x0 t3) (T.d x0 t3) x2) (Step.rightD x0 h3))) (Steps.refl _))))))))), (Steps.cons (Step.left (T.c (T.c (T.d x0 t3) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3))))) (Steps.cons (Step.left (T.c (T.c (T.d x0 t3) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3))))) (Steps.cons (Step.left (T.c (T.c (T.d x0 t3) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD x0 (Step.rightD (T.c (T.d x0 t3) (T.d x0 t3) x2) (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) x0) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) x0) (Step.secondC (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) x0) (Step.secondC (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) x0) (Step.thirdC (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.c (T.d x0 t3) (T.d x0 t3) x2) (Step.rightD x0 h3))) (Steps.cons (Step.root (Root.r21 x0 t3 x2)) (Steps.refl _)))))))))⟩
end submission.Austin5837

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak21_context_212 {x0 x1 x2 u : T} (h : Step (T.d x0 x1) u) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) u x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
    · rw [ho]
      exact peak21_root210 he
    · rw [ho]
      exact peak21_root211 he
    · rw [ho]
      exact peak21_root212 he
    · rw [ho]
      exact peak21_root213 he
    · rw [ho]
      exact peak21_root214 he
    · rw [ho]
      exact peak21_root215 he
    · rw [ho]
      exact peak21_root216 he
    · rw [ho]
      exact peak21_root217 he
    · rw [ho]
      exact peak21_root218 he
    · rw [ho]
      exact peak21_root219 he
    · rw [ho]
      exact peak21_root220 he
    · rw [ho]
      exact peak21_root221 he
    · rw [ho]
      exact peak21_root222 he
    · rw [ho]
      exact peak21_root223 he
    · rw [ho]
      exact peak21_root224 he
    · rw [ho]
      exact peak21_root225 he
    · rw [ho]
      exact peak21_root226 he
    · rw [ho]
      exact peak21_root227 he
    · rw [ho]
      exact peak21_root228 he
    · rw [ho]
      exact peak21_root229 he
    · rw [ho]
      exact peak21_root230 he
  | @leftD _ t3 _ h3 =>
    exact ⟨(T.r (T.c (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1))), (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.secondC (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.secondC (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.thirdC (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.c (T.d t3 x1) (T.d t3 x1) x2) (Step.leftD x1 h3))) (Steps.cons (Step.rightR (T.c (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.rightR (T.c (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (Step.leftD (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.rightR (T.c (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (Step.rightD (T.c (T.d t3 x1) (T.d t3 x1) x2) (Step.leftD x1 h3))) (Steps.refl _))))))))), (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d t3 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3))))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d t3 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3))))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d t3 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD x0 (Step.rightD (T.c (T.d t3 x1) (T.d t3 x1) x2) (Step.leftD x1 h3)))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d t3 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.rightD (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) h3)) (Steps.cons (Step.right (T.d (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) t3) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.firstC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) t3) (Step.secondC (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) t3) (Step.secondC (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) t3) (Step.thirdC (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.c (T.d t3 x1) (T.d t3 x1) x2) (Step.leftD x1 h3))) (Steps.cons (Step.root (Root.r21 t3 x1 x2)) (Steps.refl _))))))))))⟩
  | @rightD _ _ t3 h3 =>
    exact ⟨(T.r (T.c (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3))), (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.secondC (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.secondC (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.thirdC (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.c (T.d x0 t3) (T.d x0 t3) x2) (Step.rightD x0 h3))) (Steps.cons (Step.rightR (T.c (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.rightR (T.c (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.rightR (T.c (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (Step.rightD (T.c (T.d x0 t3) (T.d x0 t3) x2) (Step.rightD x0 h3))) (Steps.refl _))))))))), (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 t3) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3))))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 t3) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3))))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 t3) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD x0 (Step.rightD (T.c (T.d x0 t3) (T.d x0 t3) x2) (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) x0) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) x0) (Step.secondC (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) x0) (Step.secondC (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) x0) (Step.thirdC (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.c (T.d x0 t3) (T.d x0 t3) x2) (Step.rightD x0 h3))) (Steps.cons (Step.root (Root.r21 x0 t3 x2)) (Steps.refl _)))))))))⟩
end submission.Austin5837

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak21_context_21 {x0 x1 x2 u : T} (h : Step (T.c (T.d x0 x1) (T.d x0 x1) x2) u) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c u (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
    · rw [ho]
      exact peak21_root168 he
    · rw [ho]
      exact peak21_root169 he
    · rw [ho]
      exact peak21_root170 he
    · rw [ho]
      exact peak21_root171 he
    · rw [ho]
      exact peak21_root172 he
    · rw [ho]
      exact peak21_root173 he
    · rw [ho]
      exact peak21_root174 he
    · rw [ho]
      exact peak21_root175 he
    · rw [ho]
      exact peak21_root176 he
    · rw [ho]
      exact peak21_root177 he
    · rw [ho]
      exact peak21_root178 he
    · rw [ho]
      exact peak21_root179 he
    · rw [ho]
      exact peak21_root180 he
    · rw [ho]
      exact peak21_root181 he
    · rw [ho]
      exact peak21_root182 he
    · rw [ho]
      exact peak21_root183 he
    · rw [ho]
      exact peak21_root184 he
    · rw [ho]
      exact peak21_root185 he
    · rw [ho]
      exact peak21_root186 he
    · rw [ho]
      exact peak21_root187 he
    · rw [ho]
      exact peak21_root188 he
  | @firstC _ t2 _ _ h2 =>
    exact peak21_context_211 h2
  | @secondC _ _ t2 _ h2 =>
    exact peak21_context_212 h2
  | @thirdC _ _ _ t2 h2 =>
    exact ⟨(T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) t2) (T.c (T.d x0 x1) (T.d x0 x1) t2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) t2) (T.d x0 x1))), (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.thirdC (T.d x0 x1) (T.d x0 x1) h2))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.secondC (T.c (T.d x0 x1) (T.d x0 x1) t2) (T.d x0 x1) (Step.thirdC (T.d x0 x1) (T.d x0 x1) h2))) (Steps.cons (Step.rightR (T.c (T.c (T.d x0 x1) (T.d x0 x1) t2) (T.c (T.d x0 x1) (T.d x0 x1) t2) (T.d x0 x1)) (Step.leftD (T.d x0 x1) (Step.thirdC (T.d x0 x1) (T.d x0 x1) h2))) (Steps.refl _)))), (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) t2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.thirdC (T.d x0 x1) (T.d x0 x1) h2)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) t2) (T.d x0 x1)) x0) (Step.secondC (T.c (T.d x0 x1) (T.d x0 x1) t2) (T.d x0 x1) (Step.thirdC (T.d x0 x1) (T.d x0 x1) h2))) (Steps.cons (Step.root (Root.r21 x0 x1 t2)) (Steps.refl _))))⟩
end submission.Austin5837

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak21_context_221 {x0 x1 x2 u : T} (h : Step (T.d x0 x1) u) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c u (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
    · rw [ho]
      exact peak21_root252 he
    · rw [ho]
      exact peak21_root253 he
    · rw [ho]
      exact peak21_root254 he
    · rw [ho]
      exact peak21_root255 he
    · rw [ho]
      exact peak21_root256 he
    · rw [ho]
      exact peak21_root257 he
    · rw [ho]
      exact peak21_root258 he
    · rw [ho]
      exact peak21_root259 he
    · rw [ho]
      exact peak21_root260 he
    · rw [ho]
      exact peak21_root261 he
    · rw [ho]
      exact peak21_root262 he
    · rw [ho]
      exact peak21_root263 he
    · rw [ho]
      exact peak21_root264 he
    · rw [ho]
      exact peak21_root265 he
    · rw [ho]
      exact peak21_root266 he
    · rw [ho]
      exact peak21_root267 he
    · rw [ho]
      exact peak21_root268 he
    · rw [ho]
      exact peak21_root269 he
    · rw [ho]
      exact peak21_root270 he
    · rw [ho]
      exact peak21_root271 he
    · rw [ho]
      exact peak21_root272 he
  | @leftD _ t3 _ h3 =>
    exact ⟨(T.r (T.c (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1))), (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.secondC (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.secondC (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.thirdC (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.c (T.d t3 x1) (T.d t3 x1) x2) (Step.leftD x1 h3))) (Steps.cons (Step.rightR (T.c (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.rightR (T.c (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (Step.leftD (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.rightR (T.c (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (Step.rightD (T.c (T.d t3 x1) (T.d t3 x1) x2) (Step.leftD x1 h3))) (Steps.refl _))))))))), (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d t3 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3))))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d t3 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3))))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d t3 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD x0 (Step.rightD (T.c (T.d t3 x1) (T.d t3 x1) x2) (Step.leftD x1 h3)))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d t3 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.rightD (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) h3)) (Steps.cons (Step.right (T.d (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) t3) (Step.firstC (T.c (T.d t3 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) t3) (Step.firstC (T.c (T.d t3 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) t3) (Step.secondC (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) t3) (Step.thirdC (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.c (T.d t3 x1) (T.d t3 x1) x2) (Step.leftD x1 h3))) (Steps.cons (Step.root (Root.r21 t3 x1 x2)) (Steps.refl _))))))))))⟩
  | @rightD _ _ t3 h3 =>
    exact ⟨(T.r (T.c (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3))), (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.secondC (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.secondC (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.thirdC (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.c (T.d x0 t3) (T.d x0 t3) x2) (Step.rightD x0 h3))) (Steps.cons (Step.rightR (T.c (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.rightR (T.c (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.rightR (T.c (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (Step.rightD (T.c (T.d x0 t3) (T.d x0 t3) x2) (Step.rightD x0 h3))) (Steps.refl _))))))))), (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 t3) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3))))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 t3) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3))))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 t3) (T.d x0 x1) x2) (T.d x0 x1)) (Step.leftD x0 (Step.rightD (T.c (T.d x0 t3) (T.d x0 t3) x2) (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) x0) (Step.firstC (T.c (T.d x0 t3) (T.d x0 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) x0) (Step.firstC (T.c (T.d x0 t3) (T.d x0 x1) x2) (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) x0) (Step.secondC (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) x0) (Step.thirdC (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.c (T.d x0 t3) (T.d x0 t3) x2) (Step.rightD x0 h3))) (Steps.cons (Step.root (Root.r21 x0 t3 x2)) (Steps.refl _)))))))))⟩
end submission.Austin5837

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak21_context_222 {x0 x1 x2 u : T} (h : Step (T.d x0 x1) u) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) u x2) (T.d x0 x1))) := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
    · rw [ho]
      exact peak21_root273 he
    · rw [ho]
      exact peak21_root274 he
    · rw [ho]
      exact peak21_root275 he
    · rw [ho]
      exact peak21_root276 he
    · rw [ho]
      exact peak21_root277 he
    · rw [ho]
      exact peak21_root278 he
    · rw [ho]
      exact peak21_root279 he
    · rw [ho]
      exact peak21_root280 he
    · rw [ho]
      exact peak21_root281 he
    · rw [ho]
      exact peak21_root282 he
    · rw [ho]
      exact peak21_root283 he
    · rw [ho]
      exact peak21_root284 he
    · rw [ho]
      exact peak21_root285 he
    · rw [ho]
      exact peak21_root286 he
    · rw [ho]
      exact peak21_root287 he
    · rw [ho]
      exact peak21_root288 he
    · rw [ho]
      exact peak21_root289 he
    · rw [ho]
      exact peak21_root290 he
    · rw [ho]
      exact peak21_root291 he
    · rw [ho]
      exact peak21_root292 he
    · rw [ho]
      exact peak21_root293 he
  | @leftD _ t3 _ h3 =>
    exact ⟨(T.r (T.c (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1))), (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.secondC (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.secondC (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.thirdC (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.c (T.d t3 x1) (T.d t3 x1) x2) (Step.leftD x1 h3))) (Steps.cons (Step.rightR (T.c (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.rightR (T.c (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (Step.leftD (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.rightR (T.c (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) (Step.rightD (T.c (T.d t3 x1) (T.d t3 x1) x2) (Step.leftD x1 h3))) (Steps.refl _))))))))), (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d t3 x1) x2) (T.d x0 x1)) (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3))))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d t3 x1) x2) (T.d x0 x1)) (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3))))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d t3 x1) x2) (T.d x0 x1)) (Step.leftD x0 (Step.rightD (T.c (T.d t3 x1) (T.d t3 x1) x2) (Step.leftD x1 h3)))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d t3 x1) x2) (T.d x0 x1)) (Step.rightD (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) h3)) (Steps.cons (Step.right (T.d (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) t3) (Step.firstC (T.c (T.d x0 x1) (T.d t3 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) t3) (Step.firstC (T.c (T.d x0 x1) (T.d t3 x1) x2) (T.d x0 x1) (Step.secondC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) t3) (Step.secondC (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d x0 x1) (Step.firstC (T.d t3 x1) x2 (Step.leftD x1 h3)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.d t3 x1)) t3) (Step.thirdC (T.c (T.d t3 x1) (T.d t3 x1) x2) (T.c (T.d t3 x1) (T.d t3 x1) x2) (Step.leftD x1 h3))) (Steps.cons (Step.root (Root.r21 t3 x1 x2)) (Steps.refl _))))))))))⟩
  | @rightD _ _ t3 h3 =>
    exact ⟨(T.r (T.c (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3))), (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.secondC (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.secondC (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.thirdC (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.c (T.d x0 t3) (T.d x0 t3) x2) (Step.rightD x0 h3))) (Steps.cons (Step.rightR (T.c (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.rightR (T.c (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.rightR (T.c (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) (Step.rightD (T.c (T.d x0 t3) (T.d x0 t3) x2) (Step.rightD x0 h3))) (Steps.refl _))))))))), (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 t3) x2) (T.d x0 x1)) (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3))))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 t3) x2) (T.d x0 x1)) (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3))))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 t3) x2) (T.d x0 x1)) (Step.leftD x0 (Step.rightD (T.c (T.d x0 t3) (T.d x0 t3) x2) (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) x0) (Step.firstC (T.c (T.d x0 x1) (T.d x0 t3) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) x0) (Step.firstC (T.c (T.d x0 x1) (T.d x0 t3) x2) (T.d x0 x1) (Step.secondC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) x0) (Step.secondC (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 x1) (Step.firstC (T.d x0 t3) x2 (Step.rightD x0 h3)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.d x0 t3)) x0) (Step.thirdC (T.c (T.d x0 t3) (T.d x0 t3) x2) (T.c (T.d x0 t3) (T.d x0 t3) x2) (Step.rightD x0 h3))) (Steps.cons (Step.root (Root.r21 x0 t3 x2)) (Steps.refl _)))))))))⟩
end submission.Austin5837

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak21_context_22 {x0 x1 x2 u : T} (h : Step (T.c (T.d x0 x1) (T.d x0 x1) x2) u) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) u (T.d x0 x1))) := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
    · rw [ho]
      exact peak21_root231 he
    · rw [ho]
      exact peak21_root232 he
    · rw [ho]
      exact peak21_root233 he
    · rw [ho]
      exact peak21_root234 he
    · rw [ho]
      exact peak21_root235 he
    · rw [ho]
      exact peak21_root236 he
    · rw [ho]
      exact peak21_root237 he
    · rw [ho]
      exact peak21_root238 he
    · rw [ho]
      exact peak21_root239 he
    · rw [ho]
      exact peak21_root240 he
    · rw [ho]
      exact peak21_root241 he
    · rw [ho]
      exact peak21_root242 he
    · rw [ho]
      exact peak21_root243 he
    · rw [ho]
      exact peak21_root244 he
    · rw [ho]
      exact peak21_root245 he
    · rw [ho]
      exact peak21_root246 he
    · rw [ho]
      exact peak21_root247 he
    · rw [ho]
      exact peak21_root248 he
    · rw [ho]
      exact peak21_root249 he
    · rw [ho]
      exact peak21_root250 he
    · rw [ho]
      exact peak21_root251 he
  | @firstC _ t2 _ _ h2 =>
    exact peak21_context_221 h2
  | @secondC _ _ t2 _ h2 =>
    exact peak21_context_222 h2
  | @thirdC _ _ _ t2 h2 =>
    exact ⟨(T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) t2) (T.c (T.d x0 x1) (T.d x0 x1) t2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) t2) (T.d x0 x1))), (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.thirdC (T.d x0 x1) (T.d x0 x1) h2))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.secondC (T.c (T.d x0 x1) (T.d x0 x1) t2) (T.d x0 x1) (Step.thirdC (T.d x0 x1) (T.d x0 x1) h2))) (Steps.cons (Step.rightR (T.c (T.c (T.d x0 x1) (T.d x0 x1) t2) (T.c (T.d x0 x1) (T.d x0 x1) t2) (T.d x0 x1)) (Step.leftD (T.d x0 x1) (Step.thirdC (T.d x0 x1) (T.d x0 x1) h2))) (Steps.refl _)))), (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) t2) (T.d x0 x1)) (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.thirdC (T.d x0 x1) (T.d x0 x1) h2)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) t2) (T.d x0 x1)) x0) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) t2) (T.d x0 x1) (Step.thirdC (T.d x0 x1) (T.d x0 x1) h2))) (Steps.cons (Step.root (Root.r21 x0 x1 t2)) (Steps.refl _))))⟩
end submission.Austin5837

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak21_context_23 {x0 x1 x2 u : T} (h : Step (T.d x0 x1) u) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) u)) := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
    · rw [ho]
      exact peak21_root294 he
    · rw [ho]
      exact peak21_root295 he
    · rw [ho]
      exact peak21_root296 he
    · rw [ho]
      exact peak21_root297 he
    · rw [ho]
      exact peak21_root298 he
    · rw [ho]
      exact peak21_root299 he
    · rw [ho]
      exact peak21_root300 he
    · rw [ho]
      exact peak21_root301 he
    · rw [ho]
      exact peak21_root302 he
    · rw [ho]
      exact peak21_root303 he
    · rw [ho]
      exact peak21_root304 he
    · rw [ho]
      exact peak21_root305 he
    · rw [ho]
      exact peak21_root306 he
    · rw [ho]
      exact peak21_root307 he
    · rw [ho]
      exact peak21_root308 he
    · rw [ho]
      exact peak21_root309 he
    · rw [ho]
      exact peak21_root310 he
    · rw [ho]
      exact peak21_root311 he
    · rw [ho]
      exact peak21_root312 he
    · rw [ho]
      exact peak21_root313 he
    · rw [ho]
      exact peak21_root314 he
  | @leftD _ t2 _ h2 =>
    exact ⟨(T.r (T.c (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.d t2 x1)) (T.d (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.d t2 x1))), (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h2)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.secondC (T.d t2 x1) x2 (Step.leftD x1 h2)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.secondC (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h2)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.secondC (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.d x0 x1) (Step.secondC (T.d t2 x1) x2 (Step.leftD x1 h2)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.thirdC (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.c (T.d t2 x1) (T.d t2 x1) x2) (Step.leftD x1 h2))) (Steps.cons (Step.rightR (T.c (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.d t2 x1)) (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h2)))) (Steps.cons (Step.rightR (T.c (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.d t2 x1)) (Step.leftD (T.d x0 x1) (Step.secondC (T.d t2 x1) x2 (Step.leftD x1 h2)))) (Steps.cons (Step.rightR (T.c (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.d t2 x1)) (Step.rightD (T.c (T.d t2 x1) (T.d t2 x1) x2) (Step.leftD x1 h2))) (Steps.refl _))))))))), (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d t2 x1)) (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h2))))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d t2 x1)) (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.secondC (T.d t2 x1) x2 (Step.leftD x1 h2))))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d t2 x1)) (Step.leftD x0 (Step.rightD (T.c (T.d t2 x1) (T.d t2 x1) x2) (Step.leftD x1 h2)))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d t2 x1)) (Step.rightD (T.d (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.d t2 x1)) h2)) (Steps.cons (Step.right (T.d (T.d (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.d t2 x1)) t2) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d t2 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h2)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.d t2 x1)) t2) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d t2 x1) (Step.secondC (T.d t2 x1) x2 (Step.leftD x1 h2)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.d t2 x1)) t2) (Step.secondC (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.d t2 x1) (Step.firstC (T.d x0 x1) x2 (Step.leftD x1 h2)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.d t2 x1)) t2) (Step.secondC (T.c (T.d t2 x1) (T.d t2 x1) x2) (T.d t2 x1) (Step.secondC (T.d t2 x1) x2 (Step.leftD x1 h2)))) (Steps.cons (Step.root (Root.r21 t2 x1 x2)) (Steps.refl _))))))))))⟩
  | @rightD _ _ t2 h2 =>
    exact ⟨(T.r (T.c (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.d x0 t2)) (T.d (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.d x0 t2))), (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h2)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1) (Step.secondC (T.d x0 t2) x2 (Step.rightD x0 h2)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.secondC (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h2)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.secondC (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.d x0 x1) (Step.secondC (T.d x0 t2) x2 (Step.rightD x0 h2)))) (Steps.cons (Step.leftR (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (Step.thirdC (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.c (T.d x0 t2) (T.d x0 t2) x2) (Step.rightD x0 h2))) (Steps.cons (Step.rightR (T.c (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.d x0 t2)) (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h2)))) (Steps.cons (Step.rightR (T.c (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.d x0 t2)) (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t2) x2 (Step.rightD x0 h2)))) (Steps.cons (Step.rightR (T.c (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.d x0 t2)) (Step.rightD (T.c (T.d x0 t2) (T.d x0 t2) x2) (Step.rightD x0 h2))) (Steps.refl _))))))))), (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 t2)) (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h2))))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 t2)) (Step.leftD x0 (Step.leftD (T.d x0 x1) (Step.secondC (T.d x0 t2) x2 (Step.rightD x0 h2))))) (Steps.cons (Step.left (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 t2)) (Step.leftD x0 (Step.rightD (T.c (T.d x0 t2) (T.d x0 t2) x2) (Step.rightD x0 h2)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.d x0 t2)) x0) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 t2) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h2)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.d x0 t2)) x0) (Step.firstC (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 t2) (Step.secondC (T.d x0 t2) x2 (Step.rightD x0 h2)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.d x0 t2)) x0) (Step.secondC (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.d x0 t2) (Step.firstC (T.d x0 x1) x2 (Step.rightD x0 h2)))) (Steps.cons (Step.right (T.d (T.d (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.d x0 t2)) x0) (Step.secondC (T.c (T.d x0 t2) (T.d x0 t2) x2) (T.d x0 t2) (Step.secondC (T.d x0 t2) x2 (Step.rightD x0 h2)))) (Steps.cons (Step.root (Root.r21 x0 t2 x2)) (Steps.refl _)))))))))⟩
end submission.Austin5837

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak21_context_2 {x0 x1 x2 u : T} (h : Step (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) u) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) u) := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
    · rw [ho]
      exact peak21_root147 he
    · rw [ho]
      exact peak21_root148 he
    · rw [ho]
      exact peak21_root149 he
    · rw [ho]
      exact peak21_root150 he
    · rw [ho]
      exact peak21_root151 he
    · rw [ho]
      exact peak21_root152 he
    · rw [ho]
      exact peak21_root153 he
    · rw [ho]
      exact peak21_root154 he
    · rw [ho]
      exact peak21_root155 he
    · rw [ho]
      exact peak21_root156 he
    · rw [ho]
      exact peak21_root157 he
    · rw [ho]
      exact peak21_root158 he
    · rw [ho]
      exact peak21_root159 he
    · rw [ho]
      exact peak21_root160 he
    · rw [ho]
      exact peak21_root161 he
    · rw [ho]
      exact peak21_root162 he
    · rw [ho]
      exact peak21_root163 he
    · rw [ho]
      exact peak21_root164 he
    · rw [ho]
      exact peak21_root165 he
    · rw [ho]
      exact peak21_root166 he
    · rw [ho]
      exact peak21_root167 he
  | @firstC _ t1 _ _ h1 =>
    exact peak21_context_21 h1
  | @secondC _ _ t1 _ h1 =>
    exact peak21_context_22 h1
  | @thirdC _ _ _ t1 h1 =>
    exact peak21_context_23 h1
end submission.Austin5837

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak21 (x0 : T) (x1 : T) (x2 : T) {u : T} (h : Step (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) u) : Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) u := by
  cases h with
  | root hr =>
    rcases root_cases hr with ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩ | ⟨q0, q1, q2, he, ho⟩
    · rw [ho]
      exact peak21_root0 he
    · rw [ho]
      exact peak21_root1 he
    · rw [ho]
      exact peak21_root2 he
    · rw [ho]
      exact peak21_root3 he
    · rw [ho]
      exact peak21_root4 he
    · rw [ho]
      exact peak21_root5 he
    · rw [ho]
      exact peak21_root6 he
    · rw [ho]
      exact peak21_root7 he
    · rw [ho]
      exact peak21_root8 he
    · rw [ho]
      exact peak21_root9 he
    · rw [ho]
      exact peak21_root10 he
    · rw [ho]
      exact peak21_root11 he
    · rw [ho]
      exact peak21_root12 he
    · rw [ho]
      exact peak21_root13 he
    · rw [ho]
      exact peak21_root14 he
    · rw [ho]
      exact peak21_root15 he
    · rw [ho]
      exact peak21_root16 he
    · rw [ho]
      exact peak21_root17 he
    · rw [ho]
      exact peak21_root18 he
    · rw [ho]
      exact peak21_root19 he
    · rw [ho]
      exact peak21_root20 he
  | @left _ t0 _ h0 =>
    exact peak21_context_1 h0
  | @right _ _ t0 h0 =>
    exact peak21_context_2 h0
end submission.Austin5837

set_option autoImplicit false
namespace submission.Austin5837
open T
theorem root_step {x y z : T} (h : Root x y) (k : Step x z) : Join y z := by
  cases h with
  | r1 => exact peak1 _ _ k
  | r2 => exact peak2 _ _ k
  | r3 => exact peak3 _ _ _ k
  | r4 => exact peak4 _ _ _ k
  | r5 => exact peak5 _ _ k
  | r6 => exact peak6 _ _ k
  | r7 => exact peak7 _ _ _ k
  | r8 => exact peak8 _ _ _ k
  | r9 => exact peak9 _ _ k
  | r10 => exact peak10 _ _ k
  | r11 => exact peak11 _ _ k
  | r12 => exact peak12 _ _ _ k
  | r13 => exact peak13 _ _ _ k
  | r14 => exact peak14 _ _ _ k
  | r15 => exact peak15 _ _ _ k
  | r16 => exact peak16 _ _ _ k
  | r17 => exact peak17 _ _ _ k
  | r18 => exact peak18 _ _ _ k
  | r19 => exact peak19 _ _ _ k
  | r20 => exact peak20 _ _ _ k
  | r21 => exact peak21 _ _ _ k
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
end submission.Austin5837

set_option autoImplicit false
namespace submission.Austin5837
open T
def Carrier := {x : T // Normal x}
noncomputable def mul (x y : Carrier) : Carrier :=
  ⟨norm (m x.val y.val), norm_normal _⟩
theorem equation5837 (x y z : Carrier) :
    (mul y (mul x (mul y (mul (mul z y) y)))) = x := by
  apply Subtype.ext
  change (norm (T.m y.val (norm (T.m x.val (norm (T.m y.val (norm (T.m (norm (T.m z.val y.val)) y.val)))))))) = x.val
  simp only [norm_m_left, norm_m_right]
  have h : Steps (T.m y.val (T.m x.val (T.m y.val (T.m (T.m z.val y.val) y.val)))) x.val :=
    (Steps.cons (Step.right y.val (Step.right x.val (Step.right y.val (Step.root (Root.r1 z.val y.val))))) (Steps.cons (Step.right y.val (Step.right x.val (Step.root (Root.r2 y.val z.val)))) (Steps.cons (Step.right y.val (Step.root (Root.r3 x.val y.val z.val))) (Steps.cons (Step.root (Root.r4 y.val x.val z.val)) (Steps.refl _)))))
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
theorem equation40221 (x y z : Carrier) :
    (opposite (opposite (opposite (opposite y (opposite y z)) y) x) y) = x :=
  equation5837 x y z
theorem infinite_model : ∃ (A : Type) (op : A → A → A) (f : Nat → A),
    (∀ x y z, (op y (op x (op y (op (op z y) y)))) = x) ∧
    (∀ n j, f n = f j → n = j) :=
  ⟨Carrier, mul, embed, equation5837, embed_injective⟩
end submission.Austin5837

namespace submission
abbrev CM := Austin5837.Carrier
namespace CM
/-- The model contains an injective image of every natural number. -/
theorem tower_injective (n j : Nat)
    (h : Austin5837.embed n = Austin5837.embed j) : n = j :=
  Austin5837.embed_injective n j h
end CM
noncomputable instance modelMagma : Magma CM := ⟨Austin5837.opposite⟩
end submission

theorem submission : Goal := by
  refine ⟨submission.CM, submission.modelMagma, ?_, ?_⟩
  · intro x y z
    exact (submission.Austin5837.equation40221 x y z).symm
  · intro h
    have bad : 0 = 1 := submission.Austin5837.embed_injective 0 1
      (h (submission.Austin5837.embed 0) (submission.Austin5837.embed 1))
    exact Nat.noConfusion bad
example : Goal := submission
#print axioms submission
#print axioms submission.CM.tower_injective


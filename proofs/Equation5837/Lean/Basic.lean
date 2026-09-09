import Lean.Elab.Tactic.Omega
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

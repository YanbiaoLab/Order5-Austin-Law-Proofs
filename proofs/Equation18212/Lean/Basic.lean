import Lean.Elab.Tactic.Omega
set_option autoImplicit false
namespace submission.Austin18212
inductive T where
  | a : T
  | e : T
  | k : T → T
  | v : T → T
  | r : T → T → T
  | m : T → T → T
  deriving DecidableEq
open T
@[simp] def size : T → Nat
  | a => 1
  | e => 1
  | k x => size x + 1
  | v x => size x + 1
  | r x y => size x + size y + 1
  | m x y => 2 * size x + 2 * size y + 1
theorem size_pos (x : T) : 0 < size x := by
  cases x <;> simp only [size] <;> omega
inductive Root : T → T → Prop where
  | r1 (v0) : Root (T.m v0 v0) T.e
  | r2 (v0 v1) : Root (T.m (T.m v0 v1) v1) (T.r v0 v1)
  | r3 (v0 v1) : Root (T.m v0 (T.r v0 v1)) (T.v v0)
  | r4 (v0) : Root (T.r (T.v v0) (T.v v0)) v0
  | r5 (v0) : Root (T.m T.e v0) (T.r v0 v0)
  | r6 : Root (T.r T.e T.e) T.e
  | r7 : Root (T.v T.e) T.e
  | r8 (v0) : Root (T.m (T.v v0) v0) (T.v (T.v v0))
  | r9 (v0) : Root (T.r (T.r T.e v0) (T.r T.e v0)) T.e
  | r10 (v0) : Root (T.r T.e (T.r T.e v0)) T.e
  | r11 (v0) : Root (T.m v0 (T.v v0)) (T.r T.e (T.v v0))
  | r12 (v0) : Root (T.m (T.v (T.v v0)) v0) (T.r (T.v v0) v0)
  | r13 (v0) : Root (T.m (T.r T.e v0) T.e) (T.v (T.r T.e v0))
  | r14 (v0 v1) : Root (T.m (T.r v0 v1) v1) (T.r (T.m v0 v1) v1)
  | r15 (v0 v1) : Root (T.m (T.v v0) (T.r v0 v1)) (T.r v0 (T.r v0 v1))
  | r16 (v0) : Root (T.m (T.v (T.r T.e v0)) T.e) (T.r (T.r T.e v0) T.e)
inductive Step : T → T → Prop where
  | root {x y} : Root x y → Step x y
  | underK {x y} : Step x y → Step (k x) (k y)
  | underV {x y} : Step x y → Step (v x) (v y)
  | left {x y} (z) : Step x y → Step (m x z) (m y z)
  | right (x) {y z} : Step y z → Step (m x y) (m x z)
  | leftR {x y} (z) : Step x y → Step (r x z) (r y z)
  | rightR (x) {y z} : Step y z → Step (r x y) (r x z)
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
theorem root_cases {u v : T} (h : Root u v) :
    (∃ v0, u = (T.m v0 v0) ∧ v = T.e) ∨
    (∃ v0 v1, u = (T.m (T.m v0 v1) v1) ∧ v = (T.r v0 v1)) ∨
    (∃ v0 v1, u = (T.m v0 (T.r v0 v1)) ∧ v = (T.v v0)) ∨
    (∃ v0, u = (T.r (T.v v0) (T.v v0)) ∧ v = v0) ∨
    (∃ v0, u = (T.m T.e v0) ∧ v = (T.r v0 v0)) ∨
    (u = (T.r T.e T.e) ∧ v = T.e) ∨
    (u = (T.v T.e) ∧ v = T.e) ∨
    (∃ v0, u = (T.m (T.v v0) v0) ∧ v = (T.v (T.v v0))) ∨
    (∃ v0, u = (T.r (T.r T.e v0) (T.r T.e v0)) ∧ v = T.e) ∨
    (∃ v0, u = (T.r T.e (T.r T.e v0)) ∧ v = T.e) ∨
    (∃ v0, u = (T.m v0 (T.v v0)) ∧ v = (T.r T.e (T.v v0))) ∨
    (∃ v0, u = (T.m (T.v (T.v v0)) v0) ∧ v = (T.r (T.v v0) v0)) ∨
    (∃ v0, u = (T.m (T.r T.e v0) T.e) ∧ v = (T.v (T.r T.e v0))) ∨
    (∃ v0 v1, u = (T.m (T.r v0 v1) v1) ∧ v = (T.r (T.m v0 v1) v1)) ∨
    (∃ v0 v1, u = (T.m (T.v v0) (T.r v0 v1)) ∧ v = (T.r v0 (T.r v0 v1))) ∨
    (∃ v0, u = (T.m (T.v (T.r T.e v0)) T.e) ∧ v = (T.r (T.r T.e v0) T.e)) := by
  cases h with
  | r1 => exact (Or.inl ⟨_, rfl, rfl⟩)
  | r2 => exact (Or.inr (Or.inl ⟨_, _, rfl, rfl⟩))
  | r3 => exact (Or.inr (Or.inr (Or.inl ⟨_, _, rfl, rfl⟩)))
  | r4 => exact (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl, rfl⟩))))
  | r5 => exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl, rfl⟩)))))
  | r6 => exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))))
  | r7 => exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))))
  | r8 => exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl, rfl⟩))))))))
  | r9 => exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl, rfl⟩)))))))))
  | r10 => exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl, rfl⟩))))))))))
  | r11 => exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl, rfl⟩)))))))))))
  | r12 => exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl, rfl⟩))))))))))))
  | r13 => exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl, rfl⟩)))))))))))))
  | r14 => exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, rfl, rfl⟩))))))))))))))
  | r15 => exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, rfl, rfl⟩)))))))))))))))
  | r16 => exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨_, rfl, rfl⟩)))))))))))))))

end submission.Austin18212

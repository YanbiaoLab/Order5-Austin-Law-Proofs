import Lean.Elab.Tactic.Omega
set_option autoImplicit false
namespace Austin12857
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
end Austin12857

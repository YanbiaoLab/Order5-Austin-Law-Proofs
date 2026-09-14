prelude
import TraceShape
set_option autoImplicit false

namespace Austin12087Trace
open T

theorem basicInverse_cases {b out a : T} (h : basicInverse b out = some a) :
    ∃ z l r, b = c a out z l r := by
  cases b with
  | c y x z l r =>
    by_cases he : out = x
    · simp only [basicInverse,he,↓reduceIte,Option.some.injEq] at h
      exact ⟨z,l,r,by rw [h,he]⟩
    · simp only [basicInverse,he,↓reduceIte] at h; cases h
  | atom n => cases h
  | s t => cases h
  | p l r => cases h

theorem inverse_cases {b out a : T} (h : inverse b out = some a) :
    (a = b ∧ out = s b) ∨
    (origin out = some (a,b) ∧ mul a b = out) ∨ basicInverse b out = some a := by
  by_cases hs : out = s b
  · have ha : b = a := by simpa only [inverse.eq_def,hs,↓reduceIte,Option.some.injEq] using h
    exact Or.inl ⟨ha.symm,hs⟩
  · apply Or.inr
    cases out with
    | atom n => exact Or.inr (by simpa only [inverse.eq_def,hs,↓reduceIte] using h)
    | s t => exact Or.inr (by simpa only [inverse.eq_def,hs,↓reduceIte] using h)
    | p l r =>
      by_cases hr : r = b
      · subst r
        have hk : rankM l b < rankI b (p l b) := by simp only [rankM,rankI,sz]; omega
        by_cases hm : mul l b = p l b
        · have ha : l = a := by simpa only [inverse.eq_def,reduceCtorEq,hk,hm,↓reduceIte,↓reduceDIte,Option.some.injEq] using h
          exact Or.inl ⟨by rw [origin,ha],by rw [←ha]; exact hm⟩
        · exact Or.inr (by simpa only [inverse.eq_def,reduceCtorEq,hk,hm,↓reduceIte,↓reduceDIte] using h)
      · exact Or.inr (by simpa only [inverse.eq_def,hs,hr,↓reduceIte] using h)
    | c y x z l r =>
      by_cases hr : r = b
      · subst r
        have hk : rankM l b < rankI b (c y x z l b) := by simp only [rankM,rankI,sz]; omega
        by_cases hm : mul l b = c y x z l b
        · have ha : l = a := by simpa only [inverse.eq_def,reduceCtorEq,hk,hm,↓reduceIte,↓reduceDIte,Option.some.injEq] using h
          exact Or.inl ⟨by rw [origin,ha],by rw [←ha]; exact hm⟩
        · exact Or.inr (by simpa only [inverse.eq_def,reduceCtorEq,hk,hm,↓reduceIte,↓reduceDIte] using h)
      · exact Or.inr (by simpa only [inverse.eq_def,hs,hr,↓reduceIte] using h)

theorem inverse_size {b out a : T} (h : inverse b out = some a) :
    sz a ≤ max (sz b) (sz out) := by
  rcases inverse_cases h with ⟨rfl,_⟩ | ⟨ho,_⟩ | hb
  · omega
  · have hs := origin_size ho; omega
  · obtain ⟨z,l,r,hb⟩ := basicInverse_cases hb
    rw [hb]; simp only [sz]; omega

theorem inverse_sound {b out a : T} (h : inverse b out = some a) : mul a b = out := by
  rcases inverse_cases h with ⟨rfl,rfl⟩ | ⟨_,hm⟩ | hb
  · exact mul_square _
  · exact hm
  · obtain ⟨z,l,r,rfl⟩ := basicInverse_cases hb
    exact mul_code_return a out z l r

theorem inverse_square (b : T) : inverse b (s b) = some b := by
  rw [inverse.eq_def]
  simp only [↓reduceIte]

theorem inverse_raw {a b : T} (h : mul a b = p a b) : inverse b (p a b) = some a := by
  have hk : rankM a b < rankI b (p a b) := by
    simp only [rankM,rankI,sz]; omega
  rw [inverse.eq_def]
  simp only [reduceCtorEq,↓reduceIte,↓reduceDIte,hk,h]

theorem inverse_code {y x z a b : T} (h : mul a b = c y x z a b) :
    inverse b (c y x z a b) = some a := by
  have hk : rankM a b < rankI b (c y x z a b) := by
    simp only [rankM,rankI,sz]; omega
  rw [inverse.eq_def]
  simp only [reduceCtorEq,↓reduceIte,↓reduceDIte,hk,h]

theorem inverse_small {b out : T} (hs : sz out < sz b) :
    inverse b out = basicInverse b out := by
  have hn : out ≠ s b := by
    intro he; rw [he] at hs; simp only [sz] at hs; omega
  cases out with
  | atom n => rw [inverse.eq_def]; simp only [hn,↓reduceIte]
  | s t => rw [inverse.eq_def]; simp only [hn,↓reduceIte]
  | p l r =>
    have hr : r ≠ b := by
      intro he; rw [he] at hs; simp only [sz] at hs; omega
    rw [inverse.eq_def]; simp only [hn,hr,↓reduceIte]
  | c y x z l r =>
    have hr : r ≠ b := by
      intro he; rw [he] at hs; simp only [sz] at hs; omega
    rw [inverse.eq_def]; simp only [hn,hr,↓reduceIte]

theorem inverse_complete (a b : T) : inverse b (mul a b) = some a := by
  rcases mul_cases a b with ⟨he,hm⟩ | ⟨x,z,l,r,hb,hm⟩ | hm | ⟨y,x,z,hm⟩
  · subst b; rw [mul_square,inverse_square]
  · rw [hm,hb]
    rw [inverse_small (by simp only [sz]; omega)]
    simp only [basicInverse,↓reduceIte]
  · rw [hm]; exact inverse_raw hm
  · rw [hm]; exact inverse_code hm

theorem right_injective (a b z : T) (h : mul a z = mul b z) : a = b := by
  have hi := congrArg (inverse z) h
  rw [inverse_complete,inverse_complete] at hi
  exact Option.some.inj hi

end Austin12087Trace
#print axioms Austin12087Trace.basicInverse_cases
#print axioms Austin12087Trace.inverse_cases
#print axioms Austin12087Trace.inverse_size
#print axioms Austin12087Trace.inverse_sound
#print axioms Austin12087Trace.inverse_square
#print axioms Austin12087Trace.inverse_raw
#print axioms Austin12087Trace.inverse_code
#print axioms Austin12087Trace.inverse_small
#print axioms Austin12087Trace.inverse_complete
#print axioms Austin12087Trace.right_injective

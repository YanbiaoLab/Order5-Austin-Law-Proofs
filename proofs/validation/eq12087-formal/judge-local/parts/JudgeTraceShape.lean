prelude
import Init.Data.Option.Lemmas
import Init.Omega
import Init.RCases
import Init.WFTactics
import JudgeTraceBasic
set_option Elab.async false
/- Checked module: TraceShape -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem leftCode_shape {m i : T → T → Option T} {a b out : T}
    (h : leftCode m i a b = some out) : ∃ y x z, out = c y x z a b := by
  cases ho : origin a with
  | none => simp only [leftCode,ho,Option.bind_none] at h; cases h
  | some uv =>
    rcases uv with ⟨u,z⟩
    cases hm : m u z with
    | none => simp only [leftCode,ho,hm,Option.bind_some,Prod.fst,Prod.snd,Option.bind_none] at h; cases h
    | some v =>
      by_cases hv : v = a
      · cases hx : i z b with
        | none => simp only [leftCode,ho,hm,hv,hx,Option.bind_some,Prod.fst,Prod.snd,Option.bind_none,↓reduceIte] at h; cases h
        | some x =>
          cases hy : i x u with
          | none => simp only [leftCode,ho,hm,hv,hx,hy,Option.bind_some,Prod.fst,Prod.snd,Option.bind_none,↓reduceIte] at h; cases h
          | some y =>
            simp only [leftCode,ho,hm,hv,hx,hy,Option.bind_some,Prod.fst,Prod.snd,↓reduceIte,Option.some.injEq] at h
            exact ⟨y,x,z,h.symm⟩
      · simp only [leftCode,ho,hm,hv,Option.bind_some,Prod.fst,Prod.snd,↓reduceIte] at h; cases h

theorem rightCode_shape {m i : T → T → Option T} {a b out : T}
    (h : rightCode m i a b = some out) : ∃ y x z, out = c y x z a b := by
  cases ho : origin b with
  | none => simp only [rightCode,ho,Option.bind_none] at h; cases h
  | some xz =>
    rcases xz with ⟨x,z⟩
    cases hm : m x z with
    | none => simp only [rightCode,ho,hm,Option.bind_some,Prod.fst,Prod.snd,Option.bind_none] at h; cases h
    | some v =>
      by_cases hv : v = b
      · cases hu : i z a with
        | none => simp only [rightCode,ho,hm,hv,hu,Option.bind_some,Prod.fst,Prod.snd,Option.bind_none,↓reduceIte] at h; cases h
        | some u =>
          cases hy : i x u with
          | none => simp only [rightCode,ho,hm,hv,hu,hy,Option.bind_some,Prod.fst,Prod.snd,Option.bind_none,↓reduceIte] at h; cases h
          | some y =>
            simp only [rightCode,ho,hm,hv,hu,hy,Option.bind_some,Prod.fst,Prod.snd,↓reduceIte,Option.some.injEq] at h
            exact ⟨y,x,z,h.symm⟩
      · simp only [rightCode,ho,hm,hv,Option.bind_some,Prod.fst,Prod.snd,↓reduceIte] at h; cases h

theorem decode_shape (m i : T → T → Option T) (a b : T) :
    decode m i a b = p a b ∨ ∃ y x z, decode m i a b = c y x z a b := by
  cases hl : leftCode m i a b with
  | some out =>
    obtain ⟨y,x,z,h⟩ := leftCode_shape hl
    exact Or.inr ⟨y,x,z,by simp only [decode,hl,h]⟩
  | none =>
    cases hr : rightCode m i a b with
    | some out =>
      obtain ⟨y,x,z,h⟩ := rightCode_shape hr
      exact Or.inr ⟨y,x,z,by simp only [decode,hl,hr,h,Option.getD_some]⟩
    | none => exact Or.inl (by simp only [decode,hl,hr,Option.getD_none])

theorem mul_cases (a b : T) :
    (a = b ∧ mul a b = s b) ∨
    (∃ x z l r, b = c a x z l r ∧ mul a b = x) ∨
    mul a b = p a b ∨ ∃ y x z, mul a b = c y x z a b := by
  by_cases he : a = b
  · subst b
    exact Or.inl ⟨rfl,mul_square a⟩
  · apply Or.inr
    have hd := decode_shape (queryM (rankM a b)) (queryI (rankM a b)) a b
    cases b with
    | c y x z l r =>
      by_cases hy : a = y
      · subst y
        exact Or.inl ⟨x,z,l,r,rfl,mul_code_return a x z l r⟩
      · apply Or.inr
        simpa only [mul_equation,he,hy,↓reduceIte] using hd
    | atom n => apply Or.inr; simpa only [mul_equation,he,↓reduceIte] using hd
    | s t => apply Or.inr; simpa only [mul_equation,he,↓reduceIte] using hd
    | p l r => apply Or.inr; simpa only [mul_equation,he,↓reduceIte] using hd

theorem mul_small_iff (a b : T) : sz (mul a b) < sz b ↔
    ∃ x z l r, b = c a x z l r := by
  constructor
  · intro hs
    rcases mul_cases a b with ⟨he,hm⟩ | ⟨x,z,l,r,hb,hm⟩ | hm | ⟨y,x,z,hm⟩
    · rw [hm] at hs; simp only [sz] at hs; omega
    · exact ⟨x,z,l,r,hb⟩
    · rw [hm] at hs; simp only [sz] at hs; omega
    · rw [hm] at hs; simp only [sz] at hs; omega
  · rintro ⟨x,z,l,r,rfl⟩
    rw [mul_code_return]; simp only [sz]; omega

theorem mul_ne_right (a b : T) : mul a b ≠ b := by
  intro h
  rcases mul_cases a b with ⟨he,hm⟩ | ⟨x,z,l,r,hb,hm⟩ | hm | ⟨y,x,z,hm⟩
  all_goals have hs := congrArg sz (hm.symm.trans h)
  · simp only [sz] at hs; omega
  · rw [hb] at hs; simp only [sz] at hs; omega
  · simp only [sz] at hs; omega
  · simp only [sz] at hs; omega

theorem mul_grows_or_returns (a b : T) :
    (sz a < sz (mul a b) ∧ sz b < sz (mul a b) ∧ origin (mul a b) = some (a,b)) ∨
    (∃ x z l r, b = c a x z l r ∧ mul a b = x) := by
  rcases mul_cases a b with ⟨he,hm⟩ | h | hm | ⟨y,x,z,hm⟩
  · subst b; exact Or.inl (by rw [hm]; simp only [sz,origin]; exact ⟨by omega,by omega,True.intro⟩)
  · exact Or.inr h
  · exact Or.inl (by rw [hm]; simp only [sz,origin]; exact ⟨by omega,by omega,True.intro⟩)
  · exact Or.inl (by rw [hm]; simp only [sz,origin]; exact ⟨by omega,by omega,True.intro⟩)

end submission.Austin12087Trace

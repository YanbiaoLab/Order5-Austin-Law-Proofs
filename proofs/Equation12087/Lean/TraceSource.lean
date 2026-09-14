prelude
import TraceCodes
set_option autoImplicit false

namespace Austin12087Trace
open T

def Source12087 (x y z : T) : Prop :=
  x = mul y (mul (mul (mul y x) z) (mul x z))
def Law12087 : Prop := ∀ x y z : T, Source12087 x y z

theorem middle_cases (y x z : T) :
    mul (mul (mul y x) z) (mul x z) =
      c y x z (mul (mul y x) z) (mul x z) ∨
    ∃ q t l r, mul x z = c (mul (mul y x) z) q t l r ∧
      mul (mul (mul y x) z) (mul x z) = q := by
  generalize ha : mul (mul y x) z = a
  generalize hb : mul x z = b
  have hne : a ≠ b := by
    intro h
    exact mul_ne_right y x (right_injective (mul y x) x z (ha.trans (h.trans hb.symm)))
  have hd := decode_source ha hb
  cases b with
  | c y' q t l r =>
    by_cases he : a = y'
    · subst y'
      exact Or.inr ⟨q,t,l,r,rfl,mul_code_return a q t l r⟩
    · exact Or.inl (by simpa only [mul_equation,hne,he,↓reduceIte] using hd)
  | atom n => exact Or.inl (by simpa only [mul_equation,hne,↓reduceIte] using hd)
  | s t => exact Or.inl (by simpa only [mul_equation,hne,↓reduceIte] using hd)
  | p l r => exact Or.inl (by simpa only [mul_equation,hne,↓reduceIte] using hd)

theorem source_without_middle_return (x y z : T)
    (hn : ∀ q t l r, mul x z ≠ c (mul (mul y x) z) q t l r) : Source12087 x y z := by
  rcases middle_cases y x z with hc | ⟨q,t,l,r,hb,hm⟩
  · unfold Source12087
    rw [hc,mul_code_return]
  · exact False.elim (hn q t l r hb)

def CriticalReturn : Prop := ∀ x y z q t l r : T,
  mul x z = c (mul (mul y x) z) q t l r → mul y q = x

theorem law_iff_critical_return : Law12087 ↔ CriticalReturn := by
  constructor
  · intro h x y z q t l r hb
    have hs := h x y z
    unfold Source12087 at hs
    rw [hb,mul_code_return] at hs
    exact hs.symm
  · intro h x y z
    rcases middle_cases y x z with hc | ⟨q,t,l,r,hb,hm⟩
    · unfold Source12087
      rw [hc,mul_code_return]
    · unfold Source12087
      rw [hm]
      exact (h x y z q t l r hb).symm

theorem decode_generic_sound {n : Nat} {a b y x z : T}
    (h : decode (queryM n) (queryI n) a b = c y x z a b) :
    mul (mul y x) z = a ∧ mul x z = b := by
  cases hl : leftCode (queryM n) (queryI n) a b with
  | some out =>
    have he : out = c y x z a b := by simpa only [decode,hl] using h
    obtain ⟨y',x',z',he',ha,hb⟩ := leftCode_sound hl
    obtain ⟨hy,hx,hz,_,_⟩ := T.c.inj (he'.symm.trans he)
    simpa only [hy,hx,hz] using And.intro ha hb
  | none =>
    cases hr : rightCode (queryM n) (queryI n) a b with
    | none => simp only [decode,hl,hr,Option.getD_none] at h; cases h
    | some out =>
      have he : out = c y x z a b := by simpa only [decode,hl,hr,Option.getD_some] using h
      obtain ⟨y',x',z',he',ha,hb⟩ := rightCode_sound hr
      obtain ⟨hy,hx,hz,_,_⟩ := T.c.inj (he'.symm.trans he)
      simpa only [hy,hx,hz] using And.intro ha hb

theorem mul_code_semantics {y x z a b : T} (h : mul a b = c y x z a b) :
    mul (mul y x) z = a ∧ mul x z = b := by
  have hn : a ≠ b := by intro he; subst b; rw [mul_square] at h; cases h
  apply decode_generic_sound (n:=rankM a b)
  cases b with
  | atom n => simpa only [mul_equation,hn,↓reduceIte] using h
  | s t => simpa only [mul_equation,hn,↓reduceIte] using h
  | p l r => simpa only [mul_equation,hn,↓reduceIte] using h
  | c y' q t l r =>
    by_cases hy : a = y'
    · subst y'
      rw [mul_code_return] at h
      have hs := congrArg sz h
      simp only [sz] at hs
      omega
    · simpa only [mul_equation,hn,hy,↓reduceIte] using h

theorem critical_return_trace {x y z q t l r : T}
    (h : mul x z = c (mul (mul y x) z) q t l r) :
    l = x ∧ r = z ∧
    mul (mul (mul (mul y x) z) q) t = x ∧ mul q t = z := by
  have hn : mul (mul y x) z ≠ mul x z := by
    intro he
    exact mul_ne_right y x (right_injective (mul y x) x z he)
  have hs : sz (mul (mul y x) z) ≤ sz (mul x z) := by
    rw [h]; simp only [sz]; omega
  have ho := (distinct_outputs_large_origin (a:=mul x z) (b:=mul (mul y x) z)
    rfl rfl (Ne.symm hn) hs).1
  rw [h,origin] at ho
  have hp := Prod.mk.inj (Option.some.inj ho)
  rcases hp with ⟨hl,hr⟩
  subst l; subst r
  exact ⟨rfl,rfl,(mul_code_semantics h).1,(mul_code_semantics h).2⟩

theorem critical_return_is_small_first {x y z q t l r : T}
    (h : mul x z = c (mul (mul y x) z) q t l r) :
    sz (mul y x) < sz x ∨ sz (mul (mul y x) z) < sz z ∨
      sz (mul (mul (mul y x) z) q) < sz q ∨ sz x < sz t := by
  obtain ⟨hl,hr,hx,hz⟩ := critical_return_trace h
  rcases mul_grows_or_returns y x with ⟨_,h1,_⟩ | h1
  · rcases mul_grows_or_returns (mul y x) z with ⟨h2,_,_⟩ | h2
    · rcases mul_grows_or_returns (mul (mul y x) z) q with ⟨h3,_,_⟩ | h3
      · rcases mul_grows_or_returns (mul (mul (mul y x) z) q) t with ⟨h4,_,_⟩ | h4
        · rw [hx] at h4; omega
        · obtain ⟨v,s,a,b,ht,hm⟩ := h4
          apply Or.inr; apply Or.inr; apply Or.inr
          rw [←hx,hm,ht]; simp only [sz]; omega
      · obtain ⟨v,s,a,b,hq,hm⟩ := h3
        exact Or.inr (Or.inr (Or.inl ((mul_small_iff _ _).mpr ⟨v,s,a,b,hq⟩)))
    · obtain ⟨v,s,a,b,hz,hm⟩ := h2
      exact Or.inr (Or.inl ((mul_small_iff _ _).mpr ⟨v,s,a,b,hz⟩))
  · obtain ⟨v,s,a,b,hx,hm⟩ := h1
    exact Or.inl ((mul_small_iff _ _).mpr ⟨v,s,a,b,hx⟩)

-- CriticalReturn has NOT been established here. No model is registered.
end Austin12087Trace
#print axioms Austin12087Trace.middle_cases
#print axioms Austin12087Trace.source_without_middle_return
#print axioms Austin12087Trace.law_iff_critical_return
#print axioms Austin12087Trace.decode_generic_sound
#print axioms Austin12087Trace.mul_code_semantics
#print axioms Austin12087Trace.critical_return_trace
#print axioms Austin12087Trace.critical_return_is_small_first

prelude
import Init.Data.Option.Lemmas
import Init.Omega
import Init.RCases
import Init.WFTactics
import JudgeTraceCritical
set_option Elab.async false
/- Checked module: TraceOrient -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem critical_x_max {x y z q t l r : T}
    (h : mul x z = c (mul (mul y x) z) q t l r)
    (hs : sz z ≤ sz x) :
    ∃ k, x = c y (mul y x) k (mul (mul (mul y x) z) q) t ∧
      mul (mul y (mul y x)) k = mul (mul (mul y x) z) q ∧
      mul (mul y x) k = t := by
  obtain ⟨_,_,hx,hz⟩ := critical_return_trace h
  have hb := common_column_inputs_small hx hz
  have hu := inverse_strict_size (inverse_complete (mul y x) z)
  have hu' : sz (mul y x) < sz x := by omega
  obtain ⟨v,k,a,b,he⟩ := (mul_small_iff y x).mp hu'
  have hv : v = mul y x := by rw [he,mul_code_return]
  subst v
  have hn : mul (mul (mul y x) z) q ≠ q := mul_ne_right _ _
  have hne : x ≠ z := by
    intro heq
    exact hn (right_injective _ _ t (hx.trans (heq.trans hz.symm)))
  have ho := (distinct_outputs_large_origin hx hz hne hs).1
  conv at ho => lhs; rw [he,origin]
  obtain ⟨ha,hb'⟩ := Prod.mk.inj (Option.some.inj ho)
  subst a; subst b
  have hd := mul_code_semantics (hx.trans he)
  exact ⟨k,he,hd.1,hd.2⟩

theorem critical_z_max {x y z q t l r : T}
    (h : mul x z = c (mul (mul y x) z) q t l r)
    (hs : sz x ≤ sz z) :
    ∃ k, z = c (mul y x) (mul (mul y x) z) k q t ∧
      mul (mul (mul y x) (mul (mul y x) z)) k = q ∧
      mul (mul (mul y x) z) k = t := by
  obtain ⟨_,_,hx,hz⟩ := critical_return_trace h
  have hb := (common_column_inputs_small hx hz).1
  have ha : sz (mul (mul y x) z) < sz z := by omega
  obtain ⟨v,k,a,b,he⟩ := (mul_small_iff (mul y x) z).mp ha
  have hv : v = mul (mul y x) z := by rw [he,mul_code_return]
  subst v
  have hn : mul (mul (mul y x) z) q ≠ q := mul_ne_right _ _
  have hne : z ≠ x := by
    intro heq
    exact hn (right_injective _ _ t (hx.trans (heq.symm.trans hz.symm)))
  have ho := (distinct_outputs_large_origin hz hx hne hs).1
  conv at ho => lhs; rw [he,origin]
  obtain ⟨ha',hb'⟩ := Prod.mk.inj (Option.some.inj ho)
  subst a; subst b
  have hd := mul_code_semantics (hz.trans he)
  exact ⟨k,he,hd.1,hd.2⟩

-- These are proposed sufficient conditions, not established lemmas.
def FirstCycleAbsent : Prop := ∀ u q k : T,
  (inverse k (mul (mul u (mul q (mul u k))) q)).bind (inverse u) = none

def SecondCycleAbsent : Prop := ∀ u a k : T,
  inverse (mul (mul a (mul (mul u a) k)) (mul a k)) u = none

theorem critical_excluded_by_three_parameter_queries
    (hf : FirstCycleAbsent) (hs : SecondCycleAbsent)
    {x y z q t l r : T}
    (h : mul x z = c (mul (mul y x) z) q t l r) : False := by
  obtain ⟨_,_,hx,hz⟩ := critical_return_trace h
  by_cases hsz : sz z ≤ sz x
  · obtain ⟨k,_,hv,ht⟩ := critical_x_max h hsz
    have h1 := inverse_complete (mul y (mul y x)) k
    rw [hv] at h1
    have h2 := inverse_complete y (mul y x)
    have he := hf (mul y x) q k
    rw [ht,hz,h1,Option.bind_some,h2] at he
    cases he
  · obtain ⟨k,_,hq,ht⟩ := critical_z_max h (by omega)
    have he := hs (mul y x) (mul (mul y x) z) k
    rw [hq,ht,hx,inverse_complete] at he
    cases he

theorem law_of_three_parameter_query_absence
    (hf : FirstCycleAbsent) (hs : SecondCycleAbsent) : Law12087 := by
  intro x y z
  apply source_without_middle_return
  intro q t l r h
  exact critical_excluded_by_three_parameter_queries hf hs h

end submission.Austin12087Trace

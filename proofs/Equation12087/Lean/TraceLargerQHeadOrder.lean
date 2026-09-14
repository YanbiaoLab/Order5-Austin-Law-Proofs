prelude
import TraceFirstLargerQStructure
set_option autoImplicit false

namespace Austin12087Trace
open T

theorem nf_common_column_head_order {u a y k v w j h : T}
    (hnw : NF w) (hnk : NF k)
    (hv : mul u k = v) (hw : mul (mul y u) k = w)
    (haj : mul a j = v) (hgh : mul (mul a w) h = mul u a)
    (hwh : mul w h = j) (hhg : ht h < ht (mul u a)) :
    ht (mul u a) < ht j := by
  by_cases hgj : ht (mul u a) < ht j
  · exact hgj
  · let g := mul u a
    let d := mul a w
    change ht h < ht g at hhg
    change ¬ht g < ht j at hgj
    change mul d h = g at hgh
    have hgg := mul_height_growth_of_right_le (a:=d) (b:=h) (by rw [hgh]; omega)
    rw [hgh] at hgg
    have hiw := inverse_height_strict (inverse_complete w h)
    rw [hwh] at hiw
    have hia := inverse_height_strict (inverse_complete a w)
    change ht a < max (ht w) (ht d) at hia
    have haw : ht a < ht g := by omega
    have hug := mul_height_growth_of_right_le (a:=u) (b:=a) (by change ht a ≤ ht g; omega)
    change ht g = max (ht u) (ht a) + 1 at hug
    have hau : ht a < ht u := by
      by_cases hh : ht a < ht u
      · exact hh
      · have hp := nf_mul_height_key_gap (a:=a) hnw
        change ht d = max (ht a) (ht w) + 1 ∨
          (ht a + 3 ≤ ht w ∧ ht d + 2 ≤ ht w) at hp
        rcases hp with hp | hp <;> exact False.elim (by omega)
    have hvk : ht k ≤ ht v := by
      by_cases hh : ht k ≤ ht v
      · exact hh
      · obtain ⟨z,l,r,hkc⟩ := mul_return_of_height_lt (a:=u) (b:=k) (by rw [hv]; omega)
        have huk := nf_code_key_height_gap (hkc ▸ hnk)
        rw [←hkc] at huk
        have hwg := mul_height_off_return_key (a:=mul y u) hkc (mul_ne_right y u)
        rw [hw] at hwg
        exact False.elim (by omega)
    have hvg := mul_height_growth_of_right_le (a:=u) (b:=k) (by rw [hv]; exact hvk)
    rw [hv] at hvg
    have hov := mul_origin_of_right_height_le (a:=u) (b:=k) (by rw [hv]; exact hvk)
    rw [hv] at hov
    have hov' := mul_origin_of_right_height_le (a:=a) (b:=j) (by rw [haj]; omega)
    rw [haj] at hov'
    have hua := (Prod.mk.inj (Option.some.inj (hov.symm.trans hov'))).1
    have hh := congrArg ht hua
    exact False.elim (by omega)

theorem normal_first_larger_q_column_order {u q k y j h : T}
    (hq : NF q) (hk : NF k)
    (hqc : q = c (mul u (mul q (mul u k))) (mul (mul y u) k) h
      (mul u (mul u (mul q (mul u k)))) j)
    (haj : mul (mul u (mul q (mul u k))) j = mul u k) :
    ht (mul u (mul u (mul q (mul u k)))) < ht j := by
  let a := mul u (mul q (mul u k))
  let w := mul (mul y u) k
  change q = c a w h (mul u a) j at hqc
  have hnf := nf_code_actual (hqc ▸ hq)
  have hnw : NF w := hnf.2.1
  have hhq := (nf_code_height_gap (hqc ▸ hq)).2.2
  rw [←hqc] at hhq
  have hsem := hnf.2.2.2.2.2.2
  have hactual := hnf.2.2.2.2.2.1
  rw [←hqc] at hactual
  have hqg := mul_height_growth_of_right_le (a:=mul u a) (b:=j) (by
    rw [hactual,hqc]; simp only [ht]; omega)
  rw [hactual] at hqg
  by_cases hgj : ht (mul u a) < ht j
  · exact hgj
  · exact nf_common_column_head_order hnw hk rfl rfl haj hsem.1 hsem.2 (by
      change ht h < ht (mul u a)
      omega)

end Austin12087Trace
#print axioms Austin12087Trace.nf_common_column_head_order
#print axioms Austin12087Trace.normal_first_larger_q_column_order

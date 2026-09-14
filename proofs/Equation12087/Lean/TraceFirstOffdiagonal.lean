prelude
import TraceNormalFoldConsequences
set_option autoImplicit false

namespace Austin12087Trace
open T

theorem first_larger_k_nested_code {u q k y : T}
    (hf : mul (mul y u) k = mul (mul u (mul q (mul u k))) q)
    (hne : q ≠ k) (hs : sz q ≤ sz k) :
    ∃ t,
      mul u k = c q (mul q (mul u k)) t u k ∧
      mul (mul q (mul q (mul u k))) t = u ∧
      mul (mul q (mul u k)) t = k := by
  obtain ⟨⟨h,l,r,hk⟩,huv,hkv,hov⟩ := first_offdiagonal_larger_k_return hf hne hs
  let v := mul u k
  let b := mul q v
  let a := mul u b
  let w := mul (mul y u) k
  change sz u < sz v at huv
  change sz k < sz v at hkv
  change origin v = some (u,k) at hov
  have hws : sz w < sz k := by
    change sz (mul (mul y u) k) < sz k
    conv => rhs; rw [hk]
    simp only [sz]
    omega
  have hwa : mul a q = w := hf.symm
  have ha := inverse_strict_size (inverse_complete a q)
  rw [hwa] at ha
  have hret : ∃ t l r, v = c q b t l r := by
    rcases mul_grows_or_returns q v with hg | ⟨x,t,l,r,hv,hb⟩
    · have has : sz (mul u b) < sz b := by
        change sz a < sz b
        have hvb : sz v < sz b := hg.2.1
        omega
      obtain ⟨x,t,l,r,hb⟩ := (mul_small_iff u b).mp has
      have hxa : x = a := by change x = mul u b; rw [hb,mul_code_return]
      subst x
      have hob := hg.2.2
      change origin b = some (q,v) at hob
      rw [hb,origin] at hob
      obtain ⟨hl,hr⟩ := Prod.mk.inj (Option.some.inj hob)
      subst l; subst r
      have hbactual : mul q v = c u a t q v := hb
      have hbsem := mul_code_semantics hbactual
      have bounds := common_column_inputs_small hbsem.1 hbsem.2
      have hvt : sz t ≤ sz (mul a t) := by rw [hbsem.2]; omega
      have hoat := mul_origin_of_right_le hvt
      rw [hbsem.2] at hoat
      have hpo := Prod.mk.inj (Option.some.inj (hoat.symm.trans hov))
      have hau : a = u := hpo.1
      have htk : t = k := hpo.2
      have hq : mul (mul u u) k = q := by simpa only [hau,htk] using hbsem.1
      have hk₂ : ∃ z l r, k = c (mul u u) q z l r := by
        rcases mul_grows_or_returns (mul u u) k with hg₂ | ⟨v,z,l,r,hk₂,hv⟩
        · rw [hq] at hg₂
          exact False.elim (by omega)
        · have hvq : v = q := hv.symm.trans hq
          exact ⟨z,l,r,by rw [hvq] at hk₂; exact hk₂⟩
      obtain ⟨z,l,r,hk₂⟩ := hk₂
      have hkey : mul y u = mul u u := (T.c.inj (hk.symm.trans hk₂)).1
      have hyu : y = u := right_injective y u u hkey
      have hwq : w = q := by change mul (mul y u) k = q; rw [hyu,hq]
      have hbad : mul u q = q := by simpa only [hau,hwq] using hwa
      exact False.elim (mul_ne_right u q hbad)
    · have hxb : x = b := hb.symm
      exact ⟨t,l,r,by rw [hxb] at hv; exact hv⟩
  obtain ⟨t,l,r,hv⟩ := hret
  rw [hv,origin] at hov
  obtain ⟨hl,hr⟩ := Prod.mk.inj (Option.some.inj hov)
  subst l; subst r
  have hc : mul u k = c q b t u k := hv
  exact ⟨t,hc,mul_code_semantics hc⟩

theorem first_larger_k_height_dominates {u q k y : T}
    (hu : NF u) (hnk : NF k)
    (hf : mul (mul y u) k = mul (mul u (mul q (mul u k))) q)
    (hne : q ≠ k) (hs : sz q ≤ sz k) : ht u < ht k := by
  obtain ⟨t,hv,_,_⟩ := first_larger_k_nested_code hf hne hs
  obtain ⟨⟨s,l,r,hk⟩,_,_,_⟩ := first_offdiagonal_larger_k_return hf hne hs
  have nv := hv ▸ nf_mul hu hnk
  have hb := (nf_code_height_gap nv).2.1
  have hq := nf_code_key_height_gap nv
  rw [←hv] at hb hq
  have hw := (nf_code_height_gap (hk ▸ hnk)).2.1
  rw [←hk,hf] at hw
  have vg := mul_height_growth_of_right_le (a:=u) (b:=k) (by
    rw [hv]
    simp only [ht]
    omega)
  by_cases h : ht u < ht k
  · exact h
  · have ag := mul_height_growth_of_left_ge (a:=u) (b:=mul q (mul u k)) (by omega)
    have wg := mul_height_growth_of_left_ge (a:=mul u (mul q (mul u k))) (b:=q) (by omega)
    exact False.elim (by omega)

theorem first_larger_k_double_code {u q k y : T}
    (hu : NF u) (hnk : NF k)
    (hf : mul (mul y u) k = mul (mul u (mul q (mul u k))) q)
    (hne : q ≠ k) (hs : sz q ≤ sz k) :
    ∃ t s,
      mul u k = c q (mul q (mul u k)) t u k ∧
      k = c (mul y u) (mul (mul y u) k) s (mul q (mul u k)) t ∧
      mul (mul q (mul q (mul u k))) t = u ∧
      mul (mul q (mul u k)) t = k ∧
      mul (mul (mul y u) (mul (mul y u) k)) s = mul q (mul u k) ∧
      mul (mul (mul y u) k) s = t ∧
      ht u < ht k ∧ ht q < ht k ∧ ht y < ht k ∧
      ht (mul q (mul u k)) < ht k ∧ ht t < ht k ∧ ht s < ht k := by
  obtain ⟨t,hv,hut,hbt⟩ := first_larger_k_nested_code hf hne hs
  have huk := first_larger_k_height_dominates hu hnk hf hne hs
  obtain ⟨⟨s,l,r,hk⟩,_,_,_⟩ := first_offdiagonal_larger_k_return hf hne hs
  have hknu : k ≠ u := by intro he; have hh := congrArg ht he; omega
  have ho := (distinct_outputs_height_origin hbt hut hknu (by omega)).1
  conv at ho => lhs; rw [hk,origin]
  obtain ⟨hl,hr⟩ := Prod.mk.inj (Option.some.inj ho)
  subst l; subst r
  have hsem := mul_code_semantics (hbt.trans hk)
  have hkc := congrArg ht hk
  simp only [ht] at hkc
  have vg := mul_height_growth_of_right_le (a:=u) (b:=k) (by
    rw [hv]
    simp only [ht]
    omega)
  have hq := nf_code_key_height_gap (hv ▸ nf_mul hu hnk)
  rw [←hv] at hq
  have hy := inverse_height_strict (inverse_complete y u)
  exact ⟨t,s,hv,hk,hut,hbt,hsem.1,hsem.2,huk,
    by omega,by omega,by omega,by omega,by omega⟩

end Austin12087Trace
#print axioms Austin12087Trace.first_larger_k_nested_code
#print axioms Austin12087Trace.first_larger_k_height_dominates
#print axioms Austin12087Trace.first_larger_k_double_code

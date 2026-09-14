prelude
import TraceGeneralHeadExclusion
set_option autoImplicit false

namespace Austin12087Trace
open T

theorem first_larger_q_inner_code {u q k y : T}
    (hf : mul (mul y u) k = mul (mul u (mul q (mul u k))) q)
    (hne : q ≠ k) (hs : sz k ≤ sz q) :
    ∃ j, mul q (mul u k) = c u (mul u (mul q (mul u k))) j q (mul u k) ∧
      mul (mul u (mul u (mul q (mul u k)))) j = q ∧
      mul (mul u (mul q (mul u k))) j = mul u k := by
  let v := mul u k
  let b := mul q v
  let a := mul u b
  obtain ⟨h,l,r,hqc⟩ := first_offdiagonal_larger_q_return hf hne hs
  change q = c a (mul (mul y u) k) h l r at hqc
  have haq : sz a < sz q := by rw [hqc]; simp only [sz]; omega
  have hbg : sz q < sz b ∧ origin b = some (q,v) := by
    rcases mul_grows_or_returns q v with hg | ⟨x,t,l',r',hvc,hx⟩
    · exact ⟨hg.1,hg.2.2⟩
    · have hxb : x = b := hx.symm
      rw [hxb] at hvc
      have hqv : sz q < sz v := by rw [hvc]; simp only [sz]; omega
      have hov : origin v = some (u,k) := by
        rcases mul_grows_or_returns u k with hv | ⟨z,t',l'',r'',hkc,hz⟩
        · exact hv.2.2
        · have hzk : sz z < sz k := by rw [hkc]; simp only [sz]; omega
          change v = z at hz
          have hh := congrArg sz hz
          exact False.elim (by omega)
      conv at hov => lhs; rw [hvc,origin]
      obtain ⟨hl,hr⟩ := Prod.mk.inj (Option.some.inj hov)
      subst l'; subst r'
      have hsem := mul_code_semantics (show mul u k = c q b t u k from hvc)
      have bounds := common_column_inputs_small hsem.1 hsem.2
      have hi := inverse_strict_size (inverse_complete u b)
      change sz u < max (sz b) (sz a) at hi
      exact False.elim (by omega)
  obtain ⟨x,j,l',r',hbc⟩ := (mul_small_iff u b).mp (by change sz a < sz b; omega)
  have hxa : x = a := by change x = mul u b; rw [hbc,mul_code_return]
  rw [hxa] at hbc
  have hob := hbg.2
  rw [hbc,origin] at hob
  obtain ⟨hl,hr⟩ := Prod.mk.inj (Option.some.inj hob)
  subst l'; subst r'
  have hsem := mul_code_semantics (show mul q v = c u a j q v from hbc)
  exact ⟨j,hbc,hsem⟩

theorem first_larger_q_height_order {u q k y : T}
    (hf : mul (mul y u) k = mul (mul u (mul q (mul u k))) q)
    (hne : q ≠ k) (hs : sz k ≤ sz q) : ht (mul u k) ≤ ht q := by
  let v := mul u k
  let a := mul u (mul q v)
  obtain ⟨j,hbc,hgq,haj⟩ := first_larger_q_inner_code hf hne hs
  change mul (mul u a) j = q at hgq
  change mul a j = v at haj
  obtain ⟨h,l,r,hqc⟩ := first_offdiagonal_larger_q_return hf hne hs
  change q = c a (mul (mul y u) k) h l r at hqc
  have haq : ht a < ht q := by rw [hqc]; simp only [ht]; omega
  have hqv : q ≠ v := by
    intro heq
    exact mul_ne_right u a (right_injective _ _ j (hgq.trans (heq.trans haj.symm)))
  by_cases hvq : sz v ≤ sz q
  · have hoq := (distinct_outputs_large_origin hgq haj hqv hvq).1
    have hjq := (origin_height hoq).2
    have hp := mul_height_upper a j
    rw [haj] at hp
    change ht v ≤ ht q
    omega
  · have hov := (distinct_outputs_large_origin haj hgq (Ne.symm hqv) (by omega)).1
    have hov' := mul_origin_of_right_le (a:=u) (b:=k) (by change sz k ≤ sz v; omega)
    have heq := Prod.mk.inj (Option.some.inj (hov.symm.trans hov'))
    rw [heq.1,heq.2] at hgq
    have hoq := mul_origin_of_right_le (a:=mul u u) (b:=k) (by rw [hgq]; exact hs)
    rw [hgq] at hoq
    have hkq := (origin_height hoq).2
    have hqg := mul_height_growth_of_right_le (a:=mul u u) (b:=k) (by rw [hgq]; omega)
    rw [hgq,mul_square] at hqg
    simp only [ht] at hqg
    have hv := mul_height_upper u k
    change ht v ≤ ht q
    change ht v ≤ max (ht u) (ht k) + 1 at hv
    omega

theorem normal_first_larger_q_trace {u q k y : T}
    (hu : NF u) (hq : NF q) (hk : NF k)
    (hf : mul (mul y u) k = mul (mul u (mul q (mul u k))) q)
    (hne : q ≠ k) (hs : sz k ≤ sz q) :
    let v := mul u k
    let b := mul q v
    let a := mul u b
    let w := mul (mul y u) k
    ∃ j h, NF a ∧ NF j ∧ b = c u a j q v ∧
      q = c a w h (mul u a) j ∧
      mul (mul u a) j = q ∧ mul a j = v ∧
      mul (mul a w) h = mul u a ∧ mul w h = j ∧
      ht v ≤ ht q ∧ ht u < ht q ∧ ht w < ht q ∧
      ReturnLadder a a (mul u a) w v q j := by
  let v := mul u k
  let b := mul q v
  let a := mul u b
  let w := mul (mul y u) k
  obtain ⟨j,hbc,hgq,haj⟩ := first_larger_q_inner_code hf hne hs
  change b = c u a j q v at hbc
  change mul (mul u a) j = q at hgq
  change mul a j = v at haj
  have hvq := first_larger_q_height_order hf hne hs
  change ht v ≤ ht q at hvq
  have hnb : NF b := nf_mul hq (nf_mul hu hk)
  have hna : NF a := nf_mul hu hnb
  have hnj : NF j := (nf_code_actual (hbc ▸ hnb)).2.2.1
  have hqv : q ≠ v := by
    intro heq
    exact mul_ne_right u a (right_injective _ _ j (hgq.trans (heq.trans haj.symm)))
  have hoq := (distinct_outputs_height_origin hgq haj hqv hvq).1
  obtain ⟨h',l',r',hqc'⟩ := first_offdiagonal_larger_q_return hf hne hs
  change q = c a w h' l' r' at hqc'
  have hwq : ht w < ht q := by rw [hqc']; simp only [ht]; omega
  have haq : mul a q = w := hf.symm
  obtain ⟨h,hqc,_,_,hgh,hwh,_,_⟩ := nf_return_origin_trace hq hoq haq hwq
  have hbg := mul_height_growth_of_right_le (a:=q) (b:=v) (by
    change ht v ≤ ht b
    rw [hbc]; simp only [ht]; omega)
  change ht b = max (ht q) (ht v) + 1 at hbg
  have hub := nf_code_key_height_gap (hbc ▸ hnb)
  rw [←hbc] at hub
  exact ⟨j,h,hna,hnj,hbc,hqc,hgq,haj,hgh,hwh,hvq,by omega,hwq,
    hq,hgq,hoq,haq,haj⟩

end Austin12087Trace
#print axioms Austin12087Trace.first_larger_q_inner_code
#print axioms Austin12087Trace.first_larger_q_height_order
#print axioms Austin12087Trace.normal_first_larger_q_trace

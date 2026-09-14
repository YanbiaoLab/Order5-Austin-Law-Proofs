prelude
import Init.Data.Option.Lemmas
import Init.Omega
import Init.RCases
import Init.WFTactics
import JudgeTraceFactoredTailKey
set_option Elab.async false
/- Checked module: TraceSecondReturningQRepeated -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_second_returning_q_key_repeats {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hs : NormalSecondBelow (ht k))
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u)
    (hqr : ht (mul (mul u a) k) < ht k) :
    mul (mul u a) k = u ∧ y = mul a u := by
  let q := mul (mul u a) k
  let e := mul (mul a q) (mul a k)
  obtain ⟨t,z,h,_,_,_,_,_,hec,hat,htz,hbz,htr,_,_⟩ :=
    normal_second_returning_q_tail_returns hu ha hk hs hf hqr
  change e = c (mul a q) u h (mul (mul u a) q) z at hec
  have hne : NF e := nf_mul (nf_mul ha (nf_mul (nf_mul hu ha) hk)) (nf_mul ha hk)
  have hqu := normal_factored_returning_tail_key_repeats (nf_mul (nf_mul hu ha) hk)
    (hec ▸ hne) (by rw [htz]; exact hat) hbz (by rw [htz]; exact htr)
  change q = u at hqu
  obtain ⟨_,_,_,_,_,_,_,_,_,hwy,_,_,_,_,_,_,_,_⟩ :=
    normal_second_returning_q_head hu ha hk hs hf hqr
  change mul a q = y at hwy
  rw [hqu] at hwy
  exact ⟨hqu,hwy.symm⟩

theorem normal_second_returning_q_repeated_core {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hs : NormalSecondBelow (ht k))
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u)
    (hqr : ht (mul (mul u a) k) < ht k) :
    u ≠ a ∧ mul (mul u a) k = u ∧ y = mul a u ∧
    ∃ t z h s, NF t ∧ NF z ∧ NF h ∧ NF s ∧
      mul u t = a ∧ mul u z = t ∧ mul u h = z ∧
      mul a s = u ∧ mul t s = h ∧
      mul (mul (mul a u) u) h = mul (mul u a) u ∧
      ht u + 3 ≤ ht t ∧ ht a + 2 ≤ ht t ∧
      ht t + 2 ≤ ht z ∧ ht h + 1 = ht z ∧ ht z < ht k := by
  let q := mul (mul u a) k
  let e := mul (mul a q) (mul a k)
  obtain ⟨hqu,hy⟩ := normal_second_returning_q_key_repeats hu ha hk hs hf hqr
  change q = u at hqu
  obtain ⟨t,z,h,hnt,hnz,hnh,_,_,hec,hat,htz,hbz,htr,hze,hek⟩ :=
    normal_second_returning_q_tail_returns hu ha hk hs hf hqr
  change e = c (mul a q) u h (mul (mul u a) q) z at hec
  have hne : NF e := nf_mul (nf_mul ha (nf_mul (nf_mul hu ha) hk)) (nf_mul ha hk)
  have hn := hec ▸ hne
  have hfix : mul u (mul q z) = a := by rw [htz]; exact hat
  have hret : ht (mul q z) < ht z := by rw [htz]; exact htr
  obtain ⟨_,_,hhz,_,hoz⟩ := normal_factored_returning_tail_geometry (nf_mul (nf_mul hu ha) hk) hn hfix hbz hret
  have hatret := normal_factored_returning_tail_output_returns (nf_mul (nf_mul hu ha) hk) hn hfix hbz hret
  rw [htz] at hatret
  have hgap := nf_mul_height_key_gap (a:=u) hnt
  rw [hat] at hgap
  have hut : ht u + 3 ≤ ht t ∧ ht a + 2 ≤ ht t := by rcases hgap with hh | hh <;> omega
  have hc := nf_code_actual hn
  have hzh : mul u h = z := hc.2.2.2.2.2.2.2
  have hbh : mul (mul (mul a u) u) h = mul (mul u a) u := by
    have hh := hc.2.2.2.2.2.2.1
    rw [hqu] at hh
    exact hh
  change mul q z = t at htz
  rw [hqu] at htz
  obtain ⟨s,_,hns,_,has,hhs,_,_⟩ := nf_return_origin_trace hnz hoz htz htr
  rw [hat] at has
  have htg := nf_mul_height_key_gap (a:=u) hnz
  rw [htz] at htg
  have ht2 : ht t + 2 ≤ ht z := by rcases htg with hh | hh <;> omega
  exact ⟨normal_second_returning_q_inputs_distinct hu ha hk hs hf hqr,hqu,hy,
    t,z,h,s,hnt,hnz,hnh,hns,hat,htz,hzh,has,hhs,hbh,hut.1,hut.2,ht2,hhz,by omega⟩

end submission.Austin12087Trace

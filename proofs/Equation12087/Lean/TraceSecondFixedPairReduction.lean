prelude
import TraceSecondEqualKey
set_option autoImplicit false

namespace Austin12087Trace
open T

theorem normal_second_equal_input_q_fixed_pair {u k y : T}
    (hu : NF u) (hk : NF k)
    (hs : NormalSecondBelow (ht k))
    (hf : mul y (mul (mul u (mul (mul u u) k)) (mul u k)) = u)
    (hqr : ht (mul (mul u u) k) < ht k) :
    let b := mul (mul u u) u
    ∃ s, NF s ∧ ht s < ht k ∧
      mul u (mul b s) = u ∧ mul u (mul (mul b b) s) = u := by
  let q := mul (mul u u) k
  let w := mul u q
  let b := mul (mul u u) q
  let e := mul w (mul u k)
  obtain ⟨t,z,h,_,hnz,hnh,_,hkc,hec,_,hat,hbh,hzh,_,hhead,_,hek,_⟩ :=
    normal_second_returning_q_head hu hu hk hs hf hqr
  change k = c (mul u u) q z e t at hkc
  change e = c w u h b z at hec
  change mul u t = u at hat
  change mul (mul w u) h = b at hbh
  change mul u h = z at hzh
  change max (ht u) (ht q) < ht e at hhead
  change ht e < ht k at hek
  have hkc' : NF (c (mul u u) q z e t) := hkc ▸ hk
  have htz : mul q z = t := (nf_code_actual hkc').2.2.2.2.2.2.2
  have hnq : NF q := nf_mul (nf_mul hu hu) hk
  have hne : NF e := nf_mul (nf_mul hu hnq) (nf_mul hu hk)
  have hec' : NF (c w u h b z) := hec ▸ hne
  have hsmall : ht q < ht (c w u h b z) := by rw [← hec]; omega
  have hfixed : mul u (mul q z) = u := by rw [htz]; exact hat
  have hbz := normal_fixed_code_head_order hu hnq hec' hsmall hfixed
  have hqu := normal_equal_code_key_repeats hu hnq hec' hsmall hbz hfixed
  have htr := normal_equal_code_tail_returns hu hnq hec' hsmall hbz hfixed
  rw [htz] at htr
  obtain ⟨hu3,_,hhz,hb2,hoz⟩ := normal_equal_code_geometry hnq hec' hsmall hbz
  change ht b + 2 ≤ ht h at hb2
  have hww : w = mul u u := by change mul u q = mul u u; rw [hqu]
  have hb : b = mul (mul u u) u := by change mul (mul u u) q = mul (mul u u) u; rw [hqu]
  have htuz : mul u z = t := by rw [← hqu]; exact htz
  obtain ⟨r,_,_,_,hur,hhr,hrgap,_⟩ := nf_return_origin_trace hnz hoz htuz htr
  rw [hat] at hur
  have hoh := mul_origin_of_right_height_le (a:=t) (b:=r) (by rw [hhr]; omega)
  rw [hhr] at hoh
  have hbfixed : mul b h = b := by rw [hww,← hb] at hbh; exact hbh
  obtain ⟨s,_,hns,_,hts,hrs,hsgap,_⟩ := nf_return_origin_trace hnh hoh hbfixed (by omega)
  have hhsmall : ht h < ht e := by
    have hh := nf_code_height_gap hec'
    rw [← hec] at hh
    exact Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (Nat.zero_lt_succ 1)) hh.2.2
  refine ⟨s,hns,by omega,?_,?_⟩
  · rw [← hb,hrs]
    exact hur
  · rw [← hb,hts]
    exact hat

end Austin12087Trace
#print axioms Austin12087Trace.normal_second_equal_input_q_fixed_pair

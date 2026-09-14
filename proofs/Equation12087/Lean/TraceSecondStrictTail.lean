prelude
import TraceSecondEqualReturnClosed
set_option autoImplicit false

namespace Austin12087Trace
open T

theorem normal_factored_code_equal_tail_inputs {u a q h z : T}
    (hnq : NF q)
    (hn : NF (c (mul a q) u h (mul (mul u a) q) z))
    (hfix : mul u (mul q z) = a)
    (hae : ht a < ht (c (mul a q) u h (mul (mul u a) q) z))
    (hte : ht (mul q z) = ht (c (mul a q) u h (mul (mul u a) q) z)) : u = a := by
  let b := mul (mul u a) q
  let w := mul a q
  let e := c w u h b z
  let t := mul q z
  change NF e at hn
  change mul u t = a at hfix
  change ht a < ht e at hae
  change ht t = ht e at hte
  have hc := nf_code_actual hn
  have hgap := nf_code_height_gap hn
  change ht w + 2 ≤ ht e ∧ ht u + 2 ≤ ht e ∧ ht h + 2 ≤ ht e at hgap
  have hob : origin e = some (b,z) := rfl
  have hb := (origin_height hob).1
  have hz := (origin_height hob).2
  have hcol := common_column_height_bounds
    (show mul (mul u a) q = b from rfl) (show mul a q = w from rfl)
  have hq : ht q + 2 ≤ ht e := by omega
  have htg := mul_height_growth_of_right_le (a:=q) (b:=z) (by change ht z ≤ ht t; omega)
  change ht t = max (ht q) (ht z) + 1 at htg
  have hze : ht z + 1 = ht e := by omega
  have hot := mul_origin_of_right_height_le (a:=q) (b:=z) (by change ht z ≤ ht t; omega)
  change origin t = some (q,z) at hot
  have hnt : NF t := nf_mul hnq hc.2.2.2.2.1
  obtain ⟨s,_,_,_,_,hzs,hsgap,_⟩ := nf_return_origin_trace hnt hot hfix (by omega)
  have hzh : mul u h = z := hc.2.2.2.2.2.2.2
  have hoz₁ := mul_origin_of_right_height_le (a:=u) (b:=h) (by rw [hzh]; omega)
  rw [hzh] at hoz₁
  have hoz₂ := mul_origin_of_right_height_le (a:=a) (b:=s) (by rw [hzs]; omega)
  rw [hzs] at hoz₂
  exact (Prod.mk.inj (Option.some.inj (hoz₁.symm.trans hoz₂))).1

theorem normal_second_returning_q_strict_tail {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hs : NormalSecondBelow (ht k))
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u)
    (hqr : ht (mul (mul u a) k) < ht k) :
    let g := mul u a
    let q := mul g k
    let v := mul a k
    let w := mul a q
    let e := mul w v
    ∃ t z h, NF t ∧ NF z ∧ NF h ∧
      v = c w e t a k ∧ k = c g q z e t ∧ e = c w u h (mul g q) z ∧
      mul u t = a ∧ mul q z = t ∧ ht t < ht e ∧ ht e < ht k := by
  let g := mul u a
  let q := mul g k
  let v := mul a k
  let w := mul a q
  let e := mul w v
  obtain ⟨t,z,h,hnt,hnz,hnh,hvc,hkc,hec,_,hat,_,_,hte,hhead,_,hek,_⟩ :=
    normal_second_returning_q_head hu ha hk hs hf hqr
  change v = c w e t a k at hvc
  change k = c g q z e t at hkc
  change e = c w u h (mul g q) z at hec
  change mul u t = a at hat
  change ht t ≤ ht e at hte
  change max (ht a) (ht q) < ht e at hhead
  change ht e < ht k at hek
  have htz : mul q z = t := (nf_code_actual (hkc ▸ hk)).2.2.2.2.2.2.2
  have hne : NF e := nf_mul (nf_mul ha (nf_mul (nf_mul hu ha) hk)) (nf_mul ha hk)
  have hstrict : ht t < ht e := by
    by_cases hh : ht t < ht e
    · exact hh
    · have hua := normal_factored_code_equal_tail_inputs (nf_mul (nf_mul hu ha) hk) (hec ▸ hne)
        (by rw [htz]; exact hat) (by rw [← hec]; omega) (by rw [htz,← hec]; omega)
      exact False.elim ((normal_second_returning_q_inputs_distinct hu ha hk hs hf hqr) hua)
  exact ⟨t,z,h,hnt,hnz,hnh,hvc,hkc,hec,hat,htz,hstrict,hek⟩

end Austin12087Trace
#print axioms Austin12087Trace.normal_factored_code_equal_tail_inputs
#print axioms Austin12087Trace.normal_second_returning_q_strict_tail

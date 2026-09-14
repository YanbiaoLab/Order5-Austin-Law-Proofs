prelude
import TraceSecondColumnAlternatives
set_option autoImplicit false

namespace Austin12087Trace
open T

theorem normal_second_returning_v_trace {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u)
    (hvr : ht (mul a k) < ht k) :
    let g := mul u a
    let q := mul g k
    let v := mul a k
    let w := mul a q
    ∃ r s, NF r ∧ NF s ∧ q = c a w r g k ∧ k = c a v s w r ∧
      mul (mul a w) r = g ∧ mul w r = k ∧
      mul (mul a v) s = w ∧ mul v s = r ∧
      ht w < ht k ∧ ht r < ht k ∧ ht s + 2 ≤ ht k ∧
      ReturnLadder a a g w v q k := by
  let g := mul u a
  let q := mul g k
  let v := mul a k
  let w := mul a q
  have hqg : ht k < ht q := by
    rcases normal_second_column_alternatives hu ha hk hf with hh | hh
    · exact False.elim (by omega)
    · exact hh.2
  obtain ⟨r,hnr,hqc,hgr,hkr,hq,hw,hr⟩ := normal_second_growing_q_head hu ha hk hf (by change ht k ≤ ht q; omega)
  change q = c a w r g k at hqc
  change mul w r = k at hkr
  have hok := mul_origin_of_right_height_le (a:=w) (b:=r) (by rw [hkr]; omega)
  rw [hkr] at hok
  obtain ⟨s,hkc,hns,_,hws,hrs,hsgap,_⟩ :=
    nf_return_origin_trace hk hok (show mul a k = v from rfl) hvr
  have hoq := mul_origin_of_right_height_le (a:=g) (b:=k) (by change ht k ≤ ht q; omega)
  change origin q = some (g,k) at hoq
  have hnq : NF q := nf_mul (nf_mul hu ha) hk
  change ∃ r s, NF r ∧ NF s ∧ q = c a w r g k ∧ k = c a v s w r ∧
    mul (mul a w) r = g ∧ mul w r = k ∧ mul (mul a v) s = w ∧
    mul v s = r ∧ ht w < ht k ∧ ht r < ht k ∧ ht s + 2 ≤ ht k ∧
    ReturnLadder a a g w v q k
  exact ⟨r,s,hnr,hns,hqc,hkc,hgr,hkr,hws,hrs,hw,hr,hsgap,
    hnq,rfl,hoq,rfl,rfl⟩

theorem normal_second_returning_q_trace {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hs : NormalSecondBelow (ht k))
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u)
    (hqr : ht (mul (mul u a) k) < ht k) :
    let g := mul u a
    let q := mul g k
    let v := mul a k
    let w := mul a q
    let e := mul w v
    ∃ t z, NF t ∧ NF z ∧ v = c w e t a k ∧ k = c g q z e t ∧
      mul (mul w e) t = a ∧ mul e t = k ∧
      mul (mul g q) z = e ∧ mul q z = t ∧
      ht e < ht k ∧ ht t < ht k ∧ ht z + 2 ≤ ht k ∧
      ReturnLadder g (mul w e) e q a k t := by
  let g := mul u a
  let q := mul g k
  let v := mul a k
  let w := mul a q
  let e := mul w v
  change ht q < ht k at hqr
  have hb := normal_second_query_k_dominates hu ha hk hf
  have hvg : ht k < ht v := by
    rcases normal_second_column_alternatives hu ha hk hf with hh | hh
    · exact hh.2
    · change ht v < ht k ∧ ht k < ht q at hh
      exact False.elim (by omega)
  have her : ht e < ht v := by
    by_cases hh : ht e < ht v
    · exact hh
    · exact False.elim (normal_second_returning_q_growing_middle_impossible hu ha hk hs hf hqr (by change ht v ≤ ht e; omega))
  have hv := mul_height_growth_of_right_le (a:=a) (b:=k) (by change ht k ≤ ht v; omega)
  change ht v = max (ht a) (ht k) + 1 at hv
  have hov := mul_origin_of_right_height_le (a:=a) (b:=k) (by change ht k ≤ ht v; omega)
  change origin v = some (a,k) at hov
  have hnv : NF v := nf_mul ha hk
  obtain ⟨t,hvc,hnt,_,hat,hkt,htgap,_⟩ :=
    nf_return_origin_trace hnv hov (show mul w v = e from rfl) her
  have hgap := nf_mul_height_key_gap (a:=w) hnv
  change ht e = max (ht w) (ht v) + 1 ∨ (ht w + 3 ≤ ht v ∧ ht e + 2 ≤ ht v) at hgap
  have hegap : ht e + 2 ≤ ht v := by rcases hgap with hh | hh <;> omega
  have hok := mul_origin_of_right_height_le (a:=e) (b:=t) (by rw [hkt]; omega)
  rw [hkt] at hok
  obtain ⟨z,hkc,hnz,_,hez,htz,hzgap,_⟩ :=
    nf_return_origin_trace hk hok (show mul g k = q from rfl) hqr
  change ∃ t z, NF t ∧ NF z ∧ v = c w e t a k ∧ k = c g q z e t ∧
    mul (mul w e) t = a ∧ mul e t = k ∧ mul (mul g q) z = e ∧
    mul q z = t ∧ ht e < ht k ∧ ht t < ht k ∧ ht z + 2 ≤ ht k ∧
    ReturnLadder g (mul w e) e q a k t
  exact ⟨t,z,hnt,hnz,hvc,hkc,hat,hkt,hez,htz,by omega,by omega,hzgap,
    hk,hkt,hok,rfl,hat⟩

end Austin12087Trace
#print axioms Austin12087Trace.normal_second_returning_v_trace
#print axioms Austin12087Trace.normal_second_returning_q_trace

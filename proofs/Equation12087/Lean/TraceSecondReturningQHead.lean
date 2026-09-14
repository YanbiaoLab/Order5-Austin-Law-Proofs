prelude
import TraceFactoredLadderHead
set_option autoImplicit false

namespace Austin12087Trace
open T

theorem normal_second_returning_q_head {u a k y : T}
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
      w = y ∧ mul u t = a ∧ mul (mul w u) h = mul g q ∧ mul u h = z ∧
      ht t ≤ ht e ∧ max (ht a) (ht q) < ht e ∧ ht g < ht e ∧
      ht e < ht k ∧ ReturnLadder g u e q a k t := by
  let g := mul u a
  let q := mul g k
  let v := mul a k
  let w := mul a q
  let e := mul w v
  obtain ⟨t,z,hnt,hnz,hvc,hkc,hat,hkt,hez,htz,hek,htk,hzgap,hl⟩ :=
    normal_second_returning_q_trace hu ha hk hs hf hqr
  change v = c w e t a k at hvc
  change k = c g q z e t at hkc
  change mul (mul w e) t = a at hat
  change mul (mul g q) z = e at hez
  change mul q z = t at htz
  change ht e < ht k at hek
  change ReturnLadder g (mul w e) e q a k t at hl
  have hnq : NF q := nf_mul (nf_mul hu ha) hk
  have hne : NF e := nf_mul (nf_mul ha hnq) (nf_mul ha hk)
  have hhead := factored_return_ladder_head_order hnq hl hqr
  change max (ht a) (ht q) < ht e ∧ ht g < ht e ∧ ht (mul w e) < ht e at hhead
  have hou := normal_second_returning_q_outer_returns hu ha hk hf hqr
  change ht u < ht e at hou
  change mul y e = u at hf
  obtain ⟨j,l,r,hec₁⟩ := mul_return_of_height_lt hhead.2.2
  obtain ⟨j',l',r',hec₂⟩ := mul_return_of_height_lt (a:=y) (b:=e) (by rw [hf]; exact hou)
  rw [hf] at hec₂
  have hp := T.c.inj (hec₁.symm.trans hec₂)
  have hwy : w = y := hp.1
  have hwu : mul w e = u := hp.2.1
  rw [hwu] at hat hl hec₁
  have hte := factored_return_ladder_tail_stops hl hec₁ (by omega) (by omega) hqr
  have het : e ≠ t := by
    intro heq
    exact mul_ne_right g q (right_injective _ _ z (hez.trans (heq.trans htz.symm)))
  have hoe := (distinct_outputs_height_origin hez htz het (by omega)).1
  obtain ⟨h,hec,hnh,_,hbh,hzh,_,_⟩ := nf_return_origin_trace hne hoe hwu hou
  change ∃ t z h, NF t ∧ NF z ∧ NF h ∧ v = c w e t a k ∧
    k = c g q z e t ∧ e = c w u h (mul g q) z ∧ w = y ∧ mul u t = a ∧
    mul (mul w u) h = mul g q ∧ mul u h = z ∧ ht t ≤ ht e ∧
    max (ht a) (ht q) < ht e ∧ ht g < ht e ∧ ht e < ht k ∧
    ReturnLadder g u e q a k t
  exact ⟨t,z,h,hnt,hnz,hnh,hvc,hkc,hec,hwy,hat,hbh,hzh,hte,hhead.1,hhead.2.1,hek,hl⟩

end Austin12087Trace
#print axioms Austin12087Trace.normal_second_returning_q_head

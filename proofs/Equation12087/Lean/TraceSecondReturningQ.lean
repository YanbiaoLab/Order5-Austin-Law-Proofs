prelude
import TraceLocalSecondInduction
set_option autoImplicit false

namespace Austin12087Trace
open T

theorem normal_second_returning_q_growing_middle_impossible {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hs : NormalSecondBelow (ht k))
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u)
    (hqr : ht (mul (mul u a) k) < ht k)
    (hmid : ht (mul a k) ≤ ht (mul (mul a (mul (mul u a) k)) (mul a k))) : False := by
  let g := mul u a
  let q := mul g k
  let v := mul a k
  let w := mul a q
  let e := mul w v
  change ht q < ht k at hqr
  change ht v ≤ ht e at hmid
  change mul y e = u at hf
  have hbounds := normal_second_query_k_dominates hu ha hk hf
  obtain ⟨z,l,r,hkc⟩ := mul_return_of_height_lt (a:=g) (b:=k) hqr
  change k = c g q z l r at hkc
  have hvg := mul_height_off_return_key (a:=a) hkc (Ne.symm (mul_ne_right u a))
  change ht v = max (ht a) (ht k) + 1 at hvg
  have hov := mul_origin_of_right_height_le (a:=a) (b:=k) (by change ht k ≤ ht v; omega)
  change origin v = some (a,k) at hov
  have hwu := mul_height_upper a q
  change ht w ≤ max (ht a) (ht q) + 1 at hwu
  have heg := mul_height_growth_of_right_le (a:=w) (b:=v) hmid
  change ht e = max (ht w) (ht v) + 1 at heg
  have hoe := mul_origin_of_right_height_le (a:=w) (b:=v) hmid
  change origin e = some (w,v) at hoe
  have hne : NF e := nf_mul (nf_mul ha (nf_mul (nf_mul hu ha) hk)) (nf_mul ha hk)
  obtain ⟨t,_,_,_,hwt,hvt,_,_⟩ := nf_return_origin_trace hne hoe hf (by omega)
  have hvw : v ≠ w := by intro heq; have hh := congrArg ht heq; omega
  have hov' := (distinct_outputs_height_origin hvt hwt hvw (by omega)).1
  have hp := Prod.mk.inj (Option.some.inj (hov'.symm.trans hov))
  have hua : u = a := hp.1
  rw [hp.2] at hwt
  have hsrc := normal_source_of_second_below ha hu hk (by
    have hh : max (ht a) (ht k) = ht k := by omega
    rw [hh]
    exact hs)
  change a = mul u (mul q v) at hsrc
  have hvk : mul u k = v := by rw [hua]
  have hinner : mul u (mul q (mul u k)) = a := by rw [hvk]; exact hsrc.symm
  have hfirst : mul (mul y u) k = mul (mul u (mul q (mul u k))) q := by
    rw [hinner]
    exact hwt
  have hsize : sz q < sz k := by rw [hkc]; simp only [sz]; omega
  exact normal_first_larger_k_equation_impossible hu hk hfirst
    (by intro heq; have hh := congrArg ht heq; omega) (by omega)

end Austin12087Trace
#print axioms Austin12087Trace.normal_second_returning_q_growing_middle_impossible

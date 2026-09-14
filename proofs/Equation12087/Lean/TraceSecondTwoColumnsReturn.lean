prelude
import TraceSecondGrowingQHead
set_option autoImplicit false

namespace Austin12087Trace
open T

theorem normal_second_two_growing_columns_returning_middle_impossible {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u)
    (hqg : ht k ≤ ht (mul (mul u a) k))
    (hvg : ht k ≤ ht (mul a k))
    (hm : ht (mul (mul a (mul (mul u a) k)) (mul a k)) < ht (mul a k)) : False := by
  let g := mul u a
  let q := mul g k
  let v := mul a k
  let w := mul a q
  let e := mul w v
  change ht k ≤ ht v at hvg
  change ht e < ht v at hm
  change mul y e = u at hf
  have hb := normal_second_query_k_dominates hu ha hk hf
  obtain ⟨r,hnr,hqc,hgr,hkr,hq,hw,hr⟩ := normal_second_growing_q_head hu ha hk hf hqg
  change q = c a w r g k at hqc
  change mul (mul a w) r = g at hgr
  change mul w r = k at hkr
  change ht w < ht k at hw
  have hv := mul_height_growth_of_right_le (a:=a) (b:=k) hvg
  change ht v = max (ht a) (ht k) + 1 at hv
  have hov := mul_origin_of_right_height_le (a:=a) (b:=k) hvg
  change origin v = some (a,k) at hov
  have hnv : NF v := nf_mul ha hk
  obtain ⟨t,_,_,_,hat,hkt,htgap,_⟩ :=
    nf_return_origin_trace hnv hov (show mul w v = e from rfl) hm
  have hok := mul_origin_of_right_height_le (a:=w) (b:=r) (by rw [hkr]; omega)
  rw [hkr] at hok
  have hok' := mul_origin_of_right_height_le (a:=e) (b:=t) (by rw [hkt]; omega)
  rw [hkt] at hok'
  have hp := Prod.mk.inj (Option.some.inj (hok'.symm.trans hok))
  have hew : e = w := hp.1
  have htr : t = r := hp.2
  rw [hew,htr] at hat
  rw [hew] at hf
  have hag : a = mul (mul w w) r := hat.symm
  have hg : mul (mul y w) (mul (mul w w) r) = mul (mul (mul (mul w w) r) w) r := by
    rw [← hag,hf]
    exact hgr.symm
  exact square_column_transport_impossible w y r hg

end Austin12087Trace
#print axioms Austin12087Trace.normal_second_two_growing_columns_returning_middle_impossible

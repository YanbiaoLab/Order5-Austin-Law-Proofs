prelude
import TraceOuterGrowthLadder
set_option autoImplicit false

namespace Austin12087Trace
open T

theorem normal_second_returning_q_outer_growth_impossible {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u)
    (hqr : ht (mul (mul u a) k) < ht k)
    (houter : ht (mul (mul a (mul (mul u a) k)) (mul a k)) ≤ ht u) : False := by
  let g := mul u a
  let q := mul g k
  let v := mul a k
  let w := mul a q
  let e := mul w v
  change mul y e = u at hf
  change ht e ≤ ht u at houter
  have hug := mul_height_growth_of_right_le (a:=y) (b:=e) (by rw [hf]; exact houter)
  rw [hf] at hug
  have hvg : ht k < ht v := by
    rcases normal_second_column_alternatives hu ha hk hf with hh | hh
    · exact hh.2
    · exact False.elim (by omega)
  have her : ht e < ht v := by
    by_cases hh : ht e < ht v
    · exact hh
    · exact False.elim (normal_second_double_growth_impossible hu ha hk hf (by change ht v ≤ ht e; omega) houter)
  have hb := normal_second_query_k_dominates hu ha hk hf
  have hv := mul_height_growth_of_right_le (a:=a) (b:=k) (by change ht k ≤ ht v; omega)
  change ht v = max (ht a) (ht k) + 1 at hv
  have hov := mul_origin_of_right_height_le (a:=a) (b:=k) (by change ht k ≤ ht v; omega)
  change origin v = some (a,k) at hov
  have hnv : NF v := nf_mul ha hk
  have hnq : NF q := nf_mul (nf_mul hu ha) hk
  obtain ⟨t,_,_,_,hat,hkt,htgap,_⟩ :=
    nf_return_origin_trace hnv hov (show mul w v = e from rfl) her
  have hok := mul_origin_of_right_height_le (a:=e) (b:=t) (by rw [hkt]; omega)
  rw [hkt] at hok
  have hl : ReturnLadder g (mul w e) e q a k t := ⟨hk,hkt,hok,rfl,hat⟩
  exact outer_growth_return_ladder_impossible ha hnq (by omega) hl hqr

theorem normal_second_returning_q_outer_returns {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u)
    (hqr : ht (mul (mul u a) k) < ht k) :
    ht u < ht (mul (mul a (mul (mul u a) k)) (mul a k)) := by
  by_cases hh : ht u < ht (mul (mul a (mul (mul u a) k)) (mul a k))
  · exact hh
  · exact False.elim (normal_second_returning_q_outer_growth_impossible hu ha hk hf hqr (by omega))

end Austin12087Trace
#print axioms Austin12087Trace.normal_second_returning_q_outer_growth_impossible
#print axioms Austin12087Trace.normal_second_returning_q_outer_returns

prelude
import TraceLowLadderTailStop
set_option autoImplicit false

namespace Austin12087Trace
open T

theorem normal_second_v_growing_middle_w_max_height {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hs : NormalSecondBelow (ht k))
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u)
    (hvr : ht (mul a k) < ht k)
    (hmid : ht (mul a k) ≤ ht (mul (mul a (mul (mul u a) k)) (mul a k)))
    (hvw : ht (mul a k) < ht (mul a (mul (mul u a) k)))
    (hgw : ht (mul u a) ≤ ht (mul a (mul (mul u a) k))) :
    let g := mul u a
    let v := mul a k
    let w := mul a (mul g k)
    ht k = ht w + 4 ∧ mul a v = a ∧ mul (mul a w) g ≠ a := by
  let g := mul u a
  let v := mul a k
  let w := mul a (mul g k)
  let B := mul (mul a w) g
  change ht k = ht w + 4 ∧ mul a v = a ∧ B ≠ a
  obtain ⟨r,s,t,j,_,_,hnt,_,_,_,hws,hst,hvt,hks,_,hts,_,hv2,_,_,_,_,_,_,hl⟩ :=
    normal_second_v_growing_middle_ladder hu ha hk hf hvr hmid
  change ht v < ht w at hvw
  change ht g ≤ ht w at hgw
  change ht v + 2 ≤ ht t at hv2
  change mul B t = v at hvt
  change ReturnLadder B (mul (mul a v) w) w v g t j at hl
  have hbounds := normal_second_query_k_dominates hu ha hk hf
  obtain ⟨_,hDa,_⟩ := normal_low_ladder_w_max_forces_fixed hl (by omega) (by omega) hgw
  have hBa : B ≠ a := by
    intro hB
    exact normal_second_v_low_equal_keys_descent_impossible hu ha hnt hs hbounds.1 hbounds.2
      (by omega) hf hws hvt hst hB hDa
  have hnv : NF v := nf_mul ha hk
  have hjw := normal_low_ladder_w_max_tail_stops hnv hl (by omega) hvw hgw hBa
  have htHeight := mul_height_growth_of_left_ge (a:=w) (b:=j) hjw
  rw [hl.2.1] at htHeight
  exact ⟨by omega,hDa,hBa⟩

end Austin12087Trace
#print axioms Austin12087Trace.normal_second_v_growing_middle_w_max_height

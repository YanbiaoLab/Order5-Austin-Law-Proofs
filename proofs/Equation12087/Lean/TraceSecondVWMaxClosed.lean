prelude
import TraceLowShortTailConflict
set_option autoImplicit false

namespace Austin12087Trace
open T

theorem normal_low_ladder_w_max_impossible {u a v w t j y : T}
    (hnv : NF v) (hnw : NF w)
    (hl : ReturnLadder (mul (mul a w) (mul u a)) (mul (mul a v) w) w v (mul u a) t j)
    (hf : mul y (mul w v) = u)
    (hvt : ht v < ht t) (hvw : ht v < ht w) (hgw : ht (mul u a) ≤ ht w)
    (hBa : mul (mul a w) (mul u a) ≠ a) : False := by
  let g := mul u a
  let A := mul a w
  let B := mul A g
  let F := mul B v
  obtain ⟨hAw,hav,_⟩ := normal_low_ladder_w_max_forces_fixed hl hvt (by omega) hgw
  have hjw := normal_low_ladder_w_max_tail_stops hnv hl hvt hvw hgw hBa
  rw [hav] at hl
  change ReturnLadder B A w v g t j at hl
  have htHeight := mul_height_growth_of_left_ge (a:=w) (b:=j) hjw
  rw [hl.2.1] at htHeight
  obtain ⟨l,_,hnl,hnj,hFl,hvl,hlGap,_⟩ := nf_return_origin_trace hl.1 hl.2.2.1 hl.2.2.2.1 hvt
  change mul F l = w at hFl
  have how := mul_origin_of_right_height_le (a:=F) (b:=l) (by rw [hFl]; omega)
  rw [hFl] at how
  obtain ⟨n,_,_,_,hHn,hAn,hnGap,_⟩ := nf_return_origin_trace hnw how (show mul a w = A from rfl) hAw
  have hne := nf_mul hnw hnv
  have heHeight := mul_height_growth_of_left_ge (a:=w) (b:=v) (by omega)
  have hoe := mul_origin_of_right_height_le (a:=w) (b:=v) (by omega)
  have ha := inverse_height_strict (inverse_complete a v)
  rw [hav] at ha
  have hu := inverse_height_strict (inverse_complete u a)
  have houter : ht u < ht (mul w v) := by omega
  obtain ⟨z,_,_,_,hYz,huz,hzGap,_⟩ := nf_return_origin_trace hne hoe hf houter
  have how' := mul_origin_of_right_height_le (a:=mul y u) (b:=z) (by rw [hYz]; omega)
  rw [hYz] at how'
  have hp := Prod.mk.inj (Option.some.inj (how.symm.trans how'))
  have hyu : mul y u = F := hp.1.symm
  have hul : mul u l = v := by rw [hp.2]; exact huz
  exact normal_low_short_tail_conflict hnv hnj hnl hav hBa hyu hul hvl hFl hAn hHn
    hl.2.2.2.2 hnGap (by omega)

theorem normal_second_v_growing_middle_w_max_impossible {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hs : NormalSecondBelow (ht k))
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u)
    (hvr : ht (mul a k) < ht k)
    (hmid : ht (mul a k) ≤ ht (mul (mul a (mul (mul u a) k)) (mul a k)))
    (hvw : ht (mul a k) < ht (mul a (mul (mul u a) k)))
    (hgw : ht (mul u a) ≤ ht (mul a (mul (mul u a) k))) : False := by
  have hBa := (normal_second_v_growing_middle_w_max_height hu ha hk hs hf hvr hmid hvw hgw).2.2
  obtain ⟨r,s,t,j,_,_,_,_,_,_,_,_,_,_,_,_,_,hv2,_,_,_,_,_,_,hl⟩ :=
    normal_second_v_growing_middle_ladder hu ha hk hf hvr hmid
  have hnv := nf_mul ha hk
  have hnw := nf_mul ha (nf_mul (nf_mul hu ha) hk)
  exact normal_low_ladder_w_max_impossible hnv hnw hl hf (by omega) hvw hgw hBa

end Austin12087Trace
#print axioms Austin12087Trace.normal_low_ladder_w_max_impossible
#print axioms Austin12087Trace.normal_second_v_growing_middle_w_max_impossible

prelude
import TraceVHeadKeyRigidity
set_option autoImplicit false

namespace Austin12087Trace
open T

theorem normal_v_head_cycle_impossible {u a v w t j y : T}
    (ha : NF a) (hnv : NF v) (hnw : NF w)
    (hl : ReturnLadder (mul (mul a w) (mul u a)) (mul (mul a v) w) w v (mul u a) t j)
    (hf : mul y (mul w v) = u) (houter : ht u < ht (mul w v))
    (hmid : ht v ≤ ht (mul w v))
    (hvt : ht v < ht t) (hwv : ht w < ht v) (hgv : ht (mul u a) ≤ ht v)
    (hB : mul (mul a w) (mul u a) = a) (hDa : mul a v ≠ a)
    (hDv : ht (mul a v) < ht v) : False := by
  let g := mul u a
  let D := mul a v
  let C := mul D w
  let K := mul C g
  have hK := normal_changed_key_growth ha hB hDa
  change ht K = max (ht C) (ht g) + 1 ∧ ht u < ht K ∧ ht a < ht K at hK
  change ht g ≤ ht v at hgv
  change ht D < ht v at hDv
  rw [hB] at hl
  change ReturnLadder a C w v g t j at hl
  obtain ⟨zv,lv,rv,hvc⟩ := mul_return_of_height_lt (a:=a) (b:=v) hDv
  have heHeight := mul_height_growth_of_right_le (a:=w) (b:=v) hmid
  have hoe := mul_origin_of_right_height_le (a:=w) (b:=v) hmid
  obtain ⟨z,_,_,_,_,huz,hzGap,_⟩ := nf_return_origin_trace (nf_mul hnw hnv) hoe hf houter
  have hov := mul_origin_of_right_height_le (a:=u) (b:=z) (by rw [huz]; omega)
  rw [huz] at hov
  have htHeight := mul_height_growth_of_right_le (a:=w) (b:=j) (by
    rw [hl.2.1]; exact Nat.le_of_lt (origin_height hl.2.2.1).2)
  rw [hl.2.1] at htHeight
  obtain ⟨l,_,hnl,hnj,hDl,hvl,hlGap,_⟩ := nf_return_origin_trace hl.1 hl.2.2.1 hl.2.2.2.1 hvt
  change mul D l = w at hDl
  have hoj := mul_origin_of_right_height_le (a:=v) (b:=l) (by rw [hvl]; omega)
  rw [hvl] at hoj
  have hgGap := nf_mul_height_key_gap (a:=C) hnj
  rw [hl.2.2.2.2] at hgGap
  have hgj : ht g < ht j := by rcases hgGap with hh | hh <;> omega
  obtain ⟨m,_,_,_,hKm,hgm,hmGap,_⟩ := nf_return_origin_trace hnj hoj hl.2.2.2.2 hgj
  change mul K m = v at hKm
  have hvm : ht v < ht m := by
    rcases mul_height_shape K m with hg | ⟨x,z',l',r',hm,ho⟩
    · rw [hKm,hov] at hg
      have hp := Prod.mk.inj (Option.some.inj hg.2.2)
      have hh := congrArg ht hp.1
      omega
    · have hx : x = v := ho.symm.trans hKm
      rw [hx] at hm
      rw [hm]; simp only [ht]; omega
  have hjHeight := mul_height_growth_of_right_le (a:=v) (b:=l) (by rw [hvl]; omega)
  rw [hvl] at hjHeight
  have hol := mul_origin_of_right_height_le (a:=g) (b:=m) (by rw [hgm]; omega)
  rw [hgm] at hol
  have hl₂ : ReturnLadder D K g w v l m := ⟨hnl,hgm,hol,hDl,hKm⟩
  obtain ⟨n,hl₃,_⟩ := return_ladder_step hl₂ (by omega) (by omega)
  change ReturnLadder K C w v g m n at hl₃
  have hKa := normal_ladder_first_key_of_highest_return hvc hl₃ hvm hwv hgv
  have hh := congrArg ht hKa
  omega

theorem normal_second_v_growing_middle_impossible {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hs : NormalSecondBelow (ht k))
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u)
    (hvr : ht (mul a k) < ht k)
    (hmid : ht (mul a k) ≤ ht (mul (mul a (mul (mul u a) k)) (mul a k))) : False := by
  obtain ⟨hwv,hgv⟩ := normal_second_v_growing_middle_frontier hu ha hk hs hf hvr hmid
  obtain ⟨hBa,hDa,hDv⟩ := normal_second_v_growing_middle_key_frontier hu ha hk hs hf hvr hmid
  obtain ⟨r,s,t,j,_,_,_,_,_,_,_,_,_,_,_,_,_,hv2,_,_,_,_,_,_,hl⟩ :=
    normal_second_v_growing_middle_ladder hu ha hk hf hvr hmid
  have hnw := nf_mul ha (nf_mul (nf_mul hu ha) hk)
  have hnv := nf_mul ha hk
  have houter : ht u < ht (mul (mul a (mul (mul u a) k)) (mul a k)) := by
    by_cases hh : ht u < ht (mul (mul a (mul (mul u a) k)) (mul a k))
    · exact hh
    · exact False.elim (normal_second_double_growth_impossible hu ha hk hf hmid (by omega))
  exact normal_v_head_cycle_impossible ha hnv hnw hl hf houter hmid (by omega) hwv hgv hBa hDa hDv

end Austin12087Trace
#print axioms Austin12087Trace.normal_v_head_cycle_impossible
#print axioms Austin12087Trace.normal_second_v_growing_middle_impossible

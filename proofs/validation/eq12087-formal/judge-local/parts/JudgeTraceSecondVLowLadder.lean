prelude
import Init.Data.Option.Lemmas
import Init.Omega
import Init.RCases
import Init.WFTactics
import JudgeTraceSecondVLowColumnHeight
set_option Elab.async false
/- Checked module: TraceSecondVLowLadder -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_second_v_growing_middle_ladder {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u)
    (hvr : ht (mul a k) < ht k)
    (hmid : ht (mul a k) ≤ ht (mul (mul a (mul (mul u a) k)) (mul a k))) :
    let g := mul u a
    let v := mul a k
    let w := mul a (mul g k)
    let B := mul (mul a w) g
    let D := mul a v
    ∃ r s t j, NF r ∧ NF s ∧ NF t ∧ NF j ∧
      mul w r = k ∧ mul v s = r ∧ mul D s = w ∧ mul g t = s ∧ mul B t = v ∧
      ht k = ht s + 2 ∧ ht r = ht s + 1 ∧ ht t + 1 = ht s ∧ ht g < ht t ∧
      ht v + 2 ≤ ht t ∧ ht B + 3 ≤ ht t ∧ ht w + 2 ≤ ht s ∧ ht D + 3 ≤ ht s ∧
      mul (mul D w) j = g ∧ mul w j = t ∧ ht j < ht t ∧
      ReturnLadder B (mul D w) w v g t j := by
  let g := mul u a
  let v := mul a k
  let w := mul a (mul g k)
  let B := mul (mul a w) g
  let D := mul a v
  obtain ⟨r,s,t,hnr,hns,hnt,_,_,_,hkr,hws,hrs,hwr,_,_,_,hkh,hrc,hvt,hst,_,hvs⟩ :=
    normal_second_v_growing_middle_low_trace hu ha hk hf hvr hmid
  have hnw : NF w := nf_mul ha (nf_mul (nf_mul hu ha) hk)
  have hnv : NF v := nf_mul ha hk
  have houter : ht u < ht (mul w v) := by
    by_cases hh : ht u < ht (mul w v)
    · exact hh
    · exact False.elim (normal_second_double_growth_impossible hu ha hk hf hmid
        (by change ht (mul w v) ≤ ht u; omega))
  obtain ⟨hgt,hts,hrsHeight,hv2,hB3,hw2,hD3⟩ := normal_low_growing_middle_column_height
    hu ha hnv hnw hnr hns hnt hf hws hrs hvt hst hrc hwr hvs hmid houter
  change mul D s = w at hws
  change mul g t = s at hst
  change mul B t = v at hvt
  change ht w + 2 ≤ ht s at hw2
  have hos := mul_origin_of_right_height_le (a:=g) (b:=t) (by rw [hst]; omega)
  rw [hst] at hos
  obtain ⟨j,_,hnj,_,hgj,htj,hjgap,_⟩ := nf_return_origin_trace hns hos hws (by omega)
  have hot := mul_origin_of_right_height_le (a:=w) (b:=j) (by rw [htj]; omega)
  rw [htj] at hot
  exact ⟨r,s,t,j,hnr,hns,hnt,hnj,hkr,hrs,hws,hst,hvt,by omega,hrsHeight,hts,hgt,
    hv2,hB3,hw2,hD3,hgj,htj,by omega,⟨hnt,htj,hot,hvt,hgj⟩⟩

end submission.Austin12087Trace

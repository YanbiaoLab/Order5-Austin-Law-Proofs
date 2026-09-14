prelude
import Init.Data.Option.Lemmas
import Init.Omega
import Init.RCases
import Init.WFTactics
import JudgeTraceSecondVWMaxBoundary
set_option Elab.async false
/- Checked module: TraceSecondVGMaxClosed -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_low_ladder_g_strict_max_impossible {u a v w t j y : T}
    (hne : NF (mul w v))
    (hl : ReturnLadder (mul (mul a w) (mul u a)) (mul (mul a v) w) w v (mul u a) t j)
    (hf : mul y (mul w v) = u) (houter : ht u < ht (mul w v))
    (hwg : ht w < ht (mul u a)) (hvg : ht v < ht (mul u a)) : False := by
  let g := mul u a
  let A := mul a w
  let B := mul A g
  change ht w < ht g at hwg
  change ht v < ht g at hvg
  change ReturnLadder B (mul (mul a v) w) w v g t j at hl
  have huGap := nf_mul_height_key_gap (a:=y) hne
  rw [hf] at huGap
  have heUpper := mul_height_upper w v
  have hu2 : ht u + 2 ≤ ht (mul w v) := by rcases huGap with hh | hh <;> omega
  have hgUpper := mul_height_upper u a
  change ht g ≤ max (ht u) (ht a) + 1 at hgUpper
  have haw : ht w ≤ ht a := by omega
  have hAg := mul_height_growth_of_left_ge (a:=a) (b:=w) haw
  change ht A = max (ht a) (ht w) + 1 at hAg
  have hBg := mul_height_growth_of_left_ge (a:=A) (b:=g) (by change ht g ≤ ht A; omega)
  change ht B = max (ht A) (ht g) + 1 at hBg
  exact return_ladder_dominant_impossible hl (by omega) (by omega) (by omega)

theorem normal_second_v_growing_middle_frontier {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hs : NormalSecondBelow (ht k))
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u)
    (hvr : ht (mul a k) < ht k)
    (hmid : ht (mul a k) ≤ ht (mul (mul a (mul (mul u a) k)) (mul a k))) :
    ht (mul a (mul (mul u a) k)) < ht (mul a k) ∧ ht (mul u a) ≤ ht (mul a k) := by
  let g := mul u a
  let v := mul a k
  let w := mul a (mul g k)
  change ht w < ht v ∧ ht g ≤ ht v
  have hnv : NF v := nf_mul ha hk
  have hnw : NF w := nf_mul ha (nf_mul (nf_mul hu ha) hk)
  have houter : ht u < ht (mul w v) := by
    by_cases hh : ht u < ht (mul w v)
    · exact hh
    · exact False.elim (normal_second_double_growth_impossible hu ha hk hf hmid
        (by change ht (mul w v) ≤ ht u; omega))
  obtain ⟨r,s,t,j,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hl⟩ :=
    normal_second_v_growing_middle_ladder hu ha hk hf hvr hmid
  have hnotg : ¬ (ht w < ht g ∧ ht v < ht g) := by
    intro hh
    exact normal_low_ladder_g_strict_max_impossible (nf_mul hnw hnv) hl hf houter hh.1 hh.2
  have hnotw : ¬ (ht v ≤ ht w ∧ ht g ≤ ht w) := by
    intro hh
    exact normal_second_v_growing_middle_w_dominant_impossible hu ha hk hs hf hvr hmid hh.1 hh.2
  constructor <;> omega

end submission.Austin12087Trace

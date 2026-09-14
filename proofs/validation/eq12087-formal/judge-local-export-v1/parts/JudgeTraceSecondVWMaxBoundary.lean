prelude
import Init.Data.Option.Lemmas
import Init.Omega
import Init.RCases
import Init.WFTactics
import JudgeTraceSecondVWMaxClosed
set_option Elab.async false
/- Checked module: TraceSecondVWMaxBoundary -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_low_ladder_equal_max_impossible {a g v w t j : T}
    (hnv : NF v)
    (hl : ReturnLadder (mul (mul a w) g) (mul (mul a v) w) w v g t j)
    (hvt : ht v < ht t) (hvw : ht v = ht w) (hgw : ht g ≤ ht w)
    (hBa : mul (mul a w) g ≠ a) : False := by
  let A := mul a w
  let B := mul A g
  let F := mul B v
  obtain ⟨_,hav,_⟩ := normal_low_ladder_w_max_forces_fixed hl hvt (by omega) hgw
  rw [hav] at hl
  change ReturnLadder B A w v g t j at hl
  have ha := inverse_height_strict (inverse_complete a v)
  rw [hav] at ha
  obtain ⟨z,lv,rv,hvc⟩ := mul_return_of_height_lt (a:=a) (b:=v) (by rw [hav]; omega)
  have hF := mul_height_off_return_key (a:=B) hvc hBa
  change ht F = max (ht B) (ht v) + 1 at hF
  obtain ⟨l,_,_,_,hFl,_,hlGap,_⟩ := nf_return_origin_trace hl.1 hl.2.2.1 hl.2.2.2.1 hvt
  change mul F l = w at hFl
  have hFlHeight := inverse_height_strict (inverse_complete F l)
  rw [hFl] at hFlHeight
  have htHeight := mul_height_growth_of_right_le (a:=w) (b:=j) (by
    rw [hl.2.1]; exact Nat.le_of_lt (origin_height hl.2.2.1).2)
  rw [hl.2.1] at htHeight
  obtain ⟨m,hl',_⟩ := return_ladder_step hl hvt (by omega)
  change ReturnLadder A F v g w j m at hl'
  exact return_ladder_second_dominant_impossible hl' (by omega) (by omega) (by omega) (by omega)

theorem normal_second_v_growing_middle_w_dominant_impossible {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hs : NormalSecondBelow (ht k))
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u)
    (hvr : ht (mul a k) < ht k)
    (hmid : ht (mul a k) ≤ ht (mul (mul a (mul (mul u a) k)) (mul a k)))
    (hvw : ht (mul a k) ≤ ht (mul a (mul (mul u a) k)))
    (hgw : ht (mul u a) ≤ ht (mul a (mul (mul u a) k))) : False := by
  by_cases hvw' : ht (mul a k) < ht (mul a (mul (mul u a) k))
  · exact normal_second_v_growing_middle_w_max_impossible hu ha hk hs hf hvr hmid hvw' hgw
  · obtain ⟨r,s,t,j,_,_,hnt,_,_,_,hws,hst,hvt,_,_,hts,_,hv2,_,_,_,_,_,_,hl⟩ :=
      normal_second_v_growing_middle_ladder hu ha hk hf hvr hmid
    have hnv := nf_mul ha hk
    obtain ⟨_,hDa,_⟩ := normal_low_ladder_w_max_forces_fixed hl (by omega) hvw hgw
    have hbounds := normal_second_query_k_dominates hu ha hk hf
    have hBa : mul (mul a (mul a (mul (mul u a) k))) (mul u a) ≠ a := by
      intro hB
      exact normal_second_v_low_equal_keys_descent_impossible hu ha hnt hs hbounds.1 hbounds.2
        (by omega) hf hws hvt hst hB hDa
    exact normal_low_ladder_equal_max_impossible hnv hl (by omega) (by omega) hgw hBa

end submission.Austin12087Trace

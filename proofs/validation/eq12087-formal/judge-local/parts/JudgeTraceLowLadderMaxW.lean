prelude
import Init.Data.Option.Lemmas
import Init.Omega
import Init.RCases
import Init.WFTactics
import JudgeTraceSecondVLowLadder
set_option Elab.async false
/- Checked module: TraceLowLadderMaxW -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_low_ladder_w_max_forces_fixed {a g v w t j : T}
    (hl : ReturnLadder (mul (mul a w) g) (mul (mul a v) w) w v g t j)
    (hvt : ht v < ht t) (hvw : ht v ≤ ht w) (hgw : ht g ≤ ht w) :
    ht (mul a w) < ht w ∧ mul a v = a ∧ mul (mul a v) w = mul a w := by
  let A := mul a w
  let B := mul A g
  let D := mul a v
  let C := mul D w
  change ReturnLadder B C w v g t j at hl
  have hAw : ht A < ht w := by
    by_cases hh : ht A < ht w
    · exact hh
    · have hA := mul_height_growth_of_right_le (a:=a) (b:=w) (by change ht w ≤ ht A; omega)
      change ht A = max (ht a) (ht w) + 1 at hA
      have hB := mul_height_growth_of_left_ge (a:=A) (b:=g) (by omega)
      change ht B = max (ht A) (ht g) + 1 at hB
      exact False.elim (return_ladder_dominant_impossible hl (by omega) (by omega) (by omega))
  obtain ⟨z,l,r,hwc⟩ := mul_return_of_height_lt (a:=a) (b:=w) hAw
  have hDa : D = a := by
    by_cases hh : D = a
    · exact hh
    · have hC := mul_height_off_return_key (a:=D) hwc hh
      change ht C = max (ht D) (ht w) + 1 at hC
      exact False.elim (return_ladder_second_dominant_impossible hl hvt (by omega) (by omega) (by omega))
  exact ⟨hAw,hDa,by change mul D w = mul a w; rw [hDa]⟩

end submission.Austin12087Trace

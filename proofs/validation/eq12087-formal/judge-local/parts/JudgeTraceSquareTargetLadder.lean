prelude
import Init.Data.Option.Lemmas
import Init.Omega
import Init.RCases
import Init.WFTactics
import JudgeTraceSecondTwoColumnsReturn
set_option Elab.async false
/- Checked module: TraceSquareTargetLadder -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem square_target_return_ladder_impossible {u f w j h : T}
    (hfu : f ≠ u)
    (hl : ReturnLadder (mul u w) (mul f w) w (mul u u) w j h)
    (hs : ht (mul u u) < ht j) : False := by
  have hsq : ht (mul u u) = ht u + 1 := by rw [mul_square]; rfl
  by_cases hwu : ht w ≤ ht u
  · have hg := mul_height_growth_of_left_ge (a:=u) (b:=w) hwu
    exact return_ladder_dominant_impossible hl (by omega) (by omega) (by omega)
  · rcases mul_height_growth_or_return u w with hg | ⟨x,z,l,r,hw,_⟩
    · exact return_ladder_dominant_impossible hl (by omega) (by omega) (by omega)
    · have hg := mul_height_off_return_key (a:=f) hw hfu
      exact return_ladder_second_dominant_impossible hl hs (by omega) (by omega) (by omega)

end submission.Austin12087Trace

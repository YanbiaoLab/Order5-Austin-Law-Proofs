prelude
import Init.Data.Option.Lemmas
import Init.Omega
import Init.RCases
import Init.WFTactics
import JudgeTraceSecondVFrontier
set_option Elab.async false
/- Checked module: TraceSecondVEqualFixedClosed -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_fixed_column_short_key_impossible {u a w s : T}
    (hw : NF w)
    (hfixed : mul u s = u) (hws : mul (mul a u) s = w)
    (hua : ht u < ht a) (hAa : ht (mul a w) < ht a)
    (hAw : ht (mul a w) < ht w) (hwh : ht w = ht s + 1) : False := by
  let A := mul a w
  let B := mul a u
  let C := mul a A
  change ht A < ht a at hAa
  change ht A < ht w at hAw
  have how := mul_origin_of_right_height_le (a:=B) (b:=s) (by rw [hws]; omega)
  rw [hws] at how
  obtain ⟨j,_,_,hns,hCj,hAj,hjgap,_⟩ :=
    nf_return_origin_trace hw how (show mul a w = A from rfl) hAw
  have hos := mul_origin_of_right_height_le (a:=A) (b:=j) (by rw [hAj]; omega)
  rw [hAj] at hos
  have huS := inverse_height_strict (inverse_complete u s)
  rw [hfixed] at huS
  have hB := mul_height_growth_of_left_ge (a:=a) (b:=u) (by omega)
  have hC := mul_height_growth_of_left_ge (a:=a) (b:=A) (by omega)
  change ht B = max (ht a) (ht u) + 1 at hB
  change ht C = max (ht a) (ht A) + 1 at hC
  have hl : ReturnLadder u C A u B s j := ⟨hns,hAj,hos,hfixed,hCj⟩
  exact return_ladder_second_dominant_impossible hl (by omega) (by omega) (by omega) (by omega)

theorem normal_v_equal_fixed_exception_impossible {u a w s : T}
    (hw : NF w)
    (hfixed : mul u s = u) (hws : mul (mul a u) s = w)
    (hgr : mul (mul a w) u = mul u a)
    (hua : ht u < ht a) (hga : ht (mul u a) < ht a)
    (hAw : ht (mul a w) < ht w) (hwh : ht w = ht s + 1) : False := by
  have hA := inverse_height_strict (inverse_complete (mul a w) u)
  rw [hgr] at hA
  exact normal_fixed_column_short_key_impossible hw hfixed hws hua (by omega) hAw hwh

end submission.Austin12087Trace

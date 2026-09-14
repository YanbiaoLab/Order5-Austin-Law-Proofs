prelude
import Init.Data.Option.Lemmas
import Init.Omega
import Init.RCases
import Init.WFTactics
import JudgeTraceLowLadderMaxW
set_option Elab.async false
/- Checked module: TraceLowLadderTailStop -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_low_ladder_w_max_tail_stops {a g v w t j : T}
    (hnv : NF v)
    (hl : ReturnLadder (mul (mul a w) g) (mul (mul a v) w) w v g t j)
    (hvt : ht v < ht t) (hvw : ht v < ht w) (hgw : ht g ≤ ht w)
    (hBa : mul (mul a w) g ≠ a) : ht j ≤ ht w := by
  let A := mul a w
  let B := mul A g
  obtain ⟨hAw,hDa,_⟩ := normal_low_ladder_w_max_forces_fixed hl hvt (by omega) hgw
  rw [hDa] at hl
  change ReturnLadder B A w v g t j at hl
  change B ≠ a at hBa
  have haHeight := inverse_height_strict (inverse_complete a v)
  rw [hDa] at haHeight
  obtain ⟨z,l,r,hvc⟩ := mul_return_of_height_lt (a:=a) (b:=v) (by rw [hDa]; omega)
  have hF := mul_height_off_return_key (a:=B) hvc hBa
  have hFa : mul B v ≠ a := by intro he; have hh := congrArg ht he; omega
  obtain ⟨zw,lw,rw,hwc⟩ := mul_return_of_height_lt (a:=a) (b:=w) hAw
  by_cases hjw : ht j ≤ ht w
  · exact hjw
  · have hwj : ht w < ht j := by omega
    obtain ⟨l,hl₁,_⟩ := return_ladder_step hl hvt hwj
    change ReturnLadder A (mul B v) v g w j l at hl₁
    have hjGrow := mul_height_growth_of_right_le (a:=v) (b:=l) (by
      rw [hl₁.2.1]; exact Nat.le_of_lt (origin_height hl₁.2.2.1).2)
    rw [hl₁.2.1] at hjGrow
    have hlh : ht l + 1 = ht j := by omega
    have hnl : NF l := (nf_origin hl₁.1 hl₁.2.2.1).2
    have hwGap := nf_mul_height_key_gap (a:=mul B v) hnl
    rw [hl₁.2.2.2.2] at hwGap
    have hwl : ht w < ht l := by rcases hwGap with hh | hh <;> omega
    obtain ⟨m,hl₂,_⟩ := return_ladder_step hl₁ (by omega) (by omega)
    change ReturnLadder (mul B v) B g w v l m at hl₂
    have hlGrow := mul_height_growth_of_right_le (a:=g) (b:=m) (by
      rw [hl₂.2.1]; exact Nat.le_of_lt (origin_height hl₂.2.2.1).2)
    rw [hl₂.2.1] at hlGrow
    have hw2 : ht w + 2 ≤ ht l := by rcases hwGap with hh | hh <;> omega
    have hmh : ht m + 1 = ht l := by omega
    obtain ⟨n,hl₃,_⟩ := return_ladder_step hl₂ hwl (by omega)
    change ReturnLadder B (mul (mul B v) w) w v g m n at hl₃
    have hC := mul_height_off_return_key (a:=mul B v) hwc hFa
    exact False.elim (return_ladder_second_dominant_impossible hl₃ (by omega)
      (by omega) (by omega) (by omega))

end submission.Austin12087Trace

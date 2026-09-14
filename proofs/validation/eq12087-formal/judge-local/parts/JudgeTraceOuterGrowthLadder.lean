prelude
import Init.Data.Option.Lemmas
import Init.Omega
import Init.RCases
import Init.WFTactics
import JudgeTraceSecondReturningColumnTraces
set_option Elab.async false
/- Checked module: TraceOuterGrowthLadder -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem outer_growth_return_ladder_impossible {u a q e k t : T}
    (ha : NF a) (hq : NF q) (heu : ht e < ht u)
    (hl : ReturnLadder (mul u a) (mul (mul a q) e) e q a k t)
    (hqk : ht q < ht k) : False := by
  let g := mul u a
  let w := mul a q
  let A := mul w e
  change ReturnLadder g A e q a k t at hl
  by_cases hd : ht e ≤ ht g ∧ ht a ≤ ht g ∧ ht q ≤ ht g
  · exact return_ladder_dominant_impossible hl hd.1 hd.2.2 hd.2.1
  · have hem : ht e < max (ht a) (ht q) := by
      have hg := nf_mul_height_key_gap (a:=u) ha
      change ht g = max (ht u) (ht a) + 1 ∨ (ht u + 3 ≤ ht a ∧ ht g + 2 ≤ ht a) at hg
      rcases hg with hg | hg <;> omega
    have hwq : ht w < ht q := by
      by_cases hh : ht w < ht q
      · exact hh
      · have hwg := mul_height_growth_of_right_le (a:=a) (b:=q) (by change ht q ≤ ht w; omega)
        change ht w = max (ht a) (ht q) + 1 at hwg
        have hAg := mul_height_growth_of_left_ge (a:=w) (b:=e) (by omega)
        change ht A = max (ht w) (ht e) + 1 at hAg
        exact False.elim (return_ladder_second_dominant_impossible hl hqk (by omega) (by omega) (by omega))
    have hwgap := nf_mul_height_key_gap (a:=a) hq
    change ht w = max (ht a) (ht q) + 1 ∨ (ht a + 3 ≤ ht q ∧ ht w + 2 ≤ ht q) at hwgap
    have haq : ht a < ht q := by rcases hwgap with hh | hh <;> omega
    have heq : ht e < ht q := by omega
    obtain ⟨z,l,r,hqc⟩ := mul_return_of_height_lt (a:=a) (b:=q) hwq
    have hb := mul_height_off_return_key (a:=g) hqc (mul_ne_right u a)
    have hpg := nf_mul_height_key_gap (a:=g) hl.1
    rw [hl.2.2.2.1] at hpg
    have hq2 : ht q + 2 ≤ ht k := by rcases hpg with hh | hh <;> omega
    have hkg := mul_height_growth_of_right_le (a:=e) (b:=t) (by
      rw [hl.2.1]
      exact Nat.le_of_lt (origin_height hl.2.2.1).2)
    rw [hl.2.1] at hkg
    obtain ⟨r',hl',_⟩ := return_ladder_step hl hqk (by omega)
    exact return_ladder_second_dominant_impossible hl' (by omega) (by omega) (by omega) (by omega)

end submission.Austin12087Trace

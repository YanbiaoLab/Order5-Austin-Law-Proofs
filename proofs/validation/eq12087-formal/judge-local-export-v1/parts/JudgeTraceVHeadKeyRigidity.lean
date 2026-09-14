prelude
import Init.Data.Option.Lemmas
import Init.Omega
import Init.RCases
import Init.WFTactics
import JudgeTraceSecondVVMaxKeys
set_option Elab.async false
/- Checked module: TraceVHeadKeyRigidity -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_ladder_first_key_of_highest_return {a d z lv rv b c w v g t j : T}
    (hvc : v = T.c a d z lv rv) (hl : ReturnLadder b c w v g t j)
    (hvt : ht v < ht t) (hwv : ht w < ht v) (hgv : ht g ≤ ht v) : b = a := by
  have htHeight := mul_height_growth_of_right_le (a:=w) (b:=j) (by
    rw [hl.2.1]; exact Nat.le_of_lt (origin_height hl.2.2.1).2)
  rw [hl.2.1] at htHeight
  have hnj := (nf_origin hl.1 hl.2.2.1).2
  have hgGap := nf_mul_height_key_gap (a:=c) hnj
  rw [hl.2.2.2.2] at hgGap
  have hgj : ht g < ht j := by rcases hgGap with hh | hh <;> omega
  by_cases he : b = a
  · exact he
  · have hF := mul_height_off_return_key (a:=b) hvc he
    obtain ⟨m,hl',_⟩ := return_ladder_step hl hvt (by omega)
    exact False.elim (return_ladder_second_dominant_impossible hl' hgj (by omega) (by omega) (by omega))

theorem normal_changed_key_growth {u a w d : T} (ha : NF a)
    (hB : mul (mul a w) (mul u a) = a) (hda : d ≠ a) :
    let g := mul u a
    let C := mul d w
    ht (mul C g) = max (ht C) (ht g) + 1 ∧
    ht u < ht (mul C g) ∧ ht a < ht (mul C g) := by
  let g := mul u a
  let A := mul a w
  let C := mul d w
  change mul A g = a at hB
  change ht (mul C g) = max (ht C) (ht g) + 1 ∧ ht u < ht (mul C g) ∧ ht a < ht (mul C g)
  have hCA : C ≠ A := by
    intro he
    exact hda (right_injective d a w he)
  by_cases hag : ht a < ht g
  · obtain ⟨z,l,r,hgc⟩ := mul_return_of_height_lt (a:=A) (b:=g) (by rw [hB]; exact hag)
    have hK := mul_height_off_return_key (a:=C) hgc hCA
    have hu := inverse_height_strict (inverse_complete u a)
    change ht u < max (ht a) (ht g) at hu
    exact ⟨hK,by omega,by omega⟩
  · have hgGap := nf_mul_height_key_gap (a:=u) ha
    change ht g = max (ht u) (ht a) + 1 ∨ (ht u + 3 ≤ ht a ∧ ht g + 2 ≤ ht a) at hgGap
    have hug : ht u + 3 ≤ ht a ∧ ht g + 2 ≤ ht a := by rcases hgGap with hh | hh <;> omega
    have hA := inverse_height_strict (inverse_complete A g)
    rw [hB] at hA
    have hAw : ht A < ht w := by
      have ha' := inverse_height_strict (inverse_complete a w)
      change ht a < max (ht w) (ht A) at ha'
      omega
    obtain ⟨z,l,r,hwc⟩ := mul_return_of_height_lt (a:=a) (b:=w) hAw
    have hC := mul_height_off_return_key (a:=d) hwc hda
    change ht C = max (ht d) (ht w) + 1 at hC
    have hw := inverse_height_strict (inverse_complete a w)
    change ht a < max (ht w) (ht A) at hw
    have hK := mul_height_growth_of_left_ge (a:=C) (b:=g) (by omega)
    exact ⟨hK,by omega,by omega⟩

end submission.Austin12087Trace

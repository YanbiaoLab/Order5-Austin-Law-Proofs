prelude
import Init.Data.Option.Lemmas
import Init.Omega
import Init.RCases
import Init.WFTactics
import JudgeTraceSameKeyAlignedColumns
set_option Elab.async false
/- Checked module: TraceHighestReturnExit -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_ladder_first_key_at_max {a d z lv rv b c w v g t j : T}
    (hvc : v = T.c a d z lv rv) (hl : ReturnLadder b c w v g t j)
    (hvt : ht v < ht t) (hwv : ht w ≤ ht v) (hgv : ht g ≤ ht v) : b = a := by
  have htHeight := mul_height_growth_of_right_le (a:=w) (b:=j) (by
    rw [hl.2.1]; exact Nat.le_of_lt (origin_height hl.2.2.1).2)
  rw [hl.2.1] at htHeight
  have hvGap := nf_mul_height_key_gap (a:=b) hl.1
  rw [hl.2.2.2.1] at hvGap
  have hv2 : ht v + 2 ≤ ht t := by rcases hvGap with hh | hh <;> omega
  by_cases he : b = a
  · exact he
  · have hF := mul_height_off_return_key (a:=b) hvc he
    obtain ⟨m,hl',_⟩ := return_ladder_step hl hvt (by omega)
    exact False.elim (return_ladder_second_dominant_impossible hl' (by omega) (by omega) (by omega) (by omega))

theorem normal_highest_g_ladder_exit {A d v g w r s u a B z l b : T}
    (hl : ReturnLadder A d v g w r s) (hgr : ht g < ht r)
    (hvg : ht v ≤ ht g) (hwg : ht w < ht g)
    (hgc : g = T.c A B z l b) (hog : origin g = some (u,a))
    (hCA : mul d w ≠ A) : mul d w = u := by
  let C := mul d w
  have hrHeight := mul_height_growth_of_right_le (a:=v) (b:=s) (by
    rw [hl.2.1]; exact Nat.le_of_lt (origin_height hl.2.2.1).2)
  rw [hl.2.1] at hrHeight
  have hgGap := nf_mul_height_key_gap (a:=A) hl.1
  rw [hl.2.2.2.1] at hgGap
  have hgs : ht g < ht s := by rcases hgGap with hh | hh <;> omega
  obtain ⟨t,hl₁,_⟩ := return_ladder_step hl hgr (by omega)
  have htg : ht t ≤ ht g := by
    by_cases hh : ht t ≤ ht g
    · exact hh
    · obtain ⟨j,hl₂,_⟩ := return_ladder_step hl₁ (by omega) (by omega)
      change ReturnLadder (mul A g) C w v g t j at hl₂
      have htHeight := mul_height_growth_of_right_le (a:=w) (b:=j) (by
        rw [hl₂.2.1]; exact Nat.le_of_lt (origin_height hl₂.2.2.1).2)
      rw [hl₂.2.1] at htHeight
      have hnj := (nf_origin hl₂.1 hl₂.2.2.1).2
      have hjGap := nf_mul_height_key_gap (a:=C) hnj
      rw [hl₂.2.2.2.2] at hjGap
      have hgj : ht g < ht j := by rcases hjGap with hj | hj <;> omega
      obtain ⟨n,hl₃,_⟩ := return_ladder_step hl₂ (by omega) (by omega)
      exact False.elim (hCA (normal_ladder_first_key_at_max hgc hl₃ hgj hvg (by omega)))
  have hsHeight := mul_height_growth_of_left_ge (a:=g) (b:=t) htg
  rw [hl₁.2.1] at hsHeight
  obtain ⟨j,_,_,_,hCj,_,hjGap,_⟩ := nf_return_origin_trace hl₁.1 hl₁.2.2.1 hl₁.2.2.2.1 (by omega)
  change mul C j = g at hCj
  have hog' := mul_origin_of_right_height_le (a:=C) (b:=j) (by rw [hCj]; omega)
  rw [hCj,hog] at hog'
  exact (Prod.mk.inj (Option.some.inj hog')).1.symm

end submission.Austin12087Trace

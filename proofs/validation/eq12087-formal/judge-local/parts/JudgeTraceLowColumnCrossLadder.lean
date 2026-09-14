prelude
import Init.Data.Option.Lemmas
import Init.Omega
import Init.RCases
import Init.WFTactics
import JudgeTraceLowColumnTailHeight
set_option Elab.async false
/- Checked module: TraceLowColumnCrossLadder -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_low_column_cross_ladder {a e g v s t : T}
    (hng : NF g) (hnv : NF v) (hns : NF s) (hnt : NF t)
    (hvt : mul (mul (mul a a) g) t = v) (hst : mul g t = s)
    (hav : mul a v = e) (hes : mul e s = a)
    (he : ht e < ht v) (hsv : ht s < ht v) (htv : ht v = ht t + 1) :
    ∃ n p, ReturnLadder (mul a e) (mul g s) s (mul (mul a a) g) e n p ∧
      ht (mul (mul a a) g) < ht n ∧ ht v = ht n + 2 := by
  let A := mul a a
  let B := mul A g
  let H := mul a e
  change mul B t = v at hvt
  have hA : ht A = ht a + 1 := by dsimp only [A]; rw [mul_square]; rfl
  have havGap := nf_mul_height_key_gap (a:=a) hnv
  rw [hav] at havGap
  have ha3 : ht a + 3 ≤ ht v := by rcases havGap with hh | hh <;> omega
  have hesGap := nf_mul_height_key_gap (a:=e) hns
  rw [hes] at hesGap
  have he4 : ht e + 4 ≤ ht v := by rcases hesGap with hh | hh <;> omega
  have hsGap := nf_mul_height_key_gap (a:=g) hnt
  rw [hst] at hsGap
  have hg3 : ht g + 3 ≤ ht t ∧ ht s + 2 ≤ ht t := by rcases hsGap with hh | hh <;> omega
  have hov := mul_origin_of_right_height_le (a:=B) (b:=t) (by rw [hvt]; omega)
  rw [hvt] at hov
  obtain ⟨n,_,hnn,_,hHn,hen,hnGap,_⟩ := nf_return_origin_trace hnv hov hav he
  change mul H n = B at hHn
  have htUpper := mul_height_upper e n
  rw [hen] at htUpper
  have htn : ht t = ht n + 1 := by omega
  have hom := mul_origin_of_right_height_le (a:=e) (b:=n) (by rw [hen]; omega)
  rw [hen] at hom
  have hBn : ht B < ht n := by
    by_cases hh : ht B < ht n
    · exact hh
    · have hBHeight := mul_height_growth_of_right_le (a:=H) (b:=n) (by rw [hHn]; omega)
      rw [hHn] at hBHeight
      have hBgap := nf_mul_height_key_gap (a:=A) hng
      change ht B = max (ht A) (ht g) + 1 ∨ (ht A + 3 ≤ ht g ∧ ht B + 2 ≤ ht g) at hBgap
      have hBg : ht B = max (ht A) (ht g) + 1 := by rcases hBgap with hh | hh <;> omega
      have hoB := mul_origin_of_right_height_le (a:=A) (b:=g) (by change ht g ≤ ht B; omega)
      change origin B = some (A,g) at hoB
      have hoB' := mul_origin_of_right_height_le (a:=H) (b:=n) (by rw [hHn]; omega)
      rw [hHn,hoB] at hoB'
      have hgn := (Prod.mk.inj (Option.some.inj hoB')).2
      have hh' := congrArg ht hgn
      omega
  obtain ⟨p,_,_,_,hGp,hsp,hpGap,_⟩ := nf_return_origin_trace hnt hom hst (by omega)
  have hon := mul_origin_of_right_height_le (a:=s) (b:=p) (by rw [hsp]; omega)
  rw [hsp] at hon
  exact ⟨n,p,⟨hnn,hsp,hon,hHn,hGp⟩,hBn,by omega⟩

theorem normal_low_cross_ladder_equal_heads {a e g s n p : T}
    (ha : NF a) (hne : NF e) (hng : NF g) (hns : NF s)
    (hes : mul e s = a)
    (hl : ReturnLadder (mul a e) (mul g s) s (mul (mul a a) g) e n p)
    (hBn : ht (mul (mul a a) g) < ht n) : g = e ∧ ht a < ht s := by
  let A := mul a a
  let B := mul A g
  let H := mul a e
  let G := mul g s
  change ReturnLadder H G s B e n p at hl
  change ht B < ht n at hBn
  have hA : ht A = ht a + 1 := by dsimp only [A]; rw [mul_square]; rfl
  have hBUpper := mul_height_upper A g
  change ht B ≤ max (ht A) (ht g) + 1 at hBUpper
  have hesGap := nf_mul_height_key_gap (a:=e) hns
  rw [hes] at hesGap
  have has : ht a < ht s := by
    by_cases hh : ht a < ht s
    · exact hh
    · have haGrow : ht a = max (ht e) (ht s) + 1 := by rcases hesGap with hh | hh <;> omega
      have hH := mul_height_growth_of_left_ge (a:=a) (b:=e) (by omega)
      change ht H = max (ht a) (ht e) + 1 at hH
      by_cases hgA : ht A ≤ ht g
      · have hG := mul_height_growth_of_left_ge (a:=g) (b:=s) (by omega)
        change ht G = max (ht g) (ht s) + 1 at hG
        exact False.elim (return_ladder_second_dominant_impossible hl hBn (by omega) (by omega) (by omega))
      · have hB := mul_height_growth_of_left_ge (a:=A) (b:=g) (by omega)
        change ht B = max (ht A) (ht g) + 1 at hB
        have hFgap := nf_mul_height_key_gap (a:=H) (nf_mul (nf_mul ha ha) hng)
        change ht (mul H B) = max (ht H) (ht B) + 1 ∨ (ht H + 3 ≤ ht B ∧ ht (mul H B) + 2 ≤ ht B) at hFgap
        have hF : ht (mul H B) = max (ht H) (ht B) + 1 := by rcases hFgap with hh | hh <;> omega
        have hnHeight := mul_height_growth_of_right_le (a:=s) (b:=p) (by
          rw [hl.2.1]; exact Nat.le_of_lt (origin_height hl.2.2.1).2)
        rw [hl.2.1] at hnHeight
        have hnGap := nf_mul_height_key_gap (a:=H) hl.1
        rw [hl.2.2.2.1] at hnGap
        have hB2 : ht B + 2 ≤ ht n := by rcases hnGap with hh | hh <;> omega
        obtain ⟨q,hl',_⟩ := return_ladder_step hl hBn (by omega)
        exact False.elim (return_ladder_second_dominant_impossible hl' (by omega) (by omega) (by omega) (by omega))
  have hsRet : ht e + 3 ≤ ht s ∧ ht a + 2 ≤ ht s := by rcases hesGap with hh | hh <;> omega
  refine ⟨?_,has⟩
  by_cases hge : g = e
  · exact hge
  · obtain ⟨z,l,r,hsc⟩ := mul_return_of_height_lt (a:=e) (b:=s) (by rw [hes]; exact has)
    have hG := mul_height_off_return_key (a:=g) hsc hge
    change ht G = max (ht g) (ht s) + 1 at hG
    exact False.elim (return_ladder_second_dominant_impossible hl hBn (by omega) (by omega) (by omega))

end submission.Austin12087Trace

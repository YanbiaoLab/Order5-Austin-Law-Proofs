prelude
import Init.Data.Option.Lemmas
import Init.Omega
import Init.RCases
import Init.WFTactics
import JudgeTraceSecondVHighClosed
set_option Elab.async false
/- Checked module: TraceLowAlignedColumns -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_low_aligned_columns_impossible {u a v w s t d : T}
    (hnv : NF v) (hns : NF s) (hnt : NF t)
    (hvt : mul u t = v) (hwt : mul d t = w) (hst : mul (mul u a) t = s)
    (hws : mul (mul a v) s = w) (hback : mul (mul a w) (mul u a) = u)
    (hvht : ht v = ht t + 1) (hsv : ht s ≤ ht v) (hwv : ht w ≤ ht v)
    (hgv : ht (mul u a) < ht v) : False := by
  let g := mul u a
  let D := mul a v
  let A := mul a w
  change mul g t = s at hst
  change mul D s = w at hws
  change mul A g = u at hback
  change ht g < ht v at hgv
  have hD := inverse_height_strict (inverse_complete D s)
  rw [hws] at hD
  have hDsmall : ht D < ht v := by omega
  have hDgap := nf_mul_height_key_gap (a:=a) hnv
  change ht D = max (ht a) (ht v) + 1 ∨ (ht a + 3 ≤ ht v ∧ ht D + 2 ≤ ht v) at hDgap
  have ha3 : ht a + 3 ≤ ht v := by rcases hDgap with hh | hh <;> omega
  have hD2 : ht D + 2 ≤ ht v := by rcases hDgap with hh | hh <;> omega
  by_cases hsvlt : ht s < ht v
  · have hsGap := nf_mul_height_key_gap (a:=g) hnt
    rw [hst] at hsGap
    have hs2 : ht s + 2 ≤ ht t := by rcases hsGap with hh | hh <;> omega
    have hwUpper := mul_height_upper D s
    rw [hws] at hwUpper
    have hwGap := nf_mul_height_key_gap (a:=d) hnt
    rw [hwt] at hwGap
    have hwtSmall : ht w < ht t := by rcases hwGap with hh | hh <;> omega
    obtain ⟨z,l,r,hct⟩ := mul_return_of_height_lt (a:=g) (b:=t) (by rw [hst]; omega)
    obtain ⟨z',l',r',hct'⟩ := mul_return_of_height_lt (a:=d) (b:=t) (by rw [hwt]; omega)
    have hsw := (T.c.inj (hct.symm.trans hct')).2.1
    rw [hst,hwt] at hsw
    exact mul_ne_right D s (hws.trans hsw.symm)
  · have hsvEq : ht s = ht v := by omega
    have hwGap := nf_mul_height_key_gap (a:=D) hns
    rw [hws] at hwGap
    have hw2 : ht w + 2 ≤ ht s := by rcases hwGap with hh | hh <;> omega
    have hwGap' := nf_mul_height_key_gap (a:=d) hnt
    rw [hwt] at hwGap'
    have hwt2 : ht w + 2 ≤ ht t := by rcases hwGap' with hh | hh <;> omega
    have hov := mul_origin_of_right_height_le (a:=u) (b:=t) (by rw [hvt]; omega)
    rw [hvt] at hov
    have hos := mul_origin_of_right_height_le (a:=g) (b:=t) (by rw [hst]; omega)
    rw [hst] at hos
    obtain ⟨j,_,hnj,_,huj,htj,hjGap,_⟩ :=
      nf_return_origin_trace hnv hov (show mul a v = D from rfl) hDsmall
    obtain ⟨l,_,_,_,hgl,htl,hlGap,_⟩ :=
      nf_return_origin_trace hns hos hws (by omega)
    have hot := mul_origin_of_right_height_le (a:=D) (b:=j) (by rw [htj]; omega)
    rw [htj] at hot
    have hot' := mul_origin_of_right_height_le (a:=w) (b:=l) (by rw [htl]; omega)
    rw [htl] at hot'
    have hp := Prod.mk.inj (Option.some.inj (hot.symm.trans hot'))
    rw [hp.1] at huj htj hgl
    rw [←hp.2] at hgl
    change mul A j = u at huj
    have hjHeight := mul_height_growth_of_right_le (a:=w) (b:=j) (by rw [htj]; omega)
    rw [htj] at hjHeight
    have hjt : ht j + 1 = ht t := by omega
    have huHeight := inverse_height_strict (inverse_complete u a)
    change ht u < max (ht a) (ht g) at huHeight
    have huGap := nf_mul_height_key_gap (a:=A) hnj
    rw [huj] at huGap
    have hu2 : ht u + 2 ≤ ht j := by rcases huGap with hh | hh <;> omega
    have hneq : mul w w ≠ A := by
      intro he
      rw [he,huj] at hgl
      have hgu : g = u := hgl.symm
      exact mul_ne_right A g (hback.trans hgu.symm)
    obtain ⟨z,l',r,hjc⟩ := mul_return_of_height_lt (a:=A) (b:=j) (by rw [huj]; omega)
    have hgGrow := mul_height_off_return_key (a:=mul w w) hjc hneq
    rw [hgl] at hgGrow
    have hgUpper := mul_height_upper u a
    change ht g ≤ max (ht u) (ht a) + 1 at hgUpper
    omega

end submission.Austin12087Trace

prelude
import Init.Data.Option.Lemmas
import Init.Omega
import Init.RCases
import Init.WFTactics
import JudgeTraceSameKeyHighColumnClosed
set_option Elab.async false
/- Checked module: TraceLowColumnTailHeight -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem square_preimage_height {a e : T} (h : mul a e = mul a a) : ht a ≤ ht e := by
  by_cases hh : ht a ≤ ht e
  · exact hh
  · have hs : ht (mul a a) = ht a + 1 := by rw [mul_square]; rfl
    have ho := mul_origin_of_right_height_le (a:=a) (b:=e) (by rw [h]; omega)
    rw [h,mul_square] at ho
    have hea := (Prod.mk.inj (Option.some.inj ho)).2
    have heh := congrArg ht hea
    omega

theorem normal_low_column_tail_at_top {u a e v s t : T}
    (ha : NF a) (hng : NF (mul u a)) (hnv : NF v) (hns : NF s)
    (hvt : mul (mul (mul a a) (mul u a)) t = v)
    (hst : mul (mul u a) t = s) (hav : mul a v = e) (hes : mul e s = a)
    (he : ht e < ht v) (hsv : ht s < ht v) (hgv : ht (mul u a) < ht v)
    (htv : ht t < ht v) : ht v = ht t + 1 := by
  let A := mul a a
  let g := mul u a
  let B := mul A g
  change mul B t = v at hvt
  change mul g t = s at hst
  change NF g at hng
  change ht g < ht v at hgv
  have hA : ht A = ht a + 1 := by dsimp only [A]; rw [mul_square]; rfl
  have havGap := nf_mul_height_key_gap (a:=a) hnv
  rw [hav] at havGap
  have hav3 : ht a + 3 ≤ ht v := by rcases havGap with hh | hh <;> omega
  have hvHeight := mul_height_growth_of_right_le (a:=B) (b:=t) (by rw [hvt]; omega)
  rw [hvt] at hvHeight
  have hov := mul_origin_of_right_height_le (a:=B) (b:=t) (by rw [hvt]; omega)
  rw [hvt] at hov
  by_cases hh : ht v = ht t + 1
  · exact hh
  · have hBv : ht B + 1 = ht v := by omega
    have hBgGap := nf_mul_height_key_gap (a:=A) hng
    change ht B = max (ht A) (ht g) + 1 ∨ (ht A + 3 ≤ ht g ∧ ht B + 2 ≤ ht g) at hBgGap
    have hBg : ht B = max (ht A) (ht g) + 1 := by rcases hBgGap with hh | hh <;> omega
    have hoB := mul_origin_of_right_height_le (a:=A) (b:=g) (by change ht g ≤ ht B; omega)
    change origin B = some (A,g) at hoB
    obtain ⟨n,_,_,_,hHn,hen,hnGap,_⟩ := nf_return_origin_trace hnv hov hav he
    have hoB' := mul_origin_of_right_height_le (a:=mul a e) (b:=n) (by rw [hHn]; omega)
    rw [hHn,hoB] at hoB'
    have hp := Prod.mk.inj (Option.some.inj hoB')
    have hH : mul a e = A := hp.1.symm
    have hng' : n = g := hp.2.symm
    rw [hng'] at hen
    have hae := square_preimage_height hH
    have hesGap := nf_mul_height_key_gap (a:=e) hns
    rw [hes] at hesGap
    have hes3 : ht e + 3 ≤ ht s := by rcases hesGap with hh | hh <;> omega
    have hgv2 : ht g + 2 = ht v := by omega
    have htGap := nf_mul_height_key_gap (a:=e) hng
    rw [hen] at htGap
    have hgt : ht e + 3 ≤ ht g ∧ ht t + 2 ≤ ht g := by rcases htGap with hh | hh <;> omega
    have hsHeight := mul_height_growth_of_left_ge (a:=g) (b:=t) (by omega)
    rw [hst] at hsHeight
    have hos := mul_origin_of_right_height_le (a:=g) (b:=t) (by rw [hst]; omega)
    rw [hst] at hos
    obtain ⟨p,_,_,_,hCp,hap,hpGap,_⟩ := nf_return_origin_trace hns hos hes (by omega)
    have hog := mul_origin_of_right_height_le (a:=u) (b:=a) (by change ht a ≤ ht g; omega)
    change origin g = some (u,a) at hog
    have hog' := mul_origin_of_right_height_le (a:=mul e a) (b:=p) (by rw [hCp]; omega)
    rw [hCp,hog] at hog'
    have hCu : mul e a = u := (Prod.mk.inj (Option.some.inj hog')).1.symm
    have huHeight := mul_height_growth_of_left_ge (a:=e) (b:=a) hae
    rw [hCu] at huHeight
    have hgHeight := mul_height_growth_of_left_ge (a:=u) (b:=a) (by omega)
    change ht g = max (ht u) (ht a) + 1 at hgHeight
    omega

end submission.Austin12087Trace

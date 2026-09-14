prelude
import Init.Data.Option.Lemmas
import Init.Omega
import Init.RCases
import Init.WFTactics
import JudgeTraceLowAlignedColumns
set_option Elab.async false
/- Checked module: TraceSecondVLowGrowingMiddle -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_second_v_low_growing_middle_v_large_impossible {u a k y r s t : T}
    (hu : NF u) (ha : NF a) (hk : NF k) (hnr : NF r) (hns : NF s) (hnt : NF t)
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u)
    (hvr : ht (mul a k) < ht k)
    (hws : mul (mul a (mul a k)) s = mul a (mul (mul u a) k))
    (hrs : mul (mul a k) s = r)
    (hwr : ht (mul a (mul (mul u a) k)) < ht r)
    (hkh : ht k = ht r + 1)
    (hrc : r = c (mul a (mul a (mul (mul u a) k))) (mul u a) t (mul a k) s)
    (hvt : mul (mul (mul a (mul a (mul (mul u a) k))) (mul u a)) t = mul a k)
    (hst : mul (mul u a) t = s)
    (hsv : ht s ≤ ht (mul a k))
    (hmid : ht (mul a k) ≤ ht (mul (mul a (mul (mul u a) k)) (mul a k))) : False := by
  let g := mul u a
  let v := mul a k
  let w := mul a (mul g k)
  let A := mul a w
  let B := mul A g
  let e := mul w v
  change mul y e = u at hf
  change ht v < ht k at hvr
  change mul (mul a v) s = w at hws
  change mul v s = r at hrs
  change ht w < ht r at hwr
  change r = c A g t v s at hrc
  change mul B t = v at hvt
  change mul g t = s at hst
  change ht s ≤ ht v at hsv
  change ht v ≤ ht e at hmid
  have hrHeight := mul_height_growth_of_left_ge (a:=v) (b:=s) hsv
  rw [hrs] at hrHeight
  have hrh : ht r = ht v + 1 := by omega
  have hretGap := nf_mul_height_key_gap (a:=a) hk
  change ht v = max (ht a) (ht k) + 1 ∨ (ht a + 3 ≤ ht k ∧ ht v + 2 ≤ ht k) at hretGap
  have ha3 : ht a + 3 ≤ ht k := by rcases hretGap with hh | hh <;> omega
  have hcodeGap := nf_code_height_gap (hrc ▸ hnr)
  rw [←hrc] at hcodeGap
  have huHeight := inverse_height_strict (inverse_complete u a)
  change ht u < max (ht a) (ht g) at huHeight
  have hu2 : ht u + 2 ≤ ht v := by omega
  have heHeight := mul_height_growth_of_right_le (a:=w) (b:=v) hmid
  change ht e = max (ht w) (ht v) + 1 at heHeight
  have hoe := mul_origin_of_right_height_le (a:=w) (b:=v) hmid
  change origin e = some (w,v) at hoe
  have hnw : NF w := nf_mul ha (nf_mul (nf_mul hu ha) hk)
  have hnv : NF v := nf_mul ha hk
  obtain ⟨j,_,_,_,hwj,hvj,hjGap,_⟩ :=
    nf_return_origin_trace (nf_mul hnw hnv) hoe hf (by change ht u < ht e; omega)
  change ht j + 2 ≤ ht e at hjGap
  have hov := mul_origin_of_right_height_le (a:=u) (b:=j) (by rw [hvj]; omega)
  rw [hvj] at hov
  have hov' := mul_origin_of_right_height_le (a:=B) (b:=t) (by rw [hvt]; omega)
  rw [hvt] at hov'
  have hp := Prod.mk.inj (Option.some.inj (hov.symm.trans hov'))
  rw [hp.2] at hvj hwj
  have hvHeight := mul_height_growth_of_right_le (a:=u) (b:=t) (by rw [hvj]; omega)
  rw [hvj] at hvHeight
  exact normal_low_aligned_columns_impossible hnv hns hnt hvj hwj hst hws hp.1.symm
    (by omega) hsv (by omega) (by change ht g < ht v; omega)

theorem normal_second_v_growing_middle_low_trace {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u)
    (hvr : ht (mul a k) < ht k)
    (hmid : ht (mul a k) ≤ ht (mul (mul a (mul (mul u a) k)) (mul a k))) :
    let g := mul u a
    let v := mul a k
    let w := mul a (mul g k)
    ∃ r s t, NF r ∧ NF s ∧ NF t ∧ ht r < ht k ∧ ht s + 2 ≤ ht k ∧
      mul (mul a w) r = g ∧ mul w r = k ∧ mul (mul a v) s = w ∧ mul v s = r ∧
      ht w < ht r ∧ ht u < ht r ∧ ht a < ht r ∧ ht g < ht r ∧ ht k = ht r + 1 ∧
      r = c (mul a w) g t v s ∧ mul (mul (mul a w) g) t = v ∧ mul g t = s ∧
      ht t + 2 ≤ ht r ∧ ht v < ht s := by
  obtain ⟨r,s,hnr,hns,hrk,hsk,hgr,hkr,hws,hrs,hwr,hur,har,hgrh,hkh,t,hnt,hrc,hvt,hst,htgap⟩ :=
    normal_second_returning_v_low_head hu ha hk hf hvr
  have hvs : ht (mul a k) < ht s := by
    by_cases hh : ht (mul a k) < ht s
    · exact hh
    · exact False.elim (normal_second_v_low_growing_middle_v_large_impossible
        hu ha hk hnr hns hnt hf hvr hws hrs hwr hkh hrc hvt hst (by omega) hmid)
  exact ⟨r,s,t,hnr,hns,hnt,hrk,hsk,hgr,hkr,hws,hrs,hwr,hur,har,hgrh,hkh,hrc,hvt,hst,htgap,hvs⟩

end submission.Austin12087Trace

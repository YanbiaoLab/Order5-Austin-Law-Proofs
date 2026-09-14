prelude
import Init.Data.Option.Lemmas
import Init.Omega
import Init.RCases
import Init.WFTactics
import JudgeTraceSameKeyMiddleFrontier
set_option Elab.async false
/- Checked module: TraceSameKeyAlignedColumns -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_swapped_returns_top_column_impossible {a e g B v s t : T}
    (hnv : NF v) (hns : NF s) (hvt : mul B t = v) (hst : mul g t = s)
    (hav : mul a v = e) (hes : mul e s = a) (he : ht e < ht v)
    (hv : ht v = ht t + 1) (hs : ht s = ht t + 1) (hBg : B ≠ g) : False := by
  have havGap := nf_mul_height_key_gap (a:=a) hnv
  rw [hav] at havGap
  have ha3 : ht a + 3 ≤ ht v := by rcases havGap with hh | hh <;> omega
  have hov := mul_origin_of_right_height_le (a:=B) (b:=t) (by rw [hvt]; omega)
  rw [hvt] at hov
  have hos := mul_origin_of_right_height_le (a:=g) (b:=t) (by rw [hst]; omega)
  rw [hst] at hos
  obtain ⟨j,_,_,_,hBj,htj,hjGap,_⟩ := nf_return_origin_trace hnv hov hav he
  obtain ⟨l,_,_,_,hgl,htl,hlGap,_⟩ := nf_return_origin_trace hns hos hes (by omega)
  have hot := mul_origin_of_right_height_le (a:=e) (b:=j) (by rw [htj]; omega)
  rw [htj] at hot
  have hot' := mul_origin_of_right_height_le (a:=a) (b:=l) (by rw [htl]; omega)
  rw [htl] at hot'
  have hp := Prod.mk.inj (Option.some.inj (hot.symm.trans hot'))
  rw [hp.1,hp.2] at hBj
  rw [hp.1] at hgl
  exact hBg (hBj.symm.trans hgl)

theorem normal_same_key_equal_column_impossible {a e g v r s t : T}
    (hnv : NF v) (hnr : NF r) (hns : NF s) (hng : NF g)
    (hgr : mul (mul a a) r = g) (hgrh : ht g < ht r)
    (hvs : mul v s = r) (hor : origin r = some (v,s))
    (hvt : mul (mul (mul a a) g) t = v) (hst : mul g t = s)
    (hav : mul a v = e) (hes : mul e s = a) (he : ht e < ht v)
    (htGap : ht t + 2 ≤ ht r) (hsv : ht s = ht v) : False := by
  let A := mul a a
  let B := mul A g
  change mul A r = g at hgr
  change mul B t = v at hvt
  have hrHeight := mul_height_growth_of_right_le (a:=v) (b:=s) (by
    rw [hvs]; exact Nat.le_of_lt (origin_height hor).2)
  rw [hvs] at hrHeight
  have hgGap := nf_mul_height_key_gap (a:=A) hnr
  rw [hgr] at hgGap
  have hg2 : ht g + 2 ≤ ht r := by rcases hgGap with hh | hh <;> omega
  have hBg : B ≠ g := mul_ne_right A g
  by_cases httop : ht v = ht t + 1
  · exact normal_swapped_returns_top_column_impossible hnv hns hvt hst hav hes he httop (by omega) hBg
  · have htlow : ht t + 2 ≤ ht v := by omega
    have hvUpper := mul_height_upper B t
    rw [hvt] at hvUpper
    have hsUpper := mul_height_upper g t
    rw [hst] at hsUpper
    have hBHeight := inverse_height_strict (inverse_complete B t)
    rw [hvt] at hBHeight
    have hBgGap := nf_mul_height_key_gap (a:=A) hng
    change ht B = max (ht A) (ht g) + 1 ∨ (ht A + 3 ≤ ht g ∧ ht B + 2 ≤ ht g) at hBgGap
    rcases hBgGap with hh | hh <;> omega

theorem normal_second_same_key_unequal_column_trace {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u)
    (hvr : ht (mul a k) < ht k)
    (he : ht (mul (mul a (mul (mul u a) k)) (mul a k)) < ht (mul a k))
    (haw : a = mul a (mul (mul u a) k)) :
    let g := mul u a
    let v := mul a k
    ∃ r s, NF r ∧ NF s ∧ mul (mul a a) r = g ∧ mul a r = k ∧
      mul (mul a v) s = a ∧ mul v s = r ∧ ht s ≠ ht v := by
  obtain ⟨r,s,hnr,hns,_,_,hAr,hkr,hDs,hvs,_,_,_,hgr,_,t,_,hrc,hvt,hst,htGap⟩ :=
    normal_second_returning_v_low_head hu ha hk hf hvr
  rw [← haw] at hAr hkr hDs hrc hvt he
  have hor : origin r = some (mul a k,s) := by rw [hrc]; rfl
  refine ⟨r,s,hnr,hns,hAr,hkr,hDs,hvs,?_⟩
  intro hh
  exact normal_same_key_equal_column_impossible (nf_mul ha hk) hnr hns (nf_mul hu ha)
    hAr hgr hvs hor hvt hst rfl hDs he htGap hh

end submission.Austin12087Trace

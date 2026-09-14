prelude
import Init.Data.Option.Lemmas
import Init.Omega
import Init.RCases
import Init.WFTactics
import JudgeTraceSquareTargetLadder
set_option Elab.async false
/- Checked module: TraceSecondTwoColumnsGrow -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_second_two_growing_columns_growing_middle_impossible {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u)
    (hqg : ht k ≤ ht (mul (mul u a) k))
    (hvg : ht k ≤ ht (mul a k))
    (hm : ht (mul a k) ≤ ht (mul (mul a (mul (mul u a) k)) (mul a k))) : False := by
  let g := mul u a
  let q := mul g k
  let v := mul a k
  let w := mul a q
  let e := mul w v
  let f := mul y u
  change ht k ≤ ht v at hvg
  change ht v ≤ ht e at hm
  change mul y e = u at hf
  have hb := normal_second_query_k_dominates hu ha hk hf
  obtain ⟨r,hnr,hqc,hgr,hkr,hq,hw,hr⟩ := normal_second_growing_q_head hu ha hk hf hqg
  change q = c a w r g k at hqc
  change mul (mul a w) r = g at hgr
  change mul w r = k at hkr
  change ht q = ht k + 1 at hq
  change ht w < ht k at hw
  have hv := mul_height_growth_of_right_le (a:=a) (b:=k) hvg
  change ht v = max (ht a) (ht k) + 1 at hv
  have hov := mul_origin_of_right_height_le (a:=a) (b:=k) hvg
  change origin v = some (a,k) at hov
  have he := mul_height_growth_of_right_le (a:=w) (b:=v) hm
  change ht e = max (ht w) (ht v) + 1 at he
  have hoe := mul_origin_of_right_height_le (a:=w) (b:=v) hm
  change origin e = some (w,v) at hoe
  have hnq : NF q := nf_mul (nf_mul hu ha) hk
  have hne : NF e := nf_mul (nf_mul ha hnq) (nf_mul ha hk)
  obtain ⟨t,_,_,_,hft,hut,_,_⟩ := nf_return_origin_trace hne hoe hf (by omega)
  have hvw : v ≠ w := by intro hh; have hh' := congrArg ht hh; omega
  have hov' := (distinct_outputs_height_origin hut hft hvw (by omega)).1
  have hp := Prod.mk.inj (Option.some.inj (hov'.symm.trans hov))
  have hua : u = a := hp.1
  rw [hp.2] at hft
  change mul f k = w at hft
  have hkey := nf_code_key_height_gap (show NF (c a w r g k) from hqc ▸ hnq)
  rw [← hqc,← hua] at hkey
  have hsu : ht (mul u u) = ht u + 1 := by rw [mul_square]; rfl
  have hok := mul_origin_of_right_height_le (a:=w) (b:=r) (by rw [hkr]; omega)
  rw [hkr] at hok
  obtain ⟨h,_,hnh,_,hfh,hwh,hgap,_⟩ := nf_return_origin_trace hk hok hft hw
  have hkgrow := mul_height_growth_of_right_le (a:=w) (b:=r) (by rw [hkr]; omega)
  rw [hkr] at hkgrow
  have hwgap := nf_return_product_height_gap hk hft hw
  have hpw := nf_mul_height_key_gap (a:=f) hk
  rw [hft] at hpw
  have hw2 : ht w + 2 ≤ ht k := by rcases hpw with hpw | hpw <;> omega
  have hrh : ht h < ht r := by omega
  have hor := mul_origin_of_right_height_le (a:=w) (b:=h) (by rw [hwh]; omega)
  rw [hwh] at hor
  have hgr' : mul (mul u w) r = mul u u := by
    change mul (mul a w) r = mul u a at hgr
    rw [hua] at hgr
    rw [hua]
    exact hgr
  have hsbound : ht (mul u u) < ht r := by
    have hpg := nf_mul_height_key_gap (a:=mul u w) hnr
    rw [hgr'] at hpg
    rcases hpg with hpg | hpg <;> omega
  have hl : ReturnLadder (mul u w) (mul f w) w (mul u u) w r h :=
    ⟨hnr,hwh,hor,hgr',hfh⟩
  exact square_target_return_ladder_impossible (mul_ne_right y u) hl hsbound

end submission.Austin12087Trace

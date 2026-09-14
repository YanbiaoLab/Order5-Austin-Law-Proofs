prelude
import Init.Data.Option.Lemmas
import Init.Omega
import Init.RCases
import Init.WFTactics
import JudgeTraceFixedSquarePairGrowth
set_option Elab.async false
/- Checked module: TraceSmallFixedPair -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_fixed_pair_small_growing_key_impossible {u a b k : T}
    (hu : NF u) (ha : NF a) (hb : NF b) (hk : NF k)
    (hua : ht u < ht a) (hbu : ht b ≤ ht u + 3)
    (hr : mul u (mul a k) = u) (hfixT : mul u (mul b k) = u)
    (hret : ht (mul a k) < ht k) (hgrow : ht k ≤ ht (mul b k)) : False := by
  let A := mul u u
  let r := mul a k
  let t := mul b k
  change mul u r = u at hr
  change mul u t = u at hfixT
  change ht r < ht k at hret
  have hnr : NF r := nf_mul ha hk
  have hnt : NF t := nf_mul hb hk
  have hkgap := nf_mul_height_key_gap (a:=a) hk
  change ht r = max (ht a) (ht k) + 1 ∨ (ht a + 3 ≤ ht k ∧ ht r + 2 ≤ ht k) at hkgap
  have ha3 : ht a + 3 ≤ ht k := by rcases hkgap with hh | hh <;> omega
  have htg := mul_height_growth_of_right_le (a:=b) (b:=k) hgrow
  change ht t = max (ht b) (ht k) + 1 at htg
  have hot := mul_origin_of_right_height_le (a:=b) (b:=k) hgrow
  change origin t = some (b,k) at hot
  have hut : ht u < ht t := by
    have hi := inverse_height_strict (inverse_complete u t)
    rw [hfixT] at hi
    omega
  obtain ⟨h,_,hnh,_,hbh,hkh,hhgap,_⟩ := nf_return_origin_trace hnt hot hfixT hut
  change mul A h = b at hbh
  change ht h + 2 ≤ ht t at hhgap
  have hkg := mul_height_growth_of_right_le (a:=u) (b:=h) (by rw [hkh]; omega)
  rw [hkh] at hkg
  have hok := mul_origin_of_right_height_le (a:=u) (b:=h) (by rw [hkh]; omega)
  rw [hkh] at hok
  obtain ⟨j,_,_,_,huj,hhj,hjgap,_⟩ :=
    nf_return_origin_trace hk hok (show mul a k = r from rfl) hret
  have hoh := mul_origin_of_right_height_le (a:=r) (b:=j) (by rw [hhj]; omega)
  rw [hhj] at hoh
  have hbr := nf_mul_height_key_gap (a:=A) hnh
  rw [hbh] at hbr
  have hbhsmall : ht b < ht h := by rcases hbr with hh | hh <;> omega
  have hufixed := nf_mul_height_key_gap (a:=u) hnr
  rw [hr] at hufixed
  have hur3 : ht u + 3 ≤ ht r := by rcases hufixed with hh | hh <;> omega
  obtain ⟨s,l,z,hrc⟩ := mul_return_of_height_lt (a:=u) (b:=r) (by rw [hr]; omega)
  have hau : a ≠ u := by intro heq; have hh := congrArg ht heq; omega
  have harg := mul_height_off_return_key (a:=a) hrc hau
  have hl : ReturnLadder A (mul a r) r b u h j := ⟨hnh,hhj,hoh,hbh,huj⟩
  exact return_ladder_second_dominant_impossible hl hbhsmall (by omega) (by omega) (by omega)

theorem normal_small_base_fixed_square_pair_impossible {u b k : T}
    (hu : NF u) (hb : NF b) (hk : NF k)
    (hub : ht u < ht b) (hbu : ht b ≤ ht u + 2)
    (hr : mul u (mul b k) = u)
    (hfixT : mul u (mul (mul b b) k) = u) : False := by
  have hB : ht (mul b b) = ht b + 1 := by rw [mul_square]; rfl
  rcases normal_fixed_square_pair_alternatives hu hb hk hr hfixT with hh | hh
  · exact normal_fixed_pair_small_growing_key_impossible hu hb (nf_mul hb hb) hk hub (by omega)
      hr hfixT hh.1 (by omega)
  · exact normal_fixed_pair_small_growing_key_impossible hu (nf_mul hb hb) hb hk (by omega) (by omega)
      hfixT hr hh.1 (by omega)

end submission.Austin12087Trace

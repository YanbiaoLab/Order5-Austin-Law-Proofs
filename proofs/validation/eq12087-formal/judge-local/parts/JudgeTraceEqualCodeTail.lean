prelude
import Init.Data.Option.Lemmas
import Init.Omega
import Init.RCases
import Init.WFTactics
import JudgeTraceEqualCodeGeometry
set_option Elab.async false
/- Checked module: TraceEqualCodeTail -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_equal_code_tail_returns {u q h z : T}
    (hu : NF u) (hq : NF q)
    (hn : NF (c (mul u q) u h (mul (mul u u) q) z))
    (hsmall : ht q < ht (c (mul u q) u h (mul (mul u u) q) z))
    (hbz : ht (mul (mul u u) q) < ht z)
    (hfixed : mul u (mul q z) = u) : ht (mul q z) < ht z := by
  let A := mul u u
  let b := mul A q
  let w := mul u q
  let e := c w u h b z
  let t := mul q z
  change NF e at hn
  change mul u t = u at hfixed
  have hA : ht A = ht u + 1 := by dsimp only [A]; rw [mul_square]; rfl
  obtain ⟨hu3,hw2,hhz,hb2,hoz⟩ := normal_equal_code_geometry hq hn hsmall hbz
  change ht w + 2 ≤ ht z at hw2
  change ht b + 2 ≤ ht h at hb2
  have hc := nf_code_actual hn
  have hnh : NF h := hc.2.2.1
  have hnz : NF z := hc.2.2.2.2.1
  have hnt : NF t := nf_mul hq hnz
  have hbh : mul (mul w u) h = b := hc.2.2.2.2.2.2.1
  have hzh : mul u h = z := hc.2.2.2.2.2.2.2
  change ht t < ht z
  by_cases htz : ht t < ht z
  · exact htz
  · have htg := mul_height_growth_of_right_le (a:=q) (b:=z) (by change ht z ≤ ht t; omega)
    change ht t = max (ht q) (ht z) + 1 at htg
    have heact : mul b z = e := hc.2.2.2.2.2.1
    have heo : origin e = some (b,z) := rfl
    have heg := mul_height_growth_of_right_le (a:=b) (b:=z) (by
      rw [heact]
      exact Nat.le_of_lt (origin_height heo).2)
    rw [heact] at heg
    change ht q < ht e at hsmall
    change ht b < ht z at hbz
    have hot := mul_origin_of_right_height_le (a:=q) (b:=z) (by change ht z ≤ ht t; omega)
    change origin t = some (q,z) at hot
    obtain ⟨s,_,_,_,hqs,hzs,hsgap,_⟩ := nf_return_origin_trace hnt hot hfixed (by omega)
    change mul A s = q at hqs
    have hoz' := mul_origin_of_right_height_le (a:=u) (b:=s) (by rw [hzs]; omega)
    rw [hzs] at hoz'
    have hsh : s = h := (Prod.mk.inj (Option.some.inj (hoz'.symm.trans hoz))).2
    rw [hsh] at hqs
    have hAD : A ≠ mul w u := by
      intro heq
      have hqb : q = b := hqs.symm.trans (by rw [heq]; exact hbh)
      exact mul_ne_right A q hqb.symm
    obtain ⟨r,l,j,hhc⟩ := mul_return_of_height_lt (a:=mul w u) (b:=h) (by rw [hbh]; omega)
    have hqg := mul_height_off_return_key (a:=A) hhc hAD
    rw [hqs] at hqg
    have hqz : ht q = ht z := by omega
    obtain ⟨r',l',j',hqc⟩ := mul_return_of_height_lt (a:=u) (b:=q) (by change ht w < ht q; omega)
    have hAu : A ≠ u := by intro heq; have heh := congrArg ht heq; omega
    have hbg := mul_height_off_return_key (a:=A) hqc hAu
    change ht b = max (ht A) (ht q) + 1 at hbg
    exact False.elim (by omega)

theorem normal_equal_code_key_repeats {u q h z : T}
    (hu : NF u) (hq : NF q)
    (hn : NF (c (mul u q) u h (mul (mul u u) q) z))
    (hsmall : ht q < ht (c (mul u q) u h (mul (mul u u) q) z))
    (hbz : ht (mul (mul u u) q) < ht z)
    (hfixed : mul u (mul q z) = u) : q = u := by
  let A := mul u u
  let b := mul A q
  let w := mul u q
  let e := c w u h b z
  let t := mul q z
  change NF e at hn
  change mul u t = u at hfixed
  have htz := normal_equal_code_tail_returns hu hq hn hsmall hbz hfixed
  change ht t < ht z at htz
  obtain ⟨hu3,_,hhz,hb2,hoz⟩ := normal_equal_code_geometry hq hn hsmall hbz
  change ht b + 2 ≤ ht h at hb2
  have hc := nf_code_actual hn
  have hnz : NF z := hc.2.2.2.2.1
  have hbh : mul (mul w u) h = b := hc.2.2.2.2.2.2.1
  have hzh : mul u h = z := hc.2.2.2.2.2.2.2
  by_cases hqu : q = u
  · exact hqu
  · have hut : ht u < ht t := by
      have hi := inverse_height_strict (inverse_complete u t)
      rw [hfixed] at hi
      omega
    obtain ⟨s,l,r,htc⟩ := mul_return_of_height_lt (a:=u) (b:=t) (by rw [hfixed]; exact hut)
    have hBg := mul_height_off_return_key (a:=q) htc hqu
    have hA : ht A = ht u + 1 := by dsimp only [A]; rw [mul_square]; rfl
    have hbu := mul_height_upper A q
    change ht b ≤ max (ht A) (ht q) + 1 at hbu
    have hl : ReturnLadder q (mul w u) u t b z h := ⟨hnz,hzh,hoz,rfl,hbh⟩
    obtain ⟨s',hl',_⟩ := return_ladder_step hl htz (by omega)
    exact False.elim (return_ladder_second_dominant_impossible hl' (by omega) (by omega) (by omega) (by omega))

end submission.Austin12087Trace

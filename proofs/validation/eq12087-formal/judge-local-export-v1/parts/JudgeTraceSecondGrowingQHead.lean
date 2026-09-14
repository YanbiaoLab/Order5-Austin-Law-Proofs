prelude
import Init.Data.Option.Lemmas
import Init.Omega
import Init.RCases
import Init.WFTactics
import JudgeTraceSquareTransport
set_option Elab.async false
/- Checked module: TraceSecondGrowingQHead -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_second_growing_q_head {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u)
    (hqg : ht k ≤ ht (mul (mul u a) k)) :
    let g := mul u a
    let q := mul g k
    let w := mul a q
    ∃ r, NF r ∧ q = c a w r g k ∧
      mul (mul a w) r = g ∧ mul w r = k ∧
      ht q = ht k + 1 ∧ ht w < ht k ∧ ht r < ht k := by
  let g := mul u a
  let q := mul g k
  let v := mul a k
  let w := mul a q
  let e := mul w v
  change ht k ≤ ht q at hqg
  change mul y e = u at hf
  have hb := normal_second_query_k_dominates hu ha hk hf
  have hgu := mul_height_upper u a
  change ht g ≤ max (ht u) (ht a) + 1 at hgu
  have hq := mul_height_growth_of_right_le (a:=g) (b:=k) hqg
  change ht q = max (ht g) (ht k) + 1 at hq
  have hoq := mul_origin_of_right_height_le (a:=g) (b:=k) hqg
  change origin q = some (g,k) at hoq
  have hvu := mul_height_upper a k
  change ht v ≤ max (ht a) (ht k) + 1 at hvu
  have hnq : NF q := nf_mul (nf_mul hu ha) hk
  have hnw : NF w := nf_mul ha hnq
  have hne : NF e := nf_mul hnw (nf_mul ha hk)
  have hwq : ht w < ht q := by
    by_cases hh : ht w < ht q
    · exact hh
    · have hwg := mul_height_growth_of_right_le (a:=a) (b:=q) (by change ht q ≤ ht w; omega)
      change ht w = max (ht a) (ht q) + 1 at hwg
      have how := mul_origin_of_right_height_le (a:=a) (b:=q) (by change ht q ≤ ht w; omega)
      change origin w = some (a,q) at how
      have heg := mul_height_growth_of_left_ge (a:=w) (b:=v) (by omega)
      change ht e = max (ht w) (ht v) + 1 at heg
      have hoe := mul_origin_of_right_height_le (a:=w) (b:=v) (by change ht v ≤ ht e; omega)
      change origin e = some (w,v) at hoe
      obtain ⟨t,_,_,_,hft,hut,_,_⟩ := nf_return_origin_trace hne hoe hf (by omega)
      have hwv : w ≠ v := by intro heq; have hh' := congrArg ht heq; omega
      have how' := (distinct_outputs_height_origin hft hut hwv (by omega)).1
      have hp := Prod.mk.inj (Option.some.inj (how'.symm.trans how))
      rw [hp.2] at hut
      exact False.elim (nf_no_flip hu ha hk hut)
  obtain ⟨r,hcode,hnr,_,hgr,hkr,hrgap,_⟩ :=
    nf_return_origin_trace hnq hoq (show mul a q = w from rfl) hwq
  have hgap := nf_code_height_gap (show NF (c a w r g k) from hcode ▸ hnq)
  change ht a + 2 ≤ ht (c a w r g k) ∧ ht w + 2 ≤ ht (c a w r g k) ∧
    ht r + 2 ≤ ht (c a w r g k) at hgap
  rw [← hcode] at hgap
  change ∃ r, NF r ∧ q = c a w r g k ∧ mul (mul a w) r = g ∧
    mul w r = k ∧ ht q = ht k + 1 ∧ ht w < ht k ∧ ht r < ht k
  exact ⟨r,hnr,hcode,hgr,hkr,by omega,by omega,by omega⟩

end submission.Austin12087Trace

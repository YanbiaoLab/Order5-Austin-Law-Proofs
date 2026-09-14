prelude
import Init.Data.Option.Lemmas
import Init.Omega
import Init.RCases
import Init.WFTactics
import JudgeTraceSecondSuffices
set_option Elab.async false
/- Checked module: TraceSecondMaxHead -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_second_max_u_head {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hau : ht a ≤ ht u) (hku : ht k ≤ ht u)
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u) :
    let w := mul a (mul (mul u a) k)
    mul a w = u ∧ mul w a = k ∧ ht a < ht u ∧ ht w < ht u := by
  let g := mul u a
  let q := mul g k
  let v := mul a k
  let w := mul a q
  let e := mul w v
  change mul a w = u ∧ mul w a = k ∧ ht a < ht u ∧ ht w < ht u
  have hng : NF g := nf_mul hu ha
  have hnq : NF q := nf_mul hng hk
  have hnv : NF v := nf_mul ha hk
  have hnw : NF w := nf_mul ha hnq
  have hne : NF e := nf_mul hnw hnv
  have hgg := mul_height_growth_of_left_ge (a:=u) (b:=a) hau
  change ht g = max (ht u) (ht a) + 1 at hgg
  have hqg := mul_height_growth_of_left_ge (a:=g) (b:=k) (by omega)
  change ht q = max (ht g) (ht k) + 1 at hqg
  have hvu := mul_height_upper a k
  change ht v ≤ max (ht a) (ht k) + 1 at hvu
  have how : ht w < ht q := by
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
      obtain ⟨h,_,_,_,hfh,huh,_,_⟩ := nf_return_origin_trace hne hoe hf (by omega)
      have hwv : w ≠ v := by intro heq; have hh' := congrArg ht heq; omega
      have how' := (distinct_outputs_height_origin hfh huh hwv (by omega)).1
      have hp := Prod.mk.inj (Option.some.inj (how'.symm.trans how))
      rw [hp.2] at huh
      exact False.elim (nf_no_flip hu ha hk huh)
  have hoq := mul_origin_of_right_height_le (a:=g) (b:=k) (by change ht k ≤ ht q; omega)
  change origin q = some (g,k) at hoq
  obtain ⟨r,hqc,_,_,hbr,hwr,hrr,haq⟩ :=
    nf_return_origin_trace hnq hoq (show mul a q = w from rfl) how
  have hog := mul_origin_of_right_height_le (a:=u) (b:=a) (by change ht a ≤ ht g; omega)
  change origin g = some (u,a) at hog
  have hog' := mul_origin_of_right_height_le (a:=mul a w) (b:=r) (by rw [hbr]; omega)
  rw [hbr] at hog'
  have hp := Prod.mk.inj (Option.some.inj (hog'.symm.trans hog))
  have hwa : mul w a = k := by rw [hp.2] at hwr; exact hwr
  have hwu := mul_height_growth_of_right_le (a:=a) (b:=w) (by
    rw [hp.1]
    have hwq := (nf_code_height_gap (hqc ▸ hnq)).2.1
    rw [←hqc] at hwq
    omega)
  rw [hp.1] at hwu
  exact ⟨hp.1,hwa,by omega,by omega⟩

end submission.Austin12087Trace

prelude
import Init.Data.Option.Lemmas
import Init.Omega
import Init.RCases
import Init.WFTactics
import JudgeTraceHighColumnReturnCycle
set_option Elab.async false
/- Checked module: TraceSameKeyHighColumnClosed -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_same_key_high_column_impossible {u a v r s y : T}
    (hu : NF u) (ha : NF a) (hnv : NF v)
    (hl : ReturnLadder (mul a a) (mul a v) v (mul u a) a r s)
    (hgr : ht (mul u a) < ht r) (he : ht (mul a v) < ht v)
    (hgv : ht (mul u a) < ht v) (hvs : ht v < ht s)
    (hf : mul y (mul a v) = u) : False := by
  obtain ⟨hB,t,j,hl₂,hvt,_,_⟩ := normal_same_key_high_column_keys hnv hl hgr he hgv hvs
  have hout := normal_same_key_high_column_outer_return hu ha hnv hl hgr he hgv hvs hf
  obtain ⟨m,_,_,_,_,ham,_,hgm,_⟩ := normal_square_key_return_geometry hu ha hB
  exact normal_high_column_return_cycle_impossible ha hnv rfl he (by omega) (by omega) hl₂ hvt

theorem normal_second_same_key_low_column_frontier {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k) (hs : NormalSecondBelow (ht k))
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u) :
    let g := mul u a
    let v := mul a k
    let e := mul a v
    a = mul a (mul g k) ∧ ht g < ht v ∧ ht e < ht v ∧
    ∃ r s, NF r ∧ NF s ∧ mul (mul a a) r = g ∧ mul a r = k ∧
      mul e s = a ∧ mul v s = r ∧ ht s < ht v := by
  have haw := normal_second_induction_requires_equal_return_keys hu ha hk hs hf
  obtain ⟨hvr,he⟩ := normal_second_induction_requires_two_returns hu ha hk hs hf
  have hgv := normal_second_same_key_g_below_v hu ha hk hf hvr he haw
  obtain ⟨r,s,hnr,hns,_,_,hAr,hkr,hDs,hvs,_,_,_,hgr,_,t,_,hrc,hvt,hst,htGap⟩ :=
    normal_second_returning_v_low_head hu ha hk hf hvr
  rw [← haw] at hAr hkr hDs hrc hvt hf he
  have hor : origin r = some (mul a k,s) := by rw [hrc]; rfl
  have hl : ReturnLadder (mul a a) (mul a (mul a k)) (mul a k) (mul u a) a r s :=
    ⟨hnr,hvs,hor,hAr,hDs⟩
  refine ⟨haw,hgv,he,r,s,hnr,hns,hAr,hkr,hDs,hvs,?_⟩
  by_cases hh : ht s < ht (mul a k)
  · exact hh
  · by_cases heq : ht s = ht (mul a k)
    · exact False.elim (normal_same_key_equal_column_impossible (nf_mul ha hk) hnr hns (nf_mul hu ha)
        hAr hgr hvs hor hvt hst rfl hDs he htGap heq)
    · exact False.elim (normal_same_key_high_column_impossible hu ha (nf_mul ha hk) hl hgr he hgv (by omega) hf)

end submission.Austin12087Trace

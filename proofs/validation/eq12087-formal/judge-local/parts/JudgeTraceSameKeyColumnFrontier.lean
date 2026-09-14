prelude
import Init.Data.Option.Lemmas
import Init.Omega
import Init.RCases
import Init.WFTactics
import JudgeTraceSameKeyHighColumnOuter
set_option Elab.async false
/- Checked module: TraceSameKeyColumnFrontier -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_second_same_key_column_frontier {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k) (hs : NormalSecondBelow (ht k))
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u) :
    let g := mul u a
    let v := mul a k
    let e := mul a v
    a = mul a (mul g k) ∧ ht g < ht v ∧
    ∃ r s, NF r ∧ NF s ∧ mul (mul a a) r = g ∧ mul a r = k ∧
      mul e s = a ∧ mul v s = r ∧
      (ht s < ht v ∨ (ht v < ht s ∧ mul (mul a a) g = a ∧
        ht g + 1 ≤ ht e ∧ ht y + 3 ≤ ht e)) := by
  have haw := normal_second_induction_requires_equal_return_keys hu ha hk hs hf
  obtain ⟨hvr,he⟩ := normal_second_induction_requires_two_returns hu ha hk hs hf
  have hgv := normal_second_same_key_g_below_v hu ha hk hf hvr he haw
  obtain ⟨r,s,hnr,hns,hrk,_,hAr,hkr,hDs,hvs,_,_,_,hgr,_,t,_,hrc,hvt,hst,htGap⟩ :=
    normal_second_returning_v_low_head hu ha hk hf hvr
  rw [← haw] at hAr hkr hDs hrc hvt hf he
  have hor : origin r = some (mul a k,s) := by rw [hrc]; rfl
  have hl : ReturnLadder (mul a a) (mul a (mul a k)) (mul a k) (mul u a) a r s :=
    ⟨hnr,hvs,hor,hAr,hDs⟩
  refine ⟨haw,hgv,r,s,hnr,hns,hAr,hkr,hDs,hvs,?_⟩
  have hne : ht s ≠ ht (mul a k) := by
    intro hh
    exact normal_same_key_equal_column_impossible (nf_mul ha hk) hnr hns (nf_mul hu ha)
      hAr hgr hvs hor hvt hst rfl hDs he htGap hh
  by_cases hsv : ht s < ht (mul a k)
  · exact Or.inl hsv
  · have hvs' : ht (mul a k) < ht s := by omega
    obtain ⟨hB,_⟩ := normal_same_key_high_column_keys (nf_mul ha hk) hl hgr he hgv hvs'
    have ho := normal_same_key_high_column_outer_return hu ha (nf_mul ha hk) hl hgr he hgv hvs' hf
    exact Or.inr ⟨hvs',hB,ho⟩

end submission.Austin12087Trace

prelude
import TraceShortColumnTransport
set_option autoImplicit false

namespace Austin12087Trace
open T

theorem normal_second_v_high_head_impossible {u a k y r s : T}
    (hu : NF u) (ha : NF a) (hk : NF k) (hnr : NF r) (hns : NF s)
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u)
    (hvr : ht (mul a k) < ht k)
    (hgr : mul (mul a (mul a (mul (mul u a) k))) r = mul u a)
    (hkr : mul (mul a (mul (mul u a) k)) r = k)
    (hws : mul (mul a (mul a k)) s = mul a (mul (mul u a) k))
    (hrs : mul (mul a k) s = r)
    (hwk : ht (mul a (mul (mul u a) k)) < ht k)
    (hrk : ht r < ht k) (hsk : ht s + 2 ≤ ht k)
    (hrw : ht r ≤ ht (mul a (mul (mul u a) k))) : False := by
  let g := mul u a
  let v := mul a k
  let w := mul a (mul g k)
  obtain ⟨hus,_,hAw,hvs,husmall,hasmall,hwh,_⟩ :=
    normal_second_v_high_head_trace hu ha hk hns hf hvr hgr hkr hws hrs hwk hrk hsk hrw
  change mul u s = v at hus
  change ht (mul a w) < ht w at hAw
  change ht v < ht s at hvs
  change ht w = ht s + 1 at hwh
  change mul (mul a w) r = g at hgr
  change mul (mul a v) s = w at hws
  change mul v s = r at hrs
  have hnw : NF w := nf_mul ha (nf_mul (nf_mul hu ha) hk)
  by_cases hvu : v = u
  · have hru : r = u := by rw [hvu,hus,hvu] at hrs; exact hrs.symm
    have horder := normal_second_v_factor_order hu ha hk hf hgr hkr
    change ht u < max (ht a) (ht r) ∧ (ht g < ht a ∨ ht g < ht r) at horder
    rw [hru] at horder
    have hua : ht u < ht a := by omega
    have hga : ht g < ht a := by rcases horder.2 with hh | hh <;> omega
    rw [hru] at hgr
    rw [hvu] at hws
    exact normal_v_equal_fixed_exception_impossible hnw (hus.trans hvu) hws hgr hua hga hAw hwh
  · obtain ⟨_,_,_,t,hnt,_,hvt,havt,hth⟩ :=
      normal_v_high_head_distinct_fixed hu ha hnw hnr hus hrs hws hgr hAw hvs husmall hasmall hwh hvu
    exact normal_v_distinct_fixed_exception_impossible hnw hnt hAw hwh hth hvs hvt havt

theorem normal_second_returning_v_low_head {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u)
    (hvr : ht (mul a k) < ht k) :
    let g := mul u a
    let v := mul a k
    let w := mul a (mul g k)
    ∃ r s, NF r ∧ NF s ∧ ht r < ht k ∧ ht s + 2 ≤ ht k ∧
      mul (mul a w) r = g ∧ mul w r = k ∧ mul (mul a v) s = w ∧ mul v s = r ∧
      ht w < ht r ∧ ht u < ht r ∧ ht a < ht r ∧ ht g < ht r ∧ ht k = ht r + 1 ∧
      ∃ t, NF t ∧ r = c (mul a w) g t v s ∧
        mul (mul (mul a w) g) t = v ∧ mul g t = s ∧ ht t + 2 ≤ ht r := by
  obtain ⟨r,s,hnr,hns,_,_,hgr,hkr,hws,hrs,hwk,hrk,hsk,_⟩ :=
    normal_second_returning_v_trace hu ha hk hf hvr
  have hwr : ht (mul a (mul (mul u a) k)) < ht r := by
    by_cases hh : ht (mul a (mul (mul u a) k)) < ht r
    · exact hh
    · exact False.elim (normal_second_v_high_head_impossible hu ha hk hnr hns hf hvr
        hgr hkr hws hrs hwk hrk hsk (by omega))
  exact ⟨r,s,hnr,hns,hrk,hsk,hgr,hkr,hws,hrs,hwr,
    normal_second_v_low_head_trace hu ha hk hnr hf hvr hgr hkr hrs hrk hsk hwr⟩

end Austin12087Trace
#print axioms Austin12087Trace.normal_second_v_high_head_impossible
#print axioms Austin12087Trace.normal_second_returning_v_low_head

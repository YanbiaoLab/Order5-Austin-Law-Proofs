prelude
import TraceSecondVLowHead
set_option autoImplicit false

namespace Austin12087Trace
open T

theorem normal_second_returning_v_frontier {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u)
    (hvr : ht (mul a k) < ht k) :
    let g := mul u a
    let v := mul a k
    let w := mul a (mul g k)
    ∃ r s, NF r ∧ NF s ∧ ht r < ht k ∧ ht s < ht k ∧
      mul (mul a w) r = g ∧ mul w r = k ∧ mul (mul a v) s = w ∧ mul v s = r ∧
      ((ht w < ht r ∧ ht u < ht r ∧ ht a < ht r ∧ ht g < ht r ∧ ht k = ht r + 1 ∧
        ∃ t, NF t ∧ r = c (mul a w) g t v s ∧
          mul (mul (mul a w) g) t = v ∧ mul g t = s ∧ ht t + 2 ≤ ht r) ∨
       (v = u ∧ r = u ∧ y = a ∧ ht u < ht a ∧ ht g < ht a ∧
        mul u s = u ∧ ht (mul a w) < ht w ∧ ht w = ht s + 1 ∧ ht k = ht s + 2) ∨
       (v ≠ u ∧ mul a w = g ∧ mul g r = g ∧ mul y u = mul a v ∧ mul u s = v ∧
        ht r = ht w ∧ ht w = ht s + 1 ∧ ht k = ht s + 2 ∧
        ∃ t, NF t ∧ mul g t = s ∧ mul (mul g g) t = v ∧
          mul (mul a g) t = mul a v ∧ ht t + 1 = ht s)) := by
  let g := mul u a
  let v := mul a k
  let w := mul a (mul g k)
  obtain ⟨r,s,hnr,hns,_,_,hgr,hkr,hws,hrs,hwk,hrk,hsk,_⟩ :=
    normal_second_returning_v_trace hu ha hk hf hvr
  change mul (mul a w) r = g at hgr
  change mul w r = k at hkr
  change mul (mul a v) s = w at hws
  change mul v s = r at hrs
  change ht w < ht k at hwk
  refine ⟨r,s,hnr,hns,hrk,by omega,hgr,hkr,hws,hrs,?_⟩
  by_cases hwr : ht w < ht r
  · have hh := normal_second_v_low_head_trace hu ha hk hnr hf hvr hgr hkr hrs hrk hsk hwr
    exact Or.inl ⟨hwr,hh⟩
  · obtain ⟨hus,hyu,hAw,hvs,husmall,hasmall,hwh,hkh⟩ :=
      normal_second_v_high_head_trace hu ha hk hns hf hvr hgr hkr hws hrs hwk hrk hsk (by change ht r ≤ ht w; omega)
    change mul u s = v at hus
    change mul y u = mul a v at hyu
    change ht (mul a w) < ht w at hAw
    change ht v < ht s at hvs
    change ht w = ht s + 1 at hwh
    by_cases hvu : v = u
    · have hru : r = u := by rw [hvu,hus,hvu] at hrs; exact hrs.symm
      have hya : y = a := by rw [hvu] at hyu; exact right_injective _ _ u hyu
      have horder := normal_second_v_factor_order hu ha hk hf hgr hkr
      change ht u < max (ht a) (ht r) ∧ (ht g < ht a ∨ ht g < ht r) at horder
      rw [hru] at horder
      have hua : ht u < ht a := by omega
      have hga : ht g < ht a := by rcases horder.2 with hh | hh <;> omega
      exact Or.inr (Or.inl ⟨hvu,hru,hya,hua,hga,hus.trans hvu,hAw,hwh,hkh⟩)
    · have hnw : NF w := nf_mul ha (nf_mul (nf_mul hu ha) hk)
      obtain ⟨hag,hfix,hrw,t,hnt,hst,hvt,havt,hth⟩ :=
        normal_v_high_head_distinct_fixed hu ha hnw hnr hus hrs hws hgr hAw hvs husmall hasmall hwh hvu
      exact Or.inr (Or.inr ⟨hvu,hag,hfix,hyu,hus,hrw,hwh,hkh,t,hnt,hst,hvt,havt,hth⟩)

end Austin12087Trace
#print axioms Austin12087Trace.normal_second_returning_v_frontier

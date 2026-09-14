prelude
import TraceDescent
set_option autoImplicit false

namespace Austin12087Trace
open T

theorem distinct_columns_larger_returns {a b q k v : T}
    (ha : mul a q = v) (hb : mul b k = v) (hn : q ≠ k)
    (hs : sz q ≤ sz k) : ∃ h l r, k = c b v h l r := by
  rcases mul_grows_or_returns b k with hg | ⟨w,h,l,r,hk,hw⟩
  · have hq : sz q ≤ sz (mul a q) := by rw [ha,←hb]; omega
    have ho := mul_origin_of_right_le hq
    rw [ha,←hb,hg.2.2] at ho
    have hp := Prod.mk.inj (Option.some.inj ho)
    exact False.elim (hn hp.2.symm)
  · exact ⟨h,l,r,by rw [hb] at hw; rw [←hw] at hk; exact hk⟩

theorem different_plain_columns_disjoint {a b q k : T}
    (hq : PlainRight q) (hk : PlainRight k) (hn : q ≠ k) :
    mul a q ≠ mul b k := by
  intro he
  by_cases hs : sz q ≤ sz k
  · obtain ⟨h,l,r,hc⟩ := distinct_columns_larger_returns he rfl hn hs
    rw [hc] at hk; exact hk
  · obtain ⟨h,l,r,hc⟩ := distinct_columns_larger_returns he.symm rfl (Ne.symm hn) (by omega)
    rw [hc] at hq; exact hq

theorem first_offdiagonal_larger_k_return {u q k y : T}
    (hf : mul (mul y u) k = mul (mul u (mul q (mul u k))) q)
    (hn : q ≠ k) (hs : sz q ≤ sz k) :
    (∃ h l r, k = c (mul y u) (mul (mul y u) k) h l r) ∧
    sz u < sz (mul u k) ∧ sz k < sz (mul u k) ∧
      origin (mul u k) = some (u,k) := by
  obtain ⟨h,l,r,hc⟩ := distinct_columns_larger_returns hf.symm rfl hn hs
  refine ⟨⟨h,l,r,hc⟩,?_⟩
  rcases mul_grows_or_returns u k with hg | ⟨v,j,l',r',hc',_⟩
  · exact hg
  · have hp := T.c.inj (hc.symm.trans hc')
    exact False.elim (mul_ne_right y u hp.1)

theorem first_offdiagonal_larger_q_return {u q k y : T}
    (hf : mul (mul y u) k = mul (mul u (mul q (mul u k))) q)
    (hn : q ≠ k) (hs : sz k ≤ sz q) :
    ∃ h l r, q = c (mul u (mul q (mul u k))) (mul (mul y u) k) h l r := by
  exact distinct_columns_larger_returns rfl hf.symm (Ne.symm hn) hs

theorem first_query_absent_for_plain_parameters (u q k : T)
    (hq : PlainRight q) (hk : PlainRight k) :
    (inverse k (mul (mul u (mul q (mul u k))) q)).bind (inverse u) = none := by
  by_cases hn : q = k
  · subst q
    exact first_diagonal_query_absent_for_plain_parameter u k hk
  · cases h1 : inverse k (mul (mul u (mul q (mul u k))) q) with
    | none => rfl
    | some w =>
      cases h2 : inverse u w with
      | none => exact h2
      | some y =>
        have hw := inverse_sound h1
        have hy := inverse_sound h2
        rw [←hy] at hw
        exact False.elim (different_plain_columns_disjoint hq hk hn hw.symm)

end Austin12087Trace
#print axioms Austin12087Trace.distinct_columns_larger_returns
#print axioms Austin12087Trace.different_plain_columns_disjoint
#print axioms Austin12087Trace.first_offdiagonal_larger_k_return
#print axioms Austin12087Trace.first_offdiagonal_larger_q_return
#print axioms Austin12087Trace.first_query_absent_for_plain_parameters

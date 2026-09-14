prelude
import TraceCycle
set_option autoImplicit false

namespace Austin12087Trace
open T

theorem mul_origin_of_right_le {a b : T}
    (h : sz b ≤ sz (mul a b)) : origin (mul a b) = some (a,b) := by
  rcases mul_grows_or_returns a b with hg | ⟨v,k,l,r,hb,hv⟩
  · exact hg.2.2
  · rw [hv,hb] at h; simp only [sz] at h; omega

theorem row_column_collision_return {a z y : T}
    (he : mul a z = mul y a) (hn : z ≠ a) :
    ∃ k l r, z = c a (mul y a) k l r := by
  rcases mul_grows_or_returns a z with hg | ⟨v,k,l,r,hz,hv⟩
  · have hs : sz a ≤ sz (mul y a) := by rw [←he]; omega
    have ho := mul_origin_of_right_le hs
    rw [←he,hg.2.2] at ho
    have hp := Prod.mk.inj (Option.some.inj ho)
    exact False.elim (hn hp.2)
  · exact ⟨k,l,r,by rw [←he,hv]; exact hz⟩

-- A diagonal first-query witness forces a strictly smaller second-query
-- witness. This is one descent branch, not the complete induction.
theorem first_diagonal_descent_trace {u k y : T}
    (hf : mul (mul y u) k = mul (mul u (mul k (mul u k))) k) :
    ∃ a h, sz (mul u k) < sz k ∧ sz u < sz k ∧ sz a < sz k ∧ sz h < sz k ∧
      mul y (mul (mul a (mul (mul u a) h)) (mul a h)) = u ∧
      mul k (mul u k) = c u a h k (mul u k) := by
  let t := mul u k
  let z := mul k t
  let a := mul y u
  have ha : mul u z = a := (right_injective _ _ k hf).symm
  have hn : a ≠ u := mul_ne_right y u
  have hzu : z ≠ u := no_cross_two_cycle u k
  obtain ⟨h,l,r,hz⟩ := row_column_collision_return ha hzu
  change z = c u a h l r at hz
  have hzus : sz u < sz z := by rw [hz]; simp only [sz]; omega
  have hza : sz a < sz z := by rw [hz]; simp only [sz]; omega
  have hzlarge : sz t ≤ sz z := by
    by_cases hc : sz t ≤ sz z
    · exact hc
    apply False.elim
    have hsmall : sz (mul k t) < sz t := by change sz z < sz t; omega
    obtain ⟨v,j,b,c,ht⟩ := (mul_small_iff k t).mp hsmall
    have hv : v = z := by change v = mul k t; rw [ht,mul_code_return]
    subst v
    have htk : sz k ≤ sz t := by rw [ht]; simp only [sz]; omega
    have hot := mul_origin_of_right_le (a:=u) (b:=k) htk
    change origin t = some (u,k) at hot
    conv at hot => lhs; rw [ht,origin]
    obtain ⟨hb,hc⟩ := Prod.mk.inj (Option.some.inj hot)
    subst b; subst c
    have htsem := mul_code_semantics (show mul u k = c k z j u k from ht)
    have hbnd := common_column_inputs_small htsem.1 htsem.2
    omega
  have hoz := mul_origin_of_right_le (a:=k) (b:=t) hzlarge
  change origin z = some (k,t) at hoz
  conv at hoz => lhs; rw [hz,origin]
  obtain ⟨hl,hr⟩ := Prod.mk.inj (Option.some.inj hoz)
  subst l; subst r
  have hzsem := mul_code_semantics (show mul k t = c u a h k t from hz)
  have hk : mul (mul u a) h = k := hzsem.1
  have ht : mul a h = t := hzsem.2
  have hbnd := common_column_inputs_small hk ht
  have htk : sz t < sz k := by
    by_cases hc : sz t < sz k
    · exact hc
    apply False.elim
    have hot := mul_origin_of_right_le (a:=u) (b:=k) (by change sz k ≤ sz t; omega)
    change origin t = some (u,k) at hot
    have hh : sz h ≤ sz (mul a h) := by rw [ht]; omega
    have hot' := mul_origin_of_right_le hh
    rw [ht,hot] at hot'
    have hp := Prod.mk.inj (Option.some.inj hot')
    exact hn hp.1.symm
  have hu : sz u < sz k := by omega
  have haa : sz a < sz k := by omega
  have hh : sz h < sz k := by omega
  obtain ⟨v,j,l,r,hkr⟩ := (mul_small_iff u k).mp htk
  have hvk : sz k < sz (mul a k) := by
    rcases mul_grows_or_returns a k with hg | ⟨v',j',l',r',hkr',_⟩
    · exact hg.2.1
    · have hp := T.c.inj (hkr.symm.trans hkr')
      exact False.elim (hn hp.1.symm)
  have hs : Source12087 u y k := by
    apply source_without_middle_return
    intro q j l r he
    have hb : sz (mul (mul y u) k) < sz (mul u k) := by
      rw [he]; simp only [sz]; omega
    change sz (mul a k) < sz t at hb
    omega
  have hy : mul y (mul (mul a k) t) = u := hs.symm
  exact ⟨a,h,htk,hu,haa,hh,(by rw [hk,ht]; exact hy),hz⟩

theorem first_diagonal_descent {u k y : T}
    (hf : mul (mul y u) k = mul (mul u (mul k (mul u k))) k) :
    ∃ a h, sz (mul u k) < sz k ∧ sz u < sz k ∧ sz a < sz k ∧ sz h < sz k ∧
      mul y (mul (mul a (mul (mul u a) h)) (mul a h)) = u := by
  obtain ⟨a,h,ht,hu,ha,hh,he,_⟩ := first_diagonal_descent_trace hf
  exact ⟨a,h,ht,hu,ha,hh,he⟩

theorem first_diagonal_query_absent_for_plain_parameter (u k : T) (hp : PlainRight k) :
    (inverse k (mul (mul u (mul k (mul u k))) k)).bind (inverse u) = none := by
  cases h1 : inverse k (mul (mul u (mul k (mul u k))) k) with
  | none => rfl
  | some w =>
    cases h2 : inverse u w with
    | none => exact h2
    | some y =>
      have hw := inverse_sound h1
      have hy := inverse_sound h2
      rw [←hy] at hw
      obtain ⟨a,h,htk,_⟩ := first_diagonal_descent hw
      have hg := plain_right_grows u k hp
      exact False.elim (by omega)

theorem first_diagonal_query_absent_of_smaller_second (u k : T)
    (hs : ∀ a h : T, sz u < sz k → sz a < sz k → sz h < sz k →
      inverse (mul (mul a (mul (mul u a) h)) (mul a h)) u = none) :
    (inverse k (mul (mul u (mul k (mul u k))) k)).bind (inverse u) = none := by
  cases h1 : inverse k (mul (mul u (mul k (mul u k))) k) with
  | none => rfl
  | some w =>
    cases h2 : inverse u w with
    | none => exact h2
    | some y =>
      have hw := inverse_sound h1
      have hy := inverse_sound h2
      rw [←hy] at hw
      obtain ⟨a,h,_,hu,ha,hh,he⟩ := first_diagonal_descent hw
      have hi := inverse_complete y (mul (mul a (mul (mul u a) h)) (mul a h))
      rw [he,hs a h hu ha hh] at hi
      cases hi

end Austin12087Trace
#print axioms Austin12087Trace.mul_origin_of_right_le
#print axioms Austin12087Trace.row_column_collision_return
#print axioms Austin12087Trace.first_diagonal_descent_trace
#print axioms Austin12087Trace.first_diagonal_descent
#print axioms Austin12087Trace.first_diagonal_query_absent_for_plain_parameter
#print axioms Austin12087Trace.first_diagonal_query_absent_of_smaller_second

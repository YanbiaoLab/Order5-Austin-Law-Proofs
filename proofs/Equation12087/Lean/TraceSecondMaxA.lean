prelude
import TraceSecondMaxExclusion
set_option autoImplicit false

namespace Austin12087Trace
open T

theorem normal_second_max_a_impossible {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hua : ht u ≤ ht a) (hka : ht k ≤ ht a)
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u) : False := by
  let g := mul u a
  let q := mul g k
  let v := mul a k
  let w := mul a q
  let e := mul w v
  have hnq : NF q := nf_mul (nf_mul hu ha) hk
  have hnv : NF v := nf_mul ha hk
  have hnw : NF w := nf_mul ha hnq
  have hne : NF e := nf_mul hnw hnv
  have hgu := mul_height_upper u a
  change ht g ≤ max (ht u) (ht a) + 1 at hgu
  have hqu := mul_height_upper g k
  change ht q ≤ max (ht g) (ht k) + 1 at hqu
  have hvg := mul_height_growth_of_left_ge (a:=a) (b:=k) hka
  change ht v = max (ht a) (ht k) + 1 at hvg
  have hwg : ht w = max (ht a) (ht q) + 1 := by
    have hp := nf_mul_height_key_gap (a:=a) hnq
    change ht w = max (ht a) (ht q) + 1 ∨ (ht a + 3 ≤ ht q ∧ ht w + 2 ≤ ht q) at hp
    rcases hp with hp | hp
    · exact hp
    · exact False.elim (by omega)
  have how := mul_origin_of_right_height_le (a:=a) (b:=q) (by change ht q ≤ ht w; omega)
  change origin w = some (a,q) at how
  have heg := mul_height_growth_of_left_ge (a:=w) (b:=v) (by omega)
  change ht e = max (ht w) (ht v) + 1 at heg
  have hoe := mul_origin_of_right_height_le (a:=w) (b:=v) (by change ht v ≤ ht e; omega)
  change origin e = some (w,v) at hoe
  obtain ⟨t,_,_,_,hft,hut,_,_⟩ := nf_return_origin_trace hne hoe hf (by omega)
  have hwv : w ≠ v := by
    intro heq
    exact mul_ne_right y u (right_injective _ _ t (hft.trans (heq.trans hut.symm)))
  have how' := (distinct_outputs_height_origin hft hut hwv (by omega)).1
  have hp := Prod.mk.inj (Option.some.inj (how'.symm.trans how))
  rw [hp.2] at hut
  exact nf_no_flip hu ha hk hut

theorem normal_second_query_k_dominates {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u) :
    ht u < ht k ∧ ht a < ht k := by
  have hu' := normal_second_query_height_order hu ha hk hf
  have ha' : ht a < max (ht u) (ht k) := by
    by_cases hh : ht a < max (ht u) (ht k)
    · exact hh
    · exact False.elim (normal_second_max_a_impossible hu ha hk (by omega) (by omega) hf)
  exact ⟨by omega,by omega⟩

end Austin12087Trace
#print axioms Austin12087Trace.normal_second_max_a_impossible
#print axioms Austin12087Trace.normal_second_query_k_dominates

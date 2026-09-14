prelude
import TraceTransposedPairExclusion
set_option autoImplicit false

namespace Austin12087Trace
open T

theorem normal_second_v_factor_no_double_growth {u a k y r : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u)
    (hgr : mul (mul a (mul a (mul (mul u a) k))) r = mul u a)
    (hkr : mul (mul a (mul (mul u a) k)) r = k)
    (hga : ht a ≤ ht (mul u a))
    (hgrgrow : ht r ≤ ht (mul u a)) : False := by
  let w := mul a (mul (mul u a) k)
  have hog := mul_origin_of_right_height_le (a:=u) (b:=a) hga
  have hog' := mul_origin_of_right_height_le (a:=mul a w) (b:=r) (by rw [hgr]; exact hgrgrow)
  rw [hgr] at hog'
  have hp := Prod.mk.inj (Option.some.inj (hog'.symm.trans hog))
  change mul a w = u ∧ r = a at hp
  have hnw : NF w := nf_mul ha (nf_mul (nf_mul hu ha) hk)
  have hwa : mul w a = k := by rw [← hp.2]; exact hkr
  have hbad := normal_transposed_pair_no_preimage (y:=y) ha hnw
  rw [hwa,hp.1] at hbad
  exact hbad hf

theorem normal_second_v_factor_order {u a k y r : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u)
    (hgr : mul (mul a (mul a (mul (mul u a) k))) r = mul u a)
    (hkr : mul (mul a (mul (mul u a) k)) r = k) :
    ht u < max (ht a) (ht r) ∧
      (ht (mul u a) < ht a ∨ ht (mul u a) < ht r) := by
  have hcases : ht (mul u a) < ht a ∨ ht (mul u a) < ht r := by
    by_cases hh : ht (mul u a) < ht a
    · exact Or.inl hh
    · by_cases hh' : ht (mul u a) < ht r
      · exact Or.inr hh'
      · exact False.elim (normal_second_v_factor_no_double_growth hu ha hk hf hgr hkr (by omega) (by omega))
  have hu' : ht u < max (ht a) (ht r) := by
    by_cases hh : ht u < max (ht a) (ht r)
    · exact hh
    · have hg := mul_height_growth_of_left_ge (a:=u) (b:=a) (by omega)
      rcases hcases with hh | hh <;> omega
  exact ⟨hu',hcases⟩

end Austin12087Trace
#print axioms Austin12087Trace.normal_second_v_factor_no_double_growth
#print axioms Austin12087Trace.normal_second_v_factor_order

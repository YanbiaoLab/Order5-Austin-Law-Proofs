prelude
import Init.Data.Option.Lemmas
import Init.Omega
import Init.RCases
import Init.WFTactics
import JudgeTraceSecondTwoColumnsGrow
set_option Elab.async false
/- Checked module: TraceSecondColumnAlternatives -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_second_two_growing_columns_impossible {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u)
    (hqg : ht k ≤ ht (mul (mul u a) k))
    (hvg : ht k ≤ ht (mul a k)) : False := by
  by_cases hm : ht (mul a k) ≤ ht (mul (mul a (mul (mul u a) k)) (mul a k))
  · exact normal_second_two_growing_columns_growing_middle_impossible hu ha hk hf hqg hvg hm
  · exact normal_second_two_growing_columns_returning_middle_impossible hu ha hk hf hqg hvg (by omega)

theorem normal_second_column_alternatives {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u) :
    (ht (mul (mul u a) k) < ht k ∧ ht k < ht (mul a k)) ∨
    (ht (mul a k) < ht k ∧ ht k < ht (mul (mul u a) k)) := by
  by_cases hqr : ht (mul (mul u a) k) < ht k
  · obtain ⟨z,l,r,hkc⟩ := mul_return_of_height_lt hqr
    have hv := mul_height_off_return_key (a:=a) hkc (Ne.symm (mul_ne_right u a))
    exact Or.inl ⟨hqr,by omega⟩
  · have hvr : ht (mul a k) < ht k := by
      by_cases hvr : ht (mul a k) < ht k
      · exact hvr
      · exact False.elim (normal_second_two_growing_columns_impossible hu ha hk hf (by omega) (by omega))
    have hq := mul_height_growth_of_right_le (a:=mul u a) (b:=k) (by omega)
    exact Or.inr ⟨hvr,by omega⟩

theorem normal_second_growing_middle_column_order {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hs : NormalSecondBelow (ht k))
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u)
    (hm : ht (mul a k) ≤ ht (mul (mul a (mul (mul u a) k)) (mul a k))) :
    ht (mul a k) < ht k ∧ ht k < ht (mul (mul u a) k) := by
  rcases normal_second_column_alternatives hu ha hk hf with h | h
  · exact False.elim (normal_second_returning_q_growing_middle_impossible hu ha hk hs hf h.1 hm)
  · exact h

end submission.Austin12087Trace

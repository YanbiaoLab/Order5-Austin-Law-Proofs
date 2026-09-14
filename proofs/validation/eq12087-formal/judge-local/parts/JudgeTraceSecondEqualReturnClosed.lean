prelude
import Init.Data.Option.Lemmas
import Init.Omega
import Init.RCases
import Init.WFTactics
import JudgeTraceSmallFixedPair
set_option Elab.async false
/- Checked module: TraceSecondEqualReturnClosed -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_second_equal_input_returning_q_impossible {u k y : T}
    (hu : NF u) (hk : NF k)
    (hs : NormalSecondBelow (ht k))
    (hf : mul y (mul (mul u (mul (mul u u) k)) (mul u k)) = u)
    (hqr : ht (mul (mul u u) k) < ht k) : False := by
  obtain ⟨s,hns,_,hr,hfixT⟩ := normal_second_equal_input_q_fixed_pair hu hk hs hf hqr
  let b := mul (mul u u) u
  have hnB : NF b := nf_mul (nf_mul hu hu) hu
  have hsq : ht (mul u u) = ht u + 1 := by rw [mul_square]; rfl
  have hbg := mul_height_growth_of_left_ge (a:=mul u u) (b:=u) (by omega)
  change ht b = max (ht (mul u u)) (ht u) + 1 at hbg
  exact normal_small_base_fixed_square_pair_impossible hu hnB hns (by omega) (by omega) hr hfixT

theorem normal_second_returning_q_inputs_distinct {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hs : NormalSecondBelow (ht k))
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u)
    (hqr : ht (mul (mul u a) k) < ht k) : u ≠ a := by
  intro hua
  rw [← hua] at hf hqr
  exact normal_second_equal_input_returning_q_impossible hu hk hs hf hqr

theorem normal_second_equal_input_column_order {u k y : T}
    (hu : NF u) (hk : NF k)
    (hs : NormalSecondBelow (ht k))
    (hf : mul y (mul (mul u (mul (mul u u) k)) (mul u k)) = u) :
    ht (mul u k) < ht k ∧ ht k < ht (mul (mul u u) k) := by
  rcases normal_second_column_alternatives hu hu hk hf with hh | hh
  · exact False.elim (normal_second_equal_input_returning_q_impossible hu hk hs hf hh.1)
  · exact hh

end submission.Austin12087Trace

prelude
import Init.Data.Option.Lemmas
import Init.Omega
import Init.RCases
import Init.WFTactics
import JudgeTraceSecondVGrowingClosed
set_option Elab.async false
/- Checked module: TraceReturningMiddleFrontier -/
set_option autoImplicit false

namespace submission.Austin12087Trace

theorem normal_second_induction_requires_two_returns {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hs : NormalSecondBelow (ht k))
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u) :
    ht (mul a k) < ht k ∧
    ht (mul (mul a (mul (mul u a) k)) (mul a k)) < ht (mul a k) := by
  have hvr := (normal_second_induction_requires_returning_v hu ha hk hs hf).1
  refine ⟨hvr,?_⟩
  by_cases hh : ht (mul (mul a (mul (mul u a) k)) (mul a k)) < ht (mul a k)
  · exact hh
  · exact False.elim (normal_second_v_growing_middle_impossible hu ha hk hs hf hvr (by omega))

def NormalReturningMiddleStep : Prop := ∀ u a k y : T, NF u → NF a → NF k →
  NormalSecondBelow (ht k) →
  mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u →
  ht (mul a k) < ht k →
  ht (mul (mul a (mul (mul u a) k)) (mul a k)) < ht (mul a k) → False

theorem normal_returning_v_of_returning_middle (hm : NormalReturningMiddleStep) :
    NormalReturningVStep := by
  intro u a k y hu ha hk hs hf hvr
  have hr := (normal_second_induction_requires_two_returns hu ha hk hs hf).2
  exact hm u a k y hu ha hk hs hf hvr hr

theorem normal_law_of_returning_middle_step (hm : NormalReturningMiddleStep) :
    ∀ x y z : NormalTree,
      x = normalMul y (normalMul (normalMul (normalMul y x) z) (normalMul x z)) :=
  normal_law_of_returning_v_step (normal_returning_v_of_returning_middle hm)

end submission.Austin12087Trace

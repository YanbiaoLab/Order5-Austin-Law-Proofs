prelude
import Init.Data.Option.Lemmas
import Init.Omega
import Init.RCases
import Init.WFTactics
import JudgeTraceSecondReturningQClosed
set_option Elab.async false
/- Checked module: TraceReturningVInduction -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

def NormalReturningVStep : Prop := ∀ u a k y : T, NF u → NF a → NF k →
  NormalSecondBelow (ht k) →
  mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u →
  ht (mul a k) < ht k → False

theorem normal_second_of_returning_v_step (hv : NormalReturningVStep) :
    NormalSecondCycleAbsent := by
  have main : ∀ n, ∀ u a k : T, NF u → NF a → NF k → ht k = n →
      inverse (mul (mul a (mul (mul u a) k)) (mul a k)) u = none := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro u a k hu ha hk hkn
      have hs : NormalSecondBelow (ht k) := by
        intro u' a' k' hu' ha' hk' _ _ hsmall
        exact ih (ht k') (by omega) u' a' k' hu' ha' hk' rfl
      cases hi : inverse (mul (mul a (mul (mul u a) k)) (mul a k)) u with
      | none => rfl
      | some y =>
        have hf := inverse_sound hi
        have hvr := (normal_second_induction_requires_returning_v hu ha hk hs hf).1
        exact False.elim (hv u a k y hu ha hk hs hf hvr)
  intro u a k hu ha hk
  exact main (ht k) u a k hu ha hk rfl

theorem normal_source_of_returning_v_step (hv : NormalReturningVStep)
    {x y z : T} (hx : NF x) (hy : NF y) (hz : NF z) : Source12087 x y z := by
  exact normal_source_of_second (normal_second_of_returning_v_step hv) hx hy hz

theorem normal_law_of_returning_v_step (hv : NormalReturningVStep) :
    ∀ x y z : NormalTree,
      x = normalMul y (normalMul (normalMul (normalMul y x) z) (normalMul x z)) := by
  exact normal_law_of_second_query_absence (normal_second_of_returning_v_step hv)

end submission.Austin12087Trace

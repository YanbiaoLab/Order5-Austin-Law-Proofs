prelude
import TraceDoubleReturnOffKeyClosed
set_option autoImplicit false

namespace Austin12087Trace

theorem normal_second_induction_requires_equal_return_keys {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hs : NormalSecondBelow (ht k))
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u) :
    a = mul a (mul (mul u a) k) := by
  obtain ⟨hvr,he⟩ := normal_second_induction_requires_two_returns hu ha hk hs hf
  by_cases hh : a = mul a (mul (mul u a) k)
  · exact hh
  · exact False.elim (normal_second_two_return_offkey_impossible hu ha hk hf hvr he hh)

def NormalSameKeyMiddleStep : Prop := ∀ u a k y : T, NF u → NF a → NF k →
  NormalSecondBelow (ht k) →
  mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u →
  ht (mul a k) < ht k →
  ht (mul (mul a (mul (mul u a) k)) (mul a k)) < ht (mul a k) →
  a = mul a (mul (mul u a) k) → False

theorem normal_returning_middle_of_same_key (hm : NormalSameKeyMiddleStep) :
    NormalReturningMiddleStep := by
  intro u a k y hu ha hk hs hf hvr he
  exact hm u a k y hu ha hk hs hf hvr he
    (normal_second_induction_requires_equal_return_keys hu ha hk hs hf)

theorem normal_law_of_same_key_middle_step (hm : NormalSameKeyMiddleStep) :
    ∀ x y z : NormalTree,
      x = normalMul y (normalMul (normalMul (normalMul y x) z) (normalMul x z)) :=
  normal_law_of_returning_middle_step (normal_returning_middle_of_same_key hm)

end Austin12087Trace
#print axioms Austin12087Trace.normal_second_induction_requires_equal_return_keys
#print axioms Austin12087Trace.normal_returning_middle_of_same_key
#print axioms Austin12087Trace.normal_law_of_same_key_middle_step

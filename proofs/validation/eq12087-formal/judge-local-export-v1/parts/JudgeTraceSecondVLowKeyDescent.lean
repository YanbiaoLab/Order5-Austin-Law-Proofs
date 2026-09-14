prelude
import Init.Data.Option.Lemmas
import Init.Omega
import Init.RCases
import Init.WFTactics
import JudgeTraceSecondVLowGrowingMiddle
set_option Elab.async false
/- Checked module: TraceSecondVLowKeyDescent -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_second_v_low_equal_keys_descent_impossible {u a k y s t : T}
    (hu : NF u) (ha : NF a) (hnt : NF t)
    (hs : NormalSecondBelow (ht k))
    (huk : ht u < ht k) (hak : ht a < ht k) (htk : ht t < ht k)
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u)
    (hws : mul (mul a (mul a k)) s = mul a (mul (mul u a) k))
    (hvt : mul (mul (mul a (mul a (mul (mul u a) k))) (mul u a)) t = mul a k)
    (hst : mul (mul u a) t = s)
    (hB : mul (mul a (mul a (mul (mul u a) k))) (mul u a) = a)
    (hD : mul a (mul a k) = a) : False := by
  rw [hB] at hvt
  rw [hD] at hws
  have hquery := hs u a t hu ha hnt huk hak htk
  have hsmall : mul y (mul (mul a (mul (mul u a) t)) (mul a t)) = u := by
    rw [hst,hws,hvt]
    exact hf
  have hi := inverse_complete y (mul (mul a (mul (mul u a) t)) (mul a t))
  rw [hsmall,hquery] at hi
  cases hi

end submission.Austin12087Trace

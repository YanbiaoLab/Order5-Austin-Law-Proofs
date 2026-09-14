prelude
import Init.Data.Option.Lemmas
import Init.Omega
import Init.RCases
import Init.WFTactics
import JudgeTraceOrient
set_option Elab.async false
/- Checked module: TraceCycle -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem no_transposed_code (a b k : T) : mul a b ≠ c b a k a b := by
  intro h
  have hc := mul_code_semantics h
  have hs := common_column_inputs_small hc.1 hc.2
  omega

theorem no_cross_two_cycle (a b : T) : mul b (mul a b) ≠ a := by
  intro h
  have hi := inverse_strict_size (inverse_complete b (mul a b))
  rw [h] at hi
  rcases mul_grows_or_returns a b with hg | ⟨v,k,l,r,hb,hv⟩
  · have hs : sz (mul b (mul a b)) < sz (mul a b) := by rw [h]; exact hg.1
    obtain ⟨v,k,l,r,hv⟩ := (mul_small_iff b (mul a b)).mp hs
    have he : v = a := by rw [hv,mul_code_return] at h; exact h
    subst v
    have ho := hg.2.2
    conv at ho => lhs; rw [hv,origin]
    obtain ⟨hl,hr⟩ := Prod.mk.inj (Option.some.inj ho)
    subst l; subst r
    exact no_transposed_code a b k hv
  · rw [hv,hb] at hi
    simp only [sz] at hi
    omega

theorem cross_two_cycle_inverse_absent (a b : T) :
    inverse (mul a b) a ≠ some b := by
  intro h
  exact no_cross_two_cycle a b (inverse_sound h)

end submission.Austin12087Trace

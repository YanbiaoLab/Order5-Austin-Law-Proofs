prelude
import Init.Data.Option.Lemmas
import Init.Omega
import Init.RCases
import Init.WFTactics
import JudgeTraceGeneralHeadLadder
set_option Elab.async false
/- Checked module: TraceLeftFour -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

private theorem four_cycle_at_max {a x₀ x₁ x₂ x₃ : T}
    (hn₀ : NF x₀) (hn₂ : NF x₂) (hn₃ : NF x₃)
    (h₀ : mul a x₀ = x₁) (h₁ : mul a x₁ = x₂)
    (h₂ : mul a x₂ = x₃) (h₃ : mul a x₃ = x₀)
    (hm₁ : ht x₁ ≤ ht x₀) (hm₂ : ht x₂ ≤ ht x₀) (hm₃ : ht x₃ ≤ ht x₀) : False := by
  have hg₀ := nf_mul_height_key_gap (a:=a) hn₃
  rw [h₃] at hg₀
  have hx₀ : ht x₀ = max (ht a) (ht x₃) + 1 := by rcases hg₀ with hh | hh <;> omega
  have ho₀ := mul_origin_of_right_height_le (a:=a) (b:=x₃) (by rw [h₃]; omega)
  rw [h₃] at ho₀
  have hr₀ := nf_mul_height_key_gap (a:=a) hn₀
  rw [h₀] at hr₀
  have hx₁ : ht x₁ < ht x₀ := by rcases hr₀ with hh | hh <;> omega
  obtain ⟨z,_,_,_,h₂z,h₁z,_,_⟩ := nf_return_origin_trace hn₀ ho₀ h₀ hx₁
  have bounds := common_column_height_bounds h₂z h₁z
  rw [h₁] at h₂z
  have hg₃ := nf_mul_height_key_gap (a:=a) hn₂
  rw [h₂] at hg₃
  have hx₃ : ht x₃ = max (ht a) (ht x₂) + 1 := by rcases hg₃ with hh | hh <;> omega
  have ho₃ := mul_origin_of_right_height_le (a:=a) (b:=x₂) (by rw [h₂]; omega)
  rw [h₂] at ho₃
  have ho₃' := mul_origin_of_right_height_le (a:=x₁) (b:=z) (by rw [h₁z]; omega)
  rw [h₁z] at ho₃'
  have hp := Prod.mk.inj (Option.some.inj (ho₃'.symm.trans ho₃))
  have hs₂ : x₂ = s a := by rw [hp.1,mul_square] at h₁; exact h₁.symm
  rw [hp.2,mul_square,hs₂] at h₂z
  have hbad := congrArg ht h₂z
  simp only [ht] at hbad
  omega

theorem nf_no_left_four_cycle {a x : T} (ha : NF a) (hx : NF x) :
    mul a (mul a (mul a (mul a x))) ≠ x := by
  intro he
  let x₀ := x
  let x₁ := mul a x₀
  let x₂ := mul a x₁
  let x₃ := mul a x₂
  have hn₀ : NF x₀ := hx
  have hn₁ : NF x₁ := nf_mul ha hn₀
  have hn₂ : NF x₂ := nf_mul ha hn₁
  have hn₃ : NF x₃ := nf_mul ha hn₂
  have h₃ : mul a x₃ = x₀ := he
  by_cases hm₀ : ht x₁ ≤ ht x₀ ∧ ht x₂ ≤ ht x₀ ∧ ht x₃ ≤ ht x₀
  · exact four_cycle_at_max hn₀ hn₂ hn₃ rfl rfl rfl h₃ hm₀.1 hm₀.2.1 hm₀.2.2
  by_cases hm₁ : ht x₀ ≤ ht x₁ ∧ ht x₂ ≤ ht x₁ ∧ ht x₃ ≤ ht x₁
  · exact four_cycle_at_max hn₁ hn₃ hn₀ rfl rfl h₃ rfl hm₁.2.1 hm₁.2.2 hm₁.1
  by_cases hm₂ : ht x₀ ≤ ht x₂ ∧ ht x₁ ≤ ht x₂ ∧ ht x₃ ≤ ht x₂
  · exact four_cycle_at_max hn₂ hn₀ hn₁ rfl h₃ rfl rfl hm₂.2.2 hm₂.1 hm₂.2.1
  exact four_cycle_at_max hn₃ hn₁ hn₂ h₃ rfl rfl rfl (by omega) (by omega) (by omega)

end submission.Austin12087Trace

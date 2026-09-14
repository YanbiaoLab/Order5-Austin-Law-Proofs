prelude
import Init.Data.Option.Lemmas
import Init.Omega
import Init.RCases
import Init.WFTactics
import JudgeTraceSecondMaxA
set_option Elab.async false
/- Checked module: TraceNestedRightLadder -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem nested_right_return_ladder_impossible {c d h z k x y A B j r : T}
    (hoc : origin c = some (d,k)) (hod : origin d = some (h,z))
    (hxd : ht x < ht d) (hxz : x ≠ z) (hyc : ht y < ht c)
    (hl : ReturnLadder A B c x y j r) : False := by
  have hdc := (origin_height hoc).1
  have main : ∀ n, ∀ A B j r : T, ht j = n → ReturnLadder A B c x y j r → False := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro A B j r hjn hl
      have hcj := (origin_height hl.2.2.1).1
      have hrj := (origin_height hl.2.2.1).2
      have hcr : ht c < ht r := by
        by_cases hh : ht c < ht r
        · exact hh
        · obtain ⟨t,_,_,_,hct,hrt,_,_⟩ :=
            nf_return_origin_trace hl.1 hl.2.2.1 hl.2.2.2.1 (by omega)
          have hne : c ≠ r := by
            intro heq
            exact mul_ne_right A x (right_injective _ _ t (hct.trans (heq.trans hrt.symm)))
          have hoc' := (distinct_outputs_height_origin hct hrt hne (by omega)).1
          have hp := Prod.mk.inj (Option.some.inj (hoc'.symm.trans hoc))
          have hod' := mul_origin_of_right_height_le (a:=A) (b:=x) (by rw [hp.1]; omega)
          rw [hp.1] at hod'
          have hp' := Prod.mk.inj (Option.some.inj (hod'.symm.trans hod))
          exact False.elim (hxz hp'.2)
      obtain ⟨t,hl₁,_⟩ := return_ladder_step hl (by omega) hcr
      have hnt := (nf_origin hl₁.1 hl₁.2.2.1).2
      have hrg := mul_height_growth_of_right_le (a:=x) (b:=t) (by
        rw [hl₁.2.1]
        exact Nat.le_of_lt (origin_height hl₁.2.2.1).2)
      rw [hl₁.2.1] at hrg
      have hct : ht c + 2 ≤ ht t := by
        have hp := nf_mul_height_key_gap (a:=mul A x) hnt
        rw [hl₁.2.2.2.2] at hp
        rcases hp with hp | hp
        · exact False.elim (by omega)
        · exact hp.2
      obtain ⟨s,hl₂,_⟩ := return_ladder_step hl₁ (by omega) (by omega)
      have htg := mul_height_growth_of_right_le (a:=y) (b:=s) (by
        rw [hl₂.2.1]
        exact Nat.le_of_lt (origin_height hl₂.2.2.1).2)
      rw [hl₂.2.1] at htg
      obtain ⟨t',hl₃,_⟩ := return_ladder_step hl₂ (by omega) (by omega)
      have hst := (origin_height hl₂.2.2.1).2
      have htr := (origin_height hl₁.2.2.1).2
      exact ih (ht s) (by omega) (mul B y) (mul (mul A x) c) s t' rfl hl₃
  exact main (ht j) A B j r rfl hl

end submission.Austin12087Trace

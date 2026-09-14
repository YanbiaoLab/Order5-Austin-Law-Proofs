prelude
import TraceFirstCodeOrder
set_option autoImplicit false

namespace Austin12087Trace
open T

theorem triangle_return_ladder_impossible {u b k w q e j h : T}
    (ha : origin (mul u b) = some (u,b))
    (hw : origin w = some (mul u b,k))
    (hl : ReturnLadder (mul q b) e w u b j h) : False := by
  have hau := (origin_height ha).1
  have hab := (origin_height ha).2
  have hwa := (origin_height hw).1
  have main : ∀ n, ∀ q e j h : T, ht j = n →
      ReturnLadder (mul q b) e w u b j h → False := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro q e j h hjn hl
      have hwj := (origin_height hl.2.2.1).1
      obtain ⟨r,_,hnr,_,hwr,hhr,hrj,_⟩ :=
        nf_return_origin_trace hl.1 hl.2.2.1 hl.2.2.2.1 (by omega)
      have hwh : ht w < ht h := by
        by_cases hh : ht w < ht h
        · exact hh
        · have hne : w ≠ h := by
            intro he
            have hbadu := right_injective _ _ r (hwr.trans (he.trans hhr.symm))
            exact mul_ne_right (mul q b) u hbadu
          have how := (distinct_outputs_height_origin hwr hhr hne (by omega)).1
          have he := Prod.mk.inj (Option.some.inj (how.symm.trans hw))
          have hsame := he.1
          have hao := mul_origin_of_right_height_le (a:=mul q b) (b:=u) (by
            rw [hsame]
            omega)
          rw [hsame] at hao
          have hi := Prod.mk.inj (Option.some.inj (hao.symm.trans ha))
          have hbad : mul q b = b := hi.1.trans hi.2
          exact False.elim (mul_ne_right q b hbad)
      obtain ⟨r',hl₁,_⟩ := return_ladder_step hl (by omega) hwh
      have hjg := mul_height_growth_of_right_le (a:=w) (b:=h) (by
        rw [hl.2.1]
        exact Nat.le_of_lt (origin_height hl.2.2.1).2)
      rw [hl.2.1] at hjg
      -- The code's column is unique, so the first transition uses the same r.
      have hrr : r' = r := by
        have ho₁ := hl₁.2.2.1
        have ho₂ := mul_origin_of_right_height_le (a:=u) (b:=r) (by
          rw [hhr]
          omega)
        rw [hhr] at ho₂
        exact (Prod.mk.inj (Option.some.inj (ho₁.symm.trans ho₂))).2
      subst r'
      have hhg := mul_height_growth_of_right_le (a:=u) (b:=r) (by
        rw [hhr]
        exact Nat.le_of_lt (origin_height hl₁.2.2.1).2)
      rw [hhr] at hhg
      have hwrsmall : ht w < ht r := by
        have hhret := nf_mul_height_key_gap (a:=mul (mul q b) u) hnr
        rw [hl₁.2.2.2.2] at hhret
        rcases hhret with hg | hg <;> omega
      obtain ⟨s,hl₂,_⟩ := return_ladder_step hl₁ (by omega) (by omega)
      have hrg := mul_height_growth_of_right_le (a:=b) (b:=s) (by
        rw [hl₂.2.1]
        exact Nat.le_of_lt (origin_height hl₂.2.2.1).2)
      rw [hl₂.2.1] at hrg
      obtain ⟨t,hl₃,_⟩ := return_ladder_step hl₂ hwrsmall (by omega)
      have hsr := (origin_height hl₂.2.2.1).2
      exact ih (ht s) (by omega) e (mul (mul (mul q b) u) w) s t rfl hl₃
  exact main (ht j) q e j h rfl hl

end Austin12087Trace
#print axioms Austin12087Trace.triangle_return_ladder_impossible

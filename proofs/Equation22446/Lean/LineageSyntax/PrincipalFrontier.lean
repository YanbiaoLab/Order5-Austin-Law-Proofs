prelude
import LineageSyntax.SpecialExclusion
set_option autoImplicit false
set_option Elab.async false

namespace Equation22446Lineage
open Equation22446Guarded

def ZeroRightPrincipalUnique : Prop := ∀ {a u v p q : T}, Normal a → Normal (P u v) →
  Column p a → Image p (P u v) → Column q a → Image q (P u v) → p = q

theorem principal_unique_iff_zero_right : PrincipalUnique ↔ ZeroRightPrincipalUnique := by
  classical
  constructor
  · intro h a u v p q ha hb hc hi hc' hi'
    exact h ha hb hc hi hc' hi'
  · intro h a b p q ha hb hc hi hc' hi'
    by_cases hz : ∃ u v, b = P u v
    · obtain ⟨u,v,hb'⟩ := hz
      subst b
      exact h ha hb hc hi hc' hi'
    · have hn : ∀ u v, b ≠ P u v := by intro u v he; exact hz ⟨u,v,he⟩
      exact (image_nonzero_target hi hn).trans (image_nonzero_target hi' hn).symm

/-- Every remaining principal conflict has a zero-color pair on the right,
unequal left/right inputs, and targets that are not both zero-color pairs. -/
theorem principal_conflict_shape {a b p q : T} (ha : Normal a) (hb : Normal b)
    (hc : Column p a) (hi : Image p b) (hc' : Column q a) (hi' : Image q b)
    (hne : p ≠ q) :
    (∃ u v, b = P u v) ∧ a ≠ b ∧ Normal p ∧ Normal q ∧
      ¬ (∃ u v w z, p = P u v ∧ q = P w z) := by
  classical
  have hright : ∃ u v, b = P u v := by
    by_cases hz : ∃ u v, b = P u v
    · exact hz
    · have hn : ∀ u v, b ≠ P u v := by intro u v he; exact hz ⟨u,v,he⟩
      exact False.elim (hne ((image_nonzero_target hi hn).trans (image_nonzero_target hi' hn).symm))
  have hdiff : a ≠ b := by
    intro he
    rw [he] at hc hc'
    exact hne ((normal_diagonal_target hb hc hi).trans (normal_diagonal_target hb hc' hi').symm)
  have hp := normal_guard_output ha hb (.rectangle (rectangle_target_visible hc hi) hc hi) .zero
  have hq := normal_guard_output ha hb (.rectangle (rectangle_target_visible hc' hi') hc' hi') .zero
  refine ⟨hright,hdiff,hp,hq,?_⟩
  rintro ⟨u,v,w,z,hp',hq'⟩
  rw [hp'] at hc
  rw [hq'] at hc'
  rw [hp',hq'] at hne
  exact hne (column_phase_zero_unique hc hc')

theorem source_from_zero_principal_conditions (hu : ZeroRightPrincipalUnique)
    (hr : ZeroRightRectangleCovered) : ∀ x y z : NormalTree,
      x = multiplication (multiplication y (multiplication x x))
        (multiplication (multiplication x z) z) :=
  source_from_principal_conditions (principal_unique_iff_zero_right.mpr hu)
    (rectangle_coverage_iff_zero_right.mpr hr)

#print axioms principal_unique_iff_zero_right
#print axioms principal_conflict_shape
#print axioms source_from_zero_principal_conditions
end Equation22446Lineage

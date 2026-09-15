prelude
import LineageSyntax.NonzeroRectangles
import LineageSyntax.LineageReversal
set_option autoImplicit false
set_option Elab.async false

namespace Equation22446Lineage
open Equation22446Guarded

/-- A second rectangle return is impossible when the unchanged right
argument is not a zero-color pair. No Normal premise is needed. -/
theorem nonzero_rectangle_double_false {p z u b : T} (hm : Product p z u)
    (hc : Column b u) (hi : Image b z) (hn : ∀ a c, z ≠ P a c) : False := by
  have hb := image_nonzero_target hi hn
  subst b
  cases hm with
  | raw h => exact column_pair_successor_tail_false hc
  | hit hg =>
      cases hg with
      | rectangle hv hk hj =>
          rw [image_nonzero_target hj hn] at hc
          exact column_no_self hc
      | inverseDouble v => exact column_no_self hc
      | @imageReturn v q hj =>
          exact lineage_inverse_column_false (.step (.refl v) hj) hc
      | cycleReturn hv hj hk =>
          have hl := shrinking_inverse_lineage hk (visible_target_smaller hv)
          exact lineage_inverse_column_false hl (by simpa only [cube] using hc)

theorem product_double_image_nonzero_right {p z u b : T}
    (h1 : Product p z u) (h2 : Product u z b) (hn : ∀ a c, z ≠ P a c) : Image p b := by
  cases h2 with
  | raw h => exact product_raw_followup h1
  | hit hg =>
      cases hg with
      | rectangle hv hc hi => exact False.elim (nonzero_rectangle_double_false h1 hc hi hn)
      | inverseDouble v => exact second_inverse_covered h1
      | imageReturn hi => exact second_return_covered h1
      | cycleReturn hv hi hj => exact second_cycle_covered h1 hv hi hj

def ZeroRightRectangleCovered : Prop := ∀ {p v w u b : T}, Normal p → Normal (P v w) →
  Product p (P v w) u → (Part u b ∨ Part (P v w) b) → Column b u → Image b (P v w) → Image p b

theorem rectangle_coverage_iff_zero_right : RectangleReturnCovered ↔ ZeroRightRectangleCovered := by
  classical
  constructor
  · intro h p v w u b hp hz hm hv hc hi
    exact h hp hz hm hv hc hi
  · intro h p z u b hp hz hm hv hc hi
    by_cases hzero : ∃ v w, z = P v w
    · obtain ⟨v,w,hz'⟩ := hzero
      subst z
      exact h hp hz hm hv hc hi
    · exact False.elim (nonzero_rectangle_double_false hm hc hi
        (by intro v w he; exact hzero ⟨v,w,he⟩))

theorem source_from_zero_right_conditions (hu : ZeroRightRectangleUnique)
    (hr : ZeroRightRectangleCovered) : ∀ x y z : NormalTree,
      x = multiplication (multiplication y (multiplication x x))
        (multiplication (multiplication x z) z) :=
  source_from_zero_right_rectangles hu (rectangle_coverage_iff_zero_right.mpr hr)

#print axioms nonzero_rectangle_double_false
#print axioms product_double_image_nonzero_right
#print axioms rectangle_coverage_iff_zero_right
#print axioms source_from_zero_right_conditions
end Equation22446Lineage

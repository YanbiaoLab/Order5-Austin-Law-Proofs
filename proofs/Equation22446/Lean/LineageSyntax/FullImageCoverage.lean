prelude
import LineageSyntax.TriangleInduction
set_option autoImplicit false
set_option Elab.async false

namespace Equation22446Lineage
open Equation22446Guarded

theorem image_next_pair_tail_false {a b : T} (h : Image (S (P a b)) b) : False := by
  have hor := image_small_phase_one_origin h a b rfl (by rw [nodes_S]; exact pair_right .zero a b)
  exact image_triangle_false hor (column_completed hor) h

theorem principal_pair_false {r a b : T} (hc : Column r (P a b)) (hi : Image r b) : False := by
  rw [principal_pair_target hc hi] at hi
  exact image_next_pair_tail_false hi

theorem image_pair_no_guard {p z : T} (hi : Image p z) : ¬ ∃ o, Guard p z o := by
  rintro ⟨o,hg⟩
  cases hg with
  | rectangle hv hc hj => exact image_triangle_false hj hc hi
  | inverseDouble v => exact image_pair_tail_false hi
  | imageReturn hj => exact image_pair_tail_false hi
  | cycleReturn hv hj hk =>
      rw [cycle_target_literal hj hk (visible_target_smaller hv)] at hi
      exact image_pair_tail_false hi

/-- A second rectangle is impossible for every first Product, without
Normal assumptions or any premise on the second rectangle's visibility. -/
theorem rectangle_double_false {p z u b : T} (hm : Product p z u)
    (hc : Column b u) (hi : Image b z) : False := by
  cases hm with
  | raw hn => exact principal_pair_false hc hi
  | hit hg =>
      cases hg with
      | rectangle hv hk hj => exact image_triangle_false hi hc hj
      | inverseDouble v =>
          have hj : Image (S (S v)) (S v) := by simpa only [cube] using (Image.square (S (S v)))
          exact image_triangle_false hi hc hj
      | imageReturn hj =>
          exact column_triangle_false (.inverseImage hi) hc (column_completed hj)
      | cycleReturn hv hj hk =>
          have hl := shrinking_inverse_lineage hk (visible_target_smaller hv)
          have hb : Column (S (S z)) b := .inverseImage (by simpa only [cube] using hi)
          exact column_triangle_false hb hc (.ancestry hl)

theorem rectangle_return_covered : RectangleReturnCovered := by
  intro p z u b hp hz hm hv hc hi
  exact False.elim (rectangle_double_false hm hc hi)

theorem returned_image_covered : ReturnedImageCovered :=
  returned_coverage_of_rectangle rectangle_return_covered

theorem product_double_image {p z u b : T} (h1 : Product p z u) (h2 : Product u z b) :
    Image p b := by
  cases h2 with
  | raw hn => exact product_raw_followup h1
  | hit hg =>
      cases hg with
      | rectangle hv hc hi => exact False.elim (rectangle_double_false h1 hc hi)
      | inverseDouble v => exact second_inverse_covered h1
      | imageReturn hi => exact second_return_covered h1
      | cycleReturn hv hi hj => exact second_cycle_covered h1 hv hi hj

theorem chosen_double_image_unconditional (p z : T) : Image p (chosen (chosen p z) z) :=
  product_double_image (chosen_product p z) (chosen_product (chosen p z) z)

theorem source_with_principal_unique (hu : PrincipalUnique) : ∀ x y z : NormalTree,
    x = multiplication (multiplication y (multiplication x x))
      (multiplication (multiplication x z) z) :=
  source_from_principal_conditions hu rectangle_return_covered

/-- Explicitly conditional on the still-open NEW principal uniqueness. -/
theorem infinite_model_with_principal_unique (hu : PrincipalUnique) :
    (∀ x y z : NormalTree,
      x = multiplication (multiplication y (multiplication x x))
        (multiplication (multiplication x z) z)) ∧
    (∀ {a b : Nat}, normalTower a = normalTower b → a = b) :=
  ⟨source_with_principal_unique hu,normalTower_injective⟩

theorem source_with_zero_right_principal_unique (hu : ZeroRightPrincipalUnique) :
    ∀ x y z : NormalTree,
      x = multiplication (multiplication y (multiplication x x))
        (multiplication (multiplication x z) z) :=
  source_with_principal_unique (principal_unique_iff_zero_right.mpr hu)

#print axioms image_next_pair_tail_false
#print axioms principal_pair_false
#print axioms image_pair_no_guard
#print axioms rectangle_double_false
#print axioms rectangle_return_covered
#print axioms returned_image_covered
#print axioms product_double_image
#print axioms chosen_double_image_unconditional
#print axioms source_with_principal_unique
#print axioms infinite_model_with_principal_unique
#print axioms source_with_zero_right_principal_unique
end Equation22446Lineage

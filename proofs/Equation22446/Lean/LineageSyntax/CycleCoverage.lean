prelude
import LineageSyntax.InverseCycles
import LineageSyntax.ImageObstructions
set_option autoImplicit false
set_option Elab.async false

namespace Equation22446Lineage
open Equation22446Guarded

/-- Every cycle return at the SECOND multiplication is covered, for every
first Product trace. Normality is not needed. -/
theorem second_cycle_covered {p z u r : T} (hm : Product p z u)
    (hv : Part u r ∨ Part z r) (hi : Image r (P u z))
    (hj : Image (P u z) (S r)) : Image p (S (S r)) := by
  have hs := visible_target_smaller hv
  obtain ⟨a,b,hu⟩ := cycle_left_phase_zero hi hj hs
  obtain ⟨w,t,hr⟩ := cycle_target_phase_two hi hj hs
  generalize hq : P u z = q at hi
  cases hi with
  | square r => rw [hr] at hq; cases hq
  | literal r v =>
      have he := (T.p.inj hq).2.1
      have hz := (T.p.inj hq).2.2
      rw [←hz] at he
      rw [←product_pair_tail_root hm r he]
      exact .square p
  | transport hc ht =>
      rw [←(T.p.inj hq).2.1,←(T.p.inj hq).2.2] at ht
      rw [←(T.p.inj hq).2.1,hr,hu] at hc
      have he := column_zero_to_two hc
      have hr' : r = S (S u) := by rw [hu,he]; exact hr
      rw [hr',cube] at hj
      exact False.elim (image_pair_flip_false ht hj)
  | inverseFollowup r => cases hr
  | returnFollowup ht => cases hr
  | cycleFollowup hs ht hk => cases hr

theorem cycle_return_covered : CycleReturnCovered := by
  intro p z u r hp hz hm hv hi hj
  exact second_cycle_covered hm hv hi hj

theorem returned_coverage_of_rectangle (hr : RectangleReturnCovered) : ReturnedImageCovered :=
  returned_coverage_of_rectangle_cycle hr cycle_return_covered

theorem returned_coverage_iff_rectangle : ReturnedImageCovered ↔ RectangleReturnCovered := by
  constructor
  · intro hd
    exact (returned_coverage_iff_rectangle_cycle.mp hd).1
  · exact returned_coverage_of_rectangle

theorem source_from_rectangle_obligations (hu : GuardUnique) (hr : RectangleReturnCovered) :
    ∀ x y z : NormalTree,
      x = multiplication (multiplication y (multiplication x x))
        (multiplication (multiplication x z) z) :=
  normal_tree_source hu (returned_coverage_of_rectangle hr)

#print axioms second_cycle_covered
#print axioms cycle_return_covered
#print axioms returned_coverage_of_rectangle
#print axioms returned_coverage_iff_rectangle
#print axioms source_from_rectangle_obligations
end Equation22446Lineage

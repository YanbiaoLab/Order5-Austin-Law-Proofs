prelude
import Init.Classical
import Init.Data.Nat.Lemmas
import Init.RCases
import ExportLineageSyntaxRightBounds
set_option Elab.async false
set_option autoImplicit false
set_option Elab.async false

namespace submission.Equation22446Lineage
open submission.Equation22446Guarded

theorem visible_target_smaller {a b p : T} (h : Part a p ∨ Part b p) :
    nodes p < nodes (P a b) := by
  rcases h with h | h
  · exact Nat.lt_of_le_of_lt (part_nodes h) (pair_left .zero _ _)
  · exact Nat.lt_of_le_of_lt (part_nodes h) (pair_right .zero _ _)

theorem cycle_raw_followup {a z p : T} (hp : Part a p ∨ Part z p)
    (hi : Image p (P a z)) (hj : Image (P a z) (S p)) :
    Image a (P (S (S p)) z) := by
  have hs := visible_target_smaller hp
  obtain ⟨u,v,ha⟩ := cycle_left_phase_zero hi hj hs
  obtain ⟨w,t,hp⟩ := cycle_target_phase_two hi hj hs
  subst a p
  rw [cube] at hj ⊢
  exact .cycleFollowup hs hi hj

 

theorem guard_raw_followup {p z u : T} (h : Guard p z u) : Image p (P u z) := by
  cases h with
  | rectangle hp hc hi => exact .transport hc hi
  | inverseDouble p => exact .inverseFollowup p
  | imageReturn hi => exact .returnFollowup hi
  | cycleReturn hp hi hj => exact cycle_raw_followup hp hi hj

theorem product_raw_followup {p z u : T} (h : Product p z u) : Image p (P u z) := by
  cases h with
  | raw hn => exact .literal p z
  | hit hg => exact guard_raw_followup hg

end submission.Equation22446Lineage

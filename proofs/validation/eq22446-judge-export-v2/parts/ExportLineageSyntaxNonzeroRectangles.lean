prelude
import Init.Classical
import Init.Data.Nat.Lemmas
import Init.RCases
import ExportLineageSyntaxRightSquareObstructions
set_option Elab.async false
set_option autoImplicit false
set_option Elab.async false

namespace submission.Equation22446Lineage
open submission.Equation22446Guarded

theorem rectangle_nonzero_right_unique {p a b o : T} (hc : Column p a) (hi : Image p b)
    (hg : Guard a b o) (hn : ∀ u v, b ≠ P u v) : p = o := by
  have hp := image_nonzero_target hi hn
  subst p
  cases hg with
  | rectangle hv hc' hi' => exact (image_nonzero_target hi' hn).symm
  | inverseDouble v => rfl
  | imageReturn ht => exact False.elim (column_pair_successor_tail_false hc)
  | cycleReturn hv ht hk =>
      have hs := visible_target_smaller hv
      rcases cycle_target_alternatives ht hk hs with ha | ⟨hr,hj⟩
      · rw [ha] at hc
        exact False.elim (column_pair_successor_tail_false hc)
      · obtain ⟨u,v,ha⟩ := cycle_left_phase_zero ht hk hs
        rw [ha] at hc hj
        have hi' : Image (P u v) (S (S (S b))) := by simpa only [cube] using hj
        exact False.elim (raw_column_square_image_false hc hi')

theorem guard_nonzero_right_unique {a b u v : T} (hn : ∀ x y, b ≠ P x y)
    (hu : Guard a b u) (hv : Guard a b v) : u = v := by
  rcases guard_rectangle_or_special hu with ⟨hp,hc,hi⟩ | hu
  · exact rectangle_nonzero_right_unique hc hi hv hn
  · rcases guard_rectangle_or_special hv with ⟨hp,hc,hi⟩ | hv
    · exact (rectangle_nonzero_right_unique hc hi (special_guard hu) hn).symm
    · exact special_unique hu hv

def ZeroRightRectangleUnique : Prop := ∀ {p a u v o : T}, Normal a → Normal (P u v) →
  Column p a → Image p (P u v) → Guard a (P u v) o → p = o

theorem rectangle_unique_iff_zero_right : RectangleGuardUnique ↔ ZeroRightRectangleUnique := by
  classical
  constructor
  · intro h p a u v o ha hb hc hi hg
    exact h ha hb hc hi hg
  · intro h p a b o ha hb hc hi hg
    by_cases hz : ∃ u v, b = P u v
    · obtain ⟨u,v,hb'⟩ := hz
      subst b
      exact h ha hb hc hi hg
    · exact rectangle_nonzero_right_unique hc hi hg (by intro u v he; exact hz ⟨u,v,he⟩)

theorem source_from_zero_right_rectangles (hu : ZeroRightRectangleUnique)
    (hr : RectangleReturnCovered) : ∀ x y z : NormalTree,
      x = multiplication (multiplication y (multiplication x x))
        (multiplication (multiplication x z) z) :=
  source_from_rectangle_conditions (rectangle_unique_iff_zero_right.mpr hu) hr

end submission.Equation22446Lineage

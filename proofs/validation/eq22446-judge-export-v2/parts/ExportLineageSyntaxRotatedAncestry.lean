prelude
import Init.Classical
import Init.Data.Nat.Lemmas
import Init.RCases
import ExportLineageSyntaxPrincipalFrontier
set_option Elab.async false
set_option autoImplicit false
set_option Elab.async false

namespace submission.Equation22446Lineage
open submission.Equation22446Guarded

theorem lineage_inverse_image_prev_false {p r : T} (hl : Lineage p r)
    (hi : Image (S (S r)) (S (S p))) : False := by
  cases hl with
  | refl => exact image_no_self hi
  | @step p a b hl hj =>
      simp only [cube] at hi
      rcases phase_two_or_square_nonzero p with ⟨u,v,hp⟩ | hn
      · have he := image_nonzero_output hi (by intro x y h; rw [hp] at h; cases h)
        rw [hp] at he
        cases he
      · have ha : ∀ x y, p ≠ S (S (P x y)) := by
          intro x y hp
          apply hn x y
          rw [hp,cube]
        have hs := image_ancestor_bound hi p a b rfl ha hl
        rw [nodes_S,nodes_S] at hs
        exact Nat.lt_irrefl _ hs

theorem column_square_image_false {p a : T} (hc : Column p a)
    (hi : Image a (S (S p))) : False := by
  cases hc with
  | ancestry hl => exact lineage_inverse_image_prev_false hl hi
  | literal p y =>
      have hs := image_right_child hi .zero y (S p) (by intro h; cases h) rfl
      simp only [nodes_S] at hs
      exact Nat.lt_irrefl _ hs
  | inverseImage hj => exact image_no_successive_outputs hj hi

theorem column_self_image_false {p a : T} (hc : Column p a)
    (hi : Image a p) : False := by
  cases hc with
  | ancestry hl => exact lineage_inverse_image_false hl hi
  | literal p y =>
      have hs := image_right_child hi .zero y (S p) (by intro h; cases h) rfl
      rw [nodes_S] at hs
      exact Nat.lt_irrefl _ hs
  | inverseImage hj => exact image_no_successive_outputs hi hj

theorem shared_column_phase_zero_bound {u v q a : T}
    (hp : Column (P u v) a) (hq : Column q a) : nodes (P u v) ≤ nodes q := by
  cases hp with
  | ancestry hl =>
      cases hl with
      | refl => simpa only [nodes_S] using (column_phase_two_bound hq u v rfl)
      | @step p x y hl hi =>
          simp only [cube] at hq
          exact column_ancestor_bound hq (P u v) x y rfl (by intro w z h; cases h) hl
  | literal p y =>
      have hs := column_right_child hq .zero y (S (P u v)) (by intro h; cases h) rfl
      simpa only [nodes_S] using hs
  | inverseImage hi =>
      have ha := congrArg S (image_nonzero_output hi (by intro x y h; cases h))
      rw [cube] at ha
      rw [←ha] at hq
      simpa only [nodes_S] using (column_phase_two_bound hq u v rfl)

end submission.Equation22446Lineage

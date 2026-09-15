prelude
import Init.Classical
import Init.Data.Nat.Lemmas
import Init.RCases
import ExportLineageSyntaxCycleCoverage
set_option Elab.async false
set_option autoImplicit false
set_option Elab.async false

namespace submission.Equation22446Lineage
open submission.Equation22446Guarded

theorem lineage_nonincreasing_eq {p q : T} (h : Lineage p q)
    (hs : nodes q ≤ nodes p) : p = q := by
  cases h with
  | refl => rfl
  | @step p a b hl hi =>
      have ht := lineage_nodes hl
      have hb := pair_left .two a b
      exact False.elim (Nat.not_lt_of_ge hs (Nat.lt_of_le_of_lt ht hb))

theorem image_phase_two_strict {p q : T} (h : Image p q)
    (hp : ∃ a b, p = S (S (P a b))) (hq : ∃ u v, q = P u v) : nodes p < nodes q := by
  obtain ⟨a,b,hp⟩ := hp
  obtain ⟨u,v,hq⟩ := hq
  rw [hq]
  exact Nat.lt_of_le_of_lt (image_phase_two_output_left h a b u v hp hq) (pair_left .zero u v)

theorem image_no_swapped_successors {p a : T} (hp : Image p (S a))
    (ha : Image a (S p)) : False := by
  have ordinary {p a : T} (hp : Image p (S a)) (ha : Image a (S p))
      (hn : ∀ u v, S a ≠ P u v) : False := by
    have he := congrArg S (image_nonzero_output hp hn)
    rw [cube] at he
    rw [←he,cube] at ha
    exact image_no_self ha
  rcases phase_two_or_square_nonzero p with ⟨u,v,hp'⟩ | hn
  · rcases phase_two_or_square_nonzero a with ⟨r,s,ha'⟩ | hn
    · have hbig := image_phase_two_strict hp ⟨u,v,hp'⟩ ⟨r,s,by rw [ha']; rfl⟩
      have hsmall := image_phase_two_bound ha r s ha'
      rw [nodes_S] at hbig hsmall
      exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hbig hsmall)
    · exact ordinary hp ha hn
  · exact ordinary ha hp hn

theorem image_lineage_false {p q : T} (hi : Image p q) (hl : Lineage p q) : False := by
  cases hl with
  | refl => exact image_no_self hi
  | @step p a b hl hj =>
      have he := image_nonzero_output hi (by intro u v h; cases h)
      have hs := congrArg nodes he
      rw [nodes_S,nodes_S,nodes_S,nodes_S] at hs
      have ht := lineage_nodes hl
      have hb := pair_left .zero a b
      change nodes a < nodes (P a b) at hb
      rw [hs] at hb
      exact Nat.not_lt_of_ge ht hb

theorem column_image_next_false {p a : T} (hc : Column p a) (hi : Image p (S a)) : False := by
  cases hc with
  | ancestry hl => rw [cube] at hi; exact image_lineage_false hi hl
  | literal p y =>
      have he := image_nonzero_output hi (by intro u v h; cases h)
      have hs := congrArg nodes he
      rw [nodes_S,nodes_S,nodes_S] at hs
      have hb := pair_right .zero y (S p)
      change nodes (S p) < nodes (P y (S p)) at hb
      rw [nodes_S,hs] at hb
      exact Nat.lt_irrefl _ hb
  | inverseImage hj => exact image_no_swapped_successors hi hj

theorem strict_cycle_square_right_false {p r : T} (hi : Image r (P p (S p)))
    (hj : Image (P p (S p)) (S r)) (hs : nodes r < nodes (P p (S p))) : False := by
  have hl := shrinking_inverse_lineage hj hs
  rw [cube] at hl
  obtain ⟨a,b,hr⟩ := cycle_target_phase_two hi hj hs
  obtain ⟨u,v,hp⟩ := cycle_left_phase_zero hi hj hs
  have hb := image_phase_two_output_left hi a b p (S p) hr rfl
  have he := lineage_nonincreasing_eq hl hb
  rw [hp,hr] at he
  cases he

end submission.Equation22446Lineage

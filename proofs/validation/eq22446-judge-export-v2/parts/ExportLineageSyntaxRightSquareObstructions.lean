prelude
import Init.Classical
import Init.Data.Nat.Lemmas
import Init.RCases
import ExportLineageSyntaxSpecialUniqueness
set_option Elab.async false
set_option autoImplicit false
set_option Elab.async false

namespace submission.Equation22446Lineage
open submission.Equation22446Guarded

theorem image_no_successive_outputs {p q : T} (hi : Image p q) (hj : Image p (S q)) : False := by
  classical
  by_cases hq : ∃ a b, q = P a b
  · obtain ⟨a,b,hq⟩ := hq
    have he := image_nonzero_output hj (by intro u v h; rw [hq] at h; cases h)
    rw [S_injective he] at hi
    exact image_no_successor hi
  · have he := image_nonzero_output hi (by intro a b h; exact hq ⟨a,b,h⟩)
    rw [he,cube] at hj
    exact image_no_self hj

theorem column_pair_successor_tail_false {a b : T} (hc : Column (S b) (P a b)) : False := by
  generalize he : P a b = t at hc
  cases hc with
  | ancestry hl =>
      have ha := congrArg S he
      rw [cube] at ha
      have hb := lineage_non_phase_two hl (by intro u v h; rw [←ha] at h; cases h)
      have eq := S_injective (hb.trans ha.symm)
      have hn := congrArg nodes eq
      exact Nat.ne_of_lt (pair_right .zero a b) hn
  | literal p y =>
      exact SS_ne b (T.p.inj he).2.2.symm
  | inverseImage hi =>
      rw [←he] at hi
      have hs := image_right_child hi .zero a b (by intro h; cases h) rfl
      rw [nodes_S,nodes_S] at hs
      exact Nat.lt_irrefl _ hs

theorem raw_column_square_image_false {p a b : T} (hc : Column p (P a b))
    (hi : Image (P a b) (S (S p))) : False := by
  generalize he : P a b = t at hc
  cases hc with
  | ancestry hl =>
      have ha := congrArg S he
      rw [cube] at ha
      have hp := lineage_non_phase_two hl (by intro u v h; rw [←ha] at h; cases h)
      rw [hp,←ha,cube] at hi
      exact image_no_self hi
  | literal p y =>
      have hb := (T.p.inj he).2.2
      have hs := image_right_child hi .zero a b (by intro h; cases h) rfl
      rw [hb,nodes_S,nodes_S,nodes_S] at hs
      exact Nat.lt_irrefl _ hs
  | inverseImage hj =>
      rw [←he] at hj
      exact image_no_successive_outputs hj hi

theorem image_nonzero_target {p b : T} (hi : Image p b)
    (hn : ∀ u v, b ≠ P u v) : p = S b := by
  have he := congrArg S (image_nonzero_output hi hn)
  simpa only [cube] using he.symm

end submission.Equation22446Lineage

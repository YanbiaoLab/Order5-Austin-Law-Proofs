prelude
import Init.Classical
import Init.Data.Nat.Lemmas
import Init.RCases
import ExportLineageSyntaxOneTwoRootBounds
set_option Elab.async false
set_option autoImplicit false
set_option Elab.async false

namespace submission.Equation22446Lineage
open submission.Equation22446Guarded

theorem column_pair_cases {p x y : T} (hc : Column p (P x y)) :
    p = S (P x y) ∨ y = S p ∨ Image (P x y) (S p) := by
  generalize he : P x y = a at hc
  cases hc with
  | ancestry hl =>
      have hr := congrArg S he
      rw [cube] at hr
      have hp := lineage_non_phase_two hl (by intro u v h; rw [←hr] at h; cases h)
      exact Or.inl (by simpa only [cube] using hp)
  | literal p z => exact Or.inr (Or.inl (T.p.inj he).2.2)
  | inverseImage hi => exact Or.inr (Or.inr hi)

theorem column_pair_non_two_cases {p x y : T} (hc : Column p (P x y))
    (hn : ∀ u v, S p ≠ P u v) : p = S (P x y) ∨ y = S p := by
  rcases column_pair_cases hc with hp | hy | hi
  · exact Or.inl hp
  · exact Or.inr hy
  · exact Or.inl (S_injective (image_nonzero_output hi hn))

theorem column_zero_pair_literal {u v x y : T} (hc : Column (P u v) (P x y)) :
    y = S (P u v) := by
  rcases column_pair_non_two_cases hc (by intro a b h; cases h) with hp | hy
  · cases hp
  · exact hy

theorem lineage_pair_without_image_root {r h z : T} (hn : ¬ Image h z)
    (hl : Lineage r (S (S (P h z)))) : r = S (S (P h z)) := by
  cases hl with
  | refl => rfl
  | step hl hi => exact False.elim (hn hi)

theorem column_zero_pair_rotated_chain_false {u h z x y : T}
    (hn : ¬ Image h z) (hs : nodes u < nodes (P h z))
    (hc : Column u (S (P x y))) (hd : Column (P h z) (P x y)) : False := by
  have hy := column_zero_pair_literal hd
  have hqa : nodes (P h z) < nodes (P x y) := by
    have hb := pair_right .zero x y
    change nodes y < nodes (P x y) at hb
    simpa only [hy,nodes_S] using hb
  have hua : nodes u < nodes (S (P x y)) := by rw [nodes_S]; exact Nat.lt_trans hs hqa
  have hi := column_small_phase_one_origin hc x y rfl hua
  rw [hy] at hi
  have hx := image_nonzero_target hi (by intro a b h; cases h)
  obtain ⟨r,hr,hu⟩ := column_small_phase_one_common_root hc x y rfl hua
  rw [hx] at hr
  have he := lineage_pair_without_image_root hn hr
  have hb := lineage_nodes hu
  rw [he,nodes_S,nodes_S] at hb
  exact Nat.not_lt_of_ge hb hs

theorem canonical_square_transport_target {u v x y : T}
    (hc : Column u (S (P x y))) (hd : Column (S (P u v)) (P x y)) :
    S (P u v) = S (P x y) := by
  rcases column_pair_non_two_cases hd (by intro a b h; cases h) with hp | hy
  · exact hp
  · have hb := pair_right .zero x y
    change nodes y < nodes (P x y) at hb
    have hba : nodes (P u v) < nodes (P x y) := by simpa only [hy,nodes_S] using hb
    have hua : nodes u < nodes (S (P x y)) := by
      rw [nodes_S]
      exact Nat.lt_trans (pair_left .zero u v) hba
    have hi := column_small_phase_one_origin hc x y rfl hua
    rw [hy] at hi
    have hx := image_nonzero_target hi (by intro a b h; cases h)
    simp only [cube] at hx
    rw [hx,hy] at hc
    have hs := column_ancestor_bound hc (P u v) (P u v) (S (S (P u v))) rfl
      (by intro a b h; cases h) (.refl _)
    exact False.elim (Nat.not_lt_of_ge hs (pair_left .zero u v))

end submission.Equation22446Lineage

prelude
import Init.Classical
import Init.Data.Nat.Lemmas
import Init.RCases
import ExportLineageSyntaxColumnChains
set_option Elab.async false
set_option autoImplicit false
set_option Elab.async false

namespace submission.Equation22446Lineage
open submission.Equation22446Guarded

theorem image_phase_one_nongrowing {p q : T} (h : Image p q) :
    ∀ u v, p = S (P u v) → nodes q ≤ nodes p →
      q = S (S p) ∨ (Image u v ∧ ∃ r, Lineage r u ∧ Lineage r (S (S q))) := by
  intro u v hp hs
  cases h with
  | square p => exact Or.inl rfl
  | literal p z =>
      exact False.elim (Nat.not_lt_of_ge hs
        (Nat.lt_trans (pair_left .zero _ _) (pair_left .zero _ _)))
  | transport hc hi =>
      have ht := Nat.lt_of_lt_of_le (pair_left .zero _ _) hs
      have huv := column_small_phase_one_origin hc u v hp ht
      obtain ⟨r,hr,hl⟩ := column_small_phase_one_common_root hc u v hp ht
      exact Or.inr ⟨huv,r,hr,.step hl hi⟩
  | inverseFollowup p => cases hp
  | returnFollowup hi => cases hp
  | cycleFollowup ht hi hj => cases hp

theorem column_joined_lineages_false {u p q r : T} (hc : Column u p)
    (hu : Lineage u q) (hr : Lineage r q) (hp : Lineage r p) : False := by
  rcases lineage_common_comparable hu hr with h | h
  · exact column_lineage_forward_false hc (lineage_trans h hp)
  · exact column_common_root_false hc r h hp

 

theorem column_chain_ancestral_false {u p q : T} (hl : Lineage u q)
    (hc : Column u p) (hd : Column p (S (S q))) : False := by
  have hu := column_triangle_base_phase_two hc hd (.ancestry hl)
  have hq := lineage_phase_two_preserved hl hu
  generalize he : S (S q) = a at hd
  cases hd with
  | ancestry hm =>
      have hqr := S_injective (S_injective he)
      rw [←hqr] at hm
      exact common_lineage_column_false hl hm hc
  | literal p y =>
      have hq' := congrArg S he
      rw [cube] at hq'
      obtain ⟨x,z,hq⟩ := hq
      rw [hq] at hq'
      cases hq'
  | inverseImage hi =>
      rw [←he] at hi
      rcases phase_two_or_square_nonzero p with ⟨x,y,hp⟩ | hn
      · obtain ⟨v,w,hq⟩ := hq
        have hs := column_phase_two_bound hc x y hp
        have ht := lineage_nodes hl
        have hb : nodes (S p) ≤ nodes (S (S q)) := by
          simp only [nodes_S]
          exact Nat.le_trans hs ht
        have hn := image_phase_one_nongrowing hi v w (by rw [hq]; rfl) hb
        rcases hn with heq | ⟨hvw,r,hr,hp'⟩
        · have hpq := S_injective (by simpa only [cube] using heq)
          rw [hpq] at hc
          exact column_lineage_forward_false hc hl
        · have hrq : Lineage r q := by rw [hq]; exact .step hr hvw
          simp only [cube] at hp'
          exact column_joined_lineages_false hc hl hrq hp'
      · have hpq : p = q := S_injective (by simpa only [cube] using (image_nonzero_output hi hn))
        rw [hpq] at hc
        exact column_lineage_forward_false hc hl

end submission.Equation22446Lineage

prelude
import LineageSyntax.ColumnLineageChains
set_option autoImplicit false
set_option Elab.async false

namespace Equation22446Lineage
open Equation22446Guarded

theorem rotated_column_canonical_target {q x y : T} (ha : Normal (P x y))
    (hc : Column (S (S (P x y))) q) (hd : Column q (P x y)) : q = S (P x y) := by
  cases hc with
  | @ancestry u r hl =>
      obtain ⟨v,w,hr⟩ := lineage_phase_two_preserved hl ⟨x,y,rfl⟩
      have hs := column_non_two_base_bound hd (by intro a b h; rw [cube,hr] at h; cases h)
      have he := lineage_nonincreasing_eq hl (by simpa only [nodes_S] using hs)
      rw [←he,cube]
  | literal u z =>
      have hs := column_non_two_base_bound hd (by intro a b h; cases h)
      have hb := pair_right .zero z (S (S (S (P x y))))
      simp only [cube] at hs hb
      exact False.elim (Nat.not_lt_of_ge hs hb)
  | inverseImage hi =>
      simp only [cube] at hi
      exact normal_diagonal_target ha hd hi

theorem rotated_column_completed_target {u q x y : T}
    (hl : Lineage u x) (hxy : Image x y) (hc : Column u q) (hd : Column q (P x y)) :
    q = S (P x y) := by
  rcases column_pair_cases hd with hq | hy | hi
  · exact hq
  · rw [hy] at hxy
    exact False.elim (column_chain_lineage_false hl hc (.inverseImage hxy))
  · rcases phase_two_or_square_nonzero q with ⟨v,w,hq⟩ | hn
    · have hqu := column_phase_two_bound hc v w hq
      have hux := lineage_nodes hl
      have hs : nodes q < nodes (P x y) :=
        Nat.lt_of_le_of_lt (Nat.le_trans hqu hux) (pair_left .zero x y)
      have hm := shrinking_inverse_lineage hi hs
      have hyq := lineage_nodes hm
      simp only [nodes_S] at hyq
      rcases phase_two_or_square_nonzero x with ⟨a,b,hx⟩ | hn
      · have hxy' := image_phase_two_bound hxy a b hx
        have he := lineage_nonincreasing_eq hl (Nat.le_trans hxy' (Nat.le_trans hyq hqu))
        rw [he] at hc
        have ht := image_phase_two_strict (column_two_value_inverse hc ⟨v,w,hq⟩)
          ⟨v,w,hq⟩ ⟨a,b,by rw [hx]; rfl⟩
        simp only [nodes_S] at ht
        exact False.elim (Nat.not_lt_of_ge (Nat.le_trans hxy' hyq) ht)
      · have he := lineage_non_phase_two hl (by
          intro a b hx
          exact hn a b (by rw [hx,cube]))
        rw [he] at hc
        rcases column_phase_two_base_shape hc ⟨v,w,hq⟩ with ⟨a,b,hx⟩ | ⟨a,b,hx⟩
        · have hc' : Column (P a b) (S (S (P v w))) := by
            have ht := hc
            rw [hx,hq] at ht
            exact ht
          have ht := column_zero_to_two hc'
          have hqx : q = S (S x) := by rw [hq,hx,ht]; rfl
          rw [hqx,cube] at hi
          exact False.elim (image_pair_flip_false hxy hi)
        · exact False.elim (hn a b (by rw [hx,cube]))
    · exact S_injective (image_nonzero_output hi hn)

theorem rotated_column_inverse_ancestry_target {u r x y : T}
    (hu : ∃ a b, u = S (S (P a b))) (hl : Lineage u r)
    (hd : Column (S (S r)) (P x y)) (hi : Image (S (P x y)) (S u)) :
    S (S r) = S (P x y) := by
  obtain ⟨a,b,hr⟩ := lineage_phase_two_preserved hl hu
  have hn : ∀ v w, S (S (S r)) ≠ P v w := by
    intro v w h
    rw [cube,hr] at h
    cases h
  rcases column_pair_non_two_cases hd hn with he | hy
  · exact he
  · simp only [cube] at hy
    have hua : nodes (S u) < nodes (S (P x y)) := by
      simp only [nodes_S]
      rw [hy]
      have hb := pair_right .zero x y
      change nodes y < nodes (P x y) at hb
      rw [hy] at hb
      exact Nat.lt_of_le_of_lt (lineage_nodes hl) hb
    have hxy := image_small_phase_one_origin hi x y rfl hua
    rw [hy] at hxy
    have hx := image_nonzero_target hxy (by intro v w h; rw [hr] at h; cases h)
    have hnx : ∀ v w, x ≠ S (S (P v w)) := by
      intro v w h
      rw [hx,hr,cube] at h
      cases h
    have hb := image_ancestor_bound hi x x y rfl hnx (.refl _)
    rw [hx,nodes_S,nodes_S] at hb
    exact False.elim (Nat.not_lt_of_ge (lineage_nodes hl) hb)

theorem rotated_column_inverse_literal_false {u z x y : T}
    (hd : Column (P z (S u)) (P x y)) (hi : Image (S (P x y)) (S u)) : False := by
  have hy := column_zero_pair_literal hd
  have hua : nodes (S u) < nodes (S (P x y)) := by
    simp only [nodes_S]
    rw [hy]
    have hb := pair_right .zero x y
    change nodes y < nodes (P x y) at hb
    rw [hy,nodes_S] at hb
    have hz := pair_right .zero z (S u)
    rw [nodes_S] at hz
    exact Nat.lt_trans hz hb
  have hxy := image_small_phase_one_origin hi x y rfl hua
  rw [hy] at hxy
  have hx := image_nonzero_target hxy (by intro a b h; cases h)
  obtain ⟨r,hr,hu⟩ := image_small_phase_one_common_root hi x y rfl hua
  simp only [cube] at hu
  rw [hx] at hr
  exact common_root_successor_tail_false hr hu

#print axioms rotated_column_canonical_target
#print axioms rotated_column_completed_target
#print axioms rotated_column_inverse_ancestry_target
#print axioms rotated_column_inverse_literal_false
end Equation22446Lineage

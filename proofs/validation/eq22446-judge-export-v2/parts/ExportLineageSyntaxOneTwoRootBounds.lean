prelude
import Init.Classical
import Init.Data.Nat.Lemmas
import Init.RCases
import ExportLineageSyntaxLineageImageUniqueness
set_option Elab.async false
set_option autoImplicit false
set_option Elab.async false

namespace submission.Equation22446Lineage
open submission.Equation22446Guarded

theorem one_two_columns_nongrowing_inverse {p q u : T}
    (hp : ∃ x y, p = S (P x y)) (hq : ∃ x y, q = S (S (P x y)))
    (hs : nodes p ≤ nodes q) (hc : Column u p) (hd : Column u q) :
    Image p (S u) ∧ Image q (S u) := by
  have hj := column_two_value_inverse hd hq
  obtain ⟨x,y,hp⟩ := hp
  obtain ⟨w,t,hq⟩ := hq
  have hqu := column_phase_two_bound hd w t hq
  cases hc with
  | ancestry hl =>
      cases hl with
      | refl =>
          have hu := congrArg S hp
          rw [cube] at hu
          have ht := image_phase_two_strict hj ⟨w,t,hq⟩ ⟨x,y,by rw [hu]; rfl⟩
          simp only [nodes_S] at hs ht
          exact False.elim (Nat.not_lt_of_ge hs ht)
      | @step u r s hl hi =>
          have hur := lineage_nodes hl
          have hrp := pair_left .zero r s
          simp only [cube,nodes_S] at hs
          exact False.elim (Nat.not_lt_of_ge (Nat.le_trans hs hqu) (Nat.lt_of_le_of_lt hur hrp))
  | literal u z => cases hp
  | inverseImage hi => exact ⟨hi,hj⟩

theorem one_two_images_nongrowing_false_at_size (n : Nat) :
    ∀ p q b, nodes b = n → (∃ x y, p = S (P x y)) → (∃ x y, q = S (S (P x y))) →
      nodes p ≤ nodes q → Image p b → Image q b → False := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      intro p q b hn hp hq hs hi hj
      obtain ⟨x,y,hp⟩ := hp
      obtain ⟨w,t,hq⟩ := hq
      cases hi with
      | square p =>
          have ht := image_phase_two_output_left hj w t x y hq (by rw [hp]; rfl)
          rw [hp,nodes_S] at hs
          exact Nat.not_lt_of_ge (Nat.le_trans hs ht) (pair_left .zero x y)
      | literal p z =>
          generalize he : P (P p z) z = b at hj
          cases hj with
          | square q => rw [hq] at he; cases he
          | literal q z =>
              have heq := (T.p.inj (T.p.inj he).2.1).2.1
              rw [hp,hq] at heq
              cases heq
          | transport hc hk =>
              rw [←(T.p.inj he).2.1,←(T.p.inj he).2.2] at hk
              exact image_pair_tail_false hk
          | inverseFollowup q => cases hq
          | returnFollowup hk => cases hq
          | cycleFollowup ht hk hl => cases hq
      | @transport u p v hc hk =>
          generalize he : P u v = b at hj
          cases hj with
          | square q => rw [hq] at he; cases he
          | literal q z =>
              rw [(T.p.inj he).2.1,(T.p.inj he).2.2] at hk
              exact image_pair_tail_false hk
          | transport hd hl =>
              rw [←(T.p.inj he).2.1] at hd
              obtain ⟨hi',hj'⟩ := one_two_columns_nongrowing_inverse ⟨x,y,hp⟩ ⟨w,t,hq⟩ hs hc hd
              have ht : nodes (S u) < n := by rw [nodes_S,←hn]; exact pair_left .zero u v
              exact ih _ ht p q (S u) rfl ⟨x,y,hp⟩ ⟨w,t,hq⟩ hs hi' hj'
          | inverseFollowup q => cases hq
          | returnFollowup hk => cases hq
          | cycleFollowup ht hk hl => cases hq
      | inverseFollowup p => cases hp
      | returnFollowup hk => cases hp
      | cycleFollowup ht hk hl => cases hp

theorem image_one_two_root_bound {p q b : T}
    (hp : ∃ x y, p = S (P x y)) (hq : ∃ x y, q = S (S (P x y)))
    (hi : Image p b) (hj : Image q b) : nodes q < nodes p := by
  apply Nat.lt_of_not_ge
  intro hs
  exact one_two_images_nongrowing_false_at_size (nodes b) p q b rfl hp hq hs hi hj

end submission.Equation22446Lineage

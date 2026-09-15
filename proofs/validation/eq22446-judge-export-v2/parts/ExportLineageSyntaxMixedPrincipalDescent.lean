prelude
import Init.Classical
import Init.Data.Nat.Lemmas
import Init.RCases
import ExportLineageSyntaxAtomOrZeroBases
set_option Elab.async false
set_option autoImplicit false
set_option Elab.async false

namespace submission.Equation22446Lineage
open submission.Equation22446Guarded

theorem low_two_shared_transport_inverse {p q u a : T}
    (hp : AtomOrZero p) (hq : ∃ x y, q = S (S (P x y)))
    (hc : Column p a) (hd : Column q a) (hu : Column u p) (hv : Column u q) :
    Image p (S u) ∧ Image q (S u) := by
  cases hu with
  | @ancestry u r hl =>
      have hr : ∀ x y, r ≠ S (S (P x y)) := by
        intro x y he
        exact atom_or_zero_not_one hp x y (by rw [he]; rfl)
      have he := lineage_non_phase_two hl hr
      rcases column_phase_two_base_shape hv hq with ⟨x,y,hu⟩ | ⟨x,y,hu⟩
      · exact False.elim (atom_or_zero_not_two hp x y (by rw [←he,hu]))
      · exact False.elim (atom_or_zero_not_one hp x y (by rw [←he,hu]; rfl))
  | literal u y =>
      obtain ⟨x,z,hq⟩ := hq
      have hs := shared_column_atom_or_zero_bound hp hc hd
      have ht := column_phase_two_bound hv x z hq
      have hb := pair_right .zero y (S u)
      change nodes (S u) < nodes (P y (S u)) at hb
      rw [nodes_S] at hb
      exact False.elim (Nat.not_lt_of_ge (Nat.le_trans hs ht) hb)
  | inverseImage hi =>
      rcases column_phase_two_base_shape hv hq with ⟨x,y,hu⟩ | ht
      · have he := image_nonzero_target hi (by intro w z h; rw [hu] at h; cases h)
        exact False.elim (atom_or_zero_not_two hp x y (by rw [he,hu]))
      · exact ⟨hi,column_two_to_two_inverse hv ht hq⟩

theorem low_two_principal_false_at_size (n : Nat) :
    ∀ p q a b, nodes b = n → AtomOrZero p → (∃ x y, q = S (S (P x y))) →
      Column p a → Column q a → Image p b → Image q b → False := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      intro p q a b hn hp hq hc hd hi hj
      obtain ⟨w,t,hq⟩ := hq
      cases hi with
      | square p =>
          have he := image_nonzero_target hj (atom_or_zero_double_nonzero hp)
          simp only [cube] at he
          exact atom_or_zero_not_two hp w t (he.symm.trans hq)
      | literal p z =>
          generalize he : P (P p z) z = b at hj
          cases hj with
          | square q => rw [hq] at he; cases he
          | literal q t =>
              have hpq := (T.p.inj (T.p.inj he).2.1).2.1
              exact atom_or_zero_not_two hp w _ (hpq.trans hq)
          | transport hk hl =>
              rw [←(T.p.inj he).2.1,←(T.p.inj he).2.2] at hl
              exact image_pair_tail_false hl
          | inverseFollowup q => cases hq
          | returnFollowup hk => cases hq
          | cycleFollowup hs hk hl => cases hq
      | @transport u p v hu hv =>
          generalize he : P u v = b at hj
          cases hj with
          | square q => rw [hq] at he; cases he
          | literal q z =>
              rw [(T.p.inj he).2.1,(T.p.inj he).2.2] at hv
              exact image_pair_tail_false hv
          | transport hk hl =>
              rw [←(T.p.inj he).2.1] at hk
              obtain ⟨hi',hj'⟩ := low_two_shared_transport_inverse hp ⟨w,t,hq⟩ hc hd hu hk
              have hs : nodes (S u) < n := by rw [nodes_S,←hn]; exact pair_left .zero u v
              exact ih _ hs p q a (S u) rfl hp ⟨w,t,hq⟩ hc hd hi' hj'
          | inverseFollowup q => cases hq
          | returnFollowup hk => cases hq
          | cycleFollowup hs hk hl => cases hq
      | inverseFollowup v =>
          have hs := shared_column_atom_or_zero_bound hp hc hd
          have ht := image_phase_two_output_left hj w t (S (S v)) (S v) hq rfl
          simp only [nodes_S] at ht
          exact Nat.not_lt_of_ge (Nat.le_trans hs ht) (pair_left .zero v (S v))
      | @returnFollowup v z hk =>
          have hs := shared_column_atom_or_zero_bound hp hc hd
          have ht := image_phase_two_output_left hj w t (S (P v z)) (S v) hq rfl
          simp only [nodes_S] at ht
          have hb := pair_left .zero (S (S (P v z))) (S v)
          simp only [nodes_S] at hb
          exact Nat.not_lt_of_ge (Nat.le_trans hs ht) hb
      | @cycleFollowup u v x y z hs hk hl =>
          have ht := shared_column_atom_or_zero_bound hp hc hd
          have hq' := image_phase_two_output_left hj w t (S (P x y)) z hq rfl
          simp only [nodes_S] at hq'
          rw [cycle_followup_input_eq hs hk hl] at ht
          have hb := pair_left .zero (S (S (P x y))) z
          simp only [nodes_S] at hb
          exact Nat.not_lt_of_ge (Nat.le_trans ht hq') hb

theorem low_two_principal_false {p q a b : T}
    (hp : AtomOrZero p) (hq : ∃ x y, q = S (S (P x y)))
    (hc : Column p a) (hd : Column q a) (hi : Image p b) (hj : Image q b) : False :=
  low_two_principal_false_at_size (nodes b) p q a b rfl hp hq hc hd hi hj

end submission.Equation22446Lineage

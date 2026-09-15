prelude
import Init.Classical
import Init.Data.Nat.Lemmas
import Init.RCases
import ExportLineageSyntaxMixedPrincipalDescent
set_option Elab.async false
set_option autoImplicit false
set_option Elab.async false

namespace submission.Equation22446Lineage
open submission.Equation22446Guarded

theorem column_two_value_inverse {u q : T} (hc : Column u q)
    (hq : ∃ x y, q = S (S (P x y))) : Image q (S u) := by
  cases hc with
  | ancestry hl =>
      obtain ⟨x,y,hq⟩ := hq
      have hr := S_injective (S_injective hq)
      have hu := lineage_non_phase_two hl (by intro a b h; rw [hr] at h; cases h)
      rw [hu]
      simpa only [cube] using (Image.square (S (S _)))
  | literal u y => obtain ⟨x,z,hq⟩ := hq; cases hq
  | inverseImage hi => exact hi

theorem joint_lineage_query_unique (n : Nat) :
    (∀ p q b, nodes b = n → Lineage p q → Image p b → Image q b → p = q) ∧
    (∀ u p q, nodes u = n → Lineage p q → Column u p → Column u q → p = q) := by
  classical
  induction n using Nat.strongRecOn with
  | ind n ih =>
      have image_here : ∀ p q b, nodes b = n → Lineage p q → Image p b → Image q b → p = q := by
        intro p q b hn hl hi hj
        by_cases heq : p = q
        · exact heq
        have hq : ∃ x y, q = S (S (P x y)) := by
          cases hl with
          | refl => exact False.elim (heq rfl)
          | step hl hk => exact ⟨_,_,rfl⟩
        obtain ⟨w,t,hq⟩ := hq
        have hpq := lineage_nodes hl
        cases hi with
        | square p =>
            rcases phase_one_or_double_nonzero p with ⟨x,y,hp⟩ | hp
            · have hs := image_phase_two_output_left hj w t x y hq (by rw [hp]; rfl)
              rw [hp,nodes_S] at hpq
              exact False.elim (Nat.not_lt_of_ge (Nat.le_trans hpq hs) (pair_left .zero x y))
            · have he := image_nonzero_target hj hp
              simpa only [cube] using he.symm
        | literal p z =>
            generalize he : P (P p z) z = b at hj
            cases hj with
            | square q => rw [hq] at he; cases he
            | literal q t => exact (T.p.inj (T.p.inj he).2.1).2.1
            | transport hc hk =>
                rw [←(T.p.inj he).2.1,←(T.p.inj he).2.2] at hk
                exact False.elim (image_pair_tail_false hk)
            | inverseFollowup q => cases hq
            | returnFollowup hk => cases hq
            | cycleFollowup hs hk hm => cases hq
        | @transport u p v hc hk =>
            generalize he : P u v = b at hj
            cases hj with
            | square q => rw [hq] at he; cases he
            | literal q z =>
                rw [(T.p.inj he).2.1,(T.p.inj he).2.2] at hk
                exact False.elim (image_pair_tail_false hk)
            | transport hd hm =>
                rw [←(T.p.inj he).2.1] at hd
                have hs : nodes u < n := by rw [←hn]; exact pair_left .zero u v
                exact (ih _ hs).2 u p q rfl hl hc hd
            | inverseFollowup q => cases hq
            | returnFollowup hk => cases hq
            | cycleFollowup hs hk hm => cases hq
        | inverseFollowup v =>
            have hs := image_phase_two_output_left hj w t (S (S v)) (S v) hq rfl
            simp only [nodes_S] at hs
            exact False.elim (Nat.not_lt_of_ge (Nat.le_trans hpq hs) (pair_left .zero v (S v)))
        | @returnFollowup v z hk =>
            have hs := image_phase_two_output_left hj w t (S (P v z)) (S v) hq rfl
            simp only [nodes_S] at hs
            have hb := pair_left .zero (S (S (P v z))) (S v)
            simp only [nodes_S] at hb
            exact False.elim (Nat.not_lt_of_ge (Nat.le_trans hpq hs) hb)
        | @cycleFollowup x y u v z hs hk hm =>
            have ht := image_phase_two_output_left hj w t (S (P u v)) z hq rfl
            simp only [nodes_S] at ht
            rw [cycle_followup_input_eq hs hk hm] at hpq
            have hb := pair_left .zero (S (S (P u v))) z
            simp only [nodes_S] at hb
            exact False.elim (Nat.not_lt_of_ge (Nat.le_trans hpq ht) hb)
      refine ⟨image_here,?_⟩
      intro u p q hn hl hc hd
      by_cases heq : p = q
      · exact heq
      have hpq : nodes p < nodes q := by
        apply Nat.lt_of_not_ge
        intro hs
        exact heq (lineage_nonincreasing_eq hl hs)
      have hq : ∃ x y, q = S (S (P x y)) := by
        cases hl with
        | refl => exact False.elim (heq rfl)
        | step hl hi => exact ⟨_,_,rfl⟩
      obtain ⟨x,y,hq'⟩ := hq
      have hqu := column_phase_two_bound hd x y hq'
      cases hc with
      | ancestry hm =>
          have hup := lineage_nodes hm
          simp only [nodes_S] at hpq
          exact False.elim (Nat.not_lt_of_ge (Nat.le_trans hqu hup) hpq)
      | literal u z =>
          have hup := pair_right .zero z (S u)
          rw [nodes_S] at hup
          exact False.elim (Nat.not_lt_of_ge hqu (Nat.lt_trans hup hpq))
      | inverseImage hi =>
          exact image_here p q (S u) (by simpa only [nodes_S] using hn) hl hi
            (column_two_value_inverse hd ⟨x,y,hq'⟩)

theorem image_lineage_roots_unique {p q b : T} (hl : Lineage p q)
    (hi : Image p b) (hj : Image q b) : p = q :=
  (joint_lineage_query_unique (nodes b)).1 p q b rfl hl hi hj

theorem column_lineage_values_unique {u p q : T} (hl : Lineage p q)
    (hc : Column u p) (hd : Column u q) : p = q :=
  (joint_lineage_query_unique (nodes u)).2 u p q rfl hl hc hd

end submission.Equation22446Lineage

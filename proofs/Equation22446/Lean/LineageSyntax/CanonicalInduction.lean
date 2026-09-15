prelude
import LineageSyntax.RotatedColumnOrigins
set_option autoImplicit false
set_option Elab.async false

namespace Equation22446Lineage
open Equation22446Guarded

theorem image_literal_target_cases {p z q b : T} (hi : Image q b) (he : b = P (P p z) z) :
    q = p ∨ q = S b := by
  cases hi with
  | square q => exact Or.inr (cube q).symm
  | literal q t => exact Or.inl (T.p.inj (T.p.inj he).2.1).2.1
  | transport hc hj =>
      rw [(T.p.inj he).2.1,(T.p.inj he).2.2] at hj
      exact False.elim (image_pair_tail_false hj)
  | inverseFollowup v =>
      have hb := pair_right .zero p z
      change nodes z < nodes (P p z) at hb
      rw [←(T.p.inj he).2.1,←(T.p.inj he).2.2] at hb
      simp only [nodes_S] at hb
      exact False.elim (Nat.lt_irrefl _ hb)
  | returnFollowup hj => cases (T.p.inj he).2.1
  | cycleFollowup hs hj hk => cases (T.p.inj he).2.1

theorem joint_canonical_unique (n : Nat) :
    (∀ x y q b, nodes b = n → Normal (P x y) → Normal b → Column q (P x y) →
      Image (S (P x y)) b → Image q b → q = S (P x y)) ∧
    (∀ u q x y, nodes u = n → Normal (P x y) → Normal u →
      Column u q → Column q (P x y) → Column u (S (P x y)) → q = S (P x y)) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      have canonical_here : ∀ x y q b, nodes b = n → Normal (P x y) → Normal b →
          Column q (P x y) → Image (S (P x y)) b → Image q b → q = S (P x y) := by
        intro x y q b hn ha hb hc hi hj
        generalize hp : S (P x y) = p at hi
        rw [←hp]
        cases hi with
        | square p =>
            rw [←hp,cube] at hj
            exact normal_diagonal_target ha hc hj
        | literal p z =>
            rcases image_literal_target_cases hj rfl with hq | hq
            · exact hq.trans hp.symm
            · have hs := column_non_two_base_bound hc (by intro u v h; rw [hq] at h; cases h)
              rw [hq,nodes_S] at hs
              have ht := Nat.lt_trans (pair_left .zero p z) (pair_left .zero _ z)
              have hpn : nodes p = nodes (P x y) := by rw [←hp,nodes_S]
              rw [hpn] at ht
              exact False.elim (Nat.not_lt_of_ge hs ht)
        | @transport u p v hu hv =>
            rw [←hp] at hu
            have hnu : Normal u := hb.1
            generalize he : P u v = b at hj
            cases hj with
            | square q =>
                have hq := congrArg S he
                rw [cube] at hq
                rw [←hq] at hc
                exact hq.symm.trans (canonical_square_transport_target hu hc)
            | literal q z =>
                rw [(T.p.inj he).2.1,(T.p.inj he).2.2] at hv
                exact False.elim (image_pair_tail_false hv)
            | transport hk hl =>
                rw [←(T.p.inj he).2.1] at hk
                have hs : nodes u < n := by rw [←hn]; exact pair_left .zero u v
                exact (ih _ hs).2 u q x y rfl ha hnu hk hc hu
            | inverseFollowup w =>
                rw [(T.p.inj he).2.1] at hu
                have hs : nodes (S (S w)) < nodes (P w (S w)) := by
                  simp only [nodes_S]
                  exact pair_left .zero w (S w)
                exact False.elim (column_zero_pair_rotated_chain_false
                  (fun hi => image_no_successor hi) hs hu hc)
            | @returnFollowup w t hk =>
                rw [(T.p.inj he).2.1] at hu
                have hs : nodes (S (P w t)) < nodes (P (S (S (P w t))) (S w)) := by
                  have hs := pair_left .zero (S (S (P w t))) (S w)
                  change nodes (S (S (P w t))) < nodes (P (S (S (P w t))) (S w)) at hs
                  simpa only [nodes_S] using hs
                have hnot : ¬ Image (S (S (P w t))) (S w) := by
                  intro h
                  have hs := image_phase_two_bound h w t rfl
                  simp only [nodes_S] at hs
                  exact Nat.not_lt_of_ge hs (pair_left .zero w t)
                exact False.elim (column_zero_pair_rotated_chain_false hnot hs hu hc)
            | @cycleFollowup a b w t z hs hk hl =>
                rw [(T.p.inj he).2.1] at hu
                rw [cycle_followup_input_eq hs hk hl] at hc
                have hsz : nodes (S (P w t)) < nodes (P (S (S (P w t))) z) := by
                  have ht := pair_left .zero (S (S (P w t))) z
                  change nodes (S (S (P w t))) < nodes (P (S (S (P w t))) z) at ht
                  simpa only [nodes_S] using ht
                have hnot : ¬ Image (S (S (P w t))) z := by
                  intro h
                  have hbig := image_phase_two_bound h w t rfl
                  simp only [nodes_S] at hbig
                  have hsmall := image_right_child hl .zero (P a b) z (by intro h; cases h) rfl
                  exact Nat.not_lt_of_ge hbig hsmall
                exact False.elim (column_zero_pair_rotated_chain_false hnot hsz hu hc)
        | inverseFollowup p => cases hp
        | returnFollowup hk => cases hp
        | cycleFollowup hs hk hl => cases hp
      refine ⟨canonical_here,?_⟩
      intro u q x y hn ha hnu hc hd ht
      generalize he : S (P x y) = a at ht
      rw [←he]
      cases ht with
      | ancestry hl =>
          cases hl with
          | refl =>
              have hu := congrArg S he
              rw [cube] at hu
              rw [←hu] at hc
              exact rotated_column_canonical_target ha hc hd
          | @step u r s hl hi =>
              simp only [cube] at he
              have hxy := S_injective he
              rw [←(T.p.inj hxy).2.1] at hl
              rw [←(T.p.inj hxy).2.1,←(T.p.inj hxy).2.2] at hi
              exact rotated_column_completed_target hl hi hc hd
      | literal u z => cases he
      | inverseImage hi =>
          rw [←he] at hi
          rcases phase_two_or_square_nonzero u with hu | hnot
          · cases hc with
            | ancestry hl => exact rotated_column_inverse_ancestry_target hu hl hd hi
            | literal u z => exact False.elim (rotated_column_inverse_literal_false hd hi)
            | inverseImage hj =>
                exact canonical_here x y q (S u) (by simpa only [nodes_S] using hn) ha
                  ((normal_rotate .one u).mpr hnu) hd hi hj
          · have hu := congrArg S (image_nonzero_target hi hnot)
            rw [cube] at hu
            rw [←hu] at hc
            exact rotated_column_canonical_target ha hc hd

theorem normal_canonical_principal_unique {x y q b : T}
    (ha : Normal (P x y)) (hb : Normal b) (hc : Column q (P x y))
    (hi : Image (S (P x y)) b) (hj : Image q b) : q = S (P x y) :=
  (joint_canonical_unique (nodes b)).1 x y q b rfl ha hb hc hi hj

theorem normal_rotated_column_target {u q x y : T}
    (ha : Normal (P x y)) (hu : Normal u)
    (hc : Column u q) (hd : Column q (P x y)) (ht : Column u (S (P x y))) :
    q = S (P x y) :=
  (joint_canonical_unique (nodes u)).2 u q x y rfl ha hu hc hd ht

#print axioms image_literal_target_cases
#print axioms joint_canonical_unique
#print axioms normal_canonical_principal_unique
#print axioms normal_rotated_column_target
end Equation22446Lineage

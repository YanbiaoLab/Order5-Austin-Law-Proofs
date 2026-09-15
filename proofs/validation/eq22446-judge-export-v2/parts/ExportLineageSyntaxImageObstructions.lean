prelude
import Init.Classical
import Init.Data.Nat.Lemmas
import Init.RCases
import ExportLineageSyntaxInverseCycles
set_option Elab.async false
set_option autoImplicit false
set_option Elab.async false

namespace submission.Equation22446Lineage
open submission.Equation22446Guarded

theorem image_no_successor {p : T} (hi : Image p (S p)) : False := by
  rcases phase_two_or_square_nonzero p with ⟨a,b,hp⟩ | hn
  · change p = S (S (P a b)) at hp
    have hq : S p = P a b := by rw [hp,cube]
    have hs := image_phase_two_output_left hi a b a b hp hq
    rw [hp,nodes_S,nodes_S] at hs
    exact Nat.not_lt_of_ge hs (pair_left .zero a b)
  · exact S_ne p (S_injective (image_nonzero_output hi hn)).symm

theorem lineage_trans {p q r : T} (hp : Lineage p q) (hq : Lineage q r) : Lineage p r :=
  match hq with
  | .refl q => hp
  | .step hl hi => .step (lineage_trans hp hl) hi

theorem lineage_image_inverse_false {p q : T} (hi : Image p q)
    (hl : Lineage (S (S q)) p) : False := by
  cases hl with
  | refl =>
      exact image_no_successor (p := S (S q)) (by simpa only [cube] using hi)
  | @step p a b hl hj =>
      have hs := image_phase_two_bound hi a b rfl
      have ht := lineage_nodes hl
      rw [nodes_S,nodes_S] at ht hs
      exact Nat.not_lt_of_ge (Nat.le_trans hs ht) (pair_left .zero a b)

theorem column_left_pair_image_false {p z : T} (hc : Column p (P p z))
    (hi : Image p z) : False := by
  generalize ha : P p z = a at hc
  cases hc with
  | ancestry hl =>
      have he := congrArg S ha
      rw [cube] at he
      have hp := lineage_non_phase_two hl (by intro u v h; rw [←he] at h; cases h)
      have hs := congrArg nodes (hp.trans he.symm)
      rw [nodes_S] at hs
      exact Nat.ne_of_lt (pair_left .zero p z) hs
  | literal p y =>
      rw [(T.p.inj ha).2.2] at hi
      exact image_no_successor hi
  | inverseImage hj =>
      rw [←ha] at hj
      exact lineage_image_inverse_false hi (shrinking_inverse_lineage hj (pair_left .zero p z))

theorem cycle_followup_not_self {u v w t z : T}
    (hi : Image (S (S (P w t))) (P (P u v) z)) :
    P u v ≠ P (S (P w t)) z := by
  intro he
  have hu := (T.p.inj he).2.1
  generalize hp : S (S (P w t)) = p at hi
  generalize hq : P (P u v) z = q at hi
  cases hi with
  | square p => rw [←hp] at hq; cases hq
  | literal p y =>
      have hu' := (T.p.inj (T.p.inj hq).2.1).2.1
      rw [hu',←hp] at hu
      cases hu
  | transport hc hj =>
      rw [←hp,←(T.p.inj hq).2.1] at hc
      have ht := column_zero_to_two hc
      rw [ht] at he
      have hs := congrArg nodes he
      have hb := pair_left .zero (S (P w t)) z
      change nodes (S (P w t)) < nodes (P (S (P w t)) z) at hb
      rw [nodes_S,←hs] at hb
      exact Nat.lt_irrefl _ hb
  | inverseFollowup p => cases hp
  | returnFollowup hj => cases hp
  | cycleFollowup hs hj hk => cases hp

theorem image_self_eq_false {p q : T} (h : Image p q) (hp : q = p) : False := by
  cases h with
  | square p => exact SS_ne p hp
  | literal p z =>
      have hn := congrArg nodes hp
      exact Nat.ne_of_lt (Nat.lt_trans (pair_left .zero _ _) (pair_left .zero _ _)) hn.symm
  | transport hc hi =>
      rw [←hp] at hc
      exact column_left_pair_image_false hc hi
  | inverseFollowup p => exact SS_ne p (T.p.inj hp).2.1
  | returnFollowup hi => exact S_ne _ (S_injective (T.p.inj hp).2.1).symm
  | cycleFollowup hs hi hj => exact cycle_followup_not_self hi hp.symm

theorem image_no_self {p : T} (h : Image p p) : False := image_self_eq_false h rfl

theorem image_rotated_lineage_false {p q : T} (hi : Image p q)
    (hl : Lineage (S (S q)) (S (S p))) : False := by
  generalize he : S (S p) = t at hl
  cases hl with
  | refl =>
      have hp := S_injective (S_injective he)
      rw [hp] at hi
      exact image_no_self hi
  | @step p' a b hl hj =>
      have hp := S_injective (S_injective he)
      have hs := lineage_nodes hl
      rw [nodes_S,nodes_S] at hs
      have hsmall : nodes q < nodes p := by
        rw [hp]
        exact Nat.lt_of_le_of_lt hs (pair_left .zero a b)
      have hq := image_shrinking_lineage hi a b hp hsmall
      exact lineage_image_inverse_false hj (lineage_trans hq hl)

theorem image_pair_flip_false {p q : T} (hi : Image p q)
    (hj : Image (P p q) p) : False :=
  image_rotated_lineage_false hi (image_shrinking_lineage hj p q rfl (pair_left .zero p q))

end submission.Equation22446Lineage

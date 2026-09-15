prelude
import Init.Classical
import Init.Data.Nat.Lemmas
import Init.RCases
import ExportLineageSyntaxTriangleColumnExtras
set_option Elab.async false
set_option autoImplicit false
set_option Elab.async false

namespace submission.Equation22446Lineage
open submission.Equation22446Guarded

theorem cycle_followup_input_eq {u v w t z : T}
    (hs : nodes (S (S (P w t))) < nodes (P (P u v) z))
    (hi : Image (S (S (P w t))) (P (P u v) z))
    (hj : Image (P (P u v) z) (P w t)) : P u v = P (S (S (P w t))) z :=
  cycle_target_literal hi (by simpa only [cube] using hj) hs

theorem image_literal_triangle_false {p z a q : T} (hc : Column p a)
    (hi : Image a q) (he : q = P (P p z) z) : False := by
  cases hi with
  | square a =>
      have ha := congrArg S he
      rw [cube] at ha
      have hs := column_ancestor_bound hc (P p z) (P p z) z ha
        (by intro u v h; cases h) (.refl _)
      exact Nat.not_lt_of_ge hs (pair_left .zero p z)
  | literal a t =>
      have ha := (T.p.inj (T.p.inj he).2.1).2.1
      rw [ha] at hc
      exact column_no_self hc
  | transport hd hj =>
      rw [(T.p.inj he).2.1,(T.p.inj he).2.2] at hj
      exact image_pair_tail_false hj
  | inverseFollowup v =>
      have hb := pair_right .zero p z
      change nodes z < nodes (P p z) at hb
      rw [←(T.p.inj he).2.1,←(T.p.inj he).2.2] at hb
      simp only [nodes_S] at hb
      exact Nat.lt_irrefl _ hb
  | returnFollowup hj => cases (T.p.inj he).2.1
  | cycleFollowup hs hj hk => cases (T.p.inj he).2.1

theorem image_inverse_triangle_false {v a q : T} (hc : Column (P v (S v)) a)
    (hi : Image a q) (he : q = P (S (S v)) (S v)) : False := by
  cases hi with
  | square a =>
      have ha := congrArg S he
      rw [cube] at ha
      rw [ha] at hc
      have hs := lineage_nodes (column_zero_phase_one_origin hc).1
      simp only [nodes_S] at hs
      exact Nat.not_lt_of_ge hs (pair_left .zero v (S v))
  | literal a t =>
      have hb := pair_right .zero a t
      change nodes t < nodes (P a t) at hb
      rw [(T.p.inj he).2.1,(T.p.inj he).2.2] at hb
      simp only [nodes_S] at hb
      exact Nat.lt_irrefl _ hb
  | transport hd hj =>
      rw [(T.p.inj he).2.1] at hd
      have hs := shared_column_phase_zero_bound hc hd
      simp only [nodes_S] at hs
      exact Nat.not_lt_of_ge hs (pair_left .zero v (S v))
  | inverseFollowup w =>
      have hw := S_injective (T.p.inj he).2.2
      rw [hw] at hc
      exact column_no_self hc
  | @returnFollowup w t hj =>
      have hw := S_injective (T.p.inj he).2.2
      have hl := (T.p.inj he).2.1
      rw [hw] at hl
      have hn := congrArg nodes hl
      simp only [nodes_S] at hn
      exact Nat.ne_of_lt (pair_left .zero v t) hn.symm
  | @cycleFollowup u z w t b hs hj hk =>
      have ha := cycle_followup_input_eq hs hj hk
      have hr := congrArg S (T.p.inj he).2.1
      simp only [cube] at hr
      rw [ha,hr,(T.p.inj he).2.2] at hc
      exact column_no_self hc

 
theorem image_rotated_pair_triangle_false {u v z a q : T}
    (hc : Column (P (S (S (P u v))) z) a)
    (hi : Image a q) (he : q = P (S (P u v)) z) : False := by
  cases hi with
  | square a =>
      have ha := congrArg S he
      rw [cube] at ha
      rw [ha] at hc
      have hl := (column_zero_phase_one_origin hc).1
      have hp := lineage_non_phase_two hl (by intro x y h; cases h)
      cases hp
  | literal a t => cases (T.p.inj he).2.1
  | transport hd hj =>
      rw [(T.p.inj he).2.1] at hd
      have hs := shared_column_phase_zero_bound hc hd
      simp only [nodes_S] at hs
      have hb := pair_left .zero (S (S (P u v))) z
      simp only [nodes_S] at hb
      exact Nat.not_lt_of_ge hs hb
  | inverseFollowup w =>
      have hw := congrArg S (T.p.inj he).2.1
      rw [cube] at hw
      have hz := (T.p.inj he).2.2
      rw [hz,hw] at hc
      exact column_no_self hc
  | @returnFollowup w t hj =>
      have hp := S_injective (T.p.inj he).2.1
      rw [hp,(T.p.inj he).2.2] at hc
      exact column_no_self hc
  | @cycleFollowup x y w t b hs hj hk =>
      have ha := cycle_followup_input_eq hs hj hk
      have hp := S_injective (T.p.inj he).2.1
      rw [ha,hp,(T.p.inj he).2.2] at hc
      exact column_no_self hc

end submission.Equation22446Lineage

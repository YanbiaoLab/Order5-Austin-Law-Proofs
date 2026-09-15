prelude
import Init.Classical
import Init.Data.Nat.Lemmas
import Init.RCases
import ExportLineageSyntaxTriangleImageRoots
set_option Elab.async false
set_option autoImplicit false
set_option Elab.async false

namespace submission.Equation22446Lineage
open submission.Equation22446Guarded

theorem image_transport_common_column {u v p a q : T}
    (hc : Column u p) (hi : Image u v) (hd : Column p a)
    (hj : Image a q) (he : q = P u v) : Column u a := by
  cases hj with
  | square a =>
      have ha := congrArg S he
      rw [cube] at ha
      rw [ha] at hd
      exact False.elim (column_chain_completed_false hc hd)
  | literal a t =>
      rw [←(T.p.inj he).2.1,←(T.p.inj he).2.2] at hi
      exact False.elim (image_pair_tail_false hi)
  | transport hk hl =>
      rw [(T.p.inj he).2.1] at hk
      exact hk
  | inverseFollowup w =>
      rw [←(T.p.inj he).2.1] at hc
      exact False.elim (column_inverse_pair_chain_false hc hd)
  | @returnFollowup w t hk =>
      rw [←(T.p.inj he).2.1] at hc
      have hs : nodes (S w) < nodes (P w t) := by rw [nodes_S]; exact pair_left .zero w t
      exact False.elim (column_tall_head_chain_false hs hc hd)
  | @cycleFollowup x y w t z hs hk hl =>
      rw [←(T.p.inj he).2.1] at hc
      have ha := cycle_followup_input_eq hs hk hl
      rw [ha] at hd
      have hz := image_right_child hl .zero (P x y) z (by intro h; cases h) rfl
      exact False.elim (column_tall_head_chain_false hz hc hd)

end submission.Equation22446Lineage

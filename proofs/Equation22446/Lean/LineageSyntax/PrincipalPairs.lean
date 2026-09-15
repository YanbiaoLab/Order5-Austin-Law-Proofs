prelude
import LineageSyntax.NonzeroCoverage
set_option autoImplicit false
set_option Elab.async false

namespace Equation22446Lineage
open Equation22446Guarded

theorem image_no_left_pair {p q : T} (h : Image p q) : ∀ z, q = P p z → False := by
  intro z he
  cases h with
  | square p =>
      have hs := congrArg nodes he
      rw [nodes_S,nodes_S] at hs
      exact Nat.ne_of_lt (pair_left .zero p z) hs
  | literal p t =>
      exact Nat.ne_of_lt (pair_left .zero p t) (congrArg nodes (T.p.inj he).2.1).symm
  | transport hc hi =>
      rw [(T.p.inj he).2.1] at hc
      exact column_no_self hc
  | inverseFollowup p =>
      have hs := congrArg nodes (T.p.inj he).2.1
      rw [nodes_S,nodes_S] at hs
      exact Nat.ne_of_lt (pair_left .zero p (S p)) hs
  | @returnFollowup p q hi =>
      have hs := congrArg nodes (T.p.inj he).2.1
      rw [nodes_S] at hs
      have hb := pair_left .zero (S (S (P p q))) (S p)
      rw [nodes_S,nodes_S] at hb
      exact Nat.ne_of_lt hb hs
  | cycleFollowup hs hi hj => cases (T.p.inj he).2.1

/-- A rectangle on (P(a,b),b) can only target the successor of P(a,b). -/
theorem principal_pair_target {p a b : T} (hc : Column p (P a b))
    (hi : Image p b) : p = S (P a b) := by
  generalize he : P a b = t at hc
  cases hc with
  | ancestry hl =>
      have ha := congrArg S he
      rw [cube] at ha
      have hp := lineage_non_phase_two hl (by intro u v h; rw [←ha] at h; cases h)
      simpa only [cube] using hp
  | literal p y =>
      rw [(T.p.inj he).2.2] at hi
      exact False.elim (image_no_successor hi)
  | inverseImage hj =>
      rw [←he] at hj
      rcases phase_two_or_square_nonzero p with ⟨u,v,hp⟩ | hn
      · have hs := image_phase_two_bound hi u v hp
        have ht := image_right_child hj .zero a b (by intro h; cases h) rfl
        rw [nodes_S] at ht
        exact False.elim (Nat.not_lt_of_ge hs ht)
      · rw [←he]
        exact S_injective (image_nonzero_output hj hn)

theorem principal_pair_inner_image {p a b : T} (hc : Column p (P a b))
    (hi : Image p b) : Image a b := by
  have hp := principal_pair_target hc hi
  exact image_small_phase_one_origin hi a b hp (by rw [hp,nodes_S]; exact pair_right .zero a b)

theorem rectangle_inverse_double_false {r p : T} (hc : Column r (P p (S p)))
    (hi : Image r (S p)) : False := image_no_successor (principal_pair_inner_image hc hi)

theorem rectangle_image_return_false {r p q : T}
    (hc : Column r (P (S (S (P p q))) (S p))) (hi : Image r (S p)) : False := by
  have hj := principal_pair_inner_image hc hi
  have hs := image_phase_two_bound hj p q rfl
  rw [nodes_S,nodes_S,nodes_S] at hs
  exact Nat.not_lt_of_ge hs (pair_left .zero p q)

#print axioms image_no_left_pair
#print axioms principal_pair_target
#print axioms principal_pair_inner_image
#print axioms rectangle_inverse_double_false
#print axioms rectangle_image_return_false
end Equation22446Lineage

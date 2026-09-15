prelude
import LineageSyntax.FullImageCoverage
set_option autoImplicit false
set_option Elab.async false

namespace Equation22446Lineage
open Equation22446Guarded

theorem column_two_to_two_inverse {p q : T} (hc : Column p q)
    (hp : ∃ a b, p = S (S (P a b))) (hq : ∃ a b, q = S (S (P a b))) : Image q (S p) := by
  cases hc with
  | ancestry hl =>
      obtain ⟨a,b,hq⟩ := hq
      have he := S_injective (S_injective hq)
      have hp' := lineage_non_phase_two hl (by intro u v h; rw [he] at h; cases h)
      obtain ⟨u,v,hp⟩ := hp
      rw [hp,he] at hp'
      cases hp'
  | literal p y => obtain ⟨a,b,hq⟩ := hq; cases hq
  | inverseImage hi => exact hi

theorem image_phase_two_roots_unique_at_size (n : Nat) :
    ∀ p q b, nodes b = n →
      (∃ u v, p = S (S (P u v))) → (∃ u v, q = S (S (P u v))) →
      Image p b → Image q b → p = q := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      intro p q b hn hp hq hi hj
      obtain ⟨x,y,hp⟩ := hp
      obtain ⟨w,t,hq⟩ := hq
      cases hi with
      | square p =>
          have he := image_nonzero_target hj (by intro u v h; rw [hp] at h; cases h)
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
          | cycleFollowup hs hk hl => cases hq
      | @transport u p v hc hk =>
          generalize he : P u v = b at hj
          cases hj with
          | square q => rw [hq] at he; cases he
          | literal q z =>
              rw [(T.p.inj he).2.1,(T.p.inj he).2.2] at hk
              exact False.elim (image_pair_tail_false hk)
          | transport hd hl =>
              rw [←(T.p.inj he).2.1] at hd
              rcases column_phase_two_base_shape hc ⟨x,y,hp⟩ with ⟨a,b,hu⟩ | ⟨a,b,hu⟩
              · rw [hu,hp] at hc
                rw [hu,hq] at hd
                have hs := (column_zero_to_two hc).symm.trans (column_zero_to_two hd)
                rw [hp,hq,hs]
              · have hi' := column_two_to_two_inverse hc ⟨a,b,hu⟩ ⟨x,y,hp⟩
                have hj' := column_two_to_two_inverse hd ⟨a,b,hu⟩ ⟨w,t,hq⟩
                have hs : nodes (S u) < n := by
                  rw [nodes_S,←hn]
                  exact pair_left .zero u v
                exact ih _ hs p q (S u) rfl ⟨x,y,hp⟩ ⟨w,t,hq⟩ hi' hj'
          | inverseFollowup q => cases hq
          | returnFollowup hl => cases hq
          | cycleFollowup hs hl hm => cases hq
      | inverseFollowup p => cases hp
      | returnFollowup hk => cases hp
      | cycleFollowup hs hk hl => cases hp

theorem image_phase_two_roots_unique {p q b : T}
    (hp : ∃ u v, p = S (S (P u v))) (hq : ∃ u v, q = S (S (P u v)))
    (hi : Image p b) (hj : Image q b) : p = q :=
  image_phase_two_roots_unique_at_size (nodes b) p q b rfl hp hq hi hj

theorem column_phase_two_values_unique {u p q : T}
    (hp : ∃ a b, p = S (S (P a b))) (hq : ∃ a b, q = S (S (P a b)))
    (hc : Column u p) (hd : Column u q) : p = q := by
  rcases column_phase_two_base_shape hc hp with ⟨a,b,hu⟩ | ht
  · obtain ⟨x,y,hp⟩ := hp
    obtain ⟨w,t,hq⟩ := hq
    rw [hu,hp] at hc
    rw [hu,hq] at hd
    have hs := (column_zero_to_two hc).symm.trans (column_zero_to_two hd)
    rw [hp,hq,hs]
  · exact image_phase_two_roots_unique hp hq
      (column_two_to_two_inverse hc ht hp) (column_two_to_two_inverse hd ht hq)

#print axioms column_two_to_two_inverse
#print axioms image_phase_two_roots_unique_at_size
#print axioms image_phase_two_roots_unique
#print axioms column_phase_two_values_unique
end Equation22446Lineage

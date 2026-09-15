prelude
import LineageSyntax.ReturnedFrontier
set_option autoImplicit false
set_option Elab.async false

namespace Equation22446Lineage
open Equation22446Guarded

theorem strict_part_pair_children {a b p : T} (hp : Part (P a b) p)
    (hs : nodes p < nodes (P a b)) : Part a p ∨ Part b p := by
  cases hp with
  | root c t =>
      rw [nodes_rotate] at hs
      exact False.elim (Nat.lt_irrefl _ hs)
  | left c h => exact Or.inl h
  | right c h => exact Or.inr h

/-- The inverse-cycle obstruction that refuted the old syntax is absent
on normal outputs in the new syntax. It is now a theorem, not a hypothesis. -/
theorem normal_inverse_cycle {p b : T} (hb : Normal b)
    (hi : Image p b) (hj : Image b (S p)) : p = S b := by
  classical
  rcases phase_two_or_square_nonzero p with ⟨u,v,hp⟩ | hn
  · by_cases hpair : ∃ a z, b = P a z
    · obtain ⟨a,z,hb'⟩ := hpair
      subst b
      have hs := Nat.lt_of_le_of_lt (image_phase_two_output_left hi u v a z hp rfl)
        (pair_left .zero a z)
      have hv := strict_part_pair_children (image_phase_two_part hi u v hp) hs
      exact False.elim (hb.2.2 ⟨_,.cycleReturn hv hi hj⟩)
    · have he := image_nonzero_output hi (by intro a z he; exact hpair ⟨a,z,he⟩)
      rw [he,cube]
  · exact S_injective (image_nonzero_output hj hn)

theorem raw_double_cycle_target {p z r : T}
    (hi : Image r (P (P p z) z)) (hj : Image (P (P p z) z) (S r))
    (hs : nodes r < nodes (P (P p z) z)) : r = p := by
  obtain ⟨u,v,hr⟩ := cycle_target_phase_two hi hj hs
  generalize hq : P (P p z) z = q at hi
  cases hi with
  | square r => rw [hr] at hq; cases hq
  | literal r t => exact (T.p.inj (T.p.inj hq).2.1).2.1.symm
  | transport hc ht =>
      rw [←(T.p.inj hq).2.1,←(T.p.inj hq).2.2] at ht
      exact False.elim (image_pair_tail_false ht)
  | inverseFollowup t => cases hr
  | returnFollowup ht => cases hr
  | cycleFollowup hs ht hk => cases hr

/-- If the first product is raw, a cycle at the second product returns
exactly S²p, which is already a certified image of p. -/
theorem second_raw_cycle_covered {p z r : T} (hv : Part (P p z) r ∨ Part z r)
    (hi : Image r (P (P p z) z)) (hj : Image (P (P p z) z) (S r)) :
    Image p (S (S r)) := by
  rw [raw_double_cycle_target hi hj (visible_target_smaller hv)]
  exact .square p

#print axioms strict_part_pair_children
#print axioms normal_inverse_cycle
#print axioms raw_double_cycle_target
#print axioms second_raw_cycle_covered
end Equation22446Lineage

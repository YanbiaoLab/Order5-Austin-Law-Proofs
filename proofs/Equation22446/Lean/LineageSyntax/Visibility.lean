prelude
import LineageSyntax.Decoder
set_option autoImplicit false
set_option Elab.async false

namespace Equation22446Lineage
open Equation22446Guarded

theorem part_S_source {t o : T} (h : Part t o) : Part (S t) o := by
  induction h with
  | root c t =>
      cases c with
      | zero =>
          have hp := Part.root .two (S t)
          change Part (S t) (S (S (S t))) at hp
          rwa [cube] at hp
      | one => exact .root .zero (S t)
      | two => exact .root .one (S t)
  | left c h ih => exact .left (next c) h
  | right c h ih => exact .right (next c) h

theorem part_unS_source {t o : T} (h : Part (S t) o) : Part t o := by
  have hp := part_S_source (part_S_source h)
  rwa [cube] at hp

theorem lineage_part {p q : T} (h : Lineage p q) : Part q p :=
  match h with
  | .refl p => .root .zero p
  | .step hl hi => .left .two (lineage_part hl)

mutual
theorem image_phase_two_part {p q : T} (h : Image p q) :
    ∀ a b, p = S (S (P a b)) → Part q p :=
  match h with
  | .square p => by
      intro a b hp
      have hs := Part.root .one (S (S p))
      change Part (S (S p)) (S (S (S p))) at hs
      rwa [cube] at hs
  | .literal p t => by
      intro a b hp
      exact .left .zero (.left .zero (.root .zero p))
  | .transport hc hi => by
      intro a b hp
      exact .left .zero (column_phase_two_part hc a b hp)
  | .inverseFollowup p => by intro a b hp; cases hp
  | .returnFollowup hi => by intro a b hp; cases hp
  | .cycleFollowup hs hi hj => by intro a b hp; cases hp
theorem column_phase_two_part {p a : T} (h : Column p a) :
    ∀ u v, a = S (S (P u v)) → Part p a :=
  match h with
  | .ancestry hl => by
      intro u v ha
      have he := S_injective (S_injective ha)
      have hp := lineage_non_phase_two hl (by intro x y h; rw [he] at h; cases h)
      rw [hp]
      exact .root .two _
  | .literal p y => by intro u v ha; cases ha
  | .inverseImage hi => by
      intro u v ha
      exact part_unS_source (image_phase_two_part hi u v ha)
end

theorem column_visible_unless_phase_two {p a : T} (h : Column p a)
    (hn : ∀ u v, S p ≠ P u v) : Part a p := by
  cases h with
  | ancestry hl => exact part_S_source (part_S_source (lineage_part hl))
  | literal p y =>
      apply Part.right .zero
      have hp := Part.root .two (S p)
      change Part (S p) (S (S (S p))) at hp
      rwa [cube] at hp
  | inverseImage hi =>
      have he := image_nonzero_output hi hn
      have ha := congrArg S he
      rw [cube] at ha
      rw [←ha]
      have hp := Part.root .one (S (S p))
      change Part (S (S p)) (S (S (S p))) at hp
      rwa [cube] at hp

/-- Ancestral columns preserve rectangle target visibility. No Source,
normality, uniqueness, or old triangle theorem is used. -/
theorem rectangle_target_visible {p a b : T} (hc : Column p a) (hi : Image p b) :
    Part a p ∨ Part b p := by
  rcases phase_two_or_square_nonzero p with ⟨u,v,hp⟩ | hn
  · exact Or.inr (image_phase_two_part hi u v hp)
  · exact Or.inl (column_visible_unless_phase_two hc hn)

#print axioms part_S_source
#print axioms part_unS_source
#print axioms lineage_part
#print axioms image_phase_two_part
#print axioms column_phase_two_part
#print axioms column_visible_unless_phase_two
#print axioms rectangle_target_visible
end Equation22446Lineage

prelude
import GuardedSyntax.Tree
set_option autoImplicit false
set_option Elab.async false

namespace Equation22446Lineage
open Equation22446Guarded

/- Independent FREE syntax for the lineage-followup candidate. These are
not the old GuardedSyntax relations, nor Source-conditional certificates. -/
mutual
inductive Image : T → T → Prop where
  | square (p : T) : Image p (S (S p))
  | literal (p t : T) : Image p (P (P p t) t)
  | transport {p a q : T} : Column p a → Image p q → Image a (P p q)
  | inverseFollowup (p : T) : Image (P p (S p)) (P (S (S p)) (S p))
  | returnFollowup {p q : T} : Image p q →
      Image (P (S (S (P p q))) (S p)) (P (S (P p q)) (S p))
  | cycleFollowup {u v w t z : T} :
      nodes (S (S (P w t))) < nodes (P (P u v) z) →
      Image (S (S (P w t))) (P (P u v) z) → Image (P (P u v) z) (P w t) →
      Image (P u v) (P (S (P w t)) z)
inductive Column : T → T → Prop where
  | ancestry {p q : T} : Lineage p q → Column p (S (S q))
  | literal (p y : T) : Column p (P y (S p))
  | inverseImage {p a : T} : Image a (S p) → Column p a
inductive Lineage : T → T → Prop where
  | refl (p : T) : Lineage p p
  | step {p a b : T} : Lineage p a → Image a b → Lineage p (S (S (P a b)))
end

theorem column_canonical (p : T) : Column p (S (S p)) := .ancestry (.refl p)

theorem column_completed {p q : T} (hi : Image p q) : Column p (S (P p q)) :=
  .ancestry (.step (.refl p) hi)

theorem lineage_nodes {p q : T} (h : Lineage p q) : nodes p ≤ nodes q :=
  match h with
  | .refl p => Nat.le_refl _
  | .step hl hi => Nat.le_trans (lineage_nodes hl) (Nat.le_of_lt (pair_left .two _ _))

theorem lineage_non_phase_two {p q : T} (h : Lineage p q)
    (hn : ∀ a b, q ≠ S (S (P a b))) : p = q := by
  cases h with
  | refl => rfl
  | step hl hi => exact False.elim (hn _ _ rfl)

theorem image_nonzero_output {p q : T} (h : Image p q)
    (hn : ∀ a b, q ≠ P a b) : q = S (S p) := by
  cases h with
  | square p => rfl
  | literal p t => exact False.elim (hn _ _ rfl)
  | transport hc hi => exact False.elim (hn _ _ rfl)
  | inverseFollowup p => exact False.elim (hn _ _ rfl)
  | returnFollowup hi => exact False.elim (hn _ _ rfl)
  | cycleFollowup hs hi hj => exact False.elim (hn _ _ rfl)

mutual
theorem image_phase_two_bound {p q : T} (h : Image p q) :
    ∀ a b, p = S (S (P a b)) → nodes p ≤ nodes q :=
  match h with
  | .square p => by intro a b hp; rw [nodes_S,nodes_S]; exact Nat.le_refl _
  | .literal p t => by
      intro a b hp
      exact Nat.le_of_lt (Nat.lt_trans (pair_left .zero _ _) (pair_left .zero _ _))
  | .transport hc hi => by
      intro a b hp
      exact Nat.le_trans (column_phase_two_bound hc a b hp) (Nat.le_of_lt (pair_left .zero _ _))
  | .inverseFollowup p => by intro a b hp; cases hp
  | .returnFollowup hi => by intro a b hp; cases hp
  | .cycleFollowup hs hi hj => by intro a b hp; cases hp
theorem column_phase_two_bound {p a : T} (h : Column p a) :
    ∀ u v, a = S (S (P u v)) → nodes a ≤ nodes p :=
  match h with
  | .ancestry hl => by
      intro u v ha
      have he := S_injective (S_injective ha)
      have hp := lineage_non_phase_two hl (by intro x y h; rw [he] at h; cases h)
      rw [nodes_S,nodes_S,←hp]
      exact Nat.le_refl _
  | .literal p y => by intro u v ha; cases ha
  | .inverseImage hi => by
      intro u v ha
      have hb := image_phase_two_bound hi u v ha
      rwa [nodes_S] at hb
end

theorem image_phase_two_output_left {p q : T} (h : Image p q) :
    ∀ a b u v, p = S (S (P a b)) → q = P u v → nodes p ≤ nodes u := by
  intro a b u v hp hq
  cases h with
  | square p => rw [hp] at hq; cases hq
  | literal p t =>
      rw [←(T.p.inj hq).2.1]
      exact Nat.le_of_lt (pair_left .zero _ _)
  | transport hc hi =>
      rw [←(T.p.inj hq).2.1]
      exact column_phase_two_bound hc a b hp
  | inverseFollowup p => cases hp
  | returnFollowup hi => cases hp
  | cycleFollowup hs hi hj => cases hp

#print axioms column_canonical
#print axioms column_completed
#print axioms lineage_nodes
#print axioms lineage_non_phase_two
#print axioms image_nonzero_output
#print axioms image_phase_two_bound
#print axioms column_phase_two_bound
#print axioms image_phase_two_output_left
end Equation22446Lineage

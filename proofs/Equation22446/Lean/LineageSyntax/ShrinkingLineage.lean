prelude
import LineageSyntax.Relations
set_option autoImplicit false
set_option Elab.async false

namespace Equation22446Lineage
open Equation22446Guarded

theorem column_zero_to_two {a b u v : T}
    (h : Column (P a b) (S (S (P u v)))) : P a b = P u v := by
  generalize ha : S (S (P u v)) = x at h
  cases h with
  | ancestry hl =>
      have he := S_injective (S_injective ha)
      have hp := lineage_non_phase_two hl (by intro x y h; rw [←he] at h; cases h)
      exact hp.trans he.symm
  | literal p y => cases ha
  | inverseImage hi =>
      rw [←ha] at hi
      have he := image_nonzero_output hi (by intro x y he; cases he)
      rw [cube] at he
      exact S_injective he

theorem cycle_followup_size_bound {u v w t z : T}
    (h : Image (S (S (P w t))) (P (P u v) z)) :
    nodes (P u v) ≤ nodes (P (S (P w t)) z) := by
  generalize hp : S (S (P w t)) = p at h
  generalize hq : P (P u v) z = q at h
  cases h with
  | square p => rw [←hp] at hq; cases hq
  | literal p y =>
      have he := (T.p.inj hq).2.1
      have hz := (T.p.inj hq).2.2
      rw [he,hz,←hp]
      exact Nat.le_refl _
  | @transport p a q hc hi =>
      have he := (T.p.inj hq).2.1
      rw [←hp,←he] at hc
      have eq := column_zero_to_two hc
      rw [eq]
      exact Nat.le_of_lt (pair_left .zero _ _)
  | inverseFollowup p => cases hp
  | returnFollowup hi => cases hp
  | cycleFollowup hs hi hj => cases hp

/- Shrinking a zero-color pair through an image or column certificate
exposes an ancestry path from the inverse square of its right child. -/
mutual
theorem image_shrinking_lineage {p q : T} (h : Image p q) :
    ∀ u v, p = P u v → nodes q < nodes p → Lineage (S (S v)) (S (S q)) :=
  match h with
  | .square p => by
      intro u v hp hs
      rw [nodes_S,nodes_S] at hs
      exact False.elim (Nat.lt_irrefl _ hs)
  | .literal p t => by
      intro u v hp hs
      exact False.elim (Nat.lt_irrefl _ (Nat.lt_trans
        (Nat.lt_trans (pair_left .zero _ _) (pair_left .zero _ _)) hs))
  | .transport hc hi => by
      intro u v hp hs
      exact .step (column_shrinking_lineage hc u v hp
        (Nat.lt_trans (pair_left .zero _ _) hs)) hi
  | .inverseFollowup p => by
      intro u v hp hs
      have he : nodes (P (S (S p)) (S p)) = nodes (P p (S p)) := by
        simp only [P,nodes,nodes_S]
      rw [he] at hs
      exact False.elim (Nat.lt_irrefl _ hs)
  | .returnFollowup hi => by
      intro u v hp hs
      simp only [P,nodes,nodes_S] at hs
      exact False.elim (Nat.lt_irrefl _ hs)
  | .cycleFollowup ht hi hj => by
      intro u v hp hs
      exact False.elim (Nat.not_lt_of_ge (cycle_followup_size_bound hi) hs)
theorem column_shrinking_lineage {p a : T} (h : Column p a) :
    ∀ u v, a = P u v → nodes p < nodes a → Lineage (S (S v)) p :=
  match h with
  | .ancestry hl => by
      intro u v ha hs
      have he := congrArg S ha
      rw [cube] at he
      have hp := lineage_non_phase_two hl (by intro x y h; rw [he] at h; cases h)
      rw [hp,nodes_S,nodes_S] at hs
      exact False.elim (Nat.lt_irrefl _ hs)
  | .literal p y => by
      intro u v ha hs
      rw [←(T.p.inj ha).2.2,cube]
      exact .refl p
  | .inverseImage hi => by
      intro u v ha hs
      have ht := image_shrinking_lineage hi u v ha (by rwa [nodes_S])
      rwa [cube] at ht
end

#print axioms column_zero_to_two
#print axioms cycle_followup_size_bound
#print axioms image_shrinking_lineage
#print axioms column_shrinking_lineage
end Equation22446Lineage

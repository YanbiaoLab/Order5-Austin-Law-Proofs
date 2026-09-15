prelude
import LineageSyntax.ColumnTriangleFrontier
set_option autoImplicit false
set_option Elab.async false

namespace Equation22446Lineage
open Equation22446Guarded

mutual
theorem image_lineage_next_false {p q : T} (h : Image p q) :
    ∀ r, q = S r → Lineage p r → False :=
  match h with
  | .square p => by
      intro r he hl
      rw [←S_injective he] at hl
      have hp := lineage_nonincreasing_eq hl (by rw [nodes_S]; exact Nat.le_refl _)
      exact S_ne p hp.symm
  | .literal p z => by
      intro r he hl
      cases hl with
      | refl => exact image_no_successor (he ▸ Image.literal p z)
      | @step p a b hl hi =>
          simp only [cube] at he
          rw [←(T.p.inj he).2.1] at hl
          have hp := lineage_non_phase_two hl (by intro u v h; cases h)
          exact Nat.ne_of_lt (pair_left .zero p z) (congrArg nodes hp)
  | .transport hc hi => by
      intro r he hl
      cases hl with
      | refl => exact image_no_successor (he ▸ Image.transport hc hi)
      | @step p a b hl hj =>
          simp only [cube] at he
          rw [←(T.p.inj he).2.1] at hl
          exact column_lineage_reverse_false hc hl
  | .inverseFollowup p => by
      intro r he hl
      cases hl with
      | refl => exact image_no_successor (he ▸ Image.inverseFollowup p)
      | @step u a b hl hi =>
          simp only [cube] at he
          rw [←(T.p.inj he).2.1] at hl
          have hs := lineage_nodes hl
          simp only [nodes_S] at hs
          exact Nat.not_lt_of_ge hs (pair_left .zero p (S p))
  | .returnFollowup hi => by
      intro r he hl
      cases hl with
      | refl => exact image_no_successor (he ▸ Image.returnFollowup hi)
      | @step p a b hl hj =>
          simp only [cube] at he
          rw [←(T.p.inj he).2.1] at hl
          have hp := lineage_non_phase_two hl (by intro u v h; cases h)
          cases hp
  | .cycleFollowup hs hi hj => by
      intro r he hl
      cases hl with
      | refl => exact image_no_successor (he ▸ Image.cycleFollowup hs hi hj)
      | @step p a b hl hk =>
          simp only [cube] at he
          rw [←(T.p.inj he).2.1] at hl
          have hp := lineage_non_phase_two hl (by intro u v h; cases h)
          cases hp
theorem column_lineage_reverse_false {p a : T} (h : Column p a)
    (hl : Lineage a p) : False :=
  match h with
  | .ancestry hm => by
      have hs := lineage_nodes hl
      simp only [nodes_S] at hs
      have hp := lineage_nonincreasing_eq hm hs
      rw [←hp] at hl
      have he := lineage_nonincreasing_eq hl (by simp only [nodes_S]; exact Nat.le_refl _)
      exact SS_ne p he
  | .literal p y => by
      have hs := lineage_nodes hl
      have hb := pair_right .zero y (S p)
      change nodes (S p) < nodes (P y (S p)) at hb
      rw [nodes_S] at hb
      exact Nat.not_lt_of_ge hs hb
  | .inverseImage hi => image_lineage_next_false hi _ rfl hl
end

#print axioms image_lineage_next_false
#print axioms column_lineage_reverse_false
end Equation22446Lineage

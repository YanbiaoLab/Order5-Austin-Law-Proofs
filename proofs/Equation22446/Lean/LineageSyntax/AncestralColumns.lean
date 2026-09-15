prelude
import LineageSyntax.RotatedAncestry
set_option autoImplicit false
set_option Elab.async false

namespace Equation22446Lineage
open Equation22446Guarded

theorem column_adjacent_bases_false {p a : T} (hc : Column p a)
    (hd : Column (S (S p)) a) : False := by
  cases hc with
  | ancestry hl => exact lineage_inverse_column_false hl hd
  | literal p y => exact column_pair_successor_tail_false hd
  | inverseImage hi => exact column_square_image_false hd (by simpa only [cube] using hi)

theorem lineage_shifted_image_false {p r : T} (hl : Lineage p r)
    (hi : Image (S r) (S p)) : False := by
  cases hl with
  | refl => exact image_no_self hi
  | @step p a b hl hj =>
      simp only [cube] at hi
      have hs : nodes p < nodes (P a b) :=
        Nat.lt_of_le_of_lt (lineage_nodes hl) (pair_left .zero a b)
      have hm := shrinking_inverse_lineage hi hs
      exact lineage_image_inverse_false hj (lineage_trans hm hl)

theorem lineage_shifted_endpoints_false {p r : T} (hl : Lineage p r)
    (hm : Lineage p (S (S r))) : False := by
  cases hl with
  | refl =>
      have he := lineage_nonincreasing_eq hm (by simp only [nodes_S]; exact Nat.le_refl _)
      exact SS_ne p he.symm
  | @step p a b hl hi =>
      simp only [cube] at hm
      have he := lineage_non_phase_two hm (by intro u v h; cases h)
      have hs := lineage_nodes hl
      rw [he,nodes_S] at hs
      exact Nat.not_lt_of_ge hs (pair_left .zero a b)

theorem lineage_successor_column_false {p r : T} (hl : Lineage p r)
    (hc : Column p (S r)) : False := by
  generalize ha : S r = a at hc
  cases hc with
  | ancestry hm =>
      have he := congrArg (fun t => S (S t)) ha
      simp only [cube] at he
      have he' := congrArg (fun t => S (S t)) he
      simp only [cube] at he'
      rw [←he'] at hm
      exact lineage_shifted_endpoints_false hl hm
  | literal p y =>
      have he := congrArg (fun t => S (S t)) ha
      simp only [cube] at he
      cases hl with
      | refl =>
          have hs := congrArg nodes he
          simp only [nodes_S] at hs
          have hb := pair_right .zero y (S p)
          change nodes (S p) < nodes (P y (S p)) at hb
          simp only [nodes_S] at hb
          omega
      | @step p u v hm hi =>
          have hv := (T.p.inj (S_injective (S_injective he))).2.2
          rw [hv] at hi
          exact lineage_image_inverse_false hi (by simpa only [cube] using hm)
  | inverseImage hi =>
      rw [←ha] at hi
      exact lineage_shifted_image_false hl hi

#print axioms column_adjacent_bases_false
#print axioms lineage_shifted_image_false
#print axioms lineage_shifted_endpoints_false
#print axioms lineage_successor_column_false
end Equation22446Lineage

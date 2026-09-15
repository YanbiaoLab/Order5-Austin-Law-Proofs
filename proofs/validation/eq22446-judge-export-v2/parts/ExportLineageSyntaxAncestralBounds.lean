prelude
import Init.Classical
import Init.Data.Nat.Lemmas
import Init.RCases
import ExportLineageSyntaxPhaseOneOrigins
set_option Elab.async false
set_option autoImplicit false
set_option Elab.async false

namespace submission.Equation22446Lineage
open submission.Equation22446Guarded

theorem lineage_common_size_unique {p q r : T} (hl : Lineage p r) (hm : Lineage q r)
    (hs : nodes p = nodes q) : p = q :=
  match hl with
  | .refl p => (lineage_nonincreasing_eq hm (Nat.le_of_eq hs)).symm
  | .step hl hi => by
      cases hm with
      | refl => exact lineage_nonincreasing_eq (.step hl hi) (Nat.le_of_eq hs.symm)
      | step hm hj => exact lineage_common_size_unique hl hm hs

theorem non_two_lineage_common_lower {p q r : T}
    (hp : ∀ u v, p ≠ S (S (P u v))) (hl : Lineage p r) (hm : Lineage q r) :
    nodes p ≤ nodes q :=
  match hl with
  | .refl p => by rw [lineage_non_phase_two hm hp]; exact Nat.le_refl _
  | .step hl hi => by
      cases hm with
      | refl => exact lineage_nodes (.step hl hi)
      | step hm hj => exact non_two_lineage_common_lower hp hl hm

 

mutual
theorem image_ancestor_bound {p q : T} (h : Image p q) :
    ∀ a u v, p = S (P u v) → (∀ x y, a ≠ S (S (P x y))) → Lineage a u → nodes a < nodes q :=
  match h with
  | .square p => by
      intro a u v hp ha hl
      rw [nodes_S,nodes_S,hp,nodes_S]
      exact Nat.lt_of_le_of_lt (lineage_nodes hl) (pair_left .zero u v)
  | .literal p z => by
      intro a u v hp ha hl
      have hs : nodes a < nodes p := by
        rw [hp,nodes_S]
        exact Nat.lt_of_le_of_lt (lineage_nodes hl) (pair_left .zero u v)
      exact Nat.lt_trans hs (Nat.lt_trans (pair_left .zero _ _) (pair_left .zero _ _))
  | .transport hc hi => by
      intro a u v hp ha hl
      exact Nat.lt_of_le_of_lt (column_ancestor_bound hc a u v hp ha hl) (pair_left .zero _ _)
  | .inverseFollowup p => by intro a u v hp ha hl; cases hp
  | .returnFollowup hi => by intro a u v hp ha hl; cases hp
  | .cycleFollowup hs hi hj => by intro a u v hp ha hl; cases hp
theorem column_ancestor_bound {p q : T} (h : Column p q) :
    ∀ a u v, q = S (P u v) → (∀ x y, a ≠ S (S (P x y))) → Lineage a u → nodes a ≤ nodes p :=
  match h with
  | .ancestry hm => by
      intro a u v hq ha hl
      cases hm with
      | refl =>
          have hp := congrArg S hq
          rw [cube] at hp
          rw [hp,nodes_S,nodes_S]
          exact Nat.le_trans (lineage_nodes hl) (Nat.le_of_lt (pair_left .zero u v))
      | step hm hi =>
          simp only [cube] at hq
          have he := S_injective hq
          rw [(T.p.inj he).2.1] at hm
          exact non_two_lineage_common_lower ha hl hm
  | .literal p y => by intro a u v hq ha hl; cases hq
  | .inverseImage hi => by
      intro a u v hq ha hl
      have hs := image_ancestor_bound hi a u v hq ha hl
      rw [nodes_S] at hs
      exact Nat.le_of_lt hs
end

end submission.Equation22446Lineage

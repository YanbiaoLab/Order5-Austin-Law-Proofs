prelude
import Init.Classical
import Init.Data.Nat.Lemmas
import Init.RCases
import ExportLineageSyntaxLineageForward
set_option Elab.async false
set_option autoImplicit false
set_option Elab.async false

namespace submission.Equation22446Lineage
open submission.Equation22446Guarded

theorem lineage_common_comparable {p q r : T} (hp : Lineage p r) (hq : Lineage q r) :
    Lineage p q ∨ Lineage q p :=
  match hp with
  | .refl p => Or.inr hq
  | .step hp hi => by
      cases hq with
      | refl => exact Or.inl (.step hp hi)
      | step hq hj => exact lineage_common_comparable hp hq

theorem column_lineage_forward_false {p a : T} (hc : Column p a)
    (hl : Lineage p a) : False := by
  cases hl with
  | refl => exact column_no_self hc
  | @step p u v hl hi =>
      have hs := column_phase_two_bound hc u v rfl
      have hb := lineage_nodes hl
      have ht := pair_left .two u v
      exact Nat.not_lt_of_ge hs (Nat.lt_of_le_of_lt hb ht)

theorem common_lineage_column_false {p q r : T} (hp : Lineage p r) (hq : Lineage q r)
    (hc : Column p q) : False := by
  rcases lineage_common_comparable hp hq with hl | hl
  · exact column_lineage_forward_false hc hl
  · exact column_lineage_reverse_false hc hl

theorem column_triangle_base_phase_two {u p a : T}
    (hup : Column u p) (hpa : Column p a) (hua : Column u a) :
    ∃ x y, u = S (S (P x y)) := by
  rcases phase_two_or_square_nonzero u with hu | hn
  · exact hu
  · have hi := column_triangle_inverse_origin hup hpa hua
    have hp := image_nonzero_target hi hn
    rw [hp] at hpa
    exact False.elim (column_adjacent_bases_false hua hpa)

end submission.Equation22446Lineage

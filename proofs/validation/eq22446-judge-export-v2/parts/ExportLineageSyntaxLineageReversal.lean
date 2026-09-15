prelude
import Init.Classical
import Init.Data.Nat.Lemmas
import Init.RCases
import ExportLineageSyntaxAncestralBounds
set_option Elab.async false
set_option autoImplicit false
set_option Elab.async false

namespace submission.Equation22446Lineage
open submission.Equation22446Guarded

theorem lineage_inverse_image_false {p r : T} (hl : Lineage p r)
    (hi : Image (S (S r)) p) : False := by
  cases hl with
  | refl => exact image_no_successor (p := S (S p)) (by simpa only [cube] using hi)
  | @step p a b hl hj =>
      simp only [cube] at hi
      rcases phase_two_or_square_nonzero p with ⟨u,v,hp⟩ | hn
      · have he := image_nonzero_output hi (by intro x y h; rw [hp] at h; cases h)
        simp only [cube] at he
        rw [hp] at he
        cases he
      · have ha : ∀ x y, p ≠ S (S (P x y)) := by
          intro x y hp
          apply hn x y
          rw [hp,cube]
        exact Nat.lt_irrefl _ (image_ancestor_bound hi p a b rfl ha hl)

theorem lineage_inverse_column_false {p r : T} (hl : Lineage p r)
    (hc : Column (S (S p)) (S (S r))) : False := by
  generalize ha : S (S r) = a at hc
  cases hc with
  | ancestry hm =>
      have he := S_injective (S_injective ha)
      rw [←he] at hm
      have hp := lineage_common_size_unique hl hm (by rw [nodes_S,nodes_S])
      exact SS_ne p hp.symm
  | literal q y =>
      have he := congrArg S ha
      simp only [cube] at he
      have hp := lineage_non_phase_two hl (by intro x z h; rw [he] at h; cases h)
      have eq := hp.trans he
      have hs := congrArg nodes eq
      rw [nodes_S] at hs
      exact Nat.ne_of_lt (pair_right .zero y p) hs
  | inverseImage hi =>
      rw [←ha,cube] at hi
      exact lineage_inverse_image_false hl hi

theorem column_self_eq_false {p a : T} (hc : Column p a) (ha : a = p) : False := by
  cases hc with
  | ancestry hl =>
      have hs := congrArg nodes ha
      rw [nodes_S,nodes_S] at hs
      have he := lineage_nonincreasing_eq hl (Nat.le_of_eq hs)
      rw [←he] at ha
      exact SS_ne p ha
  | literal p y =>
      have hs := congrArg nodes ha
      have hb := pair_right .zero y (S p)
      change nodes (S p) < nodes (P y (S p)) at hb
      rw [nodes_S,hs] at hb
      exact Nat.lt_irrefl _ hb
  | inverseImage hi => rw [ha] at hi; exact image_no_successor hi

theorem column_no_self {p : T} (hc : Column p p) : False := column_self_eq_false hc rfl

end submission.Equation22446Lineage

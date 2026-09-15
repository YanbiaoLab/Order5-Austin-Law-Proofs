prelude
import LineageSyntax.AncestralColumns
set_option autoImplicit false
set_option Elab.async false

namespace Equation22446Lineage
open Equation22446Guarded

theorem ancestral_column_triangle_false {u q a : T} (hl : Lineage u q)
    (hq : Column (S (S q)) a) (hu : Column u a) : False := by
  classical
  by_cases he : u = q
  · subst q
    exact column_adjacent_bases_false hu hq
  · have hs : nodes u < nodes q := by
      apply Nat.lt_of_not_ge
      intro hn
      exact he (lineage_nonincreasing_eq hl hn)
    have ht : ∃ x y, q = S (S (P x y)) := by
      cases hl with
      | refl => exact False.elim (he rfl)
      | step hl hi => exact ⟨_,_,rfl⟩
    have hn : ∀ x y, S (S q) ≠ S (S (P x y)) := by
      obtain ⟨v,w,hq'⟩ := ht
      intro x y h
      rw [hq'] at h
      cases h
    cases hq with
    | ancestry hm =>
        cases hm with
        | refl =>
            exact lineage_successor_column_false hl (by simpa only [cube] using hu)
        | @step p r s hm hi =>
            simp only [cube] at hu
            have hb := column_ancestor_bound hu (S (S q)) r s rfl hn hm
            simp only [nodes_S] at hb
            exact Nat.not_lt_of_ge hb hs
    | literal p y =>
        have hb := column_right_child hu .zero y (S (S (S q))) (by intro h; cases h) rfl
        simp only [nodes_S] at hb
        exact Nat.not_lt_of_ge hb hs
    | inverseImage hi =>
        simp only [cube] at hi
        have ha := image_nonzero_target hi (by
          obtain ⟨v,w,hq'⟩ := ht
          intro x y h
          rw [hq'] at h
          cases h)
        rw [ha] at hu
        exact lineage_successor_column_false hl hu

theorem literal_column_triangle_false {u y a : T}
    (hp : Column (P y (S u)) a) (hu : Column u a) : False := by
  have hs := shared_column_phase_zero_bound hp hu
  have hb := pair_right .zero y (S u)
  change nodes (S u) < nodes (P y (S u)) at hb
  rw [nodes_S] at hb
  exact Nat.not_lt_of_ge hs hb

/-- Any surviving CT must use the inverse-image clause for its first edge. -/
theorem column_triangle_inverse_origin {u p a : T}
    (hup : Column u p) (hpa : Column p a) (hua : Column u a) : Image p (S u) := by
  cases hup with
  | ancestry hl => exact False.elim (ancestral_column_triangle_false hl hpa hua)
  | literal u y => exact False.elim (literal_column_triangle_false hpa hua)
  | inverseImage hi => exact hi

#print axioms ancestral_column_triangle_false
#print axioms literal_column_triangle_false
#print axioms column_triangle_inverse_origin
end Equation22446Lineage

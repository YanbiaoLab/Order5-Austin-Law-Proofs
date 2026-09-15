prelude
import Init.Classical
import Init.Data.Nat.Lemmas
import Init.RCases
import ExportLineageSyntaxShrinkingLineage
set_option Elab.async false
set_option autoImplicit false
set_option Elab.async false

namespace submission.Equation22446Lineage
open submission.Equation22446Guarded

theorem shrinking_inverse_lineage {a b p : T} (hi : Image (P a b) (S p))
    (hs : nodes p < nodes (P a b)) : Lineage (S (S b)) p := by
  have h := image_shrinking_lineage hi a b rfl (by rwa [nodes_S])
  rwa [cube] at h

theorem cycle_return_column {a b p : T} (hp : Part a p ∨ Part b p)
    (hi : Image (P a b) (S p)) : Column (S (S b)) (S (S p)) :=
  .ancestry (shrinking_inverse_lineage hi (visible_target_smaller hp))

 

theorem guard_column {a b o : T} (h : Guard a b o) :
    ∀ p, b = S p → Column p o := by
  intro p hb
  cases h with
  | rectangle hp hc hi =>
      rw [hb] at hi
      exact .inverseImage hi
  | inverseDouble v =>
      rw [S_injective hb]
      exact column_canonical p
  | imageReturn hi =>
      rw [S_injective hb] at hi ⊢
      exact column_completed hi
  | cycleReturn hp hi hj =>
      have hc := cycle_return_column hp hj
      rwa [hb,cube] at hc

theorem product_column {p y a : T} (h : Product y (S p) a) : Column p a := by
  cases h with
  | raw hn => exact .literal p y
  | hit hg => exact guard_column hg p rfl

theorem chosen_column (p y : T) : Column p (chosen y (S p)) :=
  product_column (chosen_product y (S p))

end submission.Equation22446Lineage

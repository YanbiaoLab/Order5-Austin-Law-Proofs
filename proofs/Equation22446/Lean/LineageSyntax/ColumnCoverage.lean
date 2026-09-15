prelude
import LineageSyntax.RawCoverage
import LineageSyntax.ShrinkingLineage
set_option autoImplicit false
set_option Elab.async false

namespace Equation22446Lineage
open Equation22446Guarded

theorem shrinking_inverse_lineage {a b p : T} (hi : Image (P a b) (S p))
    (hs : nodes p < nodes (P a b)) : Lineage (S (S b)) p := by
  have h := image_shrinking_lineage hi a b rfl (by rwa [nodes_S])
  rwa [cube] at h

theorem cycle_return_column {a b p : T} (hp : Part a p ∨ Part b p)
    (hi : Image (P a b) (S p)) : Column (S (S b)) (S (S p)) :=
  .ancestry (shrinking_inverse_lineage hi (visible_target_smaller hp))

/-- All four guard constructors preserve the square column, even without
normality assumptions. The cycle branch uses shrinking ancestry. -/
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

#print axioms shrinking_inverse_lineage
#print axioms cycle_return_column
#print axioms guard_column
#print axioms product_column
#print axioms chosen_column
end Equation22446Lineage

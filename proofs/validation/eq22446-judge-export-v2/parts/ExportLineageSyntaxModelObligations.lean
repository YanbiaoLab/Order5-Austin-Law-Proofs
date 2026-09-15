prelude
import Init.Classical
import Init.Data.Nat.Lemmas
import Init.RCases
import ExportLineageSyntaxCleanTower
set_option Elab.async false
set_option autoImplicit false
set_option Elab.async false

namespace submission.Equation22446Lineage
open submission.Equation22446Guarded

 

def GuardUnique : Prop := ∀ {a b u v : T}, Normal a → Normal b →
  Guard a b u → Guard a b v → u = v

def ReturnedImageCovered : Prop := ∀ {p z u b : T}, Normal p → Normal z →
  Product p z u → Guard u z b → Image p b

theorem chosen_of_guard (hu : GuardUnique) {a b o : T} (ha : Normal a) (hb : Normal b)
    (hg : Guard a b o) : chosen a b = o := by
  have hp := chosen_product a b
  generalize ho : chosen a b = v at hp ⊢
  cases hp with
  | raw hn => exact False.elim (hn ⟨o,hg⟩)
  | hit h => exact hu ha hb h hg

theorem chosen_square (hu : GuardUnique) {x : T} (hx : Normal x) : chosen x x = S x :=
  chosen_of_guard hu hx hx (diagonal_guard x)

theorem chosen_double_image (hd : ReturnedImageCovered) {p z : T}
    (hp : Normal p) (hz : Normal z) : Image p (chosen (chosen p z) z) := by
  have h1 := chosen_product p z
  have h2 := chosen_product (chosen p z) z
  generalize ho : chosen (chosen p z) z = b at h2 ⊢
  cases h2 with
  | raw hn => exact product_raw_followup h1
  | hit hg => exact hd hp hz h1 hg

theorem chosen_source (hu : GuardUnique) (hd : ReturnedImageCovered)
    {x y z : T} (hx : Normal x) (hy : Normal y) (hz : Normal z) :
    x = chosen (chosen y (chosen x x)) (chosen (chosen x z) z) := by
  rw [chosen_square hu hx]
  have hs : Normal (S x) := (normal_rotate .one x).mpr hx
  have ha := chosen_normal hy hs
  have hb := chosen_normal (chosen_normal hx hz) hz
  have hc := chosen_column x y
  have hi := chosen_double_image hd hx hz
  have hg := Guard.rectangle (rectangle_target_visible hc hi) hc hi
  exact (chosen_of_guard hu ha hb hg).symm

theorem normal_tree_source (hu : GuardUnique) (hd : ReturnedImageCovered) :
    ∀ x y z : NormalTree,
      x = multiplication (multiplication y (multiplication x x))
        (multiplication (multiplication x z) z) := by
  intro x y z
  apply Subtype.ext
  exact chosen_source hu hd x.property y.property z.property

 
theorem infinite_model_if (hu : GuardUnique) (hd : ReturnedImageCovered) :
    (∀ x y z : NormalTree,
      x = multiplication (multiplication y (multiplication x x))
        (multiplication (multiplication x z) z)) ∧
    (∀ {a b : Nat}, normalTower a = normalTower b → a = b) :=
  ⟨normal_tree_source hu hd,normalTower_injective⟩

end submission.Equation22446Lineage

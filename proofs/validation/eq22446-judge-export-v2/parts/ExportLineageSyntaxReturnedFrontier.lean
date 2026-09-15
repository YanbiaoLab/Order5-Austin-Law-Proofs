prelude
import Init.Classical
import Init.Data.Nat.Lemmas
import Init.RCases
import ExportLineageSyntaxModelObligations
set_option Elab.async false
set_option autoImplicit false
set_option Elab.async false

namespace submission.Equation22446Lineage
open submission.Equation22446Guarded

theorem image_pair_tail_false {a b : T} (h : Image (P a b) b) : False := by
  have hb := image_right_child h .zero a b (by intro h; cases h) rfl
  exact Nat.lt_irrefl _ hb

theorem guard_pair_tail_false {a b o : T} (h : Guard a b o) :
    ∀ v, o = P v b → False := by
  intro v he
  cases h with
  | rectangle hp hc hi => rw [he] at hi; exact image_pair_tail_false hi
  | inverseDouble p =>
      have hn := congrArg nodes he
      have hs := pair_right .zero v (S p)
      change nodes (S p) < nodes (P v (S p)) at hs
      rw [nodes_S,nodes_S] at hn
      rw [nodes_S,←hn] at hs
      exact Nat.lt_irrefl _ hs
  | imageReturn hi => cases he
  | cycleReturn hp hi hj =>
      obtain ⟨u,w,hr⟩ := cycle_target_phase_two hi hj (visible_target_smaller hp)
      rw [hr] at he
      cases he

theorem product_pair_tail_root {a b o : T} (h : Product a b o) :
    ∀ v, o = P v b → a = v := by
  intro v he
  cases h with
  | raw hn => exact (T.p.inj he).2.1
  | hit hg => exact False.elim (guard_pair_tail_false hg v he)

theorem second_inverse_covered {p v : T} (h : Product p (S v) (P v (S v))) :
    Image p (S (S v)) := by
  rw [product_pair_tail_root h v rfl]
  exact .square v

theorem second_return_covered {p v q : T}
    (h : Product p (S v) (P (S (S (P v q))) (S v))) : Image p (S (P v q)) := by
  rw [product_pair_tail_root h (S (S (P v q))) rfl]
  have hi := Image.square (S (S (P v q)))
  rwa [cube] at hi

def RectangleReturnCovered : Prop := ∀ {p z u b : T}, Normal p → Normal z →
  Product p z u → (Part u b ∨ Part z b) → Column b u → Image b z → Image p b

def CycleReturnCovered : Prop := ∀ {p z u r : T}, Normal p → Normal z →
  Product p z u → (Part u r ∨ Part z r) → Image r (P u z) →
  Image (P u z) (S r) → Image p (S (S r))

theorem returned_coverage_of_rectangle_cycle
    (hr : RectangleReturnCovered) (hc : CycleReturnCovered) : ReturnedImageCovered := by
  intro p z u b hp hz hm hg
  cases hg with
  | rectangle hv hc' hi => exact hr hp hz hm hv hc' hi
  | inverseDouble v => exact second_inverse_covered hm
  | imageReturn hi => exact second_return_covered hm
  | cycleReturn hv hi hj => exact hc hp hz hm hv hi hj

theorem returned_coverage_iff_rectangle_cycle :
    ReturnedImageCovered ↔ RectangleReturnCovered ∧ CycleReturnCovered := by
  constructor
  · intro hd
    constructor
    · intro p z u b hp hz hm hv hc hi
      exact hd hp hz hm (.rectangle hv hc hi)
    · intro p z u r hp hz hm hv hi hj
      exact hd hp hz hm (.cycleReturn hv hi hj)
  · rintro ⟨hr,hc⟩
    exact returned_coverage_of_rectangle_cycle hr hc

end submission.Equation22446Lineage

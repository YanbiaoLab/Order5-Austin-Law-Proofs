prelude
import Init.Classical
import Init.Data.Nat.Lemmas
import Init.RCases
import ExportLineageSyntaxPrincipalPairs
set_option Elab.async false
set_option autoImplicit false
set_option Elab.async false

namespace submission.Equation22446Lineage
open submission.Equation22446Guarded

 

theorem cycle_target_literal {a b r : T} (hi : Image r (P a b))
    (hj : Image (P a b) (S r)) (hs : nodes r < nodes (P a b)) : a = P r b := by
  rcases cycle_target_alternatives hi hj hs with he | ⟨he,hk⟩
  · exact he
  · rw [he,cube] at hj
    exact False.elim (image_pair_flip_false hk hj)

theorem rectangle_cycle_false {p a b r : T} (hc : Column p a) (hi : Image p b)
    (hv : Part a r ∨ Part b r) (hj : Image r (P a b)) (hk : Image (P a b) (S r)) : False := by
  have hs := visible_target_smaller hv
  have he := cycle_target_literal hj hk hs
  obtain ⟨u,v,hr⟩ := cycle_target_phase_two hj hk hs
  rw [he] at hc
  have ht := image_phase_two_bound (principal_pair_inner_image hc hi) u v hr
  have hb := image_right_child hk .zero a b (by intro h; cases h) rfl
  rw [nodes_S] at hb
  exact Nat.not_lt_of_ge ht hb

theorem rectangle_special_false {p a b o : T} (hc : Column p a) (hi : Image p b)
    (hg : SpecialGuard a b o) : False := by
  cases hg with
  | inverseDouble v => exact rectangle_inverse_double_false hc hi
  | imageReturn ht => exact rectangle_image_return_false hc hi
  | cycleReturn hv ht hk => exact rectangle_cycle_false hc hi hv ht hk

def PrincipalUnique : Prop := ∀ {a b p q : T}, Normal a → Normal b →
  Column p a → Image p b → Column q a → Image q b → p = q

theorem rectangle_guard_unique_of_principal (hu : PrincipalUnique) : RectangleGuardUnique := by
  intro p a b o ha hb hc hi hg
  rcases guard_rectangle_or_special hg with ⟨hv,hc',hi'⟩ | hs
  · exact hu ha hb hc hi hc' hi'
  · exact False.elim (rectangle_special_false hc hi hs)

theorem principal_of_rectangle_guard_unique (hu : RectangleGuardUnique) : PrincipalUnique := by
  intro a b p q ha hb hc hi hc' hi'
  exact hu ha hb hc hi (.rectangle (rectangle_target_visible hc' hi') hc' hi')

theorem guard_unique_iff_principal : GuardUnique ↔ PrincipalUnique := by
  constructor
  · intro h
    exact principal_of_rectangle_guard_unique (rectangle_unique_of_guard h)
  · intro h
    exact guard_unique_of_rectangle (rectangle_guard_unique_of_principal h)

theorem source_from_principal_conditions (hu : PrincipalUnique) (hr : RectangleReturnCovered) :
    ∀ x y z : NormalTree,
      x = multiplication (multiplication y (multiplication x x))
        (multiplication (multiplication x z) z) :=
  source_from_rectangle_conditions (rectangle_guard_unique_of_principal hu) hr

end submission.Equation22446Lineage

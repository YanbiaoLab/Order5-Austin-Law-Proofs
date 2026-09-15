prelude
import Init.Classical
import Init.Data.Nat.Lemmas
import Init.RCases
import ExportLineageSyntaxCycleUniqueness
set_option Elab.async false
set_option autoImplicit false
set_option Elab.async false

namespace submission.Equation22446Lineage
open submission.Equation22446Guarded

inductive SpecialGuard : T → T → T → Prop where
  | inverseDouble (p : T) : SpecialGuard (P p (S p)) (S p) (S (S p))
  | imageReturn {p q : T} : Image p q →
      SpecialGuard (P (S (S (P p q))) (S p)) (S p) (S (P p q))
  | cycleReturn {p a b : T} : (Part a p ∨ Part b p) →
      Image p (P a b) → Image (P a b) (S p) → SpecialGuard a b (S (S p))

theorem special_guard {a b o : T} (h : SpecialGuard a b o) : Guard a b o := by
  cases h with
  | inverseDouble p => exact .inverseDouble p
  | imageReturn hi => exact .imageReturn hi
  | cycleReturn hv hi hj => exact .cycleReturn hv hi hj

theorem guard_rectangle_or_special {a b o : T} (h : Guard a b o) :
    ((Part a o ∨ Part b o) ∧ Column o a ∧ Image o b) ∨ SpecialGuard a b o := by
  cases h with
  | rectangle hv hc hi => exact Or.inl ⟨hv,hc,hi⟩
  | inverseDouble p => exact Or.inr (.inverseDouble p)
  | imageReturn hi => exact Or.inr (.imageReturn hi)
  | cycleReturn hv hi hj => exact Or.inr (.cycleReturn hv hi hj)

theorem special_outputs_equal {a b c d u v : T} (h : SpecialGuard a b u)
    (k : SpecialGuard c d v) (ha : a = c) (hb : b = d) : u = v := by
  cases h with
  | inverseDouble p =>
      cases k with
      | inverseDouble q => rw [S_injective hb]
      | @imageReturn q r hi =>
          have he := (T.p.inj ha).2.1
          rw [S_injective hb] at he
          have hn := congrArg nodes he
          rw [nodes_S,nodes_S] at hn
          exact False.elim (Nat.ne_of_lt (pair_left .zero q r) hn)
      | cycleReturn hv hi hj =>
          rw [←ha,←hb] at hv hi hj
          exact (inverse_cycle_overlap hv hi hj).symm
  | @imageReturn p q ht =>
      cases k with
      | inverseDouble r =>
          have he := (T.p.inj ha).2.1
          rw [←S_injective hb] at he
          have hn := congrArg nodes he
          rw [nodes_S,nodes_S] at hn
          exact False.elim (Nat.ne_of_lt (pair_left .zero p q) hn.symm)
      | @imageReturn r s hi =>
          exact congrArg S (S_injective (S_injective (T.p.inj ha).2.1))
      | cycleReturn hv hi hj =>
          rw [←ha,←hb] at hv hi hj
          exact (image_return_cycle_overlap hv hi hj).symm
  | cycleReturn hv hi hj =>
      cases k with
      | inverseDouble p =>
          rw [ha,hb] at hv hi hj
          exact inverse_cycle_overlap hv hi hj
      | imageReturn ht =>
          rw [ha,hb] at hv hi hj
          exact image_return_cycle_overlap hv hi hj
      | cycleReturn hw hk hl =>
          rw [ha,hb] at hv hi hj
          exact cycle_guard_outputs_equal hv hi hj hw hk hl

theorem special_unique {a b u v : T} (h : SpecialGuard a b u)
    (k : SpecialGuard a b v) : u = v := special_outputs_equal h k rfl rfl

 

def RectangleGuardUnique : Prop := ∀ {p a b o : T}, Normal a → Normal b →
  Column p a → Image p b → Guard a b o → p = o

theorem guard_unique_of_rectangle (hr : RectangleGuardUnique) : GuardUnique := by
  intro a b u v ha hb hu hv
  rcases guard_rectangle_or_special hu with ⟨hpart,hc,hi⟩ | hu
  · exact hr ha hb hc hi hv
  · rcases guard_rectangle_or_special hv with ⟨hpart,hc,hi⟩ | hv
    · exact (hr ha hb hc hi (special_guard hu)).symm
    · exact special_unique hu hv

theorem rectangle_unique_of_guard (hu : GuardUnique) : RectangleGuardUnique := by
  intro p a b o ha hb hc hi hg
  exact hu ha hb (.rectangle (rectangle_target_visible hc hi) hc hi) hg

theorem guard_unique_iff_rectangle : GuardUnique ↔ RectangleGuardUnique :=
  ⟨rectangle_unique_of_guard,guard_unique_of_rectangle⟩

theorem source_from_rectangle_conditions (hu : RectangleGuardUnique)
    (hr : RectangleReturnCovered) : ∀ x y z : NormalTree,
      x = multiplication (multiplication y (multiplication x x))
        (multiplication (multiplication x z) z) :=
  source_from_rectangle_obligations (guard_unique_of_rectangle hu) hr

end submission.Equation22446Lineage

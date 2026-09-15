prelude
import Init.Classical
import Init.Data.Nat.Lemmas
import Init.RCases
import ExportGuardedSyntaxDecoder
set_option Elab.async false
set_option autoImplicit false
set_option Elab.async false

namespace submission.Equation22446Lineage
open submission.Equation22446Guarded

theorem part_S_target {t p : T} (h : Part t p) : Part t (S p) := by
  induction h with
  | root c t =>
      cases c with
      | zero => exact .root .one t
      | one => exact .root .two t
      | two =>
          change Part t (S (S (S t)))
          rw [cube]
          exact .root .zero t
  | left c h ih => exact .left c ih
  | right c h ih => exact .right c ih

inductive Guard : T → T → T → Prop where
  | rectangle {p a b : T} : (Part a p ∨ Part b p) → Column p a → Image p b → Guard a b p
  | inverseDouble (p : T) : Guard (P p (S p)) (S p) (S (S p))
  | imageReturn {p q : T} : Image p q →
      Guard (P (S (S (P p q))) (S p)) (S p) (S (P p q))
  | cycleReturn {p a b : T} : (Part a p ∨ Part b p) →
      Image p (P a b) → Image (P a b) (S p) → Guard a b (S (S p))

theorem guard_subterm {a b o : T} (h : Guard a b o) : Part a o ∨ Part b o := by
  cases h with
  | rectangle hp hc hi => exact hp
  | inverseDouble p => exact Or.inl (.left .zero (.root .two p))
  | imageReturn hi => exact Or.inl (.left .zero (.root .two _))
  | cycleReturn hp hi hj =>
      rcases hp with hp | hp
      · exact Or.inl (part_S_target (part_S_target hp))
      · exact Or.inr (part_S_target (part_S_target hp))

theorem guard_decreases (c : Shade) {a b o : T} (h : Guard a b o) :
    nodes (rotate c o) < nodes (.p c a b) := by
  rw [nodes_rotate]
  rcases guard_subterm h with hp | hp
  · exact Nat.lt_of_le_of_lt (part_nodes hp) (pair_left c a b)
  · exact Nat.lt_of_le_of_lt (part_nodes hp) (pair_right c a b)

def Normal : T → Prop
  | .e _ _ => True
  | .p _ a b => Normal a ∧ Normal b ∧ ¬ ∃ o, Guard a b o

theorem normal_rotate (c : Shade) (t : T) : Normal (rotate c t) ↔ Normal t := by
  cases c <;> cases t <;> exact Iff.rfl

theorem normal_part {t o : T} (hn : Normal t) (hp : Part t o) : Normal o := by
  induction hp with
  | root c t => exact (normal_rotate c t).mpr hn
  | left c h ih => exact ih hn.1
  | right c h ih => exact ih hn.2.1

theorem normal_guard_output {a b o : T} (ha : Normal a) (hb : Normal b)
    (h : Guard a b o) (c : Shade) : Normal (rotate c o) := by
  apply (normal_rotate c o).mpr
  rcases guard_subterm h with hp | hp
  · exact normal_part ha hp
  · exact normal_part hb hp

def NormalTree := {t : T // Normal t}

end submission.Equation22446Lineage

prelude
import GuardedSyntax.Relations
import Init.Classical
set_option autoImplicit false
set_option Elab.async false

namespace Equation22446Guarded

def rotate (c : Shade) (t : T) : T :=
  match c with
  | .zero => t
  | .one => S t
  | .two => S (S t)

theorem nodes_rotate (c : Shade) (t : T) : nodes (rotate c t) = nodes t := by
  cases c with
  | zero => rfl
  | one => exact nodes_S t
  | two => exact (nodes_S (S t)).trans (nodes_S t)

/-- A rotated subterm; the root itself is permitted. -/
inductive Part : T → T → Prop where
  | root (c : Shade) (t : T) : Part t (rotate c t)
  | left {a b o : T} (c : Shade) : Part a o → Part (.p c a b) o
  | right {a b o : T} (c : Shade) : Part b o → Part (.p c a b) o

theorem part_nodes {t o : T} (h : Part t o) : nodes o ≤ nodes t := by
  induction h with
  | root c t => rw [nodes_rotate]; exact Nat.le_refl _
  | left c h ih => exact Nat.le_trans ih (Nat.le_of_lt (pair_left c _ _))
  | right c h ih => exact Nat.le_trans ih (Nat.le_of_lt (pair_right c _ _))

/- Exactly the seven phase-zero root branches of guarded_roots. The rectangle
branch retains its rotated-subterm search restriction. The relation records
all available outputs, without claiming they are unique. -/
inductive Guard : T → T → T → Prop where
  | rectangle {p a b : T} : (Part a p ∨ Part b p) →
      Column p a → Image p b → Guard a b p
  | imageHit {a b : T} : Image (S a) b → Guard a b (S a)
  | doubleImageShift {a b : T} : Image a (S (S b)) → Guard a b (S b)
  | imageShift {p q : T} : Image p q → Guard (S (S p)) (S (P p q)) (S (S (P p q)))
  | imageRectangle {p q b : T} : Image p q → Image p b → Guard (S (P p q)) b p
  | inverseDouble (p : T) : Guard (P p (S p)) (S p) (S (S p))
  | imageReturn {p q : T} : Image p q →
      Guard (P (S (S (P p q))) (S p)) (S p) (S (P p q))

theorem guard_subterm {a b o : T} (h : Guard a b o) : Part a o ∨ Part b o := by
  cases h with
  | rectangle hp _ _ => exact hp
  | imageHit _ => exact Or.inl (.root .one _)
  | doubleImageShift _ => exact Or.inr (.root .one _)
  | imageShift _ => exact Or.inr (.root .one _)
  | imageRectangle _ _ => exact Or.inl (.left .one (.root .zero _))
  | inverseDouble p => exact Or.inl (.left .zero (.root .two _))
  | imageReturn _ => exact Or.inl (.left .zero (.root .two _))

theorem guard_decreases (c : Shade) {a b o : T} (h : Guard a b o) :
    nodes (rotate c o) < nodes (.p c a b) := by
  rw [nodes_rotate]
  rcases guard_subterm h with ha | hb
  · exact Nat.lt_of_le_of_lt (part_nodes ha) (pair_left c _ _)
  · exact Nat.lt_of_le_of_lt (part_nodes hb) (pair_right c _ _)

theorem diagonal_guard (x : T) : Guard x x (S x) := by
  apply Guard.rectangle (Or.inl (.root .one x))
  · have h := Column.canonical (S x)
    rwa [cube] at h
  · have h := Image.square (S x)
    rwa [cube] at h

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

/-- On normal children, every root output is already normal, even if the
unproved uniqueness property were to fail. No further root loop is needed. -/
theorem normal_guard_output {a b o : T} (ha : Normal a) (hb : Normal b)
    (h : Guard a b o) (c : Shade) : Normal (rotate c o) := by
  apply (normal_rotate c o).mpr
  rcases guard_subterm h with hp | hp
  · exact normal_part ha hp
  · exact normal_part hb hp

/-- Bottom-up evaluation allows any available guarded output. This does not
identify different outputs or assert confluence. -/
inductive Eval : T → T → Prop where
  | atom (c : Shade) (n : Nat) : Eval (.e c n) (.e c n)
  | raw {a b a' b' : T} (c : Shade) : Eval a a' → Eval b b' →
      (¬ ∃ o, Guard a' b' o) → Eval (.p c a b) (.p c a' b')
  | hit {a b a' b' o : T} (c : Shade) : Eval a a' → Eval b b' →
      Guard a' b' o → Eval (.p c a b) (rotate c o)

theorem eval_normal {t n : T} (h : Eval t n) : Normal n := by
  induction h with
  | atom c n => trivial
  | raw c _ _ hn ha hb => exact ⟨ha,hb,hn⟩
  | hit c _ _ hg ha hb => exact normal_guard_output ha hb hg c

theorem eval_exists (t : T) : ∃ n, Eval t n := by
  classical
  induction t with
  | e c n => exact ⟨.e c n,.atom c n⟩
  | p c a b ha hb =>
      obtain ⟨a',ha'⟩ := ha
      obtain ⟨b',hb'⟩ := hb
      by_cases h : ∃ o, Guard a' b' o
      · obtain ⟨o,ho⟩ := h
        exact ⟨rotate c o,.hit c ha' hb' ho⟩
      · exact ⟨.p c a' b',.raw c ha' hb' h⟩

theorem normal_evaluates_self {t : T} (h : Normal t) : Eval t t := by
  induction t with
  | e c n => exact .atom c n
  | p c a b ha hb => exact .raw c (ha h.1) (hb h.2.1) h.2.2

theorem eval_normal_fixed {t n : T} (hn : Normal t) (h : Eval t n) : n = t := by
  induction h with
  | atom c n => rfl
  | raw c _ _ h ha hb =>
      rw [ha hn.1,hb hn.2.1]
  | hit c _ _ h ha hb =>
      rw [ha hn.1,hb hn.2.1] at h
      exact False.elim (hn.2.2 ⟨_,h⟩)

#print axioms part_nodes
#print axioms guard_subterm
#print axioms guard_decreases
#print axioms diagonal_guard
#print axioms normal_rotate
#print axioms normal_part
#print axioms normal_guard_output
#print axioms eval_normal
#print axioms eval_exists
#print axioms normal_evaluates_self
#print axioms eval_normal_fixed
end Equation22446Guarded

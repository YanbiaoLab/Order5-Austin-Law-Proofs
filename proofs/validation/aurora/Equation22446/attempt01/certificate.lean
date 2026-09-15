prelude
import JudgeProblem
import Init.Classical
import Init.Data.Nat.Lemmas
import Init.RCases
set_option Elab.async false

/- Checked source module: GuardedSyntax.Tree -/
set_option autoImplicit false
set_option Elab.async false

namespace submission.Equation22446Guarded

/- Independent free syntax. S rotates only the root color; P is a raw pair.
There is no magma law assumption in this namespace. -/
inductive Shade where
  | zero | one | two
  deriving DecidableEq

inductive T where
  | e : Shade → Nat → T
  | p : Shade → T → T → T
  deriving DecidableEq

def next : Shade → Shade
  | .zero => .one
  | .one => .two
  | .two => .zero

def S : T → T
  | .e c n => .e (next c) n
  | .p c a b => .p (next c) a b

def P (a b : T) : T := .p .zero a b

def nodes : T → Nat
  | .e _ _ => 0
  | .p _ a b => nodes a + nodes b + 1

theorem cube (a : T) : S (S (S a)) = a := by
  cases a with
  | e c n => cases c <;> rfl
  | p c a b => cases c <;> rfl

theorem S_injective {a b : T} (h : S a = S b) : a = b := by
  have h' := congrArg (fun t => S (S t)) h
  rwa [cube,cube] at h'

theorem S_ne (a : T) : S a ≠ a := by
  cases a with
  | e c n => cases c <;> intro h <;> cases h
  | p c a b => cases c <;> intro h <;> cases h

theorem SS_ne (a : T) : S (S a) ≠ a := by
  intro h
  have h' := congrArg S h
  rw [cube] at h'
  exact S_ne a h'.symm

theorem nodes_S (a : T) : nodes (S a) = nodes a := by
  cases a <;> rfl

theorem pair_left (c : Shade) (a b : T) : nodes a < nodes (.p c a b) :=
  Nat.lt_succ_of_le (Nat.le_add_right _ _)

theorem pair_right (c : Shade) (a b : T) : nodes b < nodes (.p c a b) :=
  Nat.lt_succ_of_le (Nat.le_add_left _ _)

theorem children_bound {x : T} {c : Shade} {a b : T} (h : x = .p c a b) :
    nodes a < nodes x ∧ nodes b < nodes x := by
  rw [h]
  exact ⟨pair_left c a b,pair_right c a b⟩

theorem phase_two_or_square_nonzero (x : T) :
    (∃ a b, x = .p .two a b) ∨ (∀ a b, S x ≠ P a b) := by
  cases x with
  | e c n => right; intro a b h; cases c <;> cases h
  | p c a b =>
      cases c with
      | zero => right; intro u v h; cases h
      | one => right; intro u v h; cases h
      | two => exact Or.inl ⟨a,b,rfl⟩

end submission.Equation22446Guarded

/- Checked source module: LineageSyntax.Relations -/
set_option autoImplicit false
set_option Elab.async false

namespace submission.Equation22446Lineage
open submission.Equation22446Guarded

/- Independent FREE syntax for the lineage-followup candidate. These are
not the old GuardedSyntax relations, nor Source-conditional certificates. -/
mutual
inductive Image : T → T → Prop where
  | square (p : T) : Image p (S (S p))
  | literal (p t : T) : Image p (P (P p t) t)
  | transport {p a q : T} : Column p a → Image p q → Image a (P p q)
  | inverseFollowup (p : T) : Image (P p (S p)) (P (S (S p)) (S p))
  | returnFollowup {p q : T} : Image p q →
      Image (P (S (S (P p q))) (S p)) (P (S (P p q)) (S p))
  | cycleFollowup {u v w t z : T} :
      nodes (S (S (P w t))) < nodes (P (P u v) z) →
      Image (S (S (P w t))) (P (P u v) z) → Image (P (P u v) z) (P w t) →
      Image (P u v) (P (S (P w t)) z)
inductive Column : T → T → Prop where
  | ancestry {p q : T} : Lineage p q → Column p (S (S q))
  | literal (p y : T) : Column p (P y (S p))
  | inverseImage {p a : T} : Image a (S p) → Column p a
inductive Lineage : T → T → Prop where
  | refl (p : T) : Lineage p p
  | step {p a b : T} : Lineage p a → Image a b → Lineage p (S (S (P a b)))
end

theorem column_canonical (p : T) : Column p (S (S p)) := .ancestry (.refl p)

theorem column_completed {p q : T} (hi : Image p q) : Column p (S (P p q)) :=
  .ancestry (.step (.refl p) hi)

theorem lineage_nodes {p q : T} (h : Lineage p q) : nodes p ≤ nodes q :=
  match h with
  | .refl p => Nat.le_refl _
  | .step hl hi => Nat.le_trans (lineage_nodes hl) (Nat.le_of_lt (pair_left .two _ _))

theorem lineage_non_phase_two {p q : T} (h : Lineage p q)
    (hn : ∀ a b, q ≠ S (S (P a b))) : p = q := by
  cases h with
  | refl => rfl
  | step hl hi => exact False.elim (hn _ _ rfl)

theorem image_nonzero_output {p q : T} (h : Image p q)
    (hn : ∀ a b, q ≠ P a b) : q = S (S p) := by
  cases h with
  | square p => rfl
  | literal p t => exact False.elim (hn _ _ rfl)
  | transport hc hi => exact False.elim (hn _ _ rfl)
  | inverseFollowup p => exact False.elim (hn _ _ rfl)
  | returnFollowup hi => exact False.elim (hn _ _ rfl)
  | cycleFollowup hs hi hj => exact False.elim (hn _ _ rfl)

mutual
theorem image_phase_two_bound {p q : T} (h : Image p q) :
    ∀ a b, p = S (S (P a b)) → nodes p ≤ nodes q :=
  match h with
  | .square p => by intro a b hp; rw [nodes_S,nodes_S]; exact Nat.le_refl _
  | .literal p t => by
      intro a b hp
      exact Nat.le_of_lt (Nat.lt_trans (pair_left .zero _ _) (pair_left .zero _ _))
  | .transport hc hi => by
      intro a b hp
      exact Nat.le_trans (column_phase_two_bound hc a b hp) (Nat.le_of_lt (pair_left .zero _ _))
  | .inverseFollowup p => by intro a b hp; cases hp
  | .returnFollowup hi => by intro a b hp; cases hp
  | .cycleFollowup hs hi hj => by intro a b hp; cases hp
theorem column_phase_two_bound {p a : T} (h : Column p a) :
    ∀ u v, a = S (S (P u v)) → nodes a ≤ nodes p :=
  match h with
  | .ancestry hl => by
      intro u v ha
      have he := S_injective (S_injective ha)
      have hp := lineage_non_phase_two hl (by intro x y h; rw [he] at h; cases h)
      rw [nodes_S,nodes_S,←hp]
      exact Nat.le_refl _
  | .literal p y => by intro u v ha; cases ha
  | .inverseImage hi => by
      intro u v ha
      have hb := image_phase_two_bound hi u v ha
      rwa [nodes_S] at hb
end

theorem image_phase_two_output_left {p q : T} (h : Image p q) :
    ∀ a b u v, p = S (S (P a b)) → q = P u v → nodes p ≤ nodes u := by
  intro a b u v hp hq
  cases h with
  | square p => rw [hp] at hq; cases hq
  | literal p t =>
      rw [←(T.p.inj hq).2.1]
      exact Nat.le_of_lt (pair_left .zero _ _)
  | transport hc hi =>
      rw [←(T.p.inj hq).2.1]
      exact column_phase_two_bound hc a b hp
  | inverseFollowup p => cases hp
  | returnFollowup hi => cases hp
  | cycleFollowup hs hi hj => cases hp

end submission.Equation22446Lineage

/- Checked source module: GuardedSyntax.Relations -/
set_option autoImplicit false
set_option Elab.async false

namespace submission.Equation22446Guarded

/- This is the new nine-constructor grammar on FREE trees, not the earlier
Source-conditional semantic certificates. P below is always a raw pair. -/
mutual
inductive Image : T → T → Prop where
  | square (p : T) : Image p (S (S p))
  | literal (p t : T) : Image p (P (P p t) t)
  | transport {p a q : T} : Column p a → Image p q → Image a (P p q)
  | inverseFollowup (p : T) : Image (P p (S p)) (P (S (S p)) (S p))
  | returnFollowup {p q : T} : Image p q →
      Image (P (S (S (P p q))) (S p)) (P (S (P p q)) (S p))
inductive Column : T → T → Prop where
  | canonical (p : T) : Column p (S (S p))
  | literal (p y : T) : Column p (P y (S p))
  | inverseImage {p a : T} : Image a (S p) → Column p a
  | completed {p q : T} : Image p q → Column p (S (P p q))
end

theorem image_nonzero_output {p q : T} (h : Image p q)
    (hn : ∀ a b, q ≠ P a b) : q = S (S p) := by
  cases h with
  | square p => rfl
  | literal p t => exact False.elim (hn _ _ rfl)
  | transport _ _ => exact False.elim (hn _ _ rfl)
  | inverseFollowup p => exact False.elim (hn _ _ rfl)
  | returnFollowup _ => exact False.elim (hn _ _ rfl)

mutual
theorem image_phase_two_bound {p q : T} (h : Image p q) :
    ∀ a b, p = .p .two a b → nodes p ≤ nodes q :=
  match h with
  | .square p => by
      intro a b hp
      rw [nodes_S,nodes_S]
      exact Nat.le_refl _
  | .literal p t => by
      intro a b hp
      exact Nat.le_of_lt (Nat.lt_trans (pair_left .zero _ _) (pair_left .zero _ _))
  | .transport hc _ => by
      intro a b hp
      exact Nat.le_trans (column_phase_two_bound hc a b hp)
        (Nat.le_of_lt (pair_left .zero _ _))
  | .inverseFollowup p => by intro a b hp; cases hp
  | .returnFollowup _ => by intro a b hp; cases hp
theorem column_phase_two_bound {p a : T} (h : Column p a) :
    ∀ u v, a = .p .two u v → nodes a ≤ nodes p :=
  match h with
  | .canonical p => by
      intro u v ha
      rw [nodes_S,nodes_S]
      exact Nat.le_refl _
  | .literal p y => by intro u v ha; cases ha
  | .inverseImage hi => by
      intro u v ha
      have hb := image_phase_two_bound hi u v ha
      rwa [nodes_S] at hb
  | .completed _ => by intro u v ha; cases ha
end

/- The old all-color right-child bound is FALSE for the new completed-column
constructor. The correct statements here deliberately exclude color one. -/
mutual
theorem image_right_child {p q : T} (h : Image p q) :
    ∀ (c : Shade) a b, c ≠ .one → p = .p c a b → nodes b < nodes q :=
  match h with
  | .square p => by
      intro c a b hc hp
      rw [nodes_S,nodes_S]
      exact (children_bound hp).2
  | .literal p t => by
      intro c a b hc hp
      exact Nat.lt_trans (children_bound hp).2
        (Nat.lt_trans (pair_left .zero _ _) (pair_left .zero _ _))
  | .transport hc _ => by
      intro c a b hn hp
      exact Nat.lt_of_le_of_lt (column_right_child hc c a b hn hp) (pair_left .zero _ _)
  | .inverseFollowup p => by
      intro c a b hn hp
      have hb := (T.p.inj hp).2.2
      rw [←hb]
      exact pair_right .zero _ _
  | .returnFollowup _ => by
      intro c a b hn hp
      have hb := (T.p.inj hp).2.2
      rw [←hb]
      exact pair_right .zero _ _
theorem column_right_child {p a : T} (h : Column p a) :
    ∀ (c : Shade) u v, c ≠ .one → a = .p c u v → nodes v ≤ nodes p :=
  match h with
  | .canonical p => by
      intro c u v hn ha
      have hb := (children_bound ha).2
      rw [nodes_S,nodes_S] at hb
      exact Nat.le_of_lt hb
  | .literal p y => by
      intro c u v hn ha
      have hv := (T.p.inj ha).2.2
      rw [←hv,nodes_S]
      exact Nat.le_refl _
  | .inverseImage hi => by
      intro c u v hn ha
      have hb := image_right_child hi c u v hn ha
      rw [nodes_S] at hb
      exact Nat.le_of_lt hb
  | .completed _ => by
      intro c u v hn ha
      exact False.elim (hn (T.p.inj ha).1.symm)
end

theorem image_phase_two_strict {p q : T} (h : Image p q) :
    ∀ a b u v, p = .p .two a b → q = P u v → nodes p < nodes q := by
  intro a b u v hp hq
  cases h with
  | square p => rw [hp] at hq; cases hq
  | literal p t => exact Nat.lt_trans (pair_left .zero _ _) (pair_left .zero _ _)
  | transport hc _ =>
      exact Nat.lt_of_le_of_lt (column_phase_two_bound hc a b hp) (pair_left .zero _ _)
  | inverseFollowup p => cases hp
  | returnFollowup _ => cases hp

theorem image_no_successor {p : T} (h : Image p (S p)) : False := by
  rcases phase_two_or_square_nonzero p with ⟨a,b,hp⟩ | hn
  · have hb := image_phase_two_strict h a b a b hp (by rw [hp]; rfl)
    rw [nodes_S] at hb
    exact Nat.lt_irrefl _ hb
  · exact S_ne p (S_injective (image_nonzero_output h hn).symm)

theorem all_color_column_right_bound_false :
    ¬ (∀ {p a b : T} {c : Shade}, Column p (.p c a b) → nodes b ≤ nodes p) := by
  intro h
  let x : T := .e .zero 0
  have hc := Column.completed (Image.literal x (S (S x)))
  have bad : 2 ≤ 0 := h hc
  exact Nat.not_succ_le_zero 1 bad

theorem all_color_image_right_bound_false :
    ¬ (∀ {p a b : T} {c : Shade}, Image (.p c a b) p → nodes b < nodes p) := by
  intro h
  let x : T := .e .zero 0
  have hi := Image.transport (Column.completed (Image.literal x (S (S x)))) (Image.square x)
  have bad : 2 < 1 := h hi
  exact Nat.not_lt_of_ge (Nat.le_succ_of_le (Nat.le_refl 1)) bad

end submission.Equation22446Guarded

/- Checked source module: GuardedSyntax.Decoder -/
set_option autoImplicit false
set_option Elab.async false

namespace submission.Equation22446Guarded

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

end submission.Equation22446Guarded

/- Checked source module: LineageSyntax.Decoder -/
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

/- Checked source module: LineageSyntax.Evaluation -/
set_option autoImplicit false
set_option Elab.async false

namespace submission.Equation22446Lineage
open submission.Equation22446Guarded

/- Evaluation and multiplication relations for the NEW grammar. Neither
existence nor preservation of Normal asserts unique returns or Source. -/
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
  | raw c _ _ h ha hb => rw [ha hn.1,hb hn.2.1]
  | hit c _ _ h ha hb =>
      rw [ha hn.1,hb hn.2.1] at h
      exact False.elim (hn.2.2 ⟨_,h⟩)

inductive Product : T → T → T → Prop where
  | raw {a b : T} : (¬ ∃ o, Guard a b o) → Product a b (P a b)
  | hit {a b o : T} : Guard a b o → Product a b o

theorem normal_pair_eval_product {a b o : T} (ha : Normal a) (hb : Normal b)
    (he : Eval (P a b) o) : Product a b o := by
  cases he with
  | raw c ea eb hn =>
      rw [eval_normal_fixed ha ea,eval_normal_fixed hb eb] at hn ⊢
      exact .raw hn
  | hit c ea eb hg =>
      rw [eval_normal_fixed ha ea,eval_normal_fixed hb eb] at hg
      exact .hit hg

theorem product_exists (a b : T) : ∃ o, Product a b o := by
  classical
  by_cases h : ∃ o, Guard a b o
  · obtain ⟨o,ho⟩ := h
    exact ⟨o,.hit ho⟩
  · exact ⟨P a b,.raw h⟩

theorem product_normal {a b o : T} (ha : Normal a) (hb : Normal b)
    (h : Product a b o) : Normal o := by
  cases h with
  | raw hn => exact ⟨ha,hb,hn⟩
  | hit hg => exact normal_guard_output ha hb hg .zero

noncomputable def chosen (a b : T) : T := Classical.choose (product_exists a b)

theorem chosen_product (a b : T) : Product a b (chosen a b) :=
  Classical.choose_spec (product_exists a b)

theorem chosen_normal {a b : T} (ha : Normal a) (hb : Normal b) : Normal (chosen a b) :=
  product_normal ha hb (chosen_product a b)

noncomputable def multiplication (a b : NormalTree) : NormalTree :=
  ⟨chosen a.val b.val,chosen_normal a.property b.property⟩

theorem diagonal_guard (x : T) : Guard x x (S x) := by
  apply Guard.rectangle (Or.inl (.root .one x))
  · have h := column_canonical (S x)
    rwa [cube] at h
  · have h := Image.square (S x)
    rwa [cube] at h

end submission.Equation22446Lineage

/- Checked source module: LineageSyntax.RightBounds -/
set_option autoImplicit false
set_option Elab.async false

namespace submission.Equation22446Lineage
open submission.Equation22446Guarded

mutual
theorem image_right_child {p q : T} (h : Image p q) :
    ∀ (c : Shade) a b, c ≠ .one → p = .p c a b → nodes b < nodes q :=
  match h with
  | .square p => by
      intro c a b hn hp
      rw [nodes_S,nodes_S]
      exact (children_bound hp).2
  | .literal p t => by
      intro c a b hn hp
      exact Nat.lt_trans (children_bound hp).2
        (Nat.lt_trans (pair_left .zero _ _) (pair_left .zero _ _))
  | .transport hc hi => by
      intro c a b hn hp
      exact Nat.lt_of_le_of_lt (column_right_child hc c a b hn hp) (pair_left .zero _ _)
  | .inverseFollowup p => by
      intro c a b hn hp
      rw [←(T.p.inj hp).2.2]
      exact pair_right .zero _ _
  | .returnFollowup hi => by
      intro c a b hn hp
      rw [←(T.p.inj hp).2.2]
      exact pair_right .zero _ _
  | .cycleFollowup hs hi hj => by
      intro c a b hn hp
      rw [←(T.p.inj hp).2.2]
      exact cycle_input_right_bound hi _ _ _ _ _ rfl rfl
theorem column_right_child {p a : T} (h : Column p a) :
    ∀ (c : Shade) u v, c ≠ .one → a = .p c u v → nodes v ≤ nodes p :=
  match h with
  | .ancestry hl => by
      intro c u v hn ha
      cases hl with
      | refl =>
          have hb := (children_bound ha).2
          rw [nodes_S,nodes_S] at hb
          exact Nat.le_of_lt hb
      | step hl hi => exact False.elim (hn (T.p.inj ha).1.symm)
  | .literal p y => by
      intro c u v hn ha
      rw [←(T.p.inj ha).2.2,nodes_S]
      exact Nat.le_refl _
  | .inverseImage hi => by
      intro c u v hn ha
      have hb := image_right_child hi c u v hn ha
      rw [nodes_S] at hb
      exact Nat.le_of_lt hb
theorem cycle_input_right_bound {p q : T} (h : Image p q) :
    ∀ u v w t z, p = S (S (P w t)) → q = P (P u v) z →
      nodes v < nodes (P (S (P w t)) z) :=
  match h with
  | .square p => by intro u v w t z hp hq; rw [hp] at hq; cases hq
  | .literal p y => by
      intro u v w t z hp hq
      have hv := (T.p.inj (T.p.inj hq).2.1).2.2
      have hz := (T.p.inj hq).2.2
      rw [←hv,hz]
      exact pair_right .zero _ _
  | .transport hc hi => by
      intro u v w t z hp hq
      have hh := image_right_child hi .zero u v (by intro h; cases h) (T.p.inj hq).2.1
      rw [(T.p.inj hq).2.2] at hh
      exact Nat.lt_trans hh (pair_right .zero _ _)
  | .inverseFollowup p => by intro u v w t z hp hq; cases hp
  | .returnFollowup hi => by intro u v w t z hp hq; cases hp
  | .cycleFollowup hs hi hj => by intro u v w t z hp hq; cases hp
end

theorem column_phase_two_base_shape {a p : T} (hc : Column a p)
    (hp : ∃ u v, p = S (S (P u v))) :
    (∃ u v, a = P u v) ∨ (∃ u v, a = S (S (P u v))) := by
  rcases phase_two_or_square_nonzero a with ha | hn
  · exact Or.inr ha
  · obtain ⟨u,v,hp⟩ := hp
    cases hc with
    | ancestry hl =>
        have hq := S_injective (S_injective hp)
        have ha := lineage_non_phase_two hl (by intro x y h; rw [hq] at h; cases h)
        exact Or.inl ⟨u,v,ha.trans hq⟩
    | literal a y => cases hp
    | inverseImage hi =>
        have ha := S_injective (image_nonzero_output hi hn)
        left
        refine ⟨u,v,?_⟩
        rw [ha,hp,cube]

theorem cycle_target_phase_two {p a b : T} (hi : Image p (P a b))
    (hj : Image (P a b) (S p)) (hs : nodes p < nodes (P a b)) :
    ∃ u v, p = S (S (P u v)) := by
  rcases phase_two_or_square_nonzero p with hp | hn
  · exact hp
  · have he := congrArg nodes (image_nonzero_output hj hn)
    rw [nodes_S,nodes_S,nodes_S] at he
    rw [he] at hs
    exact False.elim (Nat.lt_irrefl _ hs)

/-- The phase-zero restriction in the cycle-followup classifier loses no
strict cycle return in this grammar. This is a free-syntax theorem. -/
theorem cycle_left_phase_zero {p a b : T} (hi : Image p (P a b))
    (hj : Image (P a b) (S p)) (hs : nodes p < nodes (P a b)) :
    ∃ u v, a = P u v := by
  obtain ⟨u,v,hp⟩ := cycle_target_phase_two hi hj hs
  have hpa := image_phase_two_output_left hi u v a b hp rfl
  have hbp := image_right_child hj .zero a b (by intro h; cases h) rfl
  rw [nodes_S] at hbp
  generalize hq : P a b = q at hi
  cases hi with
  | square p => rw [hp] at hq; cases hq
  | literal p t => exact ⟨p,t,(T.p.inj hq).2.1⟩
  | transport hc ht =>
      rw [←(T.p.inj hq).2.1] at hc
      rw [←(T.p.inj hq).2.1,←(T.p.inj hq).2.2] at ht
      rcases column_phase_two_base_shape hc ⟨u,v,hp⟩ with ha | ⟨x,y,ha⟩
      · exact ha
      · have hab := image_phase_two_bound ht x y ha
        exact False.elim (Nat.lt_irrefl _ (Nat.lt_of_le_of_lt (Nat.le_trans hpa hab) hbp))
  | inverseFollowup p => cases hp
  | returnFollowup ht => cases hp
  | cycleFollowup ht hk hl => cases hp

theorem old_phase_one_column_left_bound_false :
    ¬ (∀ {p a b : T}, Column p (S (P a b)) → nodes a ≤ nodes p) := by
  intro h
  let e : T := .e .zero 0
  let u := S (S (P e (S (S e))))
  let p := S (S (P u (S (S u))))
  have hu : Lineage e u := .step (.refl e) (.square e)
  have hp : Lineage e p := .step hu (.square u)
  have hc : Column e (S (P p (S (S p)))) := .ancestry (.step hp (.square p))
  have bad : 3 ≤ 0 := h hc
  exact Nat.not_succ_le_zero 2 bad

theorem old_phase_one_image_left_bound_false :
    ¬ (∀ {a b q : T}, Image (S (P a b)) q → nodes a < nodes q) := by
  intro h
  let e : T := .e .zero 0
  let u := S (S (P e (S (S e))))
  let p := S (S (P u (S (S u))))
  have hu : Lineage e u := .step (.refl e) (.square e)
  have hp : Lineage e p := .step hu (.square u)
  have hc : Column e (S (P p (S (S p)))) := .ancestry (.step hp (.square p))
  have hi := Image.transport hc (.square e)
  have bad : 3 < 1 := h hi
  exact Nat.not_lt_of_ge (by decide) bad

end submission.Equation22446Lineage

/- Checked source module: LineageSyntax.RawCoverage -/
set_option autoImplicit false
set_option Elab.async false

namespace submission.Equation22446Lineage
open submission.Equation22446Guarded

theorem visible_target_smaller {a b p : T} (h : Part a p ∨ Part b p) :
    nodes p < nodes (P a b) := by
  rcases h with h | h
  · exact Nat.lt_of_le_of_lt (part_nodes h) (pair_left .zero _ _)
  · exact Nat.lt_of_le_of_lt (part_nodes h) (pair_right .zero _ _)

theorem cycle_raw_followup {a z p : T} (hp : Part a p ∨ Part z p)
    (hi : Image p (P a z)) (hj : Image (P a z) (S p)) :
    Image a (P (S (S p)) z) := by
  have hs := visible_target_smaller hp
  obtain ⟨u,v,ha⟩ := cycle_left_phase_zero hi hj hs
  obtain ⟨w,t,hp⟩ := cycle_target_phase_two hi hj hs
  subst a p
  rw [cube] at hj ⊢
  exact .cycleFollowup hs hi hj

/-- All four possible first returns are covered when the next multiplication
is raw, including the cycle-return branch. This theorem needs no Normal. -/
theorem guard_raw_followup {p z u : T} (h : Guard p z u) : Image p (P u z) := by
  cases h with
  | rectangle hp hc hi => exact .transport hc hi
  | inverseDouble p => exact .inverseFollowup p
  | imageReturn hi => exact .returnFollowup hi
  | cycleReturn hp hi hj => exact cycle_raw_followup hp hi hj

theorem product_raw_followup {p z u : T} (h : Product p z u) : Image p (P u z) := by
  cases h with
  | raw hn => exact .literal p z
  | hit hg => exact guard_raw_followup hg

end submission.Equation22446Lineage

/- Checked source module: LineageSyntax.ShrinkingLineage -/
set_option autoImplicit false
set_option Elab.async false

namespace submission.Equation22446Lineage
open submission.Equation22446Guarded

theorem column_zero_to_two {a b u v : T}
    (h : Column (P a b) (S (S (P u v)))) : P a b = P u v := by
  generalize ha : S (S (P u v)) = x at h
  cases h with
  | ancestry hl =>
      have he := S_injective (S_injective ha)
      have hp := lineage_non_phase_two hl (by intro x y h; rw [←he] at h; cases h)
      exact hp.trans he.symm
  | literal p y => cases ha
  | inverseImage hi =>
      rw [←ha] at hi
      have he := image_nonzero_output hi (by intro x y he; cases he)
      rw [cube] at he
      exact S_injective he

theorem cycle_followup_size_bound {u v w t z : T}
    (h : Image (S (S (P w t))) (P (P u v) z)) :
    nodes (P u v) ≤ nodes (P (S (P w t)) z) := by
  generalize hp : S (S (P w t)) = p at h
  generalize hq : P (P u v) z = q at h
  cases h with
  | square p => rw [←hp] at hq; cases hq
  | literal p y =>
      have he := (T.p.inj hq).2.1
      have hz := (T.p.inj hq).2.2
      rw [he,hz,←hp]
      exact Nat.le_refl _
  | @transport p a q hc hi =>
      have he := (T.p.inj hq).2.1
      rw [←hp,←he] at hc
      have eq := column_zero_to_two hc
      rw [eq]
      exact Nat.le_of_lt (pair_left .zero _ _)
  | inverseFollowup p => cases hp
  | returnFollowup hi => cases hp
  | cycleFollowup hs hi hj => cases hp

/- Shrinking a zero-color pair through an image or column certificate
exposes an ancestry path from the inverse square of its right child. -/
mutual
theorem image_shrinking_lineage {p q : T} (h : Image p q) :
    ∀ u v, p = P u v → nodes q < nodes p → Lineage (S (S v)) (S (S q)) :=
  match h with
  | .square p => by
      intro u v hp hs
      rw [nodes_S,nodes_S] at hs
      exact False.elim (Nat.lt_irrefl _ hs)
  | .literal p t => by
      intro u v hp hs
      exact False.elim (Nat.lt_irrefl _ (Nat.lt_trans
        (Nat.lt_trans (pair_left .zero _ _) (pair_left .zero _ _)) hs))
  | .transport hc hi => by
      intro u v hp hs
      exact .step (column_shrinking_lineage hc u v hp
        (Nat.lt_trans (pair_left .zero _ _) hs)) hi
  | .inverseFollowup p => by
      intro u v hp hs
      have he : nodes (P (S (S p)) (S p)) = nodes (P p (S p)) := by
        simp only [P,nodes,nodes_S]
      rw [he] at hs
      exact False.elim (Nat.lt_irrefl _ hs)
  | .returnFollowup hi => by
      intro u v hp hs
      simp only [P,nodes,nodes_S] at hs
      exact False.elim (Nat.lt_irrefl _ hs)
  | .cycleFollowup ht hi hj => by
      intro u v hp hs
      exact False.elim (Nat.not_lt_of_ge (cycle_followup_size_bound hi) hs)
theorem column_shrinking_lineage {p a : T} (h : Column p a) :
    ∀ u v, a = P u v → nodes p < nodes a → Lineage (S (S v)) p :=
  match h with
  | .ancestry hl => by
      intro u v ha hs
      have he := congrArg S ha
      rw [cube] at he
      have hp := lineage_non_phase_two hl (by intro x y h; rw [he] at h; cases h)
      rw [hp,nodes_S,nodes_S] at hs
      exact False.elim (Nat.lt_irrefl _ hs)
  | .literal p y => by
      intro u v ha hs
      rw [←(T.p.inj ha).2.2,cube]
      exact .refl p
  | .inverseImage hi => by
      intro u v ha hs
      have ht := image_shrinking_lineage hi u v ha (by rwa [nodes_S])
      rwa [cube] at ht
end

end submission.Equation22446Lineage

/- Checked source module: LineageSyntax.ColumnCoverage -/
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

end submission.Equation22446Lineage

/- Checked source module: LineageSyntax.Visibility -/
set_option autoImplicit false
set_option Elab.async false

namespace submission.Equation22446Lineage
open submission.Equation22446Guarded

theorem part_S_source {t o : T} (h : Part t o) : Part (S t) o := by
  induction h with
  | root c t =>
      cases c with
      | zero =>
          have hp := Part.root .two (S t)
          change Part (S t) (S (S (S t))) at hp
          rwa [cube] at hp
      | one => exact .root .zero (S t)
      | two => exact .root .one (S t)
  | left c h ih => exact .left (next c) h
  | right c h ih => exact .right (next c) h

theorem part_unS_source {t o : T} (h : Part (S t) o) : Part t o := by
  have hp := part_S_source (part_S_source h)
  rwa [cube] at hp

theorem lineage_part {p q : T} (h : Lineage p q) : Part q p :=
  match h with
  | .refl p => .root .zero p
  | .step hl hi => .left .two (lineage_part hl)

mutual
theorem image_phase_two_part {p q : T} (h : Image p q) :
    ∀ a b, p = S (S (P a b)) → Part q p :=
  match h with
  | .square p => by
      intro a b hp
      have hs := Part.root .one (S (S p))
      change Part (S (S p)) (S (S (S p))) at hs
      rwa [cube] at hs
  | .literal p t => by
      intro a b hp
      exact .left .zero (.left .zero (.root .zero p))
  | .transport hc hi => by
      intro a b hp
      exact .left .zero (column_phase_two_part hc a b hp)
  | .inverseFollowup p => by intro a b hp; cases hp
  | .returnFollowup hi => by intro a b hp; cases hp
  | .cycleFollowup hs hi hj => by intro a b hp; cases hp
theorem column_phase_two_part {p a : T} (h : Column p a) :
    ∀ u v, a = S (S (P u v)) → Part p a :=
  match h with
  | .ancestry hl => by
      intro u v ha
      have he := S_injective (S_injective ha)
      have hp := lineage_non_phase_two hl (by intro x y h; rw [he] at h; cases h)
      rw [hp]
      exact .root .two _
  | .literal p y => by intro u v ha; cases ha
  | .inverseImage hi => by
      intro u v ha
      exact part_unS_source (image_phase_two_part hi u v ha)
end

theorem column_visible_unless_phase_two {p a : T} (h : Column p a)
    (hn : ∀ u v, S p ≠ P u v) : Part a p := by
  cases h with
  | ancestry hl => exact part_S_source (part_S_source (lineage_part hl))
  | literal p y =>
      apply Part.right .zero
      have hp := Part.root .two (S p)
      change Part (S p) (S (S (S p))) at hp
      rwa [cube] at hp
  | inverseImage hi =>
      have he := image_nonzero_output hi hn
      have ha := congrArg S he
      rw [cube] at ha
      rw [←ha]
      have hp := Part.root .one (S (S p))
      change Part (S (S p)) (S (S (S p))) at hp
      rwa [cube] at hp

/-- Ancestral columns preserve rectangle target visibility. No Source,
normality, uniqueness, or old triangle theorem is used. -/
theorem rectangle_target_visible {p a b : T} (hc : Column p a) (hi : Image p b) :
    Part a p ∨ Part b p := by
  rcases phase_two_or_square_nonzero p with ⟨u,v,hp⟩ | hn
  · exact Or.inr (image_phase_two_part hi u v hp)
  · exact Or.inl (column_visible_unless_phase_two hc hn)

end submission.Equation22446Lineage

/- Checked source module: LineageSyntax.CleanTower -/
set_option autoImplicit false
set_option Elab.async false

namespace submission.Equation22446Lineage
open submission.Equation22446Guarded

def leaf : T := .e .zero 0

def tower : Nat → T
  | 0 => S leaf
  | n+1 => P leaf (tower n)

theorem tower_ne_leaf (n : Nat) : tower n ≠ leaf := by
  cases n <;> intro h <;> cases h

theorem tower_ne_double_leaf (n : Nat) : tower n ≠ S (S leaf) := by
  cases n <;> intro h <;> cases h

theorem leaf_ne_next_tower (n : Nat) : leaf ≠ S (tower n) := by
  cases n <;> intro h <;> cases h

theorem image_tower_root (n : Nat) {p : T} (hi : Image p (tower n)) : p = S (tower n) := by
  induction n generalizing p with
  | zero =>
      have he := congrArg S (image_nonzero_output hi (by intro a b h; cases h))
      rw [cube] at he
      exact he.symm
  | succ n ih =>
      generalize he : tower (n+1) = q at hi
      cases hi with
      | square p => exact (cube p).symm
      | literal p t =>
          have h := (T.p.inj he).2.1
          cases h
      | transport hc hj =>
          rw [←(T.p.inj he).2.1,←(T.p.inj he).2.2] at hj
          exact False.elim (leaf_ne_next_tower n (ih hj))
      | inverseFollowup p =>
          have hp := congrArg S (T.p.inj he).2.1
          rw [cube] at hp
          have hz := (T.p.inj he).2.2
          rw [←hp] at hz
          exact False.elim (tower_ne_double_leaf n hz)
      | returnFollowup hj =>
          have hp := (T.p.inj he).2.1
          cases hp
      | cycleFollowup hs hj hk =>
          have hp := (T.p.inj he).2.1
          cases hp

theorem column_leaf_base {p : T} (hc : Column p leaf)
    (hn : ∀ a b, S p ≠ P a b) : p = S leaf := by
  generalize he : leaf = a at hc
  cases hc with
  | ancestry hl =>
      have hq := congrArg S he
      rw [cube] at hq
      have hp := lineage_non_phase_two hl (by intro u v h; rw [←hq] at h; cases h)
      rw [cube]
      exact hp
  | literal p y => cases he
  | inverseImage hi =>
      rw [←he] at hi
      rw [←he]
      exact S_injective (image_nonzero_output hi hn)

theorem tower_pair_no_guard (n : Nat) : ¬ ∃ o, Guard leaf (tower n) o := by
  rintro ⟨o,hg⟩
  cases hg with
  | rectangle hp hc hi =>
      have he := image_tower_root n hi
      have hh := column_leaf_base hc (by
        intro a b hh
        rw [he] at hh
        cases n <;> cases hh)
      exact tower_ne_leaf n (S_injective (he.symm.trans hh))
  | cycleReturn hp hi hj =>
      rename_i p
      have he := image_tower_root (n+1) hi
      have hs : nodes p < nodes (P leaf (tower n)) := by
        rcases hp with hp | hp
        · exact Nat.lt_of_le_of_lt (part_nodes hp) (pair_left .zero _ _)
        · exact Nat.lt_of_le_of_lt (part_nodes hp) (pair_right .zero _ _)
      rw [he,nodes_S] at hs
      exact Nat.lt_irrefl _ hs

theorem tower_normal (n : Nat) : Normal (tower n) := by
  induction n with
  | zero => trivial
  | succ n ih => exact ⟨True.intro,ih,tower_pair_no_guard n⟩

theorem tower_nodes (n : Nat) : nodes (tower n) = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (0 + nodes (tower n)) + 1 = n + 1
      rw [Nat.zero_add,ih]

def normalTower (n : Nat) : NormalTree := ⟨tower n,tower_normal n⟩

theorem normalTower_injective {m n : Nat} (h : normalTower m = normalTower n) : m = n := by
  have hn := congrArg (fun t : NormalTree => nodes t.val) h
  change nodes (tower m) = nodes (tower n) at hn
  rwa [tower_nodes,tower_nodes] at hn

end submission.Equation22446Lineage

/- Checked source module: LineageSyntax.ModelObligations -/
set_option autoImplicit false
set_option Elab.async false

namespace submission.Equation22446Lineage
open submission.Equation22446Guarded

/- Two OPEN propositions for this NEW candidate. No assumption from the
refuted old GuardedSyntax uniqueness claim is imported into these proofs. -/
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

/-- Conditional assembly only: both explicit hypotheses remain unproved. -/
theorem infinite_model_if (hu : GuardUnique) (hd : ReturnedImageCovered) :
    (∀ x y z : NormalTree,
      x = multiplication (multiplication y (multiplication x x))
        (multiplication (multiplication x z) z)) ∧
    (∀ {a b : Nat}, normalTower a = normalTower b → a = b) :=
  ⟨normal_tree_source hu hd,normalTower_injective⟩

end submission.Equation22446Lineage

/- Checked source module: LineageSyntax.ReturnedFrontier -/
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

/- Checked source module: LineageSyntax.InverseCycles -/
set_option autoImplicit false
set_option Elab.async false

namespace submission.Equation22446Lineage
open submission.Equation22446Guarded

theorem strict_part_pair_children {a b p : T} (hp : Part (P a b) p)
    (hs : nodes p < nodes (P a b)) : Part a p ∨ Part b p := by
  cases hp with
  | root c t =>
      rw [nodes_rotate] at hs
      exact False.elim (Nat.lt_irrefl _ hs)
  | left c h => exact Or.inl h
  | right c h => exact Or.inr h

/-- The inverse-cycle obstruction that refuted the old syntax is absent
on normal outputs in the new syntax. It is now a theorem, not a hypothesis. -/
theorem normal_inverse_cycle {p b : T} (hb : Normal b)
    (hi : Image p b) (hj : Image b (S p)) : p = S b := by
  classical
  rcases phase_two_or_square_nonzero p with ⟨u,v,hp⟩ | hn
  · by_cases hpair : ∃ a z, b = P a z
    · obtain ⟨a,z,hb'⟩ := hpair
      subst b
      have hs := Nat.lt_of_le_of_lt (image_phase_two_output_left hi u v a z hp rfl)
        (pair_left .zero a z)
      have hv := strict_part_pair_children (image_phase_two_part hi u v hp) hs
      exact False.elim (hb.2.2 ⟨_,.cycleReturn hv hi hj⟩)
    · have he := image_nonzero_output hi (by intro a z he; exact hpair ⟨a,z,he⟩)
      rw [he,cube]
  · exact S_injective (image_nonzero_output hj hn)

theorem raw_double_cycle_target {p z r : T}
    (hi : Image r (P (P p z) z)) (hj : Image (P (P p z) z) (S r))
    (hs : nodes r < nodes (P (P p z) z)) : r = p := by
  obtain ⟨u,v,hr⟩ := cycle_target_phase_two hi hj hs
  generalize hq : P (P p z) z = q at hi
  cases hi with
  | square r => rw [hr] at hq; cases hq
  | literal r t => exact (T.p.inj (T.p.inj hq).2.1).2.1.symm
  | transport hc ht =>
      rw [←(T.p.inj hq).2.1,←(T.p.inj hq).2.2] at ht
      exact False.elim (image_pair_tail_false ht)
  | inverseFollowup t => cases hr
  | returnFollowup ht => cases hr
  | cycleFollowup hs ht hk => cases hr

/-- If the first product is raw, a cycle at the second product returns
exactly S²p, which is already a certified image of p. -/
theorem second_raw_cycle_covered {p z r : T} (hv : Part (P p z) r ∨ Part z r)
    (hi : Image r (P (P p z) z)) (hj : Image (P (P p z) z) (S r)) :
    Image p (S (S r)) := by
  rw [raw_double_cycle_target hi hj (visible_target_smaller hv)]
  exact .square p

end submission.Equation22446Lineage

/- Checked source module: LineageSyntax.ImageObstructions -/
set_option autoImplicit false
set_option Elab.async false

namespace submission.Equation22446Lineage
open submission.Equation22446Guarded

theorem image_no_successor {p : T} (hi : Image p (S p)) : False := by
  rcases phase_two_or_square_nonzero p with ⟨a,b,hp⟩ | hn
  · change p = S (S (P a b)) at hp
    have hq : S p = P a b := by rw [hp,cube]
    have hs := image_phase_two_output_left hi a b a b hp hq
    rw [hp,nodes_S,nodes_S] at hs
    exact Nat.not_lt_of_ge hs (pair_left .zero a b)
  · exact S_ne p (S_injective (image_nonzero_output hi hn)).symm

theorem lineage_trans {p q r : T} (hp : Lineage p q) (hq : Lineage q r) : Lineage p r :=
  match hq with
  | .refl q => hp
  | .step hl hi => .step (lineage_trans hp hl) hi

theorem lineage_image_inverse_false {p q : T} (hi : Image p q)
    (hl : Lineage (S (S q)) p) : False := by
  cases hl with
  | refl =>
      exact image_no_successor (p := S (S q)) (by simpa only [cube] using hi)
  | @step p a b hl hj =>
      have hs := image_phase_two_bound hi a b rfl
      have ht := lineage_nodes hl
      rw [nodes_S,nodes_S] at ht hs
      exact Nat.not_lt_of_ge (Nat.le_trans hs ht) (pair_left .zero a b)

theorem column_left_pair_image_false {p z : T} (hc : Column p (P p z))
    (hi : Image p z) : False := by
  generalize ha : P p z = a at hc
  cases hc with
  | ancestry hl =>
      have he := congrArg S ha
      rw [cube] at he
      have hp := lineage_non_phase_two hl (by intro u v h; rw [←he] at h; cases h)
      have hs := congrArg nodes (hp.trans he.symm)
      rw [nodes_S] at hs
      exact Nat.ne_of_lt (pair_left .zero p z) hs
  | literal p y =>
      rw [(T.p.inj ha).2.2] at hi
      exact image_no_successor hi
  | inverseImage hj =>
      rw [←ha] at hj
      exact lineage_image_inverse_false hi (shrinking_inverse_lineage hj (pair_left .zero p z))

theorem cycle_followup_not_self {u v w t z : T}
    (hi : Image (S (S (P w t))) (P (P u v) z)) :
    P u v ≠ P (S (P w t)) z := by
  intro he
  have hu := (T.p.inj he).2.1
  generalize hp : S (S (P w t)) = p at hi
  generalize hq : P (P u v) z = q at hi
  cases hi with
  | square p => rw [←hp] at hq; cases hq
  | literal p y =>
      have hu' := (T.p.inj (T.p.inj hq).2.1).2.1
      rw [hu',←hp] at hu
      cases hu
  | transport hc hj =>
      rw [←hp,←(T.p.inj hq).2.1] at hc
      have ht := column_zero_to_two hc
      rw [ht] at he
      have hs := congrArg nodes he
      have hb := pair_left .zero (S (P w t)) z
      change nodes (S (P w t)) < nodes (P (S (P w t)) z) at hb
      rw [nodes_S,←hs] at hb
      exact Nat.lt_irrefl _ hb
  | inverseFollowup p => cases hp
  | returnFollowup hj => cases hp
  | cycleFollowup hs hj hk => cases hp

theorem image_self_eq_false {p q : T} (h : Image p q) (hp : q = p) : False := by
  cases h with
  | square p => exact SS_ne p hp
  | literal p z =>
      have hn := congrArg nodes hp
      exact Nat.ne_of_lt (Nat.lt_trans (pair_left .zero _ _) (pair_left .zero _ _)) hn.symm
  | transport hc hi =>
      rw [←hp] at hc
      exact column_left_pair_image_false hc hi
  | inverseFollowup p => exact SS_ne p (T.p.inj hp).2.1
  | returnFollowup hi => exact S_ne _ (S_injective (T.p.inj hp).2.1).symm
  | cycleFollowup hs hi hj => exact cycle_followup_not_self hi hp.symm

theorem image_no_self {p : T} (h : Image p p) : False := image_self_eq_false h rfl

theorem image_rotated_lineage_false {p q : T} (hi : Image p q)
    (hl : Lineage (S (S q)) (S (S p))) : False := by
  generalize he : S (S p) = t at hl
  cases hl with
  | refl =>
      have hp := S_injective (S_injective he)
      rw [hp] at hi
      exact image_no_self hi
  | @step p' a b hl hj =>
      have hp := S_injective (S_injective he)
      have hs := lineage_nodes hl
      rw [nodes_S,nodes_S] at hs
      have hsmall : nodes q < nodes p := by
        rw [hp]
        exact Nat.lt_of_le_of_lt hs (pair_left .zero a b)
      have hq := image_shrinking_lineage hi a b hp hsmall
      exact lineage_image_inverse_false hj (lineage_trans hq hl)

theorem image_pair_flip_false {p q : T} (hi : Image p q)
    (hj : Image (P p q) p) : False :=
  image_rotated_lineage_false hi (image_shrinking_lineage hj p q rfl (pair_left .zero p q))

end submission.Equation22446Lineage

/- Checked source module: LineageSyntax.CycleCoverage -/
set_option autoImplicit false
set_option Elab.async false

namespace submission.Equation22446Lineage
open submission.Equation22446Guarded

/-- Every cycle return at the SECOND multiplication is covered, for every
first Product trace. Normality is not needed. -/
theorem second_cycle_covered {p z u r : T} (hm : Product p z u)
    (hv : Part u r ∨ Part z r) (hi : Image r (P u z))
    (hj : Image (P u z) (S r)) : Image p (S (S r)) := by
  have hs := visible_target_smaller hv
  obtain ⟨a,b,hu⟩ := cycle_left_phase_zero hi hj hs
  obtain ⟨w,t,hr⟩ := cycle_target_phase_two hi hj hs
  generalize hq : P u z = q at hi
  cases hi with
  | square r => rw [hr] at hq; cases hq
  | literal r v =>
      have he := (T.p.inj hq).2.1
      have hz := (T.p.inj hq).2.2
      rw [←hz] at he
      rw [←product_pair_tail_root hm r he]
      exact .square p
  | transport hc ht =>
      rw [←(T.p.inj hq).2.1,←(T.p.inj hq).2.2] at ht
      rw [←(T.p.inj hq).2.1,hr,hu] at hc
      have he := column_zero_to_two hc
      have hr' : r = S (S u) := by rw [hu,he]; exact hr
      rw [hr',cube] at hj
      exact False.elim (image_pair_flip_false ht hj)
  | inverseFollowup r => cases hr
  | returnFollowup ht => cases hr
  | cycleFollowup hs ht hk => cases hr

theorem cycle_return_covered : CycleReturnCovered := by
  intro p z u r hp hz hm hv hi hj
  exact second_cycle_covered hm hv hi hj

theorem returned_coverage_of_rectangle (hr : RectangleReturnCovered) : ReturnedImageCovered :=
  returned_coverage_of_rectangle_cycle hr cycle_return_covered

theorem returned_coverage_iff_rectangle : ReturnedImageCovered ↔ RectangleReturnCovered := by
  constructor
  · intro hd
    exact (returned_coverage_iff_rectangle_cycle.mp hd).1
  · exact returned_coverage_of_rectangle

theorem source_from_rectangle_obligations (hu : GuardUnique) (hr : RectangleReturnCovered) :
    ∀ x y z : NormalTree,
      x = multiplication (multiplication y (multiplication x x))
        (multiplication (multiplication x z) z) :=
  normal_tree_source hu (returned_coverage_of_rectangle hr)

end submission.Equation22446Lineage

/- Checked source module: LineageSyntax.DiagonalSupport -/
set_option autoImplicit false
set_option Elab.async false

namespace submission.Equation22446Lineage
open submission.Equation22446Guarded

theorem lineage_nonincreasing_eq {p q : T} (h : Lineage p q)
    (hs : nodes q ≤ nodes p) : p = q := by
  cases h with
  | refl => rfl
  | @step p a b hl hi =>
      have ht := lineage_nodes hl
      have hb := pair_left .two a b
      exact False.elim (Nat.not_lt_of_ge hs (Nat.lt_of_le_of_lt ht hb))

theorem image_phase_two_strict {p q : T} (h : Image p q)
    (hp : ∃ a b, p = S (S (P a b))) (hq : ∃ u v, q = P u v) : nodes p < nodes q := by
  obtain ⟨a,b,hp⟩ := hp
  obtain ⟨u,v,hq⟩ := hq
  rw [hq]
  exact Nat.lt_of_le_of_lt (image_phase_two_output_left h a b u v hp hq) (pair_left .zero u v)

theorem image_no_swapped_successors {p a : T} (hp : Image p (S a))
    (ha : Image a (S p)) : False := by
  have ordinary {p a : T} (hp : Image p (S a)) (ha : Image a (S p))
      (hn : ∀ u v, S a ≠ P u v) : False := by
    have he := congrArg S (image_nonzero_output hp hn)
    rw [cube] at he
    rw [←he,cube] at ha
    exact image_no_self ha
  rcases phase_two_or_square_nonzero p with ⟨u,v,hp'⟩ | hn
  · rcases phase_two_or_square_nonzero a with ⟨r,s,ha'⟩ | hn
    · have hbig := image_phase_two_strict hp ⟨u,v,hp'⟩ ⟨r,s,by rw [ha']; rfl⟩
      have hsmall := image_phase_two_bound ha r s ha'
      rw [nodes_S] at hbig hsmall
      exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hbig hsmall)
    · exact ordinary hp ha hn
  · exact ordinary ha hp hn

theorem image_lineage_false {p q : T} (hi : Image p q) (hl : Lineage p q) : False := by
  cases hl with
  | refl => exact image_no_self hi
  | @step p a b hl hj =>
      have he := image_nonzero_output hi (by intro u v h; cases h)
      have hs := congrArg nodes he
      rw [nodes_S,nodes_S,nodes_S,nodes_S] at hs
      have ht := lineage_nodes hl
      have hb := pair_left .zero a b
      change nodes a < nodes (P a b) at hb
      rw [hs] at hb
      exact Nat.not_lt_of_ge ht hb

theorem column_image_next_false {p a : T} (hc : Column p a) (hi : Image p (S a)) : False := by
  cases hc with
  | ancestry hl => rw [cube] at hi; exact image_lineage_false hi hl
  | literal p y =>
      have he := image_nonzero_output hi (by intro u v h; cases h)
      have hs := congrArg nodes he
      rw [nodes_S,nodes_S,nodes_S] at hs
      have hb := pair_right .zero y (S p)
      change nodes (S p) < nodes (P y (S p)) at hb
      rw [nodes_S,hs] at hb
      exact Nat.lt_irrefl _ hb
  | inverseImage hj => exact image_no_swapped_successors hi hj

theorem strict_cycle_square_right_false {p r : T} (hi : Image r (P p (S p)))
    (hj : Image (P p (S p)) (S r)) (hs : nodes r < nodes (P p (S p))) : False := by
  have hl := shrinking_inverse_lineage hj hs
  rw [cube] at hl
  obtain ⟨a,b,hr⟩ := cycle_target_phase_two hi hj hs
  obtain ⟨u,v,hp⟩ := cycle_left_phase_zero hi hj hs
  have hb := image_phase_two_output_left hi a b p (S p) hr rfl
  have he := lineage_nonincreasing_eq hl hb
  rw [hp,hr] at he
  cases he

end submission.Equation22446Lineage

/- Checked source module: LineageSyntax.NormalDiagonal -/
set_option autoImplicit false
set_option Elab.async false

namespace submission.Equation22446Lineage
open submission.Equation22446Guarded

theorem normal_literal_diagonal {p y b : T} (hb : Normal b)
    (hi : Image p b) (he : b = P y (S p)) : p = S b := by
  cases hi with
  | square p => exact (cube p).symm
  | literal p t =>
      have ht := (T.p.inj he).2.2
      rw [ht] at hb
      exact False.elim (hb.2.2 ⟨_,.inverseDouble p⟩)
  | transport hc hj =>
      rw [(T.p.inj he).2.2] at hj
      exact False.elim (column_image_next_false hc hj)
  | inverseFollowup p =>
      have hp := S_injective (T.p.inj he).2.2
      have hn := congrArg nodes hp
      exact False.elim (Nat.ne_of_lt (pair_left .zero p (S p)) hn)
  | @returnFollowup p q hj =>
      have hp := S_injective (T.p.inj he).2.2
      have hn := congrArg nodes hp
      have hs := pair_right .zero (S (S (P p q))) (S p)
      change nodes (S p) < nodes (P (S (S (P p q))) (S p)) at hs
      rw [nodes_S] at hs
      exact False.elim (Nat.lt_irrefl _ (by rwa [←hn] at hs))
  | cycleFollowup hs hj hk =>
      have hz := (T.p.inj he).2.2
      rw [hz] at hj hk hs
      exact False.elim (strict_cycle_square_right_false hj hk hs)

theorem normal_diagonal_target {p b : T} (hb : Normal b)
    (hc : Column p b) (hi : Image p b) : p = S b := by
  cases hc with
  | ancestry hl =>
      cases hl with
      | refl p => exact (cube p).symm
      | step hl hj =>
          have he := congrArg S (image_nonzero_output hi (by intro u v h; cases h))
          simpa only [cube] using he.symm
  | literal p y => exact normal_literal_diagonal hb hi rfl
  | inverseImage hj => exact normal_inverse_cycle hb hi hj

theorem diagonal_cycle_false {b r : T} (hi : Image r (P b b))
    (hj : Image (P b b) (S r)) (hs : nodes r < nodes (P b b)) : False := by
  obtain ⟨u,v,hr⟩ := cycle_target_phase_two hi hj hs
  have hl := image_phase_two_output_left hi u v b b hr rfl
  have hb := image_right_child hj .zero b b (by intro h; cases h) rfl
  rw [nodes_S] at hb
  exact Nat.not_lt_of_ge hl hb

theorem normal_diagonal_guard_eq {a b o : T} (h : Guard a b o) (he : a = b)
    (hb : Normal b) : o = S b := by
  cases h with
  | rectangle hp hc hi =>
      rw [he] at hc
      exact normal_diagonal_target hb hc hi
  | inverseDouble p => rfl
  | @imageReturn p q hi =>
      have hn := congrArg nodes he
      have hs := pair_right .zero (S (S (P p q))) (S p)
      change nodes (S p) < nodes (P (S (S (P p q))) (S p)) at hs
      rw [hn] at hs
      exact False.elim (Nat.lt_irrefl _ hs)
  | cycleReturn hp hi hj =>
      have hs := visible_target_smaller hp
      rw [he] at hi hj hs
      exact False.elim (diagonal_cycle_false hi hj hs)

theorem normal_diagonal_product {b o : T} (hb : Normal b) (h : Product b b o) : o = S b := by
  cases h with
  | raw hn => exact False.elim (hn ⟨_,diagonal_guard b⟩)
  | hit hg => exact normal_diagonal_guard_eq hg rfl hb

theorem chosen_square_unconditional {b : T} (hb : Normal b) : chosen b b = S b :=
  normal_diagonal_product hb (chosen_product b b)

theorem multiplication_square (b : NormalTree) : (multiplication b b).val = S b.val :=
  chosen_square_unconditional b.property

end submission.Equation22446Lineage

/- Checked source module: LineageSyntax.CycleUniqueness -/
set_option autoImplicit false
set_option Elab.async false

namespace submission.Equation22446Lineage
open submission.Equation22446Guarded

theorem cycle_target_alternatives {a b r : T} (hi : Image r (P a b))
    (hj : Image (P a b) (S r)) (hs : nodes r < nodes (P a b)) :
    a = P r b ∨ (r = S (S a) ∧ Image a b) := by
  obtain ⟨u,v,ha⟩ := cycle_left_phase_zero hi hj hs
  obtain ⟨w,t,hr⟩ := cycle_target_phase_two hi hj hs
  generalize hq : P a b = q at hi
  cases hi with
  | square r => rw [hr] at hq; cases hq
  | literal r z =>
      have he := (T.p.inj hq).2.1
      rw [←(T.p.inj hq).2.2] at he
      exact Or.inl he
  | transport hc ht =>
      rw [←(T.p.inj hq).2.1,←(T.p.inj hq).2.2] at ht
      rw [←(T.p.inj hq).2.1,ha,hr] at hc
      have he := column_zero_to_two hc
      right
      refine ⟨?_,ht⟩
      rw [ha,he]
      exact hr
  | inverseFollowup r => cases hr
  | returnFollowup ht => cases hr
  | cycleFollowup hs ht hk => cases hr

/-- Strict cycles on the same raw pair have a unique target, even before
assuming that the two children are normal. -/
theorem cycle_target_unique {a b r s : T}
    (hr : Image r (P a b)) (hr' : Image (P a b) (S r))
    (hs : Image s (P a b)) (hs' : Image (P a b) (S s))
    (nr : nodes r < nodes (P a b)) (ns : nodes s < nodes (P a b)) : r = s := by
  rcases cycle_target_alternatives hr hr' nr with he | ⟨he,hi⟩
  · rcases cycle_target_alternatives hs hs' ns with hf | ⟨hf,hj⟩
    · exact (T.p.inj (he.symm.trans hf)).2.1
    · rw [he] at hj
      exact False.elim (image_pair_tail_false hj)
  · rcases cycle_target_alternatives hs hs' ns with hf | ⟨hf,hj⟩
    · rw [hf] at hi
      exact False.elim (image_pair_tail_false hi)
    · exact he.trans hf.symm

theorem cycle_guard_outputs_equal {a b r s : T}
    (vr : Part a r ∨ Part b r) (hr : Image r (P a b)) (hr' : Image (P a b) (S r))
    (vs : Part a s ∨ Part b s) (hs : Image s (P a b)) (hs' : Image (P a b) (S s)) :
    S (S r) = S (S s) :=
  congrArg (fun t => S (S t))
    (cycle_target_unique hr hr' hs hs' (visible_target_smaller vr) (visible_target_smaller vs))

theorem inverse_cycle_overlap {p r : T} (hv : Part (P p (S p)) r ∨ Part (S p) r)
    (hi : Image r (P (P p (S p)) (S p)))
    (hj : Image (P (P p (S p)) (S p)) (S r)) : S (S r) = S (S p) := by
  rw [raw_double_cycle_target hi hj (visible_target_smaller hv)]

theorem image_return_cycle_overlap {p q r : T}
    (hv : Part (P (S (S (P p q))) (S p)) r ∨ Part (S p) r)
    (hi : Image r (P (P (S (S (P p q))) (S p)) (S p)))
    (hj : Image (P (P (S (S (P p q))) (S p)) (S p)) (S r)) :
    S (S r) = S (P p q) := by
  rw [raw_double_cycle_target hi hj (visible_target_smaller hv),cube]

end submission.Equation22446Lineage

/- Checked source module: LineageSyntax.SpecialUniqueness -/
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

/-- The remaining uniqueness question consists exactly of overlaps having
at least one rectangle return. This is an explicit open proposition. -/
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

/- Checked source module: LineageSyntax.RightSquareObstructions -/
set_option autoImplicit false
set_option Elab.async false

namespace submission.Equation22446Lineage
open submission.Equation22446Guarded

theorem image_no_successive_outputs {p q : T} (hi : Image p q) (hj : Image p (S q)) : False := by
  classical
  by_cases hq : ∃ a b, q = P a b
  · obtain ⟨a,b,hq⟩ := hq
    have he := image_nonzero_output hj (by intro u v h; rw [hq] at h; cases h)
    rw [S_injective he] at hi
    exact image_no_successor hi
  · have he := image_nonzero_output hi (by intro a b h; exact hq ⟨a,b,h⟩)
    rw [he,cube] at hj
    exact image_no_self hj

theorem column_pair_successor_tail_false {a b : T} (hc : Column (S b) (P a b)) : False := by
  generalize he : P a b = t at hc
  cases hc with
  | ancestry hl =>
      have ha := congrArg S he
      rw [cube] at ha
      have hb := lineage_non_phase_two hl (by intro u v h; rw [←ha] at h; cases h)
      have eq := S_injective (hb.trans ha.symm)
      have hn := congrArg nodes eq
      exact Nat.ne_of_lt (pair_right .zero a b) hn
  | literal p y =>
      exact SS_ne b (T.p.inj he).2.2.symm
  | inverseImage hi =>
      rw [←he] at hi
      have hs := image_right_child hi .zero a b (by intro h; cases h) rfl
      rw [nodes_S,nodes_S] at hs
      exact Nat.lt_irrefl _ hs

theorem raw_column_square_image_false {p a b : T} (hc : Column p (P a b))
    (hi : Image (P a b) (S (S p))) : False := by
  generalize he : P a b = t at hc
  cases hc with
  | ancestry hl =>
      have ha := congrArg S he
      rw [cube] at ha
      have hp := lineage_non_phase_two hl (by intro u v h; rw [←ha] at h; cases h)
      rw [hp,←ha,cube] at hi
      exact image_no_self hi
  | literal p y =>
      have hb := (T.p.inj he).2.2
      have hs := image_right_child hi .zero a b (by intro h; cases h) rfl
      rw [hb,nodes_S,nodes_S,nodes_S] at hs
      exact Nat.lt_irrefl _ hs
  | inverseImage hj =>
      rw [←he] at hj
      exact image_no_successive_outputs hj hi

theorem image_nonzero_target {p b : T} (hi : Image p b)
    (hn : ∀ u v, b ≠ P u v) : p = S b := by
  have he := congrArg S (image_nonzero_output hi hn)
  simpa only [cube] using he.symm

end submission.Equation22446Lineage

/- Checked source module: LineageSyntax.NonzeroRectangles -/
set_option autoImplicit false
set_option Elab.async false

namespace submission.Equation22446Lineage
open submission.Equation22446Guarded

theorem rectangle_nonzero_right_unique {p a b o : T} (hc : Column p a) (hi : Image p b)
    (hg : Guard a b o) (hn : ∀ u v, b ≠ P u v) : p = o := by
  have hp := image_nonzero_target hi hn
  subst p
  cases hg with
  | rectangle hv hc' hi' => exact (image_nonzero_target hi' hn).symm
  | inverseDouble v => rfl
  | imageReturn ht => exact False.elim (column_pair_successor_tail_false hc)
  | cycleReturn hv ht hk =>
      have hs := visible_target_smaller hv
      rcases cycle_target_alternatives ht hk hs with ha | ⟨hr,hj⟩
      · rw [ha] at hc
        exact False.elim (column_pair_successor_tail_false hc)
      · obtain ⟨u,v,ha⟩ := cycle_left_phase_zero ht hk hs
        rw [ha] at hc hj
        have hi' : Image (P u v) (S (S (S b))) := by simpa only [cube] using hj
        exact False.elim (raw_column_square_image_false hc hi')

theorem guard_nonzero_right_unique {a b u v : T} (hn : ∀ x y, b ≠ P x y)
    (hu : Guard a b u) (hv : Guard a b v) : u = v := by
  rcases guard_rectangle_or_special hu with ⟨hp,hc,hi⟩ | hu
  · exact rectangle_nonzero_right_unique hc hi hv hn
  · rcases guard_rectangle_or_special hv with ⟨hp,hc,hi⟩ | hv
    · exact (rectangle_nonzero_right_unique hc hi (special_guard hu) hn).symm
    · exact special_unique hu hv

def ZeroRightRectangleUnique : Prop := ∀ {p a u v o : T}, Normal a → Normal (P u v) →
  Column p a → Image p (P u v) → Guard a (P u v) o → p = o

theorem rectangle_unique_iff_zero_right : RectangleGuardUnique ↔ ZeroRightRectangleUnique := by
  classical
  constructor
  · intro h p a u v o ha hb hc hi hg
    exact h ha hb hc hi hg
  · intro h p a b o ha hb hc hi hg
    by_cases hz : ∃ u v, b = P u v
    · obtain ⟨u,v,hb'⟩ := hz
      subst b
      exact h ha hb hc hi hg
    · exact rectangle_nonzero_right_unique hc hi hg (by intro u v he; exact hz ⟨u,v,he⟩)

theorem source_from_zero_right_rectangles (hu : ZeroRightRectangleUnique)
    (hr : RectangleReturnCovered) : ∀ x y z : NormalTree,
      x = multiplication (multiplication y (multiplication x x))
        (multiplication (multiplication x z) z) :=
  source_from_rectangle_conditions (rectangle_unique_iff_zero_right.mpr hu) hr

end submission.Equation22446Lineage

/- Checked source module: LineageSyntax.PhaseOneOrigins -/
set_option autoImplicit false
set_option Elab.async false

namespace submission.Equation22446Lineage
open submission.Equation22446Guarded

/- The old phase-one LEFT SIZE bound is false. The following weaker origin
statement survives: a strictly smaller query exposes the stored Image. -/
mutual
theorem image_small_phase_one_origin {p q : T} (h : Image p q) :
    ∀ u v, p = S (P u v) → nodes q < nodes p → Image u v :=
  match h with
  | .square p => by
      intro u v hp hs
      rw [nodes_S,nodes_S] at hs
      exact False.elim (Nat.lt_irrefl _ hs)
  | .literal p z => by
      intro u v hp hs
      exact False.elim (Nat.lt_irrefl _ (Nat.lt_trans
        (Nat.lt_trans (pair_left .zero _ _) (pair_left .zero _ _)) hs))
  | .transport hc hi => by
      intro u v hp hs
      exact column_small_phase_one_origin hc u v hp (Nat.lt_trans (pair_left .zero _ _) hs)
  | .inverseFollowup p => by intro u v hp hs; cases hp
  | .returnFollowup hi => by intro u v hp hs; cases hp
  | .cycleFollowup ht hi hj => by intro u v hp hs; cases hp
theorem column_small_phase_one_origin {p a : T} (h : Column p a) :
    ∀ u v, a = S (P u v) → nodes p < nodes a → Image u v :=
  match h with
  | .ancestry hl => by
      intro u v ha hs
      cases hl with
      | refl =>
          rw [nodes_S,nodes_S] at hs
          exact False.elim (Nat.lt_irrefl _ hs)
      | step hl hi =>
          simp only [cube] at ha
          have he := S_injective ha
          rw [(T.p.inj he).2.1,(T.p.inj he).2.2] at hi
          exact hi
  | .literal p y => by intro u v ha hs; cases ha
  | .inverseImage hi => by
      intro u v ha hs
      exact image_small_phase_one_origin hi u v ha (by rwa [nodes_S])
end

/-- A zero-color column base need not equal the phase-one pair's left
child; it is an ancestor of that child. This replaces the old head claim. -/
theorem column_zero_phase_one_origin {u v x y : T}
    (hc : Column (P u v) (S (P x y))) : Lineage (P u v) x ∧ Image x y := by
  generalize ha : S (P x y) = a at hc
  cases hc with
  | ancestry hl =>
      have he := congrArg S ha
      rw [cube] at he
      rw [←he] at hl
      cases hl with
      | step hl hi => exact ⟨hl,hi⟩
  | literal p z => cases ha
  | inverseImage hi =>
      rw [←ha] at hi
      have he := image_nonzero_output hi (by intro a b h; cases h)
      rw [cube] at he
      cases he

theorem lineage_non_two_roots_unique {p q a : T}
    (hp : ∀ u v, p ≠ S (S (P u v))) (hq : ∀ u v, q ≠ S (S (P u v)))
    (hl : Lineage p a) (hm : Lineage q a) : p = q :=
  match hl with
  | .refl p => (lineage_non_phase_two hm hp).symm
  | .step hl hi => by
      cases hm with
      | refl => exact False.elim (hq _ _ rfl)
      | step hm hj => exact lineage_non_two_roots_unique hp hq hl hm

theorem column_phase_zero_unique {u v w z a : T}
    (hp : Column (P u v) a) (hq : Column (P w z) a) : P u v = P w z := by
  cases hp with
  | ancestry hl =>
      cases hl with
      | refl => exact (column_zero_to_two hq).symm
      | step hl hi =>
          simp only [cube] at hq
          have hr := (column_zero_phase_one_origin hq).1
          exact lineage_non_two_roots_unique (by intro x y h; cases h)
            (by intro x y h; cases h) hl hr
  | literal p y =>
      generalize ha : P y (S (P u v)) = a at hq
      cases hq with
      | ancestry hl =>
          have he := congrArg S ha
          rw [cube] at he
          have hr := lineage_non_phase_two hl (by intro x y h; rw [←he] at h; cases h)
          have he' := hr.trans he.symm
          cases he'
      | literal p y' => exact S_injective (T.p.inj ha).2.2
      | inverseImage hi =>
          rw [←ha] at hi
          have he := image_nonzero_output hi (by intro x y h; cases h)
          cases he
  | inverseImage hi =>
      have ha := congrArg S (image_nonzero_output hi (by intro x y h; cases h))
      rw [cube] at ha
      rw [←ha] at hq
      exact (column_zero_to_two hq).symm

theorem old_phase_one_head_equality_false :
    ¬ (∀ u v x y : T, Column (P u v) (S (P x y)) → P u v = x) := by
  intro h
  let e : T := .e .zero 0
  let p := P e (S e)
  let q := S (S (P p (S (S p))))
  have hl : Lineage p q := .step (.refl p) (.square p)
  have hc : Column p (S (P q (S (S q)))) := .ancestry (.step hl (.square q))
  have he := h e (S e) q (S (S q)) hc
  have hn := congrArg nodes he
  change 1 = 3 at hn
  cases hn

end submission.Equation22446Lineage

/- Checked source module: LineageSyntax.AncestralBounds -/
set_option autoImplicit false
set_option Elab.async false

namespace submission.Equation22446Lineage
open submission.Equation22446Guarded

theorem lineage_common_size_unique {p q r : T} (hl : Lineage p r) (hm : Lineage q r)
    (hs : nodes p = nodes q) : p = q :=
  match hl with
  | .refl p => (lineage_nonincreasing_eq hm (Nat.le_of_eq hs)).symm
  | .step hl hi => by
      cases hm with
      | refl => exact lineage_nonincreasing_eq (.step hl hi) (Nat.le_of_eq hs.symm)
      | step hm hj => exact lineage_common_size_unique hl hm hs

theorem non_two_lineage_common_lower {p q r : T}
    (hp : ∀ u v, p ≠ S (S (P u v))) (hl : Lineage p r) (hm : Lineage q r) :
    nodes p ≤ nodes q :=
  match hl with
  | .refl p => by rw [lineage_non_phase_two hm hp]; exact Nat.le_refl _
  | .step hl hi => by
      cases hm with
      | refl => exact lineage_nodes (.step hl hi)
      | step hm hj => exact non_two_lineage_common_lower hp hl hm

/- A non-two-color ANCESTOR gives a valid bound even when the immediate
phase-one head can be much larger than its query output. -/
mutual
theorem image_ancestor_bound {p q : T} (h : Image p q) :
    ∀ a u v, p = S (P u v) → (∀ x y, a ≠ S (S (P x y))) → Lineage a u → nodes a < nodes q :=
  match h with
  | .square p => by
      intro a u v hp ha hl
      rw [nodes_S,nodes_S,hp,nodes_S]
      exact Nat.lt_of_le_of_lt (lineage_nodes hl) (pair_left .zero u v)
  | .literal p z => by
      intro a u v hp ha hl
      have hs : nodes a < nodes p := by
        rw [hp,nodes_S]
        exact Nat.lt_of_le_of_lt (lineage_nodes hl) (pair_left .zero u v)
      exact Nat.lt_trans hs (Nat.lt_trans (pair_left .zero _ _) (pair_left .zero _ _))
  | .transport hc hi => by
      intro a u v hp ha hl
      exact Nat.lt_of_le_of_lt (column_ancestor_bound hc a u v hp ha hl) (pair_left .zero _ _)
  | .inverseFollowup p => by intro a u v hp ha hl; cases hp
  | .returnFollowup hi => by intro a u v hp ha hl; cases hp
  | .cycleFollowup hs hi hj => by intro a u v hp ha hl; cases hp
theorem column_ancestor_bound {p q : T} (h : Column p q) :
    ∀ a u v, q = S (P u v) → (∀ x y, a ≠ S (S (P x y))) → Lineage a u → nodes a ≤ nodes p :=
  match h with
  | .ancestry hm => by
      intro a u v hq ha hl
      cases hm with
      | refl =>
          have hp := congrArg S hq
          rw [cube] at hp
          rw [hp,nodes_S,nodes_S]
          exact Nat.le_trans (lineage_nodes hl) (Nat.le_of_lt (pair_left .zero u v))
      | step hm hi =>
          simp only [cube] at hq
          have he := S_injective hq
          rw [(T.p.inj he).2.1] at hm
          exact non_two_lineage_common_lower ha hl hm
  | .literal p y => by intro a u v hq ha hl; cases hq
  | .inverseImage hi => by
      intro a u v hq ha hl
      have hs := image_ancestor_bound hi a u v hq ha hl
      rw [nodes_S] at hs
      exact Nat.le_of_lt hs
end

end submission.Equation22446Lineage

/- Checked source module: LineageSyntax.LineageReversal -/
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

/- Checked source module: LineageSyntax.NonzeroCoverage -/
set_option autoImplicit false
set_option Elab.async false

namespace submission.Equation22446Lineage
open submission.Equation22446Guarded

/-- A second rectangle return is impossible when the unchanged right
argument is not a zero-color pair. No Normal premise is needed. -/
theorem nonzero_rectangle_double_false {p z u b : T} (hm : Product p z u)
    (hc : Column b u) (hi : Image b z) (hn : ∀ a c, z ≠ P a c) : False := by
  have hb := image_nonzero_target hi hn
  subst b
  cases hm with
  | raw h => exact column_pair_successor_tail_false hc
  | hit hg =>
      cases hg with
      | rectangle hv hk hj =>
          rw [image_nonzero_target hj hn] at hc
          exact column_no_self hc
      | inverseDouble v => exact column_no_self hc
      | @imageReturn v q hj =>
          exact lineage_inverse_column_false (.step (.refl v) hj) hc
      | cycleReturn hv hj hk =>
          have hl := shrinking_inverse_lineage hk (visible_target_smaller hv)
          exact lineage_inverse_column_false hl (by simpa only [cube] using hc)

theorem product_double_image_nonzero_right {p z u b : T}
    (h1 : Product p z u) (h2 : Product u z b) (hn : ∀ a c, z ≠ P a c) : Image p b := by
  cases h2 with
  | raw h => exact product_raw_followup h1
  | hit hg =>
      cases hg with
      | rectangle hv hc hi => exact False.elim (nonzero_rectangle_double_false h1 hc hi hn)
      | inverseDouble v => exact second_inverse_covered h1
      | imageReturn hi => exact second_return_covered h1
      | cycleReturn hv hi hj => exact second_cycle_covered h1 hv hi hj

def ZeroRightRectangleCovered : Prop := ∀ {p v w u b : T}, Normal p → Normal (P v w) →
  Product p (P v w) u → (Part u b ∨ Part (P v w) b) → Column b u → Image b (P v w) → Image p b

theorem rectangle_coverage_iff_zero_right : RectangleReturnCovered ↔ ZeroRightRectangleCovered := by
  classical
  constructor
  · intro h p v w u b hp hz hm hv hc hi
    exact h hp hz hm hv hc hi
  · intro h p z u b hp hz hm hv hc hi
    by_cases hzero : ∃ v w, z = P v w
    · obtain ⟨v,w,hz'⟩ := hzero
      subst z
      exact h hp hz hm hv hc hi
    · exact False.elim (nonzero_rectangle_double_false hm hc hi
        (by intro v w he; exact hzero ⟨v,w,he⟩))

theorem source_from_zero_right_conditions (hu : ZeroRightRectangleUnique)
    (hr : ZeroRightRectangleCovered) : ∀ x y z : NormalTree,
      x = multiplication (multiplication y (multiplication x x))
        (multiplication (multiplication x z) z) :=
  source_from_zero_right_rectangles hu (rectangle_coverage_iff_zero_right.mpr hr)

end submission.Equation22446Lineage

/- Checked source module: LineageSyntax.PrincipalPairs -/
set_option autoImplicit false
set_option Elab.async false

namespace submission.Equation22446Lineage
open submission.Equation22446Guarded

theorem image_no_left_pair {p q : T} (h : Image p q) : ∀ z, q = P p z → False := by
  intro z he
  cases h with
  | square p =>
      have hs := congrArg nodes he
      rw [nodes_S,nodes_S] at hs
      exact Nat.ne_of_lt (pair_left .zero p z) hs
  | literal p t =>
      exact Nat.ne_of_lt (pair_left .zero p t) (congrArg nodes (T.p.inj he).2.1).symm
  | transport hc hi =>
      rw [(T.p.inj he).2.1] at hc
      exact column_no_self hc
  | inverseFollowup p =>
      have hs := congrArg nodes (T.p.inj he).2.1
      rw [nodes_S,nodes_S] at hs
      exact Nat.ne_of_lt (pair_left .zero p (S p)) hs
  | @returnFollowup p q hi =>
      have hs := congrArg nodes (T.p.inj he).2.1
      rw [nodes_S] at hs
      have hb := pair_left .zero (S (S (P p q))) (S p)
      rw [nodes_S,nodes_S] at hb
      exact Nat.ne_of_lt hb hs
  | cycleFollowup hs hi hj => cases (T.p.inj he).2.1

/-- A rectangle on (P(a,b),b) can only target the successor of P(a,b). -/
theorem principal_pair_target {p a b : T} (hc : Column p (P a b))
    (hi : Image p b) : p = S (P a b) := by
  generalize he : P a b = t at hc
  cases hc with
  | ancestry hl =>
      have ha := congrArg S he
      rw [cube] at ha
      have hp := lineage_non_phase_two hl (by intro u v h; rw [←ha] at h; cases h)
      simpa only [cube] using hp
  | literal p y =>
      rw [(T.p.inj he).2.2] at hi
      exact False.elim (image_no_successor hi)
  | inverseImage hj =>
      rw [←he] at hj
      rcases phase_two_or_square_nonzero p with ⟨u,v,hp⟩ | hn
      · have hs := image_phase_two_bound hi u v hp
        have ht := image_right_child hj .zero a b (by intro h; cases h) rfl
        rw [nodes_S] at ht
        exact False.elim (Nat.not_lt_of_ge hs ht)
      · rw [←he]
        exact S_injective (image_nonzero_output hj hn)

theorem principal_pair_inner_image {p a b : T} (hc : Column p (P a b))
    (hi : Image p b) : Image a b := by
  have hp := principal_pair_target hc hi
  exact image_small_phase_one_origin hi a b hp (by rw [hp,nodes_S]; exact pair_right .zero a b)

theorem rectangle_inverse_double_false {r p : T} (hc : Column r (P p (S p)))
    (hi : Image r (S p)) : False := image_no_successor (principal_pair_inner_image hc hi)

theorem rectangle_image_return_false {r p q : T}
    (hc : Column r (P (S (S (P p q))) (S p))) (hi : Image r (S p)) : False := by
  have hj := principal_pair_inner_image hc hi
  have hs := image_phase_two_bound hj p q rfl
  rw [nodes_S,nodes_S,nodes_S] at hs
  exact Nat.not_lt_of_ge hs (pair_left .zero p q)

end submission.Equation22446Lineage

/- Checked source module: LineageSyntax.SpecialExclusion -/
set_option autoImplicit false
set_option Elab.async false

namespace submission.Equation22446Lineage
open submission.Equation22446Guarded

/-- The transported alternative is impossible by image-pair flip exclusion.
Every strict cycle is a literal raw double-image return. -/
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

/- Checked source module: LineageSyntax.PrincipalFrontier -/
set_option autoImplicit false
set_option Elab.async false

namespace submission.Equation22446Lineage
open submission.Equation22446Guarded

def ZeroRightPrincipalUnique : Prop := ∀ {a u v p q : T}, Normal a → Normal (P u v) →
  Column p a → Image p (P u v) → Column q a → Image q (P u v) → p = q

theorem principal_unique_iff_zero_right : PrincipalUnique ↔ ZeroRightPrincipalUnique := by
  classical
  constructor
  · intro h a u v p q ha hb hc hi hc' hi'
    exact h ha hb hc hi hc' hi'
  · intro h a b p q ha hb hc hi hc' hi'
    by_cases hz : ∃ u v, b = P u v
    · obtain ⟨u,v,hb'⟩ := hz
      subst b
      exact h ha hb hc hi hc' hi'
    · have hn : ∀ u v, b ≠ P u v := by intro u v he; exact hz ⟨u,v,he⟩
      exact (image_nonzero_target hi hn).trans (image_nonzero_target hi' hn).symm

/-- Every remaining principal conflict has a zero-color pair on the right,
unequal left/right inputs, and targets that are not both zero-color pairs. -/
theorem principal_conflict_shape {a b p q : T} (ha : Normal a) (hb : Normal b)
    (hc : Column p a) (hi : Image p b) (hc' : Column q a) (hi' : Image q b)
    (hne : p ≠ q) :
    (∃ u v, b = P u v) ∧ a ≠ b ∧ Normal p ∧ Normal q ∧
      ¬ (∃ u v w z, p = P u v ∧ q = P w z) := by
  classical
  have hright : ∃ u v, b = P u v := by
    by_cases hz : ∃ u v, b = P u v
    · exact hz
    · have hn : ∀ u v, b ≠ P u v := by intro u v he; exact hz ⟨u,v,he⟩
      exact False.elim (hne ((image_nonzero_target hi hn).trans (image_nonzero_target hi' hn).symm))
  have hdiff : a ≠ b := by
    intro he
    rw [he] at hc hc'
    exact hne ((normal_diagonal_target hb hc hi).trans (normal_diagonal_target hb hc' hi').symm)
  have hp := normal_guard_output ha hb (.rectangle (rectangle_target_visible hc hi) hc hi) .zero
  have hq := normal_guard_output ha hb (.rectangle (rectangle_target_visible hc' hi') hc' hi') .zero
  refine ⟨hright,hdiff,hp,hq,?_⟩
  rintro ⟨u,v,w,z,hp',hq'⟩
  rw [hp'] at hc
  rw [hq'] at hc'
  rw [hp',hq'] at hne
  exact hne (column_phase_zero_unique hc hc')

theorem source_from_zero_principal_conditions (hu : ZeroRightPrincipalUnique)
    (hr : ZeroRightRectangleCovered) : ∀ x y z : NormalTree,
      x = multiplication (multiplication y (multiplication x x))
        (multiplication (multiplication x z) z) :=
  source_from_principal_conditions (principal_unique_iff_zero_right.mpr hu)
    (rectangle_coverage_iff_zero_right.mpr hr)

end submission.Equation22446Lineage

/- Checked source module: LineageSyntax.RotatedAncestry -/
set_option autoImplicit false
set_option Elab.async false

namespace submission.Equation22446Lineage
open submission.Equation22446Guarded

theorem lineage_inverse_image_prev_false {p r : T} (hl : Lineage p r)
    (hi : Image (S (S r)) (S (S p))) : False := by
  cases hl with
  | refl => exact image_no_self hi
  | @step p a b hl hj =>
      simp only [cube] at hi
      rcases phase_two_or_square_nonzero p with ⟨u,v,hp⟩ | hn
      · have he := image_nonzero_output hi (by intro x y h; rw [hp] at h; cases h)
        rw [hp] at he
        cases he
      · have ha : ∀ x y, p ≠ S (S (P x y)) := by
          intro x y hp
          apply hn x y
          rw [hp,cube]
        have hs := image_ancestor_bound hi p a b rfl ha hl
        rw [nodes_S,nodes_S] at hs
        exact Nat.lt_irrefl _ hs

theorem column_square_image_false {p a : T} (hc : Column p a)
    (hi : Image a (S (S p))) : False := by
  cases hc with
  | ancestry hl => exact lineage_inverse_image_prev_false hl hi
  | literal p y =>
      have hs := image_right_child hi .zero y (S p) (by intro h; cases h) rfl
      simp only [nodes_S] at hs
      exact Nat.lt_irrefl _ hs
  | inverseImage hj => exact image_no_successive_outputs hj hi

theorem column_self_image_false {p a : T} (hc : Column p a)
    (hi : Image a p) : False := by
  cases hc with
  | ancestry hl => exact lineage_inverse_image_false hl hi
  | literal p y =>
      have hs := image_right_child hi .zero y (S p) (by intro h; cases h) rfl
      rw [nodes_S] at hs
      exact Nat.lt_irrefl _ hs
  | inverseImage hj => exact image_no_successive_outputs hi hj

theorem shared_column_phase_zero_bound {u v q a : T}
    (hp : Column (P u v) a) (hq : Column q a) : nodes (P u v) ≤ nodes q := by
  cases hp with
  | ancestry hl =>
      cases hl with
      | refl => simpa only [nodes_S] using (column_phase_two_bound hq u v rfl)
      | @step p x y hl hi =>
          simp only [cube] at hq
          exact column_ancestor_bound hq (P u v) x y rfl (by intro w z h; cases h) hl
  | literal p y =>
      have hs := column_right_child hq .zero y (S (P u v)) (by intro h; cases h) rfl
      simpa only [nodes_S] using hs
  | inverseImage hi =>
      have ha := congrArg S (image_nonzero_output hi (by intro x y h; cases h))
      rw [cube] at ha
      rw [←ha] at hq
      simpa only [nodes_S] using (column_phase_two_bound hq u v rfl)

end submission.Equation22446Lineage

/- Checked source module: LineageSyntax.AncestralColumns -/
set_option autoImplicit false
set_option Elab.async false

namespace submission.Equation22446Lineage
open submission.Equation22446Guarded

theorem column_adjacent_bases_false {p a : T} (hc : Column p a)
    (hd : Column (S (S p)) a) : False := by
  cases hc with
  | ancestry hl => exact lineage_inverse_column_false hl hd
  | literal p y => exact column_pair_successor_tail_false hd
  | inverseImage hi => exact column_square_image_false hd (by simpa only [cube] using hi)

theorem lineage_shifted_image_false {p r : T} (hl : Lineage p r)
    (hi : Image (S r) (S p)) : False := by
  cases hl with
  | refl => exact image_no_self hi
  | @step p a b hl hj =>
      simp only [cube] at hi
      have hs : nodes p < nodes (P a b) :=
        Nat.lt_of_le_of_lt (lineage_nodes hl) (pair_left .zero a b)
      have hm := shrinking_inverse_lineage hi hs
      exact lineage_image_inverse_false hj (lineage_trans hm hl)

theorem lineage_shifted_endpoints_false {p r : T} (hl : Lineage p r)
    (hm : Lineage p (S (S r))) : False := by
  cases hl with
  | refl =>
      have he := lineage_nonincreasing_eq hm (by simp only [nodes_S]; exact Nat.le_refl _)
      exact SS_ne p he.symm
  | @step p a b hl hi =>
      simp only [cube] at hm
      have he := lineage_non_phase_two hm (by intro u v h; cases h)
      have hs := lineage_nodes hl
      rw [he,nodes_S] at hs
      exact Nat.not_lt_of_ge hs (pair_left .zero a b)

theorem lineage_successor_column_false {p r : T} (hl : Lineage p r)
    (hc : Column p (S r)) : False := by
  generalize ha : S r = a at hc
  cases hc with
  | ancestry hm =>
      have he := congrArg (fun t => S (S t)) ha
      simp only [cube] at he
      have he' := congrArg (fun t => S (S t)) he
      simp only [cube] at he'
      rw [←he'] at hm
      exact lineage_shifted_endpoints_false hl hm
  | literal p y =>
      have he := congrArg (fun t => S (S t)) ha
      simp only [cube] at he
      cases hl with
      | refl =>
          have hs := congrArg nodes he
          simp only [nodes_S] at hs
          have hb := pair_right .zero y (S p)
          change nodes (S p) < nodes (P y (S p)) at hb
          simp only [nodes_S] at hb
          omega
      | @step p u v hm hi =>
          have hv := (T.p.inj (S_injective (S_injective he))).2.2
          rw [hv] at hi
          exact lineage_image_inverse_false hi (by simpa only [cube] using hm)
  | inverseImage hi =>
      rw [←ha] at hi
      exact lineage_shifted_image_false hl hi

end submission.Equation22446Lineage

/- Checked source module: LineageSyntax.ColumnTriangleFrontier -/
set_option autoImplicit false
set_option Elab.async false

namespace submission.Equation22446Lineage
open submission.Equation22446Guarded

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

end submission.Equation22446Lineage

/- Checked source module: LineageSyntax.LineageForward -/
set_option autoImplicit false
set_option Elab.async false

namespace submission.Equation22446Lineage
open submission.Equation22446Guarded

mutual
theorem image_lineage_next_false {p q : T} (h : Image p q) :
    ∀ r, q = S r → Lineage p r → False :=
  match h with
  | .square p => by
      intro r he hl
      rw [←S_injective he] at hl
      have hp := lineage_nonincreasing_eq hl (by rw [nodes_S]; exact Nat.le_refl _)
      exact S_ne p hp.symm
  | .literal p z => by
      intro r he hl
      cases hl with
      | refl => exact image_no_successor (he ▸ Image.literal p z)
      | @step p a b hl hi =>
          simp only [cube] at he
          rw [←(T.p.inj he).2.1] at hl
          have hp := lineage_non_phase_two hl (by intro u v h; cases h)
          exact Nat.ne_of_lt (pair_left .zero p z) (congrArg nodes hp)
  | .transport hc hi => by
      intro r he hl
      cases hl with
      | refl => exact image_no_successor (he ▸ Image.transport hc hi)
      | @step p a b hl hj =>
          simp only [cube] at he
          rw [←(T.p.inj he).2.1] at hl
          exact column_lineage_reverse_false hc hl
  | .inverseFollowup p => by
      intro r he hl
      cases hl with
      | refl => exact image_no_successor (he ▸ Image.inverseFollowup p)
      | @step u a b hl hi =>
          simp only [cube] at he
          rw [←(T.p.inj he).2.1] at hl
          have hs := lineage_nodes hl
          simp only [nodes_S] at hs
          exact Nat.not_lt_of_ge hs (pair_left .zero p (S p))
  | .returnFollowup hi => by
      intro r he hl
      cases hl with
      | refl => exact image_no_successor (he ▸ Image.returnFollowup hi)
      | @step p a b hl hj =>
          simp only [cube] at he
          rw [←(T.p.inj he).2.1] at hl
          have hp := lineage_non_phase_two hl (by intro u v h; cases h)
          cases hp
  | .cycleFollowup hs hi hj => by
      intro r he hl
      cases hl with
      | refl => exact image_no_successor (he ▸ Image.cycleFollowup hs hi hj)
      | @step p a b hl hk =>
          simp only [cube] at he
          rw [←(T.p.inj he).2.1] at hl
          have hp := lineage_non_phase_two hl (by intro u v h; cases h)
          cases hp
theorem column_lineage_reverse_false {p a : T} (h : Column p a)
    (hl : Lineage a p) : False :=
  match h with
  | .ancestry hm => by
      have hs := lineage_nodes hl
      simp only [nodes_S] at hs
      have hp := lineage_nonincreasing_eq hm hs
      rw [←hp] at hl
      have he := lineage_nonincreasing_eq hl (by simp only [nodes_S]; exact Nat.le_refl _)
      exact SS_ne p he
  | .literal p y => by
      have hs := lineage_nodes hl
      have hb := pair_right .zero y (S p)
      change nodes (S p) < nodes (P y (S p)) at hb
      rw [nodes_S] at hb
      exact Nat.not_lt_of_ge hs hb
  | .inverseImage hi => image_lineage_next_false hi _ rfl hl
end

end submission.Equation22446Lineage

/- Checked source module: LineageSyntax.CommonLineage -/
set_option autoImplicit false
set_option Elab.async false

namespace submission.Equation22446Lineage
open submission.Equation22446Guarded

theorem lineage_common_comparable {p q r : T} (hp : Lineage p r) (hq : Lineage q r) :
    Lineage p q ∨ Lineage q p :=
  match hp with
  | .refl p => Or.inr hq
  | .step hp hi => by
      cases hq with
      | refl => exact Or.inl (.step hp hi)
      | step hq hj => exact lineage_common_comparable hp hq

theorem column_lineage_forward_false {p a : T} (hc : Column p a)
    (hl : Lineage p a) : False := by
  cases hl with
  | refl => exact column_no_self hc
  | @step p u v hl hi =>
      have hs := column_phase_two_bound hc u v rfl
      have hb := lineage_nodes hl
      have ht := pair_left .two u v
      exact Nat.not_lt_of_ge hs (Nat.lt_of_le_of_lt hb ht)

theorem common_lineage_column_false {p q r : T} (hp : Lineage p r) (hq : Lineage q r)
    (hc : Column p q) : False := by
  rcases lineage_common_comparable hp hq with hl | hl
  · exact column_lineage_forward_false hc hl
  · exact column_lineage_reverse_false hc hl

theorem column_triangle_base_phase_two {u p a : T}
    (hup : Column u p) (hpa : Column p a) (hua : Column u a) :
    ∃ x y, u = S (S (P x y)) := by
  rcases phase_two_or_square_nonzero u with hu | hn
  · exact hu
  · have hi := column_triangle_inverse_origin hup hpa hua
    have hp := image_nonzero_target hi hn
    rw [hp] at hpa
    exact False.elim (column_adjacent_bases_false hua hpa)

end submission.Equation22446Lineage

/- Checked source module: LineageSyntax.CommonRootExclusion -/
set_option autoImplicit false
set_option Elab.async false

namespace submission.Equation22446Lineage
open submission.Equation22446Guarded

theorem lineage_phase_two_preserved {r p : T} (hl : Lineage r p)
    (hr : ∃ u v, r = S (S (P u v))) : ∃ u v, p = S (S (P u v)) := by
  cases hl with
  | refl => exact hr
  | step hl hi => exact ⟨_,_,rfl⟩

theorem column_large_ancestor_false {u v p : T}
    (hc : Column u p) (hl : Lineage (S (S (P u v))) p) : False := by
  obtain ⟨a,b,hp⟩ := lineage_phase_two_preserved hl ⟨u,v,rfl⟩
  have hs := column_phase_two_bound hc a b hp
  have ht := lineage_nodes hl
  simp only [nodes_S] at ht
  have hb := pair_left .zero u v
  exact Nat.not_lt_of_ge (Nat.le_trans ht hs) hb

mutual
theorem image_common_root_next_false {p q : T} (h : Image p q) :
    ∀ r t, q = S t → Lineage r p → Lineage r t → False :=
  match h with
  | .square p => by
      intro r t he hp ht
      have htp := (S_injective he).symm
      rw [htp] at ht
      exact lineage_shifted_endpoints_false ht (by simpa only [cube] using hp)
  | .literal p z => by
      intro r t he hp ht
      cases ht with
      | refl =>
          have htp := congrArg (fun w => S (S w)) he
          simp only [cube] at htp
          have hs := lineage_nodes hp
          rw [←htp,nodes_S,nodes_S] at hs
          exact Nat.not_lt_of_ge hs (Nat.lt_trans (pair_left .zero p z) (pair_left .zero _ z))
      | @step r a b ht hi =>
          simp only [cube] at he
          rw [←(T.p.inj he).2.1] at ht
          have hr := lineage_non_phase_two ht (by intro u v h; cases h)
          rw [hr] at hp
          exact Nat.not_lt_of_ge (lineage_nodes hp) (pair_left .zero p z)
  | .transport hc hi => by
      intro r t he hp ht
      cases ht with
      | refl =>
          have htp := congrArg (fun w => S (S w)) he
          simp only [cube] at htp
          rw [←htp] at hp
          exact column_large_ancestor_false hc hp
      | @step r a b ht hj =>
          simp only [cube] at he
          rw [←(T.p.inj he).2.1] at ht
          exact column_common_root_false hc r ht hp
  | .inverseFollowup p => by
      intro r t he hp ht
      have hr := lineage_non_phase_two hp (by intro u v h; cases h)
      rw [hr] at ht
      cases ht with
      | refl => cases he
      | @step r a b ht hi =>
          simp only [cube] at he
          rw [←(T.p.inj he).2.1] at ht
          have hs := lineage_nodes ht
          simp only [nodes_S] at hs
          exact Nat.not_lt_of_ge hs (pair_left .zero p (S p))
  | .returnFollowup hi => by
      intro r t he hp ht
      have hr := lineage_non_phase_two hp (by intro u v h; cases h)
      rw [hr] at ht
      cases ht with
      | refl => cases he
      | @step r a b ht hj =>
          simp only [cube] at he
          rw [←(T.p.inj he).2.1] at ht
          have hr' := lineage_non_phase_two ht (by intro u v h; cases h)
          cases hr'
  | .cycleFollowup hs hi hj => by
      intro r t he hp ht
      have hr := lineage_non_phase_two hp (by intro u v h; cases h)
      rw [hr] at ht
      cases ht with
      | refl => cases he
      | @step r a b ht hk =>
          simp only [cube] at he
          rw [←(T.p.inj he).2.1] at ht
          have hr' := lineage_non_phase_two ht (by intro u v h; cases h)
          cases hr'
theorem column_common_root_false {p a : T} (h : Column p a) :
    ∀ r, Lineage r p → Lineage r a → False :=
  match h with
  | .ancestry hl => by
      intro r hp ha
      exact lineage_shifted_endpoints_false (lineage_trans hp hl) ha
  | .literal p y => by
      intro r hp ha
      have hr := lineage_non_phase_two ha (by intro u v h; cases h)
      rw [hr] at hp
      have hb := pair_right .zero y (S p)
      change nodes (S p) < nodes (P y (S p)) at hb
      rw [nodes_S] at hb
      exact Nat.not_lt_of_ge (lineage_nodes hp) hb
  | .inverseImage hi => by
      intro r hp ha
      exact image_common_root_next_false hi r _ rfl ha hp
end

end submission.Equation22446Lineage

/- Checked source module: LineageSyntax.PhaseOneLineageRoots -/
set_option autoImplicit false
set_option Elab.async false

namespace submission.Equation22446Lineage
open submission.Equation22446Guarded

mutual
theorem image_small_phase_one_common_root {p q : T} (h : Image p q) :
    ∀ u v, p = S (P u v) → nodes q < nodes p →
      ∃ r, Lineage r u ∧ Lineage r (S (S q)) :=
  match h with
  | .square p => by
      intro u v hp hs
      simp only [nodes_S] at hs
      exact False.elim (Nat.lt_irrefl _ hs)
  | .literal p z => by
      intro u v hp hs
      exact False.elim (Nat.not_lt_of_ge (Nat.le_of_lt
        (Nat.lt_trans (pair_left .zero _ _) (pair_left .zero _ _))) hs)
  | .transport hc hi => by
      intro u v hp hs
      obtain ⟨r,hr,hl⟩ := column_small_phase_one_common_root hc u v hp
        (Nat.lt_trans (pair_left .zero _ _) hs)
      exact ⟨r,hr,.step hl hi⟩
  | .inverseFollowup p => by intro u v hp hs; cases hp
  | .returnFollowup hi => by intro u v hp hs; cases hp
  | .cycleFollowup hs hi hj => by intro u v hp ht; cases hp
theorem column_small_phase_one_common_root {p a : T} (h : Column p a) :
    ∀ u v, a = S (P u v) → nodes p < nodes a →
      ∃ r, Lineage r u ∧ Lineage r p :=
  match h with
  | .ancestry hl => by
      intro u v ha hs
      cases hl with
      | refl =>
          simp only [nodes_S] at hs
          exact False.elim (Nat.lt_irrefl _ hs)
      | @step p x y hl hi =>
          simp only [cube] at ha
          have he := S_injective ha
          rw [(T.p.inj he).2.1] at hl
          exact ⟨p,hl,.refl p⟩
  | .literal p y => by intro u v ha hs; cases ha
  | .inverseImage hi => by
      intro u v ha hs
      obtain ⟨r,hr,hp⟩ := image_small_phase_one_common_root hi u v ha (by simpa only [nodes_S] using hs)
      exact ⟨r,hr,by simpa only [cube] using hp⟩
end

end submission.Equation22446Lineage

/- Checked source module: LineageSyntax.ColumnChains -/
set_option autoImplicit false
set_option Elab.async false

namespace submission.Equation22446Lineage
open submission.Equation22446Guarded

theorem column_chain_completed_false {u p v : T} (hc : Column u p)
    (hd : Column p (S (P u v))) : False := by
  generalize he : S (P u v) = a at hd
  cases hd with
  | ancestry hl =>
      cases hl with
      | refl =>
          have hp := congrArg S he
          rw [cube] at hp
          rw [←hp] at hc
          exact column_large_ancestor_false hc (.refl _)
      | @step p x y hl hi =>
          simp only [cube] at he
          rw [←(T.p.inj (S_injective he)).2.1] at hl
          exact column_lineage_reverse_false hc hl
  | literal p y => cases he
  | inverseImage hi =>
      rw [←he] at hi
      rcases phase_two_or_square_nonzero p with ⟨x,y,hp⟩ | hn
      · have hb := column_phase_two_bound hc x y hp
        have hs : nodes (S p) < nodes (S (P u v)) := by
          simp only [nodes_S]
          exact Nat.lt_of_le_of_lt hb (pair_left .zero u v)
        obtain ⟨r,hr,ht⟩ := image_small_phase_one_common_root hi u v rfl hs
        simp only [cube] at ht
        exact column_common_root_false hc r hr ht
      · have ha := image_nonzero_target hi hn
        have hp := congrArg S ha
        rw [cube] at hp
        rw [←hp] at hc
        exact column_large_ancestor_false hc (.refl _)

theorem phase_one_or_double_nonzero (a : T) :
    (∃ u v, a = S (P u v)) ∨ (∀ u v, S (S a) ≠ P u v) := by
  cases a with
  | e c n => right; intro u v h; cases c <;> cases h
  | p c u v =>
      cases c with
      | zero => right; intro x y h; cases h
      | one => exact Or.inl ⟨u,v,rfl⟩
      | two => right; intro x y h; cases h

theorem column_image_prev_false {p a : T} (hc : Column p a)
    (hi : Image p (S (S a))) : False := by
  cases hc with
  | ancestry hl =>
      simp only [cube] at hi
      exact image_lineage_next_false hi _ rfl hl
  | literal p y =>
      have he := S_injective (S_injective (image_nonzero_output hi (by intro u v h; cases h)))
      have hb := pair_right .zero y (S p)
      change nodes (S p) < nodes (P y (S p)) at hb
      rw [nodes_S] at hb
      exact Nat.ne_of_lt hb (congrArg nodes he).symm
  | inverseImage hj =>
      rcases phase_two_or_square_nonzero p with ⟨x,y,hp⟩ | hn
      · rcases phase_one_or_double_nonzero a with ⟨u,v,ha⟩ | hn
        · have hs := image_phase_two_output_left hi x y u v hp (by rw [ha]; rfl)
          have ht : nodes (S p) < nodes a := by
            rw [ha,nodes_S,nodes_S]
            exact Nat.lt_of_le_of_lt hs (pair_left .zero u v)
          obtain ⟨r,hr,hp'⟩ := image_small_phase_one_common_root hj u v ha ht
          simp only [cube] at hp'
          have huv := image_small_phase_one_origin hj u v ha ht
          exact image_common_root_next_false hi r (S (S (P u v)))
            (by rw [ha]) hp' (.step hr huv)
        · have he := S_injective (S_injective (image_nonzero_output hi hn))
          rw [he] at hj
          exact image_no_successor hj
      · have he := image_nonzero_target hj hn
        rw [he,cube] at hi
        exact image_no_successor hi

theorem column_inverse_pair_chain_false {p w : T} (hc : Column (S (S w)) p)
    (hd : Column p (P w (S w))) : False := by
  generalize he : P w (S w) = a at hd
  have completed_bad (hp : p = S (P w (S w))) : False := by
    rw [hp] at hc
    exact column_chain_completed_false (column_canonical w) hc
  cases hd with
  | ancestry hl =>
      have ha := congrArg S he
      rw [cube] at ha
      have hp := lineage_non_phase_two hl (by intro u v h; rw [←ha] at h; cases h)
      exact completed_bad (hp.trans ha.symm)
  | literal p y =>
      have hp := S_injective (T.p.inj he).2.2
      rw [←hp] at hc
      exact lineage_successor_column_false (p := S (S w)) (.refl _) (by simpa only [cube] using hc)
  | inverseImage hi =>
      rw [←he] at hi
      have hb := image_right_child hi .zero w (S w) (by intro h; cases h) rfl
      simp only [nodes_S] at hb
      rcases phase_two_or_square_nonzero p with ⟨a,b,hp⟩ | hn
      · have hs := column_phase_two_bound hc a b hp
        simp only [nodes_S] at hs
        exact Nat.not_lt_of_ge hs hb
      · exact completed_bad (S_injective (image_nonzero_output hi hn))

end submission.Equation22446Lineage

/- Checked source module: LineageSyntax.AncestralChainClosure -/
set_option autoImplicit false
set_option Elab.async false

namespace submission.Equation22446Lineage
open submission.Equation22446Guarded

theorem image_phase_one_nongrowing {p q : T} (h : Image p q) :
    ∀ u v, p = S (P u v) → nodes q ≤ nodes p →
      q = S (S p) ∨ (Image u v ∧ ∃ r, Lineage r u ∧ Lineage r (S (S q))) := by
  intro u v hp hs
  cases h with
  | square p => exact Or.inl rfl
  | literal p z =>
      exact False.elim (Nat.not_lt_of_ge hs
        (Nat.lt_trans (pair_left .zero _ _) (pair_left .zero _ _)))
  | transport hc hi =>
      have ht := Nat.lt_of_lt_of_le (pair_left .zero _ _) hs
      have huv := column_small_phase_one_origin hc u v hp ht
      obtain ⟨r,hr,hl⟩ := column_small_phase_one_common_root hc u v hp ht
      exact Or.inr ⟨huv,r,hr,.step hl hi⟩
  | inverseFollowup p => cases hp
  | returnFollowup hi => cases hp
  | cycleFollowup ht hi hj => cases hp

theorem column_joined_lineages_false {u p q r : T} (hc : Column u p)
    (hu : Lineage u q) (hr : Lineage r q) (hp : Lineage r p) : False := by
  rcases lineage_common_comparable hu hr with h | h
  · exact column_lineage_forward_false hc (lineage_trans h hp)
  · exact column_common_root_false hc r h hp

/-- CT with an ancestral LAST edge is also excluded, including inverse
middle edges and arbitrary ancestry depth. -/
theorem column_chain_ancestral_false {u p q : T} (hl : Lineage u q)
    (hc : Column u p) (hd : Column p (S (S q))) : False := by
  have hu := column_triangle_base_phase_two hc hd (.ancestry hl)
  have hq := lineage_phase_two_preserved hl hu
  generalize he : S (S q) = a at hd
  cases hd with
  | ancestry hm =>
      have hqr := S_injective (S_injective he)
      rw [←hqr] at hm
      exact common_lineage_column_false hl hm hc
  | literal p y =>
      have hq' := congrArg S he
      rw [cube] at hq'
      obtain ⟨x,z,hq⟩ := hq
      rw [hq] at hq'
      cases hq'
  | inverseImage hi =>
      rw [←he] at hi
      rcases phase_two_or_square_nonzero p with ⟨x,y,hp⟩ | hn
      · obtain ⟨v,w,hq⟩ := hq
        have hs := column_phase_two_bound hc x y hp
        have ht := lineage_nodes hl
        have hb : nodes (S p) ≤ nodes (S (S q)) := by
          simp only [nodes_S]
          exact Nat.le_trans hs ht
        have hn := image_phase_one_nongrowing hi v w (by rw [hq]; rfl) hb
        rcases hn with heq | ⟨hvw,r,hr,hp'⟩
        · have hpq := S_injective (by simpa only [cube] using heq)
          rw [hpq] at hc
          exact column_lineage_forward_false hc hl
        · have hrq : Lineage r q := by rw [hq]; exact .step hr hvw
          simp only [cube] at hp'
          exact column_joined_lineages_false hc hl hrq hp'
      · have hpq : p = q := S_injective (by simpa only [cube] using (image_nonzero_output hi hn))
        rw [hpq] at hc
        exact column_lineage_forward_false hc hl

end submission.Equation22446Lineage

/- Checked source module: LineageSyntax.TriangleColumnExtras -/
set_option autoImplicit false
set_option Elab.async false

namespace submission.Equation22446Lineage
open submission.Equation22446Guarded

theorem column_non_two_base_bound {p a : T} (hc : Column p a)
    (hn : ∀ x y, S p ≠ P x y) : nodes p ≤ nodes a := by
  cases hc with
  | ancestry hl => simpa only [nodes_S] using (lineage_nodes hl)
  | literal p y =>
      have hs := pair_right .zero y (S p)
      rw [nodes_S] at hs
      exact Nat.le_of_lt hs
  | inverseImage hi =>
      rw [image_nonzero_target hi hn,nodes_S,nodes_S]
      exact Nat.le_refl _

theorem column_phase_one_base_non_two {u v p : T} (hc : Column (S (P u v)) p) :
    ∀ x y, S p ≠ P x y := by
  intro x y hp
  have hp' : p = S (S (P x y)) := by
    have hh := congrArg (fun t => S (S t)) hp
    simpa only [cube] using hh
  rcases column_phase_two_base_shape hc ⟨x,y,hp'⟩ with ⟨a,b,hu⟩ | ⟨a,b,hu⟩
  · cases hu
  · cases hu

theorem column_tall_head_chain_false {u v z p : T}
    (hz : nodes z < nodes (P u v)) (hc : Column (S (P u v)) p)
    (hd : Column p (P (S (S (P u v))) z)) : False := by
  have canonical_bad (hp : p = S (P (S (S (P u v))) z)) : False := by
    have hs : nodes (S (P u v)) < nodes p := by
      rw [hp,nodes_S,nodes_S]
      have hb := pair_left .zero (S (S (P u v))) z
      change nodes (S (S (P u v))) < nodes (P (S (S (P u v))) z) at hb
      simpa only [nodes_S] using hb
    have hi := column_small_phase_one_origin hc (S (S (P u v))) z hp hs
    have hb := image_phase_two_bound hi u v rfl
    simp only [nodes_S] at hb
    exact Nat.not_lt_of_ge hb hz
  generalize he : P (S (S (P u v))) z = a at hd
  cases hd with
  | ancestry hl =>
      have ha := congrArg S he
      rw [cube] at ha
      have hp := lineage_non_phase_two hl (by intro x y h; rw [←ha] at h; cases h)
      exact canonical_bad (hp.trans ha.symm)
  | literal p y =>
      have hb := column_non_two_base_bound hc (by intro x y h; cases h)
      have hz' := congrArg nodes (T.p.inj he).2.2
      simp only [nodes_S] at hz' hb
      rw [←hz'] at hb
      exact Nat.not_lt_of_ge hb hz
  | inverseImage hi =>
      rw [←he] at hi
      exact canonical_bad (S_injective (image_nonzero_output hi (column_phase_one_base_non_two hc)))

end submission.Equation22446Lineage

/- Checked source module: LineageSyntax.TriangleImageRoots -/
set_option autoImplicit false
set_option Elab.async false

namespace submission.Equation22446Lineage
open submission.Equation22446Guarded

theorem cycle_followup_input_eq {u v w t z : T}
    (hs : nodes (S (S (P w t))) < nodes (P (P u v) z))
    (hi : Image (S (S (P w t))) (P (P u v) z))
    (hj : Image (P (P u v) z) (P w t)) : P u v = P (S (S (P w t))) z :=
  cycle_target_literal hi (by simpa only [cube] using hj) hs

theorem image_literal_triangle_false {p z a q : T} (hc : Column p a)
    (hi : Image a q) (he : q = P (P p z) z) : False := by
  cases hi with
  | square a =>
      have ha := congrArg S he
      rw [cube] at ha
      have hs := column_ancestor_bound hc (P p z) (P p z) z ha
        (by intro u v h; cases h) (.refl _)
      exact Nat.not_lt_of_ge hs (pair_left .zero p z)
  | literal a t =>
      have ha := (T.p.inj (T.p.inj he).2.1).2.1
      rw [ha] at hc
      exact column_no_self hc
  | transport hd hj =>
      rw [(T.p.inj he).2.1,(T.p.inj he).2.2] at hj
      exact image_pair_tail_false hj
  | inverseFollowup v =>
      have hb := pair_right .zero p z
      change nodes z < nodes (P p z) at hb
      rw [←(T.p.inj he).2.1,←(T.p.inj he).2.2] at hb
      simp only [nodes_S] at hb
      exact Nat.lt_irrefl _ hb
  | returnFollowup hj => cases (T.p.inj he).2.1
  | cycleFollowup hs hj hk => cases (T.p.inj he).2.1

theorem image_inverse_triangle_false {v a q : T} (hc : Column (P v (S v)) a)
    (hi : Image a q) (he : q = P (S (S v)) (S v)) : False := by
  cases hi with
  | square a =>
      have ha := congrArg S he
      rw [cube] at ha
      rw [ha] at hc
      have hs := lineage_nodes (column_zero_phase_one_origin hc).1
      simp only [nodes_S] at hs
      exact Nat.not_lt_of_ge hs (pair_left .zero v (S v))
  | literal a t =>
      have hb := pair_right .zero a t
      change nodes t < nodes (P a t) at hb
      rw [(T.p.inj he).2.1,(T.p.inj he).2.2] at hb
      simp only [nodes_S] at hb
      exact Nat.lt_irrefl _ hb
  | transport hd hj =>
      rw [(T.p.inj he).2.1] at hd
      have hs := shared_column_phase_zero_bound hc hd
      simp only [nodes_S] at hs
      exact Nat.not_lt_of_ge hs (pair_left .zero v (S v))
  | inverseFollowup w =>
      have hw := S_injective (T.p.inj he).2.2
      rw [hw] at hc
      exact column_no_self hc
  | @returnFollowup w t hj =>
      have hw := S_injective (T.p.inj he).2.2
      have hl := (T.p.inj he).2.1
      rw [hw] at hl
      have hn := congrArg nodes hl
      simp only [nodes_S] at hn
      exact Nat.ne_of_lt (pair_left .zero v t) hn.symm
  | @cycleFollowup u z w t b hs hj hk =>
      have ha := cycle_followup_input_eq hs hj hk
      have hr := congrArg S (T.p.inj he).2.1
      simp only [cube] at hr
      rw [ha,hr,(T.p.inj he).2.2] at hc
      exact column_no_self hc

/-- Handles both the returned-image and strict-cycle followup shapes. -/
theorem image_rotated_pair_triangle_false {u v z a q : T}
    (hc : Column (P (S (S (P u v))) z) a)
    (hi : Image a q) (he : q = P (S (P u v)) z) : False := by
  cases hi with
  | square a =>
      have ha := congrArg S he
      rw [cube] at ha
      rw [ha] at hc
      have hl := (column_zero_phase_one_origin hc).1
      have hp := lineage_non_phase_two hl (by intro x y h; cases h)
      cases hp
  | literal a t => cases (T.p.inj he).2.1
  | transport hd hj =>
      rw [(T.p.inj he).2.1] at hd
      have hs := shared_column_phase_zero_bound hc hd
      simp only [nodes_S] at hs
      have hb := pair_left .zero (S (S (P u v))) z
      simp only [nodes_S] at hb
      exact Nat.not_lt_of_ge hs hb
  | inverseFollowup w =>
      have hw := congrArg S (T.p.inj he).2.1
      rw [cube] at hw
      have hz := (T.p.inj he).2.2
      rw [hz,hw] at hc
      exact column_no_self hc
  | @returnFollowup w t hj =>
      have hp := S_injective (T.p.inj he).2.1
      rw [hp,(T.p.inj he).2.2] at hc
      exact column_no_self hc
  | @cycleFollowup x y w t b hs hj hk =>
      have ha := cycle_followup_input_eq hs hj hk
      have hp := S_injective (T.p.inj he).2.1
      rw [ha,hp,(T.p.inj he).2.2] at hc
      exact column_no_self hc

end submission.Equation22446Lineage

/- Checked source module: LineageSyntax.TransportTriangles -/
set_option autoImplicit false
set_option Elab.async false

namespace submission.Equation22446Lineage
open submission.Equation22446Guarded

theorem image_transport_common_column {u v p a q : T}
    (hc : Column u p) (hi : Image u v) (hd : Column p a)
    (hj : Image a q) (he : q = P u v) : Column u a := by
  cases hj with
  | square a =>
      have ha := congrArg S he
      rw [cube] at ha
      rw [ha] at hd
      exact False.elim (column_chain_completed_false hc hd)
  | literal a t =>
      rw [←(T.p.inj he).2.1,←(T.p.inj he).2.2] at hi
      exact False.elim (image_pair_tail_false hi)
  | transport hk hl =>
      rw [(T.p.inj he).2.1] at hk
      exact hk
  | inverseFollowup w =>
      rw [←(T.p.inj he).2.1] at hc
      exact False.elim (column_inverse_pair_chain_false hc hd)
  | @returnFollowup w t hk =>
      rw [←(T.p.inj he).2.1] at hc
      have hs : nodes (S w) < nodes (P w t) := by rw [nodes_S]; exact pair_left .zero w t
      exact False.elim (column_tall_head_chain_false hs hc hd)
  | @cycleFollowup x y w t z hs hk hl =>
      rw [←(T.p.inj he).2.1] at hc
      have ha := cycle_followup_input_eq hs hk hl
      rw [ha] at hd
      have hz := image_right_child hl .zero (P x y) z (by intro h; cases h) rfl
      exact False.elim (column_tall_head_chain_false hz hc hd)

end submission.Equation22446Lineage

/- Checked source module: LineageSyntax.TriangleInduction -/
set_option autoImplicit false
set_option Elab.async false

namespace submission.Equation22446Lineage
open submission.Equation22446Guarded

def triangleSize (p a q : T) : Nat := nodes p + nodes a + nodes q

/-- Both triangle exclusions for the NEW six-image/three-column grammar.
The measure strictly decreases at each recursive call. -/
theorem joint_triangle_exclusion (n : Nat) :
    (∀ p a q, triangleSize p a q = n → Image p q → Column p a → Image a q → False) ∧
    (∀ u p a, triangleSize p a u = n → Column u p → Column p a → Column u a → False) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      have image_here : ∀ p a q, triangleSize p a q = n →
          Image p q → Column p a → Image a q → False := by
        intro p a q hn hi hc hj
        cases hi with
        | square p => exact column_square_image_false hc hj
        | literal p z => exact image_literal_triangle_false hc hj rfl
        | @transport u p v hk hl =>
            have hm := image_transport_common_column hk hl hc hj rfl
            have hs : triangleSize p a u < n := by
              rw [←hn]
              exact Nat.add_lt_add_left (pair_left .zero u v) (nodes p + nodes a)
            exact (ih _ hs).2 u p a rfl hk hc hm
        | inverseFollowup v => exact image_inverse_triangle_false hc hj rfl
        | returnFollowup hk => exact image_rotated_pair_triangle_false hc hj rfl
        | cycleFollowup hs hk hl =>
            rw [cycle_followup_input_eq hs hk hl] at hc
            exact image_rotated_pair_triangle_false hc hj rfl
      refine ⟨image_here,?_⟩
      intro u p a hn hc hd he
      have hi := column_triangle_inverse_origin hc hd he
      cases he with
      | ancestry hl => exact column_chain_ancestral_false hl hc hd
      | literal u y =>
          have hp := principal_pair_target hd hi
          have hor := principal_pair_inner_image hd hi
          have hcp : Column y p := by rw [hp]; exact column_completed hor
          have hy := pair_left .zero y (S u)
          have hs : triangleSize y p (S u) < triangleSize p (P y (S u)) u := by
            unfold triangleSize
            rw [nodes_S,Nat.add_comm (nodes y) (nodes p)]
            exact Nat.add_lt_add_right (Nat.add_lt_add_left hy (nodes p)) (nodes u)
          have hs' : triangleSize y p (S u) < n := by rwa [hn] at hs
          exact (ih _ hs').1 y p (S u) rfl hor hcp hi
      | inverseImage hj =>
          have hn' : triangleSize p a (S u) = n := by
            unfold triangleSize
            rw [nodes_S]
            exact hn
          exact image_here p a (S u) hn' hi hd hj

theorem image_triangle_false {p a q : T} (hi : Image p q) (hc : Column p a)
    (hj : Image a q) : False :=
  (joint_triangle_exclusion (triangleSize p a q)).1 p a q rfl hi hc hj

theorem column_triangle_false {u p a : T} (hc : Column u p) (hd : Column p a)
    (he : Column u a) : False :=
  (joint_triangle_exclusion (triangleSize p a u)).2 u p a rfl hc hd he

end submission.Equation22446Lineage

/- Checked source module: LineageSyntax.FullImageCoverage -/
set_option autoImplicit false
set_option Elab.async false

namespace submission.Equation22446Lineage
open submission.Equation22446Guarded

theorem image_next_pair_tail_false {a b : T} (h : Image (S (P a b)) b) : False := by
  have hor := image_small_phase_one_origin h a b rfl (by rw [nodes_S]; exact pair_right .zero a b)
  exact image_triangle_false hor (column_completed hor) h

theorem principal_pair_false {r a b : T} (hc : Column r (P a b)) (hi : Image r b) : False := by
  rw [principal_pair_target hc hi] at hi
  exact image_next_pair_tail_false hi

theorem image_pair_no_guard {p z : T} (hi : Image p z) : ¬ ∃ o, Guard p z o := by
  rintro ⟨o,hg⟩
  cases hg with
  | rectangle hv hc hj => exact image_triangle_false hj hc hi
  | inverseDouble v => exact image_pair_tail_false hi
  | imageReturn hj => exact image_pair_tail_false hi
  | cycleReturn hv hj hk =>
      rw [cycle_target_literal hj hk (visible_target_smaller hv)] at hi
      exact image_pair_tail_false hi

/-- A second rectangle is impossible for every first Product, without
Normal assumptions or any premise on the second rectangle's visibility. -/
theorem rectangle_double_false {p z u b : T} (hm : Product p z u)
    (hc : Column b u) (hi : Image b z) : False := by
  cases hm with
  | raw hn => exact principal_pair_false hc hi
  | hit hg =>
      cases hg with
      | rectangle hv hk hj => exact image_triangle_false hi hc hj
      | inverseDouble v =>
          have hj : Image (S (S v)) (S v) := by simpa only [cube] using (Image.square (S (S v)))
          exact image_triangle_false hi hc hj
      | imageReturn hj =>
          exact column_triangle_false (.inverseImage hi) hc (column_completed hj)
      | cycleReturn hv hj hk =>
          have hl := shrinking_inverse_lineage hk (visible_target_smaller hv)
          have hb : Column (S (S z)) b := .inverseImage (by simpa only [cube] using hi)
          exact column_triangle_false hb hc (.ancestry hl)

theorem rectangle_return_covered : RectangleReturnCovered := by
  intro p z u b hp hz hm hv hc hi
  exact False.elim (rectangle_double_false hm hc hi)

theorem returned_image_covered : ReturnedImageCovered :=
  returned_coverage_of_rectangle rectangle_return_covered

theorem product_double_image {p z u b : T} (h1 : Product p z u) (h2 : Product u z b) :
    Image p b := by
  cases h2 with
  | raw hn => exact product_raw_followup h1
  | hit hg =>
      cases hg with
      | rectangle hv hc hi => exact False.elim (rectangle_double_false h1 hc hi)
      | inverseDouble v => exact second_inverse_covered h1
      | imageReturn hi => exact second_return_covered h1
      | cycleReturn hv hi hj => exact second_cycle_covered h1 hv hi hj

theorem chosen_double_image_unconditional (p z : T) : Image p (chosen (chosen p z) z) :=
  product_double_image (chosen_product p z) (chosen_product (chosen p z) z)

theorem source_with_principal_unique (hu : PrincipalUnique) : ∀ x y z : NormalTree,
    x = multiplication (multiplication y (multiplication x x))
      (multiplication (multiplication x z) z) :=
  source_from_principal_conditions hu rectangle_return_covered

/-- Explicitly conditional on the still-open NEW principal uniqueness. -/
theorem infinite_model_with_principal_unique (hu : PrincipalUnique) :
    (∀ x y z : NormalTree,
      x = multiplication (multiplication y (multiplication x x))
        (multiplication (multiplication x z) z)) ∧
    (∀ {a b : Nat}, normalTower a = normalTower b → a = b) :=
  ⟨source_with_principal_unique hu,normalTower_injective⟩

theorem source_with_zero_right_principal_unique (hu : ZeroRightPrincipalUnique) :
    ∀ x y z : NormalTree,
      x = multiplication (multiplication y (multiplication x x))
        (multiplication (multiplication x z) z) :=
  source_with_principal_unique (principal_unique_iff_zero_right.mpr hu)

end submission.Equation22446Lineage

/- Checked source module: LineageSyntax.PhaseTwoUniqueness -/
set_option autoImplicit false
set_option Elab.async false

namespace submission.Equation22446Lineage
open submission.Equation22446Guarded

theorem column_two_to_two_inverse {p q : T} (hc : Column p q)
    (hp : ∃ a b, p = S (S (P a b))) (hq : ∃ a b, q = S (S (P a b))) : Image q (S p) := by
  cases hc with
  | ancestry hl =>
      obtain ⟨a,b,hq⟩ := hq
      have he := S_injective (S_injective hq)
      have hp' := lineage_non_phase_two hl (by intro u v h; rw [he] at h; cases h)
      obtain ⟨u,v,hp⟩ := hp
      rw [hp,he] at hp'
      cases hp'
  | literal p y => obtain ⟨a,b,hq⟩ := hq; cases hq
  | inverseImage hi => exact hi

theorem image_phase_two_roots_unique_at_size (n : Nat) :
    ∀ p q b, nodes b = n →
      (∃ u v, p = S (S (P u v))) → (∃ u v, q = S (S (P u v))) →
      Image p b → Image q b → p = q := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      intro p q b hn hp hq hi hj
      obtain ⟨x,y,hp⟩ := hp
      obtain ⟨w,t,hq⟩ := hq
      cases hi with
      | square p =>
          have he := image_nonzero_target hj (by intro u v h; rw [hp] at h; cases h)
          simpa only [cube] using he.symm
      | literal p z =>
          generalize he : P (P p z) z = b at hj
          cases hj with
          | square q => rw [hq] at he; cases he
          | literal q t => exact (T.p.inj (T.p.inj he).2.1).2.1
          | transport hc hk =>
              rw [←(T.p.inj he).2.1,←(T.p.inj he).2.2] at hk
              exact False.elim (image_pair_tail_false hk)
          | inverseFollowup q => cases hq
          | returnFollowup hk => cases hq
          | cycleFollowup hs hk hl => cases hq
      | @transport u p v hc hk =>
          generalize he : P u v = b at hj
          cases hj with
          | square q => rw [hq] at he; cases he
          | literal q z =>
              rw [(T.p.inj he).2.1,(T.p.inj he).2.2] at hk
              exact False.elim (image_pair_tail_false hk)
          | transport hd hl =>
              rw [←(T.p.inj he).2.1] at hd
              rcases column_phase_two_base_shape hc ⟨x,y,hp⟩ with ⟨a,b,hu⟩ | ⟨a,b,hu⟩
              · rw [hu,hp] at hc
                rw [hu,hq] at hd
                have hs := (column_zero_to_two hc).symm.trans (column_zero_to_two hd)
                rw [hp,hq,hs]
              · have hi' := column_two_to_two_inverse hc ⟨a,b,hu⟩ ⟨x,y,hp⟩
                have hj' := column_two_to_two_inverse hd ⟨a,b,hu⟩ ⟨w,t,hq⟩
                have hs : nodes (S u) < n := by
                  rw [nodes_S,←hn]
                  exact pair_left .zero u v
                exact ih _ hs p q (S u) rfl ⟨x,y,hp⟩ ⟨w,t,hq⟩ hi' hj'
          | inverseFollowup q => cases hq
          | returnFollowup hl => cases hq
          | cycleFollowup hs hl hm => cases hq
      | inverseFollowup p => cases hp
      | returnFollowup hk => cases hp
      | cycleFollowup hs hk hl => cases hp

theorem image_phase_two_roots_unique {p q b : T}
    (hp : ∃ u v, p = S (S (P u v))) (hq : ∃ u v, q = S (S (P u v)))
    (hi : Image p b) (hj : Image q b) : p = q :=
  image_phase_two_roots_unique_at_size (nodes b) p q b rfl hp hq hi hj

theorem column_phase_two_values_unique {u p q : T}
    (hp : ∃ a b, p = S (S (P a b))) (hq : ∃ a b, q = S (S (P a b)))
    (hc : Column u p) (hd : Column u q) : p = q := by
  rcases column_phase_two_base_shape hc hp with ⟨a,b,hu⟩ | ht
  · obtain ⟨x,y,hp⟩ := hp
    obtain ⟨w,t,hq⟩ := hq
    rw [hu,hp] at hc
    rw [hu,hq] at hd
    have hs := (column_zero_to_two hc).symm.trans (column_zero_to_two hd)
    rw [hp,hq,hs]
  · exact image_phase_two_roots_unique hp hq
      (column_two_to_two_inverse hc ht hp) (column_two_to_two_inverse hd ht hq)

end submission.Equation22446Lineage

/- Checked source module: LineageSyntax.AtomOrZeroBases -/
set_option autoImplicit false
set_option Elab.async false

namespace submission.Equation22446Lineage
open submission.Equation22446Guarded

def AtomOrZero (p : T) : Prop := (∃ c n, p = T.e c n) ∨ (∃ u v, p = P u v)

theorem atom_or_zero_not_one {p : T} (hp : AtomOrZero p) : ∀ u v, p ≠ S (P u v) := by
  rcases hp with ⟨c,n,rfl⟩ | ⟨a,b,rfl⟩ <;> intro u v h <;> cases h

theorem atom_or_zero_not_two {p : T} (hp : AtomOrZero p) : ∀ u v, p ≠ S (S (P u v)) := by
  rcases hp with ⟨c,n,rfl⟩ | ⟨a,b,rfl⟩ <;> intro u v h <;> cases h

theorem atom_or_zero_next_nonzero {p : T} (hp : AtomOrZero p) : ∀ u v, S p ≠ P u v := by
  intro u v h
  have he := congrArg (fun t => S (S t)) h
  simp only [cube] at he
  exact atom_or_zero_not_two hp u v he

theorem atom_or_zero_double_nonzero {p : T} (hp : AtomOrZero p) : ∀ u v, S (S p) ≠ P u v := by
  intro u v h
  have he := congrArg S h
  simp only [cube] at he
  exact atom_or_zero_not_one hp u v he

theorem shared_column_atom_or_zero_bound {p q a : T} (hp : AtomOrZero p)
    (hc : Column p a) (hd : Column q a) : nodes p ≤ nodes q := by
  rcases hp with ⟨c,n,rfl⟩ | ⟨u,v,rfl⟩
  · exact Nat.zero_le _
  · exact shared_column_phase_zero_bound hc hd

theorem column_double_atom_or_zero_unique {p q : T} (hp : AtomOrZero p) (hq : AtomOrZero q)
    (hc : Column q (S (S p))) : p = q := by
  generalize he : S (S p) = a at hc
  cases hc with
  | ancestry hl =>
      have ht := S_injective (S_injective he)
      rw [←ht] at hl
      exact (lineage_non_phase_two hl (atom_or_zero_not_two hp)).symm
  | literal q y => exact False.elim (atom_or_zero_double_nonzero hp _ _ he)
  | inverseImage hi =>
      rw [←he] at hi
      have ht := image_nonzero_output hi (atom_or_zero_next_nonzero hq)
      simp only [cube] at ht
      exact (S_injective ht).symm

theorem column_atom_or_zero_unique {p q a : T} (hp : AtomOrZero p) (hq : AtomOrZero q)
    (hc : Column p a) (hd : Column q a) : p = q := by
  cases hc with
  | ancestry hl =>
      cases hl with
      | refl => exact column_double_atom_or_zero_unique hp hq hd
      | @step p u v hl hi =>
          simp only [cube] at hd
          generalize he : S (P u v) = a at hd
          cases hd with
          | ancestry hm =>
              have hr := congrArg S he
              rw [cube] at hr
              rw [←hr] at hm
              cases hm with
              | refl => exact False.elim (atom_or_zero_not_two hq _ _ rfl)
              | step hm hj =>
                  exact lineage_non_two_roots_unique (atom_or_zero_not_two hp) (atom_or_zero_not_two hq) hl hm
          | literal q y => cases he
          | inverseImage hj =>
              rw [←he] at hj
              have hr := congrArg S (image_nonzero_target hj (atom_or_zero_next_nonzero hq))
              simp only [cube] at hr
              exact False.elim (atom_or_zero_not_two hq _ _ hr.symm)
  | literal p y =>
      generalize he : P y (S p) = a at hd
      cases hd with
      | ancestry hl =>
          have hr := congrArg S he
          rw [cube] at hr
          have hq' := lineage_non_phase_two hl (by intro u v h; rw [←hr] at h; cases h)
          exact False.elim (atom_or_zero_not_one hq _ _ (hq'.trans hr.symm))
      | literal q z => exact S_injective (T.p.inj he).2.2
      | inverseImage hi =>
          rw [←he] at hi
          have hr := congrArg S (image_nonzero_target hi (atom_or_zero_next_nonzero hq))
          simp only [cube] at hr
          exact False.elim (atom_or_zero_not_one hq _ _ hr.symm)
  | inverseImage hi =>
      rw [image_nonzero_target hi (atom_or_zero_next_nonzero hp)] at hd
      exact column_double_atom_or_zero_unique hp hq hd

end submission.Equation22446Lineage

/- Checked source module: LineageSyntax.MixedPrincipalDescent -/
set_option autoImplicit false
set_option Elab.async false

namespace submission.Equation22446Lineage
open submission.Equation22446Guarded

theorem low_two_shared_transport_inverse {p q u a : T}
    (hp : AtomOrZero p) (hq : ∃ x y, q = S (S (P x y)))
    (hc : Column p a) (hd : Column q a) (hu : Column u p) (hv : Column u q) :
    Image p (S u) ∧ Image q (S u) := by
  cases hu with
  | @ancestry u r hl =>
      have hr : ∀ x y, r ≠ S (S (P x y)) := by
        intro x y he
        exact atom_or_zero_not_one hp x y (by rw [he]; rfl)
      have he := lineage_non_phase_two hl hr
      rcases column_phase_two_base_shape hv hq with ⟨x,y,hu⟩ | ⟨x,y,hu⟩
      · exact False.elim (atom_or_zero_not_two hp x y (by rw [←he,hu]))
      · exact False.elim (atom_or_zero_not_one hp x y (by rw [←he,hu]; rfl))
  | literal u y =>
      obtain ⟨x,z,hq⟩ := hq
      have hs := shared_column_atom_or_zero_bound hp hc hd
      have ht := column_phase_two_bound hv x z hq
      have hb := pair_right .zero y (S u)
      change nodes (S u) < nodes (P y (S u)) at hb
      rw [nodes_S] at hb
      exact False.elim (Nat.not_lt_of_ge (Nat.le_trans hs ht) hb)
  | inverseImage hi =>
      rcases column_phase_two_base_shape hv hq with ⟨x,y,hu⟩ | ht
      · have he := image_nonzero_target hi (by intro w z h; rw [hu] at h; cases h)
        exact False.elim (atom_or_zero_not_two hp x y (by rw [he,hu]))
      · exact ⟨hi,column_two_to_two_inverse hv ht hq⟩

theorem low_two_principal_false_at_size (n : Nat) :
    ∀ p q a b, nodes b = n → AtomOrZero p → (∃ x y, q = S (S (P x y))) →
      Column p a → Column q a → Image p b → Image q b → False := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      intro p q a b hn hp hq hc hd hi hj
      obtain ⟨w,t,hq⟩ := hq
      cases hi with
      | square p =>
          have he := image_nonzero_target hj (atom_or_zero_double_nonzero hp)
          simp only [cube] at he
          exact atom_or_zero_not_two hp w t (he.symm.trans hq)
      | literal p z =>
          generalize he : P (P p z) z = b at hj
          cases hj with
          | square q => rw [hq] at he; cases he
          | literal q t =>
              have hpq := (T.p.inj (T.p.inj he).2.1).2.1
              exact atom_or_zero_not_two hp w _ (hpq.trans hq)
          | transport hk hl =>
              rw [←(T.p.inj he).2.1,←(T.p.inj he).2.2] at hl
              exact image_pair_tail_false hl
          | inverseFollowup q => cases hq
          | returnFollowup hk => cases hq
          | cycleFollowup hs hk hl => cases hq
      | @transport u p v hu hv =>
          generalize he : P u v = b at hj
          cases hj with
          | square q => rw [hq] at he; cases he
          | literal q z =>
              rw [(T.p.inj he).2.1,(T.p.inj he).2.2] at hv
              exact image_pair_tail_false hv
          | transport hk hl =>
              rw [←(T.p.inj he).2.1] at hk
              obtain ⟨hi',hj'⟩ := low_two_shared_transport_inverse hp ⟨w,t,hq⟩ hc hd hu hk
              have hs : nodes (S u) < n := by rw [nodes_S,←hn]; exact pair_left .zero u v
              exact ih _ hs p q a (S u) rfl hp ⟨w,t,hq⟩ hc hd hi' hj'
          | inverseFollowup q => cases hq
          | returnFollowup hk => cases hq
          | cycleFollowup hs hk hl => cases hq
      | inverseFollowup v =>
          have hs := shared_column_atom_or_zero_bound hp hc hd
          have ht := image_phase_two_output_left hj w t (S (S v)) (S v) hq rfl
          simp only [nodes_S] at ht
          exact Nat.not_lt_of_ge (Nat.le_trans hs ht) (pair_left .zero v (S v))
      | @returnFollowup v z hk =>
          have hs := shared_column_atom_or_zero_bound hp hc hd
          have ht := image_phase_two_output_left hj w t (S (P v z)) (S v) hq rfl
          simp only [nodes_S] at ht
          have hb := pair_left .zero (S (S (P v z))) (S v)
          simp only [nodes_S] at hb
          exact Nat.not_lt_of_ge (Nat.le_trans hs ht) hb
      | @cycleFollowup u v x y z hs hk hl =>
          have ht := shared_column_atom_or_zero_bound hp hc hd
          have hq' := image_phase_two_output_left hj w t (S (P x y)) z hq rfl
          simp only [nodes_S] at hq'
          rw [cycle_followup_input_eq hs hk hl] at ht
          have hb := pair_left .zero (S (S (P x y))) z
          simp only [nodes_S] at hb
          exact Nat.not_lt_of_ge (Nat.le_trans ht hq') hb

theorem low_two_principal_false {p q a b : T}
    (hp : AtomOrZero p) (hq : ∃ x y, q = S (S (P x y)))
    (hc : Column p a) (hd : Column q a) (hi : Image p b) (hj : Image q b) : False :=
  low_two_principal_false_at_size (nodes b) p q a b rfl hp hq hc hd hi hj

end submission.Equation22446Lineage

/- Checked source module: LineageSyntax.LineageImageUniqueness -/
set_option autoImplicit false
set_option Elab.async false

namespace submission.Equation22446Lineage
open submission.Equation22446Guarded

theorem column_two_value_inverse {u q : T} (hc : Column u q)
    (hq : ∃ x y, q = S (S (P x y))) : Image q (S u) := by
  cases hc with
  | ancestry hl =>
      obtain ⟨x,y,hq⟩ := hq
      have hr := S_injective (S_injective hq)
      have hu := lineage_non_phase_two hl (by intro a b h; rw [hr] at h; cases h)
      rw [hu]
      simpa only [cube] using (Image.square (S (S _)))
  | literal u y => obtain ⟨x,z,hq⟩ := hq; cases hq
  | inverseImage hi => exact hi

theorem joint_lineage_query_unique (n : Nat) :
    (∀ p q b, nodes b = n → Lineage p q → Image p b → Image q b → p = q) ∧
    (∀ u p q, nodes u = n → Lineage p q → Column u p → Column u q → p = q) := by
  classical
  induction n using Nat.strongRecOn with
  | ind n ih =>
      have image_here : ∀ p q b, nodes b = n → Lineage p q → Image p b → Image q b → p = q := by
        intro p q b hn hl hi hj
        by_cases heq : p = q
        · exact heq
        have hq : ∃ x y, q = S (S (P x y)) := by
          cases hl with
          | refl => exact False.elim (heq rfl)
          | step hl hk => exact ⟨_,_,rfl⟩
        obtain ⟨w,t,hq⟩ := hq
        have hpq := lineage_nodes hl
        cases hi with
        | square p =>
            rcases phase_one_or_double_nonzero p with ⟨x,y,hp⟩ | hp
            · have hs := image_phase_two_output_left hj w t x y hq (by rw [hp]; rfl)
              rw [hp,nodes_S] at hpq
              exact False.elim (Nat.not_lt_of_ge (Nat.le_trans hpq hs) (pair_left .zero x y))
            · have he := image_nonzero_target hj hp
              simpa only [cube] using he.symm
        | literal p z =>
            generalize he : P (P p z) z = b at hj
            cases hj with
            | square q => rw [hq] at he; cases he
            | literal q t => exact (T.p.inj (T.p.inj he).2.1).2.1
            | transport hc hk =>
                rw [←(T.p.inj he).2.1,←(T.p.inj he).2.2] at hk
                exact False.elim (image_pair_tail_false hk)
            | inverseFollowup q => cases hq
            | returnFollowup hk => cases hq
            | cycleFollowup hs hk hm => cases hq
        | @transport u p v hc hk =>
            generalize he : P u v = b at hj
            cases hj with
            | square q => rw [hq] at he; cases he
            | literal q z =>
                rw [(T.p.inj he).2.1,(T.p.inj he).2.2] at hk
                exact False.elim (image_pair_tail_false hk)
            | transport hd hm =>
                rw [←(T.p.inj he).2.1] at hd
                have hs : nodes u < n := by rw [←hn]; exact pair_left .zero u v
                exact (ih _ hs).2 u p q rfl hl hc hd
            | inverseFollowup q => cases hq
            | returnFollowup hk => cases hq
            | cycleFollowup hs hk hm => cases hq
        | inverseFollowup v =>
            have hs := image_phase_two_output_left hj w t (S (S v)) (S v) hq rfl
            simp only [nodes_S] at hs
            exact False.elim (Nat.not_lt_of_ge (Nat.le_trans hpq hs) (pair_left .zero v (S v)))
        | @returnFollowup v z hk =>
            have hs := image_phase_two_output_left hj w t (S (P v z)) (S v) hq rfl
            simp only [nodes_S] at hs
            have hb := pair_left .zero (S (S (P v z))) (S v)
            simp only [nodes_S] at hb
            exact False.elim (Nat.not_lt_of_ge (Nat.le_trans hpq hs) hb)
        | @cycleFollowup x y u v z hs hk hm =>
            have ht := image_phase_two_output_left hj w t (S (P u v)) z hq rfl
            simp only [nodes_S] at ht
            rw [cycle_followup_input_eq hs hk hm] at hpq
            have hb := pair_left .zero (S (S (P u v))) z
            simp only [nodes_S] at hb
            exact False.elim (Nat.not_lt_of_ge (Nat.le_trans hpq ht) hb)
      refine ⟨image_here,?_⟩
      intro u p q hn hl hc hd
      by_cases heq : p = q
      · exact heq
      have hpq : nodes p < nodes q := by
        apply Nat.lt_of_not_ge
        intro hs
        exact heq (lineage_nonincreasing_eq hl hs)
      have hq : ∃ x y, q = S (S (P x y)) := by
        cases hl with
        | refl => exact False.elim (heq rfl)
        | step hl hi => exact ⟨_,_,rfl⟩
      obtain ⟨x,y,hq'⟩ := hq
      have hqu := column_phase_two_bound hd x y hq'
      cases hc with
      | ancestry hm =>
          have hup := lineage_nodes hm
          simp only [nodes_S] at hpq
          exact False.elim (Nat.not_lt_of_ge (Nat.le_trans hqu hup) hpq)
      | literal u z =>
          have hup := pair_right .zero z (S u)
          rw [nodes_S] at hup
          exact False.elim (Nat.not_lt_of_ge hqu (Nat.lt_trans hup hpq))
      | inverseImage hi =>
          exact image_here p q (S u) (by simpa only [nodes_S] using hn) hl hi
            (column_two_value_inverse hd ⟨x,y,hq'⟩)

theorem image_lineage_roots_unique {p q b : T} (hl : Lineage p q)
    (hi : Image p b) (hj : Image q b) : p = q :=
  (joint_lineage_query_unique (nodes b)).1 p q b rfl hl hi hj

theorem column_lineage_values_unique {u p q : T} (hl : Lineage p q)
    (hc : Column u p) (hd : Column u q) : p = q :=
  (joint_lineage_query_unique (nodes u)).2 u p q rfl hl hc hd

end submission.Equation22446Lineage

/- Checked source module: LineageSyntax.OneTwoRootBounds -/
set_option autoImplicit false
set_option Elab.async false

namespace submission.Equation22446Lineage
open submission.Equation22446Guarded

theorem one_two_columns_nongrowing_inverse {p q u : T}
    (hp : ∃ x y, p = S (P x y)) (hq : ∃ x y, q = S (S (P x y)))
    (hs : nodes p ≤ nodes q) (hc : Column u p) (hd : Column u q) :
    Image p (S u) ∧ Image q (S u) := by
  have hj := column_two_value_inverse hd hq
  obtain ⟨x,y,hp⟩ := hp
  obtain ⟨w,t,hq⟩ := hq
  have hqu := column_phase_two_bound hd w t hq
  cases hc with
  | ancestry hl =>
      cases hl with
      | refl =>
          have hu := congrArg S hp
          rw [cube] at hu
          have ht := image_phase_two_strict hj ⟨w,t,hq⟩ ⟨x,y,by rw [hu]; rfl⟩
          simp only [nodes_S] at hs ht
          exact False.elim (Nat.not_lt_of_ge hs ht)
      | @step u r s hl hi =>
          have hur := lineage_nodes hl
          have hrp := pair_left .zero r s
          simp only [cube,nodes_S] at hs
          exact False.elim (Nat.not_lt_of_ge (Nat.le_trans hs hqu) (Nat.lt_of_le_of_lt hur hrp))
  | literal u z => cases hp
  | inverseImage hi => exact ⟨hi,hj⟩

theorem one_two_images_nongrowing_false_at_size (n : Nat) :
    ∀ p q b, nodes b = n → (∃ x y, p = S (P x y)) → (∃ x y, q = S (S (P x y))) →
      nodes p ≤ nodes q → Image p b → Image q b → False := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      intro p q b hn hp hq hs hi hj
      obtain ⟨x,y,hp⟩ := hp
      obtain ⟨w,t,hq⟩ := hq
      cases hi with
      | square p =>
          have ht := image_phase_two_output_left hj w t x y hq (by rw [hp]; rfl)
          rw [hp,nodes_S] at hs
          exact Nat.not_lt_of_ge (Nat.le_trans hs ht) (pair_left .zero x y)
      | literal p z =>
          generalize he : P (P p z) z = b at hj
          cases hj with
          | square q => rw [hq] at he; cases he
          | literal q z =>
              have heq := (T.p.inj (T.p.inj he).2.1).2.1
              rw [hp,hq] at heq
              cases heq
          | transport hc hk =>
              rw [←(T.p.inj he).2.1,←(T.p.inj he).2.2] at hk
              exact image_pair_tail_false hk
          | inverseFollowup q => cases hq
          | returnFollowup hk => cases hq
          | cycleFollowup ht hk hl => cases hq
      | @transport u p v hc hk =>
          generalize he : P u v = b at hj
          cases hj with
          | square q => rw [hq] at he; cases he
          | literal q z =>
              rw [(T.p.inj he).2.1,(T.p.inj he).2.2] at hk
              exact image_pair_tail_false hk
          | transport hd hl =>
              rw [←(T.p.inj he).2.1] at hd
              obtain ⟨hi',hj'⟩ := one_two_columns_nongrowing_inverse ⟨x,y,hp⟩ ⟨w,t,hq⟩ hs hc hd
              have ht : nodes (S u) < n := by rw [nodes_S,←hn]; exact pair_left .zero u v
              exact ih _ ht p q (S u) rfl ⟨x,y,hp⟩ ⟨w,t,hq⟩ hs hi' hj'
          | inverseFollowup q => cases hq
          | returnFollowup hk => cases hq
          | cycleFollowup ht hk hl => cases hq
      | inverseFollowup p => cases hp
      | returnFollowup hk => cases hp
      | cycleFollowup ht hk hl => cases hp

theorem image_one_two_root_bound {p q b : T}
    (hp : ∃ x y, p = S (P x y)) (hq : ∃ x y, q = S (S (P x y)))
    (hi : Image p b) (hj : Image q b) : nodes q < nodes p := by
  apply Nat.lt_of_not_ge
  intro hs
  exact one_two_images_nongrowing_false_at_size (nodes b) p q b rfl hp hq hs hi hj

end submission.Equation22446Lineage

/- Checked source module: LineageSyntax.CanonicalColumnTools -/
set_option autoImplicit false
set_option Elab.async false

namespace submission.Equation22446Lineage
open submission.Equation22446Guarded

theorem column_pair_cases {p x y : T} (hc : Column p (P x y)) :
    p = S (P x y) ∨ y = S p ∨ Image (P x y) (S p) := by
  generalize he : P x y = a at hc
  cases hc with
  | ancestry hl =>
      have hr := congrArg S he
      rw [cube] at hr
      have hp := lineage_non_phase_two hl (by intro u v h; rw [←hr] at h; cases h)
      exact Or.inl (by simpa only [cube] using hp)
  | literal p z => exact Or.inr (Or.inl (T.p.inj he).2.2)
  | inverseImage hi => exact Or.inr (Or.inr hi)

theorem column_pair_non_two_cases {p x y : T} (hc : Column p (P x y))
    (hn : ∀ u v, S p ≠ P u v) : p = S (P x y) ∨ y = S p := by
  rcases column_pair_cases hc with hp | hy | hi
  · exact Or.inl hp
  · exact Or.inr hy
  · exact Or.inl (S_injective (image_nonzero_output hi hn))

theorem column_zero_pair_literal {u v x y : T} (hc : Column (P u v) (P x y)) :
    y = S (P u v) := by
  rcases column_pair_non_two_cases hc (by intro a b h; cases h) with hp | hy
  · cases hp
  · exact hy

theorem lineage_pair_without_image_root {r h z : T} (hn : ¬ Image h z)
    (hl : Lineage r (S (S (P h z)))) : r = S (S (P h z)) := by
  cases hl with
  | refl => rfl
  | step hl hi => exact False.elim (hn hi)

theorem column_zero_pair_rotated_chain_false {u h z x y : T}
    (hn : ¬ Image h z) (hs : nodes u < nodes (P h z))
    (hc : Column u (S (P x y))) (hd : Column (P h z) (P x y)) : False := by
  have hy := column_zero_pair_literal hd
  have hqa : nodes (P h z) < nodes (P x y) := by
    have hb := pair_right .zero x y
    change nodes y < nodes (P x y) at hb
    simpa only [hy,nodes_S] using hb
  have hua : nodes u < nodes (S (P x y)) := by rw [nodes_S]; exact Nat.lt_trans hs hqa
  have hi := column_small_phase_one_origin hc x y rfl hua
  rw [hy] at hi
  have hx := image_nonzero_target hi (by intro a b h; cases h)
  obtain ⟨r,hr,hu⟩ := column_small_phase_one_common_root hc x y rfl hua
  rw [hx] at hr
  have he := lineage_pair_without_image_root hn hr
  have hb := lineage_nodes hu
  rw [he,nodes_S,nodes_S] at hb
  exact Nat.not_lt_of_ge hb hs

theorem canonical_square_transport_target {u v x y : T}
    (hc : Column u (S (P x y))) (hd : Column (S (P u v)) (P x y)) :
    S (P u v) = S (P x y) := by
  rcases column_pair_non_two_cases hd (by intro a b h; cases h) with hp | hy
  · exact hp
  · have hb := pair_right .zero x y
    change nodes y < nodes (P x y) at hb
    have hba : nodes (P u v) < nodes (P x y) := by simpa only [hy,nodes_S] using hb
    have hua : nodes u < nodes (S (P x y)) := by
      rw [nodes_S]
      exact Nat.lt_trans (pair_left .zero u v) hba
    have hi := column_small_phase_one_origin hc x y rfl hua
    rw [hy] at hi
    have hx := image_nonzero_target hi (by intro a b h; cases h)
    simp only [cube] at hx
    rw [hx,hy] at hc
    have hs := column_ancestor_bound hc (P u v) (P u v) (S (S (P u v))) rfl
      (by intro a b h; cases h) (.refl _)
    exact False.elim (Nat.not_lt_of_ge hs (pair_left .zero u v))

end submission.Equation22446Lineage

/- Checked source module: LineageSyntax.ColumnLineageChains -/
set_option autoImplicit false
set_option Elab.async false

namespace submission.Equation22446Lineage
open submission.Equation22446Guarded

theorem column_two_cycle_false {u q : T} (hc : Column u q) (hd : Column q u) : False := by
  cases hc with
  | ancestry hl =>
      cases hl with
      | refl => exact lineage_successor_column_false (p := S (S u)) (.refl _) (by simpa only [cube] using hd)
      | @step u r t hl hi =>
          simp only [cube] at hd
          have hs := column_non_two_base_bound hd (by intro x y h; cases h)
          simp only [nodes_S] at hs
          exact Nat.not_lt_of_ge hs (Nat.lt_of_le_of_lt (lineage_nodes hl) (pair_left .zero r t))
  | literal u y =>
      have hs := column_non_two_base_bound hd (by intro x y h; cases h)
      have hb := pair_right .zero y (S u)
      rw [nodes_S] at hb
      exact Nat.not_lt_of_ge hs hb
  | inverseImage hi => exact column_image_next_false hd hi

theorem column_chain_lineage_false {u q r : T} (hl : Lineage u r)
    (hc : Column u q) (hd : Column q r) : False := by
  cases hl with
  | refl => exact column_two_cycle_false hc hd
  | @step u x y hl hi =>
      rcases column_phase_two_base_shape hd ⟨x,y,rfl⟩ with ⟨a,b,hq⟩ | hq
      · rw [hq] at hd
        have he := column_zero_to_two hd
        have hq' : q = S (S (S (P x y))) := by rw [hq,he,cube]
        rw [hq'] at hc
        exact lineage_successor_column_false (.step hl hi) hc
      · obtain ⟨a,b,hq⟩ := hq
        have hj := column_two_value_inverse hd ⟨x,y,rfl⟩
        have hs := image_phase_two_strict hj ⟨x,y,rfl⟩ ⟨a,b,by rw [hq]; rfl⟩
        simp only [nodes_S] at hs
        have hqu := column_phase_two_bound hc a b hq
        have hur := lineage_nodes (Lineage.step hl hi)
        simp only [nodes_S] at hur
        exact Nat.not_lt_of_ge (Nat.le_trans hqu hur) hs

theorem common_root_successor_tail_false {r y u : T}
    (hl : Lineage r (S (S (P y (S u))))) (hu : Lineage r u) : False := by
  cases hl with
  | refl =>
      have hs := lineage_nodes hu
      simp only [nodes_S] at hs
      have hb := pair_right .zero y (S u)
      rw [nodes_S] at hb
      exact Nat.not_lt_of_ge hs hb
  | step hl hi => exact image_common_root_next_false hi _ u rfl hl hu

end submission.Equation22446Lineage

/- Checked source module: LineageSyntax.RotatedColumnOrigins -/
set_option autoImplicit false
set_option Elab.async false

namespace submission.Equation22446Lineage
open submission.Equation22446Guarded

theorem rotated_column_canonical_target {q x y : T} (ha : Normal (P x y))
    (hc : Column (S (S (P x y))) q) (hd : Column q (P x y)) : q = S (P x y) := by
  cases hc with
  | @ancestry u r hl =>
      obtain ⟨v,w,hr⟩ := lineage_phase_two_preserved hl ⟨x,y,rfl⟩
      have hs := column_non_two_base_bound hd (by intro a b h; rw [cube,hr] at h; cases h)
      have he := lineage_nonincreasing_eq hl (by simpa only [nodes_S] using hs)
      rw [←he,cube]
  | literal u z =>
      have hs := column_non_two_base_bound hd (by intro a b h; cases h)
      have hb := pair_right .zero z (S (S (S (P x y))))
      simp only [cube] at hs hb
      exact False.elim (Nat.not_lt_of_ge hs hb)
  | inverseImage hi =>
      simp only [cube] at hi
      exact normal_diagonal_target ha hd hi

theorem rotated_column_completed_target {u q x y : T}
    (hl : Lineage u x) (hxy : Image x y) (hc : Column u q) (hd : Column q (P x y)) :
    q = S (P x y) := by
  rcases column_pair_cases hd with hq | hy | hi
  · exact hq
  · rw [hy] at hxy
    exact False.elim (column_chain_lineage_false hl hc (.inverseImage hxy))
  · rcases phase_two_or_square_nonzero q with ⟨v,w,hq⟩ | hn
    · have hqu := column_phase_two_bound hc v w hq
      have hux := lineage_nodes hl
      have hs : nodes q < nodes (P x y) :=
        Nat.lt_of_le_of_lt (Nat.le_trans hqu hux) (pair_left .zero x y)
      have hm := shrinking_inverse_lineage hi hs
      have hyq := lineage_nodes hm
      simp only [nodes_S] at hyq
      rcases phase_two_or_square_nonzero x with ⟨a,b,hx⟩ | hn
      · have hxy' := image_phase_two_bound hxy a b hx
        have he := lineage_nonincreasing_eq hl (Nat.le_trans hxy' (Nat.le_trans hyq hqu))
        rw [he] at hc
        have ht := image_phase_two_strict (column_two_value_inverse hc ⟨v,w,hq⟩)
          ⟨v,w,hq⟩ ⟨a,b,by rw [hx]; rfl⟩
        simp only [nodes_S] at ht
        exact False.elim (Nat.not_lt_of_ge (Nat.le_trans hxy' hyq) ht)
      · have he := lineage_non_phase_two hl (by
          intro a b hx
          exact hn a b (by rw [hx,cube]))
        rw [he] at hc
        rcases column_phase_two_base_shape hc ⟨v,w,hq⟩ with ⟨a,b,hx⟩ | ⟨a,b,hx⟩
        · have hc' : Column (P a b) (S (S (P v w))) := by
            have ht := hc
            rw [hx,hq] at ht
            exact ht
          have ht := column_zero_to_two hc'
          have hqx : q = S (S x) := by rw [hq,hx,ht]; rfl
          rw [hqx,cube] at hi
          exact False.elim (image_pair_flip_false hxy hi)
        · exact False.elim (hn a b (by rw [hx,cube]))
    · exact S_injective (image_nonzero_output hi hn)

theorem rotated_column_inverse_ancestry_target {u r x y : T}
    (hu : ∃ a b, u = S (S (P a b))) (hl : Lineage u r)
    (hd : Column (S (S r)) (P x y)) (hi : Image (S (P x y)) (S u)) :
    S (S r) = S (P x y) := by
  obtain ⟨a,b,hr⟩ := lineage_phase_two_preserved hl hu
  have hn : ∀ v w, S (S (S r)) ≠ P v w := by
    intro v w h
    rw [cube,hr] at h
    cases h
  rcases column_pair_non_two_cases hd hn with he | hy
  · exact he
  · simp only [cube] at hy
    have hua : nodes (S u) < nodes (S (P x y)) := by
      simp only [nodes_S]
      rw [hy]
      have hb := pair_right .zero x y
      change nodes y < nodes (P x y) at hb
      rw [hy] at hb
      exact Nat.lt_of_le_of_lt (lineage_nodes hl) hb
    have hxy := image_small_phase_one_origin hi x y rfl hua
    rw [hy] at hxy
    have hx := image_nonzero_target hxy (by intro v w h; rw [hr] at h; cases h)
    have hnx : ∀ v w, x ≠ S (S (P v w)) := by
      intro v w h
      rw [hx,hr,cube] at h
      cases h
    have hb := image_ancestor_bound hi x x y rfl hnx (.refl _)
    rw [hx,nodes_S,nodes_S] at hb
    exact False.elim (Nat.not_lt_of_ge (lineage_nodes hl) hb)

theorem rotated_column_inverse_literal_false {u z x y : T}
    (hd : Column (P z (S u)) (P x y)) (hi : Image (S (P x y)) (S u)) : False := by
  have hy := column_zero_pair_literal hd
  have hua : nodes (S u) < nodes (S (P x y)) := by
    simp only [nodes_S]
    rw [hy]
    have hb := pair_right .zero x y
    change nodes y < nodes (P x y) at hb
    rw [hy,nodes_S] at hb
    have hz := pair_right .zero z (S u)
    rw [nodes_S] at hz
    exact Nat.lt_trans hz hb
  have hxy := image_small_phase_one_origin hi x y rfl hua
  rw [hy] at hxy
  have hx := image_nonzero_target hxy (by intro a b h; cases h)
  obtain ⟨r,hr,hu⟩ := image_small_phase_one_common_root hi x y rfl hua
  simp only [cube] at hu
  rw [hx] at hr
  exact common_root_successor_tail_false hr hu

end submission.Equation22446Lineage

/- Checked source module: LineageSyntax.CanonicalInduction -/
set_option autoImplicit false
set_option Elab.async false

namespace submission.Equation22446Lineage
open submission.Equation22446Guarded

theorem image_literal_target_cases {p z q b : T} (hi : Image q b) (he : b = P (P p z) z) :
    q = p ∨ q = S b := by
  cases hi with
  | square q => exact Or.inr (cube q).symm
  | literal q t => exact Or.inl (T.p.inj (T.p.inj he).2.1).2.1
  | transport hc hj =>
      rw [(T.p.inj he).2.1,(T.p.inj he).2.2] at hj
      exact False.elim (image_pair_tail_false hj)
  | inverseFollowup v =>
      have hb := pair_right .zero p z
      change nodes z < nodes (P p z) at hb
      rw [←(T.p.inj he).2.1,←(T.p.inj he).2.2] at hb
      simp only [nodes_S] at hb
      exact False.elim (Nat.lt_irrefl _ hb)
  | returnFollowup hj => cases (T.p.inj he).2.1
  | cycleFollowup hs hj hk => cases (T.p.inj he).2.1

theorem joint_canonical_unique (n : Nat) :
    (∀ x y q b, nodes b = n → Normal (P x y) → Normal b → Column q (P x y) →
      Image (S (P x y)) b → Image q b → q = S (P x y)) ∧
    (∀ u q x y, nodes u = n → Normal (P x y) → Normal u →
      Column u q → Column q (P x y) → Column u (S (P x y)) → q = S (P x y)) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      have canonical_here : ∀ x y q b, nodes b = n → Normal (P x y) → Normal b →
          Column q (P x y) → Image (S (P x y)) b → Image q b → q = S (P x y) := by
        intro x y q b hn ha hb hc hi hj
        generalize hp : S (P x y) = p at hi
        rw [←hp]
        cases hi with
        | square p =>
            rw [←hp,cube] at hj
            exact normal_diagonal_target ha hc hj
        | literal p z =>
            rcases image_literal_target_cases hj rfl with hq | hq
            · exact hq.trans hp.symm
            · have hs := column_non_two_base_bound hc (by intro u v h; rw [hq] at h; cases h)
              rw [hq,nodes_S] at hs
              have ht := Nat.lt_trans (pair_left .zero p z) (pair_left .zero _ z)
              have hpn : nodes p = nodes (P x y) := by rw [←hp,nodes_S]
              rw [hpn] at ht
              exact False.elim (Nat.not_lt_of_ge hs ht)
        | @transport u p v hu hv =>
            rw [←hp] at hu
            have hnu : Normal u := hb.1
            generalize he : P u v = b at hj
            cases hj with
            | square q =>
                have hq := congrArg S he
                rw [cube] at hq
                rw [←hq] at hc
                exact hq.symm.trans (canonical_square_transport_target hu hc)
            | literal q z =>
                rw [(T.p.inj he).2.1,(T.p.inj he).2.2] at hv
                exact False.elim (image_pair_tail_false hv)
            | transport hk hl =>
                rw [←(T.p.inj he).2.1] at hk
                have hs : nodes u < n := by rw [←hn]; exact pair_left .zero u v
                exact (ih _ hs).2 u q x y rfl ha hnu hk hc hu
            | inverseFollowup w =>
                rw [(T.p.inj he).2.1] at hu
                have hs : nodes (S (S w)) < nodes (P w (S w)) := by
                  simp only [nodes_S]
                  exact pair_left .zero w (S w)
                exact False.elim (column_zero_pair_rotated_chain_false
                  (fun hi => image_no_successor hi) hs hu hc)
            | @returnFollowup w t hk =>
                rw [(T.p.inj he).2.1] at hu
                have hs : nodes (S (P w t)) < nodes (P (S (S (P w t))) (S w)) := by
                  have hs := pair_left .zero (S (S (P w t))) (S w)
                  change nodes (S (S (P w t))) < nodes (P (S (S (P w t))) (S w)) at hs
                  simpa only [nodes_S] using hs
                have hnot : ¬ Image (S (S (P w t))) (S w) := by
                  intro h
                  have hs := image_phase_two_bound h w t rfl
                  simp only [nodes_S] at hs
                  exact Nat.not_lt_of_ge hs (pair_left .zero w t)
                exact False.elim (column_zero_pair_rotated_chain_false hnot hs hu hc)
            | @cycleFollowup a b w t z hs hk hl =>
                rw [(T.p.inj he).2.1] at hu
                rw [cycle_followup_input_eq hs hk hl] at hc
                have hsz : nodes (S (P w t)) < nodes (P (S (S (P w t))) z) := by
                  have ht := pair_left .zero (S (S (P w t))) z
                  change nodes (S (S (P w t))) < nodes (P (S (S (P w t))) z) at ht
                  simpa only [nodes_S] using ht
                have hnot : ¬ Image (S (S (P w t))) z := by
                  intro h
                  have hbig := image_phase_two_bound h w t rfl
                  simp only [nodes_S] at hbig
                  have hsmall := image_right_child hl .zero (P a b) z (by intro h; cases h) rfl
                  exact Nat.not_lt_of_ge hbig hsmall
                exact False.elim (column_zero_pair_rotated_chain_false hnot hsz hu hc)
        | inverseFollowup p => cases hp
        | returnFollowup hk => cases hp
        | cycleFollowup hs hk hl => cases hp
      refine ⟨canonical_here,?_⟩
      intro u q x y hn ha hnu hc hd ht
      generalize he : S (P x y) = a at ht
      rw [←he]
      cases ht with
      | ancestry hl =>
          cases hl with
          | refl =>
              have hu := congrArg S he
              rw [cube] at hu
              rw [←hu] at hc
              exact rotated_column_canonical_target ha hc hd
          | @step u r s hl hi =>
              simp only [cube] at he
              have hxy := S_injective he
              rw [←(T.p.inj hxy).2.1] at hl
              rw [←(T.p.inj hxy).2.1,←(T.p.inj hxy).2.2] at hi
              exact rotated_column_completed_target hl hi hc hd
      | literal u z => cases he
      | inverseImage hi =>
          rw [←he] at hi
          rcases phase_two_or_square_nonzero u with hu | hnot
          · cases hc with
            | ancestry hl => exact rotated_column_inverse_ancestry_target hu hl hd hi
            | literal u z => exact False.elim (rotated_column_inverse_literal_false hd hi)
            | inverseImage hj =>
                exact canonical_here x y q (S u) (by simpa only [nodes_S] using hn) ha
                  ((normal_rotate .one u).mpr hnu) hd hi hj
          · have hu := congrArg S (image_nonzero_target hi hnot)
            rw [cube] at hu
            rw [←hu] at hc
            exact rotated_column_canonical_target ha hc hd

theorem normal_canonical_principal_unique {x y q b : T}
    (ha : Normal (P x y)) (hb : Normal b) (hc : Column q (P x y))
    (hi : Image (S (P x y)) b) (hj : Image q b) : q = S (P x y) :=
  (joint_canonical_unique (nodes b)).1 x y q b rfl ha hb hc hi hj

theorem normal_rotated_column_target {u q x y : T}
    (ha : Normal (P x y)) (hu : Normal u)
    (hc : Column u q) (hd : Column q (P x y)) (ht : Column u (S (P x y))) :
    q = S (P x y) :=
  (joint_canonical_unique (nodes u)).2 u q x y rfl ha hu hc hd ht

end submission.Equation22446Lineage

/- Checked source module: LineageSyntax.PrincipalUnique -/
set_option autoImplicit false
set_option Elab.async false

namespace submission.Equation22446Lineage
open submission.Equation22446Guarded

theorem non_one_base_cases {p : T} (hp : ∀ u v, p ≠ S (P u v)) :
    AtomOrZero p ∨ (∃ u v, p = S (S (P u v))) := by
  cases p with
  | e c n => exact Or.inl (Or.inl ⟨c,n,rfl⟩)
  | p c u v =>
      cases c with
      | zero => exact Or.inl (Or.inr ⟨u,v,rfl⟩)
      | one => exact False.elim (hp u v rfl)
      | two => exact Or.inr ⟨u,v,rfl⟩

theorem principal_non_one_unique {p q a b : T}
    (hp : ∀ u v, p ≠ S (P u v)) (hq : ∀ u v, q ≠ S (P u v))
    (hc : Column p a) (hd : Column q a) (hi : Image p b) (hj : Image q b) : p = q := by
  rcases non_one_base_cases hp with hp | hp
  · rcases non_one_base_cases hq with hq | hq
    · exact column_atom_or_zero_unique hp hq hc hd
    · exact False.elim (low_two_principal_false hp hq hc hd hi hj)
  · rcases non_one_base_cases hq with hq | hq
    · exact False.elim (low_two_principal_false hq hp hd hc hj hi)
    · exact image_phase_two_roots_unique hp hq hi hj

theorem principal_common_ancestry_unique {p q r b : T}
    (hl : Lineage p r) (hm : Lineage q r) (hi : Image p b) (hj : Image q b) : p = q := by
  rcases lineage_common_comparable hl hm with h | h
  · exact image_lineage_roots_unique h hi hj
  · exact (image_lineage_roots_unique h hj hi).symm

theorem principal_one_unique {u v q a b : T} (ha : Normal a) (hb : Normal b)
    (hc : Column (S (P u v)) a) (hd : Column q a)
    (hi : Image (S (P u v)) b) (hj : Image q b) : S (P u v) = q := by
  cases hc with
  | ancestry hl =>
      cases hl with
      | refl =>
          simp only [cube] at ha hd
          exact (normal_canonical_principal_unique ha hb hd hi hj).symm
      | @step p r t hl hk =>
          simp only [cube] at ha hd
          generalize he : S (P r t) = a at hd
          cases hd with
          | ancestry hm =>
              have hr := congrArg S he
              rw [cube] at hr
              rw [←hr] at hm
              cases hm with
              | refl => exact image_lineage_roots_unique (.step hl hk) hi hj
              | step hm ht => exact principal_common_ancestry_unique hl hm hi hj
          | literal q y => cases he
          | inverseImage ht =>
              rw [←he] at ht
              rcases phase_two_or_square_nonzero q with hq | hn
              · have hsmall := image_one_two_root_bound ⟨u,v,rfl⟩ hq hi hj
                have hbig := column_ancestor_bound (Column.inverseImage ht) (S (P u v)) r t rfl
                  (by intro x y h; cases h) hl
                exact False.elim (Nat.not_lt_of_ge hbig hsmall)
              · have hbad := image_nonzero_output ht hn
                simp only [cube] at hbad
                exact False.elim (hn r t hbad)
  | literal p y =>
      have canonical (hq : q = S (P y (S (S (P u v))))) : S (P u v) = q := by
        rw [hq] at hj
        exact (normal_canonical_principal_unique ha hb (Column.literal _ y) hj hi).trans hq.symm
      rcases column_pair_cases hd with hq | hq | ht
      · exact canonical hq
      · exact S_injective hq
      · rcases phase_two_or_square_nonzero q with hq | hn
        · have hsmall := image_one_two_root_bound ⟨u,v,rfl⟩ hq hi hj
          have hbig := column_right_child hd .zero y (S (S (P u v))) (by intro h; cases h) rfl
          simp only [nodes_S] at hsmall hbig
          exact False.elim (Nat.not_lt_of_ge hbig hsmall)
        · exact canonical (S_injective (image_nonzero_output ht hn))
  | inverseImage ht =>
      have he : a = P u v := by
        have he := image_nonzero_target ht (by intro x y h; cases h)
        simpa only [cube] using he
      rw [he] at ha hd
      exact (normal_canonical_principal_unique ha hb hd hi hj).symm

theorem principal_unique : PrincipalUnique := by
  classical
  intro a b p q ha hb hc hi hd hj
  by_cases hp : ∃ u v, p = S (P u v)
  · obtain ⟨u,v,hp⟩ := hp
    subst p
    exact principal_one_unique ha hb hc hd hi hj
  · by_cases hq : ∃ u v, q = S (P u v)
    · obtain ⟨u,v,hq⟩ := hq
      subst q
      exact (principal_one_unique ha hb hd hc hj hi).symm
    · exact principal_non_one_unique (by intro u v h; exact hp ⟨u,v,h⟩)
        (by intro u v h; exact hq ⟨u,v,h⟩) hc hd hi hj

theorem guard_unique : GuardUnique := guard_unique_iff_principal.mpr principal_unique

end submission.Equation22446Lineage

/- Checked source module: LineageSyntax.Model -/
set_option autoImplicit false
set_option Elab.async false

namespace submission.Equation22446Lineage

/-- The exact source equation, with every construction obligation discharged. -/
theorem equation22446 (x y z : NormalTree) :
    x = multiplication (multiplication y (multiplication x x))
      (multiplication (multiplication x z) z) :=
  source_with_principal_unique principal_unique x y z

theorem normalTower_nontrivial : normalTower 0 ≠ normalTower 1 := by
  intro h
  cases normalTower_injective h

theorem model_nontrivial : ¬ ∀ x y : NormalTree, x = y := by
  intro h
  exact normalTower_nontrivial (h (normalTower 0) (normalTower 1))

/-- Source, nontriviality, and an explicit injection of Nat into the same carrier. -/
theorem infinite_model :
    (∀ x y z : NormalTree,
      x = multiplication (multiplication y (multiplication x x))
        (multiplication (multiplication x z) z)) ∧
    (¬ ∀ x y : NormalTree, x = y) ∧
    (∀ {m n : Nat}, normalTower m = normalTower n → m = n) :=
  ⟨equation22446,model_nontrivial,normalTower_injective⟩

end submission.Equation22446Lineage

set_option autoImplicit false
set_option Elab.async false

namespace submission
abbrev CM := submission.Equation22446Lineage.NormalTree
noncomputable instance modelMagma : Magma CM := ⟨submission.Equation22446Lineage.multiplication⟩

namespace CM
theorem tower_injective (m n : Nat)
    (h : submission.Equation22446Lineage.normalTower m = submission.Equation22446Lineage.normalTower n) : m = n :=
  submission.Equation22446Lineage.normalTower_injective h
end CM

theorem source_law : EquationLHS CM := submission.Equation22446Lineage.equation22446
theorem nontrivial : ¬ EquationRHS CM := submission.Equation22446Lineage.model_nontrivial
end submission

theorem submission : Goal :=
  ⟨submission.CM,submission.modelMagma,submission.source_law,submission.nontrivial⟩

#print axioms submission
#print axioms submission.source_law
#print axioms submission.nontrivial
#print axioms submission.CM.tower_injective
#print axioms submission.Equation22446Lineage.infinite_model

prelude
import Init.Classical
import Init.Data.Nat.Lemmas
import Init.RCases
import ExportLineageSyntaxRelations
set_option Elab.async false
set_option autoImplicit false
set_option Elab.async false

namespace submission.Equation22446Guarded

 

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

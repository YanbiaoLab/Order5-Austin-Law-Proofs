prelude
import Init.Classical
import Init.Data.Nat.Lemmas
import Init.RCases
import ExportLineageSyntaxEvaluation
set_option Elab.async false
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

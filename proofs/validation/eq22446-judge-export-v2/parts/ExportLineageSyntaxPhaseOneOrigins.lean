prelude
import Init.Classical
import Init.Data.Nat.Lemmas
import Init.RCases
import ExportLineageSyntaxNonzeroRectangles
set_option Elab.async false
set_option autoImplicit false
set_option Elab.async false

namespace submission.Equation22446Lineage
open submission.Equation22446Guarded

 

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

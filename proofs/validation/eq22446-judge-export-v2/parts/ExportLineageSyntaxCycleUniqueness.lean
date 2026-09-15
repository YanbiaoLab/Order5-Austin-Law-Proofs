prelude
import Init.Classical
import Init.Data.Nat.Lemmas
import Init.RCases
import ExportLineageSyntaxNormalDiagonal
set_option Elab.async false
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

prelude
import Init.Classical
import Init.Data.Nat.Lemmas
import Init.RCases
import ExportLineageSyntaxDiagonalSupport
set_option Elab.async false
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

prelude
import Init.Classical
import Init.Data.Nat.Lemmas
import Init.RCases
import ExportLineageSyntaxPhaseTwoUniqueness
set_option Elab.async false
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

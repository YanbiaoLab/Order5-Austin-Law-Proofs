prelude
import LineageSyntax.CanonicalInduction
set_option autoImplicit false
set_option Elab.async false

namespace Equation22446Lineage
open Equation22446Guarded

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

#print axioms non_one_base_cases
#print axioms principal_non_one_unique
#print axioms principal_common_ancestry_unique
#print axioms principal_one_unique
#print axioms principal_unique
#print axioms guard_unique
end Equation22446Lineage

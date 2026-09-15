prelude
import LineageSyntax.CommonLineage
set_option autoImplicit false
set_option Elab.async false

namespace Equation22446Lineage
open Equation22446Guarded

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

#print axioms lineage_phase_two_preserved
#print axioms column_large_ancestor_false
#print axioms image_common_root_next_false
#print axioms column_common_root_false
end Equation22446Lineage

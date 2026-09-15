prelude
import LineageSyntax.PhaseOneLineageRoots
set_option autoImplicit false
set_option Elab.async false

namespace Equation22446Lineage
open Equation22446Guarded

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

#print axioms column_chain_completed_false
#print axioms phase_one_or_double_nonzero
#print axioms column_image_prev_false
#print axioms column_inverse_pair_chain_false
end Equation22446Lineage

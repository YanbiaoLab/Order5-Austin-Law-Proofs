prelude
import LineageSyntax.AncestralChainClosure
set_option autoImplicit false
set_option Elab.async false

namespace Equation22446Lineage
open Equation22446Guarded

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

#print axioms column_non_two_base_bound
#print axioms column_phase_one_base_non_two
#print axioms column_tall_head_chain_false
end Equation22446Lineage

prelude
import LineageSyntax.Decoder
set_option autoImplicit false
set_option Elab.async false

namespace Equation22446Lineage
open Equation22446Guarded

def leaf : T := .e .zero 0

def tower : Nat → T
  | 0 => S leaf
  | n+1 => P leaf (tower n)

theorem tower_ne_leaf (n : Nat) : tower n ≠ leaf := by
  cases n <;> intro h <;> cases h

theorem tower_ne_double_leaf (n : Nat) : tower n ≠ S (S leaf) := by
  cases n <;> intro h <;> cases h

theorem leaf_ne_next_tower (n : Nat) : leaf ≠ S (tower n) := by
  cases n <;> intro h <;> cases h

theorem image_tower_root (n : Nat) {p : T} (hi : Image p (tower n)) : p = S (tower n) := by
  induction n generalizing p with
  | zero =>
      have he := congrArg S (image_nonzero_output hi (by intro a b h; cases h))
      rw [cube] at he
      exact he.symm
  | succ n ih =>
      generalize he : tower (n+1) = q at hi
      cases hi with
      | square p => exact (cube p).symm
      | literal p t =>
          have h := (T.p.inj he).2.1
          cases h
      | transport hc hj =>
          rw [←(T.p.inj he).2.1,←(T.p.inj he).2.2] at hj
          exact False.elim (leaf_ne_next_tower n (ih hj))
      | inverseFollowup p =>
          have hp := congrArg S (T.p.inj he).2.1
          rw [cube] at hp
          have hz := (T.p.inj he).2.2
          rw [←hp] at hz
          exact False.elim (tower_ne_double_leaf n hz)
      | returnFollowup hj =>
          have hp := (T.p.inj he).2.1
          cases hp
      | cycleFollowup hs hj hk =>
          have hp := (T.p.inj he).2.1
          cases hp

theorem column_leaf_base {p : T} (hc : Column p leaf)
    (hn : ∀ a b, S p ≠ P a b) : p = S leaf := by
  generalize he : leaf = a at hc
  cases hc with
  | ancestry hl =>
      have hq := congrArg S he
      rw [cube] at hq
      have hp := lineage_non_phase_two hl (by intro u v h; rw [←hq] at h; cases h)
      rw [cube]
      exact hp
  | literal p y => cases he
  | inverseImage hi =>
      rw [←he] at hi
      rw [←he]
      exact S_injective (image_nonzero_output hi hn)

theorem tower_pair_no_guard (n : Nat) : ¬ ∃ o, Guard leaf (tower n) o := by
  rintro ⟨o,hg⟩
  cases hg with
  | rectangle hp hc hi =>
      have he := image_tower_root n hi
      have hh := column_leaf_base hc (by
        intro a b hh
        rw [he] at hh
        cases n <;> cases hh)
      exact tower_ne_leaf n (S_injective (he.symm.trans hh))
  | cycleReturn hp hi hj =>
      rename_i p
      have he := image_tower_root (n+1) hi
      have hs : nodes p < nodes (P leaf (tower n)) := by
        rcases hp with hp | hp
        · exact Nat.lt_of_le_of_lt (part_nodes hp) (pair_left .zero _ _)
        · exact Nat.lt_of_le_of_lt (part_nodes hp) (pair_right .zero _ _)
      rw [he,nodes_S] at hs
      exact Nat.lt_irrefl _ hs

theorem tower_normal (n : Nat) : Normal (tower n) := by
  induction n with
  | zero => trivial
  | succ n ih => exact ⟨True.intro,ih,tower_pair_no_guard n⟩

theorem tower_nodes (n : Nat) : nodes (tower n) = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (0 + nodes (tower n)) + 1 = n + 1
      rw [Nat.zero_add,ih]

def normalTower (n : Nat) : NormalTree := ⟨tower n,tower_normal n⟩

theorem normalTower_injective {m n : Nat} (h : normalTower m = normalTower n) : m = n := by
  have hn := congrArg (fun t : NormalTree => nodes t.val) h
  change nodes (tower m) = nodes (tower n) at hn
  rwa [tower_nodes,tower_nodes] at hn

#print axioms tower_ne_leaf
#print axioms tower_ne_double_leaf
#print axioms leaf_ne_next_tower
#print axioms image_tower_root
#print axioms column_leaf_base
#print axioms tower_pair_no_guard
#print axioms tower_normal
#print axioms tower_nodes
#print axioms normalTower_injective
end Equation22446Lineage

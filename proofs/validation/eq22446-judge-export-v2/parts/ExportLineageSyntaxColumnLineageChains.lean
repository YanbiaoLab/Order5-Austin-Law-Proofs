prelude
import Init.Classical
import Init.Data.Nat.Lemmas
import Init.RCases
import ExportLineageSyntaxCanonicalColumnTools
set_option Elab.async false
set_option autoImplicit false
set_option Elab.async false

namespace submission.Equation22446Lineage
open submission.Equation22446Guarded

theorem column_two_cycle_false {u q : T} (hc : Column u q) (hd : Column q u) : False := by
  cases hc with
  | ancestry hl =>
      cases hl with
      | refl => exact lineage_successor_column_false (p := S (S u)) (.refl _) (by simpa only [cube] using hd)
      | @step u r t hl hi =>
          simp only [cube] at hd
          have hs := column_non_two_base_bound hd (by intro x y h; cases h)
          simp only [nodes_S] at hs
          exact Nat.not_lt_of_ge hs (Nat.lt_of_le_of_lt (lineage_nodes hl) (pair_left .zero r t))
  | literal u y =>
      have hs := column_non_two_base_bound hd (by intro x y h; cases h)
      have hb := pair_right .zero y (S u)
      rw [nodes_S] at hb
      exact Nat.not_lt_of_ge hs hb
  | inverseImage hi => exact column_image_next_false hd hi

theorem column_chain_lineage_false {u q r : T} (hl : Lineage u r)
    (hc : Column u q) (hd : Column q r) : False := by
  cases hl with
  | refl => exact column_two_cycle_false hc hd
  | @step u x y hl hi =>
      rcases column_phase_two_base_shape hd ⟨x,y,rfl⟩ with ⟨a,b,hq⟩ | hq
      · rw [hq] at hd
        have he := column_zero_to_two hd
        have hq' : q = S (S (S (P x y))) := by rw [hq,he,cube]
        rw [hq'] at hc
        exact lineage_successor_column_false (.step hl hi) hc
      · obtain ⟨a,b,hq⟩ := hq
        have hj := column_two_value_inverse hd ⟨x,y,rfl⟩
        have hs := image_phase_two_strict hj ⟨x,y,rfl⟩ ⟨a,b,by rw [hq]; rfl⟩
        simp only [nodes_S] at hs
        have hqu := column_phase_two_bound hc a b hq
        have hur := lineage_nodes (Lineage.step hl hi)
        simp only [nodes_S] at hur
        exact Nat.not_lt_of_ge (Nat.le_trans hqu hur) hs

theorem common_root_successor_tail_false {r y u : T}
    (hl : Lineage r (S (S (P y (S u))))) (hu : Lineage r u) : False := by
  cases hl with
  | refl =>
      have hs := lineage_nodes hu
      simp only [nodes_S] at hs
      have hb := pair_right .zero y (S u)
      rw [nodes_S] at hb
      exact Nat.not_lt_of_ge hs hb
  | step hl hi => exact image_common_root_next_false hi _ u rfl hl hu

end submission.Equation22446Lineage

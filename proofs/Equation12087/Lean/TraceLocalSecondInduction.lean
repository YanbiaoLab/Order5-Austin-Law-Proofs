prelude
import TraceSecondDoubleGrowth
set_option autoImplicit false

namespace Austin12087Trace
open T

def NormalFirstBelow (n : Nat) : Prop := ∀ u q k : T, NF u → NF q → NF k →
  ht u < n → ht q < n → ht k < n →
  (inverse k (mul (mul u (mul q (mul u k))) q)).bind (inverse u) = none

def NormalSecondBelow (n : Nat) : Prop := ∀ u a k : T, NF u → NF a → NF k →
  ht u < n → ht a < n → ht k < n →
  inverse (mul (mul a (mul (mul u a) k)) (mul a k)) u = none

theorem normal_first_below_of_second_below {n : Nat} (hs : NormalSecondBelow n) :
    NormalFirstBelow n := by
  have main : ∀ m, ∀ u q k : T, NF u → NF q → NF k → ht q = m →
      ht u < n → ht q < n → ht k < n →
      (inverse k (mul (mul u (mul q (mul u k))) q)).bind (inverse u) = none := by
    intro m
    induction m using Nat.strongRecOn with
    | ind m ih =>
      intro u q k hu hq hk hqm hun hqn hkn
      by_cases hsize : sz q ≤ sz k
      · exact normal_first_larger_k_query_absent u q k hu hk hsize
      · have hneq : q ≠ k := by intro heq; rw [heq] at hsize; exact hsize (Nat.le_refl _)
        cases h₁ : inverse k (mul (mul u (mul q (mul u k))) q) with
        | none => rfl
        | some V =>
          cases h₂ : inverse u V with
          | none => exact h₂
          | some y =>
            have hf := inverse_sound h₁
            have hy := inverse_sound h₂
            rw [←hy] at hf
            let a := mul u (mul q (mul u k))
            let w := mul (mul y u) k
            obtain ⟨j,h,hna,hnj,hbc,hqc,hgq,haj,had,hwh,hvq,huq,hwq,hl⟩ :=
              normal_first_larger_q_trace hu hq hk hf hneq (by omega)
            change NF a at hna
            change mul (mul u a) j = q at hgq
            change mul a j = mul u k at haj
            change ht w < ht q at hwq
            change q = c a w h (mul u a) j at hqc
            have hanc := nf_code_key_height_gap (hqc ▸ hq)
            rw [←hqc] at hanc
            have hjq := (origin_height hl.2.2.1).2
            have hnw := (nf_code_actual (hqc ▸ hq)).2.1
            have hnV := nf_inverse hk hnw (inverse_complete (mul y u) k)
            have hny := nf_inverse hu hnV (inverse_complete y u)
            have bounds := common_column_height_bounds
              (show mul (mul y u) k = w from rfl) (show mul u k = mul u k from rfl)
            have hkq : ht k < ht q := by omega
            have hsrc := normal_source_of_lower_queries hu hny hk
              (by
                intro u' q' k' hu' hq' hk' hus hqs hks
                exact ih (ht q') (by omega) u' q' k' hu' hq' hk' rfl
                  (by omega) (by omega) (by omega))
              (by
                intro u' a' k' hu' ha' hk' hus has hks
                exact hs u' a' k' hu' ha' hk' (by omega) (by omega) (by omega))
            change u = mul y (mul w (mul u k)) at hsrc
            have hi := inverse_complete y (mul w (mul u k))
            rw [←hsrc] at hi
            have hwa : mul a q = w := hf.symm
            have hquery := hs u a j hu hna hnj (by omega) (by omega) (by omega)
            rw [hgq,haj,hwa,hi] at hquery
            cases hquery
  intro u q k hu hq hk hun hqn hkn
  exact main (ht q) u q k hu hq hk rfl hun hqn hkn

theorem normal_source_of_second_below {x y z : T}
    (hx : NF x) (hy : NF y) (hz : NF z)
    (hs : NormalSecondBelow (max (ht x) (ht z))) : Source12087 x y z := by
  exact normal_source_of_lower_queries hx hy hz (normal_first_below_of_second_below hs) hs

end Austin12087Trace
#print axioms Austin12087Trace.normal_first_below_of_second_below
#print axioms Austin12087Trace.normal_source_of_second_below

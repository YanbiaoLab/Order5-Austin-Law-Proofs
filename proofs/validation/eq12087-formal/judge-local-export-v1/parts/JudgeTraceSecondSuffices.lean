prelude
import Init.Data.Option.Lemmas
import Init.Omega
import Init.RCases
import Init.WFTactics
import JudgeTraceLowerQuerySource
set_option Elab.async false
/- Checked module: TraceSecondSuffices -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_first_of_second (hs : NormalSecondCycleAbsent) : NormalFirstCycleAbsent := by
  have main : ∀ n, ∀ u q k : T, NF u → NF q → NF k → ht q = n →
      (inverse k (mul (mul u (mul q (mul u k))) q)).bind (inverse u) = none := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro u q k hu hq hk hqn
      by_cases hsize : sz q ≤ sz k
      · exact normal_first_larger_k_query_absent u q k hu hk hsize
      · have hne : q ≠ k := by intro heq; rw [heq] at hsize; exact hsize (Nat.le_refl _)
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
              normal_first_larger_q_trace hu hq hk hf hne (by omega)
            change NF a at hna
            change mul (mul u a) j = q at hgq
            change mul a j = mul u k at haj
            change ht w < ht q at hwq
            change q = c a w h (mul u a) j at hqc
            have hnw := (nf_code_actual (hqc ▸ hq)).2.1
            have hnV := nf_inverse hk hnw (inverse_complete (mul y u) k)
            have hny := nf_inverse hu hnV (inverse_complete y u)
            have bounds := common_column_height_bounds
              (show mul (mul y u) k = w from rfl) (show mul u k = mul u k from rfl)
            have hkq : ht k < ht q := by omega
            have hsrc := normal_source_of_lower_queries hu hny hk
              (by
                intro u' q' k' hu' hq' hk' _ hqsmall _
                exact ih (ht q') (by omega) u' q' k' hu' hq' hk' rfl)
              (by
                intro u' a' k' hu' ha' hk' _ _ _
                exact hs u' a' k' hu' ha' hk')
            change u = mul y (mul w (mul u k)) at hsrc
            have hi := inverse_complete y (mul w (mul u k))
            rw [←hsrc] at hi
            have hwa : mul a q = w := hf.symm
            have hquery := hs u a j hu hna hnj
            rw [hgq,haj,hwa,hi] at hquery
            cases hquery
  intro u q k hu hq hk
  exact main (ht q) u q k hu hq hk rfl

theorem normal_source_of_second (hs : NormalSecondCycleAbsent)
    {x y z : T} (hx : NF x) (hy : NF y) (hz : NF z) : Source12087 x y z := by
  exact nf_source_of_normal_queries (normal_first_of_second hs) hs x y z hx hy hz

theorem normal_law_of_second_query_absence (hs : NormalSecondCycleAbsent) :
    ∀ x y z : NormalTree,
      x = normalMul y (normalMul (normalMul (normalMul y x) z) (normalMul x z)) := by
  exact normal_law_of_normal_queries (normal_first_of_second hs) hs

end submission.Austin12087Trace

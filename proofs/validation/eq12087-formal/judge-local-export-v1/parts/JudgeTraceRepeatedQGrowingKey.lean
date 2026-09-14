prelude
import Init.Data.Option.Lemmas
import Init.Omega
import Init.RCases
import Init.WFTactics
import JudgeTraceRepeatedQDescendingHead
set_option Elab.async false
/- Checked module: TraceRepeatedQGrowingKey -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem transposed_product_ne_square (u a : T) : mul a u ≠ mul (mul u a) (mul u a) := by
  intro he
  have hs : ht (mul (mul u a) (mul u a)) = ht (mul u a) + 1 := by rw [mul_square]; rfl
  rcases mul_height_growth_or_return u a with hg | ⟨x,z,l,r,hac,hgx⟩
  · have hw := mul_height_upper a u
    have hh := congrArg ht he
    omega
  · have hua : ht u < ht a := by rw [hac]; simp only [ht]; omega
    have hga : ht (mul u a) < ht a := by rw [hgx,hac]; simp only [ht]; omega
    have hw := mul_height_growth_of_left_ge (a:=a) (b:=u) (by omega)
    have hh := congrArg ht he
    omega

theorem repeated_q_target_ne_a (u a : T) : mul (mul u a) u ≠ a := by
  intro he
  have hh := no_cross_two_cycle (mul u a) u
  rw [he] at hh
  exact hh rfl

theorem normal_repeated_q_growing_key {u a : T} (hu : NF u) (ha : NF a) (hne : u ≠ a) :
    let g := mul u a
    let D := mul (mul a u) u
    let b := mul g u
    let A := mul D b
    ht (mul g A) = max (ht g) (ht A) + 1 ∧
      ht u ≤ max (ht g) (ht A) ∧ ht a ≤ max (ht g) (ht A) := by
  let g := mul u a
  let w := mul a u
  let D := mul w u
  let b := mul g u
  let A := mul D b
  have hnb : NF b := nf_mul (nf_mul hu ha) hu
  have hne' : D ≠ b := by
    intro heq
    have hwg := right_injective _ _ u heq
    exact hne (mul_commutative_only_equal hwg.symm)
  change ht (mul g A) = max (ht g) (ht A) + 1 ∧
    ht u ≤ max (ht g) (ht A) ∧ ht a ≤ max (ht g) (ht A)
  rcases nf_mul_height_key_gap (a:=D) hnb with hAg | hAr
  · change ht A = max (ht D) (ht b) + 1 at hAg
    have hoA := mul_origin_of_right_height_le (a:=D) (b:=b) (by change ht b ≤ ht A; omega)
    change origin A = some (D,b) at hoA
    have hF : ht (mul g A) = max (ht g) (ht A) + 1 := by
      by_cases hh : ht (mul g A) < ht A
      · have hret := return_from_column_product
          (show mul w u = D from rfl) (show mul g u = b from rfl)
          (show mul D b = A from rfl) hoA hne' hh
        exact False.elim (transposed_product_ne_square u a hret.2.2.symm)
      · exact mul_height_growth_of_right_le (by omega)
    have hub : ht u < ht A ∧ ht a < ht A := by
      rcases mul_height_growth_or_return a u with hwg | ⟨x,z,l,r,huc,_⟩
      · change ht w = max (ht a) (ht u) + 1 at hwg
        have hDg := mul_height_growth_of_left_ge (a:=w) (b:=u) (by omega)
        change ht D = max (ht w) (ht u) + 1 at hDg
        omega
      · have hau : ht a < ht u := by rw [huc]; simp only [ht]; omega
        have hgg := mul_height_growth_of_left_ge (a:=u) (b:=a) (by omega)
        change ht g = max (ht u) (ht a) + 1 at hgg
        have hbg := mul_height_growth_of_left_ge (a:=g) (b:=u) (by omega)
        change ht b = max (ht g) (ht u) + 1 at hbg
        omega
    exact ⟨hF,by omega,by omega⟩
  · change ht D + 3 ≤ ht b ∧ ht A + 2 ≤ ht b at hAr
    have hg := mul_height_upper u a
    change ht g ≤ max (ht u) (ht a) + 1 at hg
    have hb := mul_height_upper g u
    change ht b ≤ max (ht g) (ht u) + 1 at hb
    have hau : ht a < ht u := by
      rcases mul_height_growth_or_return a u with hwg | ⟨x,z,l,r,huc,_⟩
      · change ht w = max (ht a) (ht u) + 1 at hwg
        have hDg := mul_height_growth_of_left_ge (a:=w) (b:=u) (by omega)
        change ht D = max (ht w) (ht u) + 1 at hDg
        omega
      · rw [huc]; simp only [ht]; omega
    have hgg := mul_height_growth_of_left_ge (a:=u) (b:=a) (by omega)
    change ht g = max (ht u) (ht a) + 1 at hgg
    have hF := mul_height_growth_of_left_ge (a:=g) (b:=A) (by omega)
    exact ⟨hF,by omega,by omega⟩

end submission.Austin12087Trace

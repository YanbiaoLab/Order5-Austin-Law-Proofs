prelude
import Init.Data.Option.Lemmas
import Init.Omega
import Init.RCases
import Init.WFTactics
import JudgeTraceSameKeyHighGClosed
set_option Elab.async false
/- Checked module: TraceSameKeyHighColumnKeys -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_same_key_high_column_keys {a g v r s : T}
    (hnv : NF v)
    (hl : ReturnLadder (mul a a) (mul a v) v g a r s)
    (hgr : ht g < ht r) (he : ht (mul a v) < ht v)
    (hgv : ht g < ht v) (hvs : ht v < ht s) :
    mul (mul a a) g = a ∧
    ∃ t j, ReturnLadder a (mul (mul a v) a) a v g t j ∧
      ht v < ht t ∧ ht t < ht r ∧ mul g t = s := by
  have havGap := nf_mul_height_key_gap (a:=a) hnv
  have hav : ht a + 3 ≤ ht v := by rcases havGap with hh | hh <;> omega
  obtain ⟨t,hl₁,htr⟩ := return_ladder_step hl hgr hvs
  have hsHeight := mul_height_growth_of_right_le (a:=g) (b:=t) (by
    rw [hl₁.2.1]; exact Nat.le_of_lt (origin_height hl₁.2.2.1).2)
  rw [hl₁.2.1] at hsHeight
  have hnt := (nf_origin hl₁.1 hl₁.2.2.1).2
  have hvGap := nf_mul_height_key_gap (a:=mul (mul a a) g) hnt
  rw [hl₁.2.2.2.2] at hvGap
  have hvt : ht v < ht t := by rcases hvGap with hh | hh <;> omega
  obtain ⟨j,hl₂,_⟩ := return_ladder_step hl₁ (by omega) (by omega)
  obtain ⟨z,l,b,hvc⟩ := mul_return_of_height_lt (a:=a) (b:=v) he
  have hBa := normal_ladder_first_key_at_max hvc hl₂ hvt (by omega) (by omega)
  refine ⟨hBa,t,j,?_,hvt,htr,hl₁.2.1⟩
  rw [hBa] at hl₂
  exact hl₂

theorem normal_second_same_key_high_column_frontier {u a k y r s : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hs : NormalSecondBelow (ht k))
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u)
    (hvr : ht (mul a k) < ht k)
    (he : ht (mul a (mul a k)) < ht (mul a k))
    (haw : a = mul a (mul (mul u a) k))
    (hl : ReturnLadder (mul a a) (mul a (mul a k)) (mul a k) (mul u a) a r s)
    (hgr : ht (mul u a) < ht r) (hrk : ht r < ht k)
    (hvs : ht (mul a k) < ht s) :
    mul (mul a a) (mul u a) = a ∧ mul a (mul a k) ≠ a := by
  have he' : ht (mul (mul a (mul (mul u a) k)) (mul a k)) < ht (mul a k) := by
    rw [← haw]; exact he
  have hgv := normal_second_same_key_g_below_v hu ha hk hf hvr he' haw
  obtain ⟨hB,t,j,hl₂,hvt,htr,hst⟩ := normal_same_key_high_column_keys (nf_mul ha hk) hl hgr he hgv hvs
  refine ⟨hB,?_⟩
  intro hD
  have hbounds := normal_second_query_k_dominates hu ha hk hf
  have hsmall : mul y (mul (mul a (mul (mul u a) t)) (mul a t)) = u := by
    rw [hst,hl₂.2.2.2.1]
    rw [hD] at hl
    rw [hl.2.2.2.2]
    rw [← haw] at hf
    exact hf
  have hquery := hs u a t hu ha hl₂.1 hbounds.1 hbounds.2 (by omega)
  have hi := inverse_complete y (mul (mul a (mul (mul u a) t)) (mul a t))
  rw [hsmall,hquery] at hi
  cases hi

end submission.Austin12087Trace

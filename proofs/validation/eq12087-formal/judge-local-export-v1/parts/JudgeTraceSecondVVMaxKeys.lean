prelude
import Init.Data.Option.Lemmas
import Init.Omega
import Init.RCases
import Init.WFTactics
import JudgeTraceSecondVGMaxClosed
set_option Elab.async false
/- Checked module: TraceSecondVVMaxKeys -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_low_ladder_v_max_keys {a g v w t j : T}
    (hnv : NF v)
    (hl : ReturnLadder (mul (mul a w) g) (mul (mul a v) w) w v g t j)
    (hvt : ht v < ht t) (hwv : ht w < ht v) (hgv : ht g ≤ ht v) :
    mul (mul a w) g = a ∧ ht (mul a v) < ht v := by
  let B := mul (mul a w) g
  let D := mul a v
  let C := mul D w
  change ReturnLadder B C w v g t j at hl
  change B = a ∧ ht D < ht v
  have hCv : ht C < ht v := by
    by_cases hh : ht C < ht v
    · exact hh
    · exact False.elim (return_ladder_second_dominant_impossible hl hvt (by omega) (by omega) (by omega))
  have hD := inverse_height_strict (inverse_complete D w)
  change ht D < max (ht w) (ht C) at hD
  have hDv : ht D < ht v := by omega
  obtain ⟨z,l,r,hvc⟩ := mul_return_of_height_lt (a:=a) (b:=v) hDv
  have htHeight := mul_height_growth_of_right_le (a:=w) (b:=j) (by
    rw [hl.2.1]; exact Nat.le_of_lt (origin_height hl.2.2.1).2)
  rw [hl.2.1] at htHeight
  have hnj := (nf_origin hl.1 hl.2.2.1).2
  have hgGap := nf_mul_height_key_gap (a:=C) hnj
  rw [hl.2.2.2.2] at hgGap
  have hgj : ht g < ht j := by rcases hgGap with hh | hh <;> omega
  have hBa : B = a := by
    by_cases hh : B = a
    · exact hh
    · have hF := mul_height_off_return_key (a:=B) hvc hh
      obtain ⟨m,hl',_⟩ := return_ladder_step hl hvt (by omega)
      exact False.elim (return_ladder_second_dominant_impossible hl' hgj (by omega) (by omega) (by omega))
  exact ⟨hBa,hDv⟩

theorem normal_second_v_growing_middle_key_frontier {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hs : NormalSecondBelow (ht k))
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u)
    (hvr : ht (mul a k) < ht k)
    (hmid : ht (mul a k) ≤ ht (mul (mul a (mul (mul u a) k)) (mul a k))) :
    let g := mul u a
    let v := mul a k
    let w := mul a (mul g k)
    mul (mul a w) g = a ∧ mul a v ≠ a ∧ ht (mul a v) < ht v := by
  obtain ⟨hwv,hgv⟩ := normal_second_v_growing_middle_frontier hu ha hk hs hf hvr hmid
  obtain ⟨r,s,t,j,_,_,hnt,_,_,_,hws,hst,hvt,_,_,_,_,hv2,_,_,_,_,_,_,hl⟩ :=
    normal_second_v_growing_middle_ladder hu ha hk hf hvr hmid
  obtain ⟨hBa,hDv⟩ := normal_low_ladder_v_max_keys (nf_mul ha hk) hl (by omega) hwv hgv
  have hbounds := normal_second_query_k_dominates hu ha hk hf
  refine ⟨hBa,?_,hDv⟩
  intro hDa
  exact normal_second_v_low_equal_keys_descent_impossible hu ha hnt hs hbounds.1 hbounds.2
    (by omega) hf hws hvt hst hBa hDa

end submission.Austin12087Trace

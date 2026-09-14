prelude
import Init.Data.Option.Lemmas
import Init.Omega
import Init.RCases
import Init.WFTactics
import JudgeTraceSquareKeyReturnGeometry
set_option Elab.async false
/- Checked module: TraceSameKeyHighColumnOuter -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_same_key_high_column_outer_return {u a v r s y : T}
    (hu : NF u) (ha : NF a) (hnv : NF v)
    (hl : ReturnLadder (mul a a) (mul a v) v (mul u a) a r s)
    (hgr : ht (mul u a) < ht r) (he : ht (mul a v) < ht v)
    (hgv : ht (mul u a) < ht v) (hvs : ht v < ht s)
    (hf : mul y (mul a v) = u) :
    ht (mul u a) + 1 ≤ ht (mul a v) ∧ ht y + 3 ≤ ht (mul a v) := by
  let e := mul a v
  let g := mul u a
  change ReturnLadder (mul a a) e v g a r s at hl
  change ht g < ht r at hgr
  change ht e < ht v at he
  change ht g < ht v at hgv
  change mul y e = u at hf
  change ht g + 1 ≤ ht e ∧ ht y + 3 ≤ ht e
  obtain ⟨hB,t,j,hl₂,hvt,_,_⟩ := normal_same_key_high_column_keys hnv hl hgr he hgv hvs
  rcases normal_square_key_outer_alternatives hu ha (nf_mul ha hnv) hB hf with ⟨hae,_,hue⟩ | hret
  · change ht u = ht e + 1 at hue
    have heGap := nf_mul_height_key_gap (a:=a) hnv
    change ht e = max (ht a) (ht v) + 1 ∨ (ht a + 3 ≤ ht v ∧ ht e + 2 ≤ ht v) at heGap
    have hav : ht a + 3 ≤ ht v := by rcases heGap with hh | hh <;> omega
    have haGap := nf_mul_height_key_gap (a:=a) (nf_mul ha hnv)
    change ht (mul a e) = max (ht a) (ht e) + 1 ∨ (ht a + 3 ≤ ht e ∧ ht (mul a e) + 2 ≤ ht e) at haGap
    rw [hae] at haGap
    have hae3 : ht a + 3 ≤ ht e := by rcases haGap with hh | hh <;> omega
    have hgHeight := mul_height_growth_of_left_ge (a:=u) (b:=a) (by omega)
    change ht g = max (ht u) (ht a) + 1 at hgHeight
    have hge : ht g = ht e + 2 := by omega
    have htHeight := mul_height_growth_of_right_le (a:=a) (b:=j) (by
      rw [hl₂.2.1]; exact Nat.le_of_lt (origin_height hl₂.2.2.1).2)
    rw [hl₂.2.1] at htHeight
    have htGap := nf_mul_height_key_gap (a:=a) hl₂.1
    rw [hl₂.2.2.2.1] at htGap
    have hvj : ht v < ht j := by rcases htGap with hh | hh <;> omega
    obtain ⟨l,hl₃,_⟩ := return_ladder_step hl₂ hvt (by omega)
    change ReturnLadder (mul e a) e v g a j l at hl₃
    have hua : u ≠ a := by intro hh; have hh' := congrArg ht hh; omega
    exact False.elim (nonfixed_same_key_ladder_impossible ha (nf_mul ha hnv) hae rfl hf rfl hua
      (by change ht e + 1 < ht g; omega) (by change ht g ≤ ht v; omega) hl₃
      (by change ht g < ht j; omega))
  · exact hret

end submission.Austin12087Trace

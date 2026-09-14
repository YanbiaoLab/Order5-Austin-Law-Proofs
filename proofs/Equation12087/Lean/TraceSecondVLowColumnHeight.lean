prelude
import TraceSecondVLowKeyDescent
set_option autoImplicit false

namespace Austin12087Trace
open T

theorem normal_low_growing_middle_column_height {u a v w r s t y : T}
    (hu : NF u) (ha : NF a) (hnv : NF v) (hnw : NF w) (hnr : NF r) (hns : NF s) (hnt : NF t)
    (hf : mul y (mul w v) = u)
    (hws : mul (mul a v) s = w) (hrs : mul v s = r)
    (hvt : mul (mul (mul a w) (mul u a)) t = v) (hst : mul (mul u a) t = s)
    (hrc : r = c (mul a w) (mul u a) t v s)
    (hwr : ht w < ht r) (hvs : ht v < ht s)
    (hmid : ht v ≤ ht (mul w v)) (houter : ht u < ht (mul w v)) :
    ht (mul u a) < ht t ∧ ht t + 1 = ht s ∧ ht r = ht s + 1 ∧
      ht v + 2 ≤ ht t ∧ ht (mul (mul a w) (mul u a)) + 3 ≤ ht t ∧
      ht w + 2 ≤ ht s ∧ ht (mul a v) + 3 ≤ ht s := by
  let g := mul u a
  let A := mul a w
  let B := mul A g
  let D := mul a v
  let e := mul w v
  change mul y e = u at hf
  change mul D s = w at hws
  change mul B t = v at hvt
  change mul g t = s at hst
  change r = c A g t v s at hrc
  change ht v ≤ ht e at hmid
  change ht u < ht e at houter
  have hrOrigin : origin r = some (v,s) := by rw [hrc]; rfl
  have hrGrow := mul_height_growth_of_right_le (a:=v) (b:=s) (by
    rw [hrs]; exact Nat.le_of_lt (origin_height hrOrigin).2)
  rw [hrs] at hrGrow
  have hrh : ht r = ht s + 1 := by omega
  have hrGap := nf_code_height_gap (hrc ▸ hnr)
  have hrKey := nf_code_key_height_gap (hrc ▸ hnr)
  rw [←hrc] at hrGap hrKey
  have hwGap := nf_mul_height_key_gap (a:=D) hns
  rw [hws] at hwGap
  have hw2 : ht w + 2 ≤ ht s := by rcases hwGap with hh | hh <;> omega
  have hD3 : ht D + 3 ≤ ht s := by rcases hwGap with hh | hh <;> omega
  have haHeight := inverse_height_strict (inverse_complete a w)
  change ht a < max (ht w) (ht A) at haHeight
  have ha3 : ht a + 3 ≤ ht s := by omega
  have heGrow := mul_height_growth_of_right_le (a:=w) (b:=v) hmid
  change ht e = max (ht w) (ht v) + 1 at heGrow
  have heNF : NF e := nf_mul hnw hnv
  have huGap := nf_mul_height_key_gap (a:=y) heNF
  rw [hf] at huGap
  have hu2 : ht u + 2 ≤ ht e := by rcases huGap with hh | hh <;> omega
  have hgUpper := mul_height_upper u a
  change ht g ≤ max (ht u) (ht a) + 1 at hgUpper
  have hg2 : ht g + 2 ≤ ht s := by
    by_cases hh : ht g + 2 ≤ ht s
    · exact hh
    · have hvh : ht v + 1 = ht s := by omega
      have hut : ht u + 1 = ht g := by omega
      have hvGap := nf_mul_height_key_gap (a:=B) hnt
      rw [hvt] at hvGap
      have htv : ht t < ht v := by rcases hvGap with hp | hp <;> omega
      have hoe := mul_origin_of_right_height_le (a:=w) (b:=v) hmid
      change origin e = some (w,v) at hoe
      obtain ⟨j,_,_,_,_,hvj,hjGap,_⟩ := nf_return_origin_trace heNF hoe hf houter
      change ht j + 2 ≤ ht e at hjGap
      have hov := mul_origin_of_right_height_le (a:=u) (b:=j) (by rw [hvj]; omega)
      rw [hvj] at hov
      have hov' := mul_origin_of_right_height_le (a:=B) (b:=t) (by rw [hvt]; omega)
      rw [hvt] at hov'
      have huB : u = B := (Prod.mk.inj (Option.some.inj (hov.symm.trans hov'))).1
      have hgNF : NF g := nf_mul hu ha
      have hBGap := nf_mul_height_key_gap (a:=A) hgNF
      change ht B = max (ht A) (ht g) + 1 ∨ (ht A + 3 ≤ ht g ∧ ht B + 2 ≤ ht g) at hBGap
      rw [←huB] at hBGap
      rcases hBGap with hp | hp <;> omega
  have hsGrow := mul_height_growth_of_right_le (a:=g) (b:=t) (by rw [hst]; omega)
  rw [hst] at hsGrow
  have hts : ht t + 1 = ht s := by omega
  have hvGap := nf_mul_height_key_gap (a:=B) hnt
  rw [hvt] at hvGap
  have hv2 : ht v + 2 ≤ ht t := by rcases hvGap with hh | hh <;> omega
  have hB3 : ht B + 3 ≤ ht t := by rcases hvGap with hh | hh <;> omega
  exact ⟨by change ht g < ht t; omega,hts,hrh,hv2,hB3,hw2,hD3⟩

end Austin12087Trace
#print axioms Austin12087Trace.normal_low_growing_middle_column_height

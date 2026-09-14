prelude
import Init.Data.Option.Lemmas
import Init.Omega
import Init.RCases
import Init.WFTactics
import JudgeTraceSecondEqualInputHead
set_option Elab.async false
/- Checked module: TraceEqualCodeGeometry -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_equal_code_geometry {u q h z : T}
    (hq : NF q)
    (hn : NF (c (mul u q) u h (mul (mul u u) q) z))
    (hsmall : ht q < ht (c (mul u q) u h (mul (mul u u) q) z))
    (hbz : ht (mul (mul u u) q) < ht z) :
    ht u + 3 ≤ ht z ∧ ht (mul u q) + 2 ≤ ht z ∧
      ht h + 1 = ht z ∧ ht (mul (mul u u) q) + 2 ≤ ht h ∧
      origin z = some (u,h) := by
  let b := mul (mul u u) q
  let w := mul u q
  let e := c w u h b z
  change NF e at hn
  change ht q < ht e at hsmall
  change ht b < ht z at hbz
  have hc := nf_code_actual hn
  have hgap := nf_code_height_gap hn
  have hkey := nf_code_key_height_gap hn
  change ht w + 2 ≤ ht e ∧ ht u + 2 ≤ ht e ∧ ht h + 2 ≤ ht e at hgap
  change ht w + 3 ≤ ht e at hkey
  have heact : mul b z = e := hc.2.2.2.2.2.1
  have heo : origin e = some (b,z) := rfl
  have heg := mul_height_growth_of_right_le (a:=b) (b:=z) (by
    rw [heact]
    exact Nat.le_of_lt (origin_height heo).2)
  rw [heact] at heg
  have hez : ht e = ht z + 1 := by omega
  have hw := nf_mul_height_key_gap (a:=u) hq
  change ht w = max (ht u) (ht q) + 1 ∨ (ht u + 3 ≤ ht q ∧ ht w + 2 ≤ ht q) at hw
  have hu3 : ht u + 3 ≤ ht z := by rcases hw with hw | hw <;> omega
  have hzh : mul u h = z := hc.2.2.2.2.2.2.2
  have hzg := mul_height_growth_of_right_le (a:=u) (b:=h) (by rw [hzh]; omega)
  rw [hzh] at hzg
  have hoz := mul_origin_of_right_height_le (a:=u) (b:=h) (by rw [hzh]; omega)
  rw [hzh] at hoz
  have hbh : mul (mul w u) h = b := hc.2.2.2.2.2.2.1
  have hb := nf_mul_height_key_gap (a:=mul w u) hc.2.2.1
  rw [hbh] at hb
  have hb2 : ht b + 2 ≤ ht h := by rcases hb with hb | hb <;> omega
  exact ⟨hu3,by change ht w + 2 ≤ ht z; omega,by omega,hb2,hoz⟩

end submission.Austin12087Trace

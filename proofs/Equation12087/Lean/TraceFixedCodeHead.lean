prelude
import TraceFixedRotation
set_option autoImplicit false

namespace Austin12087Trace
open T

theorem normal_fixed_code_head_order {u q h z : T}
    (hu : NF u) (hq : NF q)
    (hn : NF (c (mul u q) u h (mul (mul u u) q) z))
    (hsmall : ht q < ht (c (mul u q) u h (mul (mul u u) q) z))
    (hfixed : mul u (mul q z) = u) :
    ht (mul (mul u u) q) < ht z := by
  let A := mul u u
  let b := mul A q
  let w := mul u q
  let e := c w u h b z
  change NF e at hn
  change ht q < ht e at hsmall
  change ht b < ht z
  by_cases hh : ht b < ht z
  · exact hh
  · have hnc : NF (c w u h b z) := hn
    have hc := nf_code_actual hnc
    have hgap := nf_code_height_gap hnc
    change ht w + 2 ≤ ht e ∧ ht u + 2 ≤ ht e ∧ ht h + 2 ≤ ht e at hgap
    have heact : mul b z = e := hc.2.2.2.2.2.1
    have heo : origin e = some (b,z) := rfl
    have heg := mul_height_growth_of_right_le (a:=b) (b:=z) (by
      rw [heact]
      exact Nat.le_of_lt (origin_height heo).2)
    rw [heact] at heg
    have hbg := nf_mul_height_key_gap (a:=A) hq
    change ht b = max (ht A) (ht q) + 1 ∨ (ht A + 3 ≤ ht q ∧ ht b + 2 ≤ ht q) at hbg
    have hqb : ht q < ht b := by rcases hbg with hp | hp <;> omega
    have hob := mul_origin_of_right_height_le (a:=A) (b:=q) (by change ht q ≤ ht b; omega)
    change origin b = some (A,q) at hob
    have hbh : mul (mul w u) h = b := hc.2.2.2.2.2.2.1
    have hzh : mul u h = z := hc.2.2.2.2.2.2.2
    have hob' := mul_origin_of_right_height_le (a:=mul w u) (b:=h) (by rw [hbh]; omega)
    rw [hbh] at hob'
    have hp := Prod.mk.inj (Option.some.inj (hob'.symm.trans hob))
    have hwu : w = u := right_injective _ _ u hp.1
    have hright : mul u q = u := hwu
    rw [hp.2,hright] at hzh
    rw [← hzh] at hfixed
    exact False.elim (normal_fixed_rotation_impossible hu hq hright hfixed)

end Austin12087Trace
#print axioms Austin12087Trace.normal_fixed_code_head_order

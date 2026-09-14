prelude
import TraceSecondReturningQRepeated
set_option autoImplicit false

namespace Austin12087Trace
open T

theorem right_repeated_product_ne_transpose (a u : T) :
    mul (mul a u) u ≠ mul u a := by
  intro he
  let w := mul a u
  let g := mul u a
  change mul w u = g at he
  rcases mul_height_growth_or_return a u with hw | ⟨x,z,l,r,huc,hwx⟩
  · change ht w = max (ht a) (ht u) + 1 at hw
    have hD := mul_height_growth_of_left_ge (a:=w) (b:=u) (by omega)
    rw [he] at hD
    have hg := mul_height_upper u a
    change ht g ≤ max (ht u) (ht a) + 1 at hg
    omega
  · have hau : ht a < ht u := by rw [huc]; simp only [ht]; omega
    have hwu : ht w < ht u := by change ht (mul a u) < ht u; rw [hwx,huc]; simp only [ht]; omega
    have hg := mul_height_growth_of_left_ge (a:=u) (b:=a) (by omega)
    change ht g = max (ht u) (ht a) + 1 at hg
    have hog := mul_origin_of_right_height_le (a:=u) (b:=a) (by change ht a ≤ ht g; omega)
    change origin g = some (u,a) at hog
    have hog' := mul_origin_of_right_height_le (a:=w) (b:=u) (by rw [he]; omega)
    rw [he] at hog'
    have hwu' := (Prod.mk.inj (Option.some.inj (hog'.symm.trans hog))).1
    have hh := congrArg ht hwu'
    omega

theorem normal_repeated_q_product_ne_u {u a : T} (hu : NF u) (ha : NF a) :
    mul (mul (mul a u) u) (mul (mul u a) u) ≠ u := by
  intro he
  let w := mul a u
  let g := mul u a
  let D := mul w u
  let b := mul g u
  change mul D b = u at he
  have hnb : NF b := nf_mul (nf_mul hu ha) hu
  rcases nf_mul_height_key_gap (a:=a) hu with hw | hw
  · change ht w = max (ht a) (ht u) + 1 at hw
    have hD := mul_height_growth_of_left_ge (a:=w) (b:=u) (by omega)
    change ht D = max (ht w) (ht u) + 1 at hD
    have hg := mul_height_upper u a
    change ht g ≤ max (ht u) (ht a) + 1 at hg
    have hb := mul_height_upper g u
    change ht b ≤ max (ht g) (ht u) + 1 at hb
    have hA := mul_height_growth_of_left_ge (a:=D) (b:=b) (by omega)
    rw [he] at hA
    omega
  · change ht a + 3 ≤ ht u ∧ ht w + 2 ≤ ht u at hw
    have hg := mul_height_growth_of_left_ge (a:=u) (b:=a) (by omega)
    change ht g = max (ht u) (ht a) + 1 at hg
    have hb := mul_height_growth_of_left_ge (a:=g) (b:=u) (by omega)
    change ht b = max (ht g) (ht u) + 1 at hb
    have hob := mul_origin_of_right_height_le (a:=g) (b:=u) (by change ht u ≤ ht b; omega)
    change origin b = some (g,u) at hob
    have hkey := nf_mul_height_key_gap (a:=D) hnb
    rw [he] at hkey
    have hDsmall : ht D + 3 ≤ ht b := by rcases hkey with hh | hh <;> omega
    have hDr := nf_mul_height_key_gap (a:=w) hu
    change ht D = max (ht w) (ht u) + 1 ∨ (ht w + 3 ≤ ht u ∧ ht D + 2 ≤ ht u) at hDr
    have hDu : ht D < ht u := by rcases hDr with hh | hh <;> omega
    obtain ⟨za,la,ra,huc⟩ := mul_return_of_height_lt (a:=a) (b:=u) (by change ht w < ht u; omega)
    obtain ⟨zw,lw,rw,huc'⟩ := mul_return_of_height_lt (a:=w) (b:=u) hDu
    have hwa : w = a := (T.c.inj (huc'.symm.trans huc)).1
    have hDa : D = a := by change mul w u = a; rw [hwa]; exact hwa
    obtain ⟨r,_,_,_,_,hur,hrgap,_⟩ := nf_return_origin_trace hnb hob he (by omega)
    have hi := inverse_height_strict (inverse_complete u r)
    rw [hur] at hi
    omega

end Austin12087Trace
#print axioms Austin12087Trace.right_repeated_product_ne_transpose
#print axioms Austin12087Trace.normal_repeated_q_product_ne_u

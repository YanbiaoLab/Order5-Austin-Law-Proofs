prelude
import TraceRepeatedQProducts
set_option autoImplicit false

namespace Austin12087Trace
open T

theorem repeated_q_boundary_product_height {u a t : T}
    (hut : ht u + 3 ≤ ht t) (hat : ht a + 2 ≤ ht t)
    (hbt : ht (mul (mul u a) u) = ht t) :
    ht t < ht (mul (mul (mul a u) u) (mul (mul u a) u)) := by
  have hg := mul_height_upper u a
  have hb := mul_height_upper (mul u a) u
  have hau : ht u ≤ ht a := by omega
  have hw := mul_height_growth_of_left_ge (a:=a) (b:=u) hau
  have hD := mul_height_growth_of_left_ge (a:=mul a u) (b:=u) (by omega)
  have hA := mul_height_growth_of_left_ge (a:=mul (mul a u) u) (b:=mul (mul u a) u) (by omega)
  omega

theorem normal_repeated_q_tail_stops {u a t h s : T}
    (hu : NF u) (ha : NF a) (htn : NF t) (hhn : NF h) (hsn : NF s)
    (hat : mul u t = a) (hus : mul a s = u) (hhs : mul t s = h)
    (hbh : mul (mul (mul a u) u) h = mul (mul u a) u)
    (hut : ht u + 3 ≤ ht t) (hatgap : ht a + 2 ≤ ht t)
    (hth : ht t < ht h) : ht s ≤ ht t := by
  let w := mul a u
  let D := mul w u
  let b := mul (mul u a) u
  let A := mul D b
  change mul D h = b at hbh
  have hg := mul_height_upper u a
  have hb := mul_height_upper (mul u a) u
  change ht b ≤ max (ht (mul u a)) (ht u) + 1 at hb
  have hbt : ht b ≤ ht t := by omega
  by_cases hst : ht s ≤ ht t
  · exact hst
  · have hho := (distinct_outputs_height_origin hhs hus (by
      intro heq
      have hh := congrArg ht heq
      omega) (by omega)).1
    have hhg := mul_height_growth_of_right_le (a:=t) (b:=s) (by rw [hhs]; exact Nat.le_of_lt (origin_height hho).2)
    rw [hhs] at hhg
    obtain ⟨r,_,hnr,_,hAr,hsr,hrgap,_⟩ := nf_return_origin_trace hhn hho hbh (by omega)
    change mul A r = t at hAr
    change mul b r = s at hsr
    have hso := mul_origin_of_right_height_le (a:=b) (b:=r) (by rw [hsr]; omega)
    rw [hsr] at hso
    have hsg := mul_height_growth_of_right_le (a:=b) (b:=r) (by rw [hsr]; omega)
    rw [hsr] at hsg
    have htr : ht t < ht r := by
      by_cases hbr : ht b ≤ ht r
      · have htalt := nf_mul_height_key_gap (a:=A) hnr
        rw [hAr] at htalt
        rcases htalt with hh | hh <;> omega
      · have hbteq : ht b = ht t := by omega
        have hAb := repeated_q_boundary_product_height hut hatgap hbteq
        change ht t < ht A at hAb
        have hi := inverse_height_strict (inverse_complete A r)
        rw [hAr] at hi
        omega
    obtain ⟨j,_,hnj,_,hbj,hrj,hjgap,_⟩ := nf_return_origin_trace hsn hso hus (by omega)
    change mul w j = b at hbj
    have hro := mul_origin_of_right_height_le (a:=u) (b:=j) (by rw [hrj]; omega)
    rw [hrj] at hro
    have hrg := mul_height_growth_of_right_le (a:=u) (b:=j) (by rw [hrj]; omega)
    rw [hrj] at hrg
    have hl : ReturnLadder A w u t b r j := ⟨hnr,hrj,hro,hAr,hbj⟩
    obtain ⟨l,hl',_⟩ := return_ladder_step hl htr (by omega)
    obtain ⟨z,lt,rt,htc⟩ := mul_return_of_height_lt (a:=u) (b:=t) (by rw [hat]; omega)
    have hAu : A ≠ u := normal_repeated_q_product_ne_u hu ha
    have hAt := mul_height_off_return_key (a:=A) htc hAu
    have hbjret : ht b < ht j := by
      have hh := nf_mul_height_key_gap (a:=w) hnj
      rw [hbj] at hh
      rcases hh with hh | hh <;> omega
    exact False.elim (return_ladder_second_dominant_impossible hl' hbjret (by omega) (by omega) (by omega))

end Austin12087Trace
#print axioms Austin12087Trace.repeated_q_boundary_product_height
#print axioms Austin12087Trace.normal_repeated_q_tail_stops

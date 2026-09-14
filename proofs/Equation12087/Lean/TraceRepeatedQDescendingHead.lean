prelude
import TraceRepeatedQTailStop
set_option autoImplicit false

namespace Austin12087Trace
open T

theorem normal_repeated_q_descending_head {u a t h s : T}
    (hu : NF u) (ha : NF a) (htn : NF t) (hhn : NF h) (hsn : NF s)
    (hne : u ≠ a)
    (hat : mul u t = a) (hus : mul a s = u) (hhs : mul t s = h)
    (hbh : mul (mul (mul a u) u) h = mul (mul u a) u)
    (hut : ht u + 3 ≤ ht t) (hatgap : ht a + 2 ≤ ht t)
    (hth : ht t < ht h) :
    let g := mul u a
    let D := mul (mul a u) u
    let b := mul g u
    let A := mul D b
    ∃ r l, NF r ∧ NF l ∧
      h = c D b r t s ∧ t = c u a l A r ∧
      mul A r = t ∧ mul b r = s ∧ mul g l = A ∧ mul a l = r ∧
      origin r = some (a,l) ∧
      ht h = ht t + 1 ∧ ht r + 1 = ht t ∧ ht l + 1 = ht r ∧
      ht s + 2 ≤ ht r ∧ ht A + 2 ≤ ht l := by
  let g := mul u a
  let w := mul a u
  let D := mul w u
  let b := mul g u
  let A := mul D b
  change mul D h = b at hbh
  have hst := normal_repeated_q_tail_stops hu ha htn hhn hsn hat hus hhs hbh hut hatgap hth
  have hho := (distinct_outputs_height_origin hhs hus (by
    intro heq
    have hh := congrArg ht heq
    omega) (by omega)).1
  have hhg := mul_height_growth_of_right_le (a:=t) (b:=s) (by
    rw [hhs]
    exact Nat.le_of_lt (origin_height hho).2)
  rw [hhs] at hhg
  have hht : ht h = ht t + 1 := by omega
  have hg := mul_height_upper u a
  change ht g ≤ max (ht u) (ht a) + 1 at hg
  have hb := mul_height_upper g u
  change ht b ≤ max (ht g) (ht u) + 1 at hb
  have hbt : ht b ≤ ht t := by omega
  obtain ⟨r,hcode,hnr,_,hAr,hsr,hrgap,_⟩ := nf_return_origin_trace hhn hho hbh (by omega)
  change mul A r = t at hAr
  change mul b r = s at hsr
  have hbgap := nf_code_height_gap (hcode ▸ hhn)
  rw [← hcode] at hbgap
  have hbt' : ht b < ht t := by omega
  have hto := mul_origin_of_right_height_le (a:=A) (b:=r) (by rw [hAr]; omega)
  rw [hAr] at hto
  have htg := mul_height_growth_of_right_le (a:=A) (b:=r) (by rw [hAr]; omega)
  rw [hAr] at htg
  obtain ⟨l,tcode,hnl,_,hAl,hrl,hlgap,_⟩ := nf_return_origin_trace htn hto hat (by omega)
  change mul g l = A at hAl
  have hArlt : ht A < ht r := by
    by_cases hh : ht A < ht r
    · exact hh
    · have hoA := mul_origin_of_right_height_le (a:=g) (b:=l) (by rw [hAl]; omega)
      rw [hAl] at hoA
      have hoA' := mul_origin_of_right_height_le (a:=D) (b:=b) (by change ht b ≤ ht A; omega)
      change origin A = some (D,b) at hoA'
      have hDg := (Prod.mk.inj (Option.some.inj (hoA'.symm.trans hoA))).1
      exact False.elim (right_repeated_product_ne_transpose a u hDg)
  have hrt : ht r + 1 = ht t := by omega
  have hro := mul_origin_of_right_height_le (a:=a) (b:=l) (by rw [hrl]; omega)
  rw [hrl] at hro
  have hrg := mul_height_growth_of_right_le (a:=a) (b:=l) (by rw [hrl]; omega)
  rw [hrl] at hrg
  have hal : ht a < ht l := by
    by_cases hh : ht a < ht l
    · exact hh
    · have hDkey := nf_code_key_height_gap (hcode ▸ hhn)
      rw [← hcode] at hDkey
      have hwg := mul_height_growth_of_left_ge (a:=a) (b:=u) (by omega)
      change ht w = max (ht a) (ht u) + 1 at hwg
      have hDg := mul_height_growth_of_left_ge (a:=w) (b:=u) (by omega)
      change ht D = max (ht w) (ht u) + 1 at hDg
      exact False.elim (by omega)
  have hlr : ht l + 1 = ht r := by omega
  have hAret := nf_mul_height_key_gap (a:=g) hnl
  rw [hAl] at hAret
  have hA2 : ht A + 2 ≤ ht l := by rcases hAret with hh | hh <;> omega
  have hsrlt : ht s < ht r := by
    by_cases hh : ht s < ht r
    · exact hh
    · have hsg := mul_height_growth_of_right_le (a:=b) (b:=r) (by rw [hsr]; omega)
      rw [hsr] at hsg
      have hso := mul_origin_of_right_height_le (a:=b) (b:=r) (by rw [hsr]; omega)
      rw [hsr] at hso
      obtain ⟨j,_,_,_,_,hrj,hjgap,_⟩ := nf_return_origin_trace hsn hso hus (by omega)
      have hro' := mul_origin_of_right_height_le (a:=u) (b:=j) (by rw [hrj]; omega)
      rw [hrj] at hro'
      exact False.elim (hne (Prod.mk.inj (Option.some.inj (hro'.symm.trans hro))).1)
  have hsret := nf_mul_height_key_gap (a:=b) hnr
  rw [hsr] at hsret
  have hs2 : ht s + 2 ≤ ht r := by rcases hsret with hh | hh <;> omega
  exact ⟨r,l,hnr,hnl,hcode,tcode,hAr,hsr,hAl,hrl,hro,hht,hrt,hlr,hs2,hA2⟩

end Austin12087Trace
#print axioms Austin12087Trace.normal_repeated_q_descending_head

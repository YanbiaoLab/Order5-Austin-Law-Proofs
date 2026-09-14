prelude
import TraceRepeatedRightGrowth
set_option autoImplicit false

namespace Austin12087Trace
open T

theorem normal_second_v_high_head_trace {u a k y r s : T}
    (hu : NF u) (ha : NF a) (hk : NF k) (hs : NF s)
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u)
    (hvr : ht (mul a k) < ht k)
    (hgr : mul (mul a (mul a (mul (mul u a) k))) r = mul u a)
    (hkr : mul (mul a (mul (mul u a) k)) r = k)
    (hws : mul (mul a (mul a k)) s = mul a (mul (mul u a) k))
    (hrs : mul (mul a k) s = r)
    (hwk : ht (mul a (mul (mul u a) k)) < ht k)
    (hrk : ht r < ht k) (hsk : ht s + 2 ≤ ht k)
    (hrw : ht r ≤ ht (mul a (mul (mul u a) k))) :
    let v := mul a k
    let w := mul a (mul (mul u a) k)
    mul u s = v ∧ mul y u = mul a v ∧
      ht (mul a w) < ht w ∧ ht v < ht s ∧
      ht u < ht s ∧ ht a < ht s ∧ ht w = ht s + 1 ∧ ht k = ht s + 2 := by
  let g := mul u a
  let v := mul a k
  let w := mul a (mul g k)
  let e := mul w v
  change mul u s = v ∧ mul y u = mul a v ∧ ht (mul a w) < ht w ∧
    ht v < ht s ∧ ht u < ht s ∧ ht a < ht s ∧ ht w = ht s + 1 ∧ ht k = ht s + 2
  change mul y e = u at hf
  change ht v < ht k at hvr
  change mul (mul a w) r = g at hgr
  change mul w r = k at hkr
  change mul (mul a v) s = w at hws
  change mul v s = r at hrs
  change ht w < ht k at hwk
  change ht r ≤ ht w at hrw
  have hkdom := normal_second_query_k_dominates hu ha hk hf
  have hkg := mul_height_growth_of_right_le (a:=w) (b:=r) (by rw [hkr]; omega)
  rw [hkr] at hkg
  have hkw : ht k = ht w + 1 := by omega
  have hvret := nf_mul_height_key_gap (a:=a) hk
  change ht v = max (ht a) (ht k) + 1 ∨ (ht a + 3 ≤ ht k ∧ ht v + 2 ≤ ht k) at hvret
  have hvw : ht v < ht w := by rcases hvret with hh | hh <;> omega
  have heg := mul_height_growth_of_left_ge (a:=w) (b:=v) (by omega)
  change ht e = max (ht w) (ht v) + 1 at heg
  have hoe := mul_origin_of_right_height_le (a:=w) (b:=v) (by change ht v ≤ ht e; omega)
  change origin e = some (w,v) at hoe
  have hnw : NF w := nf_mul ha (nf_mul (nf_mul hu ha) hk)
  have hnv : NF v := nf_mul ha hk
  obtain ⟨t,_,_,_,hwt,hvt,htgap,_⟩ := nf_return_origin_trace (nf_mul hnw hnv) hoe hf (by change ht u < ht e; omega)
  change ht t + 2 ≤ ht e at htgap
  have how := mul_origin_of_right_height_le (a:=mul a v) (b:=s) (by rw [hws]; omega)
  rw [hws] at how
  have how' := mul_origin_of_right_height_le (a:=mul y u) (b:=t) (by rw [hwt]; omega)
  rw [hwt] at how'
  have hp := Prod.mk.inj (Option.some.inj (how'.symm.trans how))
  rw [hp.2] at hvt
  have hgupper := mul_height_upper u a
  change ht g ≤ max (ht u) (ht a) + 1 at hgupper
  have hAw : ht (mul a w) < ht w := by
    by_cases hh : ht (mul a w) < ht w
    · exact hh
    · have hAg := mul_height_growth_of_right_le (a:=a) (b:=w) (by omega)
      have hgg := mul_height_growth_of_left_ge (a:=mul a w) (b:=r) (by omega)
      rw [hgr] at hgg
      exact False.elim (by omega)
  have hawgap := nf_mul_height_key_gap (a:=a) hnw
  have ha3 : ht a + 3 ≤ ht w := by rcases hawgap with hh | hh <;> omega
  have hav := mul_height_upper a v
  have hwupper := mul_height_upper (mul a v) s
  rw [hws] at hwupper
  have hvs : ht v < ht s := by
    by_cases hh : ht v < ht s
    · exact hh
    · have hvg := mul_height_growth_of_right_le (a:=u) (b:=s) (by rw [hvt]; omega)
      rw [hvt] at hvg
      have hav' : ht a < ht v := by omega
      have hrg := mul_height_growth_of_left_ge (a:=v) (b:=s) (by omega)
      rw [hrs] at hrg
      have hret : ht g < ht r := by omega
      have hgr' : mul (mul a w) (mul (mul u s) s) = g := by rw [hvt,hrs]; exact hgr
      exact False.elim (normal_repeated_right_growth_no_return hu hs (by rw [hvt]; omega)
        hgr' (by rw [hvt,hrs]; exact hret))
  have huvs := nf_mul_height_key_gap (a:=u) hs
  rw [hvt] at huvs
  have husmall : ht u < ht s := by rcases huvs with hh | hh <;> omega
  have hasmall : ht a < ht s := by omega
  have hwg := mul_height_growth_of_right_le (a:=mul a v) (b:=s) (by rw [hws]; omega)
  rw [hws] at hwg
  exact ⟨hvt,hp.1,hAw,hvs,husmall,hasmall,by omega,by omega⟩

end Austin12087Trace
#print axioms Austin12087Trace.normal_second_v_high_head_trace

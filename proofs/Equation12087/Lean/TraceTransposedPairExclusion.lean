prelude
import TraceTwoColumnReturnChain
set_option autoImplicit false

namespace Austin12087Trace
open T

theorem normal_transposed_pair_returning_output_impossible {a w y : T}
    (ha : NF a) (hw : NF w)
    (hret : ht (mul a w) < ht w)
    (hf : mul y (mul w (mul a (mul w a))) = mul a w) : False := by
  let u := mul a w
  let k := mul w a
  let v := mul a k
  let e := mul w v
  change ht u < ht w at hret
  change mul y e = u at hf
  have hnU : NF u := nf_mul ha hw
  have hnK : NF k := nf_mul hw ha
  have hnV : NF v := nf_mul ha hnK
  have hnE : NF e := nf_mul hw hnV
  have hagap := nf_mul_height_key_gap (a:=a) hw
  change ht u = max (ht a) (ht w) + 1 ∨ (ht a + 3 ≤ ht w ∧ ht u + 2 ≤ ht w) at hagap
  have haw : ht a + 3 ≤ ht w ∧ ht u + 2 ≤ ht w := by rcases hagap with hh | hh <;> omega
  have hkg := mul_height_growth_of_left_ge (a:=w) (b:=a) (by omega)
  change ht k = max (ht w) (ht a) + 1 at hkg
  have hok := mul_origin_of_right_height_le (a:=w) (b:=a) (by change ht a ≤ ht k; omega)
  change origin k = some (w,a) at hok
  have hvupper := mul_height_upper a k
  change ht v ≤ max (ht a) (ht k) + 1 at hvupper
  have heg : ht e = max (ht w) (ht v) + 1 := by
    have hh := nf_mul_height_key_gap (a:=w) hnV
    change ht e = max (ht w) (ht v) + 1 ∨ (ht w + 3 ≤ ht v ∧ ht e + 2 ≤ ht v) at hh
    rcases hh with hh | hh <;> omega
  have hoe := mul_origin_of_right_height_le (a:=w) (b:=v) (by change ht v ≤ ht e; omega)
  change origin e = some (w,v) at hoe
  obtain ⟨t,_,hnt,_,hwt,hvt,htgap,_⟩ := nf_return_origin_trace hnE hoe hf (by omega)
  have hvr : ht v < ht k := by
    by_cases hh : ht v < ht k
    · exact hh
    · have hvg := mul_height_growth_of_right_le (a:=a) (b:=k) (by change ht k ≤ ht v; omega)
      change ht v = max (ht a) (ht k) + 1 at hvg
      have hov := mul_origin_of_right_height_le (a:=a) (b:=k) (by change ht k ≤ ht v; omega)
      change origin v = some (a,k) at hov
      have hov' := (distinct_outputs_height_origin hvt hwt (by
        intro heq
        have hh' := congrArg ht heq
        omega) (by omega)).1
      have hp := Prod.mk.inj (Option.some.inj (hov'.symm.trans hov))
      rw [hp.2] at hwt
      have hgap := nf_mul_height_key_gap (a:=mul y u) hnK
      rw [hwt] at hgap
      exact False.elim (by rcases hgap with hh | hh <;> omega)
  have hvgap := nf_mul_height_key_gap (a:=a) hnK
  change ht v = max (ht a) (ht k) + 1 ∨ (ht a + 3 ≤ ht k ∧ ht v + 2 ≤ ht k) at hvgap
  have hvw : ht v < ht w := by rcases hvgap with hh | hh <;> omega
  obtain ⟨s,_,hns,_,hws,has,hsgap,_⟩ := nf_return_origin_trace hnK hok (show mul a k = v from rfl) hvr
  have how := mul_origin_of_right_height_le (a:=mul a v) (b:=s) (by rw [hws]; omega)
  rw [hws] at how
  have how' := mul_origin_of_right_height_le (a:=mul y u) (b:=t) (by rw [hwt]; omega)
  rw [hwt] at how'
  have hts := (Prod.mk.inj (Option.some.inj (how'.symm.trans how))).2
  rw [hts] at hvt
  exact normal_two_column_return_chain_impossible ha hnU hnV hns hvt has
    (by rw [hws]) (by rw [hws]; exact hret)

theorem normal_transposed_pair_no_preimage {a w y : T} (ha : NF a) (hw : NF w) :
    mul y (mul w (mul a (mul w a))) ≠ mul a w := by
  intro hf
  by_cases hh : ht (mul a w) < ht w
  · exact normal_transposed_pair_returning_output_impossible ha hw hh hf
  · have hg := mul_height_growth_of_right_le (a:=a) (b:=w) (by omega)
    exact nf_transposed_pair_no_preimage ha hw (by omega) (by omega) hf

end Austin12087Trace
#print axioms Austin12087Trace.normal_transposed_pair_returning_output_impossible
#print axioms Austin12087Trace.normal_transposed_pair_no_preimage

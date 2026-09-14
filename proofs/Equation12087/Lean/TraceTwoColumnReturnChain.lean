prelude
import TraceReturningVInduction
set_option autoImplicit false

namespace Austin12087Trace
open T

theorem normal_two_column_return_chain_impossible {a u v s : T}
    (ha : NF a) (hu : NF u) (hv : NF v) (hs : NF s)
    (hus : mul u s = v) (hvs : mul v s = a)
    (haw : mul a (mul (mul a v) s) = u)
    (hret : ht u < ht (mul (mul a v) s)) : False := by
  let w := mul (mul a v) s
  change mul a w = u at haw
  change ht u < ht w at hret
  have hnw : NF w := nf_mul (nf_mul ha hv) hs
  have hkey := nf_mul_height_key_gap (a:=a) hnw
  rw [haw] at hkey
  have ha3 : ht a + 3 ≤ ht w := by rcases hkey with hh | hh <;> omega
  have hav := mul_height_upper a v
  have hw := mul_height_upper (mul a v) s
  change ht w ≤ max (ht (mul a v)) (ht s) + 1 at hw
  have hasmall : ht a < max (ht v) (ht s) := by omega
  have hvsret : ht a < ht s := by
    have hh := nf_mul_height_key_gap (a:=v) hs
    rw [hvs] at hh
    rcases hh with hh | hh <;> omega
  obtain ⟨z,l,r,hsc⟩ := mul_return_of_height_lt (a:=v) (b:=s) (by rw [hvs]; exact hvsret)
  have hvsmall : ht v < ht s := by rw [hsc]; simp only [ht]; omega
  obtain ⟨z',l',r',hsc'⟩ := mul_return_of_height_lt (a:=u) (b:=s) (by rw [hus]; exact hvsmall)
  rw [hvs] at hsc
  rw [hus] at hsc'
  have hp := T.c.inj (hsc'.symm.trans hsc)
  have huv : u = v := hp.1
  have hva : v = a := hp.2.1
  have hus' : mul u s = u := hus.trans huv.symm
  change mul a (mul (mul a v) s) = u at haw
  rw [← hva,← huv] at haw
  exact normal_fixed_square_successor_impossible hu hs hus' haw

end Austin12087Trace
#print axioms Austin12087Trace.normal_two_column_return_chain_impossible

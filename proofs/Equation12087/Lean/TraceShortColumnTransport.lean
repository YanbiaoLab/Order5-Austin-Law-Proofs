prelude
import TraceSecondVEqualFixedClosed
set_option autoImplicit false

namespace Austin12087Trace
open T

theorem normal_short_column_transport_impossible {a b d t v : T}
    (htn : NF t) (hb : mul b t = v) (hd : mul d t = mul a v)
    (hat : ht a < ht t) (hvt : ht v < ht t) : False := by
  have hbGap := nf_mul_height_key_gap (a:=b) htn
  rw [hb] at hbGap
  have hv2 : ht v + 2 ≤ ht t := by rcases hbGap with hh | hh <;> omega
  have hav := mul_height_upper a v
  have hdGap := nf_mul_height_key_gap (a:=d) htn
  rw [hd] at hdGap
  have havt : ht (mul a v) < ht t := by rcases hdGap with hh | hh <;> omega
  obtain ⟨z,l,r,hct⟩ := mul_return_of_height_lt (a:=b) (b:=t) (by rw [hb]; exact hvt)
  obtain ⟨z',l',r',hct'⟩ := mul_return_of_height_lt (a:=d) (b:=t) (by rw [hd]; exact havt)
  have hout := (T.c.inj (hct.symm.trans hct')).2.1
  rw [hb,hd] at hout
  exact mul_ne_right a v hout.symm

theorem normal_v_distinct_fixed_exception_impossible {a g v w s t : T}
    (hw : NF w) (htn : NF t)
    (hAw : ht (mul a w) < ht w)
    (hwh : ht w = ht s + 1) (hth : ht t + 1 = ht s)
    (hvs : ht v < ht s)
    (hvt : mul (mul g g) t = v) (havt : mul (mul a g) t = mul a v) : False := by
  have haGap := nf_mul_height_key_gap (a:=a) hw
  have ha3 : ht a + 3 ≤ ht w := by rcases haGap with hh | hh <;> omega
  have hvGap := nf_mul_height_key_gap (a:=mul g g) htn
  rw [hvt] at hvGap
  have hvsmall : ht v < ht t := by rcases hvGap with hh | hh <;> omega
  exact normal_short_column_transport_impossible htn hvt havt (by omega) hvsmall

end Austin12087Trace
#print axioms Austin12087Trace.normal_short_column_transport_impossible
#print axioms Austin12087Trace.normal_v_distinct_fixed_exception_impossible

prelude
import TraceSecondVHighFixed
set_option autoImplicit false

namespace Austin12087Trace
open T

theorem normal_second_v_low_head_trace {u a k y r s : T}
    (hu : NF u) (ha : NF a) (hk : NF k) (hr : NF r)
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u)
    (hvr : ht (mul a k) < ht k)
    (hgr : mul (mul a (mul a (mul (mul u a) k))) r = mul u a)
    (hkr : mul (mul a (mul (mul u a) k)) r = k)
    (hrs : mul (mul a k) s = r)
    (hrk : ht r < ht k) (hsk : ht s + 2 ≤ ht k)
    (hwr : ht (mul a (mul (mul u a) k)) < ht r) :
    let g := mul u a
    let v := mul a k
    let w := mul a (mul g k)
    ht u < ht r ∧ ht a < ht r ∧ ht g < ht r ∧ ht k = ht r + 1 ∧
      ∃ t, NF t ∧ r = c (mul a w) g t v s ∧
        mul (mul (mul a w) g) t = v ∧ mul g t = s ∧ ht t + 2 ≤ ht r := by
  let g := mul u a
  let v := mul a k
  let w := mul a (mul g k)
  change mul (mul a w) r = g at hgr
  change mul w r = k at hkr
  change mul v s = r at hrs
  change ht v < ht k at hvr
  change ht w < ht r at hwr
  have hkg := mul_height_growth_of_right_le (a:=w) (b:=r) (by rw [hkr]; omega)
  rw [hkr] at hkg
  have hkrht : ht k = ht r + 1 := by omega
  have hvret := nf_mul_height_key_gap (a:=a) hk
  change ht v = max (ht a) (ht k) + 1 ∨ (ht a + 3 ≤ ht k ∧ ht v + 2 ≤ ht k) at hvret
  have har : ht a < ht r := by rcases hvret with hh | hh <;> omega
  have horder := normal_second_v_factor_order hu ha hk hf hgr hkr
  change ht u < max (ht a) (ht r) ∧ (ht g < ht a ∨ ht g < ht r) at horder
  have hur : ht u < ht r := by omega
  have hgrret : ht g < ht r := by
    rcases horder.2 with hh | hh <;> omega
  have hor := mul_origin_of_right_height_le (a:=v) (b:=s) (by rw [hrs]; omega)
  rw [hrs] at hor
  obtain ⟨t,hcode,hnt,_,hvt,hst,htgap,_⟩ := nf_return_origin_trace hr hor hgr hgrret
  exact ⟨hur,har,hgrret,hkrht,t,hnt,hcode,hvt,hst,htgap⟩

end Austin12087Trace
#print axioms Austin12087Trace.normal_second_v_low_head_trace

prelude
import TraceFixedSquareSuccessor
set_option autoImplicit false

namespace Austin12087Trace
open T

theorem normal_fixed_rotation_impossible {u q : T}
    (hu : NF u) (hq : NF q) (hfixed : mul u q = u) :
    mul u (mul q u) ≠ u := by
  intro hrotate
  have huq : ht u < ht q := by
    have hi := inverse_height_strict (inverse_complete u q)
    rw [hfixed] at hi
    omega
  have htg := mul_height_growth_of_left_ge (a:=q) (b:=u) (by omega)
  have hot := mul_origin_of_right_height_le (a:=q) (b:=u) (by omega)
  obtain ⟨s,_,hns,_,hqs,hus,_,_⟩ := nf_return_origin_trace (nf_mul hq hu) hot hrotate (by omega)
  have hbad := normal_fixed_square_successor_impossible hu hns hus
  rw [hqs] at hbad
  exact hbad hfixed

end Austin12087Trace
#print axioms Austin12087Trace.normal_fixed_rotation_impossible

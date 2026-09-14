prelude
import TraceRepeatedTail
set_option autoImplicit false

namespace Austin12087Trace
open T

theorem normal_short_return_control :
    ∃ a u s : T, NF a ∧ NF u ∧ NF s ∧
      mul a (mul (mul a u) s) = u := by
  let u := atom 0
  let w := mul u u
  let j := mul (mul (mul w w) u) (mul w u)
  let s := mul u j
  have hnu : NF u := NF.atom 0
  have hnw : NF w := nf_mul hnu hnu
  have hnj : NF j := nf_mul (nf_mul (nf_mul hnw hnw) hnu) (nf_mul hnw hnu)
  refine ⟨u,u,s,hnu,hnu,nf_mul hnu hnj,?_⟩
  simp +decide [u,w,j,s,mul_equation,inverse.eq_def,decode,leftCode,rightCode,
    origin,queryM,queryI,rankM,rankI,sz,basicInverse]

end Austin12087Trace
#print axioms Austin12087Trace.normal_short_return_control

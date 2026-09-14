prelude
import Init.Data.Option.Lemmas
import Init.Omega
import Init.RCases
import Init.WFTactics
import JudgeTraceSecondVFactorOrder
set_option Elab.async false
/- Checked module: TraceRepeatedRightGrowth -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_repeated_right_growth_no_return {u s d x : T}
    (hu : NF u) (hs : NF s)
    (hg : ht s ≤ ht (mul u s))
    (he : mul d (mul (mul u s) s) = x)
    (hr : ht x < ht (mul (mul u s) s)) : False := by
  let v := mul u s
  let r := mul v s
  change ht s ≤ ht v at hg
  change mul d r = x at he
  change ht x < ht r at hr
  have hv := mul_height_growth_of_right_le (a:=u) (b:=s) hg
  change ht v = max (ht u) (ht s) + 1 at hv
  have hov := mul_origin_of_right_height_le (a:=u) (b:=s) hg
  change origin v = some (u,s) at hov
  have hrg := mul_height_growth_of_left_ge (a:=v) (b:=s) (by omega)
  change ht r = max (ht v) (ht s) + 1 at hrg
  have hor := mul_origin_of_right_height_le (a:=v) (b:=s) (by change ht s ≤ ht r; omega)
  change origin r = some (v,s) at hor
  have hnr : NF r := nf_mul (nf_mul hu hs) hs
  obtain ⟨j,_,_,_,hvj,hsj,hjgap,_⟩ := nf_return_origin_trace hnr hor he hr
  have hov' := mul_origin_of_right_height_le (a:=mul d x) (b:=j) (by rw [hvj]; omega)
  rw [hvj] at hov'
  have hjs := (Prod.mk.inj (Option.some.inj (hov'.symm.trans hov))).2
  rw [hjs] at hsj
  exact mul_ne_right x s hsj

end submission.Austin12087Trace

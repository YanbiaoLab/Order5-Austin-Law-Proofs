prelude
import TraceSecondVHighHead
set_option autoImplicit false

namespace Austin12087Trace
open T

theorem normal_v_high_head_distinct_fixed {u a v w r s : T}
    (hu : NF u) (ha : NF a) (hw : NF w) (hr : NF r)
    (hus : mul u s = v) (hrs : mul v s = r)
    (hws : mul (mul a v) s = w) (hgr : mul (mul a w) r = mul u a)
    (hAw : ht (mul a w) < ht w)
    (hvs : ht v < ht s) (husmall : ht u < ht s) (hasmall : ht a < ht s)
    (hwh : ht w = ht s + 1) (hne : v ≠ u) :
    let g := mul u a
    mul a w = g ∧ mul g r = g ∧ ht r = ht w ∧
      ∃ t, NF t ∧ mul g t = s ∧ mul (mul g g) t = v ∧
        mul (mul a g) t = mul a v ∧ ht t + 1 = ht s := by
  let g := mul u a
  let A := mul a w
  change mul A r = g at hgr
  change ht A < ht w at hAw
  obtain ⟨z,l,j,hsc⟩ := mul_return_of_height_lt (a:=u) (b:=s) (by rw [hus]; exact hvs)
  have hrg := mul_height_off_return_key (a:=v) hsc hne
  rw [hrs] at hrg
  have hor := mul_origin_of_right_height_le (a:=v) (b:=s) (by rw [hrs]; omega)
  rw [hrs] at hor
  have hg := mul_height_upper u a
  change ht g ≤ max (ht u) (ht a) + 1 at hg
  obtain ⟨t,_,hnt,_,hvt,hst,htgap,hAkey⟩ := nf_return_origin_trace hr hor hgr (by omega)
  have how := mul_origin_of_right_height_le (a:=mul a v) (b:=s) (by rw [hws]; omega)
  rw [hws] at how
  obtain ⟨j,_,_,_,havj,hsj,hjgap,_⟩ := nf_return_origin_trace hw how (show mul a w = A from rfl) hAw
  have hos := mul_origin_of_right_height_le (a:=g) (b:=t) (by rw [hst]; omega)
  rw [hst] at hos
  have hos' := mul_origin_of_right_height_le (a:=A) (b:=j) (by rw [hsj]; omega)
  rw [hsj] at hos'
  have hp := Prod.mk.inj (Option.some.inj (hos'.symm.trans hos))
  have hAg : A = g := hp.1
  rw [hAg] at hvt hgr hAkey
  rw [hAg,hp.2] at havj
  have hsg := mul_height_growth_of_right_le (a:=g) (b:=t) (by rw [hst]; omega)
  rw [hst] at hsg
  exact ⟨hAg,hgr,by omega,t,hnt,hst,hvt,havj,by omega⟩

end Austin12087Trace
#print axioms Austin12087Trace.normal_v_high_head_distinct_fixed

prelude
import TraceSemanticEdge
set_option autoImplicit false

namespace Austin12087Trace
open T

theorem normal_fixed_column_no_transpose {a v b : T}
    (hnv : NF v) (hav : mul a v = a) : mul b v ≠ mul v a := by
  have ha := inverse_height_strict (inverse_complete a v)
  rw [hav] at ha
  have havh : ht a < ht v := by omega
  have hvag := mul_height_growth_of_left_ge (a:=v) (b:=a) (by omega)
  have hova := mul_origin_of_right_height_le (a:=v) (b:=a) (by omega)
  intro he
  have hobv := mul_origin_of_right_height_le (a:=b) (b:=v) (by rw [he]; omega)
  rw [he,hova] at hobv
  have hp := Prod.mk.inj (Option.some.inj hobv)
  rw [hp.2] at havh
  omega

theorem normal_low_short_tail_conflict {u a v w j l n y : T}
    (hnv : NF v) (hnj : NF j) (hnl : NF l)
    (hav : mul a v = a)
    (hBa : mul (mul a w) (mul u a) ≠ a)
    (hyu : mul y u = mul (mul (mul a w) (mul u a)) v)
    (hul : mul u l = v) (hvl : mul v l = j)
    (hwl : mul (mul (mul (mul a w) (mul u a)) v) l = w)
    (hAn : mul (mul a w) n = l)
    (hHn : mul (mul a (mul a w)) n = mul (mul (mul a w) (mul u a)) v)
    (hAj : mul (mul a w) j = mul u a)
    (hnw : ht n + 2 ≤ ht w) (hlw : ht l < ht w) : False := by
  let g := mul u a
  let A := mul a w
  let B := mul A g
  let F := mul B v
  change B ≠ a at hBa
  change mul y u = F at hyu
  change mul F l = w at hwl
  change mul A n = l at hAn
  change mul (mul a A) n = F at hHn
  change mul A j = g at hAj
  have ha := inverse_height_strict (inverse_complete a v)
  rw [hav] at ha
  have havh : ht a < ht v := by omega
  obtain ⟨z,lv,rv,hvc⟩ := mul_return_of_height_lt (a:=a) (b:=v) (by rw [hav]; omega)
  have hF := mul_height_off_return_key (a:=B) hvc hBa
  change ht F = max (ht B) (ht v) + 1 at hF
  have hoF := mul_origin_of_right_height_le (a:=B) (b:=v) (by change ht v ≤ ht F; omega)
  change origin F = some (B,v) at hoF
  have huv : u ≠ v := by
    intro he
    have hjv : j = v := by rw [← he] at hvl; exact hvl.symm.trans hul
    have hb : mul A v = mul v a := by simpa only [g,hjv,he] using hAj
    exact normal_fixed_column_no_transpose hnv hav hb
  have hFu : ht F < ht u := by
    by_cases hh : ht F < ht u
    · exact hh
    · have hou := mul_origin_of_right_height_le (a:=y) (b:=u) (by rw [hyu]; omega)
      rw [hyu,hoF] at hou
      have hp := Prod.mk.inj (Option.some.inj hou)
      exact False.elim (huv hp.2.symm)
  have hulGap := nf_mul_height_key_gap (a:=u) hnl
  rw [hul] at hulGap
  have hulh : ht u + 3 ≤ ht l := by rcases hulGap with hh | hh <;> omega
  have hwHeight := mul_height_growth_of_right_le (a:=F) (b:=l) (by rw [hwl]; omega)
  rw [hwl] at hwHeight
  have hwlh : ht w = ht l + 1 := by omega
  obtain ⟨zl,ll,rl,hlc⟩ := mul_return_of_height_lt (a:=u) (b:=l) (by rw [hul]; omega)
  have hjHeight := mul_height_off_return_key (a:=v) hlc (Ne.symm huv)
  rw [hvl] at hjHeight
  have hjlh : ht j = ht l + 1 := by omega
  have hoj := mul_origin_of_right_height_le (a:=v) (b:=l) (by rw [hvl]; omega)
  rw [hvl] at hoj
  have hgHeight := mul_height_growth_of_left_ge (a:=u) (b:=a) (by omega)
  change ht g = max (ht u) (ht a) + 1 at hgHeight
  obtain ⟨m,_,_,_,hBm,hgm,hmGap,_⟩ := nf_return_origin_trace hnj hoj hAj (by omega)
  change mul B m = v at hBm
  have hol := mul_origin_of_right_height_le (a:=A) (b:=n) (by rw [hAn]; omega)
  rw [hAn] at hol
  have hol' := mul_origin_of_right_height_le (a:=g) (b:=m) (by rw [hgm]; omega)
  rw [hgm] at hol'
  have hp := Prod.mk.inj (Option.some.inj (hol.symm.trans hol'))
  have hlHeight := mul_height_growth_of_right_le (a:=g) (b:=m) (by rw [hgm]; omega)
  rw [hgm] at hlHeight
  have hnm : n = m := hp.2
  have hnmHeight := congrArg ht hnm
  have hBn : mul B n = v := by rw [hnm]; exact hBm
  have hnF := (distinct_outputs_height_origin hHn hBn (by intro he; have hh := congrArg ht he; omega)
    (by omega)).2
  omega

end Austin12087Trace
#print axioms Austin12087Trace.normal_fixed_column_no_transpose
#print axioms Austin12087Trace.normal_low_short_tail_conflict

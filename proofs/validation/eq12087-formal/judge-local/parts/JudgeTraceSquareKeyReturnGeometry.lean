prelude
import Init.Data.Option.Lemmas
import Init.Omega
import Init.RCases
import Init.WFTactics
import JudgeTraceSameKeyHighColumnKeys
set_option Elab.async false
/- Checked module: TraceSquareKeyReturnGeometry -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_square_key_return_geometry {u a : T} (hu : NF u) (ha : NF a)
    (hB : mul (mul a a) (mul u a) = a) :
    ∃ m, NF m ∧ mul a m = a ∧ mul (mul (mul a a) a) m = u ∧
      origin u = some (mul (mul a a) a,m) ∧
      ht a + 3 ≤ ht m ∧ ht u = ht m + 1 ∧ ht (mul u a) = ht m + 2 ∧
      mul u a = c (mul a a) a m u a := by
  let A := mul a a
  let g := mul u a
  let Y := mul A a
  change mul A g = a at hB
  have hA : ht A = ht a + 1 := by dsimp only [A]; rw [mul_square]; rfl
  have hAg := inverse_height_strict (inverse_complete A g)
  rw [hB] at hAg
  have hag : ht a < ht g := by omega
  have hgGap := nf_mul_height_key_gap (a:=A) (nf_mul hu ha)
  change ht (mul A g) = max (ht A) (ht g) + 1 ∨ (ht A + 3 ≤ ht g ∧ ht (mul A g) + 2 ≤ ht g) at hgGap
  rw [hB] at hgGap
  have ha4 : ht a + 4 ≤ ht g := by rcases hgGap with hh | hh <;> omega
  have hgHeight := mul_height_growth_of_right_le (a:=u) (b:=a) (by change ht a ≤ ht g; omega)
  change ht g = max (ht u) (ht a) + 1 at hgHeight
  have hug : ht g = ht u + 1 := by omega
  have hog := mul_origin_of_right_height_le (a:=u) (b:=a) (by change ht a ≤ ht g; omega)
  obtain ⟨m,hgc,hnm,_,hYm,ham,hmGap,_⟩ := nf_return_origin_trace (nf_mul hu ha) hog hB hag
  have hmKey := nf_mul_height_key_gap (a:=a) hnm
  rw [ham] at hmKey
  have ham3 : ht a + 3 ≤ ht m := by rcases hmKey with hh | hh <;> omega
  have hY := mul_height_growth_of_left_ge (a:=A) (b:=a) (by omega)
  change ht Y = max (ht A) (ht a) + 1 at hY
  have huHeight := mul_height_growth_of_right_le (a:=Y) (b:=m) (by
    change mul Y m = u at hYm
    rw [hYm]; change ht m + 2 ≤ ht g at hmGap; omega)
  change mul Y m = u at hYm
  rw [hYm] at huHeight
  have hou := mul_origin_of_right_height_le (a:=Y) (b:=m) (by rw [hYm]; omega)
  rw [hYm] at hou
  exact ⟨m,hnm,ham,hYm,hou,ham3,by omega,by change ht g = ht m + 2; omega,hgc⟩

theorem normal_square_key_outer_alternatives {u a y e : T}
    (hu : NF u) (ha : NF a) (hne : NF e)
    (hB : mul (mul a a) (mul u a) = a) (hf : mul y e = u) :
    (mul a e = a ∧ y = mul (mul a a) a ∧ ht u = ht e + 1) ∨
      (ht (mul u a) + 1 ≤ ht e ∧ ht y + 3 ≤ ht e) := by
  obtain ⟨m,_,ham,_,hou,_,hum,hgm,_⟩ := normal_square_key_return_geometry hu ha hB
  by_cases heu : ht e ≤ ht u
  · have hou' := mul_origin_of_right_height_le (a:=y) (b:=e) (by rw [hf]; exact heu)
    rw [hf,hou] at hou'
    have hp := Prod.mk.inj (Option.some.inj hou')
    left
    rw [← hp.2]
    exact ⟨ham,hp.1.symm,hum⟩
  · right
    have hgap := nf_mul_height_key_gap (a:=y) hne
    rw [hf] at hgap
    rcases hgap with hh | hh <;> omega

end submission.Austin12087Trace

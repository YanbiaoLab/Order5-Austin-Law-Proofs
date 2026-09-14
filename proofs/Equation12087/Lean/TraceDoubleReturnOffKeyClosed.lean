prelude
import TraceDoubleReturnOffKey
set_option autoImplicit false

namespace Austin12087Trace
open T

theorem normal_double_return_offkey_impossible {u a v w r s y : T}
    (hu : NF u) (ha : NF a) (hnv : NF v) (hnw : NF w)
    (hl : ReturnLadder (mul a w) (mul a v) v (mul u a) w r s)
    (hgr : ht (mul u a) < ht r)
    (hf : mul y (mul w v) = u) (he : ht (mul w v) < ht v) (haw : a ≠ w) : False := by
  let g := mul u a
  let A := mul a w
  let B := mul A g
  let D := mul a v
  let C := mul D w
  let e := mul w v
  obtain ⟨hvD,hDg,heu,hBg,hAB,hBe⟩ := normal_double_return_offkey_geometry hu ha hnv hl hgr hf he haw
  change ht v < ht D at hvD
  change ht D < ht g at hDg
  change ht e < ht u at heu
  change ht B < ht g at hBg
  change mul A B = y at hAB
  change mul B e = a at hBe
  change ReturnLadder A D v g w r s at hl
  change ht g < ht r at hgr
  change mul y e = u at hf
  change ht e < ht v at he
  obtain ⟨ze,le,re,hvc⟩ := mul_return_of_height_lt (a:=w) (b:=v) he
  have hwv := inverse_height_strict (inverse_complete w v)
  change ht w < max (ht v) (ht e) at hwv
  have hD := mul_height_off_return_key (a:=a) hvc haw
  change ht D = max (ht a) (ht v) + 1 at hD
  have hCA : C ≠ A := by
    intro hh
    have hd : D = a := right_injective D a w hh
    have hd' := congrArg ht hd
    omega
  have hng : NF g := nf_mul hu ha
  obtain ⟨zg,lg,rg,hgc⟩ := mul_return_of_height_lt (a:=A) (b:=g) hBg
  have hog := mul_origin_of_right_height_le (a:=u) (b:=a) (by change ht a ≤ ht g; omega)
  change origin g = some (u,a) at hog
  have hrHeight := mul_height_growth_of_right_le (a:=v) (b:=s) (by
    rw [hl.2.1]; exact Nat.le_of_lt (origin_height hl.2.2.1).2)
  rw [hl.2.1] at hrHeight
  have hgGap := nf_mul_height_key_gap (a:=A) hl.1
  rw [hl.2.2.2.1] at hgGap
  have hgs : ht g < ht s := by rcases hgGap with hh | hh <;> omega
  obtain ⟨t,hl₁,_⟩ := return_ladder_step hl hgr (by omega)
  change ReturnLadder D B g w v s t at hl₁
  have htg : ht t ≤ ht g := by
    by_cases hh : ht t ≤ ht g
    · exact hh
    · obtain ⟨j,hl₂,_⟩ := return_ladder_step hl₁ (by omega) (by omega)
      change ReturnLadder B C w v g t j at hl₂
      have htHeight := mul_height_growth_of_right_le (a:=w) (b:=j) (by
        rw [hl₂.2.1]; exact Nat.le_of_lt (origin_height hl₂.2.2.1).2)
      rw [hl₂.2.1] at htHeight
      have hnj := (nf_origin hl₂.1 hl₂.2.2.1).2
      have hjGap := nf_mul_height_key_gap (a:=C) hnj
      rw [hl₂.2.2.2.2] at hjGap
      have hgj : ht g < ht j := by rcases hjGap with hj | hj <;> omega
      obtain ⟨l,hl₃,_⟩ := return_ladder_step hl₂ (by omega) (by omega)
      have hkey := normal_ladder_first_key_of_highest_return hgc hl₃ hgj (by omega) (by omega)
      exact False.elim (hCA hkey)
  have hsHeight := mul_height_growth_of_left_ge (a:=g) (b:=t) htg
  rw [hl₁.2.1] at hsHeight
  obtain ⟨j,_,_,_,hCj,_,hjGap,_⟩ := nf_return_origin_trace hl₁.1 hl₁.2.2.1 hl₁.2.2.2.1 (by omega)
  change mul C j = g at hCj
  have hog' := mul_origin_of_right_height_le (a:=C) (b:=j) (by rw [hCj]; omega)
  rw [hCj,hog] at hog'
  have hCu : C = u := (Prod.mk.inj (Option.some.inj hog')).1.symm
  have hC := mul_height_growth_of_left_ge (a:=D) (b:=w) (by omega)
  change ht C = max (ht D) (ht w) + 1 at hC
  have hoC := mul_origin_of_right_height_le (a:=D) (b:=w) (by change ht w ≤ ht C; omega)
  change origin C = some (D,w) at hoC
  have hou := mul_origin_of_right_height_le (a:=y) (b:=e) (by rw [hf]; omega)
  rw [hf,← hCu,hoC] at hou
  have hp := Prod.mk.inj (Option.some.inj hou)
  have hDy : D = y := hp.1
  have hwe : w = e := hp.2
  have hCuHeight := congrArg ht hCu
  have hgHeight := mul_height_growth_of_left_ge (a:=u) (b:=a) (by omega)
  change ht g = max (ht u) (ht a) + 1 at hgHeight
  have hBGap := nf_mul_height_key_gap (a:=A) hng
  change ht B = max (ht A) (ht g) + 1 ∨ (ht A + 3 ≤ ht g ∧ ht B + 2 ≤ ht g) at hBGap
  have hB2 : ht B + 2 ≤ ht g := by rcases hBGap with hh | hh <;> omega
  have hABD : mul A B = D := hAB.trans hDy.symm
  have hoD := mul_origin_of_right_height_le (a:=a) (b:=v) (by change ht v ≤ ht D; omega)
  change origin D = some (a,v) at hoD
  have hoD' := mul_origin_of_right_height_le (a:=A) (b:=B) (by rw [hABD]; omega)
  rw [hABD,hoD] at hoD'
  have hp' := Prod.mk.inj (Option.some.inj hoD')
  have hAa : A = a := hp'.1.symm
  have hBv : B = v := hp'.2.symm
  have havw : mul a w = a := hAa
  have hvw : mul v w = a := by rw [← hBv,hwe]; exact hBe
  have hva : v = a := right_injective v a w (hvw.trans havw.symm)
  have hwafix : mul w a = w := by rw [← hva]; exact hwe.symm
  exact normal_fixed_rotation_impossible ha hnw havw (by rw [hwafix,havw])

theorem normal_second_two_return_offkey_impossible {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u)
    (hvr : ht (mul a k) < ht k)
    (he : ht (mul (mul a (mul (mul u a) k)) (mul a k)) < ht (mul a k))
    (haw : a ≠ mul a (mul (mul u a) k)) : False := by
  obtain ⟨r,s,hnr,_,_,_,hAr,_,hDs,hvs,_,_,_,hgr,_,t,_,hrc,_,_,_⟩ :=
    normal_second_returning_v_low_head hu ha hk hf hvr
  have hor : origin r = some (mul a k,s) := by rw [hrc]; rfl
  have hl : ReturnLadder (mul a (mul a (mul (mul u a) k))) (mul a (mul a k))
      (mul a k) (mul u a) (mul a (mul (mul u a) k)) r s := ⟨hnr,hvs,hor,hAr,hDs⟩
  exact normal_double_return_offkey_impossible hu ha (nf_mul ha hk)
    (nf_mul ha (nf_mul (nf_mul hu ha) hk)) hl hgr hf he haw

end Austin12087Trace
#print axioms Austin12087Trace.normal_double_return_offkey_impossible
#print axioms Austin12087Trace.normal_second_two_return_offkey_impossible

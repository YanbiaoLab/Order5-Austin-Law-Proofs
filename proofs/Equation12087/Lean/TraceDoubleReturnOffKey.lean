prelude
import TraceReturningMiddleFrontier
set_option autoImplicit false

namespace Austin12087Trace
open T

theorem normal_double_return_offkey_geometry {u a v w r s y : T}
    (hu : NF u) (ha : NF a) (hnv : NF v)
    (hl : ReturnLadder (mul a w) (mul a v) v (mul u a) w r s)
    (hgr : ht (mul u a) < ht r)
    (hf : mul y (mul w v) = u) (he : ht (mul w v) < ht v) (haw : a ≠ w) :
    let g := mul u a
    let A := mul a w
    let B := mul A g
    let D := mul a v
    ht v < ht D ∧ ht D < ht g ∧ ht (mul w v) < ht u ∧
    ht B < ht g ∧ mul A B = y ∧ mul B (mul w v) = a := by
  let g := mul u a
  let A := mul a w
  let B := mul A g
  let D := mul a v
  let e := mul w v
  change ReturnLadder A D v g w r s at hl
  change ht g < ht r at hgr
  change mul y e = u at hf
  change ht e < ht v at he
  change ht v < ht D ∧ ht D < ht g ∧ ht e < ht u ∧ ht B < ht g ∧ mul A B = y ∧ mul B e = a
  have heGap := nf_mul_height_key_gap (a:=w) hnv
  change ht e = max (ht w) (ht v) + 1 ∨ (ht w + 3 ≤ ht v ∧ ht e + 2 ≤ ht v) at heGap
  have hew : ht w + 3 ≤ ht v ∧ ht e + 2 ≤ ht v := by rcases heGap with hh | hh <;> omega
  obtain ⟨z,l,b,hvc⟩ := mul_return_of_height_lt (a:=w) (b:=v) he
  have hD := mul_height_off_return_key (a:=a) hvc haw
  change ht D = max (ht a) (ht v) + 1 at hD
  have hDg : ht D < ht g := by
    by_cases hh : ht D < ht g
    · exact hh
    · exact False.elim (return_ladder_second_dominant_impossible hl hgr (by omega) (by omega) (by omega))
  have hng : NF g := nf_mul hu ha
  have hg := mul_height_growth_of_right_le (a:=u) (b:=a) (by change ht a ≤ ht g; omega)
  change ht g = max (ht u) (ht a) + 1 at hg
  have hug : ht g = ht u + 1 := by omega
  have heu : ht e < ht u := by omega
  have hou := mul_origin_of_right_height_le (a:=y) (b:=e) (by rw [hf]; omega)
  rw [hf] at hou
  have hog := mul_origin_of_right_height_le (a:=u) (b:=a) (by change ht a ≤ ht g; omega)
  change origin g = some (u,a) at hog
  have hBg : ht B < ht g := by
    by_cases hh : ht B < ht g
    · exact hh
    · have hB := mul_height_growth_of_right_le (a:=A) (b:=g) (by change ht g ≤ ht B; omega)
      exact False.elim (factored_growing_key_ladder_impossible hl hgr (show mul w v = e from rfl)
        haw hB (by omega) (by omega))
  obtain ⟨m,_,_,_,hABm,hBm,hmGap,_⟩ := nf_return_origin_trace hng hog (show mul A g = B from rfl) hBg
  have hou' := mul_origin_of_right_height_le (a:=mul A B) (b:=m) (by rw [hABm]; omega)
  rw [hABm,hou] at hou'
  have hp := Prod.mk.inj (Option.some.inj hou')
  have hAB : mul A B = y := hp.1.symm
  have hme : m = e := hp.2.symm
  have hBe : mul B e = a := by rw [← hme]; exact hBm
  exact ⟨by omega,hDg,heu,hBg,hAB,hBe⟩

theorem normal_second_two_return_offkey_trace {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u)
    (hvr : ht (mul a k) < ht k)
    (he : ht (mul (mul a (mul (mul u a) k)) (mul a k)) < ht (mul a k))
    (haw : a ≠ mul a (mul (mul u a) k)) :
    let g := mul u a
    let v := mul a k
    let w := mul a (mul g k)
    let A := mul a w
    let B := mul A g
    let D := mul a v
    ht v < ht D ∧ ht D < ht g ∧ ht (mul w v) < ht u ∧
    ht B < ht g ∧ mul A B = y ∧ mul B (mul w v) = a := by
  obtain ⟨r,s,hnr,_,_,_,hAr,_,hDs,hvs,_,_,_,hgr,_,t,_,hrc,_,_,_⟩ :=
    normal_second_returning_v_low_head hu ha hk hf hvr
  have hor : origin r = some (mul a k,s) := by rw [hrc]; rfl
  have hl : ReturnLadder (mul a (mul a (mul (mul u a) k))) (mul a (mul a k))
      (mul a k) (mul u a) (mul a (mul (mul u a) k)) r s := ⟨hnr,hvs,hor,hAr,hDs⟩
  exact normal_double_return_offkey_geometry hu ha (nf_mul ha hk) hl hgr hf he haw

end Austin12087Trace
#print axioms Austin12087Trace.normal_double_return_offkey_geometry
#print axioms Austin12087Trace.normal_second_two_return_offkey_trace

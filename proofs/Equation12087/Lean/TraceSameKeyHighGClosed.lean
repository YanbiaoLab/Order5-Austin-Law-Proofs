prelude
import TraceHighestReturnExit
set_option autoImplicit false

namespace Austin12087Trace
open T

theorem normal_same_key_high_g_impossible {u a v r s y : T}
    (hu : NF u) (ha : NF a) (hnv : NF v)
    (hl : ReturnLadder (mul a a) (mul a v) v (mul u a) a r s)
    (hgr : ht (mul u a) < ht r)
    (hf : mul y (mul a v) = u) (he : ht (mul a v) < ht v)
    (hvg : ht v ≤ ht (mul u a)) : False := by
  let A := mul a a
  let g := mul u a
  let B := mul A g
  let e := mul a v
  change ReturnLadder A e v g a r s at hl
  change ht g < ht r at hgr
  change ht v ≤ ht g at hvg
  change mul y e = u at hf
  change ht e < ht v at he
  have havGap := nf_mul_height_key_gap (a:=a) hnv
  change ht e = max (ht a) (ht v) + 1 ∨ (ht a + 3 ≤ ht v ∧ ht e + 2 ≤ ht v) at havGap
  have hav : ht a + 3 ≤ ht v ∧ ht e + 2 ≤ ht v := by rcases havGap with hh | hh <;> omega
  have hA : ht A = ht a + 1 := by dsimp only [A]; rw [mul_square]; rfl
  have hgHeight := mul_height_growth_of_right_le (a:=u) (b:=a) (by change ht a ≤ ht g; omega)
  change ht g = max (ht u) (ht a) + 1 at hgHeight
  have hug : ht g = ht u + 1 := by omega
  have heu : ht e < ht u := by omega
  have hog := mul_origin_of_right_height_le (a:=u) (b:=a) (by change ht a ≤ ht g; omega)
  change origin g = some (u,a) at hog
  have hou := mul_origin_of_right_height_le (a:=y) (b:=e) (by rw [hf]; omega)
  rw [hf] at hou
  have hrHeight := mul_height_growth_of_right_le (a:=v) (b:=s) (by
    rw [hl.2.1]; exact Nat.le_of_lt (origin_height hl.2.2.1).2)
  rw [hl.2.1] at hrHeight
  have hgrGap := nf_mul_height_key_gap (a:=A) hl.1
  rw [hl.2.2.2.1] at hgrGap
  have hgs : ht g < ht s := by rcases hgrGap with hh | hh <;> omega
  have hBg : ht B < ht g := by
    by_cases hh : ht B < ht g
    · exact hh
    · have hB := mul_height_growth_of_right_le (a:=A) (b:=g) (by change ht g ≤ ht B; omega)
      change ht B = max (ht A) (ht g) + 1 at hB
      obtain ⟨t,hl',_⟩ := return_ladder_step hl hgr (by omega)
      change ReturnLadder e B g a v s t at hl'
      exact False.elim (return_ladder_second_dominant_impossible hl' (by omega) (by omega) (by omega) (by omega))
  have hng : NF g := nf_mul hu ha
  obtain ⟨m,hgc,_,_,hABm,hBm,hmGap,_⟩ := nf_return_origin_trace hng hog (show mul A g = B from rfl) hBg
  have hou' := mul_origin_of_right_height_le (a:=mul A B) (b:=m) (by rw [hABm]; omega)
  rw [hABm,hou] at hou'
  have hme : m = e := (Prod.mk.inj (Option.some.inj hou')).2.symm
  have hBe : mul B e = a := by rw [← hme]; exact hBm
  have hea : e ≠ a := by intro hh; rw [hh] at hBe; exact mul_ne_right B a hBe
  have hCA : mul e a ≠ A := by
    intro hh
    exact hea (right_injective e a a hh)
  have hCu : mul e a = u := normal_highest_g_ladder_exit hl hgr hvg (by omega) hgc hog hCA
  have hou'' := mul_origin_of_right_height_le (a:=e) (b:=a) (by rw [hCu]; omega)
  rw [hCu,hou] at hou''
  have hae : a = e := (Prod.mk.inj (Option.some.inj hou'')).2.symm
  exact hea hae.symm

theorem normal_second_same_key_g_below_v {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u)
    (hvr : ht (mul a k) < ht k)
    (he : ht (mul (mul a (mul (mul u a) k)) (mul a k)) < ht (mul a k))
    (haw : a = mul a (mul (mul u a) k)) : ht (mul u a) < ht (mul a k) := by
  obtain ⟨r,s,hnr,_,_,_,hAr,_,hDs,hvs,_,_,_,hgr,_,t,_,hrc,_,_,_⟩ :=
    normal_second_returning_v_low_head hu ha hk hf hvr
  rw [← haw] at hAr hDs hrc hf he
  have hor : origin r = some (mul a k,s) := by rw [hrc]; rfl
  have hl : ReturnLadder (mul a a) (mul a (mul a k)) (mul a k) (mul u a) a r s :=
    ⟨hnr,hvs,hor,hAr,hDs⟩
  by_cases hh : ht (mul u a) < ht (mul a k)
  · exact hh
  · exact False.elim (normal_same_key_high_g_impossible hu ha (nf_mul ha hk) hl hgr hf he (by omega))

end Austin12087Trace
#print axioms Austin12087Trace.normal_same_key_high_g_impossible
#print axioms Austin12087Trace.normal_second_same_key_g_below_v

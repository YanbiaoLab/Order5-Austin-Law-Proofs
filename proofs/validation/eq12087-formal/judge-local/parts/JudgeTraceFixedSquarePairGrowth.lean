prelude
import Init.Data.Option.Lemmas
import Init.Omega
import Init.RCases
import Init.WFTactics
import JudgeTraceSecondFixedPairReduction
set_option Elab.async false
/- Checked module: TraceFixedSquarePairGrowth -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_fixed_square_pair_both_growth_impossible {u b k : T}
    (hu : NF u) (hb : NF b) (hk : NF k)
    (hr : mul u (mul b k) = u)
    (hfixT : mul u (mul (mul b b) k) = u)
    (hrg : ht k ≤ ht (mul b k))
    (htg : ht k ≤ ht (mul (mul b b) k)) : False := by
  let A := mul u u
  let B := mul b b
  let r := mul b k
  let t := mul B k
  have hA : ht A = ht u + 1 := by dsimp only [A]; rw [mul_square]; rfl
  have hB : ht B = ht b + 1 := by dsimp only [B]; rw [mul_square]; rfl
  change mul u r = u at hr
  change mul u t = u at hfixT
  have hur : ht u < ht r := by
    have hi := inverse_height_strict (inverse_complete u r)
    rw [hr] at hi
    omega
  have hut : ht u < ht t := by
    have hi := inverse_height_strict (inverse_complete u t)
    rw [hfixT] at hi
    omega
  have hrg' := mul_height_growth_of_right_le (a:=b) (b:=k) hrg
  change ht r = max (ht b) (ht k) + 1 at hrg'
  have htg' := mul_height_growth_of_right_le (a:=B) (b:=k) htg
  change ht t = max (ht B) (ht k) + 1 at htg'
  have hor := mul_origin_of_right_height_le (a:=b) (b:=k) hrg
  change origin r = some (b,k) at hor
  have hot := mul_origin_of_right_height_le (a:=B) (b:=k) htg
  change origin t = some (B,k) at hot
  obtain ⟨j,_,_,_,hbj,hkj,hjgap,_⟩ := nf_return_origin_trace (nf_mul hb hk) hor hr hur
  obtain ⟨h,_,_,_,hBh,hkh,hhgap,_⟩ := nf_return_origin_trace (nf_mul (nf_mul hb hb) hk) hot hfixT hut
  change ht j + 2 ≤ ht r at hjgap
  change ht h + 2 ≤ ht t at hhgap
  change mul A j = b at hbj
  change mul A h = B at hBh
  by_cases hkb : ht k ≤ ht b
  · have hoB := mul_origin_of_right_height_le (a:=A) (b:=h) (by rw [hBh]; omega)
    rw [hBh] at hoB
    have hoB' : origin B = some (b,b) := by dsimp only [B]; rw [mul_square]; rfl
    have hp := Prod.mk.inj (Option.some.inj (hoB.symm.trans hoB'))
    have hAb : A = b := hp.1
    rw [hp.2,← hAb] at hkh
    rcases mul_height_growth_or_return u A with hg | ⟨x,z,l,r',hc,_⟩
    · rw [hkh] at hg
      have hh := congrArg ht hAb
      omega
    · change mul u u = c u x z l r' at hc
      rw [mul_square] at hc
      cases hc
  · have hok₁ := mul_origin_of_right_height_le (a:=u) (b:=h) (by rw [hkh]; omega)
    rw [hkh] at hok₁
    have hok₂ := mul_origin_of_right_height_le (a:=u) (b:=j) (by rw [hkj]; omega)
    rw [hkj] at hok₂
    have hhj := (Prod.mk.inj (Option.some.inj (hok₁.symm.trans hok₂))).2
    rw [hhj,hbj] at hBh
    have hh := congrArg ht hBh
    omega

theorem normal_fixed_square_pair_alternatives {u b k : T}
    (hu : NF u) (hb : NF b) (hk : NF k)
    (hr : mul u (mul b k) = u)
    (hfixT : mul u (mul (mul b b) k) = u) :
    (ht (mul b k) < ht k ∧ ht k < ht (mul (mul b b) k)) ∨
    (ht (mul (mul b b) k) < ht k ∧ ht k < ht (mul b k)) := by
  have hB : ht (mul b b) = ht b + 1 := by rw [mul_square]; rfl
  by_cases hh : ht (mul b k) < ht k
  · obtain ⟨z,l,r,hkc⟩ := mul_return_of_height_lt hh
    have hneq : mul b b ≠ b := by intro heq; have heh := congrArg ht heq; omega
    have hg := mul_height_off_return_key (a:=mul b b) hkc hneq
    exact Or.inl ⟨hh,by omega⟩
  · have hret : ht (mul (mul b b) k) < ht k := by
      by_cases hret : ht (mul (mul b b) k) < ht k
      · exact hret
      · exact False.elim (normal_fixed_square_pair_both_growth_impossible hu hb hk hr hfixT (by omega) (by omega))
    have hg := mul_height_growth_of_right_le (a:=b) (b:=k) (by omega)
    exact Or.inr ⟨hret,by omega⟩

end submission.Austin12087Trace

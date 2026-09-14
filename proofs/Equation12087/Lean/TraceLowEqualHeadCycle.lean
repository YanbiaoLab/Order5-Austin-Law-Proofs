prelude
import TraceLowColumnCrossLadder
set_option autoImplicit false

namespace Austin12087Trace
open T

theorem normal_equal_head_height {u a y : T} (ha : NF a) (hu : NF u)
    (hf : mul y (mul u a) = u) : ht (mul u a) ≤ ht a + 1 := by
  have hg := nf_mul_height_key_gap (a:=u) ha
  have hfGap := nf_mul_height_key_gap (a:=y) (nf_mul hu ha)
  rw [hf] at hfGap
  rcases hg with hg | hg <;> rcases hfGap with hh | hh <;> omega

theorem normal_equal_head_ladder_impossible {a e s n p : T}
    (ha : NF a) (hne : NF e) (hns : NF s)
    (hea : e ≠ a) (heHeight : ht e ≤ ht a + 1)
    (hes : mul e s = a) (has : ht a < ht s)
    (hl : ReturnLadder (mul a e) a s (mul (mul a a) e) e n p)
    (hBn : ht (mul (mul a a) e) < ht n) : False := by
  let A := mul a a
  let B := mul A e
  let H := mul a e
  let F := mul H B
  let C := mul e a
  change ReturnLadder H a s B e n p at hl
  change ht B < ht n at hBn
  have hA : ht A = ht a + 1 := by dsimp only [A]; rw [mul_square]; rfl
  have hHgap := nf_mul_height_key_gap (a:=a) hne
  change ht H = max (ht a) (ht e) + 1 ∨ (ht a + 3 ≤ ht e ∧ ht H + 2 ≤ ht e) at hHgap
  have hH : ht H = max (ht a) (ht e) + 1 := by rcases hHgap with hh | hh <;> omega
  have hBgap := nf_mul_height_key_gap (a:=A) hne
  change ht B = max (ht A) (ht e) + 1 ∨ (ht A + 3 ≤ ht e ∧ ht B + 2 ≤ ht e) at hBgap
  have hB : ht B = ht a + 2 := by rcases hBgap with hh | hh <;> omega
  have hFgap := nf_mul_height_key_gap (a:=H) (nf_mul (nf_mul ha ha) hne)
  change ht F = max (ht H) (ht B) + 1 ∨ (ht H + 3 ≤ ht B ∧ ht F + 2 ≤ ht B) at hFgap
  have hF : ht F = ht B + 1 := by rcases hFgap with hh | hh <;> omega
  have hoF := mul_origin_of_right_height_le (a:=H) (b:=B) (by change ht B ≤ ht F; omega)
  change origin F = some (H,B) at hoF
  have hesGap := nf_mul_height_key_gap (a:=e) hns
  rw [hes] at hesGap
  have hsRet : ht e + 3 ≤ ht s ∧ ht a + 2 ≤ ht s := by rcases hesGap with hh | hh <;> omega
  have hnHeight := mul_height_growth_of_right_le (a:=s) (b:=p) (by
    rw [hl.2.1]; exact Nat.le_of_lt (origin_height hl.2.2.1).2)
  rw [hl.2.1] at hnHeight
  obtain ⟨q,_,hnq,hnp,hFq,hBq,hqGap,_⟩ := nf_return_origin_trace hl.1 hl.2.2.1 hl.2.2.2.1 hBn
  change mul F q = s at hFq
  by_cases hps : ht p ≤ ht s
  · have hsHeight := mul_height_growth_of_right_le (a:=F) (b:=q) (by rw [hFq]; omega)
    rw [hFq] at hsHeight
    have hos := mul_origin_of_right_height_le (a:=F) (b:=q) (by rw [hFq]; omega)
    rw [hFq] at hos
    obtain ⟨z,_,hnz,_,hCz,haz,hzGap,_⟩ := nf_return_origin_trace hns hos hes has
    change mul C z = F at hCz
    have hCH : C ≠ H := by
      intro hh
      exact hea (mul_commutative_only_equal hh)
    have hFz : ht F < ht z := by
      by_cases hh : ht F < ht z
      · exact hh
      · have hoF' := mul_origin_of_right_height_le (a:=C) (b:=z) (by rw [hCz]; omega)
        rw [hCz,hoF] at hoF'
        exact False.elim (hCH (Prod.mk.inj (Option.some.inj hoF')).1.symm)
    have hsq : ht s = ht q + 1 := by omega
    have hqUpper := mul_height_upper a z
    rw [haz] at hqUpper
    have hqz : ht q = ht z + 1 := by omega
    have hoq := mul_origin_of_right_height_le (a:=a) (b:=z) (by rw [haz]; omega)
    rw [haz] at hoq
    have hpq : ht p < ht q := by
      by_cases hh : ht p < ht q
      · exact hh
      · have hpHeight := mul_height_growth_of_right_le (a:=B) (b:=q) (by rw [hBq]; omega)
        rw [hBq] at hpHeight
        have hBF : B ≠ F := by intro hh; have hh' := congrArg ht hh; omega
        exact False.elim (normal_swapped_returns_top_column_impossible hnp hns hBq hFq
          hl.2.2.2.2 hes (by omega) (by omega) hsq hBF)
    obtain ⟨w,_,_,_,hBPw,hpw,hwGap,_⟩ := nf_return_origin_trace hnq hoq hBq hpq
    have hoz := mul_origin_of_right_height_le (a:=p) (b:=w) (by rw [hpw]; omega)
    rw [hpw] at hoz
    have hl' : ReturnLadder C (mul B p) p F a z w := ⟨hnz,hpw,hoz,hCz,hBPw⟩
    have hBP : ht (mul B p) = max (ht B) (ht p) + 1 := by
      by_cases hpB : ht p ≤ ht B
      · exact mul_height_growth_of_left_ge hpB
      · obtain ⟨zp,lp,rp,hpc⟩ := mul_return_of_height_lt (a:=a) (b:=p) (by rw [hl.2.2.2.2]; omega)
        have hBa : B ≠ a := by intro hh; have hh' := congrArg ht hh; omega
        exact mul_height_off_return_key hpc hBa
    exact return_ladder_second_dominant_impossible hl' hFz (by omega) (by omega) (by omega)
  · have hpHeight := mul_height_growth_of_right_le (a:=B) (b:=q) (by rw [hBq]; omega)
    rw [hBq] at hpHeight
    have hsq : ht s < ht q := by
      have hsGap := nf_mul_height_key_gap (a:=F) hnq
      rw [hFq] at hsGap
      rcases hsGap with hh | hh <;> omega
    obtain ⟨q',hl₁,_⟩ := return_ladder_step hl hBn (by omega)
    have hq'q : q' = q := by
      have hoq := mul_origin_of_right_height_le (a:=B) (b:=q) (by rw [hBq]; omega)
      rw [hBq] at hoq
      exact (Prod.mk.inj (Option.some.inj (hl₁.2.2.1.symm.trans hoq))).2
    subst q'
    obtain ⟨r,hl₂,_⟩ := return_ladder_step hl₁ (by omega) (by omega)
    change ReturnLadder F H e s B q r at hl₂
    have hqHeight := mul_height_growth_of_right_le (a:=e) (b:=r) (by
      rw [hl₂.2.1]; exact Nat.le_of_lt (origin_height hl₂.2.2.1).2)
    rw [hl₂.2.1] at hqHeight
    have hqGap := nf_mul_height_key_gap (a:=F) hl₂.1
    rw [hl₂.2.2.2.1] at hqGap
    have hsr : ht s < ht r := by rcases hqGap with hh | hh <;> omega
    obtain ⟨z,hl₃,_⟩ := return_ladder_step hl₂ hsq (by omega)
    change ReturnLadder H (mul F s) s B e r z at hl₃
    obtain ⟨zs,ls,rs,hsc⟩ := mul_return_of_height_lt (a:=e) (b:=s) (by rw [hes]; exact has)
    have hFe : F ≠ e := by intro hh; have hh' := congrArg ht hh; omega
    have hFs := mul_height_off_return_key (a:=F) hsc hFe
    exact return_ladder_second_dominant_impossible hl₃ (by omega) (by omega) (by omega) (by omega)

end Austin12087Trace
#print axioms Austin12087Trace.normal_equal_head_height
#print axioms Austin12087Trace.normal_equal_head_ladder_impossible

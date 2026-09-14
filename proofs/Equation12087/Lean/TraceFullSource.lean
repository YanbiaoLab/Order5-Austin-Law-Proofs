prelude
import TraceLowEqualHeadCycle
set_option autoImplicit false

namespace Austin12087Trace
open T

theorem normal_low_column_cycle_impossible {u a e v s t y : T}
    (hu : NF u) (ha : NF a) (hnv : NF v) (hns : NF s) (hnt : NF t)
    (hvt : mul (mul (mul a a) (mul u a)) t = v)
    (hst : mul (mul u a) t = s) (hav : mul a v = e) (hes : mul e s = a)
    (he : ht e < ht v) (hsv : ht s < ht v) (hgv : ht (mul u a) < ht v)
    (htv : ht t < ht v) (hf : mul y e = u) : False := by
  have hng := nf_mul hu ha
  have hne : NF e := hav ▸ nf_mul ha hnv
  have httop := normal_low_column_tail_at_top ha hng hnv hns hvt hst hav hes he hsv hgv htv
  obtain ⟨n,p,hl,hBn,_⟩ := normal_low_column_cross_ladder hng hnv hns hnt hvt hst hav hes he hsv httop
  obtain ⟨hge,has⟩ := normal_low_cross_ladder_equal_heads ha hne hng hns hes hl hBn
  rw [hge,hes] at hl
  rw [hge] at hBn
  have hea : e ≠ a := by rw [← hge]; exact mul_ne_right u a
  have hf' : mul y (mul u a) = u := by rw [hge]; exact hf
  have hh := normal_equal_head_height ha hu hf'
  rw [hge] at hh
  exact normal_equal_head_ladder_impossible ha hne hns hea hh hes has hl hBn

theorem normal_same_key_middle_step : NormalSameKeyMiddleStep := by
  intro u a k y hu ha hk hs hf hvr he haw
  have hgv := normal_second_same_key_g_below_v hu ha hk hf hvr he haw
  obtain ⟨r,s,hnr,hns,_,_,hAr,hkr,hDs,hvs,_,_,_,hgr,_,t,hnt,hrc,hvt,hst,htGap⟩ :=
    normal_second_returning_v_low_head hu ha hk hf hvr
  rw [← haw] at hAr hkr hDs hrc hvt hf he
  have hor : origin r = some (mul a k,s) := by rw [hrc]; rfl
  have hl : ReturnLadder (mul a a) (mul a (mul a k)) (mul a k) (mul u a) a r s :=
    ⟨hnr,hvs,hor,hAr,hDs⟩
  have hsv : ht s < ht (mul a k) := by
    by_cases hh : ht s < ht (mul a k)
    · exact hh
    · by_cases heq : ht s = ht (mul a k)
      · exact False.elim (normal_same_key_equal_column_impossible (nf_mul ha hk) hnr hns (nf_mul hu ha)
          hAr hgr hvs hor hvt hst rfl hDs he htGap heq)
      · exact False.elim (normal_same_key_high_column_impossible hu ha (nf_mul ha hk) hl hgr he hgv (by omega) hf)
  have hrHeight := mul_height_growth_of_right_le (a:=mul a k) (b:=s) (by
    rw [hvs]; exact Nat.le_of_lt (origin_height hor).2)
  rw [hvs] at hrHeight
  exact normal_low_column_cycle_impossible hu ha (nf_mul ha hk) hns hnt hvt hst rfl hDs
    he hsv hgv (by omega) hf

theorem full_source_law : ∀ x y z : NormalTree,
    x = normalMul y (normalMul (normalMul (normalMul y x) z) (normalMul x z)) :=
  normal_law_of_same_key_middle_step normal_same_key_middle_step

theorem infinite_model : ∃ (G : Type) (op : G → G → G) (embed : Nat → G),
    (∀ x y z, x = op y (op (op (op y x) z) (op x z))) ∧
    (∀ m n, embed m = embed n → m = n) ∧ embed 0 ≠ embed 1 := by
  exact ⟨NormalTree,normalMul,normalAtom,full_source_law,
    fun _ _ h => normalAtom_injective h,normalAtom_nontrivial⟩

end Austin12087Trace
#print axioms Austin12087Trace.normal_low_column_cycle_impossible
#print axioms Austin12087Trace.normal_same_key_middle_step
#print axioms Austin12087Trace.full_source_law
#print axioms Austin12087Trace.infinite_model

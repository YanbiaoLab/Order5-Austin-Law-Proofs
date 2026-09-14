prelude
import Init.Data.Option.Lemmas
import Init.Omega
import Init.RCases
import Init.WFTactics
import JudgeTraceSameKeyColumnFrontier
set_option Elab.async false
/- Checked module: TraceHighColumnReturnCycle -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_high_v_tail_growth {a e g v t j : T}
    (hnv : NF v) (hav : mul a v = e) (he : ht e < ht v)
    (hag : ht a < ht v) (hgv : ht g < ht v)
    (hl : ReturnLadder a (mul e a) a v g t j) (hvt : ht v < ht t)
    (hKa : mul (mul e a) g ≠ a) :
    ∃ l m, NF l ∧ NF m ∧ mul e l = a ∧ mul v l = j ∧
      mul (mul (mul e a) g) m = v ∧ mul g m = l ∧
      origin v = some (mul (mul e a) g,m) ∧ ht m < ht v := by
  let C := mul e a
  let K := mul C g
  change ReturnLadder a C a v g t j at hl
  change K ≠ a at hKa
  obtain ⟨z,lv,rv,hvc⟩ := mul_return_of_height_lt (a:=a) (b:=v) (by rw [hav]; exact he)
  rw [hav] at hvc
  have htHeight := mul_height_growth_of_right_le (a:=a) (b:=j) (by
    rw [hl.2.1]; exact Nat.le_of_lt (origin_height hl.2.2.1).2)
  rw [hl.2.1] at htHeight
  have htGap := nf_mul_height_key_gap (a:=a) hl.1
  rw [hl.2.2.2.1] at htGap
  have hvj : ht v < ht j := by rcases htGap with hh | hh <;> omega
  obtain ⟨l,_,hnl,hnj,hel,hvl,hlGap,_⟩ := nf_return_origin_trace hl.1 hl.2.2.1 hl.2.2.2.1 hvt
  rw [hav] at hel
  have hjHeight := mul_height_growth_of_right_le (a:=v) (b:=l) (by rw [hvl]; omega)
  rw [hvl] at hjHeight
  have hoj := mul_origin_of_right_height_le (a:=v) (b:=l) (by rw [hvl]; omega)
  rw [hvl] at hoj
  obtain ⟨m,_,hnm,_,hKm,hgm,hmGap,_⟩ := nf_return_origin_trace hnj hoj hl.2.2.2.2 (by omega)
  change mul K m = v at hKm
  have hmv : ht m ≤ ht v := by
    by_cases hh : ht m ≤ ht v
    · exact hh
    · have hml : ht m < ht l := by omega
      have hol := mul_origin_of_right_height_le (a:=g) (b:=m) (by rw [hgm]; omega)
      rw [hgm] at hol
      have hl₂ : ReturnLadder e K g a v l m := ⟨hnl,hgm,hol,hel,hKm⟩
      obtain ⟨n,hl₃,_⟩ := return_ladder_step hl₂ (by omega) (by omega)
      change ReturnLadder K C a v g m n at hl₃
      exact False.elim (hKa (normal_ladder_first_key_at_max hvc hl₃ (by omega) (by omega) (by omega)))
  have hvHeight := mul_height_growth_of_right_le (a:=K) (b:=m) (by rw [hKm]; exact hmv)
  rw [hKm] at hvHeight
  have hov := mul_origin_of_right_height_le (a:=K) (b:=m) (by rw [hKm]; exact hmv)
  rw [hKm] at hov
  exact ⟨l,m,hnl,hnm,hel,hvl,hKm,hgm,hov,by omega⟩

theorem normal_high_column_return_cycle_impossible {a e g v t j : T}
    (ha : NF a) (hnv : NF v) (hav : mul a v = e)
    (he : ht e < ht v) (hae : ht a < ht e) (hge : ht g < ht e)
    (hl : ReturnLadder a (mul e a) a v g t j) (hvt : ht v < ht t) : False := by
  let C := mul e a
  let K := mul C g
  let H := mul a e
  have hC := mul_height_growth_of_left_ge (a:=e) (b:=a) (by omega)
  change ht C = max (ht e) (ht a) + 1 at hC
  have hK := mul_height_growth_of_left_ge (a:=C) (b:=g) (by omega)
  change ht K = max (ht C) (ht g) + 1 at hK
  have hKe : ht K = ht e + 2 := by omega
  have hoK := mul_origin_of_right_height_le (a:=C) (b:=g) (by change ht g ≤ ht K; omega)
  change origin K = some (C,g) at hoK
  have hKa : K ≠ a := by intro hh; have hh' := congrArg ht hh; omega
  obtain ⟨l,m,hnl,hnm,hel,_,hKm,hgm,hov,hmv⟩ :=
    normal_high_v_tail_growth hnv hav he (by omega) (by omega) hl hvt hKa
  change mul K m = v at hKm
  change origin v = some (K,m) at hov
  obtain ⟨n,_,hnn,_,hHn,hen,hnGap,_⟩ := nf_return_origin_trace hnv hov hav he
  change mul H n = K at hHn
  have hKn : ht K < ht n := by
    by_cases hh : ht K < ht n
    · exact hh
    · have hoK' := mul_origin_of_right_height_le (a:=H) (b:=n) (by rw [hHn]; omega)
      rw [hHn,hoK] at hoK'
      have hHC : H = C := (Prod.mk.inj (Option.some.inj hoK')).1.symm
      have hae' := mul_commutative_only_equal hHC
      have hheight := congrArg ht hae'
      exact False.elim (by omega)
  obtain ⟨z,ln,rn,hnc⟩ := mul_return_of_height_lt (a:=H) (b:=n) (by rw [hHn]; exact hKn)
  have heH : e ≠ H := by intro hh; exact mul_ne_right a e hh.symm
  have hmHeight := mul_height_off_return_key (a:=e) hnc heH
  rw [hen] at hmHeight
  have hom := mul_origin_of_right_height_le (a:=e) (b:=n) (by rw [hen]; omega)
  rw [hen] at hom
  have hvHeight := mul_height_growth_of_right_le (a:=K) (b:=m) (by rw [hKm]; omega)
  rw [hKm] at hvHeight
  have hlm : ht l < ht m := by
    by_cases hh : ht l < ht m
    · exact hh
    · have hlHeight := mul_height_growth_of_right_le (a:=g) (b:=m) (by rw [hgm]; omega)
      rw [hgm] at hlHeight
      have hol := mul_origin_of_right_height_le (a:=g) (b:=m) (by rw [hgm]; omega)
      rw [hgm] at hol
      obtain ⟨p,_,_,_,_,hap,hpGap,_⟩ := nf_return_origin_trace hnl hol hel (by omega)
      have hom' := mul_origin_of_right_height_le (a:=a) (b:=p) (by rw [hap]; omega)
      rw [hap,hom] at hom'
      have hea' := (Prod.mk.inj (Option.some.inj hom')).1
      have hheight := congrArg ht hea'
      exact False.elim (by omega)
  obtain ⟨p,_,_,_,hGl,hlp,hpGap,_⟩ := nf_return_origin_trace hnm hom hgm hlm
  have hon := mul_origin_of_right_height_le (a:=l) (b:=p) (by rw [hlp]; omega)
  rw [hlp] at hon
  have hl₂ : ReturnLadder H (mul g l) l K e n p := ⟨hnn,hlp,hon,hHn,hGl⟩
  have hlGap := nf_mul_height_key_gap (a:=e) hnl
  rw [hel] at hlGap
  have hel3 : ht e + 3 ≤ ht l := by rcases hlGap with hh | hh <;> omega
  obtain ⟨zl,ll,rl,hlc⟩ := mul_return_of_height_lt (a:=e) (b:=l) (by rw [hel]; omega)
  have hge' : g ≠ e := by intro hh; have hh' := congrArg ht hh; omega
  have hG := mul_height_off_return_key (a:=g) hlc hge'
  exact return_ladder_second_dominant_impossible hl₂ hKn (by omega) (by omega) (by omega)

end submission.Austin12087Trace

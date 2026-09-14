prelude
import TraceRepeatedQGrowingKey
set_option autoImplicit false

namespace Austin12087Trace
open T

theorem factored_growing_key_ladder_impossible {g b s A a u l j : T}
    (hl : ReturnLadder g (mul b s) s A a l j)
    (hAl : ht A < ht l) (hus : mul a s = u) (hba : b ≠ a)
    (hF : ht (mul g A) = max (ht g) (ht A) + 1)
    (hu : ht u ≤ max (ht g) (ht A))
    (ha : ht a ≤ max (ht g) (ht A)) : False := by
  by_cases hsm : ht s ≤ max (ht g) (ht A)
  · by_cases hAg : ht A ≤ ht g
    · exact return_ladder_dominant_impossible hl (by omega) hAg (by omega)
    · have hlg := mul_height_growth_of_right_le (a:=s) (b:=j) (by
        rw [hl.2.1]
        exact Nat.le_of_lt (origin_height hl.2.2.1).2)
      rw [hl.2.1] at hlg
      have hgap := nf_mul_height_key_gap (a:=g) hl.1
      rw [hl.2.2.2.1] at hgap
      have hA2 : ht A + 2 ≤ ht l := by rcases hgap with hh | hh <;> omega
      obtain ⟨m,hl',_⟩ := return_ladder_step hl hAl (by omega)
      exact return_ladder_second_dominant_impossible hl' (by omega) (by omega) (by omega) (by omega)
  · obtain ⟨z,x,y,hsc⟩ := mul_return_of_height_lt (a:=a) (b:=s) (by rw [hus]; omega)
    have hbs := mul_height_off_return_key (a:=b) hsc hba
    exact return_ladder_second_dominant_impossible hl hAl (by omega) (by omega) (by omega)

theorem normal_repeated_q_core_impossible {u a t h s : T}
    (hu : NF u) (ha : NF a) (htn : NF t) (hhn : NF h) (hsn : NF s)
    (hne : u ≠ a)
    (hat : mul u t = a) (hus : mul a s = u) (hhs : mul t s = h)
    (hbh : mul (mul (mul a u) u) h = mul (mul u a) u)
    (hut : ht u + 3 ≤ ht t) (hatgap : ht a + 2 ≤ ht t)
    (hth : ht t < ht h) : False := by
  let g := mul u a
  let D := mul (mul a u) u
  let b := mul g u
  let A := mul D b
  obtain ⟨r,l,hnr,hnl,_,_,_,hsr,hAl,_,hro,_,hrt,hlr,hs2,hA2⟩ :=
    normal_repeated_q_descending_head hu ha htn hhn hsn hne hat hus hhs hbh hut hatgap hth
  change mul b r = s at hsr
  change mul g l = A at hAl
  change ht A + 2 ≤ ht l at hA2
  obtain ⟨j,_,_,_,haj,hlj,hjgap,_⟩ := nf_return_origin_trace hnr hro hsr (by omega)
  have hlo := mul_origin_of_right_height_le (a:=s) (b:=j) (by rw [hlj]; omega)
  rw [hlj] at hlo
  have hl : ReturnLadder g (mul b s) s A a l j := ⟨hnl,hlj,hlo,hAl,haj⟩
  obtain ⟨hF,hub,hab⟩ := normal_repeated_q_growing_key hu ha hne
  exact factored_growing_key_ladder_impossible hl (by omega) hus
    (repeated_q_target_ne_a u a) hF hub hab

theorem normal_second_returning_q_impossible {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hs : NormalSecondBelow (ht k))
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u)
    (hqr : ht (mul (mul u a) k) < ht k) : False := by
  obtain ⟨hne,_,_,t,z,h,s,hnt,_,hnh,hns,hat,_,_,hus,hhs,hbh,hut,hatgap,htz,hhz,_⟩ :=
    normal_second_returning_q_repeated_core hu ha hk hs hf hqr
  exact normal_repeated_q_core_impossible hu ha hnt hnh hns hne hat hus hhs hbh hut hatgap (by omega)

theorem normal_second_induction_requires_returning_v {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hs : NormalSecondBelow (ht k))
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u) :
    ht (mul a k) < ht k ∧ ht k < ht (mul (mul u a) k) := by
  rcases normal_second_column_alternatives hu ha hk hf with hh | hh
  · exact False.elim (normal_second_returning_q_impossible hu ha hk hs hf hh.1)
  · exact hh

end Austin12087Trace
#print axioms Austin12087Trace.factored_growing_key_ladder_impossible
#print axioms Austin12087Trace.normal_repeated_q_core_impossible
#print axioms Austin12087Trace.normal_second_returning_q_impossible
#print axioms Austin12087Trace.normal_second_induction_requires_returning_v

prelude
import Init.Data.Option.Lemmas
import Init.Omega
import Init.RCases
import Init.WFTactics
import JudgeTraceNonfixedSameKey
set_option Elab.async false
/- Checked module: TraceGeneralHeadExclusion -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem general_head_return_ladder_impossible {u a y V w e t j r : T}
    (hna : NF a) (hnu : NF u) (hV : mul y u = V) (hw : mul a u = w)
    (he : mul V w = e) (hne : V ≠ w) (hat : mul a t = u)
    (hl : ReturnLadder (mul u a) (mul w t) t e a j r) (hej : ht e < ht j) : False := by
  have hnt := (nf_origin hl.1 hl.2.2.1).1
  rcases nf_mul_height_key_gap (a:=a) hnu with hwg | ⟨hau,hwu⟩
  · rw [hw] at hwg
    have hwa : w ≠ a := by intro hh; have hh' := congrArg ht hh; omega
    have hd : ht (mul w t) = max (ht w) (ht t) + 1 := by
      by_cases htu : ht t ≤ ht u
      · exact mul_height_growth_of_left_ge (by omega)
      · obtain ⟨z,l,r,htc⟩ := mul_return_of_height_lt (a:=a) (b:=t) (by rw [hat]; omega)
        exact mul_height_off_return_key htc hwa
    have hde : ht (mul w t) < ht e := by
      by_cases hh : ht (mul w t) < ht e
      · exact hh
      · exact False.elim (return_ladder_second_dominant_impossible hl hej
          (by omega) (by omega) (by omega))
    exact large_head_return_ladder_impossible hna hnu hV hw he hne hat
      (by omega) (by omega) (by omega) (by omega) hl hej
  · rw [hw] at hwu
    obtain ⟨z,l,r,huc⟩ := mul_return_of_height_lt (a:=a) (b:=u) (by rw [hw]; omega)
    have hya : y ≠ a := by
      intro hh
      rw [hh,hw] at hV
      exact hne hV.symm
    have hVg := mul_height_off_return_key (a:=y) huc hya
    rw [hV] at hVg
    have heg := mul_height_growth_of_left_ge (a:=V) (b:=w) (by omega)
    rw [he] at heg
    have hbig : ht u + 1 < ht e := by omega
    by_cases hte : ht t < ht e
    · exact large_head_return_ladder_impossible hna hnu hV hw he hne hat
        (by omega) (by omega) (by omega) hte hl hej
    · obtain ⟨zt,lt,rt,htc⟩ := mul_return_of_height_lt (a:=a) (b:=t) (by rw [hat]; omega)
      by_cases hwa : w = a
      · rw [hwa,hat] at hl
        rw [hwa] at hw he hne
        exact nonfixed_same_key_ladder_impossible hna hnu hw hat hV he hne hbig (by omega) hl hej
      · have hd := mul_height_off_return_key (a:=w) htc hwa
        exact return_ladder_second_dominant_impossible hl hej (by omega) (by omega) (by omega)

theorem normal_first_larger_k_equation_impossible {u q k y : T}
    (hu : NF u) (hnk : NF k)
    (hf : mul (mul y u) k = mul (mul u (mul q (mul u k))) q)
    (hne : q ≠ k) (hs : sz q ≤ sz k) : False := by
  have hqu := normal_first_larger_k_forces_repeated_key hu hnk hf hne hs
  subst q
  obtain ⟨t,j,r,hna,hat,hl,hej,hvw⟩ := normal_first_general_head_ladder hu hnk hne hs hf
  exact general_head_return_ladder_impossible hna hu rfl rfl rfl hvw hat hl hej

theorem normal_first_larger_k_query_absent (u q k : T) (hu : NF u) (hk : NF k)
    (hs : sz q ≤ sz k) :
    (inverse k (mul (mul u (mul q (mul u k))) q)).bind (inverse u) = none := by
  by_cases hqk : q = k
  · subst q
    exact normal_first_diagonal_query_absent u k hu hk
  · cases h₁ : inverse k (mul (mul u (mul q (mul u k))) q) with
    | none => rfl
    | some w =>
      cases h₂ : inverse u w with
      | none => exact h₂
      | some y =>
        have hw := inverse_sound h₁
        have hy := inverse_sound h₂
        rw [←hy] at hw
        exact False.elim (normal_first_larger_k_equation_impossible hu hk hw hqk hs)

end submission.Austin12087Trace

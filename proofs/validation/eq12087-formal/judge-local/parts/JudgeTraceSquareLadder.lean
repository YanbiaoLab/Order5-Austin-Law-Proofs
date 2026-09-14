prelude
import Init.Data.Option.Lemmas
import Init.Omega
import Init.RCases
import Init.WFTactics
import JudgeTraceFixedHeadGeometry
set_option Elab.async false
/- Checked module: TraceSquareLadder -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem same_key_square_ladder_impossible {u a t j r : T}
    (hnu : NF u) (hat : mul a t = u) (hau : mul a u = a)
    (hl : ReturnLadder (mul u a) u t (mul a a) a j r)
    (he : ht (mul a a) < ht j) (hut : ht u < ht t) : False := by
  let g := mul u a
  let e := mul a a
  let f := mul g e
  have hnt : NF t := (nf_origin hl.1 hl.2.2.1).1
  have hnr : NF r := (nf_origin hl.1 hl.2.2.1).2
  have haur := nf_mul_height_key_gap (a:=a) hnu
  rw [hau] at haur
  have hau3 : ht a + 3 ≤ ht u := by rcases haur with hh | hh <;> omega
  have hg : ht g = ht u + 1 := by
    have hh := mul_height_growth_of_left_ge (a:=u) (b:=a) (by omega)
    change ht g = max (ht u) (ht a) + 1 at hh
    omega
  have heh : ht e = ht a + 1 := by dsimp only [e]; rw [mul_square]; rfl
  have hf : ht f = ht u + 2 := by
    have hh := mul_height_growth_of_left_ge (a:=g) (b:=e) (by omega)
    change ht f = max (ht g) (ht e) + 1 at hh
    omega
  obtain ⟨zₜ,lₜ,rₜ,htcode⟩ := mul_return_of_height_lt (a:=a) (b:=t) (by rw [hat]; exact hut)
  rw [hat] at htcode
  have hur := inverse_height_strict (inverse_complete u r)
  rw [hl.2.2.2.2] at hur
  obtain ⟨zᵣ,lᵣ,rᵣ,hrcode⟩ := mul_return_of_height_lt (a:=u) (b:=r) (by
    rw [hl.2.2.2.2]
    omega)
  rw [hl.2.2.2.2] at hrcode
  have hur3 := nf_code_key_height_gap (hrcode ▸ hnr)
  rw [←hrcode] at hur3
  change ht e < ht j at he
  by_cases htr : ht t < ht r
  · obtain ⟨h,hl₁,_⟩ := return_ladder_step hl he htr
    change ReturnLadder u f e a t r h at hl₁
    by_cases htf : ht t ≤ ht f
    · exact return_ladder_second_dominant_impossible hl₁ (by omega)
        (by omega) (by omega) htf
    · have hrg := mul_height_growth_of_right_le (a:=e) (b:=h) (by
        rw [hl₁.2.1]
        exact Nat.le_of_lt (origin_height hl₁.2.2.1).2)
      rw [hl₁.2.1] at hrg
      have hnh : NF h := (nf_origin hl₁.1 hl₁.2.2.1).2
      have hth : ht t < ht h := by
        have hh := nf_mul_height_key_gap (a:=f) hnh
        rw [hl₁.2.2.2.2] at hh
        rcases hh with hh | hh <;> omega
      obtain ⟨z,hl₂,_⟩ := return_ladder_step hl₁ (by omega) (by omega)
      change ReturnLadder f g a t e h z at hl₂
      have hhg := mul_height_growth_of_right_le (a:=a) (b:=z) (by
        rw [hl₂.2.1]
        exact Nat.le_of_lt (origin_height hl₂.2.2.1).2)
      rw [hl₂.2.1] at hhg
      obtain ⟨l,hl₃,_⟩ := return_ladder_step hl₂ hth (by omega)
      have hfg := mul_height_off_return_key (a:=f) htcode (by
        intro heq
        have hh := congrArg ht heq
        omega)
      exact return_ladder_second_dominant_impossible hl₃ (by omega)
        (by omega) (by omega) (by omega)
  · obtain ⟨h,_,hnh,_,hth,hrh,_,_⟩ := nf_return_origin_trace hl.1 hl.2.2.1 hl.2.2.2.1 he
    change mul f h = t at hth
    change mul e h = r at hrh
    have hne : t ≠ r := by
      intro heq
      have hfe := right_injective _ _ h (hth.trans (heq.trans hrh.symm))
      have hh := congrArg ht hfe
      omega
    have hot := (distinct_outputs_height_origin hth hrh hne (by omega)).1
    obtain ⟨z,_,_,_,haz,huz,_,_⟩ := nf_return_origin_trace hnt hot hat hut
    rw [hau] at haz
    have hupper := mul_height_upper e h
    rw [hrh] at hupper
    have hne' : h ≠ f := by
      intro heq
      have hua := right_injective _ _ z (huz.trans (heq.trans haz.symm))
      have hh := congrArg ht hua
      omega
    have hoh := (distinct_outputs_height_origin huz haz hne' (by omega)).1
    have hrlt : ht r < ht h := by
      by_cases hh : ht r < ht h
      · exact hh
      · have hor := mul_origin_of_right_height_le (a:=e) (b:=h) (by rw [hrh]; omega)
        rw [hrh] at hor
        obtain ⟨q,_,_,_,hgq,haq,_,_⟩ :=
          nf_return_origin_trace hnr hor hl.2.2.2.2 (by omega)
        change mul g q = e at hgq
        have hi := inverse_height_strict (inverse_complete g q)
        rw [hgq] at hi
        obtain ⟨zq,lq,rq,hqc⟩ := mul_return_of_height_lt (a:=g) (b:=q) (by rw [hgq]; omega)
        have hag := mul_height_off_return_key (a:=a) hqc (by
          intro heq
          have h := congrArg ht heq
          omega)
        have hoh' := mul_origin_of_right_height_le (a:=a) (b:=q) (by omega)
        rw [haq] at hoh'
        have hua := (Prod.mk.inj (Option.some.inj (hoh.symm.trans hoh'))).1
        have heq := congrArg ht hua
        exact False.elim (by omega)
    have hlₕ : ReturnLadder e a u r f h z := ⟨hnh,huz,hoh,hrh,haz⟩
    have hhg := mul_height_growth_of_right_le (a:=u) (b:=z) (by
      rw [huz]
      exact Nat.le_of_lt (origin_height hoh).2)
    rw [huz] at hhg
    obtain ⟨l,hl',_⟩ := return_ladder_step hlₕ hrlt (by omega)
    have heg := mul_height_off_return_key (a:=e) hrcode (by
      intro heq
      have hh := congrArg ht heq
      omega)
    exact return_ladder_second_dominant_impossible hl' (by omega)
      (by omega) (by omega) (by omega)

end submission.Austin12087Trace

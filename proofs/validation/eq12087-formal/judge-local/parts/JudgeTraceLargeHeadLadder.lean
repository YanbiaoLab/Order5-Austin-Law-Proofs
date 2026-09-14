prelude
import Init.Data.Option.Lemmas
import Init.Omega
import Init.RCases
import Init.WFTactics
import JudgeTraceLeftFour
set_option Elab.async false
/- Checked module: TraceLargeHeadLadder -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem return_from_column_product {u y a g V w e : T}
    (hV : mul y u = V) (hw : mul a u = w) (he : mul V w = e)
    (ho : origin e = some (V,w)) (hne : V ≠ w)
    (hr : ht (mul g e) < ht e) :
    e = c g a u V w ∧ mul g e = a ∧ mul g a = y := by
  obtain ⟨z,l,r,hc⟩ := mul_return_of_height_lt hr
  conv at ho => lhs; rw [hc,origin]
  obtain ⟨hl,hrr⟩ := Prod.mk.inj (Option.some.inj ho)
  subst l; subst r
  have hsem := mul_code_semantics (he.trans hc)
  have hzu := common_column_key_unique hsem.1 hsem.2 hV hw hne
  subst z
  have hfa := right_injective _ _ u (hsem.2.trans hw.symm)
  rw [hfa] at hc hsem
  have hgy := right_injective _ _ u (hsem.1.trans hV.symm)
  exact ⟨hc,hfa,hgy⟩

theorem large_head_return_ladder_impossible {u a y V w e t j r : T}
    (hna : NF a) (hnu : NF u) (hV : mul y u = V) (hw : mul a u = w)
    (he : mul V w = e) (hne : V ≠ w) (hat : mul a t = u)
    (hae : ht a < ht e) (hue : ht u < ht e) (hwe : ht w < ht e) (hte : ht t < ht e)
    (hl : ReturnLadder (mul u a) (mul w t) t e a j r) (hej : ht e < ht j) : False := by
  let g := mul u a
  let d := mul w t
  have hnw : NF w := hw ▸ nf_mul hna hnu
  have hoe := mul_origin_of_right_height_le (a:=V) (b:=w) (by rw [he]; omega)
  rw [he] at hoe
  have main : ∀ n, ∀ j r : T, ht j = n → ReturnLadder g d t e a j r → ht e < ht j → False := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro j r hjn hl hej
      have hjg := mul_height_growth_of_right_le (a:=t) (b:=r) (by
        rw [hl.2.1]
        exact Nat.le_of_lt (origin_height hl.2.2.1).2)
      rw [hl.2.1] at hjg
      have hegap : ht e + 2 ≤ ht j := by
        have hp := nf_mul_height_key_gap (a:=g) hl.1
        rw [hl.2.2.2.1] at hp
        rcases hp with hp | hp <;> omega
      obtain ⟨h,hl₁,_⟩ := return_ladder_step hl hej (by omega)
      have hfa : ht (mul g e) < ht e := by
        by_cases hh : ht (mul g e) < ht e
        · exact hh
        · have hfg := mul_height_growth_of_right_le (a:=g) (b:=e) (by omega)
          exact False.elim (return_ladder_second_dominant_impossible hl₁ (by omega)
            (by omega) (by omega) (by omega))
      obtain ⟨hecode,hfa,_⟩ := return_from_column_product hV hw he hoe hne hfa
      rw [hfa] at hl₁
      change ReturnLadder d a e a t r h at hl₁
      have heh : ht e < ht h := by
        by_cases hh : ht e < ht h
        · exact hh
        · obtain ⟨z,_,_,_,hez,haz,_,_⟩ :=
            nf_return_origin_trace hl₁.1 hl₁.2.2.1 hl₁.2.2.2.1 (by omega)
          have hneh : e ≠ h := by
            intro heq
            exact mul_ne_right d a (right_injective _ _ z (hez.trans (heq.trans haz.symm)))
          have hoe' := (distinct_outputs_height_origin hez haz hneh (by omega)).1
          have hp := Prod.mk.inj (Option.some.inj (hoe'.symm.trans hoe))
          rw [hp.2] at haz
          have hcycle : mul a (mul a (mul a (mul a w))) = w := by
            rw [haz,hl₁.2.2.2.2,hat,hw]
          exact False.elim (nf_no_left_four_cycle hna hnw hcycle)
      obtain ⟨z,hl₂,_⟩ := return_ladder_step hl₁ (by omega) heh
      have hhg := mul_height_growth_of_right_le (a:=a) (b:=z) (by
        rw [hl₂.2.1]
        exact Nat.le_of_lt (origin_height hl₂.2.2.1).2)
      rw [hl₂.2.1] at hhg
      obtain ⟨l,hl₃,_⟩ := return_ladder_step hl₂ (by omega) (by omega)
      rw [hat] at hl₃
      change ReturnLadder (mul d a) u t e a z l at hl₃
      have hez : ht e < ht z := by
        have hp := nf_mul_height_key_gap (a:=mul d a) hl₃.1
        rw [hl₃.2.2.2.1] at hp
        rcases hp with hp | hp <;> omega
      by_cases hwa : w = a
      · have hd : d = u := by dsimp only [d]; rw [hwa,hat]
        have hlnew : ReturnLadder g d t e a z l := by
          change ReturnLadder (mul u a) d t e a z l
          simpa only [hd] using hl₃
        have hzh := (origin_height hl₂.2.2.1).2
        have hhr := (origin_height hl₁.2.2.1).2
        have hrj := (origin_height hl.2.2.1).2
        exact ih (ht z) (by omega) z l rfl hlnew hez
      · have hdg : mul d a ≠ g := by
          intro heq
          have hdu := right_injective _ _ a heq
          have hwa' := right_injective _ _ t (hdu.trans hat.symm)
          exact hwa hwa'
        have hzg := mul_height_growth_of_right_le (a:=t) (b:=l) (by
          rw [hl₃.2.1]
          exact Nat.le_of_lt (origin_height hl₃.2.2.1).2)
        rw [hl₃.2.1] at hzg
        obtain ⟨m,hl₄,_⟩ := return_ladder_step hl₃ hez (by omega)
        have hD := mul_height_off_return_key (a:=mul d a) hecode hdg
        exact return_ladder_second_dominant_impossible hl₄ (by omega)
          (by omega) (by omega) (by omega)
  exact main (ht j) j r rfl hl hej

end submission.Austin12087Trace

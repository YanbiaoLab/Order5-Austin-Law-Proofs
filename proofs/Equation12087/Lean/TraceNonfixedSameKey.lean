prelude
import TraceLargeHeadLadder
set_option autoImplicit false

namespace Austin12087Trace
open T

private theorem return_of_wrong_origin {a b out l r : T}
    (hm : mul a b = out) (ho : origin out = some (l,r)) (hne : a ≠ l) :
    ∃ z x y, b = c a out z x y := by
  rcases mul_height_shape a b with hg | ⟨v,z,x,y,hb,hv⟩
  · rw [hm] at hg
    exact False.elim (hne (Prod.mk.inj (Option.some.inj (hg.2.2.symm.trans ho))).1)
  · have he : v = out := hv.symm.trans hm
    exact ⟨z,x,y,by rw [he] at hb; exact hb⟩

theorem nonfixed_same_key_ladder_impossible {u a y V e t j r : T}
    (hna : NF a) (hnu : NF u) (hau : mul a u = a) (hat : mul a t = u)
    (hV : mul y u = V) (he : mul V a = e) (hne : V ≠ a)
    (hbig : ht u + 1 < ht e) (hte : ht e ≤ ht t)
    (hl : ReturnLadder (mul u a) u t e a j r) (hej : ht e < ht j) : False := by
  let g := mul u a
  let f := mul g e
  have hpu := nf_mul_height_key_gap (a:=a) hnu
  rw [hau] at hpu
  have hau3 : ht a + 3 ≤ ht u := by rcases hpu with hh | hh <;> omega
  have hg : ht g = ht u + 1 := by
    have hh := mul_height_growth_of_left_ge (a:=u) (b:=a) (by omega)
    change ht g = max (ht u) (ht a) + 1 at hh
    omega
  have hoe := mul_origin_of_right_height_le (a:=V) (b:=a) (by rw [he]; omega)
  rw [he] at hoe
  have hag : a ≠ g := by intro h; exact mul_ne_right u a h.symm
  have hua : u ≠ a := by intro h; have hh := congrArg ht h; omega
  have hcases : f = a ∨ (ht f = ht e + 1 ∧ origin f = some (g,e)) := by
    by_cases hh : ht f < ht e
    · exact Or.inl (return_from_column_product hV hau he hoe hne hh).2.1
    · have hfg := mul_height_growth_of_right_le (a:=g) (b:=e) (by change ht e ≤ ht f; omega)
      have hof := mul_origin_of_right_height_le (a:=g) (b:=e) (by change ht e ≤ ht f; omega)
      change ht f = max (ht g) (ht e) + 1 at hfg
      exact Or.inr ⟨by omega,hof⟩
  have main : ∀ n, ∀ j r : T, ht j = n → ReturnLadder g u t e a j r → ht e < ht j → False := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro j r hjn hl hej
      have hnt := (nf_origin hl.1 hl.2.2.1).1
      have hnr := (nf_origin hl.1 hl.2.2.1).2
      obtain ⟨zt,lt,rt,htcode⟩ := mul_return_of_height_lt (a:=a) (b:=t) (by rw [hat]; omega)
      rw [hat] at htcode
      have hir := inverse_height_strict (inverse_complete u r)
      rw [hl.2.2.2.2] at hir
      obtain ⟨zr,lr,rr,hrcode⟩ := mul_return_of_height_lt (a:=u) (b:=r) (by rw [hl.2.2.2.2]; omega)
      rw [hl.2.2.2.2] at hrcode
      have hur := nf_code_key_height_gap (hrcode ▸ hnr)
      rw [←hrcode] at hur
      by_cases htr : ht t < ht r
      · obtain ⟨h,hl₁,_⟩ := return_ladder_step hl hej htr
        change ReturnLadder u f e a t r h at hl₁
        have hrg := mul_height_growth_of_right_le (a:=e) (b:=h) (by
          rw [hl₁.2.1]
          exact Nat.le_of_lt (origin_height hl₁.2.2.1).2)
        rw [hl₁.2.1] at hrg
        have hnh := (nf_origin hl₁.1 hl₁.2.2.1).2
        have heh : ht e < ht h := by
          by_cases hh : ht e < ht h
          · exact hh
          · rcases hcases with hfa | ⟨hfg,_⟩
            · obtain ⟨z,_,_,_,hez,haz,_,_⟩ :=
                nf_return_origin_trace hl₁.1 hl₁.2.2.1 hl₁.2.2.2.1 (by omega)
              have hneh : e ≠ h := by
                intro heq
                exact mul_ne_right u a (right_injective _ _ z (hez.trans (heq.trans haz.symm)))
              have hoe' := (distinct_outputs_height_origin hez haz hneh (by omega)).1
              have hp := Prod.mk.inj (Option.some.inj (hoe'.symm.trans hoe))
              rw [hp.2] at haz
              have hath : mul a h = t := by rw [←hfa]; exact hl₁.2.2.2.2
              have hcycle : mul a (mul a (mul a (mul a a))) = a := by
                rw [haz,hath,hat,hau]
              exact False.elim (nf_no_left_four_cycle hna hna hcycle)
            · exact False.elim (return_ladder_second_dominant_impossible hl₁ (by omega)
                (by omega) (by omega) (by omega))
        have hth : ht t < ht h := by
          have hp := nf_mul_height_key_gap (a:=f) hnh
          rw [hl₁.2.2.2.2] at hp
          rcases hp with hp | hp <;> omega
        obtain ⟨z,hl₂,_⟩ := return_ladder_step hl₁ (by omega) (by omega)
        change ReturnLadder f g a t e h z at hl₂
        have hhg := mul_height_growth_of_right_le (a:=a) (b:=z) (by
          rw [hl₂.2.1]
          exact Nat.le_of_lt (origin_height hl₂.2.2.1).2)
        rw [hl₂.2.1] at hhg
        obtain ⟨l,hl₃,_⟩ := return_ladder_step hl₂ hth (by omega)
        have hez : ht e < ht z := by
          have hp := nf_mul_height_key_gap (a:=g) hl₃.1
          rw [hl₃.2.2.2.1] at hp
          rcases hp with hp | hp <;> omega
        rcases hcases with hfa | ⟨hfg,_⟩
        · rw [hfa,hat] at hl₃
          have hzh := (origin_height hl₂.2.2.1).2
          have hhr := (origin_height hl₁.2.2.1).2
          have hrj := (origin_height hl.2.2.1).2
          exact ih (ht z) (by omega) z l rfl hl₃ hez
        · have hft := mul_height_off_return_key (a:=f) htcode (by
            intro h
            have hh := congrArg ht h
            omega)
          exact return_ladder_second_dominant_impossible hl₃ hez (by omega) (by omega) (by omega)
      · obtain ⟨h,_,hnh,_,hfh,heh,_,_⟩ := nf_return_origin_trace hl.1 hl.2.2.1 hl.2.2.2.1 hej
        change mul f h = t at hfh
        have hfe : f ≠ e := by
          intro h
          have hh := congrArg ht h
          rcases hcases with hfa | hf
          · have ha' := congrArg ht hfa
            omega
          · omega
        have hne' : t ≠ r := by
          intro heq
          exact hfe (right_injective _ _ h (hfh.trans (heq.trans heh.symm)))
        have hot := (distinct_outputs_height_origin hfh heh hne' (by omega)).1
        obtain ⟨z,_,_,_,haz,huz,_,_⟩ := nf_return_origin_trace hnt hot hat (by omega)
        rw [hau] at haz
        have hzc : ∃ q l b, z = c a f q l b := by
          rcases hcases with hfa | ⟨_,hof⟩
          · have hi := inverse_height_strict (inverse_complete a z)
            rw [haz,hfa] at hi
            obtain ⟨q,l,b,hc⟩ := mul_return_of_height_lt (a:=a) (b:=z) (by rw [haz,hfa]; omega)
            rw [haz] at hc
            exact ⟨q,l,b,hc⟩
          · exact return_of_wrong_origin haz hof hag
        obtain ⟨qz,lz,bz,hzc⟩ := hzc
        have hgz := mul_height_off_return_key (a:=u) hzc hua
        have hoh := mul_origin_of_right_height_le (a:=u) (b:=z) (by omega)
        rw [huz] at hgz hoh
        have hfz : ht f < ht z := by rw [hzc]; simp only [ht]; omega
        have hrh : ht r < ht h := by
          by_cases hh : ht r < ht h
          · exact hh
          · have hor := mul_origin_of_right_height_le (a:=e) (b:=h) (by rw [heh]; omega)
            rw [heh] at hor
            obtain ⟨q,_,_,_,hgq,haq,_,_⟩ :=
              nf_return_origin_trace hnr hor hl.2.2.2.2 (by omega)
            change mul g q = e at hgq
            obtain ⟨zq,lq,rq,hqc⟩ := return_of_wrong_origin haq hoh (Ne.symm hua)
            have hgrowth := mul_height_off_return_key (a:=g) hqc (Ne.symm hag)
            rw [hgq] at hgrowth
            have hqh : ht h < ht q := by rw [hqc]; simp only [ht]; omega
            have hrg := mul_height_growth_of_right_le (a:=e) (b:=h) (by rw [heh]; omega)
            rw [heh] at hrg
            have htu := mul_height_upper f h
            rw [hfh] at htu
            exact False.elim (by omega)
        have hlh : ReturnLadder e a u r f h z := ⟨hnh,huz,hoh,heh,haz⟩
        obtain ⟨l,hl',_⟩ := return_ladder_step hlh hrh (by omega)
        have her := mul_height_off_return_key (a:=e) hrcode (by
          intro h
          have hh := congrArg ht h
          omega)
        have hfb : ht f ≤ ht (mul e r) := by
          rcases hcases with hfa | hf
          · have hh := congrArg ht hfa
            omega
          · omega
        exact return_ladder_second_dominant_impossible hl' hfz (by omega) hfb (by omega)
  exact main (ht j) j r rfl hl hej

end Austin12087Trace
#print axioms Austin12087Trace.nonfixed_same_key_ladder_impossible

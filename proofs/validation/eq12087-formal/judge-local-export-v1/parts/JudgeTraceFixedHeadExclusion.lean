prelude
import Init.Data.Option.Lemmas
import Init.Omega
import Init.RCases
import Init.WFTactics
import JudgeTraceSquareLadder
set_option Elab.async false
/- Checked module: TraceFixedHeadExclusion -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem square_return_ladder_impossible {u a t j r : T}
    (hnu : NF u) (hat : mul a t = u)
    (hl : ReturnLadder (mul u a) (mul (mul a u) t) t
      (mul (mul a u) (mul a u)) a j r)
    (he : ht (mul (mul a u) (mul a u)) < ht j) : False := by
  let w := mul a u
  let e := mul w w
  have hnt : NF t := (nf_origin hl.1 hl.2.2.1).1
  have heh : ht e = ht w + 1 := by dsimp only [e]; rw [mul_square]; rfl
  change ht e < ht j at he
  change ReturnLadder (mul u a) (mul w t) t e a j r at hl
  have hw := nf_mul_height_key_gap (a:=a) hnu
  change ht w = max (ht a) (ht u) + 1 ∨
    (ht a + 3 ≤ ht u ∧ ht w + 2 ≤ ht u) at hw
  rcases hw with hw | hw
  · by_cases htu : ht t ≤ ht u
    · have hdg := mul_height_growth_of_left_ge (a:=w) (b:=t) (by omega)
      exact return_ladder_second_dominant_impossible hl he (by omega) (by omega) (by omega)
    · obtain ⟨z,l,r,htcode⟩ := mul_return_of_height_lt (a:=a) (b:=t) (by rw [hat]; omega)
      have hdg := mul_height_off_return_key (a:=w) htcode (by
        intro heq
        have hh := congrArg ht heq
        omega)
      exact return_ladder_second_dominant_impossible hl he (by omega) (by omega) (by omega)
  · by_cases htu : ht t ≤ ht u
    · have hg := mul_height_growth_of_left_ge (a:=u) (b:=a) (by omega)
      exact return_ladder_dominant_impossible hl (by omega) (by omega) (by omega)
    · by_cases hwa : w = a
      · have hl' : ReturnLadder (mul u a) u t (mul a a) a j r := by
          change ReturnLadder (mul u a) (mul w t) t (mul w w) a j r at hl
          rw [hwa,hat] at hl
          exact hl
        have he' : ht (mul a a) < ht j := by change ht (mul w w) < ht j at he; rw [hwa] at he; exact he
        exact same_key_square_ladder_impossible hnu hat hwa hl' he' (by omega)
      · obtain ⟨z,l,r,htcode⟩ := mul_return_of_height_lt (a:=a) (b:=t) (by rw [hat]; omega)
        have hdg := mul_height_off_return_key (a:=w) htcode hwa
        exact return_ladder_second_dominant_impossible hl he (by omega) (by omega) (by omega)

theorem normal_first_fixed_query_absent {u k : T} (hu : NF u) (hnk : NF k)
    (hne : u ≠ k) (hs : sz u ≤ sz k) :
    mul (mul (mul u (mul u (mul u k))) u) k ≠ mul (mul u (mul u (mul u k))) u := by
  intro hf
  let b := mul u (mul u k)
  let a := mul u b
  let w := mul a u
  let e := mul w w
  let g := mul u a
  obtain ⟨t,s,j,hv,hk,hbc,hat,hbt,hes,hws,hgj,haj,hhead,hse⟩ :=
    normal_first_fixed_head_trace hu hnk hne hs hf
  change b = c u a j e s at hbc
  change k = c w w s b t at hk
  change mul a t = u at hat
  change mul b t = k at hbt
  change mul e s = b at hes
  change mul w s = t at hws
  change mul g j = e at hgj
  change mul a j = s at haj
  change ht t ≤ ht b at hhead
  change ht e < ht s at hse
  have hkc := nf_code_actual (hk ▸ hnk)
  have hnb : NF b := hkc.2.2.2.1
  have hnt : NF t := hkc.2.2.2.2.1
  have hns : NF s := hkc.2.2.1
  have hnj : NF j := (nf_code_actual (hbc ▸ hnb)).2.2.1
  have hub := nf_code_key_height_gap (hbc ▸ hnb)
  rw [←hbc] at hub
  have heh : ht e = ht w + 1 := by dsimp only [e]; rw [mul_square]; rfl
  have hos : origin s = some (a,j) := by
    have hne' : s ≠ e := by intro heq; have hh := congrArg ht heq; omega
    exact (distinct_outputs_height_origin haj hgj hne' (by omega)).1
  have hbg := mul_height_growth_of_right_le (a:=e) (b:=s) (by
    rw [hes]
    have ho : origin b = some (e,s) := by rw [hbc]; rfl
    exact Nat.le_of_lt (origin_height ho).2)
  rw [hes] at hbg
  have htret : ht t < ht s := by
    by_cases hh : ht t < ht s
    · exact hh
    · have htg := mul_height_growth_of_right_le (a:=w) (b:=s) (by rw [hws]; omega)
      rw [hws] at htg
      have hot := mul_origin_of_right_height_le (a:=w) (b:=s) (by rw [hws]; omega)
      rw [hws] at hot
      obtain ⟨r,_,_,_,hwr,hurs,_,_⟩ := nf_return_origin_trace hnt hot hat (by omega)
      change mul w r = w at hwr
      have hi := inverse_height_strict (inverse_complete w r)
      rw [hwr] at hi
      obtain ⟨z,l,q,hrc⟩ := mul_return_of_height_lt (a:=w) (b:=r) (by rw [hwr]; omega)
      have huw : u ≠ w := by intro heq; exact mul_ne_right a u heq.symm
      have hsg := mul_height_off_return_key (a:=u) hrc huw
      have hos' := mul_origin_of_right_height_le (a:=u) (b:=r) (by omega)
      rw [hurs] at hos'
      have hp := Prod.mk.inj (Option.some.inj (hos'.symm.trans hos))
      have hgw : g = w := by dsimp only [g,w]; rw [hp.1]
      rw [hp.2] at hwr
      rw [hgw] at hgj
      exact False.elim (mul_ne_right w w (hgj.symm.trans hwr))
  have hej : ht e < ht j := by
    by_cases hh : ht e < ht j
    · exact hh
    · have hoe := mul_origin_of_right_height_le (a:=g) (b:=j) (by rw [hgj]; omega)
      rw [hgj] at hoe
      have hoe' : origin e = some (w,w) := by change origin (mul w w) = some (w,w); rw [mul_square]; rfl
      have hp := Prod.mk.inj (Option.some.inj (hoe.symm.trans hoe'))
      have hua : u = a := mul_commutative_only_equal hp.1
      have hw : ht w = ht u + 1 := by dsimp only [w]; rw [←hua,mul_square]; rfl
      have hupper := mul_height_upper a j
      rw [haj,hp.2,←hua] at hupper
      exact False.elim (by omega)
  obtain ⟨r,hsc,_,_,hdr,htr,hrs,_⟩ := nf_return_origin_trace hns hos hws htret
  have hgjj := nf_mul_height_key_gap (a:=g) hnj
  rw [hgj] at hgjj
  have hug := inverse_height_strict (inverse_complete u a)
  have haw := inverse_height_strict (inverse_complete a u)
  change ht u < max (ht a) (ht g) at hug
  change ht a < max (ht u) (ht w) at haw
  have hgjlt : ht g < ht j := by rcases hgjj with hh | hh <;> omega
  have hsg := mul_height_growth_of_right_le (a:=a) (b:=j) (by
    rw [haj]
    exact Nat.le_of_lt (origin_height hos).2)
  rw [haj] at hsg
  have hor := mul_origin_of_right_height_le (a:=t) (b:=r) (by rw [htr]; omega)
  rw [htr] at hor
  have hl : ReturnLadder g (mul w t) t e a j r := ⟨hnj,htr,hor,hgj,hdr⟩
  exact square_return_ladder_impossible hu hat hl hej

end submission.Austin12087Trace

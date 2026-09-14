prelude
import Init.Data.Option.Lemmas
import Init.Omega
import Init.RCases
import Init.WFTactics
import JudgeTraceGeneralHeadGeometry
set_option Elab.async false
/- Checked module: TraceGeneralHeadLadder -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_first_general_head_ladder {u k y : T} (hu : NF u) (hnk : NF k)
    (hne : u ≠ k) (hs : sz u ≤ sz k)
    (hf : mul (mul y u) k = mul (mul u (mul u (mul u k))) u) :
    let b := mul u (mul u k)
    let a := mul u b
    let V := mul y u
    let w := mul a u
    let e := mul V w
    ∃ t j r, NF a ∧ mul a t = u ∧
      ReturnLadder (mul u a) (mul w t) t e a j r ∧ ht e < ht j ∧ V ≠ w := by
  let b := mul u (mul u k)
  let a := mul u b
  let V := mul y u
  let w := mul a u
  let e := mul V w
  let g := mul u a
  obtain ⟨t,s,j,hv,hk,hbc,hat,hbt,hes,hws,hgj,haj,hhead,hse,hvw⟩ :=
    normal_first_general_head_trace hu hnk hne hs hf
  change b = c u a j e s at hbc
  change k = c V w s b t at hk
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
  have hna : NF a := nf_mul hu hnb
  have hub := nf_code_key_height_gap (hbc ▸ hnb)
  rw [←hbc] at hub
  have hos : origin s = some (a,j) := by
    have hne' : s ≠ e := by intro heq; have hh := congrArg ht heq; omega
    exact (distinct_outputs_height_origin haj hgj hne' (by omega)).1
  have hbg := mul_height_growth_of_right_le (a:=e) (b:=s) (by
    rw [hes]
    have ho : origin b = some (e,s) := by rw [hbc]; rfl
    exact Nat.le_of_lt (origin_height ho).2)
  rw [hes] at hbg
  have hkg := mul_height_growth_of_right_le (a:=b) (b:=t) (by
    rw [hbt]
    have ho : origin k = some (b,t) := by rw [hk]; rfl
    exact Nat.le_of_lt (origin_height ho).2)
  rw [hbt] at hkg
  have hwk := (nf_code_height_gap (hk ▸ hnk)).2.1
  rw [←hk] at hwk
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
      exact False.elim (mul_ne_right V w (hgj.symm.trans hwr))
  obtain ⟨r,hsc,_,_,hdr,htr,hrs,_⟩ := nf_return_origin_trace hns hos hws htret
  have hwskey := nf_code_key_height_gap (hsc ▸ hns)
  rw [←hsc] at hwskey
  have hug := inverse_height_strict (inverse_complete u a)
  have haw := inverse_height_strict (inverse_complete a u)
  change ht u < max (ht a) (ht g) at hug
  change ht a < max (ht u) (ht w) at haw
  have hsg := mul_height_growth_of_right_le (a:=a) (b:=j) (by
    rw [haj]
    exact Nat.le_of_lt (origin_height hos).2)
  rw [haj] at hsg
  have hej : ht e < ht j := by
    by_cases hh : ht e < ht j
    · exact hh
    · have heg := mul_height_growth_of_right_le (a:=g) (b:=j) (by rw [hgj]; omega)
      rw [hgj] at heg
      by_cases hwe : ht w ≤ ht e
      · have hoe := mul_origin_of_right_height_le (a:=g) (b:=j) (by rw [hgj]; omega)
        rw [hgj] at hoe
        have hoe' := mul_origin_of_right_height_le (a:=V) (b:=w) hwe
        change origin e = some (V,w) at hoe'
        have hp := Prod.mk.inj (Option.some.inj (hoe.symm.trans hoe'))
        have hjw := congrArg ht hp.2
        exact False.elim (by omega)
      · exact False.elim (by omega)
  have hgjj := nf_mul_height_key_gap (a:=g) hnj
  rw [hgj] at hgjj
  have hgjlt : ht g < ht j := by rcases hgjj with hh | hh <;> omega
  have hor := mul_origin_of_right_height_le (a:=t) (b:=r) (by rw [htr]; omega)
  rw [htr] at hor
  exact ⟨t,j,r,hna,hat,⟨hnj,htr,hor,hgj,hdr⟩,hej,hvw⟩

end submission.Austin12087Trace

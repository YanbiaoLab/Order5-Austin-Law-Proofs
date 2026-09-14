prelude
import Init.Data.Option.Lemmas
import Init.Omega
import Init.RCases
import Init.WFTactics
import JudgeTraceRepeatedTailClosure
set_option Elab.async false
/- Checked module: TraceGeneralHeadGeometry -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem nf_short_chain_absent_of_left_ge {a u : T} (ha : NF a) (hu : NF u)
    (hle : ht u ≤ ht a) : mul a (mul (mul a u) (mul a (mul a u))) ≠ u := by
  intro he
  let w := mul a u
  let s₀ := mul a w
  let t := mul w s₀
  have hnw : NF w := nf_mul ha hu
  have hns : NF s₀ := nf_mul ha hnw
  have hnt : NF t := nf_mul hnw hns
  have hw : ht w = ht a + 1 := by
    have hg := mul_height_growth_of_left_ge hle
    change ht w = max (ht a) (ht u) + 1 at hg
    omega
  have hsg : ht s₀ = ht a + 2 := by
    have hh := nf_mul_height_key_gap (a:=a) hnw
    change ht s₀ = max (ht a) (ht w) + 1 ∨
      (ht a + 3 ≤ ht w ∧ ht s₀ + 2 ≤ ht w) at hh
    rcases hh with hh | hh <;> omega
  have htg : ht t = ht a + 3 := by
    have hh := nf_mul_height_key_gap (a:=w) hns
    change ht t = max (ht w) (ht s₀) + 1 ∨
      (ht w + 3 ≤ ht s₀ ∧ ht t + 2 ≤ ht s₀) at hh
    rcases hh with hh | hh <;> omega
  have hot := mul_origin_of_right_height_le (a:=w) (b:=s₀) (by
    change ht s₀ ≤ ht t
    omega)
  change origin t = some (w,s₀) at hot
  change mul a t = u at he
  obtain ⟨r,_,_,_,hwr,_,hr,_⟩ := nf_return_origin_trace hnt hot he (by omega)
  change mul w r = w at hwr
  have hi := inverse_height_strict (inverse_complete w r)
  rw [hwr] at hi
  omega

theorem normal_first_general_head_trace {u k y : T} (hu : NF u) (hnk : NF k)
    (hne : u ≠ k) (hs : sz u ≤ sz k)
    (hf : mul (mul y u) k = mul (mul u (mul u (mul u k))) u) :
    let b := mul u (mul u k)
    let a := mul u b
    let V := mul y u
    let w := mul a u
    let e := mul V w
    ∃ t s j,
      mul u k = c u b t u k ∧ k = c V w s b t ∧ b = c u a j e s ∧
      mul a t = u ∧ mul b t = k ∧ mul e s = b ∧ mul w s = t ∧
      mul (mul u a) j = e ∧ mul a j = s ∧ ht t ≤ ht b ∧ ht e < ht s ∧ V ≠ w := by
  let b := mul u (mul u k)
  let a := mul u b
  let V := mul y u
  let w := mul a u
  let e := mul V w
  have hret : mul V k = w := hf
  obtain ⟨t,s,hv,hk,hut,hbt,hes,hws,huk,hqk,hyk,hbk,htk,hsk⟩ :=
    first_larger_k_double_code hu hnk hf hne hs
  have hhead := normal_first_repeated_head_order hu hnk hf hne hs hv
  change k = c V (mul V k) s b t at hk
  change mul (mul V (mul V k)) s = b at hes
  change mul (mul V k) s = t at hws
  change mul a t = u at hut
  change mul b t = k at hbt
  change ht t ≤ ht b at hhead
  rw [hret] at hk hes hws
  change mul e s = b at hes
  have hnb : NF b := (nf_code_actual (hv ▸ nf_mul hu hnk)).2.1
  have hna : NF a := nf_mul hu hnb
  have hab := normal_first_larger_k_inner_returns hu hnk hf hne hs
  change ht a < ht b at hab
  have hbne : b ≠ t := by
    intro he
    exact mul_ne_right V w (right_injective _ _ s (hes.trans (he.trans hws.symm)))
  have hob := (distinct_outputs_height_origin hes hws hbne hhead).1
  obtain ⟨j,hbc,_,_,hgj,haj,_,_⟩ := nf_return_origin_trace hnb hob (show mul u b = a from rfl) hab
  have heslt : ht e < ht s := by
    by_cases hh : ht e < ht s
    · exact hh
    · have hbg := mul_height_growth_of_right_le (a:=e) (b:=s) (by
        rw [hes]
        exact Nat.le_of_lt (origin_height hob).2)
      rw [hes] at hbg
      have hkg := mul_height_growth_of_right_le (a:=b) (b:=t) (by rw [hbt]; exact Nat.le_of_lt htk)
      rw [hbt] at hkg
      have hwk := (nf_code_height_gap (hk ▸ hnk)).2.1
      rw [←hk] at hwk
      have hnes : e ≠ s := by
        intro he
        exact mul_ne_right u a (right_injective _ _ j (hgj.trans (he.trans haj.symm)))
      have hoe := (distinct_outputs_height_origin hgj haj hnes (by omega)).1
      have hoe' := mul_origin_of_right_height_le (a:=V) (b:=w) (by
        change ht w ≤ ht e
        omega)
      change origin e = some (V,w) at hoe'
      have hp := Prod.mk.inj (Option.some.inj (hoe.symm.trans hoe'))
      have hua : ht u ≤ ht a := by
        by_cases h : ht u ≤ ht a
        · exact h
        · have hg := mul_height_growth_of_left_ge (a:=u) (b:=a) (by omega)
          have hog := mul_origin_of_right_height_le (a:=u) (b:=a) (by omega)
          have hoy := mul_origin_of_right_height_le (a:=y) (b:=u) (by
            change ht u ≤ ht V
            rw [←hp.1]
            omega)
          rw [hp.1] at hog
          change origin V = some (y,u) at hoy
          have hau := (Prod.mk.inj (Option.some.inj (hog.symm.trans hoy))).2
          have heq := congrArg ht hau
          exact False.elim (by omega)
      have hss : s = mul a w := by rw [hp.2] at haj; exact haj.symm
      have hbad := hut
      rw [←hws,hss] at hbad
      exact False.elim (nf_short_chain_absent_of_left_ge hna hu hua hbad)
  have hvw : V ≠ w := by
    intro he
    have hfixed := hret
    rw [he] at hfixed
    exact normal_first_fixed_query_absent hu hnk hne hs hfixed
  exact ⟨t,s,j,hv,hk,hbc,hut,hbt,hes,hws,hgj,haj,hhead,heslt,hvw⟩

end submission.Austin12087Trace

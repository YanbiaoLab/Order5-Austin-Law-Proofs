prelude
import Init.Data.Option.Lemmas
import Init.Omega
import Init.RCases
import Init.WFTactics
import JudgeTraceRepeatedFixed
set_option Elab.async false
/- Checked module: TraceFixedHeadGeometry -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem nf_next_square_short_return_absent {u : T} (hu : NF u) :
    mul u (mul (mul u u) (mul u (mul u u))) ≠ u := by
  intro he
  let w := mul u u
  let s₀ := mul u w
  let t := mul w s₀
  have hnw : NF w := nf_mul hu hu
  have hns : NF s₀ := nf_mul hu hnw
  have hnt : NF t := nf_mul hnw hns
  have hw : ht w = ht u + 1 := by dsimp only [w]; rw [mul_square]; rfl
  have hsg : ht s₀ = ht u + 2 := by
    have hshape := mul_height_growth_or_return u w
    rcases hshape with hg | ⟨x,z,l,r,hc,_⟩
    · change ht s₀ = max (ht u) (ht w) + 1 at hg
      omega
    · change mul u u = c u x z l r at hc
      rw [mul_square] at hc
      cases hc
  have htg : ht t = ht u + 3 := by
    have hp := nf_mul_height_key_gap (a:=w) hns
    change ht t = max (ht w) (ht s₀) + 1 ∨
      (ht w + 3 ≤ ht s₀ ∧ ht t + 2 ≤ ht s₀) at hp
    rcases hp with hp | hp <;> omega
  have hot := mul_origin_of_right_height_le (a:=w) (b:=s₀) (by
    change ht s₀ ≤ ht t
    omega)
  change origin t = some (w,s₀) at hot
  change mul u t = u at he
  obtain ⟨r,_,_,_,hwr,_,hr,_⟩ := nf_return_origin_trace hnt hot he (by omega)
  change mul w r = w at hwr
  have hi := inverse_height_strict (inverse_complete w r)
  rw [hwr] at hi
  omega

theorem normal_first_fixed_head_trace {u k : T} (hu : NF u) (hnk : NF k)
    (hne : u ≠ k) (hs : sz u ≤ sz k)
    (hf : mul (mul (mul u (mul u (mul u k))) u) k =
      mul (mul u (mul u (mul u k))) u) :
    let b := mul u (mul u k)
    let a := mul u b
    let w := mul a u
    let e := mul w w
    ∃ t s j,
      mul u k = c u b t u k ∧ k = c w w s b t ∧ b = c u a j e s ∧
      mul a t = u ∧ mul b t = k ∧ mul e s = b ∧ mul w s = t ∧
      mul (mul u a) j = e ∧ mul a j = s ∧ ht t ≤ ht b ∧ ht e < ht s := by
  let b := mul u (mul u k)
  let a := mul u b
  let w := mul a u
  let e := mul w w
  have hfixed : mul w k = w := hf
  obtain ⟨t,s,hv,hk,hut,hbt,hes,hws,huk,hqk,hyk,hbk,htk,hsk⟩ :=
    first_larger_k_double_code (y:=a) hu hnk hf hne hs
  have hhead := normal_first_repeated_fixed_head_order (y:=a) hu hnk hf hne hs hf hv
  change k = c w (mul w k) s b t at hk
  change mul (mul w (mul w k)) s = b at hes
  change mul (mul w k) s = t at hws
  change mul a t = u at hut
  change mul b t = k at hbt
  change ht t ≤ ht b at hhead
  rw [hfixed] at hk hes hws
  change mul e s = b at hes
  have hnb : NF b := (nf_code_actual (hv ▸ nf_mul hu hnk)).2.1
  have hab := normal_first_larger_k_inner_returns (y:=a) hu hnk hf hne hs
  change ht a < ht b at hab
  have hbne : b ≠ t := by
    intro he
    have hew := right_injective _ _ s (hes.trans (he.trans hws.symm))
    exact mul_ne_right w w hew
  have hob := (distinct_outputs_height_origin hes hws hbne hhead).1
  obtain ⟨j,hbc,_,_,hgj,haj,_,_⟩ := nf_return_origin_trace hnb hob (show mul u b = a from rfl) hab
  have heslt : ht e < ht s := by
    by_cases hh : ht e < ht s
    · exact hh
    · have hnes : e ≠ s := by
        intro he
        exact mul_ne_right u a (right_injective _ _ j (hgj.trans (he.trans haj.symm)))
      have hoe := (distinct_outputs_height_origin hgj haj hnes (by omega)).1
      have heo : origin e = some (w,w) := by
        change origin (mul w w) = some (w,w)
        rw [mul_square]
        rfl
      have hp := Prod.mk.inj (Option.some.inj (hoe.symm.trans heo))
      have hua : u = a := mul_commutative_only_equal hp.1
      have hww : w = mul u u := by dsimp only [w]; rw [←hua]
      have hss : s = mul u w := by rw [hp.2,←hua] at haj; exact haj.symm
      have hbad := hut
      rw [←hua,←hws] at hbad
      have hbad' : mul u (mul (mul u u) (mul u (mul u u))) = u := by
        simpa only [hss,hww] using hbad
      exact False.elim (nf_next_square_short_return_absent hu hbad')
  exact ⟨t,s,j,hv,hk,hbc,hut,hbt,hes,hws,hgj,haj,hhead,heslt⟩

end submission.Austin12087Trace

prelude
import Init.Data.Option.Lemmas
import Init.Omega
import Init.RCases
import Init.WFTactics
import JudgeTraceFixedHeadExclusion
set_option Elab.async false
/- Checked module: TraceRepeatedTailClosure -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_first_repeated_tail_impossible {u k y t : T}
    (hu : NF u) (hnk : NF k)
    (hf : mul (mul y u) k = mul (mul u (mul u (mul u k))) u)
    (hne : u ≠ k) (hs : sz u ≤ sz k)
    (hc : mul u k = c u (mul u (mul u k)) t u k)
    (hbtlt : ht (mul u (mul u k)) < ht t) : False := by
  have he := (normal_first_repeated_tail_descent hu hnk hf hne hs hc hbtlt).1
  obtain ⟨t₀,s,hv,hk,hut,hbt,hes,hws,huk,hqk,hyk,hbk,htk,hsk⟩ :=
    first_larger_k_double_code hu hnk hf hne hs
  have htt : t₀ = t := (T.c.inj (hv.symm.trans hc)).2.2.1
  rw [htt] at hv hk hut hbt hws htk
  clear htt t₀
  let b := mul u (mul u k)
  let a := mul u b
  let V := mul y u
  let w := mul V k
  change mul a t = u at hut
  change mul b t = k at hbt
  change mul w s = t at hws
  rw [he] at hes
  change mul u s = b at hes
  have hwa : mul a u = w := hf.symm
  have hnc := nf_code_actual (hc ▸ nf_mul hu hnk)
  have hnb : NF b := hnc.2.1
  have hnt : NF t := hnc.2.2.1
  have hab := normal_first_larger_k_inner_returns hu hnk hf hne hs
  obtain ⟨z,l,r₀,hbc⟩ := mul_return_of_height_lt hab
  change b = c u a z l r₀ at hbc
  have hub := nf_code_key_height_gap (hbc ▸ hnb)
  rw [←hbc] at hub
  have hkg := mul_height_growth_of_right_le (a:=b) (b:=t) (by rw [hbt]; exact Nat.le_of_lt htk)
  rw [hbt] at hkg
  change ht b < ht t at hbtlt
  have hout : origin t = some (w,s) := by
    have hh : t ≠ b := by intro heq; have ht' := congrArg ht heq; omega
    exact (distinct_outputs_height_origin hws hes hh (by omega)).1
  have hutlt : ht u < ht t := by
    have hp := nf_mul_height_key_gap (a:=a) hnt
    rw [hut] at hp
    rcases hp with hg | hg <;> omega
  obtain ⟨r,_,hnr,hns,hwr,hurs,hrt,_⟩ := nf_return_origin_trace hnt hout hut hutlt
  change mul (mul a u) r = w at hwr
  rw [hwa] at hwr
  have hwrlt : ht w < ht r := by
    have hi := inverse_height_strict (inverse_complete w r)
    rw [hwr] at hi
    omega
  obtain ⟨z',l',r',hrc⟩ := mul_return_of_height_lt (a:=w) (b:=r) (by rw [hwr]; exact hwrlt)
  have huw : u ≠ w := by intro heq; exact mul_ne_right a u (hwa.trans heq.symm)
  have hsg := mul_height_off_return_key (a:=u) hrc huw
  rw [hurs] at hsg
  have hos := mul_origin_of_right_height_le (a:=u) (b:=r) (by rw [hurs]; omega)
  rw [hurs] at hos
  have htg := mul_height_growth_of_right_le (a:=w) (b:=s) (by
    rw [hws]
    exact Nat.le_of_lt (origin_height hout).2)
  rw [hws] at htg
  have hbs : ht b < ht s := by
    have hp := nf_mul_height_key_gap (a:=u) hns
    rw [hes] at hp
    rcases hp with hg | hg <;> omega
  obtain ⟨j,hsc,_,_,_,hbr,hjs,_⟩ := nf_return_origin_trace hns hos hes hbs
  have hsb := (nf_code_height_gap (hsc ▸ hns)).2.1
  rw [←hsc] at hsb
  have hor := mul_origin_of_right_height_le (a:=b) (b:=j) (by rw [hbr]; omega)
  rw [hbr] at hor
  obtain ⟨h,hrcode,_,_,_,_,_,_⟩ := nf_return_origin_trace hnr hor hwr hwrlt
  have hubs : sz u < sz b := by rw [hbc]; simp only [sz]; omega
  have hbrs : sz b < sz r := by rw [hrcode]; simp only [sz]; omega
  have hne' : u ≠ r := by intro heq; have hh := congrArg sz heq; omega
  apply normal_first_fixed_query_absent hu hnr hne' (by omega)
  rw [hurs,hes]
  change mul (mul a u) r = mul a u
  rw [hwa,hwr]

theorem normal_first_repeated_head_order {u k y t : T}
    (hu : NF u) (hnk : NF k)
    (hf : mul (mul y u) k = mul (mul u (mul u (mul u k))) u)
    (hne : u ≠ k) (hs : sz u ≤ sz k)
    (hc : mul u k = c u (mul u (mul u k)) t u k) :
    ht t ≤ ht (mul u (mul u k)) := by
  by_cases hh : ht t ≤ ht (mul u (mul u k))
  · exact hh
  · exact False.elim (normal_first_repeated_tail_impossible hu hnk hf hne hs hc (by omega))

end submission.Austin12087Trace

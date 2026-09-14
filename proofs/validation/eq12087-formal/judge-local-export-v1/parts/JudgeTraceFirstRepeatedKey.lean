prelude
import Init.Data.Option.Lemmas
import Init.Omega
import Init.RCases
import Init.WFTactics
import JudgeTraceTriangleLadder
set_option Elab.async false
/- Checked module: TraceFirstRepeatedKey -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_first_larger_k_forces_repeated_key {u q k y : T}
    (hu : NF u) (hnk : NF k)
    (hf : mul (mul y u) k = mul (mul u (mul q (mul u k))) q)
    (hne : q ≠ k) (hs : sz q ≤ sz k) : q = u := by
  by_cases hqu : q = u
  · exact hqu
  · obtain ⟨t,s,hv,hk,hut,hbt,hes,hws,huk,hqk,hyk,hbk,htk,hsk⟩ :=
      first_larger_k_double_code hu hnk hf hne hs
    let b := mul q (mul u k)
    let a := mul u b
    let d := mul q b
    let V := mul y u
    let w := mul V k
    have hwa : mul a q = w := hf.symm
    have hnc := nf_code_actual (hv ▸ nf_mul hu hnk)
    have hnq : NF q := hnc.1
    have hnb : NF b := hnc.2.1
    have hwk := (nf_code_height_gap (hk ▸ hnk)).2.1
    rw [←hk] at hwk
    change ht w + 2 ≤ ht k at hwk
    have hok : origin k = some (b,t) := by rw [hk]; rfl
    have hl : ReturnLadder V d b w u k t := ⟨hnk,hbt,hok,rfl,hut⟩
    have hab : ht b ≤ ht a := by
      by_cases hh : ht b ≤ ht a
      · exact hh
      · obtain ⟨z,l,r,hb⟩ := mul_return_of_height_lt (a:=u) (b:=b) (by
          change ht a < ht b
          omega)
        have hg := mul_height_off_return_key (a:=q) hb hqu
        have hgu := nf_code_key_height_gap (hb ▸ hnb)
        rw [←hb] at hgu
        have hgw := mul_height_upper a q
        rw [hwa] at hgw
        change ht d = max (ht q) (ht b) + 1 at hg
        exact False.elim (return_ladder_second_dominant_impossible hl (by omega)
          (by omega) (by omega) (by omega))
    have hao := mul_origin_of_right_height_le (a:=u) (b:=b) hab
    have hau := (origin_height hao).1
    change ht u < ht a at hau
    have haq : ht q ≤ ht w := by
      by_cases hh : ht q ≤ ht w
      · exact hh
      · have hqr := nf_mul_height_key_gap (a:=a) hnq
        rw [hwa] at hqr
        rcases hqr with hg | ⟨hga,hgw⟩
        · omega
        · have hdg := mul_height_growth_of_left_ge (a:=q) (b:=b) (by omega)
          change ht d = max (ht q) (ht b) + 1 at hdg
          exact False.elim (return_ladder_second_dominant_impossible hl (by omega)
            (by omega) (by omega) (by omega))
    have hwo := mul_origin_of_right_height_le (a:=a) (b:=q) (by rw [hwa]; exact haq)
    rw [hwa] at hwo
    have hbtlt : ht b < ht t := by
      by_cases hh : ht b < ht t
      · exact hh
      · exact False.elim (hqu (first_larger_k_head_forces_same_key hu hnk hf hne hs hv (by
          change ht t ≤ ht b
          omega)))
    obtain ⟨r,hl₂,_⟩ := return_ladder_step hl (by omega) hbtlt
    exact False.elim (triangle_return_ladder_impossible hao hwo hl₂)

theorem normal_first_larger_k_inner_returns {u q k y : T}
    (hu : NF u) (hnk : NF k)
    (hf : mul (mul y u) k = mul (mul u (mul q (mul u k))) q)
    (hne : q ≠ k) (hs : sz q ≤ sz k) :
    ht (mul u (mul q (mul u k))) < ht (mul q (mul u k)) := by
  have hqu := normal_first_larger_k_forces_repeated_key hu hnk hf hne hs
  subst q
  obtain ⟨t,s,hv,hk,hut,hbt,hes,hws,huk,hqk,hyk,hbk,htk,hsk⟩ :=
    first_larger_k_double_code hu hnk hf hne hs
  let b := mul u (mul u k)
  let a := mul u b
  let V := mul y u
  let w := mul V k
  change ht a < ht b
  by_cases hh : ht a < ht b
  · exact hh
  · have hao := mul_origin_of_right_height_le (a:=u) (b:=b) (by
      change ht b ≤ ht a
      omega)
    have hau := (origin_height hao).1
    have hab := (origin_height hao).2
    change ht u < ht a at hau
    change ht b < ht a at hab
    have hwa : mul a u = w := hf.symm
    have hwg := mul_height_growth_of_left_ge (a:=a) (b:=u) (by omega)
    have hwo := mul_origin_of_right_height_le (a:=a) (b:=u) (by omega)
    rw [hwa] at hwo
    have hat := inverse_height_strict (inverse_complete a t)
    change mul a t = u at hut
    rw [hut] at hat
    have hwk := (nf_code_height_gap (hk ▸ hnk)).2.1
    rw [←hk] at hwk
    change ht w + 2 ≤ ht k at hwk
    have hok : origin k = some (b,t) := by rw [hk]; rfl
    have hl : ReturnLadder V a b w u k t := ⟨hnk,hbt,hok,rfl,hut⟩
    obtain ⟨r,hl₂,_⟩ := return_ladder_step hl (by omega) (by omega)
    exact False.elim (triangle_return_ladder_impossible hao hwo hl₂)

end submission.Austin12087Trace

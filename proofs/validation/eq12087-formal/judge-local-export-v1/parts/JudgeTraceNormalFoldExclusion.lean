prelude
import Init.Data.Option.Lemmas
import Init.Omega
import Init.RCases
import Init.WFTactics
import JudgeTraceReturnLadder
set_option Elab.async false
/- Checked module: TraceNormalFoldExclusion -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem initial_fold_keys_or_same {u a t : T} (hnt : NF t) :
    (ht (mul u a) ≤ ht (mul u t) ∧ ht t ≤ ht (mul u t)) ∨
    (ht (mul u a) ≤ ht (mul a t) ∧ ht t ≤ ht (mul a t)) ∨
    (u = a ∧ ht (mul u a) < ht t ∧ ht (mul u t) < ht t) := by
  have hw := mul_height_upper u a
  by_cases hv : ht t ≤ ht (mul u t)
  · have hg := mul_height_growth_of_right_le hv
    by_cases hwide : ht (mul u a) ≤ ht (mul u t)
    · exact Or.inl ⟨hwide,hv⟩
    · have had := mul_height_growth_of_left_ge (a:=a) (b:=t) (by omega)
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
  by_cases hd : ht t ≤ ht (mul a t)
  · have hg := mul_height_growth_of_right_le hd
    by_cases hwide : ht (mul u a) ≤ ht (mul a t)
    · exact Or.inr (Or.inl ⟨hwide,hd⟩)
    · have hu := mul_height_growth_of_left_ge (a:=u) (b:=t) (by omega)
      exact Or.inl ⟨by omega,by omega⟩
  obtain ⟨r,l,b,htu⟩ := mul_return_of_height_lt (a:=u) (b:=t) (by omega)
  obtain ⟨s,c,d,hta⟩ := mul_return_of_height_lt (a:=a) (b:=t) (by omega)
  have he : u = a := (T.c.inj (htu.symm.trans hta)).1
  have hk := nf_code_key_height_gap (htu ▸ hnt)
  rw [←htu] at hk
  apply Or.inr
  apply Or.inr
  refine ⟨he,?_,by omega⟩
  rw [←he,mul_square]
  simp only [ht]
  omega

theorem mul_height_off_return_key {a b k x z l r : T}
    (hb : b = T.c k x z l r) (ha : a ≠ k) :
    ht (mul a b) = max (ht a) (ht b) + 1 := by
  rcases mul_height_growth_or_return a b with hg | ⟨v,s,c,d,hcode,_⟩
  · exact hg
  · exact False.elim (ha (T.c.inj (hcode.symm.trans hb)).1)

theorem nf_fold_impossible {u a t j : T} (hn : NF j) (hf : FoldWitness u a t j) : False := by
  obtain ⟨h,r,s,hj,hh,hrs,hhs,hjs,_,_,hts,hws⟩ := fold_height_tower hf
  let w := mul u a
  let v := mul u t
  let d := mul a t
  let e := mul v w
  let g := mul d t
  change j = T.c v w r t h at hj
  change h = T.c d t s w r at hh
  change ht w < ht s at hws
  have cj := nf_code_actual (hj ▸ hn)
  have hnh : NF h := cj.2.2.2.2.1
  have ch := nf_code_actual (hh ▸ hnh)
  have jgen : mul t h = j := cj.2.2.2.2.2.1.trans hj.symm
  have jorigin : origin j = some (t,h) := by rw [hj]; rfl
  have jret : mul v j = w := hf.1.symm
  have hret : mul d h = t := by rw [hh,mul_code_return]
  have hl₀ : ReturnLadder v d t w t j h := ⟨hn,jgen,jorigin,jret,hret⟩
  have choices := initial_fold_keys_or_same (u:=u) (a:=a) cj.2.2.2.1
  change (ht w ≤ ht v ∧ ht t ≤ ht v) ∨
    (ht w ≤ ht d ∧ ht t ≤ ht d) ∨ (u=a ∧ ht w < ht t ∧ ht v < ht t) at choices
  rcases choices with hv | hd | ⟨hua,hwt,hvt⟩
  · exact return_ladder_dominant_impossible hl₀ hv.2 hv.1 hv.2
  · exact return_ladder_second_dominant_impossible hl₀ (by omega) hd.2 hd.1 hd.2
  · have rgen : mul t s = r := ch.2.2.2.2.2.2.2
    have rorigin := mul_origin_of_right_height_le (a:=t) (b:=s) (by rw [rgen]; omega)
    rw [rgen] at rorigin
    have rret : mul e r = t := cj.2.2.2.2.2.2.1
    obtain ⟨k,_,_,hns,hk,hkgen,hkgap,_⟩ :=
      nf_return_origin_trace cj.2.2.1 rorigin rret (by omega)
    have sorigin := mul_origin_of_right_height_le (a:=t) (b:=k) (by rw [hkgen]; omega)
    rw [hkgen] at sorigin
    have sret : mul g s = w := ch.2.2.2.2.2.2.1
    have hl₃ : ReturnLadder g (mul e t) t w t s k := ⟨hns,hkgen,sorigin,sret,hk⟩
    obtain ⟨z,l,b,htcode⟩ := mul_return_of_height_lt (a:=u) (b:=t) hvt
    have hdv : d = v := by dsimp only [d,v]; rw [hua]
    have hgv : g = mul v t := congrArg (fun q => mul q t) hdv
    by_cases hvu : v = u
    · have hwsq : w = T.s u := by dsimp only [w]; rw [←hua,mul_square]
      have heg : ht e = ht u + 2 := by
        change ht (mul v w) = ht u + 2
        rw [hvu,hwsq]
        rcases mul_height_growth_or_return u (T.s u) with hg | ⟨x,z,l,r,hc,_⟩
        · simp only [ht] at hg
          omega
        · cases hc
      have henu : e ≠ u := by intro he; have hs := congrArg ht he; omega
      have hegrow := mul_height_off_return_key (a:=e) htcode henu
      exact return_ladder_second_dominant_impossible hl₃ hws
        (by omega) (by omega) (by omega)
    · have hvgrow := mul_height_off_return_key (a:=v) htcode hvu
      rw [←hgv] at hvgrow
      exact return_ladder_dominant_impossible hl₃ (by omega) (by omega) (by omega)

end submission.Austin12087Trace

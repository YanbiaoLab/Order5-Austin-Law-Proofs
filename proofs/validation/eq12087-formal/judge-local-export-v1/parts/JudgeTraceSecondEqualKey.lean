prelude
import Init.Data.Option.Lemmas
import Init.Omega
import Init.RCases
import Init.WFTactics
import JudgeTraceEqualCodeTail
set_option Elab.async false
/- Checked module: TraceSecondEqualKey -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_second_equal_input_q_key {u k y : T}
    (hu : NF u) (hk : NF k)
    (hs : NormalSecondBelow (ht k))
    (hf : mul y (mul (mul u (mul (mul u u) k)) (mul u k)) = u)
    (hqr : ht (mul (mul u u) k) < ht k) :
    mul (mul u u) k = u ∧ y = mul u u := by
  let q := mul (mul u u) k
  let w := mul u q
  let e := mul w (mul u k)
  obtain ⟨t,z,h,_,_,_,_,hkc,hec,hwy,hat,_,_,_,hhead,_,_,_⟩ :=
    normal_second_returning_q_head hu hu hk hs hf hqr
  change k = c (mul u u) q z e t at hkc
  change e = c w u h (mul (mul u u) q) z at hec
  change w = y at hwy
  change mul u t = u at hat
  change max (ht u) (ht q) < ht e at hhead
  have hkc' : NF (c (mul u u) q z e t) := hkc ▸ hk
  have htz : mul q z = t := (nf_code_actual hkc').2.2.2.2.2.2.2
  have hnq : NF q := nf_mul (nf_mul hu hu) hk
  have hne : NF e := nf_mul (nf_mul hu hnq) (nf_mul hu hk)
  have hec' : NF (c w u h (mul (mul u u) q) z) := hec ▸ hne
  have hsmall : ht q < ht (c w u h (mul (mul u u) q) z) := by rw [← hec]; omega
  have hfixed : mul u (mul q z) = u := by rw [htz]; exact hat
  have hbz := normal_fixed_code_head_order hu hnq hec' hsmall hfixed
  have hqu := normal_equal_code_key_repeats hu hnq hec' hsmall hbz hfixed
  refine ⟨hqu,?_⟩
  change mul u q = y at hwy
  rw [hqu] at hwy
  exact hwy.symm

theorem normal_second_equal_input_q_core {u k y : T}
    (hu : NF u) (hk : NF k)
    (hs : NormalSecondBelow (ht k))
    (hf : mul y (mul (mul u (mul (mul u u) k)) (mul u k)) = u)
    (hqr : ht (mul (mul u u) k) < ht k) :
    mul (mul u u) k = u ∧
      mul (mul u u) (mul (mul u u) (mul u k)) = u := by
  obtain ⟨hqu,hy⟩ := normal_second_equal_input_q_key hu hk hs hf hqr
  rw [hqu,hy] at hf
  exact ⟨hqu,hf⟩

end submission.Austin12087Trace

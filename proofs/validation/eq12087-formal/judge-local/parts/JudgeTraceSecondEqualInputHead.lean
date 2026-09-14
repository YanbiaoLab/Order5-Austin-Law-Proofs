prelude
import Init.Data.Option.Lemmas
import Init.Omega
import Init.RCases
import Init.WFTactics
import JudgeTraceFixedCodeHead
set_option Elab.async false
/- Checked module: TraceSecondEqualInputHead -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_second_equal_input_returning_q_head {u k y : T}
    (hu : NF u) (hk : NF k)
    (hs : NormalSecondBelow (ht k))
    (hf : mul y (mul (mul u (mul (mul u u) k)) (mul u k)) = u)
    (hqr : ht (mul (mul u u) k) < ht k) :
    let q := mul (mul u u) k
    let w := mul u q
    let e := mul w (mul u k)
    ∃ z h, NF z ∧ NF h ∧ e = c w u h (mul (mul u u) q) z ∧
      ht (mul (mul u u) q) < ht z ∧ ht z < ht e ∧ ht e < ht k := by
  let q := mul (mul u u) k
  let w := mul u q
  let e := mul w (mul u k)
  obtain ⟨t,z,h,_,hnz,hnh,_,hkc,hec,_,hat,_,_,_,hhead,_,hek,_⟩ :=
    normal_second_returning_q_head hu hu hk hs hf hqr
  change k = c (mul u u) q z e t at hkc
  change e = c w u h (mul (mul u u) q) z at hec
  change mul u t = u at hat
  change max (ht u) (ht q) < ht e at hhead
  change ht e < ht k at hek
  have hkc' : NF (c (mul u u) q z e t) := hkc ▸ hk
  have htz : mul q z = t := (nf_code_actual hkc').2.2.2.2.2.2.2
  have hnq : NF q := nf_mul (nf_mul hu hu) hk
  have hne : NF e := nf_mul (nf_mul hu hnq) (nf_mul hu hk)
  have hec' : NF (c w u h (mul (mul u u) q) z) := hec ▸ hne
  have hbz := normal_fixed_code_head_order hu hnq hec'
    (by rw [← hec]; change ht q < ht e; omega)
    (by rw [htz]; exact hat)
  have heo : origin e = some (mul (mul u u) q,z) := by rw [hec]; rfl
  change ∃ z h, NF z ∧ NF h ∧ e = c w u h (mul (mul u u) q) z ∧
    ht (mul (mul u u) q) < ht z ∧ ht z < ht e ∧ ht e < ht k
  exact ⟨z,h,hnz,hnh,hec,hbz,(origin_height heo).2,hek⟩

end submission.Austin12087Trace

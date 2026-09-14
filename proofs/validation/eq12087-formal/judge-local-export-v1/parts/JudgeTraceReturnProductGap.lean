prelude
import Init.Data.Option.Lemmas
import Init.Omega
import Init.RCases
import Init.WFTactics
import JudgeTraceLargerQHeadOrder
set_option Elab.async false
/- Checked module: TraceReturnProductGap -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem nf_code_product_height_gap {a x z l r : T} (hn : NF (c a x z l r)) :
    ht (mul a x) + 2 ≤ ht (c a x z l r) := by
  have hs := (nf_code_actual hn).2.2.2.2.2.2.1
  have hi := inverse_height_strict (inverse_complete (mul a x) z)
  rw [hs] at hi
  simp only [ht]
  omega

theorem nf_return_product_height_gap {a b out : T} (hn : NF b)
    (hm : mul a b = out) (hh : ht out < ht b) :
    ht (mul a out) + 2 ≤ ht b := by
  obtain ⟨z,l,r,hc⟩ := mul_return_of_height_lt (a:=a) (b:=b) (by rw [hm]; exact hh)
  rw [hm] at hc
  have hg := nf_code_product_height_gap (hc ▸ hn)
  rw [←hc] at hg
  exact hg

theorem nf_return_target_or_key_gap {a b out : T} (hn : NF b)
    (hm : mul a b = out) (hh : ht out < ht b) :
    ht out + 3 ≤ ht b ∨ ht a + 3 ≤ ht out := by
  obtain ⟨z,l,r,hc⟩ := mul_return_of_height_lt (a:=a) (b:=b) (by rw [hm]; exact hh)
  rw [hm] at hc
  have hno := (nf_code_actual (hc ▸ hn)).2.1
  have hg := nf_return_product_height_gap hn hm hh
  rcases nf_mul_height_key_gap (a:=a) hno with hp | hp
  · exact Or.inl (by omega)
  · exact Or.inr hp.1

end submission.Austin12087Trace

prelude
import Init.Data.Option.Lemmas
import Init.Omega
import Init.RCases
import Init.WFTactics
import JudgeTraceShortReturnControl
set_option Elab.async false
/- Checked module: TraceRepeatedFixed -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem mul_commutative_only_equal {a b : T} (he : mul a b = mul b a) : a = b := by
  by_cases hh : ht b ≤ ht a
  · have hg := mul_height_growth_of_left_ge hh
    have ho := mul_origin_of_right_height_le (a:=a) (b:=b) (by omega)
    have ho' := mul_origin_of_right_height_le (a:=b) (b:=a) (by rw [←he]; omega)
    rw [←he] at ho'
    exact (Prod.mk.inj (Option.some.inj (ho.symm.trans ho'))).1
  · have hg := mul_height_growth_of_left_ge (a:=b) (b:=a) (by omega)
    have ho := mul_origin_of_right_height_le (a:=b) (b:=a) (by omega)
    have ho' := mul_origin_of_right_height_le (a:=a) (b:=b) (by rw [he]; omega)
    rw [he] at ho'
    exact (Prod.mk.inj (Option.some.inj (ho'.symm.trans ho))).1

theorem square_left_product_ne_right (a u : T) : mul (mul a u) (mul a u) ≠ u := by
  intro he
  let w := mul a u
  have hs : s w = u := by simpa only [mul_square] using he
  have hp : mul a (s w) = w := by rw [hs]
  rcases mul_height_growth_or_return a (s w) with hg | ⟨x,z,l,r,hc,_⟩
  · rw [hp] at hg
    simp only [ht] at hg
    omega
  · cases hc

theorem normal_first_repeated_fixed_head_order {u k y t : T}
    (hu : NF u) (hnk : NF k)
    (hf : mul (mul y u) k = mul (mul u (mul u (mul u k))) u)
    (hne : u ≠ k) (hs : sz u ≤ sz k)
    (hfixed : mul (mul y u) k = mul y u)
    (hc : mul u k = c u (mul u (mul u k)) t u k) :
    ht t ≤ ht (mul u (mul u k)) := by
  by_cases hh : ht t ≤ ht (mul u (mul u k))
  · exact hh
  · have he := (normal_first_repeated_tail_descent hu hnk hf hne hs hc (by omega)).1
    rw [hfixed] at he
    have hw : mul y u = mul (mul u (mul u (mul u k))) u := hfixed.symm.trans hf
    rw [hw] at he
    exact False.elim (square_left_product_ne_right _ _ he)

end submission.Austin12087Trace

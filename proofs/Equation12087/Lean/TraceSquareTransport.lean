prelude
import TraceSecondReturningQ
set_option autoImplicit false

namespace Austin12087Trace
open T

theorem square_column_transport_impossible (w y r : T) :
    mul (mul y w) (mul (mul w w) r) ≠
      mul (mul (mul (mul w w) r) w) r := by
  let a := mul (mul w w) r
  let b := mul a w
  let g := mul b r
  intro hf
  change mul (mul y w) a = g at hf
  have has : ht a < ht r := by
    by_cases hh : ht a < ht r
    · exact hh
    · have hag := mul_height_growth_of_right_le (a:=mul w w) (b:=r) (by change ht r ≤ ht a; omega)
      change ht a = max (ht (mul w w)) (ht r) + 1 at hag
      rw [mul_square] at hag
      simp only [ht] at hag
      have hbg := mul_height_growth_of_left_ge (a:=a) (b:=w) (by omega)
      change ht b = max (ht a) (ht w) + 1 at hbg
      have hgg := mul_height_growth_of_left_ge (a:=b) (b:=r) (by omega)
      change ht g = max (ht b) (ht r) + 1 at hgg
      have ho := mul_origin_of_right_height_le (a:=mul y w) (b:=a) (by rw [hf]; omega)
      rw [hf] at ho
      have ho' := mul_origin_of_right_height_le (a:=b) (b:=r) (by change ht r ≤ ht g; omega)
      change origin g = some (b,r) at ho'
      have hp := (Prod.mk.inj (Option.some.inj (ho.symm.trans ho'))).2
      have hp' := congrArg ht hp
      exact False.elim (by omega)
  have hgr : ht g < ht r := by
    by_cases hh : ht g < ht r
    · exact hh
    · have ho := mul_origin_of_right_height_le (a:=mul y w) (b:=a) (by rw [hf]; omega)
      rw [hf] at ho
      have ho' := mul_origin_of_right_height_le (a:=b) (b:=r) (by change ht r ≤ ht g; omega)
      change origin g = some (b,r) at ho'
      have hp := (Prod.mk.inj (Option.some.inj (ho.symm.trans ho'))).2
      have hp' := congrArg ht hp
      exact False.elim (by omega)
  obtain ⟨z,l,s,hr₁⟩ := mul_return_of_height_lt (a:=mul w w) (b:=r) has
  obtain ⟨z',l',s',hr₂⟩ := mul_return_of_height_lt (a:=b) (b:=r) hgr
  change r = c (mul w w) a z l s at hr₁
  change r = c b g z' l' s' at hr₂
  have hag : a = g := (T.c.inj (hr₁.symm.trans hr₂)).2.1
  exact mul_ne_right (mul y w) a (hf.trans hag.symm)

end Austin12087Trace
#print axioms Austin12087Trace.square_column_transport_impossible

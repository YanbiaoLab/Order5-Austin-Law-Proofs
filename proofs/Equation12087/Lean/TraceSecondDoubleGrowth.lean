prelude
import TraceNestedRightLadder
set_option autoImplicit false

namespace Austin12087Trace
open T

theorem normal_second_double_growth_impossible {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u)
    (hve : ht (mul a k) ≤ ht (mul (mul a (mul (mul u a) k)) (mul a k)))
    (heu : ht (mul (mul a (mul (mul u a) k)) (mul a k)) ≤ ht u) : False := by
  let g := mul u a
  let q := mul g k
  let v := mul a k
  let w := mul a q
  let e := mul w v
  change ht v ≤ ht e at hve
  change ht e ≤ ht u at heu
  change mul y e = u at hf
  have hne : NF e := nf_mul (nf_mul ha (nf_mul (nf_mul hu ha) hk)) (nf_mul ha hk)
  have heg := mul_height_growth_of_right_le (a:=w) (b:=v) hve
  change ht e = max (ht w) (ht v) + 1 at heg
  have hug := mul_height_growth_of_right_le (a:=y) (b:=e) (by rw [hf]; exact heu)
  rw [hf] at hug
  have hou := mul_origin_of_right_height_le (a:=y) (b:=e) (by rw [hf]; exact heu)
  rw [hf] at hou
  have hbounds := normal_second_query_k_dominates hu ha hk hf
  obtain ⟨z,l,r,hkc⟩ := mul_return_of_height_lt (a:=a) (b:=k) (by change ht v < ht k; omega)
  have hqg := mul_height_off_return_key (a:=g) hkc (mul_ne_right u a)
  change ht q = max (ht g) (ht k) + 1 at hqg
  have hoq := mul_origin_of_right_height_le (a:=g) (b:=k) (by change ht k ≤ ht q; omega)
  change origin q = some (g,k) at hoq
  have hnq : NF q := nf_mul (nf_mul hu ha) hk
  have hl : ReturnLadder a a g w v q k := ⟨hnq,rfl,hoq,rfl,rfl⟩
  by_cases hag : ht a ≤ ht g
  · have hgg := mul_height_growth_of_right_le (a:=u) (b:=a) hag
    change ht g = max (ht u) (ht a) + 1 at hgg
    have hog := mul_origin_of_right_height_le (a:=u) (b:=a) hag
    change origin g = some (u,a) at hog
    exact nested_right_return_ladder_impossible hog hou (by omega)
      (by intro heq; have hh := congrArg ht heq; omega) (by omega) hl
  · have hp := nf_mul_height_key_gap (a:=u) ha
    change ht g = max (ht u) (ht a) + 1 ∨ (ht u + 3 ≤ ht a ∧ ht g + 2 ≤ ht a) at hp
    rcases hp with hp | hp
    · omega
    · exact return_ladder_dominant_impossible hl (by omega) (by omega) (by omega)

theorem normal_second_growth_order {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u) :
    ht u < ht (mul (mul a (mul (mul u a) k)) (mul a k)) ∨
      ht (mul (mul a (mul (mul u a) k)) (mul a k)) < ht (mul a k) := by
  by_cases hh : ht u < ht (mul (mul a (mul (mul u a) k)) (mul a k))
  · exact Or.inl hh
  · by_cases hv : ht (mul a k) ≤ ht (mul (mul a (mul (mul u a) k)) (mul a k))
    · exact False.elim (normal_second_double_growth_impossible hu ha hk hf hv (by omega))
    · exact Or.inr (by omega)

end Austin12087Trace
#print axioms Austin12087Trace.normal_second_double_growth_impossible
#print axioms Austin12087Trace.normal_second_growth_order

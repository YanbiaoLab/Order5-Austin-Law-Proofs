prelude
import Austin10222.UnitBounds
set_option autoImplicit false
namespace Austin10222Unit
open T

theorem mul_unit_decoder (a : T) : mul (u a) (s a) = a := by
  rw [mul.eq_def]
  simp

theorem mul_square_decode {c w : T}
    (hi : (inverse c w).isSome = true) (hm : mul w c = p w c) :
    mul c (s (p w c)) = w := by
  have h0 : c ≠ s (p w c) := by
    intro h; have hh := congrArg sz h; simp only [sz] at hh; omega
  have h1 : c ≠ s (u (s (p w c))) := by
    intro h; have hh := congrArg sz h; simp only [sz] at hh; omega
  have h2 : c ≠ u (p w c) := by
    intro h; have hh := congrArg sz h; simp only [sz] at hh; omega
  rw [mul.eq_def]
  simp [h0,h1,h2,hi,hm]

theorem mul_unit_fiber {t v : T}
    (hi : (inverse v t).isSome = true) (hm : mul t v = p t v) :
    mul (s v) (p t v) = u v := by
  have h1 : s v ≠ s (u (p t v)) := by
    intro h; have hh := congrArg sz h; simp only [sz] at hh; omega
  rw [mul.eq_def]
  simp [h1,hi,hm]

theorem mul_pair_unit_decode {t v x : T} (hi : inverse (u v) t = some x) :
    mul (u v) (p t v) = x := by
  rw [mul.eq_def]
  simp [hi]

theorem mul_pair_tail_decode {t w c x : T}
    (hi : (inverse c w).isSome = true) (hm : mul w c = p w c)
    (hx : inverse c t = some x) :
    mul c (p t (p w c)) = x := by
  have h0 : c ≠ p t (p w c) := by
    intro h; have hh := congrArg sz h; simp only [sz] at hh; omega
  have h1 : c ≠ s (u (p t (p w c))) := by
    intro h; have hh := congrArg sz h; simp only [sz] at hh; omega
  have h2 : c ≠ s (p w c) := by
    intro h; have hh := congrArg sz h; simp only [sz] at hh; omega
  have h3 : c ≠ u (p w c) := by
    intro h; have hh := congrArg sz h; simp only [sz] at hh; omega
  rw [mul.eq_def]
  simp [h0,h1,h2,h3,hi,hm,hx]

theorem inverse_sound {b out a : T} (h : inverse b out = some a) : mul a b = out := by
  rw [inverse.eq_def] at h
  repeat' first | split at h | contradiction
  all_goals simp_all only [Option.some.injEq]
  all_goals subst a
  all_goals first
    | exact mul_square _
    | exact mul_large_code _
    | exact mul_unit _
    | exact mul_unit_decoder _
    | assumption
    | (apply mul_square_decode <;> simp_all; done)
    | (apply mul_unit_fiber <;> simp_all; done)
    | (apply mul_pair_unit_decode; assumption)
    | (apply mul_pair_tail_decode <;> simp_all; done)

end Austin10222Unit
#print axioms Austin10222Unit.mul_unit_decoder
#print axioms Austin10222Unit.mul_square_decode
#print axioms Austin10222Unit.mul_unit_fiber
#print axioms Austin10222Unit.mul_pair_unit_decode
#print axioms Austin10222Unit.mul_pair_tail_decode
#print axioms Austin10222Unit.inverse_sound

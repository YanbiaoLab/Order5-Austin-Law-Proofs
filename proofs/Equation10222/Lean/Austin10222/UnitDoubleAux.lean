prelude
import Austin10222.UnitNormal
set_option autoImplicit false
namespace Austin10222Unit
open T

theorem inverse_large_pair_none {b l r : T} (hs : sz b ≤ sz (p l r)) (hn : r ≠ b) :
    inverse b (p l r) = none := by
  cases hi : inverse b (p l r) with
  | none => rfl
  | some a =>
      have hm := inverse_sound hi
      have hh : sz b ≤ sz (mul a b) := by rw [hm]; exact hs
      rcases large_output_cases hh with hp | hq | hu
      · exact False.elim (hn (T.p.inj (hp.symm.trans hm)).2.symm)
      · have he := hq.symm.trans hm; cases he
      · have he := hu.symm.trans hm; cases he

theorem inverse_unit_none (b : T) : inverse b (u b) = none := by
  cases hi : inverse b (u b) with
  | none => rfl
  | some a =>
      have hm := inverse_sound hi
      have hh : sz b ≤ sz (mul a b) := by rw [hm]; simp only [sz]; omega
      rcases large_output_cases hh with hp | hq | hu
      · have he := hp.symm.trans hm; cases he
      · have he := hq.symm.trans hm; cases he
      · exact False.elim (u_ne_self b (T.u.inj (hu.symm.trans hm)))

theorem small_unit_raw {c v : T} (hs : sz c < sz v) :
    mul c (u v) = p c (u v) := by
  have h1 : c ≠ u v := by
    intro h; have hh := congrArg sz h; simp only [sz] at hh; omega
  have h2 : c ≠ s (u (u v)) := by
    intro h; have hh := congrArg sz h; simp only [sz] at hh; omega
  have h3 : c ≠ v := by intro h; subst c; omega
  rw [mul.eq_def]
  simp [h1,h2,h3]

theorem inverse_unit_small_key {c v t : T} (hs : sz c < sz v)
    (hi : inverse (u v) t = some c) : inverse c t = none := by
  have ht : t = p c (u v) := (inverse_sound hi).symm.trans (small_unit_raw hs)
  rw [ht]
  apply inverse_large_pair_none
  · simp only [sz]; omega
  · intro h; have hh := congrArg sz h; simp only [sz] at hh; omega

theorem inverse_small_unit_value {c v t : T} (hs : sz c < sz v)
    (hi : inverse c t = some (u v)) : inverse (u v) t = none := by
  have hr : mul (u v) c = p (u v) c := by
    apply bigger_key_raw
    · simp only [sz]; omega
    · intro h; cases h
  have ht := (inverse_sound hi).symm.trans hr
  rw [ht]
  apply inverse_large_pair_none
  · simp only [sz]; omega
  · intro h; have hh := congrArg sz h; simp only [sz] at hh; omega

theorem inverse_square_tail_value {w c t : T}
    (hi : inverse c t = some (s (p w c))) : inverse (p w c) t = none := by
  have hr : mul (s (p w c)) c = p (s (p w c)) c := by
    apply bigger_key_raw
    · simp only [sz]; omega
    · intro h; have hh := T.s.inj h; cases hh
  have ht := (inverse_sound hi).symm.trans hr
  rw [ht]
  apply inverse_large_pair_none
  · simp only [sz]; omega
  · intro h; have hh := congrArg sz h; simp only [sz] at hh; omega

theorem inverse_base_excludes_unit {v t : T} (hi : (inverse v t).isSome = true) :
    inverse (u v) t = none := by
  cases hq : inverse (u v) t with
  | none => rfl
  | some x =>
      rw [inverse_unit_excludes_base hq] at hi
      cases hi

theorem unit_decoder_second_raw (v : T) : mul v (s v) = p v (s v) := by
  have h1 : v ≠ s v := by intro h; have hh := congrArg sz h; simp only [sz] at hh; omega
  have h2 : v ≠ s (u (s v)) := by intro h; have hh := congrArg sz h; simp only [sz] at hh; omega
  have h3 : v ≠ u v := Ne.symm (u_ne_self v)
  rw [mul.eq_def]
  simp only [h1,h2,h3,↓reduceIte]
  cases v with
  | atom n => rfl
  | s a => rfl
  | u a => rfl
  | p w c =>
      have hn : p w c ≠ c := by intro h; have hh := congrArg sz h; simp only [sz] at hh; omega
      simp [hn]

theorem square_tail_second_raw {w c : T} (hi : (inverse c w).isSome = true) :
    mul w (s (p w c)) = p w (s (p w c)) := by
  have hn : w ≠ c := by
    intro h; subst w
    cases hk : inverse c c with
    | none => rw [hk] at hi; cases hi
    | some a => exact mul_ne_right a c (inverse_sound hk)
  have h1 : w ≠ s (p w c) := by intro h; have hh := congrArg sz h; simp only [sz] at hh; omega
  have h2 : w ≠ s (u (s (p w c))) := by intro h; have hh := congrArg sz h; simp only [sz] at hh; omega
  have h3 : w ≠ u (p w c) := by intro h; have hh := congrArg sz h; simp only [sz] at hh; omega
  rw [mul.eq_def]
  simp [h1,h2,h3,hn]

theorem fiber_second_raw {t v : T} (hi : (inverse v t).isSome = true) :
    mul (u v) (p t v) = p (u v) (p t v) := by
  rw [mul.eq_def]
  simp [inverse_base_excludes_unit hi]

end Austin10222Unit
#print axioms Austin10222Unit.inverse_large_pair_none
#print axioms Austin10222Unit.inverse_unit_none
#print axioms Austin10222Unit.small_unit_raw
#print axioms Austin10222Unit.inverse_unit_small_key
#print axioms Austin10222Unit.inverse_small_unit_value
#print axioms Austin10222Unit.inverse_square_tail_value
#print axioms Austin10222Unit.inverse_base_excludes_unit
#print axioms Austin10222Unit.unit_decoder_second_raw
#print axioms Austin10222Unit.square_tail_second_raw
#print axioms Austin10222Unit.fiber_second_raw

prelude
import Austin10222.UnitInverse
set_option autoImplicit false
namespace Austin10222Unit
open T

theorem no_large_fixed_left {a b : T} (hs : sz b < sz a) : mul a b ≠ a := by
  intro he
  by_cases hr : mul a b = p a b
  · have hh := congrArg sz (he.symm.trans hr)
    simp only [sz] at hh
    omega
  · have hab : a ≠ b := by intro h; subst a; omega
    rcases nonraw_key_size hab hr with hk | hk
    · subst a
      rw [mul_large_code] at he
      cases he
    · omega

theorem same_row_small_unit {c v x : T} (hs : sz c < sz v) :
    mul x c ≠ mul x (u v) := by
  intro he
  by_cases h1 : x = u v
  · subst x
    rw [mul_square] at he
    have hr : mul (u v) c = p (u v) c := by
      apply bigger_key_raw
      · simp only [sz]; omega
      · intro h; cases h
    rw [hr] at he
    cases he
  · by_cases h2 : x = s (u (u v))
    · subst x
      rw [mul_large_code] at he
      have hr : mul (s (u (u v))) c = p (s (u (u v))) c := by
        apply bigger_key_raw
        · simp only [sz]; omega
        · intro h
          have hh := congrArg sz h
          simp only [sz] at hh
          omega
      rw [hr] at he
      cases he
    · by_cases h3 : x = v
      · subst x
        rw [mul_unit] at he
        exact no_large_fixed_left hs he
      · have hr : mul x (u v) = p x (u v) := by
          rw [mul.eq_def]
          simp [h1,h2,h3]
        rw [hr] at he
        have hb : sz c ≤ sz (mul x c) := by rw [he]; simp only [sz]; omega
        rcases large_output_cases hb with hp | hq | hu
        · have hh := congrArg sz (T.p.inj (hp.symm.trans he)).2
          simp only [sz] at hh
          omega
        · have hh := hq.symm.trans he; cases hh
        · have hh := hu.symm.trans he; cases hh

theorem inverse_unit_excludes_base {v t x : T} (h : inverse (u v) t = some x) :
    inverse v t = none := by
  cases hg : inverse v t with
  | none => rfl
  | some y =>
      exact False.elim (column_unit_disjoint v y x
        ((inverse_sound hg).trans (inverse_sound h).symm))

theorem inverse_small_unit_different {c v t x : T} (hs : sz c < sz v)
    (h : inverse c t = some x) : inverse (u v) t ≠ some x := by
  intro hk
  exact same_row_small_unit hs ((inverse_sound h).trans (inverse_sound hk).symm)

theorem inverse_unit_value_excludes_larger {c v t : T} (hs : sz c < sz v)
    (h : inverse c t = some (u v)) : inverse v t = none := by
  have hr : mul (u v) c = p (u v) c := by
    apply bigger_key_raw
    · simp only [sz]; omega
    · intro he; cases he
  have ht : t = p (u v) c := (inverse_sound h).symm.trans hr
  cases hg : inverse v t with
  | none => rfl
  | some y =>
      have hy : mul y v = p (u v) c := (inverse_sound hg).trans ht
      have hb : sz v ≤ sz (mul y v) := by rw [hy]; simp only [sz]; omega
      rcases large_output_cases hb with hp | hq | hu
      · have hh := congrArg sz (T.p.inj (hp.symm.trans hy)).2
        omega
      · have hh := hq.symm.trans hy; cases hh
      · have hh := hu.symm.trans hy; cases hh

end Austin10222Unit
#print axioms Austin10222Unit.no_large_fixed_left
#print axioms Austin10222Unit.same_row_small_unit
#print axioms Austin10222Unit.inverse_unit_excludes_base
#print axioms Austin10222Unit.inverse_small_unit_different
#print axioms Austin10222Unit.inverse_unit_value_excludes_larger

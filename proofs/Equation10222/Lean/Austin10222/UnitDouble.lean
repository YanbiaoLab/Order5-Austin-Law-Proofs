prelude
import Austin10222.UnitDoubleAux
set_option autoImplicit false
namespace Austin10222Unit
open T

theorem unit_decode_second_raw {t v x : T} (hi : inverse (u v) t = some x)
    (hr : mul t v = p t v) : mul x (p t v) = p x (p t v) := by
  have hx := inverse_unit_size hi
  have hs : sz x < sz (p t v) := by simp only [sz]; omega
  have h1 : x ≠ p t v := by intro h; have hh := congrArg sz h; omega
  have h2 : x ≠ s (u (p t v)) := by intro h; have hh := congrArg sz h; simp only [sz] at hh; omega
  have hg : ¬(x = s v ∧ (inverse v t).isSome = true ∧ mul t v = p t v) := by
    rintro ⟨_,hk,_⟩
    rw [inverse_unit_excludes_base hi] at hk
    cases hk
  have h3 : x ≠ u v := by
    intro h; subst x
    have ht : t = s (u v) := (inverse_sound hi).symm.trans (mul_square (u v))
    rw [ht,mul_large_code] at hr
    cases hr
  rw [mul.eq_def]
  dsimp only
  simp only [h1,h2,hg,h3,↓reduceIte]
  cases v with
  | atom n => rfl
  | s a => rfl
  | u a => rfl
  | p w c =>
      by_cases hk : x = c ∧ (inverse c w).isSome = true ∧ mul w c = p w c
      · have hc : inverse (u (p w c)) t = some c := hi.trans (congrArg some hk.1)
        have hn := inverse_unit_small_key (by simp only [sz]; omega) hc
        simp [hk,hn]
      · simp [hk]

theorem tail_decode_second_raw {t w c x : T}
    (hi : (inverse c w).isSome = true) (hm : mul w c = p w c)
    (hx : inverse c t = some x) (hr : mul t (p w c) = p t (p w c)) :
    mul x (p t (p w c)) = p x (p t (p w c)) := by
  have hs := inverse_nested_pair_size (w:=w) hx
  have h1 : x ≠ p t (p w c) := by intro h; have hh := congrArg sz h; omega
  have h2 : x ≠ s (u (p t (p w c))) := by intro h; have hh := congrArg sz h; simp only [sz] at hh hs; omega
  have hg : ¬(x = s (p w c) ∧ (inverse (p w c) t).isSome = true ∧
      mul t (p w c) = p t (p w c)) := by
    rintro ⟨he,hj,_⟩
    subst x
    rw [inverse_square_tail_value hx] at hj
    cases hj
  have h3 : x ≠ c := by
    intro he; subst x
    have ht : t = s c := (inverse_sound hx).symm.trans (mul_square c)
    rw [ht,mul_unit_fiber hi hm] at hr
    cases hr
  by_cases h4 : x = u (p w c)
  · have hk : inverse c t = some (u (p w c)) := by rw [←h4]; exact hx
    have hn := inverse_small_unit_value (by simp only [sz]; omega) hk
    rw [mul.eq_def]
    simp [h1,h2,hg,h4,hn]
  · rw [mul.eq_def]
    simp [h1,h2,hg,h3,h4]

theorem column_double_cases (a b : T) (hb : NF b) :
    (b = u a ∧ mul a b = a) ∨ mul (mul a b) b = p (mul a b) b := by
  have raw (a b : T) (hr : mul a b = p a b) :
      (b = u a ∧ mul a b = a) ∨ mul (mul a b) b = p (mul a b) b := by
    right; rw [hr]; exact pair_column_raw a b
  by_cases h1 : a = b
  · subst a; right; rw [mul_square]; exact square_column_raw b
  by_cases h2 : a = s (u b)
  · subst a; right; rw [mul_large_code]; exact large_output_column_raw b
  cases b with
  | atom n => apply raw; rw [mul.eq_def]; simp [h1,h2]
  | u v =>
      by_cases h3 : a = v
      · subst a; exact Or.inl ⟨rfl,mul_unit v⟩
      · apply raw; rw [mul.eq_def]; simp [h1,h2,h3]
  | s v =>
      by_cases h3 : a = u v
      · subst a; right; rw [mul_unit_decoder]; exact unit_decoder_second_raw v
      cases v with
      | atom n => apply raw; rw [mul.eq_def]; simp [h1,h2,h3]
      | s w => apply raw; rw [mul.eq_def]; simp [h1,h2,h3]
      | u w => apply raw; rw [mul.eq_def]; simp [h1,h2,h3]
      | p w c =>
          by_cases hg : a = c ∧ (inverse c w).isSome = true ∧ mul w c = p w c
          · rcases hg with ⟨rfl,hi,hm⟩
            right; rw [mul_square_decode hi hm]; exact square_tail_second_raw hi
          · apply raw; rw [mul.eq_def]; simp [h1,h2,h3,hg]
  | p t v =>
      by_cases hg : a = s v ∧ (inverse v t).isSome = true ∧ mul t v = p t v
      · rcases hg with ⟨rfl,hi,hm⟩
        right; rw [mul_unit_fiber hi hm]; exact fiber_second_raw hi
      by_cases h3 : a = u v
      · subst a
        cases hi : inverse (u v) t with
        | some x =>
            right; rw [mul_pair_unit_decode hi]; exact unit_decode_second_raw hi hb.2.2
        | none => apply raw; rw [mul.eq_def]; simp [h1,h2,hg,hi]
      cases v with
      | atom n => apply raw; rw [mul.eq_def]; simp [h1,h2,h3,hg]
      | s w => apply raw; rw [mul.eq_def]; simp [h1,h2,h3,hg]
      | u w => apply raw; rw [mul.eq_def]; simp [h1,h2,h3,hg]
      | p w c =>
          by_cases hk : a = c ∧ (inverse c w).isSome = true ∧ mul w c = p w c
          · rcases hk with ⟨rfl,hi,hm⟩
            cases hx : inverse a t with
            | some x =>
                right; rw [mul_pair_tail_decode hi hm hx]
                exact tail_decode_second_raw hi hm hx hb.2.2
            | none => apply raw; rw [mul.eq_def]; simp [h1,h2,h3,hg,hi,hm,hx]
          · apply raw; rw [mul.eq_def]; simp [h1,h2,h3,hg,hk]

end Austin10222Unit
#print axioms Austin10222Unit.unit_decode_second_raw
#print axioms Austin10222Unit.tail_decode_second_raw
#print axioms Austin10222Unit.column_double_cases

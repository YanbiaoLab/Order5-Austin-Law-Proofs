prelude
import Austin10222.UnitConflicts
set_option autoImplicit false
namespace Austin10222Unit
open T

def inverseTail (b out : T) : Option T := match b with
  | atom _ => none
  | u v => if out = v then some v else none
  | s v =>
      if out = v then some (u v)
      else match v with
      | p w c =>
          if out = w ∧ (inverse c w).isSome ∧ mul w c = v then some c else none
      | _ => none
  | p t v =>
      if out = u v ∧ (inverse v t).isSome ∧ mul t v = b then some (s v)
      else if inverse (u v) t = some out then some (u v)
      else match v with
      | p w c =>
          if (inverse c w).isSome ∧ mul w c = v ∧ inverse c t = some out then some c else none
      | _ => none

theorem inverse_small {b out : T} (hs : sz out < sz b) :
    inverse b out = inverseTail b out := by
  have h1 : out ≠ s b := by
    intro h; have hh := congrArg sz h; simp only [sz] at hh; omega
  have h2 : out ≠ u (u b) := by
    intro h; have hh := congrArg sz h; simp only [sz] at hh; omega
  rw [inverse.eq_def]
  simp only [h1,h2,↓reduceIte]
  cases out with
  | atom n => rfl
  | s a => rfl
  | u a => rfl
  | p a c =>
      have hn : c ≠ b := by
        intro h; subst c; simp only [sz] at hs; omega
      simp only [hn,false_and,↓reduceIte,inverseTail]
      all_goals rfl

theorem inverse_square (b : T) : inverse b (s b) = some b := by
  rw [inverse.eq_def]
  simp

theorem inverse_large (b : T) : inverse b (u (u b)) = some (s (u b)) := by
  rw [inverse.eq_def]
  simp

theorem inverse_raw {a b : T} (h : mul a b = p a b) :
    inverse b (p a b) = some a := by
  rw [inverse.eq_def]
  simp [h]

theorem inverse_unit_fixed (a : T) : inverse (u a) a = some a := by
  rw [inverse_small (by simp only [sz]; omega)]
  simp [inverseTail]

theorem inverse_unit_decoder (a : T) : inverse (s a) a = some (u a) := by
  rw [inverse_small (by simp only [sz]; omega)]
  simp [inverseTail]

theorem inverse_square_tail {c w : T}
    (hi : (inverse c w).isSome = true) (hm : mul w c = p w c) :
    inverse (s (p w c)) w = some c := by
  have hs : sz w < sz (s (p w c)) := by simp only [sz]; omega
  have hn : w ≠ p w c := by
    intro h; have hh := congrArg sz h; simp only [sz] at hh; omega
  rw [inverse_small hs]
  simp [inverseTail,hn,hi,hm]

theorem inverse_pair_fiber {t v : T}
    (hi : (inverse v t).isSome = true) (hm : mul t v = p t v) :
    inverse (p t v) (u v) = some (s v) := by
  rw [inverse_small (unit_lt_pair t v)]
  simp [inverseTail,hi,hm]

theorem inverse_pair_unit {t v x : T} (hi : inverse (u v) t = some x) :
    inverse (p t v) x = some (u v) := by
  have hx := inverse_unit_size hi
  have hs : sz x < sz (p t v) := by simp only [sz]; omega
  rw [inverse_small hs]
  simp [inverseTail,inverse_unit_excludes_base hi,hi]

theorem inverse_pair_tail {t w c x : T}
    (hi : (inverse c w).isSome = true) (hm : mul w c = p w c)
    (hx : inverse c t = some x) :
    inverse (p t (p w c)) x = some c := by
  have hs : sz c < sz (p w c) := by simp only [sz]; omega
  have hn : ¬(x = u (p w c) ∧ (inverse (p w c) t).isSome = true ∧
      mul t (p w c) = p t (p w c)) := by
    rintro ⟨he,hj,_⟩
    subst x
    rw [inverse_unit_value_excludes_larger hs hx] at hj
    cases hj
  rw [inverse_small (inverse_nested_pair_size hx)]
  simp only [inverseTail,hn,inverse_small_unit_different hs hx,↓reduceIte]
  simp [hi,hm,hx]

theorem inverse_complete (a b : T) : inverse b (mul a b) = some a := by
  have raw (a b : T) (hr : mul a b = p a b) : inverse b (mul a b) = some a := by
    rw [hr]; exact inverse_raw hr
  by_cases h1 : a = b
  · subst a; rw [mul_square]; exact inverse_square b
  by_cases h2 : a = s (u b)
  · subst a; rw [mul_large_code]; exact inverse_large b
  cases b with
  | atom n =>
      apply raw; rw [mul.eq_def]; simp [h1,h2]
  | u v =>
      by_cases h3 : a = v
      · subst a; rw [mul_unit]; exact inverse_unit_fixed v
      · apply raw; rw [mul.eq_def]; simp [h1,h2,h3]
  | s v =>
      by_cases h3 : a = u v
      · subst a; rw [mul_unit_decoder]; exact inverse_unit_decoder v
      cases v with
      | atom n => apply raw; rw [mul.eq_def]; simp [h1,h2,h3]
      | s w => apply raw; rw [mul.eq_def]; simp [h1,h2,h3]
      | u w => apply raw; rw [mul.eq_def]; simp [h1,h2,h3]
      | p w c =>
          by_cases hg : a = c ∧ (inverse c w).isSome = true ∧ mul w c = p w c
          · rcases hg with ⟨rfl,hi,hm⟩
            rw [mul_square_decode hi hm]
            exact inverse_square_tail hi hm
          · apply raw; rw [mul.eq_def]; simp [h1,h2,h3,hg]
  | p t v =>
      by_cases hg : a = s v ∧ (inverse v t).isSome = true ∧ mul t v = p t v
      · rcases hg with ⟨rfl,hi,hm⟩
        rw [mul_unit_fiber hi hm]
        exact inverse_pair_fiber hi hm
      by_cases h3 : a = u v
      · subst a
        cases hi : inverse (u v) t with
        | some x => rw [mul_pair_unit_decode hi]; exact inverse_pair_unit hi
        | none => apply raw; rw [mul.eq_def]; simp [h1,h2,hg,hi]
      cases v with
      | atom n => apply raw; rw [mul.eq_def]; simp [h1,h2,h3,hg]
      | s w => apply raw; rw [mul.eq_def]; simp [h1,h2,h3,hg]
      | u w => apply raw; rw [mul.eq_def]; simp [h1,h2,h3,hg]
      | p w c =>
          by_cases hk : a = c ∧ (inverse c w).isSome = true ∧ mul w c = p w c
          · rcases hk with ⟨rfl,hi,hm⟩
            cases hx : inverse a t with
            | some x => rw [mul_pair_tail_decode hi hm hx]; exact inverse_pair_tail hi hm hx
            | none => apply raw; rw [mul.eq_def]; simp [h1,h2,h3,hg,hi,hm,hx]
          · apply raw; rw [mul.eq_def]; simp [h1,h2,h3,hg,hk]

theorem right_injective {a b c : T} (h : mul a c = mul b c) : a = b := by
  have hh := congrArg (inverse c) h
  rw [inverse_complete,inverse_complete] at hh
  exact Option.some.inj hh

end Austin10222Unit
#print axioms Austin10222Unit.inverse_small
#print axioms Austin10222Unit.inverse_square
#print axioms Austin10222Unit.inverse_large
#print axioms Austin10222Unit.inverse_raw
#print axioms Austin10222Unit.inverse_unit_fixed
#print axioms Austin10222Unit.inverse_unit_decoder
#print axioms Austin10222Unit.inverse_square_tail
#print axioms Austin10222Unit.inverse_pair_fiber
#print axioms Austin10222Unit.inverse_pair_unit
#print axioms Austin10222Unit.inverse_pair_tail
#print axioms Austin10222Unit.inverse_complete
#print axioms Austin10222Unit.right_injective

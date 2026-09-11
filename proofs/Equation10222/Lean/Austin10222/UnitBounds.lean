prelude
import Austin10222.UnitBasic
set_option autoImplicit false
namespace Austin10222Unit
open T

theorem inverse_size {b out a : T} (h : inverse b out = some a) :
    sz a ≤ max (sz b + 2) (sz out) := by
  rw [inverse.eq_def] at h
  repeat' first | split at h | contradiction
  all_goals simp_all only [Option.some.injEq,sz]
  all_goals subst a
  all_goals try simp only [sz]
  all_goals omega

theorem inverse_unit_size {b out a : T} (h : inverse (u b) out = some a) :
    sz a ≤ sz out := by
  rw [inverse.eq_def] at h
  repeat' first | split at h | contradiction
  all_goals simp_all only [Option.some.injEq,sz]
  all_goals subst a
  all_goals try simp only [sz]
  all_goals omega

theorem unit_lt_pair (a b : T) : sz (u b) < sz (p a b) := by
  have := sz_pos a
  simp only [sz]
  omega

theorem inverse_nested_pair_size {c w t a : T} (h : inverse c t = some a) :
    sz a < sz (p t (p w c)) := by
  have hh := inverse_size h
  have ht := sz_pos t
  have hw := sz_pos w
  simp only [sz]
  omega

theorem mul_nonraw_size {a b : T} (hne : a ≠ b) (hr : mul a b ≠ p a b) :
    mul a b = u (u b) ∨ sz (mul a b) < sz b := by
  generalize he : mul a b = out at *
  rw [mul.eq_def] at he
  simp only [Option.getD] at he
  repeat' first | split at he | contradiction
  all_goals subst out
  all_goals first
    | contradiction
    | exact Or.inl rfl
    | exact Or.inr (unit_lt_pair _ _)
    | (apply Or.inr; simp_all only [sz]; omega)
    | (have hh := inverse_unit_size (show inverse (u _) _ = some _ from by assumption)
       apply Or.inr
       simp_all only [sz]
       omega)
    | (apply Or.inr; apply inverse_nested_pair_size; assumption)

theorem nonraw_key_size {a b : T} (hne : a ≠ b) (hr : mul a b ≠ p a b) :
    a = s (u b) ∨ sz a ≤ sz b := by
  generalize he : mul a b = out at *
  rw [mul.eq_def] at he
  simp only [Option.getD] at he
  repeat' first | split at he | contradiction
  all_goals subst out
  all_goals first
    | contradiction
    | (apply Or.inl; assumption)
    | (apply Or.inr; simp_all only [sz]; omega)

theorem bigger_key_raw {a b : T} (hsize : sz b < sz a) (hne : a ≠ s (u b)) :
    mul a b = p a b := by
  by_cases hr : mul a b = p a b
  · exact hr
  · have hab : a ≠ b := by intro hh; subst a; omega
    rcases nonraw_key_size hab hr with he | hs
    · exact False.elim (hne he)
    · omega

theorem pair_column_raw (a b : T) : mul (p a b) b = p (p a b) b := by
  apply bigger_key_raw
  · simp only [sz]; omega
  · intro h; cases h

theorem square_column_raw (b : T) : mul (s b) b = p (s b) b := by
  apply bigger_key_raw
  · simp only [sz]; omega
  · intro h
    exact u_ne_self b (T.s.inj h).symm

theorem large_output_column_raw (b : T) : mul (u (u b)) b = p (u (u b)) b := by
  apply bigger_key_raw
  · simp only [sz]; omega
  · intro h; cases h

theorem mul_ne_right (a b : T) : mul a b ≠ b := by
  intro he
  by_cases hab : a = b
  · subst a
    rw [mul_square] at he
    have hh := congrArg sz he
    simp only [sz] at hh
    omega
  · by_cases hr : mul a b = p a b
    · have hh := congrArg sz (hr.symm.trans he)
      simp only [sz] at hh
      omega
    · rcases mul_nonraw_size hab hr with hu | hs
      · have hh := congrArg sz (hu.symm.trans he)
        simp only [sz] at hh
        omega
      · rw [he] at hs
        omega

theorem large_output_cases {a b : T} (hs : sz b ≤ sz (mul a b)) :
    mul a b = p a b ∨ mul a b = s b ∨ mul a b = u (u b) := by
  by_cases hab : a = b
  · subst a; exact Or.inr (Or.inl (mul_square b))
  · by_cases hr : mul a b = p a b
    · exact Or.inl hr
    · rcases mul_nonraw_size hab hr with hu | ht
      · exact Or.inr (Or.inr hu)
      · omega

theorem unit_column_cases (a b : T) :
    mul a (u b) = b ∨ mul a (u b) = s (u b) ∨
      mul a (u b) = u (u (u b)) ∨ mul a (u b) = p a (u b) := by
  rw [mul.eq_def]
  dsimp only
  split
  · rename_i h; subst a; exact Or.inr (Or.inl rfl)
  · split
    · exact Or.inr (Or.inr (Or.inl rfl))
    · split
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inr rfl))

theorem column_unit_disjoint (a x z : T) : mul x a ≠ mul z (u a) := by
  intro he
  rcases unit_column_cases z a with hf | hf | hf | hf
  · exact mul_ne_right x a (he.trans hf)
  · have h := he.trans hf
    have hs : sz a ≤ sz (mul x a) := by rw [h]; simp only [sz]; omega
    rcases large_output_cases hs with hp | hq | hu
    · have hh := hp.symm.trans h; cases hh
    · exact u_ne_self a (T.s.inj (hq.symm.trans h)).symm
    · have hh := hu.symm.trans h; cases hh
  · have h := he.trans hf
    have hs : sz a ≤ sz (mul x a) := by rw [h]; simp only [sz]; omega
    rcases large_output_cases hs with hp | hq | hu
    · have hh := hp.symm.trans h; cases hh
    · have hh := hq.symm.trans h; cases hh
    · have hh := congrArg sz (hu.symm.trans h)
      simp only [sz] at hh
      omega
  · have h := he.trans hf
    have hs : sz a ≤ sz (mul x a) := by rw [h]; simp only [sz]; omega
    rcases large_output_cases hs with hp | hq | hu
    · have hh := hp.symm.trans h
      exact u_ne_self a (T.p.inj hh).2.symm
    · have hh := hq.symm.trans h; cases hh
    · have hh := hu.symm.trans h; cases hh

end Austin10222Unit
#print axioms Austin10222Unit.inverse_size
#print axioms Austin10222Unit.inverse_unit_size
#print axioms Austin10222Unit.mul_nonraw_size
#print axioms Austin10222Unit.nonraw_key_size
#print axioms Austin10222Unit.bigger_key_raw
#print axioms Austin10222Unit.pair_column_raw
#print axioms Austin10222Unit.square_column_raw
#print axioms Austin10222Unit.large_output_column_raw
#print axioms Austin10222Unit.mul_ne_right
#print axioms Austin10222Unit.large_output_cases
#print axioms Austin10222Unit.unit_column_cases
#print axioms Austin10222Unit.column_unit_disjoint

prelude
import Init.Core
import Init.Classical
import Init.Data.Option.Lemmas
import Init.WFTactics
import Init.Omega
import Init.RCases

class Magma (G : Type _) where
  op : G → G → G
infix:65 " ◇ " => Magma.op

@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop :=
  ∀ (x y z : G), x = ((y ◇ (y ◇ z)) ◇ (y ◇ x)) ◇ y
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x y : G), x = y
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G

set_option autoImplicit false

namespace Austin10222Unit

inductive T where
  | atom : Nat → T
  | s : T → T
  | u : T → T
  | p : T → T → T
  deriving DecidableEq

open T

def sz : T → Nat
  | atom _ => 1
  | s a => sz a + 1
  | u a => sz a + 1
  | p a b => sz a + sz b + 1

theorem sz_pos (a : T) : 0 < sz a := by cases a <;> simp only [sz] <;> omega

mutual
def mul (a b : T) : T :=
  if a = b then s a
  else if a = s (u b) then u (u b)
  else match b with
  | atom _ => p a b
  | u v => if a = v then v else p a b
  | s v =>
      if a = u v then v
      else match v with
      | p w c =>
          if a = c ∧ (inverse c w).isSome ∧ mul w c = v then w else p a b
      | _ => p a b
  | p u0 v =>
      if a = s v ∧ (inverse v u0).isSome ∧ mul u0 v = b then u v
      else if a = u v then (inverse (u v) u0).getD (p a b)
      else match v with
      | p w c =>
          if a = c ∧ (inverse c w).isSome ∧ mul w c = v then
            (inverse c u0).getD (p a b)
          else p a b
      | _ => p a b
termination_by sz a + sz b
decreasing_by
  all_goals have ha := sz_pos a; have hb := sz_pos b
  all_goals simp_wf; simp_all only [sz]; omega

def inverse (b out : T) : Option T :=
  if out = s b then some b
  else if out = u (u b) then some (s (u b))
  else
    let rest : Option T := match b with
      | atom _ => none
      | u v => if out = v then some v else none
      | s v =>
          if out = v then some (u v)
          else match v with
          | p w c =>
              if out = w ∧ (inverse c w).isSome ∧ mul w c = v then some c else none
          | _ => none
      | p u0 v =>
          if out = u v ∧ (inverse v u0).isSome ∧ mul u0 v = b then some (s v)
          else if inverse (u v) u0 = some out then some (u v)
          else match v with
          | p w c =>
              if (inverse c w).isSome ∧ mul w c = v ∧ inverse c u0 = some out then some c
              else none
          | _ => none
    match out with
    | p a b' => if b' = b ∧ mul a b = out then some a else rest
    | _ => rest
termination_by sz b + sz out
decreasing_by
  all_goals have hb := sz_pos b; have ho := sz_pos out
  all_goals simp_wf; simp_all only [sz]; omega
end

def NF : T → Prop
  | atom _ => True
  | s a => NF a
  | u a => NF a
  | p a b => NF a ∧ NF b ∧ mul a b = p a b

theorem u_ne_self (a : T) : u a ≠ a := by
  intro h
  have := congrArg sz h
  simp only [sz] at this
  omega

theorem su_ne_self (a : T) : s (u a) ≠ a := by
  intro h
  have := congrArg sz h
  simp only [sz] at this
  omega

theorem mul_square (a : T) : mul a a = s a := by
  rw [mul.eq_def]
  simp only [↓reduceIte]

theorem mul_unit (a : T) : mul a (u a) = a := by
  have h1 : a ≠ u a := Ne.symm (u_ne_self a)
  have h2 : a ≠ s (u (u a)) := by
    intro h
    have := congrArg sz h
    simp only [sz] at this
    omega
  rw [mul.eq_def]
  simp only [h1,h2,↓reduceIte]

theorem mul_large_code (b : T) : mul (s (u b)) b = u (u b) := by
  rw [mul.eq_def]
  simp only [su_ne_self b,↓reduceIte]

theorem nf_atom (n : Nat) : NF (atom n) := True.intro
theorem atom_injective (m n : Nat) (h : (atom m : T) = atom n) : m = n := T.atom.inj h

def Law : Prop := ∀ x y z : T, NF x → NF y → NF z →
  x = mul y (mul (mul x y) (mul (mul z y) y))

-- Totality and these local equations do not establish Law or NF closure.
end Austin10222Unit


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

set_option autoImplicit false
namespace Austin10222Unit
open T

theorem inverse_tail_normal {b out a : T} (h : inverseTail b out = some a)
    (hb : NF b) : NF a := by
  unfold inverseTail at h
  repeat' first | split at h | contradiction
  all_goals simp_all only [Option.some.injEq]
  all_goals subst a
  all_goals simp_all [NF]

theorem inverse_eq_tail (b out : T) : inverse b out =
    if out = s b then some b
    else if out = u (u b) then some (s (u b))
    else match out with
    | p a c => if c = b ∧ mul a b = out then some a else inverseTail b out
    | _ => inverseTail b out := by
  rw [inverse.eq_def]
  rfl

theorem inverse_normal {b out a : T} (h : inverse b out = some a)
    (hb : NF b) (ho : NF out) : NF a := by
  rw [inverse_eq_tail] at h
  split at h
  · have he := Option.some.inj h; subst a; exact hb
  · split at h
    · have he := Option.some.inj h; subst a; exact hb
    · cases out with
      | atom n => exact inverse_tail_normal h hb
      | s v => exact inverse_tail_normal h hb
      | u v => exact inverse_tail_normal h hb
      | p v c =>
          dsimp only at h
          split at h
          · have he := Option.some.inj h; subst a; exact ho.1
          · exact inverse_tail_normal h hb

theorem mul_normal {a b : T} (ha : NF a) (hb : NF b) : NF (mul a b) := by
  generalize he : mul a b = out
  have original := he
  rw [mul.eq_def] at he
  simp only [Option.getD] at he
  repeat' first | split at he | contradiction
  all_goals cases he
  all_goals try simp only [NF] at ha hb ⊢
  all_goals first
    | exact ⟨ha,hb,original⟩
    | assumption
    | exact hb.1
    | exact hb.2.1
    | exact hb.1.1
    | exact hb.2.1.2.1
    | (apply inverse_normal (show inverse _ _ = some _ from by assumption) <;>
        first | assumption | exact hb.1 | exact hb.2.1 | exact hb.2.1.2.1)

abbrev Carrier := {a : T // NF a}
def embed (n : Nat) : Carrier := ⟨atom n,nf_atom n⟩
theorem embed_injective (m n : Nat) (h : embed m = embed n) : m = n := by
  exact atom_injective m n (congrArg Subtype.val h)

def carrierMul (a b : Carrier) : Carrier := ⟨mul a.val b.val,mul_normal a.property b.property⟩

end Austin10222Unit

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

set_option autoImplicit false
namespace Austin10222Unit
open T

theorem inverse_self_none (a : T) : inverse a a = none := by
  cases hi : inverse a a with
  | none => rfl
  | some x => exact False.elim (mul_ne_right x a (inverse_sound hi))

theorem inverse_double_key_none {w c : T} (hi : (inverse c w).isSome = true) :
    inverse (p w c) c = none := by
  have hs : sz c < sz (p w c) := by simp only [sz]; omega
  have h1 : c ≠ u c := Ne.symm (u_ne_self c)
  have h2 : inverse (u c) w ≠ some c := by
    intro h
    have hw : w = c := (inverse_sound h).symm.trans (mul_unit c)
    rw [hw,inverse_self_none] at hi
    cases hi
  rw [inverse_small hs]
  simp only [inverseTail,h1,h2,false_and,↓reduceIte]
  cases c with
  | atom n => rfl
  | s a => rfl
  | u a => rfl
  | p t d =>
      have hn : ¬((inverse d t).isSome = true ∧ mul t d = p t d ∧
          inverse d w = some (p t d)) := by
        rintro ⟨_,_,hx⟩
        have hw : w = p (p t d) d := (inverse_sound hx).symm.trans (pair_column_raw t d)
        have hz : inverse (p t d) w = none := by
          rw [hw]
          apply inverse_large_pair_none
          · simp only [sz]; omega
          · intro h; have hh := congrArg sz h; simp only [sz] at hh; omega
        rw [hz] at hi
        cases hi
      simp [hn]

theorem image_not_large_pair_key {x y v : T} :
    mul x y ≠ s (u (p v y)) := by
  intro he
  have hs : sz y ≤ sz (mul x y) := by rw [he]; simp only [sz]; omega
  rcases large_output_cases hs with hp | hq | hu
  · have hh := hp.symm.trans he; cases hh
  · have hh := congrArg sz (hq.symm.trans he)
    simp only [sz] at hh
    omega
  · have hh := hu.symm.trans he; cases hh

theorem source_middle_raw {u0 v y x : T}
    (hi : inverse y u0 = some x) (hv : (inverse y v).isSome = true)
    (hm : mul v y = p v y) (h1 : u0 ≠ p v y) (h2 : u0 ≠ s y) :
    mul u0 (p v y) = p u0 (p v y) := by
  have h3 : u0 ≠ s (u (p v y)) := by
    intro h
    exact image_not_large_pair_key ((inverse_sound hi).trans h)
  have h4 : u0 ≠ u y := by
    intro h; rw [h,inverse_unit_none] at hi; cases hi
  rw [mul.eq_def]
  dsimp only
  simp only [h1,h2,h3,h4,false_and,↓reduceIte]
  cases y with
  | atom n => rfl
  | s a => rfl
  | u a => rfl
  | p w c =>
      have hn : ¬(u0 = c ∧ (inverse c w).isSome = true ∧ mul w c = p w c) := by
        rintro ⟨he,hj,_⟩
        have hx : inverse (p w c) c = some x :=
          (congrArg (inverse (p w c)) he).symm.trans hi
        rw [inverse_double_key_none hj] at hx
        cases hx
      simp [hn]

theorem source_raw_double (x y v : T) (hv : (inverse y v).isSome = true)
    (hm : mul v y = p v y) :
    x = mul y (mul (mul x y) (p v y)) := by
  have hi := inverse_complete x y
  by_cases h1 : mul x y = p v y
  · have hx : x = v := right_injective (h1.trans hm.symm)
    rw [h1,mul_square,mul_square_decode hv hm]
    exact hx
  by_cases h2 : mul x y = s y
  · have hx : x = y := right_injective (h2.trans (mul_square y).symm)
    rw [h2,mul_unit_fiber hv hm,mul_unit]
    exact hx
  rw [source_middle_raw hi hv hm h1 h2,mul_pair_tail_decode hv hm hi]

theorem fixed_middle_raw {x z : T} (h1 : x ≠ z) (h2 : x ≠ u z) :
    mul (mul x (u z)) z = p (mul x (u z)) z := by
  rcases unit_column_cases x z with hu | hu | hu | hu
  · exact False.elim (h1 (right_injective (hu.trans (mul_unit z).symm)))
  · exact False.elim (h2 (right_injective (hu.trans (mul_square (u z)).symm)))
  · rw [hu]
    apply bigger_key_raw
    · simp only [sz]; omega
    · intro h; cases h
  · rw [hu]
    apply bigger_key_raw
    · simp only [sz]; omega
    · intro h; cases h

theorem source_unit_middle (x z : T) :
    x = mul (u z) (mul (mul x (u z)) z) := by
  by_cases h1 : x = z
  · subst x; rw [mul_unit,mul_square,mul_unit_decoder]
  by_cases h2 : x = u z
  · subst x; rw [mul_square,mul_large_code,mul_unit]
  rw [fixed_middle_raw h1 h2,mul_pair_unit_decode (inverse_complete x (u z))]

theorem source_of_normal_middle (x y z : T) (hy : NF y) :
    x = mul y (mul (mul x y) (mul (mul z y) y)) := by
  rcases column_double_cases z y hy with ⟨he,_⟩ | hd
  · subst y
    rw [mul_unit,mul_unit]
    exact source_unit_middle x z
  · rw [hd]
    apply source_raw_double
    · rw [inverse_complete]; rfl
    · exact hd

theorem source_holds : Law := by
  intro x y z _ hy _
  exact source_of_normal_middle x y z hy

theorem carrier_source (x y z : Carrier) :
    x = carrierMul y (carrierMul (carrierMul x y) (carrierMul (carrierMul z y) y)) := by
  apply Subtype.ext
  exact source_of_normal_middle x.val y.val z.val y.property

theorem carrier_dual (x y z : Carrier) :
    x = (fun a b => carrierMul b a)
      ((fun a b => carrierMul b a)
        ((fun a b => carrierMul b a) y ((fun a b => carrierMul b a) y z))
        ((fun a b => carrierMul b a) y x)) y := carrier_source x y z

theorem carrier_nontrivial : embed 0 ≠ embed 1 := by
  intro h
  have hh := embed_injective 0 1 h
  cases hh

end Austin10222Unit

namespace submission
abbrev CM := Austin10222Unit.Carrier
namespace CM
theorem tower_injective (m n : Nat)
    (h : Austin10222Unit.embed m = Austin10222Unit.embed n) : m = n :=
  Austin10222Unit.embed_injective m n h
end CM
instance modelMagma : Magma CM := ⟨fun a b => Austin10222Unit.carrierMul b a⟩
end submission

theorem submission : Goal := by
  refine ⟨submission.CM,submission.modelMagma,?_,?_⟩
  · intro x y z
    exact Austin10222Unit.carrier_dual x y z
  · intro h
    exact Austin10222Unit.carrier_nontrivial
      (h (Austin10222Unit.embed 0) (Austin10222Unit.embed 1))

example : Goal := submission
#print axioms submission
#print axioms submission.CM.tower_injective

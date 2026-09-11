prelude
import Init.Data.Option.Lemmas
import Init.WFTactics
import Init.Omega
import Init.RCases
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

#print axioms Austin10222Unit.mul
#print axioms Austin10222Unit.inverse
#print axioms Austin10222Unit.mul_square
#print axioms Austin10222Unit.mul_unit
#print axioms Austin10222Unit.mul_large_code
#print axioms Austin10222Unit.nf_atom
#print axioms Austin10222Unit.atom_injective

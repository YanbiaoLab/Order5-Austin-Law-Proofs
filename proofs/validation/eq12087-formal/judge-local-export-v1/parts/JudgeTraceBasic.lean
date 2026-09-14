prelude
import Init.Data.Option.Lemmas
import Init.Omega
import Init.RCases
import Init.WFTactics
set_option Elab.async false
/- Checked module: TraceBasic -/
set_option autoImplicit false

namespace submission.Austin12087Trace

inductive T where
  | atom : Nat → T
  | s : T → T
  | p : T → T → T
  | c : T → T → T → T → T → T
  deriving DecidableEq

open T

def sz : T → Nat
  | atom _ => 1
  | s a => sz a + 1
  | p a b => sz a + sz b + 1
  | c y x z a b => sz y + sz x + sz z + sz a + sz b + 1

theorem sz_pos (a : T) : 0 < sz a := by cases a <;> simp only [sz] <;> omega

def rankM (a b : T) := 3 * max (sz a) (sz b) + 2
def rankI (a b : T) := 3 * max (sz a) (sz b) + 1

def origin : T → Option (T × T)
  | atom _ => none
  | s a => some (a,a)
  | p a b => some (a,b)
  | c _ _ _ a b => some (a,b)

theorem origin_size {t a b : T} (h : origin t = some (a,b)) :
    sz a < sz t ∧ sz b < sz t := by
  cases t <;> simp only [origin, Option.some.injEq, Prod.mk.injEq] at h
  · cases h
  all_goals rcases h with ⟨rfl,rfl⟩; simp only [sz]; omega

def leftCode (m i : T → T → Option T) (a b : T) : Option T :=
  match origin a with
  | none => none
  | some (u,z) => match m u z with
    | none => none
    | some value => if value = a then
        match i z b with
        | none => none
        | some x => match i x u with
          | none => none
          | some y => some (c y x z a b)
      else none

def rightCode (m i : T → T → Option T) (a b : T) : Option T :=
  match origin b with
  | none => none
  | some (x,z) => match m x z with
    | none => none
    | some value => if value = b then
        match i z a with
        | none => none
        | some u => match i x u with
          | none => none
          | some y => some (c y x z a b)
      else none

def decode (m i : T → T → Option T) (a b : T) : T :=
  match leftCode m i a b with
  | some out => out
  | none => (rightCode m i a b).getD (p a b)

def basicInverse (b out : T) : Option T :=
  match b with
  | c y x _ _ _ => if out = x then some y else none
  | _ => none

mutual
def mul (a b : T) : T :=
  if a = b then s a
  else
    let raw : T := decode
      (fun u v => if h : rankM u v < rankM a b then some (mul u v) else none)
      (fun u v => if h : rankI u v < rankM a b then inverse u v else none) a b
    match b with
    | c y x _ _ _ => if a = y then x else raw
    | _ => raw
termination_by rankM a b

def inverse (b out : T) : Option T :=
  if out = s b then some b
  else
    let rest := basicInverse b out
    match ho : out with
    | p a b' =>
        if b' = b then
          if h : rankM a b < rankI b out then
            if mul a b = out then some a else rest
          else rest
        else rest
    | c _ _ _ a b' =>
        if b' = b then
          if h : rankM a b < rankI b out then
            if mul a b = out then some a else rest
          else rest
        else rest
    | _ => rest
termination_by rankI b out
decreasing_by all_goals simpa only [ho] using h
end

def queryM (n : Nat) (a b : T) : Option T :=
  if rankM a b < n then some (mul a b) else none
def queryI (n : Nat) (a b : T) : Option T :=
  if rankI a b < n then inverse a b else none

theorem mul_equation (a b : T) : mul a b =
    if a = b then s a else
      match b with
      | c y x _ _ _ => if a = y then x else decode (queryM (rankM a b)) (queryI (rankM a b)) a b
      | _ => decode (queryM (rankM a b)) (queryI (rankM a b)) a b := by
  rw [mul.eq_def]
  rfl

theorem mul_square (a : T) : mul a a = s a := by
  rw [mul_equation]
  simp only [↓reduceIte]

theorem mul_code_return (y x z a b : T) : mul y (c y x z a b) = x := by
  have hn : y ≠ c y x z a b := by
    intro h
    have hs := congrArg sz h
    simp only [sz] at hs
    omega
  rw [mul_equation]
  simp only [hn,↓reduceIte]

theorem atom_injective (m n : Nat) (h : (atom m : T) = atom n) : m = n := T.atom.inj h

-- These total functions and local equations do not yet establish the source law.
end submission.Austin12087Trace


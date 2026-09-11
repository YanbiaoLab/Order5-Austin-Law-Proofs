import Austin21866.Separation
set_option autoImplicit false
set_option Elab.async false

namespace submission.Austin21866
open T

theorem equation21866 (x y z w : T) :
    x = op (op y (op z x)) (op x (op x w)) := by
  obtain ⟨v, hv, hr⟩ := op_row_shape (row_op x w)
  rw [hv]
  exact (op_hit (op y (op z x)) x v hr (row_back x y z)).symm

theorem equation21714 (x y z : T) :
    x = op (op y (op y x)) (op x (op x z)) := equation21866 x y y z

theorem equation21864 (x y z : T) :
    x = op (op y (op z x)) (op x (op x y)) := equation21866 x y z y

theorem equation21865 (x y z : T) :
    x = op (op y (op z x)) (op x (op x z)) := equation21866 x y z z

noncomputable def dualOp (x y : T) : T := op y x

def tower : Nat → T
  | 0 => e
  | n+1 => k (tower n)

theorem tower_size (n : Nat) : size (tower n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [tower, size, ih]

theorem tower_injective (n m : Nat) (h : tower n = tower m) : n = m := by
  have hs := congrArg size h
  simpa only [tower_size] using hs

theorem infinite_model :
    ∃ (G : Type) (f : G → G → G) (i : Nat → G),
      (∀ n m, i n = i m → n = m) ∧
      (∀ x y z w, x = f (f y (f z x)) (f x (f x w))) :=
  ⟨T, op, tower, tower_injective, equation21866⟩

end submission.Austin21866

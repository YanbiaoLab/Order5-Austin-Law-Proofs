import Confluence
set_option autoImplicit false
namespace Austin12857
open T

def Carrier := {x : T // Normal x}
noncomputable def mul (x y : Carrier) : Carrier :=
  ⟨norm (m x.val y.val), norm_normal _⟩

theorem mul_val (x y : Carrier) : (mul x y).val = norm (m x.val y.val) := rfl

theorem equation12857 (x y z : Carrier) :
    mul y (mul (mul x (mul y (mul z z))) y) = x := by
  apply Subtype.ext
  change norm (m y.val (norm (m (norm (m x.val (norm (m y.val
    (norm (m z.val z.val)))))) y.val))) = x.val
  have nx := norm_of_normal x.property
  have ny := norm_of_normal y.property
  have nz := norm_of_normal z.property
  have hl : norm (m y.val (m (m x.val (m y.val (m z.val z.val))) y.val)) = x.val := by
    have h : Steps (m y.val (m (m x.val (m y.val (m z.val z.val))) y.val)) x.val :=
      .cons (.right _ (.left _ (.right _ (.right _ (.root (.r1 z.val))))))
        (.single (.root (.r2 y.val x.val z.val)))
    exact (norm_steps h).trans nx
  -- Replace the fixed normal inputs by their normalizations to apply congruence.
  have left_norm (p q : T) : norm (m p (norm q)) = norm (m p q) := by
    exact (norm_steps (Steps.right p (steps_norm q))).symm
  have right_norm (p q : T) : norm (m (norm p) q) = norm (m p q) := by
    exact (norm_steps (Steps.left q (steps_norm p))).symm
  simp only [left_norm, right_norm]
  exact hl

def clean : T → Prop
  | a => True
  | b => True
  | s _ => False
  | m x y => clean x ∧ clean y

theorem clean_root {x y : T} (h : Root x y) (hc : clean x) : ∃ t, x = m t t := by
  cases h <;> simp only [clean, and_false, false_and] at hc
  exact ⟨_, rfl⟩

def tower : Nat → T
  | 0 => b
  | n+1 => m a (tower n)

theorem tower_clean (n : Nat) : clean (tower n) := by
  induction n with
  | zero => exact True.intro
  | succ n ih => exact ⟨True.intro, ih⟩

theorem tower_ne_a (n : Nat) : tower n ≠ a := by
  cases n <;> simp only [tower] <;> intro h <;> cases h

theorem normal_a : Normal a := by
  intro y h
  cases h with
  | root h => cases h

theorem tower_normal (n : Nat) : Normal (tower n) := by
  induction n with
  | zero =>
    intro y h
    cases h with
    | root h => cases h
  | succ n ih =>
    intro y h
    cases h with
    | root h =>
      obtain ⟨t, ht⟩ := clean_root h (tower_clean (n+1))
      have h1 := (T.m.inj ht).1
      have h2 := (T.m.inj ht).2
      exact tower_ne_a n (h2.trans h1.symm)
    | left _ h => exact normal_a h
    | right _ h => exact ih h

theorem tower_size (n : Nat) : size (tower n) = 2*n+1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [tower, size, ih]; omega

def embed (n : Nat) : Carrier := ⟨tower n, tower_normal n⟩

theorem embed_injective (n k : Nat) (h : embed n = embed k) : n = k := by
  have hh := congrArg (fun x : Carrier => size x.val) h
  change size (tower n) = size (tower k) at hh
  rw [tower_size, tower_size] at hh
  omega

noncomputable def opposite (x y : Carrier) : Carrier := mul y x

theorem equation33436 (x y z : Carrier) :
    opposite (opposite y (opposite (opposite (opposite z z) y) x)) y = x :=
  equation12857 x y z

/-- Explicit injection of Nat, in addition to the universally quantified law. -/
theorem infinite_model : ∃ (A : Type) (op : A → A → A) (f : Nat → A),
    (∀ x y z, op y (op (op x (op y (op z z))) y) = x) ∧
    (∀ n k, f n = f k → n = k) :=
  ⟨Carrier, mul, embed, equation12857, embed_injective⟩
end Austin12857

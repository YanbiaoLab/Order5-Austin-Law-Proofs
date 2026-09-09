import Confluence
set_option autoImplicit false
namespace submission.Austin13992
open T
def Carrier := {x : T // Normal x}
noncomputable def mul (x y : Carrier) : Carrier :=
  ⟨norm (m x.val y.val), norm_normal _⟩
theorem equation13992 (x y z : Carrier) :
    (mul y (mul (mul z (mul (mul x y) y)) y)) = x := by
  apply Subtype.ext
  change (norm (T.m y.val (norm (T.m (norm (T.m z.val (norm (T.m (norm (T.m x.val y.val)) y.val)))) y.val)))) = x.val
  simp only [norm_m_left, norm_m_right]
  have h : Steps (T.m y.val (T.m (T.m z.val (T.m (T.m x.val y.val) y.val)) y.val)) x.val :=
    (Steps.cons (Step.right y.val (Step.left y.val (Step.right z.val (Step.root (Root.r1 x.val y.val))))) (Steps.cons (Step.right y.val (Step.root (Root.r2 z.val x.val y.val))) (Steps.cons (Step.root (Root.r3 y.val z.val x.val)) (Steps.refl _))))
  exact (norm_steps h).trans (norm_of_normal x.property)
def tower : Nat → T
  | 0 => a
  | n+1 => k (tower n)
theorem tower_normal (n : Nat) : Normal (tower n) := by
  induction n with
  | zero =>
    intro y h
    cases h with
    | root h => cases h
  | succ n ih =>
    intro y h
    cases h with
    | root h => cases h
    | underK h => exact ih h
theorem tower_size (n : Nat) : size (tower n) = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [tower, size, ih] <;> omega
def embed (n : Nat) : Carrier := ⟨tower n, tower_normal n⟩
theorem embed_injective (n j : Nat) (h : embed n = embed j) : n = j := by
  have hh := congrArg (fun x : Carrier => size x.val) h
  change size (tower n) = size (tower j) at hh
  rw [tower_size, tower_size] at hh
  omega
noncomputable def opposite (x y : Carrier) : Carrier := mul y x
theorem equation32280 (x y z : Carrier) :
    (opposite (opposite y (opposite (opposite y (opposite y x)) z)) y) = x :=
  equation13992 x y z
theorem infinite_model : ∃ (A : Type) (op : A → A → A) (f : Nat → A),
    (∀ x y z, (op y (op (op z (op (op x y) y)) y)) = x) ∧
    (∀ n j, f n = f j → n = j) :=
  ⟨Carrier, mul, embed, equation13992, embed_injective⟩
end submission.Austin13992

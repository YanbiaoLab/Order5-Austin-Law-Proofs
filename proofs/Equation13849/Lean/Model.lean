import Confluence
set_option autoImplicit false
namespace submission.Austin13849
open T
def Carrier := {x : T // Normal x}
noncomputable def mul (x y : Carrier) : Carrier :=
  ⟨norm (m x.val y.val), norm_normal _⟩
theorem equation13849 (x y z : Carrier) :
    (mul y (mul (mul y (mul (mul x z) z)) z)) = x := by
  apply Subtype.ext
  change (norm (T.m y.val (norm (T.m (norm (T.m y.val (norm (T.m (norm (T.m x.val z.val)) z.val)))) z.val)))) = x.val
  simp only [norm_m_left, norm_m_right]
  have h : Steps (T.m y.val (T.m (T.m y.val (T.m (T.m x.val z.val) z.val)) z.val)) x.val :=
    (Steps.cons (Step.right y.val (Step.left z.val (Step.right y.val (Step.root (Root.r1 x.val z.val))))) (Steps.cons (Step.right y.val (Step.root (Root.r2 y.val x.val z.val))) (Steps.cons (Step.root (Root.r3 y.val x.val z.val)) (Steps.refl _))))
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
theorem equation32281 (x y z : Carrier) :
    (opposite (opposite y (opposite (opposite y (opposite y x)) z)) z) = x :=
  equation13849 x z y
theorem infinite_model : ∃ (A : Type) (op : A → A → A) (f : Nat → A),
    (∀ x y z, (op y (op (op y (op (op x z) z)) z)) = x) ∧
    (∀ n j, f n = f j → n = j) :=
  ⟨Carrier, mul, embed, equation13849, embed_injective⟩
end submission.Austin13849

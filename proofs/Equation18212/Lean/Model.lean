import Confluence
set_option autoImplicit false
namespace submission.Austin18212
open T
def Carrier := {x : T // Normal x}
noncomputable def mul (x y : Carrier) : Carrier :=
  ⟨norm (m x.val y.val), norm_normal _⟩
theorem equation18212 (x y z : Carrier) :
    mul (mul y y) (mul x (mul (mul x z) z)) = x := by
  apply Subtype.ext
  change norm (m (norm (m y.val y.val))
    (norm (m x.val (norm (m (norm (m x.val z.val)) z.val))))) = x.val
  simp only [norm_m_left, norm_m_right]
  have h : Steps (T.m (T.m y.val y.val) (T.m x.val (T.m (T.m x.val z.val) z.val))) x.val :=
    (Steps.cons (Step.left (T.m x.val (T.m (T.m x.val z.val) z.val)) (Step.root (Root.r1 y.val))) (Steps.cons (Step.root (Root.r5 (T.m x.val (T.m (T.m x.val z.val) z.val)))) (Steps.cons (Step.leftR (T.m x.val (T.m (T.m x.val z.val) z.val)) (Step.right x.val (Step.root (Root.r2 x.val z.val)))) (Steps.cons (Step.leftR (T.m x.val (T.m (T.m x.val z.val) z.val)) (Step.root (Root.r3 x.val z.val))) (Steps.cons (Step.rightR (T.v x.val) (Step.right x.val (Step.root (Root.r2 x.val z.val)))) (Steps.cons (Step.rightR (T.v x.val) (Step.root (Root.r3 x.val z.val))) (Steps.cons (Step.root (Root.r4 x.val)) (Steps.refl _))))))))
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
theorem equation27859 (x y z : Carrier) :
    opposite (opposite (opposite y (opposite y x)) x) (opposite z z) = x :=
  equation18212 x z y
theorem infinite_model : ∃ (A : Type) (op : A → A → A) (f : Nat → A),
    (∀ x y z, op (op y y) (op x (op (op x z) z)) = x) ∧
    (∀ n j, f n = f j → n = j) :=
  ⟨Carrier, mul, embed, equation18212, embed_injective⟩
end submission.Austin18212

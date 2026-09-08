import Lean.Elab.Tactic.Omega
import JudgeProblem

set_option autoImplicit false
namespace submission.Austin7763
inductive T where
  | e : T
  | k : T → T
  | p : T → T → T
  deriving DecidableEq
open T
def sz : T → Nat
  | e => 0
  | k a => sz a + 1
  | p a b => sz a + sz b + 2
def left : T → T
  | p a _ => a
  | _ => e
def right : T → T
  | p _ b => b
  | _ => e

mutual
inductive Code : T → T → T → Prop
  | law (x y z h₀ h₁ : T)
      (s₀ : Step x z h₀) (s₁ : Step (p z h₀) y h₁) :
      Code y (p y h₁) x
inductive Step : T → T → T → Prop
  | raw (a b : T) : Step a b (p a b)
  | hit {a b o : T} (h : Code a b o) : Step a b o
end

theorem code_bounds {a b o : T} (h : Code a b o) : sz a < sz b ∧ sz o < sz b := by
  apply Code.rec (motive_1 := fun a b o _ => sz a < sz b ∧ sz o < sz b)
    (motive_2 := fun a b o _ => sz a < sz (p o b)) ?_ ?_ ?_ h
  · intro x y z h₀ h₁ s₀ s₁ ih₀ ih₁
    simp only [sz] at ih₀ ih₁ ⊢
    constructor <;> omega
  · intro a b
    simp only [sz]
    omega
  · intro a b o hc ih
    simp only [sz]
    omega

theorem code_key {a b o : T} (h : Code a b o) : left b = a := by
  cases h
  rfl

theorem code_shape {a b o : T} (h : Code a b o) :
    ∃ x y z h₀ h₁, Step x z h₀ ∧ Step (p z h₀) y h₁ ∧
      a = y ∧ b = p y h₁ ∧ o = x := by
  cases h
  exact ⟨_, _, _, _, _, by assumption, by assumption, rfl, rfl, rfl⟩

theorem step_first_unique {a q b o : T} (h : Step a b o) (k : Step q b o) : a = q := by
  cases h with
  | raw =>
    cases k with
    | raw => rfl
    | hit hc =>
      have hb := (code_bounds hc).2
      simp only [sz] at hb
      omega
  | hit hc =>
    cases k with
    | raw =>
      have hb := (code_bounds hc).2
      simp only [sz] at hb
      omega
    | hit hk => exact (code_key hc).symm.trans (code_key hk)

theorem code_unique {a b o q : T} (h : Code a b o) (k : Code a b q) : o = q := by
  obtain ⟨x,y,z,h₀,h₁,s₀,s₁,ha,hb,ho⟩ := code_shape h
  obtain ⟨xx,yy,zz,t₀,t₁,r₀,r₁,ka,kb,ko⟩ := code_shape k
  have hy : y = yy := ha.symm.trans ka
  have ht : h₁ = t₁ := congrArg right (hb.symm.trans kb)
  subst yy
  subst t₁
  rw [ha] at r₁
  have hp : p z h₀ = p zz t₀ := step_first_unique s₁ r₁
  have hz : z = zz := congrArg left hp
  have hh : h₀ = t₀ := congrArg right hp
  subst zz
  subst t₀
  have hx : x = xx := step_first_unique s₀ r₀
  exact ho.trans (hx.trans ko.symm)

theorem step_ne_second {a b : T} (h : Step a b b) : False := by
  cases h with
  | hit hc =>
    have hb := (code_bounds hc).2
    omega

theorem no_code_after_step {a b o : T} (h : Step a b o) : ¬ ∃ q, Code b o q := by
  rintro ⟨q,hc⟩
  cases h with
  | raw =>
    obtain ⟨x,y,z,h₀,h₁,s₀,s₁,hb,hp,hq⟩ := code_shape hc
    have ht : b = h₁ := congrArg right hp
    subst y
    subst h₁
    exact step_ne_second s₁
  | hit h₀ =>
    have hsmall := (code_bounds h₀).2
    have hlarge := (code_bounds hc).1
    omega

noncomputable def eval (a b : T) : T := by
  classical
  exact if h : ∃ o, Code a b o then Classical.choose h else p a b
theorem eval_hit {a b o : T} (h : Code a b o) : eval a b = o := by
  rw [eval, dif_pos ⟨o,h⟩]
  exact code_unique (Classical.choose_spec ⟨o,h⟩) h
theorem eval_raw {a b : T} (h : ¬ ∃ o, Code a b o) : eval a b = p a b := by
  rw [eval, dif_neg h]
theorem eval_step (a b : T) : Step a b (eval a b) := by
  by_cases h : ∃ o, Code a b o
  · obtain ⟨o,h⟩ := h
    rw [eval_hit h]
    exact Step.hit h
  · rw [eval_raw h]
    exact Step.raw a b

abbrev Carrier := T
noncomputable def mul : Carrier → Carrier → Carrier := eval
theorem equation7763 (x y z : Carrier) : mul y (mul y (mul (mul z (mul x z)) y)) = x := by
  change eval y (eval y (eval (eval z (eval x z)) y)) = x
  have s₀ := eval_step x z
  have h₀ : eval z (eval x z) = p z (eval x z) := eval_raw (no_code_after_step s₀)
  rw [h₀]
  have s₁ := eval_step (p z (eval x z)) y
  have h₁ : eval y (eval (p z (eval x z)) y) = p y (eval (p z (eval x z)) y) :=
    eval_raw (no_code_after_step s₁)
  rw [h₁]
  exact eval_hit (Code.law x y z _ _ s₀ s₁)

def tower : Nat → T
  | 0 => e
  | n+1 => k (tower n)
theorem tower_size (n : Nat) : sz (tower n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [tower, sz, ih]
def embed : Nat → Carrier := tower
theorem embed_injective (n j : Nat) (h : embed n = embed j) : n = j := by
  have hh := congrArg sz h
  change sz (tower n) = sz (tower j) at hh
  simpa only [tower_size] using hh
noncomputable def opposite (a b : Carrier) : Carrier := mul b a
theorem equation38565 (x y z : Carrier) :
    opposite (opposite (opposite y (opposite (opposite z x) z)) y) y = x :=
  equation7763 x y z
theorem infinite_model : ∃ (A : Type) (op : A → A → A) (f : Nat → A),
    (∀ x y z, op y (op y (op (op z (op x z)) y)) = x) ∧
    (∀ n j, f n = f j → n = j) :=
  ⟨Carrier, mul, embed, equation7763, embed_injective⟩
end submission.Austin7763

namespace submission
abbrev CM := Austin7763.Carrier
namespace CM
theorem tower_injective (n j : Nat)
    (h : Austin7763.embed n = Austin7763.embed j) : n = j :=
  Austin7763.embed_injective n j h
end CM
noncomputable instance modelMagma : Magma CM := ⟨Austin7763.opposite⟩
end submission
theorem submission : Goal := by
  refine ⟨submission.CM, submission.modelMagma, ?_, ?_⟩
  · intro x y z
    exact (submission.Austin7763.equation38565 x y z).symm
  · intro h
    have bad : 0 = 1 := submission.Austin7763.embed_injective 0 1
      (h (submission.Austin7763.embed 0) (submission.Austin7763.embed 1))
    exact Nat.noConfusion bad
example : Goal := submission
#print axioms submission
#print axioms submission.CM.tower_injective

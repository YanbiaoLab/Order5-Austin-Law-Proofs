import Lean.Elab.Tactic.Omega
import JudgeProblem

set_option autoImplicit false
namespace submission.Austin11280
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
      (s₀ : Step z y h₀) (s₁ : Step x y h₁) :
      Code y (p (p y h₀) h₁) x
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

theorem code_key {a b o : T} (h : Code a b o) : left (left b) = a := by
  cases h
  rfl

theorem code_shape {a b o : T} (h : Code a b o) :
    ∃ x y z h₀ h₁, Step z y h₀ ∧ Step x y h₁ ∧
      a = y ∧ b = p (p y h₀) h₁ ∧ o = x := by
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
  have hx : x = xx := step_first_unique s₁ r₁
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

theorem step_bound {a b o : T} (h : Step a b o) : sz a < sz (p o b) := by
  cases h with
  | raw => simp only [sz]; omega
  | hit hc =>
    have hb := (code_bounds hc).1
    simp only [sz]
    omega

theorem no_code_paired {z y h₀ x h₁ : T}
    (s₀ : Step z y h₀) (s₁ : Step x y h₁) : ¬ ∃ q, Code (p y h₀) h₁ q := by
  rintro ⟨q,hc⟩
  cases s₁ with
  | hit hx =>
    have hs := (code_bounds hx).2
    have hl := (code_bounds hc).1
    simp only [sz] at hl
    omega
  | raw =>
    obtain ⟨xx,yy,zz,t₀,t₁,r₀,r₁,ha,hb,ho⟩ := code_shape hc
    have ht : y = t₁ := congrArg right hb
    rw [← ha,← ht] at r₁
    cases r₁ with
    | hit hc₁ =>
      obtain ⟨xo,yk,zk,u₀,u₁,k₀,k₁,ka,kb,ko⟩ := code_shape hc₁
      have hy : y = p yk u₀ := congrArg left kb
      have hh : h₀ = u₁ := congrArg right kb
      rw [← ko,← hh] at k₁
      have hs := congrArg sz hy
      simp only [sz] at hs
      cases k₁ with
      | hit hk =>
        have hb := (code_bounds hk).1
        omega
      | raw =>
        cases s₀ with
        | raw => omega
        | hit hz =>
          have hb := (code_bounds hz).2
          simp only [sz] at hb
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
theorem equation11280 (x y z : Carrier) : mul y (mul (mul y (mul z y)) (mul x y)) = x := by
  change eval y (eval (eval y (eval z y)) (eval x y)) = x
  have s₀ := eval_step z y
  have s₁ := eval_step x y
  have h₀ : eval y (eval z y) = p y (eval z y) := eval_raw (no_code_after_step s₀)
  rw [h₀]
  have h₁ : eval (p y (eval z y)) (eval x y) = p (p y (eval z y)) (eval x y) :=
    eval_raw (no_code_paired s₀ s₁)
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
theorem equation34778 (x y z : Carrier) :
    (opposite (opposite (opposite y x) (opposite (opposite y z) y)) y) = x := equation11280 x y z
theorem infinite_model : ∃ (A : Type) (op : A → A → A) (f : Nat → A),
    (∀ x y z, (op y (op (op y (op z y)) (op x y))) = x) ∧
    (∀ n j, f n = f j → n = j) :=
  ⟨Carrier, mul, embed, equation11280, embed_injective⟩
end submission.Austin11280

namespace submission
abbrev CM := Austin11280.Carrier
namespace CM
theorem tower_injective (n j : Nat)
    (h : Austin11280.embed n = Austin11280.embed j) : n = j :=
  Austin11280.embed_injective n j h
end CM
noncomputable instance modelMagma : Magma CM := ⟨Austin11280.opposite⟩
end submission
theorem submission : Goal := by
  refine ⟨submission.CM, submission.modelMagma, ?_, ?_⟩
  · intro x y z
    exact (submission.Austin11280.equation34778 x y z).symm
  · intro h
    have bad : 0 = 1 := submission.Austin11280.embed_injective 0 1
      (h (submission.Austin11280.embed 0) (submission.Austin11280.embed 1))
    exact Nat.noConfusion bad
example : Goal := submission
#print axioms submission
#print axioms submission.CM.tower_injective

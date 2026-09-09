import JudgeProblem
import Mathlib.Logic.Relation
import Lean

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace submission

inductive T where
  | leaf : Nat → T
  | sq : T → T
  | op : T → T → T
  deriving DecidableEq
open T

def sz : T → Nat
  | leaf _ => 1
  | T.sq a => sz a + 1
  | op a b => sz a + sz b + 1

theorem sz_pos (a : T) : 0 < sz a := by
  cases a <;> simp [sz]

inductive Rule where
  | r0 | r1 | r2 | r3 | r4 | r5 | r6 | r7 | r8 | r9

def L : Rule → T → T → T → T
  | .r0, v0, v1, v2 => (op v0 v0)
  | .r1, v0, v1, v2 => (op v0 (op (op v1 (op v0 (sq v2))) v0))
  | .r2, v0, v1, v2 => (op v0 (op (sq (op v0 (sq v1))) v0))
  | .r3, v0, v1, v2 => (op (sq v0) (op (op v1 (sq (sq v0))) (sq v0)))
  | .r4, v0, v1, v2 => (op (op v0 (op (sq v1) (sq v2))) (op v0 (op v0 (op (sq v1) (sq v2)))))
  | .r5, v0, v1, v2 => (sq (sq (sq (sq v0))))
  | .r6, v0, v1, v2 => (op (sq (sq (sq v0))) (op (op v1 (sq v0)) (sq (sq (sq v0)))))
  | .r7, v0, v1, v2 => (op (op v0 (sq v1)) (op v0 (op v0 (sq v1))))
  | .r8, v0, v1, v2 => (sq (op (sq v0) (sq v1)))
  | .r9, v0, v1, v2 => (op (sq v0) (op (sq v1) (sq v0)))
def R : Rule → T → T → T → T
  | .r0, v0, v1, v2 => (sq v0)
  | .r1, v0, v1, v2 => v1
  | .r2, v0, v1, v2 => (op v0 (sq v1))
  | .r3, v0, v1, v2 => v1
  | .r4, v0, v1, v2 => (sq v1)
  | .r5, v0, v1, v2 => (sq v0)
  | .r6, v0, v1, v2 => v1
  | .r7, v0, v1, v2 => (sq (sq (sq v1)))
  | .r8, v0, v1, v2 => (sq (sq (sq v1)))
  | .r9, v0, v1, v2 => (op (sq v0) (sq (sq v1)))


def Root (t u : T) : Prop :=
  ∃ k a b c, t = L k a b c ∧ u = R k a b c

inductive Step : T → T → Prop where
  | root {a b : T} : Root a b → Step a b
  | sq {a b : T} : Step a b → Step (sq a) (sq b)
  | left {a b : T} (c : T) : Step a b → Step (op a c) (op b c)
  | right {a b : T} (c : T) : Step a b → Step (op c a) (op c b)

abbrev Reach := Relation.ReflTransGen Step
def Join (a b : T) : Prop := ∃ c, Reach a c ∧ Reach b c

theorem root_step (k : Rule) (a b c : T) : Step (L k a b c) (R k a b c) :=
  .root ⟨k, a, b, c, rfl, rfl⟩

theorem root_decrease {a b : T} (h : Root a b) : sz b < sz a := by
  rcases h with ⟨k, x, y, z, rfl, rfl⟩
  have hx := sz_pos x
  have hy := sz_pos y
  have hz := sz_pos z
  cases k <;> simp only [L, R, sz] <;> omega

theorem step_decrease {a b : T} (h : Step a b) : sz b < sz a := by
  induction h with
  | root h => exact root_decrease h
  | sq h ih => simp only [sz]; omega
  | left c h ih => simp only [sz]; omega
  | right c h ih => simp only [sz]; omega

theorem reach_size {a b : T} (h : Reach a b) : sz b ≤ sz a := by
  induction h with
  | refl => exact Nat.le_refl _
  | tail h hs ih => have hd := step_decrease hs; omega

theorem reach_sq {a b : T} (h : Reach a b) : Reach (sq a) (sq b) :=
  h.lift sq (fun _ _ h => Step.sq h)
theorem reach_left {a b : T} (c : T) (h : Reach a b) : Reach (op a c) (op b c) :=
  h.lift (fun a => op a c) (fun _ _ h => Step.left c h)
theorem reach_right {a b : T} (c : T) (h : Reach a b) : Reach (op c a) (op c b) :=
  h.lift (op c) (fun _ _ h => Step.right c h)

theorem join_symm {a b : T} (h : Join a b) : Join b a := by
  rcases h with ⟨c, h1, h2⟩
  exact ⟨c, h2, h1⟩
theorem join_sq {a b : T} (h : Join a b) : Join (sq a) (sq b) := by
  rcases h with ⟨c, h1, h2⟩
  exact ⟨sq c, reach_sq h1, reach_sq h2⟩
theorem join_left {a b : T} (c : T) (h : Join a b) : Join (op a c) (op b c) := by
  rcases h with ⟨d, h1, h2⟩
  exact ⟨op d c, reach_left c h1, reach_left c h2⟩
theorem join_right {a b : T} (c : T) (h : Join a b) : Join (op c a) (op c b) := by
  rcases h with ⟨d, h1, h2⟩
  exact ⟨op c d, reach_right c h1, reach_right c h2⟩

theorem step_sq_cases {a u : T} (h : Step (sq a) u) :
    Root (sq a) u ∨ ∃ v, u = sq v ∧ Step a v := by
  cases h with
  | root h => exact Or.inl h
  | sq h => exact Or.inr ⟨_, rfl, h⟩

theorem step_op_cases {a b u : T} (h : Step (op a b) u) :
    Root (op a b) u ∨ (∃ v, u = op v b ∧ Step a v) ∨
      (∃ v, u = op a v ∧ Step b v) := by
  cases h with
  | root h => exact Or.inl h
  | left _ h => exact Or.inr (Or.inl ⟨_, rfl, h⟩)
  | right _ h => exact Or.inr (Or.inr ⟨_, rfl, h⟩)

theorem cp_0_root_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 a0) = (op b0 b0)) :
    Join (sq a0) (sq b0) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  revert he1
  subst a0
  intro he1
  clear he1
  exact ⟨(sq b0), (Relation.ReflTransGen.refl), (Relation.ReflTransGen.refl)⟩

theorem cp_0_root_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 a0) = (op b0 (op (op b1 (op b0 (sq b2))) b0))) :
    Join (sq a0) b1 := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  revert he1
  subst a0
  intro he1
  have hsize := congrArg sz he1
  have hp_b0 := sz_pos b0
  have hp_b1 := sz_pos b1
  have hp_b2 := sz_pos b2
  simp only [sz] at hsize
  omega

theorem cp_0_root_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 a0) = (op b0 (op (sq (op b0 (sq b1))) b0))) :
    Join (sq a0) (op b0 (sq b1)) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  revert he1
  subst a0
  intro he1
  have hsize := congrArg sz he1
  have hp_b0 := sz_pos b0
  have hp_b1 := sz_pos b1
  simp only [sz] at hsize
  omega

theorem cp_0_root_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 a0) = (op (sq b0) (op (op b1 (sq (sq b0))) (sq b0)))) :
    Join (sq a0) b1 := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  revert he1
  subst a0
  intro he1
  cases he1

theorem cp_0_root_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 a0) = (op (op b0 (op (sq b1) (sq b2))) (op b0 (op b0 (op (sq b1) (sq b2)))))) :
    Join (sq a0) (sq b1) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  revert he1
  subst a0
  intro he1
  rcases T.op.inj he1 with ⟨he3, he4⟩
  clear he1
  rcases T.op.inj he4 with ⟨he5, he6⟩
  clear he4
  cases he6

theorem cp_0_root_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 a0) = (sq (sq (sq (sq b0))))) :
    Join (sq a0) (sq b0) := by
  cases heq

theorem cp_0_root_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 a0) = (op (sq (sq (sq b0))) (op (op b1 (sq b0)) (sq (sq (sq b0)))))) :
    Join (sq a0) b1 := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  revert he1
  subst a0
  intro he1
  cases he1

theorem cp_0_root_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 a0) = (op (op b0 (sq b1)) (op b0 (op b0 (sq b1))))) :
    Join (sq a0) (sq (sq (sq b1))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  revert he1
  subst a0
  intro he1
  rcases T.op.inj he1 with ⟨he3, he4⟩
  clear he1
  cases he4

theorem cp_0_root_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 a0) = (sq (op (sq b0) (sq b1)))) :
    Join (sq a0) (sq (sq (sq b1))) := by
  cases heq

theorem cp_0_root_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 a0) = (op (sq b0) (op (sq b1) (sq b0)))) :
    Join (sq a0) (op (sq b0) (sq (sq b1))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  revert he1
  subst a0
  intro he1
  cases he1

theorem cp_1_root_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (op (op a1 (op a0 (sq a2))) a0)) = (op b0 b0)) :
    Join a1 (sq b0) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  revert he1
  subst b0
  intro he1
  have hsize := congrArg sz he1
  have hp_a0 := sz_pos a0
  have hp_a1 := sz_pos a1
  have hp_a2 := sz_pos a2
  simp only [sz] at hsize
  omega

theorem cp_1_2_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (op a1 (op a0 (sq a2))) a0) = (op b0 b0)) :
    Join a1 (op a0 (sq b0)) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  revert he1
  subst a0
  intro he1
  have hsize := congrArg sz he1
  have hp_a1 := sz_pos a1
  have hp_a2 := sz_pos a2
  have hp_b0 := sz_pos b0
  simp only [sz] at hsize
  omega

theorem cp_1_21_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a1 (op a0 (sq a2))) = (op b0 b0)) :
    Join a1 (op a0 (op (sq b0) a0)) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  revert he1
  subst b0
  intro he1
  subst a1
  exact ⟨(op a0 (sq a2)), (Relation.ReflTransGen.refl), ((Relation.ReflTransGen.refl).tail (root_step .r2 a0 a2 (leaf 0)))⟩

theorem cp_1_212_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (sq a2)) = (op b0 b0)) :
    Join a1 (op a0 (op (op a1 (sq b0)) a0)) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  revert he1
  subst b0
  intro he1
  subst a0
  exact ⟨a1, (Relation.ReflTransGen.refl), ((Relation.ReflTransGen.refl).tail (root_step .r3 a2 a1 (leaf 0)))⟩

theorem cp_1_2122_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a2) = (op b0 b0)) :
    Join a1 (op a0 (op (op a1 (op a0 (sq b0))) a0)) := by
  cases heq

theorem cp_1_root_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (op (op a1 (op a0 (sq a2))) a0)) = (op b0 (op (op b1 (op b0 (sq b2))) b0))) :
    Join a1 b1 := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  revert he1 he3
  subst a0
  intro he1 he3
  rcases T.op.inj he3 with ⟨he5, he6⟩
  clear he3
  rcases T.op.inj he6 with ⟨he7, he8⟩
  clear he6
  have he9 := T.sq.inj he8
  clear he8
  revert he1 he5 he7
  subst a2
  intro he1 he5 he7
  clear he7
  revert he1
  subst a1
  intro he1
  clear he1
  exact ⟨b1, (Relation.ReflTransGen.refl), (Relation.ReflTransGen.refl)⟩

theorem cp_1_2_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (op a1 (op a0 (sq a2))) a0) = (op b0 (op (op b1 (op b0 (sq b2))) b0))) :
    Join a1 (op a0 b1) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  revert he1
  subst a0
  intro he1
  have hsize := congrArg sz he1
  have hp_a1 := sz_pos a1
  have hp_a2 := sz_pos a2
  have hp_b0 := sz_pos b0
  have hp_b1 := sz_pos b1
  have hp_b2 := sz_pos b2
  simp only [sz] at hsize
  omega

theorem cp_1_21_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a1 (op a0 (sq a2))) = (op b0 (op (op b1 (op b0 (sq b2))) b0))) :
    Join a1 (op a0 (op b1 a0)) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  revert he1 he3
  subst b0
  intro he1 he3
  revert he1
  subst a0
  intro he1
  subst a1
  exact ⟨(sq a2), (Relation.ReflTransGen.refl), ((Relation.ReflTransGen.refl).tail (root_step .r4 b1 a2 b2))⟩

theorem cp_1_212_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (sq a2)) = (op b0 (op (op b1 (op b0 (sq b2))) b0))) :
    Join a1 (op a0 (op (op a1 b1) a0)) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_1_2122_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a2) = (op b0 (op (op b1 (op b0 (sq b2))) b0))) :
    Join a1 (op a0 (op (op a1 (op a0 b1)) a0)) := by
  cases heq

theorem cp_1_root_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (op (op a1 (op a0 (sq a2))) a0)) = (op b0 (op (sq (op b0 (sq b1))) b0))) :
    Join a1 (op b0 (sq b1)) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  revert he1 he3
  subst a0
  intro he1 he3
  cases he3

theorem cp_1_2_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (op a1 (op a0 (sq a2))) a0) = (op b0 (op (sq (op b0 (sq b1))) b0))) :
    Join a1 (op a0 (op b0 (sq b1))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  revert he1
  subst a0
  intro he1
  have hsize := congrArg sz he1
  have hp_a1 := sz_pos a1
  have hp_a2 := sz_pos a2
  have hp_b0 := sz_pos b0
  have hp_b1 := sz_pos b1
  simp only [sz] at hsize
  omega

theorem cp_1_21_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a1 (op a0 (sq a2))) = (op b0 (op (sq (op b0 (sq b1))) b0))) :
    Join a1 (op a0 (op (op b0 (sq b1)) a0)) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  revert he1 he3
  subst b0
  intro he1 he3
  revert he1
  subst a0
  intro he1
  subst a1
  exact ⟨(sq a2), (Relation.ReflTransGen.refl), ((((Relation.ReflTransGen.refl).tail (Step.left (op (op (sq a2) (sq b1)) (sq (op (sq a2) (sq b1)))) (root_step .r8 a2 b1 (leaf 0)))).tail (Step.right (sq (sq (sq b1))) (Step.right (op (sq a2) (sq b1)) (root_step .r8 a2 b1 (leaf 0))))).tail (root_step .r6 b1 (sq a2) (leaf 0)))⟩

theorem cp_1_212_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (sq a2)) = (op b0 (op (sq (op b0 (sq b1))) b0))) :
    Join a1 (op a0 (op (op a1 (op b0 (sq b1))) a0)) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_1_2122_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a2) = (op b0 (op (sq (op b0 (sq b1))) b0))) :
    Join a1 (op a0 (op (op a1 (op a0 (op b0 (sq b1)))) a0)) := by
  cases heq

theorem cp_1_root_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (op (op a1 (op a0 (sq a2))) a0)) = (op (sq b0) (op (op b1 (sq (sq b0))) (sq b0)))) :
    Join a1 b1 := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  revert he1 he3
  subst a0
  intro he1 he3
  rcases T.op.inj he3 with ⟨he5, he6⟩
  clear he3
  cases he6

theorem cp_1_2_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (op a1 (op a0 (sq a2))) a0) = (op (sq b0) (op (op b1 (sq (sq b0))) (sq b0)))) :
    Join a1 (op a0 b1) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  revert he1
  subst a0
  intro he1
  cases he1

theorem cp_1_21_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a1 (op a0 (sq a2))) = (op (sq b0) (op (op b1 (sq (sq b0))) (sq b0)))) :
    Join a1 (op a0 (op b1 a0)) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  have he5 := T.sq.inj he4
  clear he4
  revert he1 he3
  subst a2
  intro he1 he3
  revert he1
  subst a0
  intro he1
  subst a1
  exact ⟨(sq b0), (Relation.ReflTransGen.refl), (((Relation.ReflTransGen.refl).tail (root_step .r7 b1 (sq b0) (leaf 0))).tail (root_step .r5 b0 (leaf 0) (leaf 0)))⟩

theorem cp_1_212_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (sq a2)) = (op (sq b0) (op (op b1 (sq (sq b0))) (sq b0)))) :
    Join a1 (op a0 (op (op a1 b1) a0)) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_1_2122_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a2) = (op (sq b0) (op (op b1 (sq (sq b0))) (sq b0)))) :
    Join a1 (op a0 (op (op a1 (op a0 b1)) a0)) := by
  cases heq

theorem cp_1_root_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (op (op a1 (op a0 (sq a2))) a0)) = (op (op b0 (op (sq b1) (sq b2))) (op b0 (op b0 (op (sq b1) (sq b2)))))) :
    Join a1 (sq b1) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  revert he1 he3
  subst a0
  intro he1 he3
  have hsize := congrArg sz he3
  have hp_a1 := sz_pos a1
  have hp_a2 := sz_pos a2
  have hp_b0 := sz_pos b0
  have hp_b1 := sz_pos b1
  have hp_b2 := sz_pos b2
  simp only [sz] at hsize
  omega

theorem cp_1_2_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (op a1 (op a0 (sq a2))) a0) = (op (op b0 (op (sq b1) (sq b2))) (op b0 (op b0 (op (sq b1) (sq b2)))))) :
    Join a1 (op a0 (sq b1)) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  revert he1
  subst a0
  intro he1
  rcases T.op.inj he1 with ⟨he3, he4⟩
  clear he1
  rcases T.op.inj he4 with ⟨he5, he6⟩
  clear he4
  have he7 := T.sq.inj he6
  clear he6
  revert he3 he5
  subst a2
  intro he3 he5
  cases he5

theorem cp_1_21_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a1 (op a0 (sq a2))) = (op (op b0 (op (sq b1) (sq b2))) (op b0 (op b0 (op (sq b1) (sq b2)))))) :
    Join a1 (op a0 (op (sq b1) a0)) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  cases he4

theorem cp_1_212_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (sq a2)) = (op (op b0 (op (sq b1) (sq b2))) (op b0 (op b0 (op (sq b1) (sq b2)))))) :
    Join a1 (op a0 (op (op a1 (sq b1)) a0)) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_1_2122_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a2) = (op (op b0 (op (sq b1) (sq b2))) (op b0 (op b0 (op (sq b1) (sq b2)))))) :
    Join a1 (op a0 (op (op a1 (op a0 (sq b1))) a0)) := by
  cases heq

theorem cp_1_root_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (op (op a1 (op a0 (sq a2))) a0)) = (sq (sq (sq (sq b0))))) :
    Join a1 (sq b0) := by
  cases heq

theorem cp_1_2_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (op a1 (op a0 (sq a2))) a0) = (sq (sq (sq (sq b0))))) :
    Join a1 (op a0 (sq b0)) := by
  cases heq

theorem cp_1_21_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a1 (op a0 (sq a2))) = (sq (sq (sq (sq b0))))) :
    Join a1 (op a0 (op (sq b0) a0)) := by
  cases heq

theorem cp_1_212_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (sq a2)) = (sq (sq (sq (sq b0))))) :
    Join a1 (op a0 (op (op a1 (sq b0)) a0)) := by
  cases heq

theorem cp_1_2122_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a2) = (sq (sq (sq (sq b0))))) :
    Join a1 (op a0 (op (op a1 (op a0 (sq b0))) a0)) := by
  have he1 := T.sq.inj heq
  clear heq
  subst a2
  exact ⟨a1, (Relation.ReflTransGen.refl), ((Relation.ReflTransGen.refl).tail (root_step .r1 a0 a1 b0))⟩

theorem cp_1_root_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (op (op a1 (op a0 (sq a2))) a0)) = (op (sq (sq (sq b0))) (op (op b1 (sq b0)) (sq (sq (sq b0)))))) :
    Join a1 b1 := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  revert he1 he3
  subst a0
  intro he1 he3
  rcases T.op.inj he3 with ⟨he5, he6⟩
  clear he3
  cases he6

theorem cp_1_2_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (op a1 (op a0 (sq a2))) a0) = (op (sq (sq (sq b0))) (op (op b1 (sq b0)) (sq (sq (sq b0)))))) :
    Join a1 (op a0 b1) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  revert he1
  subst a0
  intro he1
  cases he1

theorem cp_1_21_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a1 (op a0 (sq a2))) = (op (sq (sq (sq b0))) (op (op b1 (sq b0)) (sq (sq (sq b0)))))) :
    Join a1 (op a0 (op b1 a0)) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  have he5 := T.sq.inj he4
  clear he4
  revert he1 he3
  subst a2
  intro he1 he3
  revert he1
  subst a0
  intro he1
  subst a1
  exact ⟨(sq (sq (sq b0))), (Relation.ReflTransGen.refl), ((Relation.ReflTransGen.refl).tail (root_step .r7 b1 b0 (leaf 0)))⟩

theorem cp_1_212_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (sq a2)) = (op (sq (sq (sq b0))) (op (op b1 (sq b0)) (sq (sq (sq b0)))))) :
    Join a1 (op a0 (op (op a1 b1) a0)) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_1_2122_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a2) = (op (sq (sq (sq b0))) (op (op b1 (sq b0)) (sq (sq (sq b0)))))) :
    Join a1 (op a0 (op (op a1 (op a0 b1)) a0)) := by
  cases heq

theorem cp_1_root_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (op (op a1 (op a0 (sq a2))) a0)) = (op (op b0 (sq b1)) (op b0 (op b0 (sq b1))))) :
    Join a1 (sq (sq (sq b1))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  revert he1 he3
  subst a0
  intro he1 he3
  have hsize := congrArg sz he3
  have hp_a1 := sz_pos a1
  have hp_a2 := sz_pos a2
  have hp_b0 := sz_pos b0
  have hp_b1 := sz_pos b1
  simp only [sz] at hsize
  omega

theorem cp_1_2_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (op a1 (op a0 (sq a2))) a0) = (op (op b0 (sq b1)) (op b0 (op b0 (sq b1))))) :
    Join a1 (op a0 (sq (sq (sq b1)))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  revert he1
  subst a0
  intro he1
  rcases T.op.inj he1 with ⟨he3, he4⟩
  clear he1
  cases he4

theorem cp_1_21_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a1 (op a0 (sq a2))) = (op (op b0 (sq b1)) (op b0 (op b0 (sq b1))))) :
    Join a1 (op a0 (op (sq (sq (sq b1))) a0)) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  cases he4

theorem cp_1_212_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (sq a2)) = (op (op b0 (sq b1)) (op b0 (op b0 (sq b1))))) :
    Join a1 (op a0 (op (op a1 (sq (sq (sq b1)))) a0)) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_1_2122_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a2) = (op (op b0 (sq b1)) (op b0 (op b0 (sq b1))))) :
    Join a1 (op a0 (op (op a1 (op a0 (sq (sq (sq b1))))) a0)) := by
  cases heq

theorem cp_1_root_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (op (op a1 (op a0 (sq a2))) a0)) = (sq (op (sq b0) (sq b1)))) :
    Join a1 (sq (sq (sq b1))) := by
  cases heq

theorem cp_1_2_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (op a1 (op a0 (sq a2))) a0) = (sq (op (sq b0) (sq b1)))) :
    Join a1 (op a0 (sq (sq (sq b1)))) := by
  cases heq

theorem cp_1_21_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a1 (op a0 (sq a2))) = (sq (op (sq b0) (sq b1)))) :
    Join a1 (op a0 (op (sq (sq (sq b1))) a0)) := by
  cases heq

theorem cp_1_212_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (sq a2)) = (sq (op (sq b0) (sq b1)))) :
    Join a1 (op a0 (op (op a1 (sq (sq (sq b1)))) a0)) := by
  cases heq

theorem cp_1_2122_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a2) = (sq (op (sq b0) (sq b1)))) :
    Join a1 (op a0 (op (op a1 (op a0 (sq (sq (sq b1))))) a0)) := by
  have he1 := T.sq.inj heq
  clear heq
  subst a2
  exact ⟨a1, (Relation.ReflTransGen.refl), ((Relation.ReflTransGen.refl).tail (root_step .r1 a0 a1 (sq (sq b1))))⟩

theorem cp_1_root_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (op (op a1 (op a0 (sq a2))) a0)) = (op (sq b0) (op (sq b1) (sq b0)))) :
    Join a1 (op (sq b0) (sq (sq b1))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  revert he1 he3
  subst a0
  intro he1 he3
  cases he3

theorem cp_1_2_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (op a1 (op a0 (sq a2))) a0) = (op (sq b0) (op (sq b1) (sq b0)))) :
    Join a1 (op a0 (op (sq b0) (sq (sq b1)))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  revert he1
  subst a0
  intro he1
  cases he1

theorem cp_1_21_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a1 (op a0 (sq a2))) = (op (sq b0) (op (sq b1) (sq b0)))) :
    Join a1 (op a0 (op (op (sq b0) (sq (sq b1))) a0)) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  have he5 := T.sq.inj he4
  clear he4
  revert he1 he3
  subst a2
  intro he1 he3
  revert he1
  subst a0
  intro he1
  subst a1
  exact ⟨(sq b0), (Relation.ReflTransGen.refl), ((Relation.ReflTransGen.refl).tail (root_step .r3 b1 (sq b0) (leaf 0)))⟩

theorem cp_1_212_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (sq a2)) = (op (sq b0) (op (sq b1) (sq b0)))) :
    Join a1 (op a0 (op (op a1 (op (sq b0) (sq (sq b1)))) a0)) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_1_2122_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a2) = (op (sq b0) (op (sq b1) (sq b0)))) :
    Join a1 (op a0 (op (op a1 (op a0 (op (sq b0) (sq (sq b1))))) a0)) := by
  cases heq

theorem cp_2_root_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (op (sq (op a0 (sq a1))) a0)) = (op b0 b0)) :
    Join (op a0 (sq a1)) (sq b0) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  revert he1
  subst b0
  intro he1
  have hsize := congrArg sz he1
  have hp_a0 := sz_pos a0
  have hp_a1 := sz_pos a1
  simp only [sz] at hsize
  omega

theorem cp_2_2_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (sq (op a0 (sq a1))) a0) = (op b0 b0)) :
    Join (op a0 (sq a1)) (op a0 (sq b0)) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  revert he1
  subst a0
  intro he1
  have hsize := congrArg sz he1
  have hp_a1 := sz_pos a1
  have hp_b0 := sz_pos b0
  simp only [sz] at hsize
  omega

theorem cp_2_21_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (op a0 (sq a1))) = (op b0 b0)) :
    Join (op a0 (sq a1)) (op a0 (op (sq b0) a0)) := by
  cases heq

theorem cp_2_211_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (sq a1)) = (op b0 b0)) :
    Join (op a0 (sq a1)) (op a0 (op (sq (sq b0)) a0)) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  revert he1
  subst b0
  intro he1
  subst a0
  exact ⟨(sq (sq a1)), ((Relation.ReflTransGen.refl).tail (root_step .r0 (sq a1) (leaf 0) (leaf 0))), ((((Relation.ReflTransGen.refl).tail (root_step .r9 a1 (sq (sq a1)) (leaf 0))).tail (Step.right (sq a1) (root_step .r5 a1 (leaf 0) (leaf 0)))).tail (root_step .r0 (sq a1) (leaf 0) (leaf 0)))⟩

theorem cp_2_2112_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a1) = (op b0 b0)) :
    Join (op a0 (sq a1)) (op a0 (op (sq (op a0 (sq b0))) a0)) := by
  cases heq

theorem cp_2_root_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (op (sq (op a0 (sq a1))) a0)) = (op b0 (op (op b1 (op b0 (sq b2))) b0))) :
    Join (op a0 (sq a1)) b1 := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  revert he1 he3
  subst a0
  intro he1 he3
  cases he3

theorem cp_2_2_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (sq (op a0 (sq a1))) a0) = (op b0 (op (op b1 (op b0 (sq b2))) b0))) :
    Join (op a0 (sq a1)) (op a0 b1) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  revert he1
  subst a0
  intro he1
  have hsize := congrArg sz he1
  have hp_a1 := sz_pos a1
  have hp_b0 := sz_pos b0
  have hp_b1 := sz_pos b1
  have hp_b2 := sz_pos b2
  simp only [sz] at hsize
  omega

theorem cp_2_21_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (op a0 (sq a1))) = (op b0 (op (op b1 (op b0 (sq b2))) b0))) :
    Join (op a0 (sq a1)) (op a0 (op b1 a0)) := by
  cases heq

theorem cp_2_211_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (sq a1)) = (op b0 (op (op b1 (op b0 (sq b2))) b0))) :
    Join (op a0 (sq a1)) (op a0 (op (sq b1) a0)) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_2_2112_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a1) = (op b0 (op (op b1 (op b0 (sq b2))) b0))) :
    Join (op a0 (sq a1)) (op a0 (op (sq (op a0 b1)) a0)) := by
  cases heq

theorem cp_2_root_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (op (sq (op a0 (sq a1))) a0)) = (op b0 (op (sq (op b0 (sq b1))) b0))) :
    Join (op a0 (sq a1)) (op b0 (sq b1)) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  revert he1 he3
  subst a0
  intro he1 he3
  have he5 := T.sq.inj he3
  clear he3
  rcases T.op.inj he5 with ⟨he6, he7⟩
  clear he5
  have he8 := T.sq.inj he7
  clear he7
  revert he1 he6
  subst a1
  intro he1 he6
  clear he6
  clear he1
  exact ⟨(op b0 (sq b1)), (Relation.ReflTransGen.refl), (Relation.ReflTransGen.refl)⟩

theorem cp_2_2_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (sq (op a0 (sq a1))) a0) = (op b0 (op (sq (op b0 (sq b1))) b0))) :
    Join (op a0 (sq a1)) (op a0 (op b0 (sq b1))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  revert he1
  subst a0
  intro he1
  have hsize := congrArg sz he1
  have hp_a1 := sz_pos a1
  have hp_b0 := sz_pos b0
  have hp_b1 := sz_pos b1
  simp only [sz] at hsize
  omega

theorem cp_2_21_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (op a0 (sq a1))) = (op b0 (op (sq (op b0 (sq b1))) b0))) :
    Join (op a0 (sq a1)) (op a0 (op (op b0 (sq b1)) a0)) := by
  cases heq

theorem cp_2_211_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (sq a1)) = (op b0 (op (sq (op b0 (sq b1))) b0))) :
    Join (op a0 (sq a1)) (op a0 (op (sq (op b0 (sq b1))) a0)) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_2_2112_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a1) = (op b0 (op (sq (op b0 (sq b1))) b0))) :
    Join (op a0 (sq a1)) (op a0 (op (sq (op a0 (op b0 (sq b1)))) a0)) := by
  cases heq

theorem cp_2_root_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (op (sq (op a0 (sq a1))) a0)) = (op (sq b0) (op (op b1 (sq (sq b0))) (sq b0)))) :
    Join (op a0 (sq a1)) b1 := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  revert he1 he3
  subst a0
  intro he1 he3
  cases he3

theorem cp_2_2_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (sq (op a0 (sq a1))) a0) = (op (sq b0) (op (op b1 (sq (sq b0))) (sq b0)))) :
    Join (op a0 (sq a1)) (op a0 b1) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  revert he1
  subst a0
  intro he1
  have he3 := T.sq.inj he1
  clear he1
  have hsize := congrArg sz he3
  have hp_a1 := sz_pos a1
  have hp_b0 := sz_pos b0
  have hp_b1 := sz_pos b1
  simp only [sz] at hsize
  omega

theorem cp_2_21_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (op a0 (sq a1))) = (op (sq b0) (op (op b1 (sq (sq b0))) (sq b0)))) :
    Join (op a0 (sq a1)) (op a0 (op b1 a0)) := by
  cases heq

theorem cp_2_211_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (sq a1)) = (op (sq b0) (op (op b1 (sq (sq b0))) (sq b0)))) :
    Join (op a0 (sq a1)) (op a0 (op (sq b1) a0)) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_2_2112_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a1) = (op (sq b0) (op (op b1 (sq (sq b0))) (sq b0)))) :
    Join (op a0 (sq a1)) (op a0 (op (sq (op a0 b1)) a0)) := by
  cases heq

theorem cp_2_root_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (op (sq (op a0 (sq a1))) a0)) = (op (op b0 (op (sq b1) (sq b2))) (op b0 (op b0 (op (sq b1) (sq b2)))))) :
    Join (op a0 (sq a1)) (sq b1) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  revert he1 he3
  subst a0
  intro he1 he3
  have hsize := congrArg sz he3
  have hp_a1 := sz_pos a1
  have hp_b0 := sz_pos b0
  have hp_b1 := sz_pos b1
  have hp_b2 := sz_pos b2
  simp only [sz] at hsize
  omega

theorem cp_2_2_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (sq (op a0 (sq a1))) a0) = (op (op b0 (op (sq b1) (sq b2))) (op b0 (op b0 (op (sq b1) (sq b2)))))) :
    Join (op a0 (sq a1)) (op a0 (sq b1)) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  revert he1
  subst a0
  intro he1
  cases he1

theorem cp_2_21_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (op a0 (sq a1))) = (op (op b0 (op (sq b1) (sq b2))) (op b0 (op b0 (op (sq b1) (sq b2)))))) :
    Join (op a0 (sq a1)) (op a0 (op (sq b1) a0)) := by
  cases heq

theorem cp_2_211_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (sq a1)) = (op (op b0 (op (sq b1) (sq b2))) (op b0 (op b0 (op (sq b1) (sq b2)))))) :
    Join (op a0 (sq a1)) (op a0 (op (sq (sq b1)) a0)) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_2_2112_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a1) = (op (op b0 (op (sq b1) (sq b2))) (op b0 (op b0 (op (sq b1) (sq b2)))))) :
    Join (op a0 (sq a1)) (op a0 (op (sq (op a0 (sq b1))) a0)) := by
  cases heq

theorem cp_2_root_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (op (sq (op a0 (sq a1))) a0)) = (sq (sq (sq (sq b0))))) :
    Join (op a0 (sq a1)) (sq b0) := by
  cases heq

theorem cp_2_2_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (sq (op a0 (sq a1))) a0) = (sq (sq (sq (sq b0))))) :
    Join (op a0 (sq a1)) (op a0 (sq b0)) := by
  cases heq

theorem cp_2_21_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (op a0 (sq a1))) = (sq (sq (sq (sq b0))))) :
    Join (op a0 (sq a1)) (op a0 (op (sq b0) a0)) := by
  have he1 := T.sq.inj heq
  clear heq
  cases he1

theorem cp_2_211_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (sq a1)) = (sq (sq (sq (sq b0))))) :
    Join (op a0 (sq a1)) (op a0 (op (sq (sq b0)) a0)) := by
  cases heq

theorem cp_2_2112_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a1) = (sq (sq (sq (sq b0))))) :
    Join (op a0 (sq a1)) (op a0 (op (sq (op a0 (sq b0))) a0)) := by
  have he1 := T.sq.inj heq
  clear heq
  subst a1
  exact ⟨(op a0 (sq b0)), ((Relation.ReflTransGen.refl).tail (Step.right a0 (root_step .r5 b0 (leaf 0) (leaf 0)))), ((Relation.ReflTransGen.refl).tail (root_step .r2 a0 b0 (leaf 0)))⟩

theorem cp_2_root_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (op (sq (op a0 (sq a1))) a0)) = (op (sq (sq (sq b0))) (op (op b1 (sq b0)) (sq (sq (sq b0)))))) :
    Join (op a0 (sq a1)) b1 := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  revert he1 he3
  subst a0
  intro he1 he3
  cases he3

theorem cp_2_2_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (sq (op a0 (sq a1))) a0) = (op (sq (sq (sq b0))) (op (op b1 (sq b0)) (sq (sq (sq b0)))))) :
    Join (op a0 (sq a1)) (op a0 b1) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  revert he1
  subst a0
  intro he1
  have he3 := T.sq.inj he1
  clear he1
  cases he3

theorem cp_2_21_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (op a0 (sq a1))) = (op (sq (sq (sq b0))) (op (op b1 (sq b0)) (sq (sq (sq b0)))))) :
    Join (op a0 (sq a1)) (op a0 (op b1 a0)) := by
  cases heq

theorem cp_2_211_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (sq a1)) = (op (sq (sq (sq b0))) (op (op b1 (sq b0)) (sq (sq (sq b0)))))) :
    Join (op a0 (sq a1)) (op a0 (op (sq b1) a0)) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_2_2112_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a1) = (op (sq (sq (sq b0))) (op (op b1 (sq b0)) (sq (sq (sq b0)))))) :
    Join (op a0 (sq a1)) (op a0 (op (sq (op a0 b1)) a0)) := by
  cases heq

theorem cp_2_root_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (op (sq (op a0 (sq a1))) a0)) = (op (op b0 (sq b1)) (op b0 (op b0 (sq b1))))) :
    Join (op a0 (sq a1)) (sq (sq (sq b1))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  revert he1 he3
  subst a0
  intro he1 he3
  have hsize := congrArg sz he3
  have hp_a1 := sz_pos a1
  have hp_b0 := sz_pos b0
  have hp_b1 := sz_pos b1
  simp only [sz] at hsize
  omega

theorem cp_2_2_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (sq (op a0 (sq a1))) a0) = (op (op b0 (sq b1)) (op b0 (op b0 (sq b1))))) :
    Join (op a0 (sq a1)) (op a0 (sq (sq (sq b1)))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  revert he1
  subst a0
  intro he1
  cases he1

theorem cp_2_21_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (op a0 (sq a1))) = (op (op b0 (sq b1)) (op b0 (op b0 (sq b1))))) :
    Join (op a0 (sq a1)) (op a0 (op (sq (sq (sq b1))) a0)) := by
  cases heq

theorem cp_2_211_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (sq a1)) = (op (op b0 (sq b1)) (op b0 (op b0 (sq b1))))) :
    Join (op a0 (sq a1)) (op a0 (op (sq (sq (sq (sq b1)))) a0)) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_2_2112_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a1) = (op (op b0 (sq b1)) (op b0 (op b0 (sq b1))))) :
    Join (op a0 (sq a1)) (op a0 (op (sq (op a0 (sq (sq (sq b1))))) a0)) := by
  cases heq

theorem cp_2_root_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (op (sq (op a0 (sq a1))) a0)) = (sq (op (sq b0) (sq b1)))) :
    Join (op a0 (sq a1)) (sq (sq (sq b1))) := by
  cases heq

theorem cp_2_2_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (sq (op a0 (sq a1))) a0) = (sq (op (sq b0) (sq b1)))) :
    Join (op a0 (sq a1)) (op a0 (sq (sq (sq b1)))) := by
  cases heq

theorem cp_2_21_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (op a0 (sq a1))) = (sq (op (sq b0) (sq b1)))) :
    Join (op a0 (sq a1)) (op a0 (op (sq (sq (sq b1))) a0)) := by
  have he1 := T.sq.inj heq
  clear heq
  rcases T.op.inj he1 with ⟨he2, he3⟩
  clear he1
  have he4 := T.sq.inj he3
  clear he3
  revert he2
  subst a1
  intro he2
  subst a0
  exact ⟨(op (sq b0) (sq b1)), (Relation.ReflTransGen.refl), (((Relation.ReflTransGen.refl).tail (root_step .r9 b0 (sq (sq b1)) (leaf 0))).tail (Step.right (sq b0) (root_step .r5 b1 (leaf 0) (leaf 0))))⟩

theorem cp_2_211_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (sq a1)) = (sq (op (sq b0) (sq b1)))) :
    Join (op a0 (sq a1)) (op a0 (op (sq (sq (sq (sq b1)))) a0)) := by
  cases heq

theorem cp_2_2112_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a1) = (sq (op (sq b0) (sq b1)))) :
    Join (op a0 (sq a1)) (op a0 (op (sq (op a0 (sq (sq (sq b1))))) a0)) := by
  have he1 := T.sq.inj heq
  clear heq
  subst a1
  exact ⟨(op a0 (sq (sq (sq b1)))), ((Relation.ReflTransGen.refl).tail (Step.right a0 (root_step .r8 b0 b1 (leaf 0)))), ((Relation.ReflTransGen.refl).tail (root_step .r2 a0 (sq (sq b1)) (leaf 0)))⟩

theorem cp_2_root_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (op (sq (op a0 (sq a1))) a0)) = (op (sq b0) (op (sq b1) (sq b0)))) :
    Join (op a0 (sq a1)) (op (sq b0) (sq (sq b1))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  revert he1 he3
  subst a0
  intro he1 he3
  have he5 := T.sq.inj he3
  clear he3
  revert he1
  subst b1
  intro he1
  clear he1
  exact ⟨(op (sq b0) (sq a1)), (Relation.ReflTransGen.refl), (((Relation.ReflTransGen.refl).tail (Step.right (sq b0) (Step.sq (root_step .r8 b0 a1 (leaf 0))))).tail (Step.right (sq b0) (root_step .r5 a1 (leaf 0) (leaf 0))))⟩

theorem cp_2_2_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (sq (op a0 (sq a1))) a0) = (op (sq b0) (op (sq b1) (sq b0)))) :
    Join (op a0 (sq a1)) (op a0 (op (sq b0) (sq (sq b1)))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  revert he1
  subst a0
  intro he1
  have he3 := T.sq.inj he1
  clear he1
  have hsize := congrArg sz he3
  have hp_a1 := sz_pos a1
  have hp_b0 := sz_pos b0
  have hp_b1 := sz_pos b1
  simp only [sz] at hsize
  omega

theorem cp_2_21_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (op a0 (sq a1))) = (op (sq b0) (op (sq b1) (sq b0)))) :
    Join (op a0 (sq a1)) (op a0 (op (op (sq b0) (sq (sq b1))) a0)) := by
  cases heq

theorem cp_2_211_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (sq a1)) = (op (sq b0) (op (sq b1) (sq b0)))) :
    Join (op a0 (sq a1)) (op a0 (op (sq (op (sq b0) (sq (sq b1)))) a0)) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_2_2112_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a1) = (op (sq b0) (op (sq b1) (sq b0)))) :
    Join (op a0 (sq a1)) (op a0 (op (sq (op a0 (op (sq b0) (sq (sq b1))))) a0)) := by
  cases heq

theorem cp_3_root_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (sq a0) (op (op a1 (sq (sq a0))) (sq a0))) = (op b0 b0)) :
    Join a1 (sq b0) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  revert he1
  subst b0
  intro he1
  cases he1

theorem cp_3_1_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (op b0 b0)) :
    Join a1 (op (sq b0) (op (op a1 (sq (sq a0))) (sq a0))) := by
  cases heq

theorem cp_3_2_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (op a1 (sq (sq a0))) (sq a0)) = (op b0 b0)) :
    Join a1 (op (sq a0) (sq b0)) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  revert he1
  subst b0
  intro he1
  cases he1

theorem cp_3_21_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a1 (sq (sq a0))) = (op b0 b0)) :
    Join a1 (op (sq a0) (op (sq b0) (sq a0))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  revert he1
  subst b0
  intro he1
  subst a1
  exact ⟨(sq (sq a0)), (Relation.ReflTransGen.refl), ((((Relation.ReflTransGen.refl).tail (root_step .r9 a0 (sq (sq a0)) (leaf 0))).tail (Step.right (sq a0) (root_step .r5 a0 (leaf 0) (leaf 0)))).tail (root_step .r0 (sq a0) (leaf 0) (leaf 0)))⟩

theorem cp_3_212_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (sq a0)) = (op b0 b0)) :
    Join a1 (op (sq a0) (op (op a1 (sq b0)) (sq a0))) := by
  cases heq

theorem cp_3_2121_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (op b0 b0)) :
    Join a1 (op (sq a0) (op (op a1 (sq (sq b0))) (sq a0))) := by
  cases heq

theorem cp_3_22_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (op b0 b0)) :
    Join a1 (op (sq a0) (op (op a1 (sq (sq a0))) (sq b0))) := by
  cases heq

theorem cp_3_root_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (sq a0) (op (op a1 (sq (sq a0))) (sq a0))) = (op b0 (op (op b1 (op b0 (sq b2))) b0))) :
    Join a1 b1 := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  revert he1 he3
  subst b0
  intro he1 he3
  rcases T.op.inj he3 with ⟨he5, he6⟩
  clear he3
  cases he6

theorem cp_3_1_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (op b0 (op (op b1 (op b0 (sq b2))) b0))) :
    Join a1 (op b1 (op (op a1 (sq (sq a0))) (sq a0))) := by
  cases heq

theorem cp_3_2_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (op a1 (sq (sq a0))) (sq a0)) = (op b0 (op (op b1 (op b0 (sq b2))) b0))) :
    Join a1 (op (sq a0) b1) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_3_21_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a1 (sq (sq a0))) = (op b0 (op (op b1 (op b0 (sq b2))) b0))) :
    Join a1 (op (sq a0) (op b1 (sq a0))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_3_212_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (sq a0)) = (op b0 (op (op b1 (op b0 (sq b2))) b0))) :
    Join a1 (op (sq a0) (op (op a1 b1) (sq a0))) := by
  cases heq

theorem cp_3_2121_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (op b0 (op (op b1 (op b0 (sq b2))) b0))) :
    Join a1 (op (sq a0) (op (op a1 (sq b1)) (sq a0))) := by
  cases heq

theorem cp_3_22_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (op b0 (op (op b1 (op b0 (sq b2))) b0))) :
    Join a1 (op (sq a0) (op (op a1 (sq (sq a0))) b1)) := by
  cases heq

theorem cp_3_root_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (sq a0) (op (op a1 (sq (sq a0))) (sq a0))) = (op b0 (op (sq (op b0 (sq b1))) b0))) :
    Join a1 (op b0 (sq b1)) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  revert he1 he3
  subst b0
  intro he1 he3
  cases he3

theorem cp_3_1_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (op b0 (op (sq (op b0 (sq b1))) b0))) :
    Join a1 (op (op b0 (sq b1)) (op (op a1 (sq (sq a0))) (sq a0))) := by
  cases heq

theorem cp_3_2_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (op a1 (sq (sq a0))) (sq a0)) = (op b0 (op (sq (op b0 (sq b1))) b0))) :
    Join a1 (op (sq a0) (op b0 (sq b1))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_3_21_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a1 (sq (sq a0))) = (op b0 (op (sq (op b0 (sq b1))) b0))) :
    Join a1 (op (sq a0) (op (op b0 (sq b1)) (sq a0))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_3_212_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (sq a0)) = (op b0 (op (sq (op b0 (sq b1))) b0))) :
    Join a1 (op (sq a0) (op (op a1 (op b0 (sq b1))) (sq a0))) := by
  cases heq

theorem cp_3_2121_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (op b0 (op (sq (op b0 (sq b1))) b0))) :
    Join a1 (op (sq a0) (op (op a1 (sq (op b0 (sq b1)))) (sq a0))) := by
  cases heq

theorem cp_3_22_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (op b0 (op (sq (op b0 (sq b1))) b0))) :
    Join a1 (op (sq a0) (op (op a1 (sq (sq a0))) (op b0 (sq b1)))) := by
  cases heq

theorem cp_3_root_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (sq a0) (op (op a1 (sq (sq a0))) (sq a0))) = (op (sq b0) (op (op b1 (sq (sq b0))) (sq b0)))) :
    Join a1 b1 := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  have he5 := T.sq.inj he4
  clear he4
  revert he1 he3
  subst a0
  intro he1 he3
  rcases T.op.inj he3 with ⟨he6, he7⟩
  clear he3
  clear he7
  revert he1
  subst a1
  intro he1
  clear he1
  exact ⟨b1, (Relation.ReflTransGen.refl), (Relation.ReflTransGen.refl)⟩

theorem cp_3_1_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (op (sq b0) (op (op b1 (sq (sq b0))) (sq b0)))) :
    Join a1 (op b1 (op (op a1 (sq (sq a0))) (sq a0))) := by
  cases heq

theorem cp_3_2_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (op a1 (sq (sq a0))) (sq a0)) = (op (sq b0) (op (op b1 (sq (sq b0))) (sq b0)))) :
    Join a1 (op (sq a0) b1) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_3_21_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a1 (sq (sq a0))) = (op (sq b0) (op (op b1 (sq (sq b0))) (sq b0)))) :
    Join a1 (op (sq a0) (op b1 (sq a0))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_3_212_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (sq a0)) = (op (sq b0) (op (op b1 (sq (sq b0))) (sq b0)))) :
    Join a1 (op (sq a0) (op (op a1 b1) (sq a0))) := by
  cases heq

theorem cp_3_2121_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (op (sq b0) (op (op b1 (sq (sq b0))) (sq b0)))) :
    Join a1 (op (sq a0) (op (op a1 (sq b1)) (sq a0))) := by
  cases heq

theorem cp_3_22_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (op (sq b0) (op (op b1 (sq (sq b0))) (sq b0)))) :
    Join a1 (op (sq a0) (op (op a1 (sq (sq a0))) b1)) := by
  cases heq

theorem cp_3_root_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (sq a0) (op (op a1 (sq (sq a0))) (sq a0))) = (op (op b0 (op (sq b1) (sq b2))) (op b0 (op b0 (op (sq b1) (sq b2)))))) :
    Join a1 (sq b1) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  cases he4

theorem cp_3_1_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (op (op b0 (op (sq b1) (sq b2))) (op b0 (op b0 (op (sq b1) (sq b2)))))) :
    Join a1 (op (sq b1) (op (op a1 (sq (sq a0))) (sq a0))) := by
  cases heq

theorem cp_3_2_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (op a1 (sq (sq a0))) (sq a0)) = (op (op b0 (op (sq b1) (sq b2))) (op b0 (op b0 (op (sq b1) (sq b2)))))) :
    Join a1 (op (sq a0) (sq b1)) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_3_21_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a1 (sq (sq a0))) = (op (op b0 (op (sq b1) (sq b2))) (op b0 (op b0 (op (sq b1) (sq b2)))))) :
    Join a1 (op (sq a0) (op (sq b1) (sq a0))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_3_212_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (sq a0)) = (op (op b0 (op (sq b1) (sq b2))) (op b0 (op b0 (op (sq b1) (sq b2)))))) :
    Join a1 (op (sq a0) (op (op a1 (sq b1)) (sq a0))) := by
  cases heq

theorem cp_3_2121_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (op (op b0 (op (sq b1) (sq b2))) (op b0 (op b0 (op (sq b1) (sq b2)))))) :
    Join a1 (op (sq a0) (op (op a1 (sq (sq b1))) (sq a0))) := by
  cases heq

theorem cp_3_22_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (op (op b0 (op (sq b1) (sq b2))) (op b0 (op b0 (op (sq b1) (sq b2)))))) :
    Join a1 (op (sq a0) (op (op a1 (sq (sq a0))) (sq b1))) := by
  cases heq

theorem cp_3_root_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (sq a0) (op (op a1 (sq (sq a0))) (sq a0))) = (sq (sq (sq (sq b0))))) :
    Join a1 (sq b0) := by
  cases heq

theorem cp_3_1_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (sq (sq (sq (sq b0))))) :
    Join a1 (op (sq b0) (op (op a1 (sq (sq a0))) (sq a0))) := by
  have he1 := T.sq.inj heq
  clear heq
  subst a0
  exact ⟨a1, (Relation.ReflTransGen.refl), ((((Relation.ReflTransGen.refl).tail (Step.right (sq b0) (Step.left (sq (sq (sq (sq b0)))) (Step.right a1 (root_step .r5 (sq b0) (leaf 0) (leaf 0)))))).tail (Step.right (sq b0) (Step.right (op a1 (sq (sq b0))) (root_step .r5 b0 (leaf 0) (leaf 0))))).tail (root_step .r3 b0 a1 (leaf 0)))⟩

theorem cp_3_2_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (op a1 (sq (sq a0))) (sq a0)) = (sq (sq (sq (sq b0))))) :
    Join a1 (op (sq a0) (sq b0)) := by
  cases heq

theorem cp_3_21_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a1 (sq (sq a0))) = (sq (sq (sq (sq b0))))) :
    Join a1 (op (sq a0) (op (sq b0) (sq a0))) := by
  cases heq

theorem cp_3_212_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (sq a0)) = (sq (sq (sq (sq b0))))) :
    Join a1 (op (sq a0) (op (op a1 (sq b0)) (sq a0))) := by
  have he1 := T.sq.inj heq
  clear heq
  have he2 := T.sq.inj he1
  clear he1
  subst a0
  exact ⟨a1, (Relation.ReflTransGen.refl), ((Relation.ReflTransGen.refl).tail (root_step .r6 b0 a1 (leaf 0)))⟩

theorem cp_3_2121_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (sq (sq (sq (sq b0))))) :
    Join a1 (op (sq a0) (op (op a1 (sq (sq b0))) (sq a0))) := by
  have he1 := T.sq.inj heq
  clear heq
  subst a0
  exact ⟨a1, (Relation.ReflTransGen.refl), ((Relation.ReflTransGen.refl).tail (root_step .r6 (sq b0) a1 (leaf 0)))⟩

theorem cp_3_22_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (sq (sq (sq (sq b0))))) :
    Join a1 (op (sq a0) (op (op a1 (sq (sq a0))) (sq b0))) := by
  have he1 := T.sq.inj heq
  clear heq
  subst a0
  exact ⟨a1, (Relation.ReflTransGen.refl), ((((Relation.ReflTransGen.refl).tail (Step.left (op (op a1 (sq (sq (sq (sq (sq b0)))))) (sq b0)) (root_step .r5 b0 (leaf 0) (leaf 0)))).tail (Step.right (sq b0) (Step.left (sq b0) (Step.right a1 (root_step .r5 (sq b0) (leaf 0) (leaf 0)))))).tail (root_step .r3 b0 a1 (leaf 0)))⟩

theorem cp_3_root_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (sq a0) (op (op a1 (sq (sq a0))) (sq a0))) = (op (sq (sq (sq b0))) (op (op b1 (sq b0)) (sq (sq (sq b0)))))) :
    Join a1 b1 := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  have he5 := T.sq.inj he4
  clear he4
  revert he1 he3
  subst a0
  intro he1 he3
  rcases T.op.inj he3 with ⟨he6, he7⟩
  clear he3
  have he8 := T.sq.inj he7
  clear he7
  have hsize := congrArg sz he8
  have hp_b0 := sz_pos b0
  simp only [sz] at hsize
  omega

theorem cp_3_1_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (op (sq (sq (sq b0))) (op (op b1 (sq b0)) (sq (sq (sq b0)))))) :
    Join a1 (op b1 (op (op a1 (sq (sq a0))) (sq a0))) := by
  cases heq

theorem cp_3_2_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (op a1 (sq (sq a0))) (sq a0)) = (op (sq (sq (sq b0))) (op (op b1 (sq b0)) (sq (sq (sq b0)))))) :
    Join a1 (op (sq a0) b1) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_3_21_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a1 (sq (sq a0))) = (op (sq (sq (sq b0))) (op (op b1 (sq b0)) (sq (sq (sq b0)))))) :
    Join a1 (op (sq a0) (op b1 (sq a0))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_3_212_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (sq a0)) = (op (sq (sq (sq b0))) (op (op b1 (sq b0)) (sq (sq (sq b0)))))) :
    Join a1 (op (sq a0) (op (op a1 b1) (sq a0))) := by
  cases heq

theorem cp_3_2121_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (op (sq (sq (sq b0))) (op (op b1 (sq b0)) (sq (sq (sq b0)))))) :
    Join a1 (op (sq a0) (op (op a1 (sq b1)) (sq a0))) := by
  cases heq

theorem cp_3_22_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (op (sq (sq (sq b0))) (op (op b1 (sq b0)) (sq (sq (sq b0)))))) :
    Join a1 (op (sq a0) (op (op a1 (sq (sq a0))) b1)) := by
  cases heq

theorem cp_3_root_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (sq a0) (op (op a1 (sq (sq a0))) (sq a0))) = (op (op b0 (sq b1)) (op b0 (op b0 (sq b1))))) :
    Join a1 (sq (sq (sq b1))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  cases he4

theorem cp_3_1_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (op (op b0 (sq b1)) (op b0 (op b0 (sq b1))))) :
    Join a1 (op (sq (sq (sq b1))) (op (op a1 (sq (sq a0))) (sq a0))) := by
  cases heq

theorem cp_3_2_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (op a1 (sq (sq a0))) (sq a0)) = (op (op b0 (sq b1)) (op b0 (op b0 (sq b1))))) :
    Join a1 (op (sq a0) (sq (sq (sq b1)))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_3_21_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a1 (sq (sq a0))) = (op (op b0 (sq b1)) (op b0 (op b0 (sq b1))))) :
    Join a1 (op (sq a0) (op (sq (sq (sq b1))) (sq a0))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_3_212_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (sq a0)) = (op (op b0 (sq b1)) (op b0 (op b0 (sq b1))))) :
    Join a1 (op (sq a0) (op (op a1 (sq (sq (sq b1)))) (sq a0))) := by
  cases heq

theorem cp_3_2121_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (op (op b0 (sq b1)) (op b0 (op b0 (sq b1))))) :
    Join a1 (op (sq a0) (op (op a1 (sq (sq (sq (sq b1))))) (sq a0))) := by
  cases heq

theorem cp_3_22_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (op (op b0 (sq b1)) (op b0 (op b0 (sq b1))))) :
    Join a1 (op (sq a0) (op (op a1 (sq (sq a0))) (sq (sq (sq b1))))) := by
  cases heq

theorem cp_3_root_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (sq a0) (op (op a1 (sq (sq a0))) (sq a0))) = (sq (op (sq b0) (sq b1)))) :
    Join a1 (sq (sq (sq b1))) := by
  cases heq

theorem cp_3_1_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (sq (op (sq b0) (sq b1)))) :
    Join a1 (op (sq (sq (sq b1))) (op (op a1 (sq (sq a0))) (sq a0))) := by
  have he1 := T.sq.inj heq
  clear heq
  subst a0
  exact ⟨a1, (Relation.ReflTransGen.refl), (((((Relation.ReflTransGen.refl).tail (Step.right (sq (sq (sq b1))) (Step.left (sq (op (sq b0) (sq b1))) (Step.right a1 (Step.sq (root_step .r8 b0 b1 (leaf 0))))))).tail (Step.right (sq (sq (sq b1))) (Step.left (sq (op (sq b0) (sq b1))) (Step.right a1 (root_step .r5 b1 (leaf 0) (leaf 0)))))).tail (Step.right (sq (sq (sq b1))) (Step.right (op a1 (sq b1)) (root_step .r8 b0 b1 (leaf 0))))).tail (root_step .r6 b1 a1 (leaf 0)))⟩

theorem cp_3_2_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (op a1 (sq (sq a0))) (sq a0)) = (sq (op (sq b0) (sq b1)))) :
    Join a1 (op (sq a0) (sq (sq (sq b1)))) := by
  cases heq

theorem cp_3_21_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a1 (sq (sq a0))) = (sq (op (sq b0) (sq b1)))) :
    Join a1 (op (sq a0) (op (sq (sq (sq b1))) (sq a0))) := by
  cases heq

theorem cp_3_212_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (sq a0)) = (sq (op (sq b0) (sq b1)))) :
    Join a1 (op (sq a0) (op (op a1 (sq (sq (sq b1)))) (sq a0))) := by
  have he1 := T.sq.inj heq
  clear heq
  cases he1

theorem cp_3_2121_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (sq (op (sq b0) (sq b1)))) :
    Join a1 (op (sq a0) (op (op a1 (sq (sq (sq (sq b1))))) (sq a0))) := by
  have he1 := T.sq.inj heq
  clear heq
  subst a0
  exact ⟨a1, (Relation.ReflTransGen.refl), (((((Relation.ReflTransGen.refl).tail (Step.left (op (op a1 (sq (sq (sq (sq b1))))) (sq (op (sq b0) (sq b1)))) (root_step .r8 b0 b1 (leaf 0)))).tail (Step.right (sq (sq (sq b1))) (Step.left (sq (op (sq b0) (sq b1))) (Step.right a1 (root_step .r5 b1 (leaf 0) (leaf 0)))))).tail (Step.right (sq (sq (sq b1))) (Step.right (op a1 (sq b1)) (root_step .r8 b0 b1 (leaf 0))))).tail (root_step .r6 b1 a1 (leaf 0)))⟩

theorem cp_3_22_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (sq (op (sq b0) (sq b1)))) :
    Join a1 (op (sq a0) (op (op a1 (sq (sq a0))) (sq (sq (sq b1))))) := by
  have he1 := T.sq.inj heq
  clear heq
  subst a0
  exact ⟨a1, (Relation.ReflTransGen.refl), ((((Relation.ReflTransGen.refl).tail (Step.left (op (op a1 (sq (sq (op (sq b0) (sq b1))))) (sq (sq (sq b1)))) (root_step .r8 b0 b1 (leaf 0)))).tail (Step.right (sq (sq (sq b1))) (Step.left (sq (sq (sq b1))) (Step.right a1 (Step.sq (root_step .r8 b0 b1 (leaf 0))))))).tail (root_step .r3 (sq (sq b1)) a1 (leaf 0)))⟩

theorem cp_3_root_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (sq a0) (op (op a1 (sq (sq a0))) (sq a0))) = (op (sq b0) (op (sq b1) (sq b0)))) :
    Join a1 (op (sq b0) (sq (sq b1))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  have he5 := T.sq.inj he4
  clear he4
  revert he1 he3
  subst a0
  intro he1 he3
  cases he3

theorem cp_3_1_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (op (sq b0) (op (sq b1) (sq b0)))) :
    Join a1 (op (op (sq b0) (sq (sq b1))) (op (op a1 (sq (sq a0))) (sq a0))) := by
  cases heq

theorem cp_3_2_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (op a1 (sq (sq a0))) (sq a0)) = (op (sq b0) (op (sq b1) (sq b0)))) :
    Join a1 (op (sq a0) (op (sq b0) (sq (sq b1)))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_3_21_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a1 (sq (sq a0))) = (op (sq b0) (op (sq b1) (sq b0)))) :
    Join a1 (op (sq a0) (op (op (sq b0) (sq (sq b1))) (sq a0))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_3_212_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (sq a0)) = (op (sq b0) (op (sq b1) (sq b0)))) :
    Join a1 (op (sq a0) (op (op a1 (op (sq b0) (sq (sq b1)))) (sq a0))) := by
  cases heq

theorem cp_3_2121_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (op (sq b0) (op (sq b1) (sq b0)))) :
    Join a1 (op (sq a0) (op (op a1 (sq (op (sq b0) (sq (sq b1))))) (sq a0))) := by
  cases heq

theorem cp_3_22_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (op (sq b0) (op (sq b1) (sq b0)))) :
    Join a1 (op (sq a0) (op (op a1 (sq (sq a0))) (op (sq b0) (sq (sq b1))))) := by
  cases heq

theorem cp_4_root_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (op a0 (op (sq a1) (sq a2))) (op a0 (op a0 (op (sq a1) (sq a2))))) = (op b0 b0)) :
    Join (sq a1) (sq b0) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  revert he1
  subst b0
  intro he1
  rcases T.op.inj he1 with ⟨he3, he4⟩
  clear he1
  rcases T.op.inj he4 with ⟨he5, he6⟩
  clear he4
  cases he6

theorem cp_4_1_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (op (sq a1) (sq a2))) = (op b0 b0)) :
    Join (sq a1) (op (sq b0) (op a0 (op a0 (op (sq a1) (sq a2))))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  revert he1
  subst b0
  intro he1
  subst a0
  exact ⟨(sq a1), (Relation.ReflTransGen.refl), (((((Relation.ReflTransGen.refl).tail (Step.left (op (op (sq a1) (sq a2)) (op (op (sq a1) (sq a2)) (op (sq a1) (sq a2)))) (root_step .r8 a1 a2 (leaf 0)))).tail (Step.right (sq (sq (sq a2))) (Step.right (op (sq a1) (sq a2)) (root_step .r0 (op (sq a1) (sq a2)) (leaf 0) (leaf 0))))).tail (Step.right (sq (sq (sq a2))) (Step.right (op (sq a1) (sq a2)) (root_step .r8 a1 a2 (leaf 0))))).tail (root_step .r6 a2 (sq a1) (leaf 0)))⟩

theorem cp_4_12_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (sq a1) (sq a2)) = (op b0 b0)) :
    Join (sq a1) (op (op a0 (sq b0)) (op a0 (op a0 (op (sq a1) (sq a2))))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  revert he1
  subst b0
  intro he1
  have he3 := T.sq.inj he1
  clear he1
  subst a1
  exact ⟨(sq a2), (Relation.ReflTransGen.refl), ((((Relation.ReflTransGen.refl).tail (Step.right (op a0 (sq (sq a2))) (Step.right a0 (Step.right a0 (root_step .r0 (sq a2) (leaf 0) (leaf 0)))))).tail (root_step .r7 a0 (sq a2) (leaf 0))).tail (root_step .r5 a2 (leaf 0) (leaf 0)))⟩

theorem cp_4_121_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a1) = (op b0 b0)) :
    Join (sq a1) (op (op a0 (op (sq b0) (sq a2))) (op a0 (op a0 (op (sq a1) (sq a2))))) := by
  cases heq

theorem cp_4_122_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a2) = (op b0 b0)) :
    Join (sq a1) (op (op a0 (op (sq a1) (sq b0))) (op a0 (op a0 (op (sq a1) (sq a2))))) := by
  cases heq

theorem cp_4_2_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (op a0 (op (sq a1) (sq a2)))) = (op b0 b0)) :
    Join (sq a1) (op (op a0 (op (sq a1) (sq a2))) (sq b0)) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  revert he1
  subst b0
  intro he1
  have hsize := congrArg sz he1
  have hp_a0 := sz_pos a0
  have hp_a1 := sz_pos a1
  have hp_a2 := sz_pos a2
  simp only [sz] at hsize
  omega

theorem cp_4_22_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (op (sq a1) (sq a2))) = (op b0 b0)) :
    Join (sq a1) (op (op a0 (op (sq a1) (sq a2))) (op a0 (sq b0))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  revert he1
  subst b0
  intro he1
  subst a0
  exact ⟨(sq a1), (Relation.ReflTransGen.refl), (((((Relation.ReflTransGen.refl).tail (Step.left (op (op (sq a1) (sq a2)) (sq (op (sq a1) (sq a2)))) (root_step .r0 (op (sq a1) (sq a2)) (leaf 0) (leaf 0)))).tail (Step.left (op (op (sq a1) (sq a2)) (sq (op (sq a1) (sq a2)))) (root_step .r8 a1 a2 (leaf 0)))).tail (Step.right (sq (sq (sq a2))) (Step.right (op (sq a1) (sq a2)) (root_step .r8 a1 a2 (leaf 0))))).tail (root_step .r6 a2 (sq a1) (leaf 0)))⟩

theorem cp_4_222_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (sq a1) (sq a2)) = (op b0 b0)) :
    Join (sq a1) (op (op a0 (op (sq a1) (sq a2))) (op a0 (op a0 (sq b0)))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  revert he1
  subst b0
  intro he1
  have he3 := T.sq.inj he1
  clear he1
  subst a1
  exact ⟨(sq a2), (Relation.ReflTransGen.refl), ((((Relation.ReflTransGen.refl).tail (Step.left (op a0 (op a0 (sq (sq a2)))) (Step.right a0 (root_step .r0 (sq a2) (leaf 0) (leaf 0))))).tail (root_step .r7 a0 (sq a2) (leaf 0))).tail (root_step .r5 a2 (leaf 0) (leaf 0)))⟩

theorem cp_4_2221_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a1) = (op b0 b0)) :
    Join (sq a1) (op (op a0 (op (sq a1) (sq a2))) (op a0 (op a0 (op (sq b0) (sq a2))))) := by
  cases heq

theorem cp_4_2222_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a2) = (op b0 b0)) :
    Join (sq a1) (op (op a0 (op (sq a1) (sq a2))) (op a0 (op a0 (op (sq a1) (sq b0))))) := by
  cases heq

theorem cp_4_root_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (op a0 (op (sq a1) (sq a2))) (op a0 (op a0 (op (sq a1) (sq a2))))) = (op b0 (op (op b1 (op b0 (sq b2))) b0))) :
    Join (sq a1) b1 := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  revert he1 he3
  subst b0
  intro he1 he3
  have hsize := congrArg sz he3
  have hp_a0 := sz_pos a0
  have hp_a1 := sz_pos a1
  have hp_a2 := sz_pos a2
  have hp_b1 := sz_pos b1
  have hp_b2 := sz_pos b2
  simp only [sz] at hsize
  omega

theorem cp_4_1_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (op (sq a1) (sq a2))) = (op b0 (op (op b1 (op b0 (sq b2))) b0))) :
    Join (sq a1) (op b1 (op a0 (op a0 (op (sq a1) (sq a2))))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  revert he1 he3
  subst b0
  intro he1 he3
  cases he3

theorem cp_4_12_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (sq a1) (sq a2)) = (op b0 (op (op b1 (op b0 (sq b2))) b0))) :
    Join (sq a1) (op (op a0 b1) (op a0 (op a0 (op (sq a1) (sq a2))))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_4_121_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a1) = (op b0 (op (op b1 (op b0 (sq b2))) b0))) :
    Join (sq a1) (op (op a0 (op b1 (sq a2))) (op a0 (op a0 (op (sq a1) (sq a2))))) := by
  cases heq

theorem cp_4_122_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a2) = (op b0 (op (op b1 (op b0 (sq b2))) b0))) :
    Join (sq a1) (op (op a0 (op (sq a1) b1)) (op a0 (op a0 (op (sq a1) (sq a2))))) := by
  cases heq

theorem cp_4_2_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (op a0 (op (sq a1) (sq a2)))) = (op b0 (op (op b1 (op b0 (sq b2))) b0))) :
    Join (sq a1) (op (op a0 (op (sq a1) (sq a2))) b1) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  revert he1 he3
  subst b0
  intro he1 he3
  revert he1
  subst a0
  intro he1
  rcases T.op.inj he1 with ⟨he5, he6⟩
  clear he1
  cases he6

theorem cp_4_22_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (op (sq a1) (sq a2))) = (op b0 (op (op b1 (op b0 (sq b2))) b0))) :
    Join (sq a1) (op (op a0 (op (sq a1) (sq a2))) (op a0 b1)) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  revert he1 he3
  subst b0
  intro he1 he3
  cases he3

theorem cp_4_222_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (sq a1) (sq a2)) = (op b0 (op (op b1 (op b0 (sq b2))) b0))) :
    Join (sq a1) (op (op a0 (op (sq a1) (sq a2))) (op a0 (op a0 b1))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_4_2221_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a1) = (op b0 (op (op b1 (op b0 (sq b2))) b0))) :
    Join (sq a1) (op (op a0 (op (sq a1) (sq a2))) (op a0 (op a0 (op b1 (sq a2))))) := by
  cases heq

theorem cp_4_2222_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a2) = (op b0 (op (op b1 (op b0 (sq b2))) b0))) :
    Join (sq a1) (op (op a0 (op (sq a1) (sq a2))) (op a0 (op a0 (op (sq a1) b1)))) := by
  cases heq

theorem cp_4_root_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (op a0 (op (sq a1) (sq a2))) (op a0 (op a0 (op (sq a1) (sq a2))))) = (op b0 (op (sq (op b0 (sq b1))) b0))) :
    Join (sq a1) (op b0 (sq b1)) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  revert he1 he3
  subst b0
  intro he1 he3
  have hsize := congrArg sz he3
  have hp_a0 := sz_pos a0
  have hp_a1 := sz_pos a1
  have hp_a2 := sz_pos a2
  have hp_b1 := sz_pos b1
  simp only [sz] at hsize
  omega

theorem cp_4_1_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (op (sq a1) (sq a2))) = (op b0 (op (sq (op b0 (sq b1))) b0))) :
    Join (sq a1) (op (op b0 (sq b1)) (op a0 (op a0 (op (sq a1) (sq a2))))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  revert he1 he3
  subst b0
  intro he1 he3
  have he5 := T.sq.inj he3
  clear he3
  revert he1
  subst a1
  intro he1
  subst a0
  exact ⟨(sq (sq (sq b1))), ((Relation.ReflTransGen.refl).tail (root_step .r8 a2 b1 (leaf 0))), (((Relation.ReflTransGen.refl).tail (Step.right (op (sq a2) (sq b1)) (Step.right (sq a2) (root_step .r2 (sq a2) b1 (leaf 0))))).tail (root_step .r7 (sq a2) b1 (leaf 0)))⟩

theorem cp_4_12_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (sq a1) (sq a2)) = (op b0 (op (sq (op b0 (sq b1))) b0))) :
    Join (sq a1) (op (op a0 (op b0 (sq b1))) (op a0 (op a0 (op (sq a1) (sq a2))))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_4_121_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a1) = (op b0 (op (sq (op b0 (sq b1))) b0))) :
    Join (sq a1) (op (op a0 (op (op b0 (sq b1)) (sq a2))) (op a0 (op a0 (op (sq a1) (sq a2))))) := by
  cases heq

theorem cp_4_122_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a2) = (op b0 (op (sq (op b0 (sq b1))) b0))) :
    Join (sq a1) (op (op a0 (op (sq a1) (op b0 (sq b1)))) (op a0 (op a0 (op (sq a1) (sq a2))))) := by
  cases heq

theorem cp_4_2_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (op a0 (op (sq a1) (sq a2)))) = (op b0 (op (sq (op b0 (sq b1))) b0))) :
    Join (sq a1) (op (op a0 (op (sq a1) (sq a2))) (op b0 (sq b1))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  revert he1 he3
  subst b0
  intro he1 he3
  revert he1
  subst a0
  intro he1
  cases he1

theorem cp_4_22_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (op (sq a1) (sq a2))) = (op b0 (op (sq (op b0 (sq b1))) b0))) :
    Join (sq a1) (op (op a0 (op (sq a1) (sq a2))) (op a0 (op b0 (sq b1)))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  revert he1 he3
  subst b0
  intro he1 he3
  have he5 := T.sq.inj he3
  clear he3
  revert he1
  subst a1
  intro he1
  subst a0
  exact ⟨(sq (sq (sq b1))), ((Relation.ReflTransGen.refl).tail (root_step .r8 a2 b1 (leaf 0))), (((Relation.ReflTransGen.refl).tail (Step.left (op (sq a2) (op (sq a2) (sq b1))) (root_step .r2 (sq a2) b1 (leaf 0)))).tail (root_step .r7 (sq a2) b1 (leaf 0)))⟩

theorem cp_4_222_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (sq a1) (sq a2)) = (op b0 (op (sq (op b0 (sq b1))) b0))) :
    Join (sq a1) (op (op a0 (op (sq a1) (sq a2))) (op a0 (op a0 (op b0 (sq b1))))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_4_2221_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a1) = (op b0 (op (sq (op b0 (sq b1))) b0))) :
    Join (sq a1) (op (op a0 (op (sq a1) (sq a2))) (op a0 (op a0 (op (op b0 (sq b1)) (sq a2))))) := by
  cases heq

theorem cp_4_2222_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a2) = (op b0 (op (sq (op b0 (sq b1))) b0))) :
    Join (sq a1) (op (op a0 (op (sq a1) (sq a2))) (op a0 (op a0 (op (sq a1) (op b0 (sq b1)))))) := by
  cases heq

theorem cp_4_root_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (op a0 (op (sq a1) (sq a2))) (op a0 (op a0 (op (sq a1) (sq a2))))) = (op (sq b0) (op (op b1 (sq (sq b0))) (sq b0)))) :
    Join (sq a1) b1 := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  cases he4

theorem cp_4_1_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (op (sq a1) (sq a2))) = (op (sq b0) (op (op b1 (sq (sq b0))) (sq b0)))) :
    Join (sq a1) (op b1 (op a0 (op a0 (op (sq a1) (sq a2))))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  have he5 := T.sq.inj he4
  clear he4
  revert he1 he3
  subst a2
  intro he1 he3
  cases he3

theorem cp_4_12_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (sq a1) (sq a2)) = (op (sq b0) (op (op b1 (sq (sq b0))) (sq b0)))) :
    Join (sq a1) (op (op a0 b1) (op a0 (op a0 (op (sq a1) (sq a2))))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_4_121_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a1) = (op (sq b0) (op (op b1 (sq (sq b0))) (sq b0)))) :
    Join (sq a1) (op (op a0 (op b1 (sq a2))) (op a0 (op a0 (op (sq a1) (sq a2))))) := by
  cases heq

theorem cp_4_122_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a2) = (op (sq b0) (op (op b1 (sq (sq b0))) (sq b0)))) :
    Join (sq a1) (op (op a0 (op (sq a1) b1)) (op a0 (op a0 (op (sq a1) (sq a2))))) := by
  cases heq

theorem cp_4_2_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (op a0 (op (sq a1) (sq a2)))) = (op (sq b0) (op (op b1 (sq (sq b0))) (sq b0)))) :
    Join (sq a1) (op (op a0 (op (sq a1) (sq a2))) b1) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  cases he4

theorem cp_4_22_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (op (sq a1) (sq a2))) = (op (sq b0) (op (op b1 (sq (sq b0))) (sq b0)))) :
    Join (sq a1) (op (op a0 (op (sq a1) (sq a2))) (op a0 b1)) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  have he5 := T.sq.inj he4
  clear he4
  revert he1 he3
  subst a2
  intro he1 he3
  cases he3

theorem cp_4_222_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (sq a1) (sq a2)) = (op (sq b0) (op (op b1 (sq (sq b0))) (sq b0)))) :
    Join (sq a1) (op (op a0 (op (sq a1) (sq a2))) (op a0 (op a0 b1))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_4_2221_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a1) = (op (sq b0) (op (op b1 (sq (sq b0))) (sq b0)))) :
    Join (sq a1) (op (op a0 (op (sq a1) (sq a2))) (op a0 (op a0 (op b1 (sq a2))))) := by
  cases heq

theorem cp_4_2222_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a2) = (op (sq b0) (op (op b1 (sq (sq b0))) (sq b0)))) :
    Join (sq a1) (op (op a0 (op (sq a1) (sq a2))) (op a0 (op a0 (op (sq a1) b1)))) := by
  cases heq

theorem cp_4_root_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (op a0 (op (sq a1) (sq a2))) (op a0 (op a0 (op (sq a1) (sq a2))))) = (op (op b0 (op (sq b1) (sq b2))) (op b0 (op b0 (op (sq b1) (sq b2)))))) :
    Join (sq a1) (sq b1) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  rcases T.op.inj he4 with ⟨he5, he6⟩
  clear he4
  rcases T.op.inj he6 with ⟨he7, he8⟩
  clear he6
  have he9 := T.sq.inj he8
  clear he8
  revert he1 he3 he5 he7
  subst a2
  intro he1 he3 he5 he7
  have he10 := T.sq.inj he7
  clear he7
  revert he1 he3 he5
  subst a1
  intro he1 he3 he5
  revert he1 he3
  subst a0
  intro he1 he3
  clear he3
  clear he1
  exact ⟨(sq b1), (Relation.ReflTransGen.refl), (Relation.ReflTransGen.refl)⟩

theorem cp_4_1_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (op (sq a1) (sq a2))) = (op (op b0 (op (sq b1) (sq b2))) (op b0 (op b0 (op (sq b1) (sq b2)))))) :
    Join (sq a1) (op (sq b1) (op a0 (op a0 (op (sq a1) (sq a2))))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  cases he4

theorem cp_4_12_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (sq a1) (sq a2)) = (op (op b0 (op (sq b1) (sq b2))) (op b0 (op b0 (op (sq b1) (sq b2)))))) :
    Join (sq a1) (op (op a0 (sq b1)) (op a0 (op a0 (op (sq a1) (sq a2))))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_4_121_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a1) = (op (op b0 (op (sq b1) (sq b2))) (op b0 (op b0 (op (sq b1) (sq b2)))))) :
    Join (sq a1) (op (op a0 (op (sq b1) (sq a2))) (op a0 (op a0 (op (sq a1) (sq a2))))) := by
  cases heq

theorem cp_4_122_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a2) = (op (op b0 (op (sq b1) (sq b2))) (op b0 (op b0 (op (sq b1) (sq b2)))))) :
    Join (sq a1) (op (op a0 (op (sq a1) (sq b1))) (op a0 (op a0 (op (sq a1) (sq a2))))) := by
  cases heq

theorem cp_4_2_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (op a0 (op (sq a1) (sq a2)))) = (op (op b0 (op (sq b1) (sq b2))) (op b0 (op b0 (op (sq b1) (sq b2)))))) :
    Join (sq a1) (op (op a0 (op (sq a1) (sq a2))) (sq b1)) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  rcases T.op.inj he4 with ⟨he5, he6⟩
  clear he4
  cases he6

theorem cp_4_22_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (op (sq a1) (sq a2))) = (op (op b0 (op (sq b1) (sq b2))) (op b0 (op b0 (op (sq b1) (sq b2)))))) :
    Join (sq a1) (op (op a0 (op (sq a1) (sq a2))) (op a0 (sq b1))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  cases he4

theorem cp_4_222_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (sq a1) (sq a2)) = (op (op b0 (op (sq b1) (sq b2))) (op b0 (op b0 (op (sq b1) (sq b2)))))) :
    Join (sq a1) (op (op a0 (op (sq a1) (sq a2))) (op a0 (op a0 (sq b1)))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_4_2221_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a1) = (op (op b0 (op (sq b1) (sq b2))) (op b0 (op b0 (op (sq b1) (sq b2)))))) :
    Join (sq a1) (op (op a0 (op (sq a1) (sq a2))) (op a0 (op a0 (op (sq b1) (sq a2))))) := by
  cases heq

theorem cp_4_2222_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a2) = (op (op b0 (op (sq b1) (sq b2))) (op b0 (op b0 (op (sq b1) (sq b2)))))) :
    Join (sq a1) (op (op a0 (op (sq a1) (sq a2))) (op a0 (op a0 (op (sq a1) (sq b1))))) := by
  cases heq

theorem cp_4_root_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (op a0 (op (sq a1) (sq a2))) (op a0 (op a0 (op (sq a1) (sq a2))))) = (sq (sq (sq (sq b0))))) :
    Join (sq a1) (sq b0) := by
  cases heq

theorem cp_4_1_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (op (sq a1) (sq a2))) = (sq (sq (sq (sq b0))))) :
    Join (sq a1) (op (sq b0) (op a0 (op a0 (op (sq a1) (sq a2))))) := by
  cases heq

theorem cp_4_12_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (sq a1) (sq a2)) = (sq (sq (sq (sq b0))))) :
    Join (sq a1) (op (op a0 (sq b0)) (op a0 (op a0 (op (sq a1) (sq a2))))) := by
  cases heq

theorem cp_4_121_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a1) = (sq (sq (sq (sq b0))))) :
    Join (sq a1) (op (op a0 (op (sq b0) (sq a2))) (op a0 (op a0 (op (sq a1) (sq a2))))) := by
  have he1 := T.sq.inj heq
  clear heq
  subst a1
  exact ⟨(sq b0), ((Relation.ReflTransGen.refl).tail (root_step .r5 b0 (leaf 0) (leaf 0))), (((Relation.ReflTransGen.refl).tail (Step.right (op a0 (op (sq b0) (sq a2))) (Step.right a0 (Step.right a0 (Step.left (sq a2) (root_step .r5 b0 (leaf 0) (leaf 0))))))).tail (root_step .r4 a0 b0 a2))⟩

theorem cp_4_122_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a2) = (sq (sq (sq (sq b0))))) :
    Join (sq a1) (op (op a0 (op (sq a1) (sq b0))) (op a0 (op a0 (op (sq a1) (sq a2))))) := by
  have he1 := T.sq.inj heq
  clear heq
  subst a2
  exact ⟨(sq a1), (Relation.ReflTransGen.refl), (((Relation.ReflTransGen.refl).tail (Step.right (op a0 (op (sq a1) (sq b0))) (Step.right a0 (Step.right a0 (Step.right (sq a1) (root_step .r5 b0 (leaf 0) (leaf 0))))))).tail (root_step .r4 a0 a1 b0))⟩

theorem cp_4_2_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (op a0 (op (sq a1) (sq a2)))) = (sq (sq (sq (sq b0))))) :
    Join (sq a1) (op (op a0 (op (sq a1) (sq a2))) (sq b0)) := by
  cases heq

theorem cp_4_22_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (op (sq a1) (sq a2))) = (sq (sq (sq (sq b0))))) :
    Join (sq a1) (op (op a0 (op (sq a1) (sq a2))) (op a0 (sq b0))) := by
  cases heq

theorem cp_4_222_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (sq a1) (sq a2)) = (sq (sq (sq (sq b0))))) :
    Join (sq a1) (op (op a0 (op (sq a1) (sq a2))) (op a0 (op a0 (sq b0)))) := by
  cases heq

theorem cp_4_2221_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a1) = (sq (sq (sq (sq b0))))) :
    Join (sq a1) (op (op a0 (op (sq a1) (sq a2))) (op a0 (op a0 (op (sq b0) (sq a2))))) := by
  have he1 := T.sq.inj heq
  clear heq
  subst a1
  exact ⟨(sq b0), ((Relation.ReflTransGen.refl).tail (root_step .r5 b0 (leaf 0) (leaf 0))), (((Relation.ReflTransGen.refl).tail (Step.left (op a0 (op a0 (op (sq b0) (sq a2)))) (Step.right a0 (Step.left (sq a2) (root_step .r5 b0 (leaf 0) (leaf 0)))))).tail (root_step .r4 a0 b0 a2))⟩

theorem cp_4_2222_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a2) = (sq (sq (sq (sq b0))))) :
    Join (sq a1) (op (op a0 (op (sq a1) (sq a2))) (op a0 (op a0 (op (sq a1) (sq b0))))) := by
  have he1 := T.sq.inj heq
  clear heq
  subst a2
  exact ⟨(sq a1), (Relation.ReflTransGen.refl), (((Relation.ReflTransGen.refl).tail (Step.left (op a0 (op a0 (op (sq a1) (sq b0)))) (Step.right a0 (Step.right (sq a1) (root_step .r5 b0 (leaf 0) (leaf 0)))))).tail (root_step .r4 a0 a1 b0))⟩

theorem cp_4_root_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (op a0 (op (sq a1) (sq a2))) (op a0 (op a0 (op (sq a1) (sq a2))))) = (op (sq (sq (sq b0))) (op (op b1 (sq b0)) (sq (sq (sq b0)))))) :
    Join (sq a1) b1 := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  cases he4

theorem cp_4_1_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (op (sq a1) (sq a2))) = (op (sq (sq (sq b0))) (op (op b1 (sq b0)) (sq (sq (sq b0)))))) :
    Join (sq a1) (op b1 (op a0 (op a0 (op (sq a1) (sq a2))))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  have he5 := T.sq.inj he4
  clear he4
  revert he1 he3
  subst a2
  intro he1 he3
  cases he3

theorem cp_4_12_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (sq a1) (sq a2)) = (op (sq (sq (sq b0))) (op (op b1 (sq b0)) (sq (sq (sq b0)))))) :
    Join (sq a1) (op (op a0 b1) (op a0 (op a0 (op (sq a1) (sq a2))))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_4_121_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a1) = (op (sq (sq (sq b0))) (op (op b1 (sq b0)) (sq (sq (sq b0)))))) :
    Join (sq a1) (op (op a0 (op b1 (sq a2))) (op a0 (op a0 (op (sq a1) (sq a2))))) := by
  cases heq

theorem cp_4_122_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a2) = (op (sq (sq (sq b0))) (op (op b1 (sq b0)) (sq (sq (sq b0)))))) :
    Join (sq a1) (op (op a0 (op (sq a1) b1)) (op a0 (op a0 (op (sq a1) (sq a2))))) := by
  cases heq

theorem cp_4_2_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (op a0 (op (sq a1) (sq a2)))) = (op (sq (sq (sq b0))) (op (op b1 (sq b0)) (sq (sq (sq b0)))))) :
    Join (sq a1) (op (op a0 (op (sq a1) (sq a2))) b1) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  cases he4

theorem cp_4_22_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (op (sq a1) (sq a2))) = (op (sq (sq (sq b0))) (op (op b1 (sq b0)) (sq (sq (sq b0)))))) :
    Join (sq a1) (op (op a0 (op (sq a1) (sq a2))) (op a0 b1)) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  have he5 := T.sq.inj he4
  clear he4
  revert he1 he3
  subst a2
  intro he1 he3
  cases he3

theorem cp_4_222_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (sq a1) (sq a2)) = (op (sq (sq (sq b0))) (op (op b1 (sq b0)) (sq (sq (sq b0)))))) :
    Join (sq a1) (op (op a0 (op (sq a1) (sq a2))) (op a0 (op a0 b1))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_4_2221_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a1) = (op (sq (sq (sq b0))) (op (op b1 (sq b0)) (sq (sq (sq b0)))))) :
    Join (sq a1) (op (op a0 (op (sq a1) (sq a2))) (op a0 (op a0 (op b1 (sq a2))))) := by
  cases heq

theorem cp_4_2222_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a2) = (op (sq (sq (sq b0))) (op (op b1 (sq b0)) (sq (sq (sq b0)))))) :
    Join (sq a1) (op (op a0 (op (sq a1) (sq a2))) (op a0 (op a0 (op (sq a1) b1)))) := by
  cases heq

theorem cp_4_root_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (op a0 (op (sq a1) (sq a2))) (op a0 (op a0 (op (sq a1) (sq a2))))) = (op (op b0 (sq b1)) (op b0 (op b0 (sq b1))))) :
    Join (sq a1) (sq (sq (sq b1))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  rcases T.op.inj he4 with ⟨he5, he6⟩
  clear he4
  cases he6

theorem cp_4_1_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (op (sq a1) (sq a2))) = (op (op b0 (sq b1)) (op b0 (op b0 (sq b1))))) :
    Join (sq a1) (op (sq (sq (sq b1))) (op a0 (op a0 (op (sq a1) (sq a2))))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  cases he4

theorem cp_4_12_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (sq a1) (sq a2)) = (op (op b0 (sq b1)) (op b0 (op b0 (sq b1))))) :
    Join (sq a1) (op (op a0 (sq (sq (sq b1)))) (op a0 (op a0 (op (sq a1) (sq a2))))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_4_121_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a1) = (op (op b0 (sq b1)) (op b0 (op b0 (sq b1))))) :
    Join (sq a1) (op (op a0 (op (sq (sq (sq b1))) (sq a2))) (op a0 (op a0 (op (sq a1) (sq a2))))) := by
  cases heq

theorem cp_4_122_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a2) = (op (op b0 (sq b1)) (op b0 (op b0 (sq b1))))) :
    Join (sq a1) (op (op a0 (op (sq a1) (sq (sq (sq b1))))) (op a0 (op a0 (op (sq a1) (sq a2))))) := by
  cases heq

theorem cp_4_2_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (op a0 (op (sq a1) (sq a2)))) = (op (op b0 (sq b1)) (op b0 (op b0 (sq b1))))) :
    Join (sq a1) (op (op a0 (op (sq a1) (sq a2))) (sq (sq (sq b1)))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  rcases T.op.inj he4 with ⟨he5, he6⟩
  clear he4
  have he7 := T.sq.inj he6
  clear he6
  revert he1 he3 he5
  subst a2
  intro he1 he3 he5
  revert he1 he3
  subst b0
  intro he1 he3
  revert he1
  subst a0
  intro he1
  cases he1

theorem cp_4_22_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (op (sq a1) (sq a2))) = (op (op b0 (sq b1)) (op b0 (op b0 (sq b1))))) :
    Join (sq a1) (op (op a0 (op (sq a1) (sq a2))) (op a0 (sq (sq (sq b1))))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  cases he4

theorem cp_4_222_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (sq a1) (sq a2)) = (op (op b0 (sq b1)) (op b0 (op b0 (sq b1))))) :
    Join (sq a1) (op (op a0 (op (sq a1) (sq a2))) (op a0 (op a0 (sq (sq (sq b1)))))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_4_2221_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a1) = (op (op b0 (sq b1)) (op b0 (op b0 (sq b1))))) :
    Join (sq a1) (op (op a0 (op (sq a1) (sq a2))) (op a0 (op a0 (op (sq (sq (sq b1))) (sq a2))))) := by
  cases heq

theorem cp_4_2222_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a2) = (op (op b0 (sq b1)) (op b0 (op b0 (sq b1))))) :
    Join (sq a1) (op (op a0 (op (sq a1) (sq a2))) (op a0 (op a0 (op (sq a1) (sq (sq (sq b1))))))) := by
  cases heq

theorem cp_4_root_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (op a0 (op (sq a1) (sq a2))) (op a0 (op a0 (op (sq a1) (sq a2))))) = (sq (op (sq b0) (sq b1)))) :
    Join (sq a1) (sq (sq (sq b1))) := by
  cases heq

theorem cp_4_1_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (op (sq a1) (sq a2))) = (sq (op (sq b0) (sq b1)))) :
    Join (sq a1) (op (sq (sq (sq b1))) (op a0 (op a0 (op (sq a1) (sq a2))))) := by
  cases heq

theorem cp_4_12_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (sq a1) (sq a2)) = (sq (op (sq b0) (sq b1)))) :
    Join (sq a1) (op (op a0 (sq (sq (sq b1)))) (op a0 (op a0 (op (sq a1) (sq a2))))) := by
  cases heq

theorem cp_4_121_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a1) = (sq (op (sq b0) (sq b1)))) :
    Join (sq a1) (op (op a0 (op (sq (sq (sq b1))) (sq a2))) (op a0 (op a0 (op (sq a1) (sq a2))))) := by
  have he1 := T.sq.inj heq
  clear heq
  subst a1
  exact ⟨(sq (sq (sq b1))), ((Relation.ReflTransGen.refl).tail (root_step .r8 b0 b1 (leaf 0))), (((Relation.ReflTransGen.refl).tail (Step.right (op a0 (op (sq (sq (sq b1))) (sq a2))) (Step.right a0 (Step.right a0 (Step.left (sq a2) (root_step .r8 b0 b1 (leaf 0))))))).tail (root_step .r4 a0 (sq (sq b1)) a2))⟩

theorem cp_4_122_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a2) = (sq (op (sq b0) (sq b1)))) :
    Join (sq a1) (op (op a0 (op (sq a1) (sq (sq (sq b1))))) (op a0 (op a0 (op (sq a1) (sq a2))))) := by
  have he1 := T.sq.inj heq
  clear heq
  subst a2
  exact ⟨(sq a1), (Relation.ReflTransGen.refl), (((Relation.ReflTransGen.refl).tail (Step.right (op a0 (op (sq a1) (sq (sq (sq b1))))) (Step.right a0 (Step.right a0 (Step.right (sq a1) (root_step .r8 b0 b1 (leaf 0))))))).tail (root_step .r4 a0 a1 (sq (sq b1))))⟩

theorem cp_4_2_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (op a0 (op (sq a1) (sq a2)))) = (sq (op (sq b0) (sq b1)))) :
    Join (sq a1) (op (op a0 (op (sq a1) (sq a2))) (sq (sq (sq b1)))) := by
  cases heq

theorem cp_4_22_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (op (sq a1) (sq a2))) = (sq (op (sq b0) (sq b1)))) :
    Join (sq a1) (op (op a0 (op (sq a1) (sq a2))) (op a0 (sq (sq (sq b1))))) := by
  cases heq

theorem cp_4_222_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (sq a1) (sq a2)) = (sq (op (sq b0) (sq b1)))) :
    Join (sq a1) (op (op a0 (op (sq a1) (sq a2))) (op a0 (op a0 (sq (sq (sq b1)))))) := by
  cases heq

theorem cp_4_2221_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a1) = (sq (op (sq b0) (sq b1)))) :
    Join (sq a1) (op (op a0 (op (sq a1) (sq a2))) (op a0 (op a0 (op (sq (sq (sq b1))) (sq a2))))) := by
  have he1 := T.sq.inj heq
  clear heq
  subst a1
  exact ⟨(sq (sq (sq b1))), ((Relation.ReflTransGen.refl).tail (root_step .r8 b0 b1 (leaf 0))), (((Relation.ReflTransGen.refl).tail (Step.left (op a0 (op a0 (op (sq (sq (sq b1))) (sq a2)))) (Step.right a0 (Step.left (sq a2) (root_step .r8 b0 b1 (leaf 0)))))).tail (root_step .r4 a0 (sq (sq b1)) a2))⟩

theorem cp_4_2222_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a2) = (sq (op (sq b0) (sq b1)))) :
    Join (sq a1) (op (op a0 (op (sq a1) (sq a2))) (op a0 (op a0 (op (sq a1) (sq (sq (sq b1))))))) := by
  have he1 := T.sq.inj heq
  clear heq
  subst a2
  exact ⟨(sq a1), (Relation.ReflTransGen.refl), (((Relation.ReflTransGen.refl).tail (Step.left (op a0 (op a0 (op (sq a1) (sq (sq (sq b1)))))) (Step.right a0 (Step.right (sq a1) (root_step .r8 b0 b1 (leaf 0)))))).tail (root_step .r4 a0 a1 (sq (sq b1))))⟩

theorem cp_4_root_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (op a0 (op (sq a1) (sq a2))) (op a0 (op a0 (op (sq a1) (sq a2))))) = (op (sq b0) (op (sq b1) (sq b0)))) :
    Join (sq a1) (op (sq b0) (sq (sq b1))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  cases he4

theorem cp_4_1_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (op (sq a1) (sq a2))) = (op (sq b0) (op (sq b1) (sq b0)))) :
    Join (sq a1) (op (op (sq b0) (sq (sq b1))) (op a0 (op a0 (op (sq a1) (sq a2))))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  have he5 := T.sq.inj he4
  clear he4
  revert he1 he3
  subst a2
  intro he1 he3
  have he6 := T.sq.inj he3
  clear he3
  revert he1
  subst a1
  intro he1
  subst a0
  exact ⟨(sq b1), (Relation.ReflTransGen.refl), ((((Relation.ReflTransGen.refl).tail (Step.right (op (sq b0) (sq (sq b1))) (Step.right (sq b0) (root_step .r9 b0 b1 (leaf 0))))).tail (root_step .r7 (sq b0) (sq b1) (leaf 0))).tail (root_step .r5 b1 (leaf 0) (leaf 0)))⟩

theorem cp_4_12_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (sq a1) (sq a2)) = (op (sq b0) (op (sq b1) (sq b0)))) :
    Join (sq a1) (op (op a0 (op (sq b0) (sq (sq b1)))) (op a0 (op a0 (op (sq a1) (sq a2))))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_4_121_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a1) = (op (sq b0) (op (sq b1) (sq b0)))) :
    Join (sq a1) (op (op a0 (op (op (sq b0) (sq (sq b1))) (sq a2))) (op a0 (op a0 (op (sq a1) (sq a2))))) := by
  cases heq

theorem cp_4_122_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a2) = (op (sq b0) (op (sq b1) (sq b0)))) :
    Join (sq a1) (op (op a0 (op (sq a1) (op (sq b0) (sq (sq b1))))) (op a0 (op a0 (op (sq a1) (sq a2))))) := by
  cases heq

theorem cp_4_2_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (op a0 (op (sq a1) (sq a2)))) = (op (sq b0) (op (sq b1) (sq b0)))) :
    Join (sq a1) (op (op a0 (op (sq a1) (sq a2))) (op (sq b0) (sq (sq b1)))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  cases he4

theorem cp_4_22_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (op (sq a1) (sq a2))) = (op (sq b0) (op (sq b1) (sq b0)))) :
    Join (sq a1) (op (op a0 (op (sq a1) (sq a2))) (op a0 (op (sq b0) (sq (sq b1))))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  have he5 := T.sq.inj he4
  clear he4
  revert he1 he3
  subst a2
  intro he1 he3
  have he6 := T.sq.inj he3
  clear he3
  revert he1
  subst a1
  intro he1
  subst a0
  exact ⟨(sq b1), (Relation.ReflTransGen.refl), ((((Relation.ReflTransGen.refl).tail (Step.left (op (sq b0) (op (sq b0) (sq (sq b1)))) (root_step .r9 b0 b1 (leaf 0)))).tail (root_step .r7 (sq b0) (sq b1) (leaf 0))).tail (root_step .r5 b1 (leaf 0) (leaf 0)))⟩

theorem cp_4_222_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (sq a1) (sq a2)) = (op (sq b0) (op (sq b1) (sq b0)))) :
    Join (sq a1) (op (op a0 (op (sq a1) (sq a2))) (op a0 (op a0 (op (sq b0) (sq (sq b1)))))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_4_2221_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a1) = (op (sq b0) (op (sq b1) (sq b0)))) :
    Join (sq a1) (op (op a0 (op (sq a1) (sq a2))) (op a0 (op a0 (op (op (sq b0) (sq (sq b1))) (sq a2))))) := by
  cases heq

theorem cp_4_2222_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a2) = (op (sq b0) (op (sq b1) (sq b0)))) :
    Join (sq a1) (op (op a0 (op (sq a1) (sq a2))) (op a0 (op a0 (op (sq a1) (op (sq b0) (sq (sq b1))))))) := by
  cases heq

theorem cp_5_root_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (sq (sq (sq a0)))) = (op b0 b0)) :
    Join (sq a0) (sq b0) := by
  cases heq

theorem cp_5_1_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (sq (sq a0))) = (op b0 b0)) :
    Join (sq a0) (sq (sq b0)) := by
  cases heq

theorem cp_5_11_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (sq a0)) = (op b0 b0)) :
    Join (sq a0) (sq (sq (sq b0))) := by
  cases heq

theorem cp_5_111_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (op b0 b0)) :
    Join (sq a0) (sq (sq (sq (sq b0)))) := by
  cases heq

theorem cp_5_root_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (sq (sq (sq a0)))) = (op b0 (op (op b1 (op b0 (sq b2))) b0))) :
    Join (sq a0) b1 := by
  cases heq

theorem cp_5_1_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (sq (sq a0))) = (op b0 (op (op b1 (op b0 (sq b2))) b0))) :
    Join (sq a0) (sq b1) := by
  cases heq

theorem cp_5_11_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (sq a0)) = (op b0 (op (op b1 (op b0 (sq b2))) b0))) :
    Join (sq a0) (sq (sq b1)) := by
  cases heq

theorem cp_5_111_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (op b0 (op (op b1 (op b0 (sq b2))) b0))) :
    Join (sq a0) (sq (sq (sq b1))) := by
  cases heq

theorem cp_5_root_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (sq (sq (sq a0)))) = (op b0 (op (sq (op b0 (sq b1))) b0))) :
    Join (sq a0) (op b0 (sq b1)) := by
  cases heq

theorem cp_5_1_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (sq (sq a0))) = (op b0 (op (sq (op b0 (sq b1))) b0))) :
    Join (sq a0) (sq (op b0 (sq b1))) := by
  cases heq

theorem cp_5_11_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (sq a0)) = (op b0 (op (sq (op b0 (sq b1))) b0))) :
    Join (sq a0) (sq (sq (op b0 (sq b1)))) := by
  cases heq

theorem cp_5_111_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (op b0 (op (sq (op b0 (sq b1))) b0))) :
    Join (sq a0) (sq (sq (sq (op b0 (sq b1))))) := by
  cases heq

theorem cp_5_root_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (sq (sq (sq a0)))) = (op (sq b0) (op (op b1 (sq (sq b0))) (sq b0)))) :
    Join (sq a0) b1 := by
  cases heq

theorem cp_5_1_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (sq (sq a0))) = (op (sq b0) (op (op b1 (sq (sq b0))) (sq b0)))) :
    Join (sq a0) (sq b1) := by
  cases heq

theorem cp_5_11_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (sq a0)) = (op (sq b0) (op (op b1 (sq (sq b0))) (sq b0)))) :
    Join (sq a0) (sq (sq b1)) := by
  cases heq

theorem cp_5_111_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (op (sq b0) (op (op b1 (sq (sq b0))) (sq b0)))) :
    Join (sq a0) (sq (sq (sq b1))) := by
  cases heq

theorem cp_5_root_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (sq (sq (sq a0)))) = (op (op b0 (op (sq b1) (sq b2))) (op b0 (op b0 (op (sq b1) (sq b2)))))) :
    Join (sq a0) (sq b1) := by
  cases heq

theorem cp_5_1_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (sq (sq a0))) = (op (op b0 (op (sq b1) (sq b2))) (op b0 (op b0 (op (sq b1) (sq b2)))))) :
    Join (sq a0) (sq (sq b1)) := by
  cases heq

theorem cp_5_11_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (sq a0)) = (op (op b0 (op (sq b1) (sq b2))) (op b0 (op b0 (op (sq b1) (sq b2)))))) :
    Join (sq a0) (sq (sq (sq b1))) := by
  cases heq

theorem cp_5_111_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (op (op b0 (op (sq b1) (sq b2))) (op b0 (op b0 (op (sq b1) (sq b2)))))) :
    Join (sq a0) (sq (sq (sq (sq b1)))) := by
  cases heq

theorem cp_5_root_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (sq (sq (sq a0)))) = (sq (sq (sq (sq b0))))) :
    Join (sq a0) (sq b0) := by
  have he1 := T.sq.inj heq
  clear heq
  have he2 := T.sq.inj he1
  clear he1
  have he3 := T.sq.inj he2
  clear he2
  have he4 := T.sq.inj he3
  clear he3
  subst a0
  exact ⟨(sq b0), (Relation.ReflTransGen.refl), (Relation.ReflTransGen.refl)⟩

theorem cp_5_1_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (sq (sq a0))) = (sq (sq (sq (sq b0))))) :
    Join (sq a0) (sq (sq b0)) := by
  have he1 := T.sq.inj heq
  clear heq
  have he2 := T.sq.inj he1
  clear he1
  have he3 := T.sq.inj he2
  clear he2
  subst a0
  exact ⟨(sq (sq b0)), (Relation.ReflTransGen.refl), (Relation.ReflTransGen.refl)⟩

theorem cp_5_11_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (sq a0)) = (sq (sq (sq (sq b0))))) :
    Join (sq a0) (sq (sq (sq b0))) := by
  have he1 := T.sq.inj heq
  clear heq
  have he2 := T.sq.inj he1
  clear he1
  subst a0
  exact ⟨(sq (sq (sq b0))), (Relation.ReflTransGen.refl), (Relation.ReflTransGen.refl)⟩

theorem cp_5_111_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (sq (sq (sq (sq b0))))) :
    Join (sq a0) (sq (sq (sq (sq b0)))) := by
  have he1 := T.sq.inj heq
  clear heq
  subst a0
  exact ⟨(sq b0), ((Relation.ReflTransGen.refl).tail (root_step .r5 b0 (leaf 0) (leaf 0))), ((Relation.ReflTransGen.refl).tail (root_step .r5 b0 (leaf 0) (leaf 0)))⟩

theorem cp_5_root_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (sq (sq (sq a0)))) = (op (sq (sq (sq b0))) (op (op b1 (sq b0)) (sq (sq (sq b0)))))) :
    Join (sq a0) b1 := by
  cases heq

theorem cp_5_1_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (sq (sq a0))) = (op (sq (sq (sq b0))) (op (op b1 (sq b0)) (sq (sq (sq b0)))))) :
    Join (sq a0) (sq b1) := by
  cases heq

theorem cp_5_11_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (sq a0)) = (op (sq (sq (sq b0))) (op (op b1 (sq b0)) (sq (sq (sq b0)))))) :
    Join (sq a0) (sq (sq b1)) := by
  cases heq

theorem cp_5_111_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (op (sq (sq (sq b0))) (op (op b1 (sq b0)) (sq (sq (sq b0)))))) :
    Join (sq a0) (sq (sq (sq b1))) := by
  cases heq

theorem cp_5_root_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (sq (sq (sq a0)))) = (op (op b0 (sq b1)) (op b0 (op b0 (sq b1))))) :
    Join (sq a0) (sq (sq (sq b1))) := by
  cases heq

theorem cp_5_1_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (sq (sq a0))) = (op (op b0 (sq b1)) (op b0 (op b0 (sq b1))))) :
    Join (sq a0) (sq (sq (sq (sq b1)))) := by
  cases heq

theorem cp_5_11_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (sq a0)) = (op (op b0 (sq b1)) (op b0 (op b0 (sq b1))))) :
    Join (sq a0) (sq (sq (sq (sq (sq b1))))) := by
  cases heq

theorem cp_5_111_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (op (op b0 (sq b1)) (op b0 (op b0 (sq b1))))) :
    Join (sq a0) (sq (sq (sq (sq (sq (sq b1)))))) := by
  cases heq

theorem cp_5_root_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (sq (sq (sq a0)))) = (sq (op (sq b0) (sq b1)))) :
    Join (sq a0) (sq (sq (sq b1))) := by
  have he1 := T.sq.inj heq
  clear heq
  cases he1

theorem cp_5_1_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (sq (sq a0))) = (sq (op (sq b0) (sq b1)))) :
    Join (sq a0) (sq (sq (sq (sq b1)))) := by
  have he1 := T.sq.inj heq
  clear heq
  cases he1

theorem cp_5_11_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (sq a0)) = (sq (op (sq b0) (sq b1)))) :
    Join (sq a0) (sq (sq (sq (sq (sq b1))))) := by
  have he1 := T.sq.inj heq
  clear heq
  cases he1

theorem cp_5_111_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (sq (op (sq b0) (sq b1)))) :
    Join (sq a0) (sq (sq (sq (sq (sq (sq b1)))))) := by
  have he1 := T.sq.inj heq
  clear heq
  subst a0
  exact ⟨(sq (sq (sq b1))), ((Relation.ReflTransGen.refl).tail (root_step .r8 b0 b1 (leaf 0))), ((Relation.ReflTransGen.refl).tail (root_step .r5 (sq (sq b1)) (leaf 0) (leaf 0)))⟩

theorem cp_5_root_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (sq (sq (sq a0)))) = (op (sq b0) (op (sq b1) (sq b0)))) :
    Join (sq a0) (op (sq b0) (sq (sq b1))) := by
  cases heq

theorem cp_5_1_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (sq (sq a0))) = (op (sq b0) (op (sq b1) (sq b0)))) :
    Join (sq a0) (sq (op (sq b0) (sq (sq b1)))) := by
  cases heq

theorem cp_5_11_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (sq a0)) = (op (sq b0) (op (sq b1) (sq b0)))) :
    Join (sq a0) (sq (sq (op (sq b0) (sq (sq b1))))) := by
  cases heq

theorem cp_5_111_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (op (sq b0) (op (sq b1) (sq b0)))) :
    Join (sq a0) (sq (sq (sq (op (sq b0) (sq (sq b1)))))) := by
  cases heq

theorem cp_6_root_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (sq (sq (sq a0))) (op (op a1 (sq a0)) (sq (sq (sq a0))))) = (op b0 b0)) :
    Join a1 (sq b0) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  revert he1
  subst b0
  intro he1
  cases he1

theorem cp_6_1_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (sq (sq a0))) = (op b0 b0)) :
    Join a1 (op (sq b0) (op (op a1 (sq a0)) (sq (sq (sq a0))))) := by
  cases heq

theorem cp_6_11_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (sq a0)) = (op b0 b0)) :
    Join a1 (op (sq (sq b0)) (op (op a1 (sq a0)) (sq (sq (sq a0))))) := by
  cases heq

theorem cp_6_111_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (op b0 b0)) :
    Join a1 (op (sq (sq (sq b0))) (op (op a1 (sq a0)) (sq (sq (sq a0))))) := by
  cases heq

theorem cp_6_2_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (op a1 (sq a0)) (sq (sq (sq a0)))) = (op b0 b0)) :
    Join a1 (op (sq (sq (sq a0))) (sq b0)) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  revert he1
  subst b0
  intro he1
  cases he1

theorem cp_6_21_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a1 (sq a0)) = (op b0 b0)) :
    Join a1 (op (sq (sq (sq a0))) (op (sq b0) (sq (sq (sq a0))))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  revert he1
  subst b0
  intro he1
  subst a1
  exact ⟨(sq a0), (Relation.ReflTransGen.refl), ((((Relation.ReflTransGen.refl).tail (root_step .r9 (sq (sq a0)) (sq a0) (leaf 0))).tail (root_step .r0 (sq (sq (sq a0))) (leaf 0) (leaf 0))).tail (root_step .r5 a0 (leaf 0) (leaf 0)))⟩

theorem cp_6_212_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (op b0 b0)) :
    Join a1 (op (sq (sq (sq a0))) (op (op a1 (sq b0)) (sq (sq (sq a0))))) := by
  cases heq

theorem cp_6_22_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (sq (sq a0))) = (op b0 b0)) :
    Join a1 (op (sq (sq (sq a0))) (op (op a1 (sq a0)) (sq b0))) := by
  cases heq

theorem cp_6_221_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (sq a0)) = (op b0 b0)) :
    Join a1 (op (sq (sq (sq a0))) (op (op a1 (sq a0)) (sq (sq b0)))) := by
  cases heq

theorem cp_6_2211_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (op b0 b0)) :
    Join a1 (op (sq (sq (sq a0))) (op (op a1 (sq a0)) (sq (sq (sq b0))))) := by
  cases heq

theorem cp_6_root_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (sq (sq (sq a0))) (op (op a1 (sq a0)) (sq (sq (sq a0))))) = (op b0 (op (op b1 (op b0 (sq b2))) b0))) :
    Join a1 b1 := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  revert he1 he3
  subst b0
  intro he1 he3
  rcases T.op.inj he3 with ⟨he5, he6⟩
  clear he3
  cases he6

theorem cp_6_1_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (sq (sq a0))) = (op b0 (op (op b1 (op b0 (sq b2))) b0))) :
    Join a1 (op b1 (op (op a1 (sq a0)) (sq (sq (sq a0))))) := by
  cases heq

theorem cp_6_11_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (sq a0)) = (op b0 (op (op b1 (op b0 (sq b2))) b0))) :
    Join a1 (op (sq b1) (op (op a1 (sq a0)) (sq (sq (sq a0))))) := by
  cases heq

theorem cp_6_111_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (op b0 (op (op b1 (op b0 (sq b2))) b0))) :
    Join a1 (op (sq (sq b1)) (op (op a1 (sq a0)) (sq (sq (sq a0))))) := by
  cases heq

theorem cp_6_2_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (op a1 (sq a0)) (sq (sq (sq a0)))) = (op b0 (op (op b1 (op b0 (sq b2))) b0))) :
    Join a1 (op (sq (sq (sq a0))) b1) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_6_21_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a1 (sq a0)) = (op b0 (op (op b1 (op b0 (sq b2))) b0))) :
    Join a1 (op (sq (sq (sq a0))) (op b1 (sq (sq (sq a0))))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_6_212_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (op b0 (op (op b1 (op b0 (sq b2))) b0))) :
    Join a1 (op (sq (sq (sq a0))) (op (op a1 b1) (sq (sq (sq a0))))) := by
  cases heq

theorem cp_6_22_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (sq (sq a0))) = (op b0 (op (op b1 (op b0 (sq b2))) b0))) :
    Join a1 (op (sq (sq (sq a0))) (op (op a1 (sq a0)) b1)) := by
  cases heq

theorem cp_6_221_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (sq a0)) = (op b0 (op (op b1 (op b0 (sq b2))) b0))) :
    Join a1 (op (sq (sq (sq a0))) (op (op a1 (sq a0)) (sq b1))) := by
  cases heq

theorem cp_6_2211_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (op b0 (op (op b1 (op b0 (sq b2))) b0))) :
    Join a1 (op (sq (sq (sq a0))) (op (op a1 (sq a0)) (sq (sq b1)))) := by
  cases heq

theorem cp_6_root_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (sq (sq (sq a0))) (op (op a1 (sq a0)) (sq (sq (sq a0))))) = (op b0 (op (sq (op b0 (sq b1))) b0))) :
    Join a1 (op b0 (sq b1)) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  revert he1 he3
  subst b0
  intro he1 he3
  cases he3

theorem cp_6_1_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (sq (sq a0))) = (op b0 (op (sq (op b0 (sq b1))) b0))) :
    Join a1 (op (op b0 (sq b1)) (op (op a1 (sq a0)) (sq (sq (sq a0))))) := by
  cases heq

theorem cp_6_11_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (sq a0)) = (op b0 (op (sq (op b0 (sq b1))) b0))) :
    Join a1 (op (sq (op b0 (sq b1))) (op (op a1 (sq a0)) (sq (sq (sq a0))))) := by
  cases heq

theorem cp_6_111_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (op b0 (op (sq (op b0 (sq b1))) b0))) :
    Join a1 (op (sq (sq (op b0 (sq b1)))) (op (op a1 (sq a0)) (sq (sq (sq a0))))) := by
  cases heq

theorem cp_6_2_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (op a1 (sq a0)) (sq (sq (sq a0)))) = (op b0 (op (sq (op b0 (sq b1))) b0))) :
    Join a1 (op (sq (sq (sq a0))) (op b0 (sq b1))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_6_21_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a1 (sq a0)) = (op b0 (op (sq (op b0 (sq b1))) b0))) :
    Join a1 (op (sq (sq (sq a0))) (op (op b0 (sq b1)) (sq (sq (sq a0))))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_6_212_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (op b0 (op (sq (op b0 (sq b1))) b0))) :
    Join a1 (op (sq (sq (sq a0))) (op (op a1 (op b0 (sq b1))) (sq (sq (sq a0))))) := by
  cases heq

theorem cp_6_22_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (sq (sq a0))) = (op b0 (op (sq (op b0 (sq b1))) b0))) :
    Join a1 (op (sq (sq (sq a0))) (op (op a1 (sq a0)) (op b0 (sq b1)))) := by
  cases heq

theorem cp_6_221_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (sq a0)) = (op b0 (op (sq (op b0 (sq b1))) b0))) :
    Join a1 (op (sq (sq (sq a0))) (op (op a1 (sq a0)) (sq (op b0 (sq b1))))) := by
  cases heq

theorem cp_6_2211_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (op b0 (op (sq (op b0 (sq b1))) b0))) :
    Join a1 (op (sq (sq (sq a0))) (op (op a1 (sq a0)) (sq (sq (op b0 (sq b1)))))) := by
  cases heq

theorem cp_6_root_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (sq (sq (sq a0))) (op (op a1 (sq a0)) (sq (sq (sq a0))))) = (op (sq b0) (op (op b1 (sq (sq b0))) (sq b0)))) :
    Join a1 b1 := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  have he5 := T.sq.inj he4
  clear he4
  revert he1 he3
  subst b0
  intro he1 he3
  rcases T.op.inj he3 with ⟨he6, he7⟩
  clear he3
  have he8 := T.sq.inj he7
  clear he7
  have hsize := congrArg sz he8
  have hp_a0 := sz_pos a0
  simp only [sz] at hsize
  omega

theorem cp_6_1_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (sq (sq a0))) = (op (sq b0) (op (op b1 (sq (sq b0))) (sq b0)))) :
    Join a1 (op b1 (op (op a1 (sq a0)) (sq (sq (sq a0))))) := by
  cases heq

theorem cp_6_11_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (sq a0)) = (op (sq b0) (op (op b1 (sq (sq b0))) (sq b0)))) :
    Join a1 (op (sq b1) (op (op a1 (sq a0)) (sq (sq (sq a0))))) := by
  cases heq

theorem cp_6_111_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (op (sq b0) (op (op b1 (sq (sq b0))) (sq b0)))) :
    Join a1 (op (sq (sq b1)) (op (op a1 (sq a0)) (sq (sq (sq a0))))) := by
  cases heq

theorem cp_6_2_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (op a1 (sq a0)) (sq (sq (sq a0)))) = (op (sq b0) (op (op b1 (sq (sq b0))) (sq b0)))) :
    Join a1 (op (sq (sq (sq a0))) b1) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_6_21_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a1 (sq a0)) = (op (sq b0) (op (op b1 (sq (sq b0))) (sq b0)))) :
    Join a1 (op (sq (sq (sq a0))) (op b1 (sq (sq (sq a0))))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_6_212_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (op (sq b0) (op (op b1 (sq (sq b0))) (sq b0)))) :
    Join a1 (op (sq (sq (sq a0))) (op (op a1 b1) (sq (sq (sq a0))))) := by
  cases heq

theorem cp_6_22_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (sq (sq a0))) = (op (sq b0) (op (op b1 (sq (sq b0))) (sq b0)))) :
    Join a1 (op (sq (sq (sq a0))) (op (op a1 (sq a0)) b1)) := by
  cases heq

theorem cp_6_221_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (sq a0)) = (op (sq b0) (op (op b1 (sq (sq b0))) (sq b0)))) :
    Join a1 (op (sq (sq (sq a0))) (op (op a1 (sq a0)) (sq b1))) := by
  cases heq

theorem cp_6_2211_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (op (sq b0) (op (op b1 (sq (sq b0))) (sq b0)))) :
    Join a1 (op (sq (sq (sq a0))) (op (op a1 (sq a0)) (sq (sq b1)))) := by
  cases heq

theorem cp_6_root_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (sq (sq (sq a0))) (op (op a1 (sq a0)) (sq (sq (sq a0))))) = (op (op b0 (op (sq b1) (sq b2))) (op b0 (op b0 (op (sq b1) (sq b2)))))) :
    Join a1 (sq b1) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  cases he4

theorem cp_6_1_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (sq (sq a0))) = (op (op b0 (op (sq b1) (sq b2))) (op b0 (op b0 (op (sq b1) (sq b2)))))) :
    Join a1 (op (sq b1) (op (op a1 (sq a0)) (sq (sq (sq a0))))) := by
  cases heq

theorem cp_6_11_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (sq a0)) = (op (op b0 (op (sq b1) (sq b2))) (op b0 (op b0 (op (sq b1) (sq b2)))))) :
    Join a1 (op (sq (sq b1)) (op (op a1 (sq a0)) (sq (sq (sq a0))))) := by
  cases heq

theorem cp_6_111_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (op (op b0 (op (sq b1) (sq b2))) (op b0 (op b0 (op (sq b1) (sq b2)))))) :
    Join a1 (op (sq (sq (sq b1))) (op (op a1 (sq a0)) (sq (sq (sq a0))))) := by
  cases heq

theorem cp_6_2_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (op a1 (sq a0)) (sq (sq (sq a0)))) = (op (op b0 (op (sq b1) (sq b2))) (op b0 (op b0 (op (sq b1) (sq b2)))))) :
    Join a1 (op (sq (sq (sq a0))) (sq b1)) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_6_21_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a1 (sq a0)) = (op (op b0 (op (sq b1) (sq b2))) (op b0 (op b0 (op (sq b1) (sq b2)))))) :
    Join a1 (op (sq (sq (sq a0))) (op (sq b1) (sq (sq (sq a0))))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_6_212_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (op (op b0 (op (sq b1) (sq b2))) (op b0 (op b0 (op (sq b1) (sq b2)))))) :
    Join a1 (op (sq (sq (sq a0))) (op (op a1 (sq b1)) (sq (sq (sq a0))))) := by
  cases heq

theorem cp_6_22_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (sq (sq a0))) = (op (op b0 (op (sq b1) (sq b2))) (op b0 (op b0 (op (sq b1) (sq b2)))))) :
    Join a1 (op (sq (sq (sq a0))) (op (op a1 (sq a0)) (sq b1))) := by
  cases heq

theorem cp_6_221_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (sq a0)) = (op (op b0 (op (sq b1) (sq b2))) (op b0 (op b0 (op (sq b1) (sq b2)))))) :
    Join a1 (op (sq (sq (sq a0))) (op (op a1 (sq a0)) (sq (sq b1)))) := by
  cases heq

theorem cp_6_2211_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (op (op b0 (op (sq b1) (sq b2))) (op b0 (op b0 (op (sq b1) (sq b2)))))) :
    Join a1 (op (sq (sq (sq a0))) (op (op a1 (sq a0)) (sq (sq (sq b1))))) := by
  cases heq

theorem cp_6_root_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (sq (sq (sq a0))) (op (op a1 (sq a0)) (sq (sq (sq a0))))) = (sq (sq (sq (sq b0))))) :
    Join a1 (sq b0) := by
  cases heq

theorem cp_6_1_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (sq (sq a0))) = (sq (sq (sq (sq b0))))) :
    Join a1 (op (sq b0) (op (op a1 (sq a0)) (sq (sq (sq a0))))) := by
  have he1 := T.sq.inj heq
  clear heq
  have he2 := T.sq.inj he1
  clear he1
  have he3 := T.sq.inj he2
  clear he2
  subst a0
  exact ⟨a1, (Relation.ReflTransGen.refl), (((Relation.ReflTransGen.refl).tail (Step.right (sq b0) (Step.right (op a1 (sq (sq b0))) (root_step .r5 b0 (leaf 0) (leaf 0))))).tail (root_step .r3 b0 a1 (leaf 0)))⟩

theorem cp_6_11_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (sq a0)) = (sq (sq (sq (sq b0))))) :
    Join a1 (op (sq (sq b0)) (op (op a1 (sq a0)) (sq (sq (sq a0))))) := by
  have he1 := T.sq.inj heq
  clear heq
  have he2 := T.sq.inj he1
  clear he1
  subst a0
  exact ⟨a1, (Relation.ReflTransGen.refl), (((Relation.ReflTransGen.refl).tail (Step.right (sq (sq b0)) (Step.right (op a1 (sq (sq (sq b0)))) (root_step .r5 (sq b0) (leaf 0) (leaf 0))))).tail (root_step .r3 (sq b0) a1 (leaf 0)))⟩

theorem cp_6_111_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (sq (sq (sq (sq b0))))) :
    Join a1 (op (sq (sq (sq b0))) (op (op a1 (sq a0)) (sq (sq (sq a0))))) := by
  have he1 := T.sq.inj heq
  clear heq
  subst a0
  exact ⟨a1, (Relation.ReflTransGen.refl), ((((Relation.ReflTransGen.refl).tail (Step.right (sq (sq (sq b0))) (Step.left (sq (sq (sq (sq (sq (sq b0)))))) (Step.right a1 (root_step .r5 b0 (leaf 0) (leaf 0)))))).tail (Step.right (sq (sq (sq b0))) (Step.right (op a1 (sq b0)) (root_step .r5 (sq (sq b0)) (leaf 0) (leaf 0))))).tail (root_step .r6 b0 a1 (leaf 0)))⟩

theorem cp_6_2_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (op a1 (sq a0)) (sq (sq (sq a0)))) = (sq (sq (sq (sq b0))))) :
    Join a1 (op (sq (sq (sq a0))) (sq b0)) := by
  cases heq

theorem cp_6_21_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a1 (sq a0)) = (sq (sq (sq (sq b0))))) :
    Join a1 (op (sq (sq (sq a0))) (op (sq b0) (sq (sq (sq a0))))) := by
  cases heq

theorem cp_6_212_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (sq (sq (sq (sq b0))))) :
    Join a1 (op (sq (sq (sq a0))) (op (op a1 (sq b0)) (sq (sq (sq a0))))) := by
  have he1 := T.sq.inj heq
  clear heq
  subst a0
  exact ⟨a1, (Relation.ReflTransGen.refl), ((((Relation.ReflTransGen.refl).tail (Step.left (op (op a1 (sq b0)) (sq (sq (sq (sq (sq (sq b0))))))) (root_step .r5 (sq (sq b0)) (leaf 0) (leaf 0)))).tail (Step.right (sq (sq (sq b0))) (Step.right (op a1 (sq b0)) (root_step .r5 (sq (sq b0)) (leaf 0) (leaf 0))))).tail (root_step .r6 b0 a1 (leaf 0)))⟩

theorem cp_6_22_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (sq (sq a0))) = (sq (sq (sq (sq b0))))) :
    Join a1 (op (sq (sq (sq a0))) (op (op a1 (sq a0)) (sq b0))) := by
  have he1 := T.sq.inj heq
  clear heq
  have he2 := T.sq.inj he1
  clear he1
  have he3 := T.sq.inj he2
  clear he2
  subst a0
  exact ⟨a1, (Relation.ReflTransGen.refl), (((Relation.ReflTransGen.refl).tail (Step.left (op (op a1 (sq (sq b0))) (sq b0)) (root_step .r5 b0 (leaf 0) (leaf 0)))).tail (root_step .r3 b0 a1 (leaf 0)))⟩

theorem cp_6_221_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (sq a0)) = (sq (sq (sq (sq b0))))) :
    Join a1 (op (sq (sq (sq a0))) (op (op a1 (sq a0)) (sq (sq b0)))) := by
  have he1 := T.sq.inj heq
  clear heq
  have he2 := T.sq.inj he1
  clear he1
  subst a0
  exact ⟨a1, (Relation.ReflTransGen.refl), (((Relation.ReflTransGen.refl).tail (Step.left (op (op a1 (sq (sq (sq b0)))) (sq (sq b0))) (root_step .r5 (sq b0) (leaf 0) (leaf 0)))).tail (root_step .r3 (sq b0) a1 (leaf 0)))⟩

theorem cp_6_2211_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (sq (sq (sq (sq b0))))) :
    Join a1 (op (sq (sq (sq a0))) (op (op a1 (sq a0)) (sq (sq (sq b0))))) := by
  have he1 := T.sq.inj heq
  clear heq
  subst a0
  exact ⟨a1, (Relation.ReflTransGen.refl), (((Relation.ReflTransGen.refl).tail (Step.left (op (op a1 (sq (sq (sq (sq b0))))) (sq (sq (sq b0)))) (root_step .r5 (sq (sq b0)) (leaf 0) (leaf 0)))).tail (root_step .r3 (sq (sq b0)) a1 (leaf 0)))⟩

theorem cp_6_root_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (sq (sq (sq a0))) (op (op a1 (sq a0)) (sq (sq (sq a0))))) = (op (sq (sq (sq b0))) (op (op b1 (sq b0)) (sq (sq (sq b0)))))) :
    Join a1 b1 := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  have he5 := T.sq.inj he4
  clear he4
  have he6 := T.sq.inj he5
  clear he5
  have he7 := T.sq.inj he6
  clear he6
  revert he1 he3
  subst a0
  intro he1 he3
  rcases T.op.inj he3 with ⟨he8, he9⟩
  clear he3
  clear he9
  revert he1
  subst a1
  intro he1
  clear he1
  exact ⟨b1, (Relation.ReflTransGen.refl), (Relation.ReflTransGen.refl)⟩

theorem cp_6_1_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (sq (sq a0))) = (op (sq (sq (sq b0))) (op (op b1 (sq b0)) (sq (sq (sq b0)))))) :
    Join a1 (op b1 (op (op a1 (sq a0)) (sq (sq (sq a0))))) := by
  cases heq

theorem cp_6_11_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (sq a0)) = (op (sq (sq (sq b0))) (op (op b1 (sq b0)) (sq (sq (sq b0)))))) :
    Join a1 (op (sq b1) (op (op a1 (sq a0)) (sq (sq (sq a0))))) := by
  cases heq

theorem cp_6_111_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (op (sq (sq (sq b0))) (op (op b1 (sq b0)) (sq (sq (sq b0)))))) :
    Join a1 (op (sq (sq b1)) (op (op a1 (sq a0)) (sq (sq (sq a0))))) := by
  cases heq

theorem cp_6_2_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (op a1 (sq a0)) (sq (sq (sq a0)))) = (op (sq (sq (sq b0))) (op (op b1 (sq b0)) (sq (sq (sq b0)))))) :
    Join a1 (op (sq (sq (sq a0))) b1) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_6_21_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a1 (sq a0)) = (op (sq (sq (sq b0))) (op (op b1 (sq b0)) (sq (sq (sq b0)))))) :
    Join a1 (op (sq (sq (sq a0))) (op b1 (sq (sq (sq a0))))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_6_212_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (op (sq (sq (sq b0))) (op (op b1 (sq b0)) (sq (sq (sq b0)))))) :
    Join a1 (op (sq (sq (sq a0))) (op (op a1 b1) (sq (sq (sq a0))))) := by
  cases heq

theorem cp_6_22_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (sq (sq a0))) = (op (sq (sq (sq b0))) (op (op b1 (sq b0)) (sq (sq (sq b0)))))) :
    Join a1 (op (sq (sq (sq a0))) (op (op a1 (sq a0)) b1)) := by
  cases heq

theorem cp_6_221_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (sq a0)) = (op (sq (sq (sq b0))) (op (op b1 (sq b0)) (sq (sq (sq b0)))))) :
    Join a1 (op (sq (sq (sq a0))) (op (op a1 (sq a0)) (sq b1))) := by
  cases heq

theorem cp_6_2211_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (op (sq (sq (sq b0))) (op (op b1 (sq b0)) (sq (sq (sq b0)))))) :
    Join a1 (op (sq (sq (sq a0))) (op (op a1 (sq a0)) (sq (sq b1)))) := by
  cases heq

theorem cp_6_root_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (sq (sq (sq a0))) (op (op a1 (sq a0)) (sq (sq (sq a0))))) = (op (op b0 (sq b1)) (op b0 (op b0 (sq b1))))) :
    Join a1 (sq (sq (sq b1))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  cases he4

theorem cp_6_1_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (sq (sq a0))) = (op (op b0 (sq b1)) (op b0 (op b0 (sq b1))))) :
    Join a1 (op (sq (sq (sq b1))) (op (op a1 (sq a0)) (sq (sq (sq a0))))) := by
  cases heq

theorem cp_6_11_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (sq a0)) = (op (op b0 (sq b1)) (op b0 (op b0 (sq b1))))) :
    Join a1 (op (sq (sq (sq (sq b1)))) (op (op a1 (sq a0)) (sq (sq (sq a0))))) := by
  cases heq

theorem cp_6_111_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (op (op b0 (sq b1)) (op b0 (op b0 (sq b1))))) :
    Join a1 (op (sq (sq (sq (sq (sq b1))))) (op (op a1 (sq a0)) (sq (sq (sq a0))))) := by
  cases heq

theorem cp_6_2_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (op a1 (sq a0)) (sq (sq (sq a0)))) = (op (op b0 (sq b1)) (op b0 (op b0 (sq b1))))) :
    Join a1 (op (sq (sq (sq a0))) (sq (sq (sq b1)))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_6_21_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a1 (sq a0)) = (op (op b0 (sq b1)) (op b0 (op b0 (sq b1))))) :
    Join a1 (op (sq (sq (sq a0))) (op (sq (sq (sq b1))) (sq (sq (sq a0))))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_6_212_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (op (op b0 (sq b1)) (op b0 (op b0 (sq b1))))) :
    Join a1 (op (sq (sq (sq a0))) (op (op a1 (sq (sq (sq b1)))) (sq (sq (sq a0))))) := by
  cases heq

theorem cp_6_22_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (sq (sq a0))) = (op (op b0 (sq b1)) (op b0 (op b0 (sq b1))))) :
    Join a1 (op (sq (sq (sq a0))) (op (op a1 (sq a0)) (sq (sq (sq b1))))) := by
  cases heq

theorem cp_6_221_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (sq a0)) = (op (op b0 (sq b1)) (op b0 (op b0 (sq b1))))) :
    Join a1 (op (sq (sq (sq a0))) (op (op a1 (sq a0)) (sq (sq (sq (sq b1)))))) := by
  cases heq

theorem cp_6_2211_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (op (op b0 (sq b1)) (op b0 (op b0 (sq b1))))) :
    Join a1 (op (sq (sq (sq a0))) (op (op a1 (sq a0)) (sq (sq (sq (sq (sq b1))))))) := by
  cases heq

theorem cp_6_root_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (sq (sq (sq a0))) (op (op a1 (sq a0)) (sq (sq (sq a0))))) = (sq (op (sq b0) (sq b1)))) :
    Join a1 (sq (sq (sq b1))) := by
  cases heq

theorem cp_6_1_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (sq (sq a0))) = (sq (op (sq b0) (sq b1)))) :
    Join a1 (op (sq (sq (sq b1))) (op (op a1 (sq a0)) (sq (sq (sq a0))))) := by
  have he1 := T.sq.inj heq
  clear heq
  cases he1

theorem cp_6_11_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (sq a0)) = (sq (op (sq b0) (sq b1)))) :
    Join a1 (op (sq (sq (sq (sq b1)))) (op (op a1 (sq a0)) (sq (sq (sq a0))))) := by
  have he1 := T.sq.inj heq
  clear heq
  cases he1

theorem cp_6_111_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (sq (op (sq b0) (sq b1)))) :
    Join a1 (op (sq (sq (sq (sq (sq b1))))) (op (op a1 (sq a0)) (sq (sq (sq a0))))) := by
  have he1 := T.sq.inj heq
  clear heq
  subst a0
  exact ⟨a1, (Relation.ReflTransGen.refl), ((((((Relation.ReflTransGen.refl).tail (Step.left (op (op a1 (sq (op (sq b0) (sq b1)))) (sq (sq (sq (op (sq b0) (sq b1)))))) (root_step .r5 (sq b1) (leaf 0) (leaf 0)))).tail (Step.right (sq (sq b1)) (Step.left (sq (sq (sq (op (sq b0) (sq b1))))) (Step.right a1 (root_step .r8 b0 b1 (leaf 0)))))).tail (Step.right (sq (sq b1)) (Step.right (op a1 (sq (sq (sq b1)))) (Step.sq (Step.sq (root_step .r8 b0 b1 (leaf 0))))))).tail (Step.right (sq (sq b1)) (Step.right (op a1 (sq (sq (sq b1)))) (root_step .r5 (sq b1) (leaf 0) (leaf 0))))).tail (root_step .r3 (sq b1) a1 (leaf 0)))⟩

theorem cp_6_2_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (op a1 (sq a0)) (sq (sq (sq a0)))) = (sq (op (sq b0) (sq b1)))) :
    Join a1 (op (sq (sq (sq a0))) (sq (sq (sq b1)))) := by
  cases heq

theorem cp_6_21_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a1 (sq a0)) = (sq (op (sq b0) (sq b1)))) :
    Join a1 (op (sq (sq (sq a0))) (op (sq (sq (sq b1))) (sq (sq (sq a0))))) := by
  cases heq

theorem cp_6_212_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (sq (op (sq b0) (sq b1)))) :
    Join a1 (op (sq (sq (sq a0))) (op (op a1 (sq (sq (sq b1)))) (sq (sq (sq a0))))) := by
  have he1 := T.sq.inj heq
  clear heq
  subst a0
  exact ⟨a1, (Relation.ReflTransGen.refl), ((((((Relation.ReflTransGen.refl).tail (Step.left (op (op a1 (sq (sq (sq b1)))) (sq (sq (sq (op (sq b0) (sq b1)))))) (Step.sq (Step.sq (root_step .r8 b0 b1 (leaf 0)))))).tail (Step.left (op (op a1 (sq (sq (sq b1)))) (sq (sq (sq (op (sq b0) (sq b1)))))) (root_step .r5 (sq b1) (leaf 0) (leaf 0)))).tail (Step.right (sq (sq b1)) (Step.right (op a1 (sq (sq (sq b1)))) (Step.sq (Step.sq (root_step .r8 b0 b1 (leaf 0))))))).tail (Step.right (sq (sq b1)) (Step.right (op a1 (sq (sq (sq b1)))) (root_step .r5 (sq b1) (leaf 0) (leaf 0))))).tail (root_step .r3 (sq b1) a1 (leaf 0)))⟩

theorem cp_6_22_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (sq (sq a0))) = (sq (op (sq b0) (sq b1)))) :
    Join a1 (op (sq (sq (sq a0))) (op (op a1 (sq a0)) (sq (sq (sq b1))))) := by
  have he1 := T.sq.inj heq
  clear heq
  cases he1

theorem cp_6_221_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (sq a0)) = (sq (op (sq b0) (sq b1)))) :
    Join a1 (op (sq (sq (sq a0))) (op (op a1 (sq a0)) (sq (sq (sq (sq b1)))))) := by
  have he1 := T.sq.inj heq
  clear heq
  cases he1

theorem cp_6_2211_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (sq (op (sq b0) (sq b1)))) :
    Join a1 (op (sq (sq (sq a0))) (op (op a1 (sq a0)) (sq (sq (sq (sq (sq b1))))))) := by
  have he1 := T.sq.inj heq
  clear heq
  subst a0
  exact ⟨a1, (Relation.ReflTransGen.refl), ((((((Relation.ReflTransGen.refl).tail (Step.left (op (op a1 (sq (op (sq b0) (sq b1)))) (sq (sq (sq (sq (sq b1)))))) (Step.sq (Step.sq (root_step .r8 b0 b1 (leaf 0)))))).tail (Step.left (op (op a1 (sq (op (sq b0) (sq b1)))) (sq (sq (sq (sq (sq b1)))))) (root_step .r5 (sq b1) (leaf 0) (leaf 0)))).tail (Step.right (sq (sq b1)) (Step.left (sq (sq (sq (sq (sq b1))))) (Step.right a1 (root_step .r8 b0 b1 (leaf 0)))))).tail (Step.right (sq (sq b1)) (Step.right (op a1 (sq (sq (sq b1)))) (root_step .r5 (sq b1) (leaf 0) (leaf 0))))).tail (root_step .r3 (sq b1) a1 (leaf 0)))⟩

theorem cp_6_root_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (sq (sq (sq a0))) (op (op a1 (sq a0)) (sq (sq (sq a0))))) = (op (sq b0) (op (sq b1) (sq b0)))) :
    Join a1 (op (sq b0) (sq (sq b1))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  have he5 := T.sq.inj he4
  clear he4
  revert he1 he3
  subst b0
  intro he1 he3
  cases he3

theorem cp_6_1_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (sq (sq a0))) = (op (sq b0) (op (sq b1) (sq b0)))) :
    Join a1 (op (op (sq b0) (sq (sq b1))) (op (op a1 (sq a0)) (sq (sq (sq a0))))) := by
  cases heq

theorem cp_6_11_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (sq a0)) = (op (sq b0) (op (sq b1) (sq b0)))) :
    Join a1 (op (sq (op (sq b0) (sq (sq b1)))) (op (op a1 (sq a0)) (sq (sq (sq a0))))) := by
  cases heq

theorem cp_6_111_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (op (sq b0) (op (sq b1) (sq b0)))) :
    Join a1 (op (sq (sq (op (sq b0) (sq (sq b1))))) (op (op a1 (sq a0)) (sq (sq (sq a0))))) := by
  cases heq

theorem cp_6_2_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (op a1 (sq a0)) (sq (sq (sq a0)))) = (op (sq b0) (op (sq b1) (sq b0)))) :
    Join a1 (op (sq (sq (sq a0))) (op (sq b0) (sq (sq b1)))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_6_21_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a1 (sq a0)) = (op (sq b0) (op (sq b1) (sq b0)))) :
    Join a1 (op (sq (sq (sq a0))) (op (op (sq b0) (sq (sq b1))) (sq (sq (sq a0))))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_6_212_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (op (sq b0) (op (sq b1) (sq b0)))) :
    Join a1 (op (sq (sq (sq a0))) (op (op a1 (op (sq b0) (sq (sq b1)))) (sq (sq (sq a0))))) := by
  cases heq

theorem cp_6_22_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (sq (sq a0))) = (op (sq b0) (op (sq b1) (sq b0)))) :
    Join a1 (op (sq (sq (sq a0))) (op (op a1 (sq a0)) (op (sq b0) (sq (sq b1))))) := by
  cases heq

theorem cp_6_221_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (sq a0)) = (op (sq b0) (op (sq b1) (sq b0)))) :
    Join a1 (op (sq (sq (sq a0))) (op (op a1 (sq a0)) (sq (op (sq b0) (sq (sq b1)))))) := by
  cases heq

theorem cp_6_2211_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (op (sq b0) (op (sq b1) (sq b0)))) :
    Join a1 (op (sq (sq (sq a0))) (op (op a1 (sq a0)) (sq (sq (op (sq b0) (sq (sq b1))))))) := by
  cases heq

theorem cp_7_root_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (op a0 (sq a1)) (op a0 (op a0 (sq a1)))) = (op b0 b0)) :
    Join (sq (sq (sq a1))) (sq b0) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  revert he1
  subst b0
  intro he1
  rcases T.op.inj he1 with ⟨he3, he4⟩
  clear he1
  cases he4

theorem cp_7_1_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (sq a1)) = (op b0 b0)) :
    Join (sq (sq (sq a1))) (op (sq b0) (op a0 (op a0 (sq a1)))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  revert he1
  subst b0
  intro he1
  subst a0
  exact ⟨(sq (sq (sq a1))), (Relation.ReflTransGen.refl), ((((Relation.ReflTransGen.refl).tail (Step.right (sq (sq a1)) (root_step .r9 a1 a1 (leaf 0)))).tail (root_step .r9 (sq a1) a1 (leaf 0))).tail (root_step .r0 (sq (sq a1)) (leaf 0) (leaf 0)))⟩

theorem cp_7_12_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a1) = (op b0 b0)) :
    Join (sq (sq (sq a1))) (op (op a0 (sq b0)) (op a0 (op a0 (sq a1)))) := by
  cases heq

theorem cp_7_2_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (op a0 (sq a1))) = (op b0 b0)) :
    Join (sq (sq (sq a1))) (op (op a0 (sq a1)) (sq b0)) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  revert he1
  subst b0
  intro he1
  have hsize := congrArg sz he1
  have hp_a0 := sz_pos a0
  have hp_a1 := sz_pos a1
  simp only [sz] at hsize
  omega

theorem cp_7_22_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (sq a1)) = (op b0 b0)) :
    Join (sq (sq (sq a1))) (op (op a0 (sq a1)) (op a0 (sq b0))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  revert he1
  subst b0
  intro he1
  subst a0
  exact ⟨(sq (sq (sq a1))), (Relation.ReflTransGen.refl), ((((Relation.ReflTransGen.refl).tail (Step.left (op (sq a1) (sq (sq a1))) (root_step .r0 (sq a1) (leaf 0) (leaf 0)))).tail (root_step .r9 (sq a1) a1 (leaf 0))).tail (root_step .r0 (sq (sq a1)) (leaf 0) (leaf 0)))⟩

theorem cp_7_222_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a1) = (op b0 b0)) :
    Join (sq (sq (sq a1))) (op (op a0 (sq a1)) (op a0 (op a0 (sq b0)))) := by
  cases heq

theorem cp_7_root_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (op a0 (sq a1)) (op a0 (op a0 (sq a1)))) = (op b0 (op (op b1 (op b0 (sq b2))) b0))) :
    Join (sq (sq (sq a1))) b1 := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  revert he1 he3
  subst b0
  intro he1 he3
  have hsize := congrArg sz he3
  have hp_a0 := sz_pos a0
  have hp_a1 := sz_pos a1
  have hp_b1 := sz_pos b1
  have hp_b2 := sz_pos b2
  simp only [sz] at hsize
  omega

theorem cp_7_1_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (sq a1)) = (op b0 (op (op b1 (op b0 (sq b2))) b0))) :
    Join (sq (sq (sq a1))) (op b1 (op a0 (op a0 (sq a1)))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_7_12_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a1) = (op b0 (op (op b1 (op b0 (sq b2))) b0))) :
    Join (sq (sq (sq a1))) (op (op a0 b1) (op a0 (op a0 (sq a1)))) := by
  cases heq

theorem cp_7_2_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (op a0 (sq a1))) = (op b0 (op (op b1 (op b0 (sq b2))) b0))) :
    Join (sq (sq (sq a1))) (op (op a0 (sq a1)) b1) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  revert he1 he3
  subst b0
  intro he1 he3
  revert he1
  subst a0
  intro he1
  cases he1

theorem cp_7_22_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (sq a1)) = (op b0 (op (op b1 (op b0 (sq b2))) b0))) :
    Join (sq (sq (sq a1))) (op (op a0 (sq a1)) (op a0 b1)) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_7_222_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a1) = (op b0 (op (op b1 (op b0 (sq b2))) b0))) :
    Join (sq (sq (sq a1))) (op (op a0 (sq a1)) (op a0 (op a0 b1))) := by
  cases heq

theorem cp_7_root_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (op a0 (sq a1)) (op a0 (op a0 (sq a1)))) = (op b0 (op (sq (op b0 (sq b1))) b0))) :
    Join (sq (sq (sq a1))) (op b0 (sq b1)) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  revert he1 he3
  subst b0
  intro he1 he3
  have hsize := congrArg sz he3
  have hp_a0 := sz_pos a0
  have hp_a1 := sz_pos a1
  have hp_b1 := sz_pos b1
  simp only [sz] at hsize
  omega

theorem cp_7_1_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (sq a1)) = (op b0 (op (sq (op b0 (sq b1))) b0))) :
    Join (sq (sq (sq a1))) (op (op b0 (sq b1)) (op a0 (op a0 (sq a1)))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_7_12_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a1) = (op b0 (op (sq (op b0 (sq b1))) b0))) :
    Join (sq (sq (sq a1))) (op (op a0 (op b0 (sq b1))) (op a0 (op a0 (sq a1)))) := by
  cases heq

theorem cp_7_2_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (op a0 (sq a1))) = (op b0 (op (sq (op b0 (sq b1))) b0))) :
    Join (sq (sq (sq a1))) (op (op a0 (sq a1)) (op b0 (sq b1))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  revert he1 he3
  subst b0
  intro he1 he3
  revert he1
  subst a0
  intro he1
  have he5 := T.sq.inj he1
  clear he1
  have hsize := congrArg sz he5
  have hp_a1 := sz_pos a1
  have hp_b1 := sz_pos b1
  simp only [sz] at hsize
  omega

theorem cp_7_22_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (sq a1)) = (op b0 (op (sq (op b0 (sq b1))) b0))) :
    Join (sq (sq (sq a1))) (op (op a0 (sq a1)) (op a0 (op b0 (sq b1)))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_7_222_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a1) = (op b0 (op (sq (op b0 (sq b1))) b0))) :
    Join (sq (sq (sq a1))) (op (op a0 (sq a1)) (op a0 (op a0 (op b0 (sq b1))))) := by
  cases heq

theorem cp_7_root_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (op a0 (sq a1)) (op a0 (op a0 (sq a1)))) = (op (sq b0) (op (op b1 (sq (sq b0))) (sq b0)))) :
    Join (sq (sq (sq a1))) b1 := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  cases he4

theorem cp_7_1_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (sq a1)) = (op (sq b0) (op (op b1 (sq (sq b0))) (sq b0)))) :
    Join (sq (sq (sq a1))) (op b1 (op a0 (op a0 (sq a1)))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_7_12_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a1) = (op (sq b0) (op (op b1 (sq (sq b0))) (sq b0)))) :
    Join (sq (sq (sq a1))) (op (op a0 b1) (op a0 (op a0 (sq a1)))) := by
  cases heq

theorem cp_7_2_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (op a0 (sq a1))) = (op (sq b0) (op (op b1 (sq (sq b0))) (sq b0)))) :
    Join (sq (sq (sq a1))) (op (op a0 (sq a1)) b1) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  have he5 := T.sq.inj he4
  clear he4
  revert he1 he3
  subst a1
  intro he1 he3
  revert he1
  subst a0
  intro he1
  cases he1

theorem cp_7_22_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (sq a1)) = (op (sq b0) (op (op b1 (sq (sq b0))) (sq b0)))) :
    Join (sq (sq (sq a1))) (op (op a0 (sq a1)) (op a0 b1)) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_7_222_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a1) = (op (sq b0) (op (op b1 (sq (sq b0))) (sq b0)))) :
    Join (sq (sq (sq a1))) (op (op a0 (sq a1)) (op a0 (op a0 b1))) := by
  cases heq

theorem cp_7_root_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (op a0 (sq a1)) (op a0 (op a0 (sq a1)))) = (op (op b0 (op (sq b1) (sq b2))) (op b0 (op b0 (op (sq b1) (sq b2)))))) :
    Join (sq (sq (sq a1))) (sq b1) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  rcases T.op.inj he4 with ⟨he5, he6⟩
  clear he4
  cases he6

theorem cp_7_1_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (sq a1)) = (op (op b0 (op (sq b1) (sq b2))) (op b0 (op b0 (op (sq b1) (sq b2)))))) :
    Join (sq (sq (sq a1))) (op (sq b1) (op a0 (op a0 (sq a1)))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_7_12_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a1) = (op (op b0 (op (sq b1) (sq b2))) (op b0 (op b0 (op (sq b1) (sq b2)))))) :
    Join (sq (sq (sq a1))) (op (op a0 (sq b1)) (op a0 (op a0 (sq a1)))) := by
  cases heq

theorem cp_7_2_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (op a0 (sq a1))) = (op (op b0 (op (sq b1) (sq b2))) (op b0 (op b0 (op (sq b1) (sq b2)))))) :
    Join (sq (sq (sq a1))) (op (op a0 (sq a1)) (sq b1)) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  cases he4

theorem cp_7_22_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (sq a1)) = (op (op b0 (op (sq b1) (sq b2))) (op b0 (op b0 (op (sq b1) (sq b2)))))) :
    Join (sq (sq (sq a1))) (op (op a0 (sq a1)) (op a0 (sq b1))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_7_222_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a1) = (op (op b0 (op (sq b1) (sq b2))) (op b0 (op b0 (op (sq b1) (sq b2)))))) :
    Join (sq (sq (sq a1))) (op (op a0 (sq a1)) (op a0 (op a0 (sq b1)))) := by
  cases heq

theorem cp_7_root_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (op a0 (sq a1)) (op a0 (op a0 (sq a1)))) = (sq (sq (sq (sq b0))))) :
    Join (sq (sq (sq a1))) (sq b0) := by
  cases heq

theorem cp_7_1_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (sq a1)) = (sq (sq (sq (sq b0))))) :
    Join (sq (sq (sq a1))) (op (sq b0) (op a0 (op a0 (sq a1)))) := by
  cases heq

theorem cp_7_12_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a1) = (sq (sq (sq (sq b0))))) :
    Join (sq (sq (sq a1))) (op (op a0 (sq b0)) (op a0 (op a0 (sq a1)))) := by
  have he1 := T.sq.inj heq
  clear heq
  subst a1
  exact ⟨(sq (sq (sq b0))), ((Relation.ReflTransGen.refl).tail (root_step .r5 (sq (sq b0)) (leaf 0) (leaf 0))), (((Relation.ReflTransGen.refl).tail (Step.right (op a0 (sq b0)) (Step.right a0 (Step.right a0 (root_step .r5 b0 (leaf 0) (leaf 0)))))).tail (root_step .r7 a0 b0 (leaf 0)))⟩

theorem cp_7_2_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (op a0 (sq a1))) = (sq (sq (sq (sq b0))))) :
    Join (sq (sq (sq a1))) (op (op a0 (sq a1)) (sq b0)) := by
  cases heq

theorem cp_7_22_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (sq a1)) = (sq (sq (sq (sq b0))))) :
    Join (sq (sq (sq a1))) (op (op a0 (sq a1)) (op a0 (sq b0))) := by
  cases heq

theorem cp_7_222_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a1) = (sq (sq (sq (sq b0))))) :
    Join (sq (sq (sq a1))) (op (op a0 (sq a1)) (op a0 (op a0 (sq b0)))) := by
  have he1 := T.sq.inj heq
  clear heq
  subst a1
  exact ⟨(sq (sq (sq b0))), ((Relation.ReflTransGen.refl).tail (root_step .r5 (sq (sq b0)) (leaf 0) (leaf 0))), (((Relation.ReflTransGen.refl).tail (Step.left (op a0 (op a0 (sq b0))) (Step.right a0 (root_step .r5 b0 (leaf 0) (leaf 0))))).tail (root_step .r7 a0 b0 (leaf 0)))⟩

theorem cp_7_root_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (op a0 (sq a1)) (op a0 (op a0 (sq a1)))) = (op (sq (sq (sq b0))) (op (op b1 (sq b0)) (sq (sq (sq b0)))))) :
    Join (sq (sq (sq a1))) b1 := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  cases he4

theorem cp_7_1_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (sq a1)) = (op (sq (sq (sq b0))) (op (op b1 (sq b0)) (sq (sq (sq b0)))))) :
    Join (sq (sq (sq a1))) (op b1 (op a0 (op a0 (sq a1)))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_7_12_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a1) = (op (sq (sq (sq b0))) (op (op b1 (sq b0)) (sq (sq (sq b0)))))) :
    Join (sq (sq (sq a1))) (op (op a0 b1) (op a0 (op a0 (sq a1)))) := by
  cases heq

theorem cp_7_2_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (op a0 (sq a1))) = (op (sq (sq (sq b0))) (op (op b1 (sq b0)) (sq (sq (sq b0)))))) :
    Join (sq (sq (sq a1))) (op (op a0 (sq a1)) b1) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  have he5 := T.sq.inj he4
  clear he4
  revert he1 he3
  subst a1
  intro he1 he3
  revert he1
  subst a0
  intro he1
  cases he1

theorem cp_7_22_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (sq a1)) = (op (sq (sq (sq b0))) (op (op b1 (sq b0)) (sq (sq (sq b0)))))) :
    Join (sq (sq (sq a1))) (op (op a0 (sq a1)) (op a0 b1)) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_7_222_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a1) = (op (sq (sq (sq b0))) (op (op b1 (sq b0)) (sq (sq (sq b0)))))) :
    Join (sq (sq (sq a1))) (op (op a0 (sq a1)) (op a0 (op a0 b1))) := by
  cases heq

theorem cp_7_root_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (op a0 (sq a1)) (op a0 (op a0 (sq a1)))) = (op (op b0 (sq b1)) (op b0 (op b0 (sq b1))))) :
    Join (sq (sq (sq a1))) (sq (sq (sq b1))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  rcases T.op.inj he4 with ⟨he5, he6⟩
  clear he4
  have he7 := T.sq.inj he6
  clear he6
  revert he1 he3 he5
  subst a1
  intro he1 he3 he5
  revert he1 he3
  subst a0
  intro he1 he3
  clear he3
  clear he1
  exact ⟨(sq (sq (sq b1))), (Relation.ReflTransGen.refl), (Relation.ReflTransGen.refl)⟩

theorem cp_7_1_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (sq a1)) = (op (op b0 (sq b1)) (op b0 (op b0 (sq b1))))) :
    Join (sq (sq (sq a1))) (op (sq (sq (sq b1))) (op a0 (op a0 (sq a1)))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_7_12_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a1) = (op (op b0 (sq b1)) (op b0 (op b0 (sq b1))))) :
    Join (sq (sq (sq a1))) (op (op a0 (sq (sq (sq b1)))) (op a0 (op a0 (sq a1)))) := by
  cases heq

theorem cp_7_2_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (op a0 (sq a1))) = (op (op b0 (sq b1)) (op b0 (op b0 (sq b1))))) :
    Join (sq (sq (sq a1))) (op (op a0 (sq a1)) (sq (sq (sq b1)))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  cases he4

theorem cp_7_22_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (sq a1)) = (op (op b0 (sq b1)) (op b0 (op b0 (sq b1))))) :
    Join (sq (sq (sq a1))) (op (op a0 (sq a1)) (op a0 (sq (sq (sq b1))))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_7_222_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a1) = (op (op b0 (sq b1)) (op b0 (op b0 (sq b1))))) :
    Join (sq (sq (sq a1))) (op (op a0 (sq a1)) (op a0 (op a0 (sq (sq (sq b1)))))) := by
  cases heq

theorem cp_7_root_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (op a0 (sq a1)) (op a0 (op a0 (sq a1)))) = (sq (op (sq b0) (sq b1)))) :
    Join (sq (sq (sq a1))) (sq (sq (sq b1))) := by
  cases heq

theorem cp_7_1_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (sq a1)) = (sq (op (sq b0) (sq b1)))) :
    Join (sq (sq (sq a1))) (op (sq (sq (sq b1))) (op a0 (op a0 (sq a1)))) := by
  cases heq

theorem cp_7_12_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a1) = (sq (op (sq b0) (sq b1)))) :
    Join (sq (sq (sq a1))) (op (op a0 (sq (sq (sq b1)))) (op a0 (op a0 (sq a1)))) := by
  have he1 := T.sq.inj heq
  clear heq
  subst a1
  exact ⟨(sq (sq b1)), (((Relation.ReflTransGen.refl).tail (Step.sq (Step.sq (root_step .r8 b0 b1 (leaf 0))))).tail (root_step .r5 (sq b1) (leaf 0) (leaf 0))), ((((Relation.ReflTransGen.refl).tail (Step.right (op a0 (sq (sq (sq b1)))) (Step.right a0 (Step.right a0 (root_step .r8 b0 b1 (leaf 0)))))).tail (root_step .r7 a0 (sq (sq b1)) (leaf 0))).tail (root_step .r5 (sq b1) (leaf 0) (leaf 0)))⟩

theorem cp_7_2_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (op a0 (sq a1))) = (sq (op (sq b0) (sq b1)))) :
    Join (sq (sq (sq a1))) (op (op a0 (sq a1)) (sq (sq (sq b1)))) := by
  cases heq

theorem cp_7_22_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (sq a1)) = (sq (op (sq b0) (sq b1)))) :
    Join (sq (sq (sq a1))) (op (op a0 (sq a1)) (op a0 (sq (sq (sq b1))))) := by
  cases heq

theorem cp_7_222_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a1) = (sq (op (sq b0) (sq b1)))) :
    Join (sq (sq (sq a1))) (op (op a0 (sq a1)) (op a0 (op a0 (sq (sq (sq b1)))))) := by
  have he1 := T.sq.inj heq
  clear heq
  subst a1
  exact ⟨(sq (sq b1)), (((Relation.ReflTransGen.refl).tail (Step.sq (Step.sq (root_step .r8 b0 b1 (leaf 0))))).tail (root_step .r5 (sq b1) (leaf 0) (leaf 0))), ((((Relation.ReflTransGen.refl).tail (Step.left (op a0 (op a0 (sq (sq (sq b1))))) (Step.right a0 (root_step .r8 b0 b1 (leaf 0))))).tail (root_step .r7 a0 (sq (sq b1)) (leaf 0))).tail (root_step .r5 (sq b1) (leaf 0) (leaf 0)))⟩

theorem cp_7_root_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (op a0 (sq a1)) (op a0 (op a0 (sq a1)))) = (op (sq b0) (op (sq b1) (sq b0)))) :
    Join (sq (sq (sq a1))) (op (sq b0) (sq (sq b1))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  cases he4

theorem cp_7_1_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (sq a1)) = (op (sq b0) (op (sq b1) (sq b0)))) :
    Join (sq (sq (sq a1))) (op (op (sq b0) (sq (sq b1))) (op a0 (op a0 (sq a1)))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_7_12_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a1) = (op (sq b0) (op (sq b1) (sq b0)))) :
    Join (sq (sq (sq a1))) (op (op a0 (op (sq b0) (sq (sq b1)))) (op a0 (op a0 (sq a1)))) := by
  cases heq

theorem cp_7_2_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (op a0 (sq a1))) = (op (sq b0) (op (sq b1) (sq b0)))) :
    Join (sq (sq (sq a1))) (op (op a0 (sq a1)) (op (sq b0) (sq (sq b1)))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  have he5 := T.sq.inj he4
  clear he4
  revert he1 he3
  subst a1
  intro he1 he3
  revert he1
  subst a0
  intro he1
  have he6 := T.sq.inj he1
  clear he1
  subst b1
  exact ⟨(sq (sq (sq b0))), (Relation.ReflTransGen.refl), ((((Relation.ReflTransGen.refl).tail (Step.left (op (sq b0) (sq (sq b0))) (root_step .r0 (sq b0) (leaf 0) (leaf 0)))).tail (root_step .r9 (sq b0) b0 (leaf 0))).tail (root_step .r0 (sq (sq b0)) (leaf 0) (leaf 0)))⟩

theorem cp_7_22_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (sq a1)) = (op (sq b0) (op (sq b1) (sq b0)))) :
    Join (sq (sq (sq a1))) (op (op a0 (sq a1)) (op a0 (op (sq b0) (sq (sq b1))))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_7_222_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a1) = (op (sq b0) (op (sq b1) (sq b0)))) :
    Join (sq (sq (sq a1))) (op (op a0 (sq a1)) (op a0 (op a0 (op (sq b0) (sq (sq b1)))))) := by
  cases heq

theorem cp_8_root_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (op (sq a0) (sq a1))) = (op b0 b0)) :
    Join (sq (sq (sq a1))) (sq b0) := by
  cases heq

theorem cp_8_1_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (sq a0) (sq a1)) = (op b0 b0)) :
    Join (sq (sq (sq a1))) (sq (sq b0)) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  revert he1
  subst b0
  intro he1
  have he3 := T.sq.inj he1
  clear he1
  subst a0
  exact ⟨(sq (sq (sq a1))), (Relation.ReflTransGen.refl), (Relation.ReflTransGen.refl)⟩

theorem cp_8_11_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (op b0 b0)) :
    Join (sq (sq (sq a1))) (sq (op (sq b0) (sq a1))) := by
  cases heq

theorem cp_8_12_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a1) = (op b0 b0)) :
    Join (sq (sq (sq a1))) (sq (op (sq a0) (sq b0))) := by
  cases heq

theorem cp_8_root_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (op (sq a0) (sq a1))) = (op b0 (op (op b1 (op b0 (sq b2))) b0))) :
    Join (sq (sq (sq a1))) b1 := by
  cases heq

theorem cp_8_1_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (sq a0) (sq a1)) = (op b0 (op (op b1 (op b0 (sq b2))) b0))) :
    Join (sq (sq (sq a1))) (sq b1) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_8_11_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (op b0 (op (op b1 (op b0 (sq b2))) b0))) :
    Join (sq (sq (sq a1))) (sq (op b1 (sq a1))) := by
  cases heq

theorem cp_8_12_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a1) = (op b0 (op (op b1 (op b0 (sq b2))) b0))) :
    Join (sq (sq (sq a1))) (sq (op (sq a0) b1)) := by
  cases heq

theorem cp_8_root_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (op (sq a0) (sq a1))) = (op b0 (op (sq (op b0 (sq b1))) b0))) :
    Join (sq (sq (sq a1))) (op b0 (sq b1)) := by
  cases heq

theorem cp_8_1_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (sq a0) (sq a1)) = (op b0 (op (sq (op b0 (sq b1))) b0))) :
    Join (sq (sq (sq a1))) (sq (op b0 (sq b1))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_8_11_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (op b0 (op (sq (op b0 (sq b1))) b0))) :
    Join (sq (sq (sq a1))) (sq (op (op b0 (sq b1)) (sq a1))) := by
  cases heq

theorem cp_8_12_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a1) = (op b0 (op (sq (op b0 (sq b1))) b0))) :
    Join (sq (sq (sq a1))) (sq (op (sq a0) (op b0 (sq b1)))) := by
  cases heq

theorem cp_8_root_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (op (sq a0) (sq a1))) = (op (sq b0) (op (op b1 (sq (sq b0))) (sq b0)))) :
    Join (sq (sq (sq a1))) b1 := by
  cases heq

theorem cp_8_1_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (sq a0) (sq a1)) = (op (sq b0) (op (op b1 (sq (sq b0))) (sq b0)))) :
    Join (sq (sq (sq a1))) (sq b1) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_8_11_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (op (sq b0) (op (op b1 (sq (sq b0))) (sq b0)))) :
    Join (sq (sq (sq a1))) (sq (op b1 (sq a1))) := by
  cases heq

theorem cp_8_12_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a1) = (op (sq b0) (op (op b1 (sq (sq b0))) (sq b0)))) :
    Join (sq (sq (sq a1))) (sq (op (sq a0) b1)) := by
  cases heq

theorem cp_8_root_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (op (sq a0) (sq a1))) = (op (op b0 (op (sq b1) (sq b2))) (op b0 (op b0 (op (sq b1) (sq b2)))))) :
    Join (sq (sq (sq a1))) (sq b1) := by
  cases heq

theorem cp_8_1_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (sq a0) (sq a1)) = (op (op b0 (op (sq b1) (sq b2))) (op b0 (op b0 (op (sq b1) (sq b2)))))) :
    Join (sq (sq (sq a1))) (sq (sq b1)) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_8_11_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (op (op b0 (op (sq b1) (sq b2))) (op b0 (op b0 (op (sq b1) (sq b2)))))) :
    Join (sq (sq (sq a1))) (sq (op (sq b1) (sq a1))) := by
  cases heq

theorem cp_8_12_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a1) = (op (op b0 (op (sq b1) (sq b2))) (op b0 (op b0 (op (sq b1) (sq b2)))))) :
    Join (sq (sq (sq a1))) (sq (op (sq a0) (sq b1))) := by
  cases heq

theorem cp_8_root_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (op (sq a0) (sq a1))) = (sq (sq (sq (sq b0))))) :
    Join (sq (sq (sq a1))) (sq b0) := by
  have he1 := T.sq.inj heq
  clear heq
  cases he1

theorem cp_8_1_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (sq a0) (sq a1)) = (sq (sq (sq (sq b0))))) :
    Join (sq (sq (sq a1))) (sq (sq b0)) := by
  cases heq

theorem cp_8_11_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (sq (sq (sq (sq b0))))) :
    Join (sq (sq (sq a1))) (sq (op (sq b0) (sq a1))) := by
  have he1 := T.sq.inj heq
  clear heq
  subst a0
  exact ⟨(sq (sq (sq a1))), (Relation.ReflTransGen.refl), ((Relation.ReflTransGen.refl).tail (root_step .r8 b0 a1 (leaf 0)))⟩

theorem cp_8_12_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a1) = (sq (sq (sq (sq b0))))) :
    Join (sq (sq (sq a1))) (sq (op (sq a0) (sq b0))) := by
  have he1 := T.sq.inj heq
  clear heq
  subst a1
  exact ⟨(sq (sq (sq b0))), ((Relation.ReflTransGen.refl).tail (root_step .r5 (sq (sq b0)) (leaf 0) (leaf 0))), ((Relation.ReflTransGen.refl).tail (root_step .r8 a0 b0 (leaf 0)))⟩

theorem cp_8_root_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (op (sq a0) (sq a1))) = (op (sq (sq (sq b0))) (op (op b1 (sq b0)) (sq (sq (sq b0)))))) :
    Join (sq (sq (sq a1))) b1 := by
  cases heq

theorem cp_8_1_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (sq a0) (sq a1)) = (op (sq (sq (sq b0))) (op (op b1 (sq b0)) (sq (sq (sq b0)))))) :
    Join (sq (sq (sq a1))) (sq b1) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_8_11_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (op (sq (sq (sq b0))) (op (op b1 (sq b0)) (sq (sq (sq b0)))))) :
    Join (sq (sq (sq a1))) (sq (op b1 (sq a1))) := by
  cases heq

theorem cp_8_12_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a1) = (op (sq (sq (sq b0))) (op (op b1 (sq b0)) (sq (sq (sq b0)))))) :
    Join (sq (sq (sq a1))) (sq (op (sq a0) b1)) := by
  cases heq

theorem cp_8_root_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (op (sq a0) (sq a1))) = (op (op b0 (sq b1)) (op b0 (op b0 (sq b1))))) :
    Join (sq (sq (sq a1))) (sq (sq (sq b1))) := by
  cases heq

theorem cp_8_1_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (sq a0) (sq a1)) = (op (op b0 (sq b1)) (op b0 (op b0 (sq b1))))) :
    Join (sq (sq (sq a1))) (sq (sq (sq (sq b1)))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_8_11_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (op (op b0 (sq b1)) (op b0 (op b0 (sq b1))))) :
    Join (sq (sq (sq a1))) (sq (op (sq (sq (sq b1))) (sq a1))) := by
  cases heq

theorem cp_8_12_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a1) = (op (op b0 (sq b1)) (op b0 (op b0 (sq b1))))) :
    Join (sq (sq (sq a1))) (sq (op (sq a0) (sq (sq (sq b1))))) := by
  cases heq

theorem cp_8_root_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (op (sq a0) (sq a1))) = (sq (op (sq b0) (sq b1)))) :
    Join (sq (sq (sq a1))) (sq (sq (sq b1))) := by
  have he1 := T.sq.inj heq
  clear heq
  rcases T.op.inj he1 with ⟨he2, he3⟩
  clear he1
  have he4 := T.sq.inj he3
  clear he3
  revert he2
  subst a1
  intro he2
  have he5 := T.sq.inj he2
  clear he2
  subst a0
  exact ⟨(sq (sq (sq b1))), (Relation.ReflTransGen.refl), (Relation.ReflTransGen.refl)⟩

theorem cp_8_1_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (sq a0) (sq a1)) = (sq (op (sq b0) (sq b1)))) :
    Join (sq (sq (sq a1))) (sq (sq (sq (sq b1)))) := by
  cases heq

theorem cp_8_11_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (sq (op (sq b0) (sq b1)))) :
    Join (sq (sq (sq a1))) (sq (op (sq (sq (sq b1))) (sq a1))) := by
  have he1 := T.sq.inj heq
  clear heq
  subst a0
  exact ⟨(sq (sq (sq a1))), (Relation.ReflTransGen.refl), ((Relation.ReflTransGen.refl).tail (root_step .r8 (sq (sq b1)) a1 (leaf 0)))⟩

theorem cp_8_12_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a1) = (sq (op (sq b0) (sq b1)))) :
    Join (sq (sq (sq a1))) (sq (op (sq a0) (sq (sq (sq b1))))) := by
  have he1 := T.sq.inj heq
  clear heq
  subst a1
  exact ⟨(sq (sq b1)), (((Relation.ReflTransGen.refl).tail (Step.sq (Step.sq (root_step .r8 b0 b1 (leaf 0))))).tail (root_step .r5 (sq b1) (leaf 0) (leaf 0))), (((Relation.ReflTransGen.refl).tail (root_step .r8 a0 (sq (sq b1)) (leaf 0))).tail (root_step .r5 (sq b1) (leaf 0) (leaf 0)))⟩

theorem cp_8_root_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq (op (sq a0) (sq a1))) = (op (sq b0) (op (sq b1) (sq b0)))) :
    Join (sq (sq (sq a1))) (op (sq b0) (sq (sq b1))) := by
  cases heq

theorem cp_8_1_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (sq a0) (sq a1)) = (op (sq b0) (op (sq b1) (sq b0)))) :
    Join (sq (sq (sq a1))) (sq (op (sq b0) (sq (sq b1)))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_8_11_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (op (sq b0) (op (sq b1) (sq b0)))) :
    Join (sq (sq (sq a1))) (sq (op (op (sq b0) (sq (sq b1))) (sq a1))) := by
  cases heq

theorem cp_8_12_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a1) = (op (sq b0) (op (sq b1) (sq b0)))) :
    Join (sq (sq (sq a1))) (sq (op (sq a0) (op (sq b0) (sq (sq b1))))) := by
  cases heq

theorem cp_9_root_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (sq a0) (op (sq a1) (sq a0))) = (op b0 b0)) :
    Join (op (sq a0) (sq (sq a1))) (sq b0) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  revert he1
  subst b0
  intro he1
  cases he1

theorem cp_9_1_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (op b0 b0)) :
    Join (op (sq a0) (sq (sq a1))) (op (sq b0) (op (sq a1) (sq a0))) := by
  cases heq

theorem cp_9_2_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (sq a1) (sq a0)) = (op b0 b0)) :
    Join (op (sq a0) (sq (sq a1))) (op (sq a0) (sq b0)) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  revert he1
  subst b0
  intro he1
  have he3 := T.sq.inj he1
  clear he1
  subst a1
  exact ⟨(op (sq a0) (sq (sq a0))), (Relation.ReflTransGen.refl), (Relation.ReflTransGen.refl)⟩

theorem cp_9_21_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a1) = (op b0 b0)) :
    Join (op (sq a0) (sq (sq a1))) (op (sq a0) (op (sq b0) (sq a0))) := by
  cases heq

theorem cp_9_22_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (op b0 b0)) :
    Join (op (sq a0) (sq (sq a1))) (op (sq a0) (op (sq a1) (sq b0))) := by
  cases heq

theorem cp_9_root_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (sq a0) (op (sq a1) (sq a0))) = (op b0 (op (op b1 (op b0 (sq b2))) b0))) :
    Join (op (sq a0) (sq (sq a1))) b1 := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  revert he1 he3
  subst b0
  intro he1 he3
  cases he3

theorem cp_9_1_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (op b0 (op (op b1 (op b0 (sq b2))) b0))) :
    Join (op (sq a0) (sq (sq a1))) (op b1 (op (sq a1) (sq a0))) := by
  cases heq

theorem cp_9_2_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (sq a1) (sq a0)) = (op b0 (op (op b1 (op b0 (sq b2))) b0))) :
    Join (op (sq a0) (sq (sq a1))) (op (sq a0) b1) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_9_21_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a1) = (op b0 (op (op b1 (op b0 (sq b2))) b0))) :
    Join (op (sq a0) (sq (sq a1))) (op (sq a0) (op b1 (sq a0))) := by
  cases heq

theorem cp_9_22_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (op b0 (op (op b1 (op b0 (sq b2))) b0))) :
    Join (op (sq a0) (sq (sq a1))) (op (sq a0) (op (sq a1) b1)) := by
  cases heq

theorem cp_9_root_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (sq a0) (op (sq a1) (sq a0))) = (op b0 (op (sq (op b0 (sq b1))) b0))) :
    Join (op (sq a0) (sq (sq a1))) (op b0 (sq b1)) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  revert he1 he3
  subst b0
  intro he1 he3
  have he5 := T.sq.inj he3
  clear he3
  revert he1
  subst a1
  intro he1
  clear he1
  exact ⟨(op (sq a0) (sq b1)), (((Relation.ReflTransGen.refl).tail (Step.right (sq a0) (Step.sq (root_step .r8 a0 b1 (leaf 0))))).tail (Step.right (sq a0) (root_step .r5 b1 (leaf 0) (leaf 0)))), (Relation.ReflTransGen.refl)⟩

theorem cp_9_1_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (op b0 (op (sq (op b0 (sq b1))) b0))) :
    Join (op (sq a0) (sq (sq a1))) (op (op b0 (sq b1)) (op (sq a1) (sq a0))) := by
  cases heq

theorem cp_9_2_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (sq a1) (sq a0)) = (op b0 (op (sq (op b0 (sq b1))) b0))) :
    Join (op (sq a0) (sq (sq a1))) (op (sq a0) (op b0 (sq b1))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_9_21_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a1) = (op b0 (op (sq (op b0 (sq b1))) b0))) :
    Join (op (sq a0) (sq (sq a1))) (op (sq a0) (op (op b0 (sq b1)) (sq a0))) := by
  cases heq

theorem cp_9_22_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (op b0 (op (sq (op b0 (sq b1))) b0))) :
    Join (op (sq a0) (sq (sq a1))) (op (sq a0) (op (sq a1) (op b0 (sq b1)))) := by
  cases heq

theorem cp_9_root_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (sq a0) (op (sq a1) (sq a0))) = (op (sq b0) (op (op b1 (sq (sq b0))) (sq b0)))) :
    Join (op (sq a0) (sq (sq a1))) b1 := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  have he5 := T.sq.inj he4
  clear he4
  revert he1 he3
  subst a0
  intro he1 he3
  cases he3

theorem cp_9_1_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (op (sq b0) (op (op b1 (sq (sq b0))) (sq b0)))) :
    Join (op (sq a0) (sq (sq a1))) (op b1 (op (sq a1) (sq a0))) := by
  cases heq

theorem cp_9_2_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (sq a1) (sq a0)) = (op (sq b0) (op (op b1 (sq (sq b0))) (sq b0)))) :
    Join (op (sq a0) (sq (sq a1))) (op (sq a0) b1) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_9_21_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a1) = (op (sq b0) (op (op b1 (sq (sq b0))) (sq b0)))) :
    Join (op (sq a0) (sq (sq a1))) (op (sq a0) (op b1 (sq a0))) := by
  cases heq

theorem cp_9_22_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (op (sq b0) (op (op b1 (sq (sq b0))) (sq b0)))) :
    Join (op (sq a0) (sq (sq a1))) (op (sq a0) (op (sq a1) b1)) := by
  cases heq

theorem cp_9_root_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (sq a0) (op (sq a1) (sq a0))) = (op (op b0 (op (sq b1) (sq b2))) (op b0 (op b0 (op (sq b1) (sq b2)))))) :
    Join (op (sq a0) (sq (sq a1))) (sq b1) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  cases he4

theorem cp_9_1_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (op (op b0 (op (sq b1) (sq b2))) (op b0 (op b0 (op (sq b1) (sq b2)))))) :
    Join (op (sq a0) (sq (sq a1))) (op (sq b1) (op (sq a1) (sq a0))) := by
  cases heq

theorem cp_9_2_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (sq a1) (sq a0)) = (op (op b0 (op (sq b1) (sq b2))) (op b0 (op b0 (op (sq b1) (sq b2)))))) :
    Join (op (sq a0) (sq (sq a1))) (op (sq a0) (sq b1)) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_9_21_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a1) = (op (op b0 (op (sq b1) (sq b2))) (op b0 (op b0 (op (sq b1) (sq b2)))))) :
    Join (op (sq a0) (sq (sq a1))) (op (sq a0) (op (sq b1) (sq a0))) := by
  cases heq

theorem cp_9_22_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (op (op b0 (op (sq b1) (sq b2))) (op b0 (op b0 (op (sq b1) (sq b2)))))) :
    Join (op (sq a0) (sq (sq a1))) (op (sq a0) (op (sq a1) (sq b1))) := by
  cases heq

theorem cp_9_root_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (sq a0) (op (sq a1) (sq a0))) = (sq (sq (sq (sq b0))))) :
    Join (op (sq a0) (sq (sq a1))) (sq b0) := by
  cases heq

theorem cp_9_1_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (sq (sq (sq (sq b0))))) :
    Join (op (sq a0) (sq (sq a1))) (op (sq b0) (op (sq a1) (sq a0))) := by
  have he1 := T.sq.inj heq
  clear heq
  subst a0
  exact ⟨(op (sq b0) (sq (sq a1))), ((Relation.ReflTransGen.refl).tail (Step.left (sq (sq a1)) (root_step .r5 b0 (leaf 0) (leaf 0)))), (((Relation.ReflTransGen.refl).tail (Step.right (sq b0) (Step.right (sq a1) (root_step .r5 b0 (leaf 0) (leaf 0))))).tail (root_step .r9 b0 a1 (leaf 0)))⟩

theorem cp_9_2_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (sq a1) (sq a0)) = (sq (sq (sq (sq b0))))) :
    Join (op (sq a0) (sq (sq a1))) (op (sq a0) (sq b0)) := by
  cases heq

theorem cp_9_21_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a1) = (sq (sq (sq (sq b0))))) :
    Join (op (sq a0) (sq (sq a1))) (op (sq a0) (op (sq b0) (sq a0))) := by
  have he1 := T.sq.inj heq
  clear heq
  subst a1
  exact ⟨(op (sq a0) (sq (sq b0))), ((Relation.ReflTransGen.refl).tail (Step.right (sq a0) (root_step .r5 (sq b0) (leaf 0) (leaf 0)))), ((Relation.ReflTransGen.refl).tail (root_step .r9 a0 b0 (leaf 0)))⟩

theorem cp_9_22_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (sq (sq (sq (sq b0))))) :
    Join (op (sq a0) (sq (sq a1))) (op (sq a0) (op (sq a1) (sq b0))) := by
  have he1 := T.sq.inj heq
  clear heq
  subst a0
  exact ⟨(op (sq b0) (sq (sq a1))), ((Relation.ReflTransGen.refl).tail (Step.left (sq (sq a1)) (root_step .r5 b0 (leaf 0) (leaf 0)))), (((Relation.ReflTransGen.refl).tail (Step.left (op (sq a1) (sq b0)) (root_step .r5 b0 (leaf 0) (leaf 0)))).tail (root_step .r9 b0 a1 (leaf 0)))⟩

theorem cp_9_root_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (sq a0) (op (sq a1) (sq a0))) = (op (sq (sq (sq b0))) (op (op b1 (sq b0)) (sq (sq (sq b0)))))) :
    Join (op (sq a0) (sq (sq a1))) b1 := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  have he5 := T.sq.inj he4
  clear he4
  revert he1 he3
  subst a0
  intro he1 he3
  cases he3

theorem cp_9_1_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (op (sq (sq (sq b0))) (op (op b1 (sq b0)) (sq (sq (sq b0)))))) :
    Join (op (sq a0) (sq (sq a1))) (op b1 (op (sq a1) (sq a0))) := by
  cases heq

theorem cp_9_2_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (sq a1) (sq a0)) = (op (sq (sq (sq b0))) (op (op b1 (sq b0)) (sq (sq (sq b0)))))) :
    Join (op (sq a0) (sq (sq a1))) (op (sq a0) b1) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_9_21_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a1) = (op (sq (sq (sq b0))) (op (op b1 (sq b0)) (sq (sq (sq b0)))))) :
    Join (op (sq a0) (sq (sq a1))) (op (sq a0) (op b1 (sq a0))) := by
  cases heq

theorem cp_9_22_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (op (sq (sq (sq b0))) (op (op b1 (sq b0)) (sq (sq (sq b0)))))) :
    Join (op (sq a0) (sq (sq a1))) (op (sq a0) (op (sq a1) b1)) := by
  cases heq

theorem cp_9_root_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (sq a0) (op (sq a1) (sq a0))) = (op (op b0 (sq b1)) (op b0 (op b0 (sq b1))))) :
    Join (op (sq a0) (sq (sq a1))) (sq (sq (sq b1))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  cases he4

theorem cp_9_1_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (op (op b0 (sq b1)) (op b0 (op b0 (sq b1))))) :
    Join (op (sq a0) (sq (sq a1))) (op (sq (sq (sq b1))) (op (sq a1) (sq a0))) := by
  cases heq

theorem cp_9_2_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (sq a1) (sq a0)) = (op (op b0 (sq b1)) (op b0 (op b0 (sq b1))))) :
    Join (op (sq a0) (sq (sq a1))) (op (sq a0) (sq (sq (sq b1)))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_9_21_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a1) = (op (op b0 (sq b1)) (op b0 (op b0 (sq b1))))) :
    Join (op (sq a0) (sq (sq a1))) (op (sq a0) (op (sq (sq (sq b1))) (sq a0))) := by
  cases heq

theorem cp_9_22_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (op (op b0 (sq b1)) (op b0 (op b0 (sq b1))))) :
    Join (op (sq a0) (sq (sq a1))) (op (sq a0) (op (sq a1) (sq (sq (sq b1))))) := by
  cases heq

theorem cp_9_root_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (sq a0) (op (sq a1) (sq a0))) = (sq (op (sq b0) (sq b1)))) :
    Join (op (sq a0) (sq (sq a1))) (sq (sq (sq b1))) := by
  cases heq

theorem cp_9_1_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (sq (op (sq b0) (sq b1)))) :
    Join (op (sq a0) (sq (sq a1))) (op (sq (sq (sq b1))) (op (sq a1) (sq a0))) := by
  have he1 := T.sq.inj heq
  clear heq
  subst a0
  exact ⟨(op (sq (sq (sq b1))) (sq (sq a1))), ((Relation.ReflTransGen.refl).tail (Step.left (sq (sq a1)) (root_step .r8 b0 b1 (leaf 0)))), (((Relation.ReflTransGen.refl).tail (Step.right (sq (sq (sq b1))) (Step.right (sq a1) (root_step .r8 b0 b1 (leaf 0))))).tail (root_step .r9 (sq (sq b1)) a1 (leaf 0)))⟩

theorem cp_9_2_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (sq a1) (sq a0)) = (sq (op (sq b0) (sq b1)))) :
    Join (op (sq a0) (sq (sq a1))) (op (sq a0) (sq (sq (sq b1)))) := by
  cases heq

theorem cp_9_21_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a1) = (sq (op (sq b0) (sq b1)))) :
    Join (op (sq a0) (sq (sq a1))) (op (sq a0) (op (sq (sq (sq b1))) (sq a0))) := by
  have he1 := T.sq.inj heq
  clear heq
  subst a1
  exact ⟨(op (sq a0) (sq b1)), (((Relation.ReflTransGen.refl).tail (Step.right (sq a0) (Step.sq (root_step .r8 b0 b1 (leaf 0))))).tail (Step.right (sq a0) (root_step .r5 b1 (leaf 0) (leaf 0)))), (((Relation.ReflTransGen.refl).tail (root_step .r9 a0 (sq (sq b1)) (leaf 0))).tail (Step.right (sq a0) (root_step .r5 b1 (leaf 0) (leaf 0))))⟩

theorem cp_9_22_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (sq (op (sq b0) (sq b1)))) :
    Join (op (sq a0) (sq (sq a1))) (op (sq a0) (op (sq a1) (sq (sq (sq b1))))) := by
  have he1 := T.sq.inj heq
  clear heq
  subst a0
  exact ⟨(op (sq (sq (sq b1))) (sq (sq a1))), ((Relation.ReflTransGen.refl).tail (Step.left (sq (sq a1)) (root_step .r8 b0 b1 (leaf 0)))), (((Relation.ReflTransGen.refl).tail (Step.left (op (sq a1) (sq (sq (sq b1)))) (root_step .r8 b0 b1 (leaf 0)))).tail (root_step .r9 (sq (sq b1)) a1 (leaf 0)))⟩

theorem cp_9_root_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (sq a0) (op (sq a1) (sq a0))) = (op (sq b0) (op (sq b1) (sq b0)))) :
    Join (op (sq a0) (sq (sq a1))) (op (sq b0) (sq (sq b1))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  rcases T.op.inj he2 with ⟨he3, he4⟩
  clear he2
  have he5 := T.sq.inj he4
  clear he4
  revert he1 he3
  subst a0
  intro he1 he3
  have he6 := T.sq.inj he3
  clear he3
  revert he1
  subst a1
  intro he1
  clear he1
  exact ⟨(op (sq b0) (sq (sq b1))), (Relation.ReflTransGen.refl), (Relation.ReflTransGen.refl)⟩

theorem cp_9_1_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (op (sq b0) (op (sq b1) (sq b0)))) :
    Join (op (sq a0) (sq (sq a1))) (op (op (sq b0) (sq (sq b1))) (op (sq a1) (sq a0))) := by
  cases heq

theorem cp_9_2_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (sq a1) (sq a0)) = (op (sq b0) (op (sq b1) (sq b0)))) :
    Join (op (sq a0) (sq (sq a1))) (op (sq a0) (op (sq b0) (sq (sq b1)))) := by
  rcases T.op.inj heq with ⟨he1, he2⟩
  clear heq
  cases he2

theorem cp_9_21_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a1) = (op (sq b0) (op (sq b1) (sq b0)))) :
    Join (op (sq a0) (sq (sq a1))) (op (sq a0) (op (op (sq b0) (sq (sq b1))) (sq a0))) := by
  cases heq

theorem cp_9_22_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (sq a0) = (op (sq b0) (op (sq b1) (sq b0)))) :
    Join (op (sq a0) (sq (sq a1))) (op (sq a0) (op (sq a1) (op (sq b0) (sq (sq b1))))) := by
  cases heq

theorem vp_0_1 (a0 a1 a2 v : T) (hv : Step a0 v) :
    Join (sq a0) (op v a0) := by
  exact ⟨(sq v), ((Relation.ReflTransGen.refl).tail (Step.sq hv)), (((Relation.ReflTransGen.refl).tail (Step.right v hv)).tail (root_step .r0 v a1 a2))⟩

theorem vp_0_2 (a0 a1 a2 v : T) (hv : Step a0 v) :
    Join (sq a0) (op a0 v) := by
  exact ⟨(sq v), ((Relation.ReflTransGen.refl).tail (Step.sq hv)), (((Relation.ReflTransGen.refl).tail (Step.left v hv)).tail (root_step .r0 v a1 a2))⟩

theorem vp_1_1 (a0 a1 a2 v : T) (hv : Step a0 v) :
    Join a1 (op v (op (op a1 (op a0 (sq a2))) a0)) := by
  exact ⟨a1, (Relation.ReflTransGen.refl), ((((Relation.ReflTransGen.refl).tail (Step.right v (Step.left a0 (Step.right a1 (Step.left (sq a2) hv))))).tail (Step.right v (Step.right (op a1 (op v (sq a2))) hv))).tail (root_step .r1 v a1 a2))⟩

theorem vp_1_211 (a0 a1 a2 v : T) (hv : Step a1 v) :
    Join a1 (op a0 (op (op v (op a0 (sq a2))) a0)) := by
  exact ⟨v, ((Relation.ReflTransGen.refl).tail hv), ((Relation.ReflTransGen.refl).tail (root_step .r1 a0 v a2))⟩

theorem vp_1_2121 (a0 a1 a2 v : T) (hv : Step a0 v) :
    Join a1 (op a0 (op (op a1 (op v (sq a2))) a0)) := by
  exact ⟨a1, (Relation.ReflTransGen.refl), ((((Relation.ReflTransGen.refl).tail (Step.left (op (op a1 (op v (sq a2))) a0) hv)).tail (Step.right v (Step.right (op a1 (op v (sq a2))) hv))).tail (root_step .r1 v a1 a2))⟩

theorem vp_1_21221 (a0 a1 a2 v : T) (hv : Step a2 v) :
    Join a1 (op a0 (op (op a1 (op a0 (sq v))) a0)) := by
  exact ⟨a1, (Relation.ReflTransGen.refl), ((Relation.ReflTransGen.refl).tail (root_step .r1 a0 a1 v))⟩

theorem vp_1_22 (a0 a1 a2 v : T) (hv : Step a0 v) :
    Join a1 (op a0 (op (op a1 (op a0 (sq a2))) v)) := by
  exact ⟨a1, (Relation.ReflTransGen.refl), ((((Relation.ReflTransGen.refl).tail (Step.left (op (op a1 (op a0 (sq a2))) v) hv)).tail (Step.right v (Step.left v (Step.right a1 (Step.left (sq a2) hv))))).tail (root_step .r1 v a1 a2))⟩

theorem vp_2_1 (a0 a1 a2 v : T) (hv : Step a0 v) :
    Join (op a0 (sq a1)) (op v (op (sq (op a0 (sq a1))) a0)) := by
  exact ⟨(op v (sq a1)), ((Relation.ReflTransGen.refl).tail (Step.left (sq a1) hv)), ((((Relation.ReflTransGen.refl).tail (Step.right v (Step.left a0 (Step.sq (Step.left (sq a1) hv))))).tail (Step.right v (Step.right (sq (op v (sq a1))) hv))).tail (root_step .r2 v a1 a2))⟩

theorem vp_2_2111 (a0 a1 a2 v : T) (hv : Step a0 v) :
    Join (op a0 (sq a1)) (op a0 (op (sq (op v (sq a1))) a0)) := by
  exact ⟨(op v (sq a1)), ((Relation.ReflTransGen.refl).tail (Step.left (sq a1) hv)), ((((Relation.ReflTransGen.refl).tail (Step.left (op (sq (op v (sq a1))) a0) hv)).tail (Step.right v (Step.right (sq (op v (sq a1))) hv))).tail (root_step .r2 v a1 a2))⟩

theorem vp_2_21121 (a0 a1 a2 v : T) (hv : Step a1 v) :
    Join (op a0 (sq a1)) (op a0 (op (sq (op a0 (sq v))) a0)) := by
  exact ⟨(op a0 (sq v)), ((Relation.ReflTransGen.refl).tail (Step.right a0 (Step.sq hv))), ((Relation.ReflTransGen.refl).tail (root_step .r2 a0 v a2))⟩

theorem vp_2_22 (a0 a1 a2 v : T) (hv : Step a0 v) :
    Join (op a0 (sq a1)) (op a0 (op (sq (op a0 (sq a1))) v)) := by
  exact ⟨(op v (sq a1)), ((Relation.ReflTransGen.refl).tail (Step.left (sq a1) hv)), ((((Relation.ReflTransGen.refl).tail (Step.left (op (sq (op a0 (sq a1))) v) hv)).tail (Step.right v (Step.left v (Step.sq (Step.left (sq a1) hv))))).tail (root_step .r2 v a1 a2))⟩

theorem vp_3_11 (a0 a1 a2 v : T) (hv : Step a0 v) :
    Join a1 (op (sq v) (op (op a1 (sq (sq a0))) (sq a0))) := by
  exact ⟨a1, (Relation.ReflTransGen.refl), ((((Relation.ReflTransGen.refl).tail (Step.right (sq v) (Step.left (sq a0) (Step.right a1 (Step.sq (Step.sq hv)))))).tail (Step.right (sq v) (Step.right (op a1 (sq (sq v))) (Step.sq hv)))).tail (root_step .r3 v a1 a2))⟩

theorem vp_3_211 (a0 a1 a2 v : T) (hv : Step a1 v) :
    Join a1 (op (sq a0) (op (op v (sq (sq a0))) (sq a0))) := by
  exact ⟨v, ((Relation.ReflTransGen.refl).tail hv), ((Relation.ReflTransGen.refl).tail (root_step .r3 a0 v a2))⟩

theorem vp_3_21211 (a0 a1 a2 v : T) (hv : Step a0 v) :
    Join a1 (op (sq a0) (op (op a1 (sq (sq v))) (sq a0))) := by
  exact ⟨a1, (Relation.ReflTransGen.refl), ((((Relation.ReflTransGen.refl).tail (Step.left (op (op a1 (sq (sq v))) (sq a0)) (Step.sq hv))).tail (Step.right (sq v) (Step.right (op a1 (sq (sq v))) (Step.sq hv)))).tail (root_step .r3 v a1 a2))⟩

theorem vp_3_221 (a0 a1 a2 v : T) (hv : Step a0 v) :
    Join a1 (op (sq a0) (op (op a1 (sq (sq a0))) (sq v))) := by
  exact ⟨a1, (Relation.ReflTransGen.refl), ((((Relation.ReflTransGen.refl).tail (Step.left (op (op a1 (sq (sq a0))) (sq v)) (Step.sq hv))).tail (Step.right (sq v) (Step.left (sq v) (Step.right a1 (Step.sq (Step.sq hv)))))).tail (root_step .r3 v a1 a2))⟩

theorem vp_4_11 (a0 a1 a2 v : T) (hv : Step a0 v) :
    Join (sq a1) (op (op v (op (sq a1) (sq a2))) (op a0 (op a0 (op (sq a1) (sq a2))))) := by
  exact ⟨(sq a1), (Relation.ReflTransGen.refl), ((((Relation.ReflTransGen.refl).tail (Step.right (op v (op (sq a1) (sq a2))) (Step.left (op a0 (op (sq a1) (sq a2))) hv))).tail (Step.right (op v (op (sq a1) (sq a2))) (Step.right v (Step.left (op (sq a1) (sq a2)) hv)))).tail (root_step .r4 v a1 a2))⟩

theorem vp_4_1211 (a0 a1 a2 v : T) (hv : Step a1 v) :
    Join (sq a1) (op (op a0 (op (sq v) (sq a2))) (op a0 (op a0 (op (sq a1) (sq a2))))) := by
  exact ⟨(sq v), ((Relation.ReflTransGen.refl).tail (Step.sq hv)), (((Relation.ReflTransGen.refl).tail (Step.right (op a0 (op (sq v) (sq a2))) (Step.right a0 (Step.right a0 (Step.left (sq a2) (Step.sq hv)))))).tail (root_step .r4 a0 v a2))⟩

theorem vp_4_1221 (a0 a1 a2 v : T) (hv : Step a2 v) :
    Join (sq a1) (op (op a0 (op (sq a1) (sq v))) (op a0 (op a0 (op (sq a1) (sq a2))))) := by
  exact ⟨(sq a1), (Relation.ReflTransGen.refl), (((Relation.ReflTransGen.refl).tail (Step.right (op a0 (op (sq a1) (sq v))) (Step.right a0 (Step.right a0 (Step.right (sq a1) (Step.sq hv)))))).tail (root_step .r4 a0 a1 v))⟩

theorem vp_4_21 (a0 a1 a2 v : T) (hv : Step a0 v) :
    Join (sq a1) (op (op a0 (op (sq a1) (sq a2))) (op v (op a0 (op (sq a1) (sq a2))))) := by
  exact ⟨(sq a1), (Relation.ReflTransGen.refl), ((((Relation.ReflTransGen.refl).tail (Step.left (op v (op a0 (op (sq a1) (sq a2)))) (Step.left (op (sq a1) (sq a2)) hv))).tail (Step.right (op v (op (sq a1) (sq a2))) (Step.right v (Step.left (op (sq a1) (sq a2)) hv)))).tail (root_step .r4 v a1 a2))⟩

theorem vp_4_221 (a0 a1 a2 v : T) (hv : Step a0 v) :
    Join (sq a1) (op (op a0 (op (sq a1) (sq a2))) (op a0 (op v (op (sq a1) (sq a2))))) := by
  exact ⟨(sq a1), (Relation.ReflTransGen.refl), ((((Relation.ReflTransGen.refl).tail (Step.left (op a0 (op v (op (sq a1) (sq a2)))) (Step.left (op (sq a1) (sq a2)) hv))).tail (Step.right (op v (op (sq a1) (sq a2))) (Step.left (op v (op (sq a1) (sq a2))) hv))).tail (root_step .r4 v a1 a2))⟩

theorem vp_4_22211 (a0 a1 a2 v : T) (hv : Step a1 v) :
    Join (sq a1) (op (op a0 (op (sq a1) (sq a2))) (op a0 (op a0 (op (sq v) (sq a2))))) := by
  exact ⟨(sq v), ((Relation.ReflTransGen.refl).tail (Step.sq hv)), (((Relation.ReflTransGen.refl).tail (Step.left (op a0 (op a0 (op (sq v) (sq a2)))) (Step.right a0 (Step.left (sq a2) (Step.sq hv))))).tail (root_step .r4 a0 v a2))⟩

theorem vp_4_22221 (a0 a1 a2 v : T) (hv : Step a2 v) :
    Join (sq a1) (op (op a0 (op (sq a1) (sq a2))) (op a0 (op a0 (op (sq a1) (sq v))))) := by
  exact ⟨(sq a1), (Relation.ReflTransGen.refl), (((Relation.ReflTransGen.refl).tail (Step.left (op a0 (op a0 (op (sq a1) (sq v)))) (Step.right a0 (Step.right (sq a1) (Step.sq hv))))).tail (root_step .r4 a0 a1 v))⟩

theorem vp_5_1111 (a0 a1 a2 v : T) (hv : Step a0 v) :
    Join (sq a0) (sq (sq (sq (sq v)))) := by
  exact ⟨(sq v), ((Relation.ReflTransGen.refl).tail (Step.sq hv)), ((Relation.ReflTransGen.refl).tail (root_step .r5 v a1 a2))⟩

theorem vp_6_1111 (a0 a1 a2 v : T) (hv : Step a0 v) :
    Join a1 (op (sq (sq (sq v))) (op (op a1 (sq a0)) (sq (sq (sq a0))))) := by
  exact ⟨a1, (Relation.ReflTransGen.refl), ((((Relation.ReflTransGen.refl).tail (Step.right (sq (sq (sq v))) (Step.left (sq (sq (sq a0))) (Step.right a1 (Step.sq hv))))).tail (Step.right (sq (sq (sq v))) (Step.right (op a1 (sq v)) (Step.sq (Step.sq (Step.sq hv)))))).tail (root_step .r6 v a1 a2))⟩

theorem vp_6_211 (a0 a1 a2 v : T) (hv : Step a1 v) :
    Join a1 (op (sq (sq (sq a0))) (op (op v (sq a0)) (sq (sq (sq a0))))) := by
  exact ⟨v, ((Relation.ReflTransGen.refl).tail hv), ((Relation.ReflTransGen.refl).tail (root_step .r6 a0 v a2))⟩

theorem vp_6_2121 (a0 a1 a2 v : T) (hv : Step a0 v) :
    Join a1 (op (sq (sq (sq a0))) (op (op a1 (sq v)) (sq (sq (sq a0))))) := by
  exact ⟨a1, (Relation.ReflTransGen.refl), ((((Relation.ReflTransGen.refl).tail (Step.left (op (op a1 (sq v)) (sq (sq (sq a0)))) (Step.sq (Step.sq (Step.sq hv))))).tail (Step.right (sq (sq (sq v))) (Step.right (op a1 (sq v)) (Step.sq (Step.sq (Step.sq hv)))))).tail (root_step .r6 v a1 a2))⟩

theorem vp_6_22111 (a0 a1 a2 v : T) (hv : Step a0 v) :
    Join a1 (op (sq (sq (sq a0))) (op (op a1 (sq a0)) (sq (sq (sq v))))) := by
  exact ⟨a1, (Relation.ReflTransGen.refl), ((((Relation.ReflTransGen.refl).tail (Step.left (op (op a1 (sq a0)) (sq (sq (sq v)))) (Step.sq (Step.sq (Step.sq hv))))).tail (Step.right (sq (sq (sq v))) (Step.left (sq (sq (sq v))) (Step.right a1 (Step.sq hv))))).tail (root_step .r6 v a1 a2))⟩

theorem vp_7_11 (a0 a1 a2 v : T) (hv : Step a0 v) :
    Join (sq (sq (sq a1))) (op (op v (sq a1)) (op a0 (op a0 (sq a1)))) := by
  exact ⟨(sq (sq (sq a1))), (Relation.ReflTransGen.refl), ((((Relation.ReflTransGen.refl).tail (Step.right (op v (sq a1)) (Step.left (op a0 (sq a1)) hv))).tail (Step.right (op v (sq a1)) (Step.right v (Step.left (sq a1) hv)))).tail (root_step .r7 v a1 a2))⟩

theorem vp_7_121 (a0 a1 a2 v : T) (hv : Step a1 v) :
    Join (sq (sq (sq a1))) (op (op a0 (sq v)) (op a0 (op a0 (sq a1)))) := by
  exact ⟨(sq (sq (sq v))), ((Relation.ReflTransGen.refl).tail (Step.sq (Step.sq (Step.sq hv)))), (((Relation.ReflTransGen.refl).tail (Step.right (op a0 (sq v)) (Step.right a0 (Step.right a0 (Step.sq hv))))).tail (root_step .r7 a0 v a2))⟩

theorem vp_7_21 (a0 a1 a2 v : T) (hv : Step a0 v) :
    Join (sq (sq (sq a1))) (op (op a0 (sq a1)) (op v (op a0 (sq a1)))) := by
  exact ⟨(sq (sq (sq a1))), (Relation.ReflTransGen.refl), ((((Relation.ReflTransGen.refl).tail (Step.left (op v (op a0 (sq a1))) (Step.left (sq a1) hv))).tail (Step.right (op v (sq a1)) (Step.right v (Step.left (sq a1) hv)))).tail (root_step .r7 v a1 a2))⟩

theorem vp_7_221 (a0 a1 a2 v : T) (hv : Step a0 v) :
    Join (sq (sq (sq a1))) (op (op a0 (sq a1)) (op a0 (op v (sq a1)))) := by
  exact ⟨(sq (sq (sq a1))), (Relation.ReflTransGen.refl), ((((Relation.ReflTransGen.refl).tail (Step.left (op a0 (op v (sq a1))) (Step.left (sq a1) hv))).tail (Step.right (op v (sq a1)) (Step.left (op v (sq a1)) hv))).tail (root_step .r7 v a1 a2))⟩

theorem vp_7_2221 (a0 a1 a2 v : T) (hv : Step a1 v) :
    Join (sq (sq (sq a1))) (op (op a0 (sq a1)) (op a0 (op a0 (sq v)))) := by
  exact ⟨(sq (sq (sq v))), ((Relation.ReflTransGen.refl).tail (Step.sq (Step.sq (Step.sq hv)))), (((Relation.ReflTransGen.refl).tail (Step.left (op a0 (op a0 (sq v))) (Step.right a0 (Step.sq hv)))).tail (root_step .r7 a0 v a2))⟩

theorem vp_8_111 (a0 a1 a2 v : T) (hv : Step a0 v) :
    Join (sq (sq (sq a1))) (sq (op (sq v) (sq a1))) := by
  exact ⟨(sq (sq (sq a1))), (Relation.ReflTransGen.refl), ((Relation.ReflTransGen.refl).tail (root_step .r8 v a1 a2))⟩

theorem vp_8_121 (a0 a1 a2 v : T) (hv : Step a1 v) :
    Join (sq (sq (sq a1))) (sq (op (sq a0) (sq v))) := by
  exact ⟨(sq (sq (sq v))), ((Relation.ReflTransGen.refl).tail (Step.sq (Step.sq (Step.sq hv)))), ((Relation.ReflTransGen.refl).tail (root_step .r8 a0 v a2))⟩

theorem vp_9_11 (a0 a1 a2 v : T) (hv : Step a0 v) :
    Join (op (sq a0) (sq (sq a1))) (op (sq v) (op (sq a1) (sq a0))) := by
  exact ⟨(op (sq v) (sq (sq a1))), ((Relation.ReflTransGen.refl).tail (Step.left (sq (sq a1)) (Step.sq hv))), (((Relation.ReflTransGen.refl).tail (Step.right (sq v) (Step.right (sq a1) (Step.sq hv)))).tail (root_step .r9 v a1 a2))⟩

theorem vp_9_211 (a0 a1 a2 v : T) (hv : Step a1 v) :
    Join (op (sq a0) (sq (sq a1))) (op (sq a0) (op (sq v) (sq a0))) := by
  exact ⟨(op (sq a0) (sq (sq v))), ((Relation.ReflTransGen.refl).tail (Step.right (sq a0) (Step.sq (Step.sq hv)))), ((Relation.ReflTransGen.refl).tail (root_step .r9 a0 v a2))⟩

theorem vp_9_221 (a0 a1 a2 v : T) (hv : Step a0 v) :
    Join (op (sq a0) (sq (sq a1))) (op (sq a0) (op (sq a1) (sq v))) := by
  exact ⟨(op (sq v) (sq (sq a1))), ((Relation.ReflTransGen.refl).tail (Step.left (sq (sq a1)) (Step.sq hv))), (((Relation.ReflTransGen.refl).tail (Step.left (op (sq a1) (sq v)) (Step.sq hv))).tail (root_step .r9 v a1 a2))⟩

theorem peak_0 (a0 a1 a2 : T) {u : T} (h : Step (op a0 a0) u) :
    Join (sq a0) u := by
  rcases step_op_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
  · rcases hr with ⟨k, b0, b1, b2, heq, rfl⟩
    cases k with
    | r0 => exact cp_0_root_0 a0 a1 a2 b0 b1 b2 heq
    | r1 => exact cp_0_root_1 a0 a1 a2 b0 b1 b2 heq
    | r2 => exact cp_0_root_2 a0 a1 a2 b0 b1 b2 heq
    | r3 => exact cp_0_root_3 a0 a1 a2 b0 b1 b2 heq
    | r4 => exact cp_0_root_4 a0 a1 a2 b0 b1 b2 heq
    | r5 => exact cp_0_root_5 a0 a1 a2 b0 b1 b2 heq
    | r6 => exact cp_0_root_6 a0 a1 a2 b0 b1 b2 heq
    | r7 => exact cp_0_root_7 a0 a1 a2 b0 b1 b2 heq
    | r8 => exact cp_0_root_8 a0 a1 a2 b0 b1 b2 heq
    | r9 => exact cp_0_root_9 a0 a1 a2 b0 b1 b2 heq
  ·
    exact vp_0_1 a0 a1 a2 u0 h0
  ·
    exact vp_0_2 a0 a1 a2 u0 h0

theorem peak_1 (a0 a1 a2 : T) {u : T} (h : Step (op a0 (op (op a1 (op a0 (sq a2))) a0)) u) :
    Join a1 u := by
  rcases step_op_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
  · rcases hr with ⟨k, b0, b1, b2, heq, rfl⟩
    cases k with
    | r0 => exact cp_1_root_0 a0 a1 a2 b0 b1 b2 heq
    | r1 => exact cp_1_root_1 a0 a1 a2 b0 b1 b2 heq
    | r2 => exact cp_1_root_2 a0 a1 a2 b0 b1 b2 heq
    | r3 => exact cp_1_root_3 a0 a1 a2 b0 b1 b2 heq
    | r4 => exact cp_1_root_4 a0 a1 a2 b0 b1 b2 heq
    | r5 => exact cp_1_root_5 a0 a1 a2 b0 b1 b2 heq
    | r6 => exact cp_1_root_6 a0 a1 a2 b0 b1 b2 heq
    | r7 => exact cp_1_root_7 a0 a1 a2 b0 b1 b2 heq
    | r8 => exact cp_1_root_8 a0 a1 a2 b0 b1 b2 heq
    | r9 => exact cp_1_root_9 a0 a1 a2 b0 b1 b2 heq
  ·
    exact vp_1_1 a0 a1 a2 u0 h0
  ·
    rcases step_op_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
    · rcases hr with ⟨k, b0, b1, b2, heq, rfl⟩
      cases k with
      | r0 => exact cp_1_2_0 a0 a1 a2 b0 b1 b2 heq
      | r1 => exact cp_1_2_1 a0 a1 a2 b0 b1 b2 heq
      | r2 => exact cp_1_2_2 a0 a1 a2 b0 b1 b2 heq
      | r3 => exact cp_1_2_3 a0 a1 a2 b0 b1 b2 heq
      | r4 => exact cp_1_2_4 a0 a1 a2 b0 b1 b2 heq
      | r5 => exact cp_1_2_5 a0 a1 a2 b0 b1 b2 heq
      | r6 => exact cp_1_2_6 a0 a1 a2 b0 b1 b2 heq
      | r7 => exact cp_1_2_7 a0 a1 a2 b0 b1 b2 heq
      | r8 => exact cp_1_2_8 a0 a1 a2 b0 b1 b2 heq
      | r9 => exact cp_1_2_9 a0 a1 a2 b0 b1 b2 heq
    ·
      rcases step_op_cases h1 with hr | ⟨u2, rfl, h2⟩ | ⟨u2, rfl, h2⟩
      · rcases hr with ⟨k, b0, b1, b2, heq, rfl⟩
        cases k with
        | r0 => exact cp_1_21_0 a0 a1 a2 b0 b1 b2 heq
        | r1 => exact cp_1_21_1 a0 a1 a2 b0 b1 b2 heq
        | r2 => exact cp_1_21_2 a0 a1 a2 b0 b1 b2 heq
        | r3 => exact cp_1_21_3 a0 a1 a2 b0 b1 b2 heq
        | r4 => exact cp_1_21_4 a0 a1 a2 b0 b1 b2 heq
        | r5 => exact cp_1_21_5 a0 a1 a2 b0 b1 b2 heq
        | r6 => exact cp_1_21_6 a0 a1 a2 b0 b1 b2 heq
        | r7 => exact cp_1_21_7 a0 a1 a2 b0 b1 b2 heq
        | r8 => exact cp_1_21_8 a0 a1 a2 b0 b1 b2 heq
        | r9 => exact cp_1_21_9 a0 a1 a2 b0 b1 b2 heq
      ·
        exact vp_1_211 a0 a1 a2 u2 h2
      ·
        rcases step_op_cases h2 with hr | ⟨u3, rfl, h3⟩ | ⟨u3, rfl, h3⟩
        · rcases hr with ⟨k, b0, b1, b2, heq, rfl⟩
          cases k with
          | r0 => exact cp_1_212_0 a0 a1 a2 b0 b1 b2 heq
          | r1 => exact cp_1_212_1 a0 a1 a2 b0 b1 b2 heq
          | r2 => exact cp_1_212_2 a0 a1 a2 b0 b1 b2 heq
          | r3 => exact cp_1_212_3 a0 a1 a2 b0 b1 b2 heq
          | r4 => exact cp_1_212_4 a0 a1 a2 b0 b1 b2 heq
          | r5 => exact cp_1_212_5 a0 a1 a2 b0 b1 b2 heq
          | r6 => exact cp_1_212_6 a0 a1 a2 b0 b1 b2 heq
          | r7 => exact cp_1_212_7 a0 a1 a2 b0 b1 b2 heq
          | r8 => exact cp_1_212_8 a0 a1 a2 b0 b1 b2 heq
          | r9 => exact cp_1_212_9 a0 a1 a2 b0 b1 b2 heq
        ·
          exact vp_1_2121 a0 a1 a2 u3 h3
        ·
          rcases step_sq_cases h3 with hr | ⟨u4, rfl, h4⟩
          · rcases hr with ⟨k, b0, b1, b2, heq, rfl⟩
            cases k with
            | r0 => exact cp_1_2122_0 a0 a1 a2 b0 b1 b2 heq
            | r1 => exact cp_1_2122_1 a0 a1 a2 b0 b1 b2 heq
            | r2 => exact cp_1_2122_2 a0 a1 a2 b0 b1 b2 heq
            | r3 => exact cp_1_2122_3 a0 a1 a2 b0 b1 b2 heq
            | r4 => exact cp_1_2122_4 a0 a1 a2 b0 b1 b2 heq
            | r5 => exact cp_1_2122_5 a0 a1 a2 b0 b1 b2 heq
            | r6 => exact cp_1_2122_6 a0 a1 a2 b0 b1 b2 heq
            | r7 => exact cp_1_2122_7 a0 a1 a2 b0 b1 b2 heq
            | r8 => exact cp_1_2122_8 a0 a1 a2 b0 b1 b2 heq
            | r9 => exact cp_1_2122_9 a0 a1 a2 b0 b1 b2 heq
          ·
            exact vp_1_21221 a0 a1 a2 u4 h4
    ·
      exact vp_1_22 a0 a1 a2 u1 h1

theorem peak_2 (a0 a1 a2 : T) {u : T} (h : Step (op a0 (op (sq (op a0 (sq a1))) a0)) u) :
    Join (op a0 (sq a1)) u := by
  rcases step_op_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
  · rcases hr with ⟨k, b0, b1, b2, heq, rfl⟩
    cases k with
    | r0 => exact cp_2_root_0 a0 a1 a2 b0 b1 b2 heq
    | r1 => exact cp_2_root_1 a0 a1 a2 b0 b1 b2 heq
    | r2 => exact cp_2_root_2 a0 a1 a2 b0 b1 b2 heq
    | r3 => exact cp_2_root_3 a0 a1 a2 b0 b1 b2 heq
    | r4 => exact cp_2_root_4 a0 a1 a2 b0 b1 b2 heq
    | r5 => exact cp_2_root_5 a0 a1 a2 b0 b1 b2 heq
    | r6 => exact cp_2_root_6 a0 a1 a2 b0 b1 b2 heq
    | r7 => exact cp_2_root_7 a0 a1 a2 b0 b1 b2 heq
    | r8 => exact cp_2_root_8 a0 a1 a2 b0 b1 b2 heq
    | r9 => exact cp_2_root_9 a0 a1 a2 b0 b1 b2 heq
  ·
    exact vp_2_1 a0 a1 a2 u0 h0
  ·
    rcases step_op_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
    · rcases hr with ⟨k, b0, b1, b2, heq, rfl⟩
      cases k with
      | r0 => exact cp_2_2_0 a0 a1 a2 b0 b1 b2 heq
      | r1 => exact cp_2_2_1 a0 a1 a2 b0 b1 b2 heq
      | r2 => exact cp_2_2_2 a0 a1 a2 b0 b1 b2 heq
      | r3 => exact cp_2_2_3 a0 a1 a2 b0 b1 b2 heq
      | r4 => exact cp_2_2_4 a0 a1 a2 b0 b1 b2 heq
      | r5 => exact cp_2_2_5 a0 a1 a2 b0 b1 b2 heq
      | r6 => exact cp_2_2_6 a0 a1 a2 b0 b1 b2 heq
      | r7 => exact cp_2_2_7 a0 a1 a2 b0 b1 b2 heq
      | r8 => exact cp_2_2_8 a0 a1 a2 b0 b1 b2 heq
      | r9 => exact cp_2_2_9 a0 a1 a2 b0 b1 b2 heq
    ·
      rcases step_sq_cases h1 with hr | ⟨u2, rfl, h2⟩
      · rcases hr with ⟨k, b0, b1, b2, heq, rfl⟩
        cases k with
        | r0 => exact cp_2_21_0 a0 a1 a2 b0 b1 b2 heq
        | r1 => exact cp_2_21_1 a0 a1 a2 b0 b1 b2 heq
        | r2 => exact cp_2_21_2 a0 a1 a2 b0 b1 b2 heq
        | r3 => exact cp_2_21_3 a0 a1 a2 b0 b1 b2 heq
        | r4 => exact cp_2_21_4 a0 a1 a2 b0 b1 b2 heq
        | r5 => exact cp_2_21_5 a0 a1 a2 b0 b1 b2 heq
        | r6 => exact cp_2_21_6 a0 a1 a2 b0 b1 b2 heq
        | r7 => exact cp_2_21_7 a0 a1 a2 b0 b1 b2 heq
        | r8 => exact cp_2_21_8 a0 a1 a2 b0 b1 b2 heq
        | r9 => exact cp_2_21_9 a0 a1 a2 b0 b1 b2 heq
      ·
        rcases step_op_cases h2 with hr | ⟨u3, rfl, h3⟩ | ⟨u3, rfl, h3⟩
        · rcases hr with ⟨k, b0, b1, b2, heq, rfl⟩
          cases k with
          | r0 => exact cp_2_211_0 a0 a1 a2 b0 b1 b2 heq
          | r1 => exact cp_2_211_1 a0 a1 a2 b0 b1 b2 heq
          | r2 => exact cp_2_211_2 a0 a1 a2 b0 b1 b2 heq
          | r3 => exact cp_2_211_3 a0 a1 a2 b0 b1 b2 heq
          | r4 => exact cp_2_211_4 a0 a1 a2 b0 b1 b2 heq
          | r5 => exact cp_2_211_5 a0 a1 a2 b0 b1 b2 heq
          | r6 => exact cp_2_211_6 a0 a1 a2 b0 b1 b2 heq
          | r7 => exact cp_2_211_7 a0 a1 a2 b0 b1 b2 heq
          | r8 => exact cp_2_211_8 a0 a1 a2 b0 b1 b2 heq
          | r9 => exact cp_2_211_9 a0 a1 a2 b0 b1 b2 heq
        ·
          exact vp_2_2111 a0 a1 a2 u3 h3
        ·
          rcases step_sq_cases h3 with hr | ⟨u4, rfl, h4⟩
          · rcases hr with ⟨k, b0, b1, b2, heq, rfl⟩
            cases k with
            | r0 => exact cp_2_2112_0 a0 a1 a2 b0 b1 b2 heq
            | r1 => exact cp_2_2112_1 a0 a1 a2 b0 b1 b2 heq
            | r2 => exact cp_2_2112_2 a0 a1 a2 b0 b1 b2 heq
            | r3 => exact cp_2_2112_3 a0 a1 a2 b0 b1 b2 heq
            | r4 => exact cp_2_2112_4 a0 a1 a2 b0 b1 b2 heq
            | r5 => exact cp_2_2112_5 a0 a1 a2 b0 b1 b2 heq
            | r6 => exact cp_2_2112_6 a0 a1 a2 b0 b1 b2 heq
            | r7 => exact cp_2_2112_7 a0 a1 a2 b0 b1 b2 heq
            | r8 => exact cp_2_2112_8 a0 a1 a2 b0 b1 b2 heq
            | r9 => exact cp_2_2112_9 a0 a1 a2 b0 b1 b2 heq
          ·
            exact vp_2_21121 a0 a1 a2 u4 h4
    ·
      exact vp_2_22 a0 a1 a2 u1 h1

theorem peak_3 (a0 a1 a2 : T) {u : T} (h : Step (op (sq a0) (op (op a1 (sq (sq a0))) (sq a0))) u) :
    Join a1 u := by
  rcases step_op_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
  · rcases hr with ⟨k, b0, b1, b2, heq, rfl⟩
    cases k with
    | r0 => exact cp_3_root_0 a0 a1 a2 b0 b1 b2 heq
    | r1 => exact cp_3_root_1 a0 a1 a2 b0 b1 b2 heq
    | r2 => exact cp_3_root_2 a0 a1 a2 b0 b1 b2 heq
    | r3 => exact cp_3_root_3 a0 a1 a2 b0 b1 b2 heq
    | r4 => exact cp_3_root_4 a0 a1 a2 b0 b1 b2 heq
    | r5 => exact cp_3_root_5 a0 a1 a2 b0 b1 b2 heq
    | r6 => exact cp_3_root_6 a0 a1 a2 b0 b1 b2 heq
    | r7 => exact cp_3_root_7 a0 a1 a2 b0 b1 b2 heq
    | r8 => exact cp_3_root_8 a0 a1 a2 b0 b1 b2 heq
    | r9 => exact cp_3_root_9 a0 a1 a2 b0 b1 b2 heq
  ·
    rcases step_sq_cases h0 with hr | ⟨u1, rfl, h1⟩
    · rcases hr with ⟨k, b0, b1, b2, heq, rfl⟩
      cases k with
      | r0 => exact cp_3_1_0 a0 a1 a2 b0 b1 b2 heq
      | r1 => exact cp_3_1_1 a0 a1 a2 b0 b1 b2 heq
      | r2 => exact cp_3_1_2 a0 a1 a2 b0 b1 b2 heq
      | r3 => exact cp_3_1_3 a0 a1 a2 b0 b1 b2 heq
      | r4 => exact cp_3_1_4 a0 a1 a2 b0 b1 b2 heq
      | r5 => exact cp_3_1_5 a0 a1 a2 b0 b1 b2 heq
      | r6 => exact cp_3_1_6 a0 a1 a2 b0 b1 b2 heq
      | r7 => exact cp_3_1_7 a0 a1 a2 b0 b1 b2 heq
      | r8 => exact cp_3_1_8 a0 a1 a2 b0 b1 b2 heq
      | r9 => exact cp_3_1_9 a0 a1 a2 b0 b1 b2 heq
    ·
      exact vp_3_11 a0 a1 a2 u1 h1
  ·
    rcases step_op_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
    · rcases hr with ⟨k, b0, b1, b2, heq, rfl⟩
      cases k with
      | r0 => exact cp_3_2_0 a0 a1 a2 b0 b1 b2 heq
      | r1 => exact cp_3_2_1 a0 a1 a2 b0 b1 b2 heq
      | r2 => exact cp_3_2_2 a0 a1 a2 b0 b1 b2 heq
      | r3 => exact cp_3_2_3 a0 a1 a2 b0 b1 b2 heq
      | r4 => exact cp_3_2_4 a0 a1 a2 b0 b1 b2 heq
      | r5 => exact cp_3_2_5 a0 a1 a2 b0 b1 b2 heq
      | r6 => exact cp_3_2_6 a0 a1 a2 b0 b1 b2 heq
      | r7 => exact cp_3_2_7 a0 a1 a2 b0 b1 b2 heq
      | r8 => exact cp_3_2_8 a0 a1 a2 b0 b1 b2 heq
      | r9 => exact cp_3_2_9 a0 a1 a2 b0 b1 b2 heq
    ·
      rcases step_op_cases h1 with hr | ⟨u2, rfl, h2⟩ | ⟨u2, rfl, h2⟩
      · rcases hr with ⟨k, b0, b1, b2, heq, rfl⟩
        cases k with
        | r0 => exact cp_3_21_0 a0 a1 a2 b0 b1 b2 heq
        | r1 => exact cp_3_21_1 a0 a1 a2 b0 b1 b2 heq
        | r2 => exact cp_3_21_2 a0 a1 a2 b0 b1 b2 heq
        | r3 => exact cp_3_21_3 a0 a1 a2 b0 b1 b2 heq
        | r4 => exact cp_3_21_4 a0 a1 a2 b0 b1 b2 heq
        | r5 => exact cp_3_21_5 a0 a1 a2 b0 b1 b2 heq
        | r6 => exact cp_3_21_6 a0 a1 a2 b0 b1 b2 heq
        | r7 => exact cp_3_21_7 a0 a1 a2 b0 b1 b2 heq
        | r8 => exact cp_3_21_8 a0 a1 a2 b0 b1 b2 heq
        | r9 => exact cp_3_21_9 a0 a1 a2 b0 b1 b2 heq
      ·
        exact vp_3_211 a0 a1 a2 u2 h2
      ·
        rcases step_sq_cases h2 with hr | ⟨u3, rfl, h3⟩
        · rcases hr with ⟨k, b0, b1, b2, heq, rfl⟩
          cases k with
          | r0 => exact cp_3_212_0 a0 a1 a2 b0 b1 b2 heq
          | r1 => exact cp_3_212_1 a0 a1 a2 b0 b1 b2 heq
          | r2 => exact cp_3_212_2 a0 a1 a2 b0 b1 b2 heq
          | r3 => exact cp_3_212_3 a0 a1 a2 b0 b1 b2 heq
          | r4 => exact cp_3_212_4 a0 a1 a2 b0 b1 b2 heq
          | r5 => exact cp_3_212_5 a0 a1 a2 b0 b1 b2 heq
          | r6 => exact cp_3_212_6 a0 a1 a2 b0 b1 b2 heq
          | r7 => exact cp_3_212_7 a0 a1 a2 b0 b1 b2 heq
          | r8 => exact cp_3_212_8 a0 a1 a2 b0 b1 b2 heq
          | r9 => exact cp_3_212_9 a0 a1 a2 b0 b1 b2 heq
        ·
          rcases step_sq_cases h3 with hr | ⟨u4, rfl, h4⟩
          · rcases hr with ⟨k, b0, b1, b2, heq, rfl⟩
            cases k with
            | r0 => exact cp_3_2121_0 a0 a1 a2 b0 b1 b2 heq
            | r1 => exact cp_3_2121_1 a0 a1 a2 b0 b1 b2 heq
            | r2 => exact cp_3_2121_2 a0 a1 a2 b0 b1 b2 heq
            | r3 => exact cp_3_2121_3 a0 a1 a2 b0 b1 b2 heq
            | r4 => exact cp_3_2121_4 a0 a1 a2 b0 b1 b2 heq
            | r5 => exact cp_3_2121_5 a0 a1 a2 b0 b1 b2 heq
            | r6 => exact cp_3_2121_6 a0 a1 a2 b0 b1 b2 heq
            | r7 => exact cp_3_2121_7 a0 a1 a2 b0 b1 b2 heq
            | r8 => exact cp_3_2121_8 a0 a1 a2 b0 b1 b2 heq
            | r9 => exact cp_3_2121_9 a0 a1 a2 b0 b1 b2 heq
          ·
            exact vp_3_21211 a0 a1 a2 u4 h4
    ·
      rcases step_sq_cases h1 with hr | ⟨u2, rfl, h2⟩
      · rcases hr with ⟨k, b0, b1, b2, heq, rfl⟩
        cases k with
        | r0 => exact cp_3_22_0 a0 a1 a2 b0 b1 b2 heq
        | r1 => exact cp_3_22_1 a0 a1 a2 b0 b1 b2 heq
        | r2 => exact cp_3_22_2 a0 a1 a2 b0 b1 b2 heq
        | r3 => exact cp_3_22_3 a0 a1 a2 b0 b1 b2 heq
        | r4 => exact cp_3_22_4 a0 a1 a2 b0 b1 b2 heq
        | r5 => exact cp_3_22_5 a0 a1 a2 b0 b1 b2 heq
        | r6 => exact cp_3_22_6 a0 a1 a2 b0 b1 b2 heq
        | r7 => exact cp_3_22_7 a0 a1 a2 b0 b1 b2 heq
        | r8 => exact cp_3_22_8 a0 a1 a2 b0 b1 b2 heq
        | r9 => exact cp_3_22_9 a0 a1 a2 b0 b1 b2 heq
      ·
        exact vp_3_221 a0 a1 a2 u2 h2

theorem peak_4 (a0 a1 a2 : T) {u : T} (h : Step (op (op a0 (op (sq a1) (sq a2))) (op a0 (op a0 (op (sq a1) (sq a2))))) u) :
    Join (sq a1) u := by
  rcases step_op_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
  · rcases hr with ⟨k, b0, b1, b2, heq, rfl⟩
    cases k with
    | r0 => exact cp_4_root_0 a0 a1 a2 b0 b1 b2 heq
    | r1 => exact cp_4_root_1 a0 a1 a2 b0 b1 b2 heq
    | r2 => exact cp_4_root_2 a0 a1 a2 b0 b1 b2 heq
    | r3 => exact cp_4_root_3 a0 a1 a2 b0 b1 b2 heq
    | r4 => exact cp_4_root_4 a0 a1 a2 b0 b1 b2 heq
    | r5 => exact cp_4_root_5 a0 a1 a2 b0 b1 b2 heq
    | r6 => exact cp_4_root_6 a0 a1 a2 b0 b1 b2 heq
    | r7 => exact cp_4_root_7 a0 a1 a2 b0 b1 b2 heq
    | r8 => exact cp_4_root_8 a0 a1 a2 b0 b1 b2 heq
    | r9 => exact cp_4_root_9 a0 a1 a2 b0 b1 b2 heq
  ·
    rcases step_op_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
    · rcases hr with ⟨k, b0, b1, b2, heq, rfl⟩
      cases k with
      | r0 => exact cp_4_1_0 a0 a1 a2 b0 b1 b2 heq
      | r1 => exact cp_4_1_1 a0 a1 a2 b0 b1 b2 heq
      | r2 => exact cp_4_1_2 a0 a1 a2 b0 b1 b2 heq
      | r3 => exact cp_4_1_3 a0 a1 a2 b0 b1 b2 heq
      | r4 => exact cp_4_1_4 a0 a1 a2 b0 b1 b2 heq
      | r5 => exact cp_4_1_5 a0 a1 a2 b0 b1 b2 heq
      | r6 => exact cp_4_1_6 a0 a1 a2 b0 b1 b2 heq
      | r7 => exact cp_4_1_7 a0 a1 a2 b0 b1 b2 heq
      | r8 => exact cp_4_1_8 a0 a1 a2 b0 b1 b2 heq
      | r9 => exact cp_4_1_9 a0 a1 a2 b0 b1 b2 heq
    ·
      exact vp_4_11 a0 a1 a2 u1 h1
    ·
      rcases step_op_cases h1 with hr | ⟨u2, rfl, h2⟩ | ⟨u2, rfl, h2⟩
      · rcases hr with ⟨k, b0, b1, b2, heq, rfl⟩
        cases k with
        | r0 => exact cp_4_12_0 a0 a1 a2 b0 b1 b2 heq
        | r1 => exact cp_4_12_1 a0 a1 a2 b0 b1 b2 heq
        | r2 => exact cp_4_12_2 a0 a1 a2 b0 b1 b2 heq
        | r3 => exact cp_4_12_3 a0 a1 a2 b0 b1 b2 heq
        | r4 => exact cp_4_12_4 a0 a1 a2 b0 b1 b2 heq
        | r5 => exact cp_4_12_5 a0 a1 a2 b0 b1 b2 heq
        | r6 => exact cp_4_12_6 a0 a1 a2 b0 b1 b2 heq
        | r7 => exact cp_4_12_7 a0 a1 a2 b0 b1 b2 heq
        | r8 => exact cp_4_12_8 a0 a1 a2 b0 b1 b2 heq
        | r9 => exact cp_4_12_9 a0 a1 a2 b0 b1 b2 heq
      ·
        rcases step_sq_cases h2 with hr | ⟨u3, rfl, h3⟩
        · rcases hr with ⟨k, b0, b1, b2, heq, rfl⟩
          cases k with
          | r0 => exact cp_4_121_0 a0 a1 a2 b0 b1 b2 heq
          | r1 => exact cp_4_121_1 a0 a1 a2 b0 b1 b2 heq
          | r2 => exact cp_4_121_2 a0 a1 a2 b0 b1 b2 heq
          | r3 => exact cp_4_121_3 a0 a1 a2 b0 b1 b2 heq
          | r4 => exact cp_4_121_4 a0 a1 a2 b0 b1 b2 heq
          | r5 => exact cp_4_121_5 a0 a1 a2 b0 b1 b2 heq
          | r6 => exact cp_4_121_6 a0 a1 a2 b0 b1 b2 heq
          | r7 => exact cp_4_121_7 a0 a1 a2 b0 b1 b2 heq
          | r8 => exact cp_4_121_8 a0 a1 a2 b0 b1 b2 heq
          | r9 => exact cp_4_121_9 a0 a1 a2 b0 b1 b2 heq
        ·
          exact vp_4_1211 a0 a1 a2 u3 h3
      ·
        rcases step_sq_cases h2 with hr | ⟨u3, rfl, h3⟩
        · rcases hr with ⟨k, b0, b1, b2, heq, rfl⟩
          cases k with
          | r0 => exact cp_4_122_0 a0 a1 a2 b0 b1 b2 heq
          | r1 => exact cp_4_122_1 a0 a1 a2 b0 b1 b2 heq
          | r2 => exact cp_4_122_2 a0 a1 a2 b0 b1 b2 heq
          | r3 => exact cp_4_122_3 a0 a1 a2 b0 b1 b2 heq
          | r4 => exact cp_4_122_4 a0 a1 a2 b0 b1 b2 heq
          | r5 => exact cp_4_122_5 a0 a1 a2 b0 b1 b2 heq
          | r6 => exact cp_4_122_6 a0 a1 a2 b0 b1 b2 heq
          | r7 => exact cp_4_122_7 a0 a1 a2 b0 b1 b2 heq
          | r8 => exact cp_4_122_8 a0 a1 a2 b0 b1 b2 heq
          | r9 => exact cp_4_122_9 a0 a1 a2 b0 b1 b2 heq
        ·
          exact vp_4_1221 a0 a1 a2 u3 h3
  ·
    rcases step_op_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
    · rcases hr with ⟨k, b0, b1, b2, heq, rfl⟩
      cases k with
      | r0 => exact cp_4_2_0 a0 a1 a2 b0 b1 b2 heq
      | r1 => exact cp_4_2_1 a0 a1 a2 b0 b1 b2 heq
      | r2 => exact cp_4_2_2 a0 a1 a2 b0 b1 b2 heq
      | r3 => exact cp_4_2_3 a0 a1 a2 b0 b1 b2 heq
      | r4 => exact cp_4_2_4 a0 a1 a2 b0 b1 b2 heq
      | r5 => exact cp_4_2_5 a0 a1 a2 b0 b1 b2 heq
      | r6 => exact cp_4_2_6 a0 a1 a2 b0 b1 b2 heq
      | r7 => exact cp_4_2_7 a0 a1 a2 b0 b1 b2 heq
      | r8 => exact cp_4_2_8 a0 a1 a2 b0 b1 b2 heq
      | r9 => exact cp_4_2_9 a0 a1 a2 b0 b1 b2 heq
    ·
      exact vp_4_21 a0 a1 a2 u1 h1
    ·
      rcases step_op_cases h1 with hr | ⟨u2, rfl, h2⟩ | ⟨u2, rfl, h2⟩
      · rcases hr with ⟨k, b0, b1, b2, heq, rfl⟩
        cases k with
        | r0 => exact cp_4_22_0 a0 a1 a2 b0 b1 b2 heq
        | r1 => exact cp_4_22_1 a0 a1 a2 b0 b1 b2 heq
        | r2 => exact cp_4_22_2 a0 a1 a2 b0 b1 b2 heq
        | r3 => exact cp_4_22_3 a0 a1 a2 b0 b1 b2 heq
        | r4 => exact cp_4_22_4 a0 a1 a2 b0 b1 b2 heq
        | r5 => exact cp_4_22_5 a0 a1 a2 b0 b1 b2 heq
        | r6 => exact cp_4_22_6 a0 a1 a2 b0 b1 b2 heq
        | r7 => exact cp_4_22_7 a0 a1 a2 b0 b1 b2 heq
        | r8 => exact cp_4_22_8 a0 a1 a2 b0 b1 b2 heq
        | r9 => exact cp_4_22_9 a0 a1 a2 b0 b1 b2 heq
      ·
        exact vp_4_221 a0 a1 a2 u2 h2
      ·
        rcases step_op_cases h2 with hr | ⟨u3, rfl, h3⟩ | ⟨u3, rfl, h3⟩
        · rcases hr with ⟨k, b0, b1, b2, heq, rfl⟩
          cases k with
          | r0 => exact cp_4_222_0 a0 a1 a2 b0 b1 b2 heq
          | r1 => exact cp_4_222_1 a0 a1 a2 b0 b1 b2 heq
          | r2 => exact cp_4_222_2 a0 a1 a2 b0 b1 b2 heq
          | r3 => exact cp_4_222_3 a0 a1 a2 b0 b1 b2 heq
          | r4 => exact cp_4_222_4 a0 a1 a2 b0 b1 b2 heq
          | r5 => exact cp_4_222_5 a0 a1 a2 b0 b1 b2 heq
          | r6 => exact cp_4_222_6 a0 a1 a2 b0 b1 b2 heq
          | r7 => exact cp_4_222_7 a0 a1 a2 b0 b1 b2 heq
          | r8 => exact cp_4_222_8 a0 a1 a2 b0 b1 b2 heq
          | r9 => exact cp_4_222_9 a0 a1 a2 b0 b1 b2 heq
        ·
          rcases step_sq_cases h3 with hr | ⟨u4, rfl, h4⟩
          · rcases hr with ⟨k, b0, b1, b2, heq, rfl⟩
            cases k with
            | r0 => exact cp_4_2221_0 a0 a1 a2 b0 b1 b2 heq
            | r1 => exact cp_4_2221_1 a0 a1 a2 b0 b1 b2 heq
            | r2 => exact cp_4_2221_2 a0 a1 a2 b0 b1 b2 heq
            | r3 => exact cp_4_2221_3 a0 a1 a2 b0 b1 b2 heq
            | r4 => exact cp_4_2221_4 a0 a1 a2 b0 b1 b2 heq
            | r5 => exact cp_4_2221_5 a0 a1 a2 b0 b1 b2 heq
            | r6 => exact cp_4_2221_6 a0 a1 a2 b0 b1 b2 heq
            | r7 => exact cp_4_2221_7 a0 a1 a2 b0 b1 b2 heq
            | r8 => exact cp_4_2221_8 a0 a1 a2 b0 b1 b2 heq
            | r9 => exact cp_4_2221_9 a0 a1 a2 b0 b1 b2 heq
          ·
            exact vp_4_22211 a0 a1 a2 u4 h4
        ·
          rcases step_sq_cases h3 with hr | ⟨u4, rfl, h4⟩
          · rcases hr with ⟨k, b0, b1, b2, heq, rfl⟩
            cases k with
            | r0 => exact cp_4_2222_0 a0 a1 a2 b0 b1 b2 heq
            | r1 => exact cp_4_2222_1 a0 a1 a2 b0 b1 b2 heq
            | r2 => exact cp_4_2222_2 a0 a1 a2 b0 b1 b2 heq
            | r3 => exact cp_4_2222_3 a0 a1 a2 b0 b1 b2 heq
            | r4 => exact cp_4_2222_4 a0 a1 a2 b0 b1 b2 heq
            | r5 => exact cp_4_2222_5 a0 a1 a2 b0 b1 b2 heq
            | r6 => exact cp_4_2222_6 a0 a1 a2 b0 b1 b2 heq
            | r7 => exact cp_4_2222_7 a0 a1 a2 b0 b1 b2 heq
            | r8 => exact cp_4_2222_8 a0 a1 a2 b0 b1 b2 heq
            | r9 => exact cp_4_2222_9 a0 a1 a2 b0 b1 b2 heq
          ·
            exact vp_4_22221 a0 a1 a2 u4 h4

theorem peak_5 (a0 a1 a2 : T) {u : T} (h : Step (sq (sq (sq (sq a0)))) u) :
    Join (sq a0) u := by
  rcases step_sq_cases h with hr | ⟨u0, rfl, h0⟩
  · rcases hr with ⟨k, b0, b1, b2, heq, rfl⟩
    cases k with
    | r0 => exact cp_5_root_0 a0 a1 a2 b0 b1 b2 heq
    | r1 => exact cp_5_root_1 a0 a1 a2 b0 b1 b2 heq
    | r2 => exact cp_5_root_2 a0 a1 a2 b0 b1 b2 heq
    | r3 => exact cp_5_root_3 a0 a1 a2 b0 b1 b2 heq
    | r4 => exact cp_5_root_4 a0 a1 a2 b0 b1 b2 heq
    | r5 => exact cp_5_root_5 a0 a1 a2 b0 b1 b2 heq
    | r6 => exact cp_5_root_6 a0 a1 a2 b0 b1 b2 heq
    | r7 => exact cp_5_root_7 a0 a1 a2 b0 b1 b2 heq
    | r8 => exact cp_5_root_8 a0 a1 a2 b0 b1 b2 heq
    | r9 => exact cp_5_root_9 a0 a1 a2 b0 b1 b2 heq
  ·
    rcases step_sq_cases h0 with hr | ⟨u1, rfl, h1⟩
    · rcases hr with ⟨k, b0, b1, b2, heq, rfl⟩
      cases k with
      | r0 => exact cp_5_1_0 a0 a1 a2 b0 b1 b2 heq
      | r1 => exact cp_5_1_1 a0 a1 a2 b0 b1 b2 heq
      | r2 => exact cp_5_1_2 a0 a1 a2 b0 b1 b2 heq
      | r3 => exact cp_5_1_3 a0 a1 a2 b0 b1 b2 heq
      | r4 => exact cp_5_1_4 a0 a1 a2 b0 b1 b2 heq
      | r5 => exact cp_5_1_5 a0 a1 a2 b0 b1 b2 heq
      | r6 => exact cp_5_1_6 a0 a1 a2 b0 b1 b2 heq
      | r7 => exact cp_5_1_7 a0 a1 a2 b0 b1 b2 heq
      | r8 => exact cp_5_1_8 a0 a1 a2 b0 b1 b2 heq
      | r9 => exact cp_5_1_9 a0 a1 a2 b0 b1 b2 heq
    ·
      rcases step_sq_cases h1 with hr | ⟨u2, rfl, h2⟩
      · rcases hr with ⟨k, b0, b1, b2, heq, rfl⟩
        cases k with
        | r0 => exact cp_5_11_0 a0 a1 a2 b0 b1 b2 heq
        | r1 => exact cp_5_11_1 a0 a1 a2 b0 b1 b2 heq
        | r2 => exact cp_5_11_2 a0 a1 a2 b0 b1 b2 heq
        | r3 => exact cp_5_11_3 a0 a1 a2 b0 b1 b2 heq
        | r4 => exact cp_5_11_4 a0 a1 a2 b0 b1 b2 heq
        | r5 => exact cp_5_11_5 a0 a1 a2 b0 b1 b2 heq
        | r6 => exact cp_5_11_6 a0 a1 a2 b0 b1 b2 heq
        | r7 => exact cp_5_11_7 a0 a1 a2 b0 b1 b2 heq
        | r8 => exact cp_5_11_8 a0 a1 a2 b0 b1 b2 heq
        | r9 => exact cp_5_11_9 a0 a1 a2 b0 b1 b2 heq
      ·
        rcases step_sq_cases h2 with hr | ⟨u3, rfl, h3⟩
        · rcases hr with ⟨k, b0, b1, b2, heq, rfl⟩
          cases k with
          | r0 => exact cp_5_111_0 a0 a1 a2 b0 b1 b2 heq
          | r1 => exact cp_5_111_1 a0 a1 a2 b0 b1 b2 heq
          | r2 => exact cp_5_111_2 a0 a1 a2 b0 b1 b2 heq
          | r3 => exact cp_5_111_3 a0 a1 a2 b0 b1 b2 heq
          | r4 => exact cp_5_111_4 a0 a1 a2 b0 b1 b2 heq
          | r5 => exact cp_5_111_5 a0 a1 a2 b0 b1 b2 heq
          | r6 => exact cp_5_111_6 a0 a1 a2 b0 b1 b2 heq
          | r7 => exact cp_5_111_7 a0 a1 a2 b0 b1 b2 heq
          | r8 => exact cp_5_111_8 a0 a1 a2 b0 b1 b2 heq
          | r9 => exact cp_5_111_9 a0 a1 a2 b0 b1 b2 heq
        ·
          exact vp_5_1111 a0 a1 a2 u3 h3

theorem peak_6 (a0 a1 a2 : T) {u : T} (h : Step (op (sq (sq (sq a0))) (op (op a1 (sq a0)) (sq (sq (sq a0))))) u) :
    Join a1 u := by
  rcases step_op_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
  · rcases hr with ⟨k, b0, b1, b2, heq, rfl⟩
    cases k with
    | r0 => exact cp_6_root_0 a0 a1 a2 b0 b1 b2 heq
    | r1 => exact cp_6_root_1 a0 a1 a2 b0 b1 b2 heq
    | r2 => exact cp_6_root_2 a0 a1 a2 b0 b1 b2 heq
    | r3 => exact cp_6_root_3 a0 a1 a2 b0 b1 b2 heq
    | r4 => exact cp_6_root_4 a0 a1 a2 b0 b1 b2 heq
    | r5 => exact cp_6_root_5 a0 a1 a2 b0 b1 b2 heq
    | r6 => exact cp_6_root_6 a0 a1 a2 b0 b1 b2 heq
    | r7 => exact cp_6_root_7 a0 a1 a2 b0 b1 b2 heq
    | r8 => exact cp_6_root_8 a0 a1 a2 b0 b1 b2 heq
    | r9 => exact cp_6_root_9 a0 a1 a2 b0 b1 b2 heq
  ·
    rcases step_sq_cases h0 with hr | ⟨u1, rfl, h1⟩
    · rcases hr with ⟨k, b0, b1, b2, heq, rfl⟩
      cases k with
      | r0 => exact cp_6_1_0 a0 a1 a2 b0 b1 b2 heq
      | r1 => exact cp_6_1_1 a0 a1 a2 b0 b1 b2 heq
      | r2 => exact cp_6_1_2 a0 a1 a2 b0 b1 b2 heq
      | r3 => exact cp_6_1_3 a0 a1 a2 b0 b1 b2 heq
      | r4 => exact cp_6_1_4 a0 a1 a2 b0 b1 b2 heq
      | r5 => exact cp_6_1_5 a0 a1 a2 b0 b1 b2 heq
      | r6 => exact cp_6_1_6 a0 a1 a2 b0 b1 b2 heq
      | r7 => exact cp_6_1_7 a0 a1 a2 b0 b1 b2 heq
      | r8 => exact cp_6_1_8 a0 a1 a2 b0 b1 b2 heq
      | r9 => exact cp_6_1_9 a0 a1 a2 b0 b1 b2 heq
    ·
      rcases step_sq_cases h1 with hr | ⟨u2, rfl, h2⟩
      · rcases hr with ⟨k, b0, b1, b2, heq, rfl⟩
        cases k with
        | r0 => exact cp_6_11_0 a0 a1 a2 b0 b1 b2 heq
        | r1 => exact cp_6_11_1 a0 a1 a2 b0 b1 b2 heq
        | r2 => exact cp_6_11_2 a0 a1 a2 b0 b1 b2 heq
        | r3 => exact cp_6_11_3 a0 a1 a2 b0 b1 b2 heq
        | r4 => exact cp_6_11_4 a0 a1 a2 b0 b1 b2 heq
        | r5 => exact cp_6_11_5 a0 a1 a2 b0 b1 b2 heq
        | r6 => exact cp_6_11_6 a0 a1 a2 b0 b1 b2 heq
        | r7 => exact cp_6_11_7 a0 a1 a2 b0 b1 b2 heq
        | r8 => exact cp_6_11_8 a0 a1 a2 b0 b1 b2 heq
        | r9 => exact cp_6_11_9 a0 a1 a2 b0 b1 b2 heq
      ·
        rcases step_sq_cases h2 with hr | ⟨u3, rfl, h3⟩
        · rcases hr with ⟨k, b0, b1, b2, heq, rfl⟩
          cases k with
          | r0 => exact cp_6_111_0 a0 a1 a2 b0 b1 b2 heq
          | r1 => exact cp_6_111_1 a0 a1 a2 b0 b1 b2 heq
          | r2 => exact cp_6_111_2 a0 a1 a2 b0 b1 b2 heq
          | r3 => exact cp_6_111_3 a0 a1 a2 b0 b1 b2 heq
          | r4 => exact cp_6_111_4 a0 a1 a2 b0 b1 b2 heq
          | r5 => exact cp_6_111_5 a0 a1 a2 b0 b1 b2 heq
          | r6 => exact cp_6_111_6 a0 a1 a2 b0 b1 b2 heq
          | r7 => exact cp_6_111_7 a0 a1 a2 b0 b1 b2 heq
          | r8 => exact cp_6_111_8 a0 a1 a2 b0 b1 b2 heq
          | r9 => exact cp_6_111_9 a0 a1 a2 b0 b1 b2 heq
        ·
          exact vp_6_1111 a0 a1 a2 u3 h3
  ·
    rcases step_op_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
    · rcases hr with ⟨k, b0, b1, b2, heq, rfl⟩
      cases k with
      | r0 => exact cp_6_2_0 a0 a1 a2 b0 b1 b2 heq
      | r1 => exact cp_6_2_1 a0 a1 a2 b0 b1 b2 heq
      | r2 => exact cp_6_2_2 a0 a1 a2 b0 b1 b2 heq
      | r3 => exact cp_6_2_3 a0 a1 a2 b0 b1 b2 heq
      | r4 => exact cp_6_2_4 a0 a1 a2 b0 b1 b2 heq
      | r5 => exact cp_6_2_5 a0 a1 a2 b0 b1 b2 heq
      | r6 => exact cp_6_2_6 a0 a1 a2 b0 b1 b2 heq
      | r7 => exact cp_6_2_7 a0 a1 a2 b0 b1 b2 heq
      | r8 => exact cp_6_2_8 a0 a1 a2 b0 b1 b2 heq
      | r9 => exact cp_6_2_9 a0 a1 a2 b0 b1 b2 heq
    ·
      rcases step_op_cases h1 with hr | ⟨u2, rfl, h2⟩ | ⟨u2, rfl, h2⟩
      · rcases hr with ⟨k, b0, b1, b2, heq, rfl⟩
        cases k with
        | r0 => exact cp_6_21_0 a0 a1 a2 b0 b1 b2 heq
        | r1 => exact cp_6_21_1 a0 a1 a2 b0 b1 b2 heq
        | r2 => exact cp_6_21_2 a0 a1 a2 b0 b1 b2 heq
        | r3 => exact cp_6_21_3 a0 a1 a2 b0 b1 b2 heq
        | r4 => exact cp_6_21_4 a0 a1 a2 b0 b1 b2 heq
        | r5 => exact cp_6_21_5 a0 a1 a2 b0 b1 b2 heq
        | r6 => exact cp_6_21_6 a0 a1 a2 b0 b1 b2 heq
        | r7 => exact cp_6_21_7 a0 a1 a2 b0 b1 b2 heq
        | r8 => exact cp_6_21_8 a0 a1 a2 b0 b1 b2 heq
        | r9 => exact cp_6_21_9 a0 a1 a2 b0 b1 b2 heq
      ·
        exact vp_6_211 a0 a1 a2 u2 h2
      ·
        rcases step_sq_cases h2 with hr | ⟨u3, rfl, h3⟩
        · rcases hr with ⟨k, b0, b1, b2, heq, rfl⟩
          cases k with
          | r0 => exact cp_6_212_0 a0 a1 a2 b0 b1 b2 heq
          | r1 => exact cp_6_212_1 a0 a1 a2 b0 b1 b2 heq
          | r2 => exact cp_6_212_2 a0 a1 a2 b0 b1 b2 heq
          | r3 => exact cp_6_212_3 a0 a1 a2 b0 b1 b2 heq
          | r4 => exact cp_6_212_4 a0 a1 a2 b0 b1 b2 heq
          | r5 => exact cp_6_212_5 a0 a1 a2 b0 b1 b2 heq
          | r6 => exact cp_6_212_6 a0 a1 a2 b0 b1 b2 heq
          | r7 => exact cp_6_212_7 a0 a1 a2 b0 b1 b2 heq
          | r8 => exact cp_6_212_8 a0 a1 a2 b0 b1 b2 heq
          | r9 => exact cp_6_212_9 a0 a1 a2 b0 b1 b2 heq
        ·
          exact vp_6_2121 a0 a1 a2 u3 h3
    ·
      rcases step_sq_cases h1 with hr | ⟨u2, rfl, h2⟩
      · rcases hr with ⟨k, b0, b1, b2, heq, rfl⟩
        cases k with
        | r0 => exact cp_6_22_0 a0 a1 a2 b0 b1 b2 heq
        | r1 => exact cp_6_22_1 a0 a1 a2 b0 b1 b2 heq
        | r2 => exact cp_6_22_2 a0 a1 a2 b0 b1 b2 heq
        | r3 => exact cp_6_22_3 a0 a1 a2 b0 b1 b2 heq
        | r4 => exact cp_6_22_4 a0 a1 a2 b0 b1 b2 heq
        | r5 => exact cp_6_22_5 a0 a1 a2 b0 b1 b2 heq
        | r6 => exact cp_6_22_6 a0 a1 a2 b0 b1 b2 heq
        | r7 => exact cp_6_22_7 a0 a1 a2 b0 b1 b2 heq
        | r8 => exact cp_6_22_8 a0 a1 a2 b0 b1 b2 heq
        | r9 => exact cp_6_22_9 a0 a1 a2 b0 b1 b2 heq
      ·
        rcases step_sq_cases h2 with hr | ⟨u3, rfl, h3⟩
        · rcases hr with ⟨k, b0, b1, b2, heq, rfl⟩
          cases k with
          | r0 => exact cp_6_221_0 a0 a1 a2 b0 b1 b2 heq
          | r1 => exact cp_6_221_1 a0 a1 a2 b0 b1 b2 heq
          | r2 => exact cp_6_221_2 a0 a1 a2 b0 b1 b2 heq
          | r3 => exact cp_6_221_3 a0 a1 a2 b0 b1 b2 heq
          | r4 => exact cp_6_221_4 a0 a1 a2 b0 b1 b2 heq
          | r5 => exact cp_6_221_5 a0 a1 a2 b0 b1 b2 heq
          | r6 => exact cp_6_221_6 a0 a1 a2 b0 b1 b2 heq
          | r7 => exact cp_6_221_7 a0 a1 a2 b0 b1 b2 heq
          | r8 => exact cp_6_221_8 a0 a1 a2 b0 b1 b2 heq
          | r9 => exact cp_6_221_9 a0 a1 a2 b0 b1 b2 heq
        ·
          rcases step_sq_cases h3 with hr | ⟨u4, rfl, h4⟩
          · rcases hr with ⟨k, b0, b1, b2, heq, rfl⟩
            cases k with
            | r0 => exact cp_6_2211_0 a0 a1 a2 b0 b1 b2 heq
            | r1 => exact cp_6_2211_1 a0 a1 a2 b0 b1 b2 heq
            | r2 => exact cp_6_2211_2 a0 a1 a2 b0 b1 b2 heq
            | r3 => exact cp_6_2211_3 a0 a1 a2 b0 b1 b2 heq
            | r4 => exact cp_6_2211_4 a0 a1 a2 b0 b1 b2 heq
            | r5 => exact cp_6_2211_5 a0 a1 a2 b0 b1 b2 heq
            | r6 => exact cp_6_2211_6 a0 a1 a2 b0 b1 b2 heq
            | r7 => exact cp_6_2211_7 a0 a1 a2 b0 b1 b2 heq
            | r8 => exact cp_6_2211_8 a0 a1 a2 b0 b1 b2 heq
            | r9 => exact cp_6_2211_9 a0 a1 a2 b0 b1 b2 heq
          ·
            exact vp_6_22111 a0 a1 a2 u4 h4

theorem peak_7 (a0 a1 a2 : T) {u : T} (h : Step (op (op a0 (sq a1)) (op a0 (op a0 (sq a1)))) u) :
    Join (sq (sq (sq a1))) u := by
  rcases step_op_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
  · rcases hr with ⟨k, b0, b1, b2, heq, rfl⟩
    cases k with
    | r0 => exact cp_7_root_0 a0 a1 a2 b0 b1 b2 heq
    | r1 => exact cp_7_root_1 a0 a1 a2 b0 b1 b2 heq
    | r2 => exact cp_7_root_2 a0 a1 a2 b0 b1 b2 heq
    | r3 => exact cp_7_root_3 a0 a1 a2 b0 b1 b2 heq
    | r4 => exact cp_7_root_4 a0 a1 a2 b0 b1 b2 heq
    | r5 => exact cp_7_root_5 a0 a1 a2 b0 b1 b2 heq
    | r6 => exact cp_7_root_6 a0 a1 a2 b0 b1 b2 heq
    | r7 => exact cp_7_root_7 a0 a1 a2 b0 b1 b2 heq
    | r8 => exact cp_7_root_8 a0 a1 a2 b0 b1 b2 heq
    | r9 => exact cp_7_root_9 a0 a1 a2 b0 b1 b2 heq
  ·
    rcases step_op_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
    · rcases hr with ⟨k, b0, b1, b2, heq, rfl⟩
      cases k with
      | r0 => exact cp_7_1_0 a0 a1 a2 b0 b1 b2 heq
      | r1 => exact cp_7_1_1 a0 a1 a2 b0 b1 b2 heq
      | r2 => exact cp_7_1_2 a0 a1 a2 b0 b1 b2 heq
      | r3 => exact cp_7_1_3 a0 a1 a2 b0 b1 b2 heq
      | r4 => exact cp_7_1_4 a0 a1 a2 b0 b1 b2 heq
      | r5 => exact cp_7_1_5 a0 a1 a2 b0 b1 b2 heq
      | r6 => exact cp_7_1_6 a0 a1 a2 b0 b1 b2 heq
      | r7 => exact cp_7_1_7 a0 a1 a2 b0 b1 b2 heq
      | r8 => exact cp_7_1_8 a0 a1 a2 b0 b1 b2 heq
      | r9 => exact cp_7_1_9 a0 a1 a2 b0 b1 b2 heq
    ·
      exact vp_7_11 a0 a1 a2 u1 h1
    ·
      rcases step_sq_cases h1 with hr | ⟨u2, rfl, h2⟩
      · rcases hr with ⟨k, b0, b1, b2, heq, rfl⟩
        cases k with
        | r0 => exact cp_7_12_0 a0 a1 a2 b0 b1 b2 heq
        | r1 => exact cp_7_12_1 a0 a1 a2 b0 b1 b2 heq
        | r2 => exact cp_7_12_2 a0 a1 a2 b0 b1 b2 heq
        | r3 => exact cp_7_12_3 a0 a1 a2 b0 b1 b2 heq
        | r4 => exact cp_7_12_4 a0 a1 a2 b0 b1 b2 heq
        | r5 => exact cp_7_12_5 a0 a1 a2 b0 b1 b2 heq
        | r6 => exact cp_7_12_6 a0 a1 a2 b0 b1 b2 heq
        | r7 => exact cp_7_12_7 a0 a1 a2 b0 b1 b2 heq
        | r8 => exact cp_7_12_8 a0 a1 a2 b0 b1 b2 heq
        | r9 => exact cp_7_12_9 a0 a1 a2 b0 b1 b2 heq
      ·
        exact vp_7_121 a0 a1 a2 u2 h2
  ·
    rcases step_op_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
    · rcases hr with ⟨k, b0, b1, b2, heq, rfl⟩
      cases k with
      | r0 => exact cp_7_2_0 a0 a1 a2 b0 b1 b2 heq
      | r1 => exact cp_7_2_1 a0 a1 a2 b0 b1 b2 heq
      | r2 => exact cp_7_2_2 a0 a1 a2 b0 b1 b2 heq
      | r3 => exact cp_7_2_3 a0 a1 a2 b0 b1 b2 heq
      | r4 => exact cp_7_2_4 a0 a1 a2 b0 b1 b2 heq
      | r5 => exact cp_7_2_5 a0 a1 a2 b0 b1 b2 heq
      | r6 => exact cp_7_2_6 a0 a1 a2 b0 b1 b2 heq
      | r7 => exact cp_7_2_7 a0 a1 a2 b0 b1 b2 heq
      | r8 => exact cp_7_2_8 a0 a1 a2 b0 b1 b2 heq
      | r9 => exact cp_7_2_9 a0 a1 a2 b0 b1 b2 heq
    ·
      exact vp_7_21 a0 a1 a2 u1 h1
    ·
      rcases step_op_cases h1 with hr | ⟨u2, rfl, h2⟩ | ⟨u2, rfl, h2⟩
      · rcases hr with ⟨k, b0, b1, b2, heq, rfl⟩
        cases k with
        | r0 => exact cp_7_22_0 a0 a1 a2 b0 b1 b2 heq
        | r1 => exact cp_7_22_1 a0 a1 a2 b0 b1 b2 heq
        | r2 => exact cp_7_22_2 a0 a1 a2 b0 b1 b2 heq
        | r3 => exact cp_7_22_3 a0 a1 a2 b0 b1 b2 heq
        | r4 => exact cp_7_22_4 a0 a1 a2 b0 b1 b2 heq
        | r5 => exact cp_7_22_5 a0 a1 a2 b0 b1 b2 heq
        | r6 => exact cp_7_22_6 a0 a1 a2 b0 b1 b2 heq
        | r7 => exact cp_7_22_7 a0 a1 a2 b0 b1 b2 heq
        | r8 => exact cp_7_22_8 a0 a1 a2 b0 b1 b2 heq
        | r9 => exact cp_7_22_9 a0 a1 a2 b0 b1 b2 heq
      ·
        exact vp_7_221 a0 a1 a2 u2 h2
      ·
        rcases step_sq_cases h2 with hr | ⟨u3, rfl, h3⟩
        · rcases hr with ⟨k, b0, b1, b2, heq, rfl⟩
          cases k with
          | r0 => exact cp_7_222_0 a0 a1 a2 b0 b1 b2 heq
          | r1 => exact cp_7_222_1 a0 a1 a2 b0 b1 b2 heq
          | r2 => exact cp_7_222_2 a0 a1 a2 b0 b1 b2 heq
          | r3 => exact cp_7_222_3 a0 a1 a2 b0 b1 b2 heq
          | r4 => exact cp_7_222_4 a0 a1 a2 b0 b1 b2 heq
          | r5 => exact cp_7_222_5 a0 a1 a2 b0 b1 b2 heq
          | r6 => exact cp_7_222_6 a0 a1 a2 b0 b1 b2 heq
          | r7 => exact cp_7_222_7 a0 a1 a2 b0 b1 b2 heq
          | r8 => exact cp_7_222_8 a0 a1 a2 b0 b1 b2 heq
          | r9 => exact cp_7_222_9 a0 a1 a2 b0 b1 b2 heq
        ·
          exact vp_7_2221 a0 a1 a2 u3 h3

theorem peak_8 (a0 a1 a2 : T) {u : T} (h : Step (sq (op (sq a0) (sq a1))) u) :
    Join (sq (sq (sq a1))) u := by
  rcases step_sq_cases h with hr | ⟨u0, rfl, h0⟩
  · rcases hr with ⟨k, b0, b1, b2, heq, rfl⟩
    cases k with
    | r0 => exact cp_8_root_0 a0 a1 a2 b0 b1 b2 heq
    | r1 => exact cp_8_root_1 a0 a1 a2 b0 b1 b2 heq
    | r2 => exact cp_8_root_2 a0 a1 a2 b0 b1 b2 heq
    | r3 => exact cp_8_root_3 a0 a1 a2 b0 b1 b2 heq
    | r4 => exact cp_8_root_4 a0 a1 a2 b0 b1 b2 heq
    | r5 => exact cp_8_root_5 a0 a1 a2 b0 b1 b2 heq
    | r6 => exact cp_8_root_6 a0 a1 a2 b0 b1 b2 heq
    | r7 => exact cp_8_root_7 a0 a1 a2 b0 b1 b2 heq
    | r8 => exact cp_8_root_8 a0 a1 a2 b0 b1 b2 heq
    | r9 => exact cp_8_root_9 a0 a1 a2 b0 b1 b2 heq
  ·
    rcases step_op_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
    · rcases hr with ⟨k, b0, b1, b2, heq, rfl⟩
      cases k with
      | r0 => exact cp_8_1_0 a0 a1 a2 b0 b1 b2 heq
      | r1 => exact cp_8_1_1 a0 a1 a2 b0 b1 b2 heq
      | r2 => exact cp_8_1_2 a0 a1 a2 b0 b1 b2 heq
      | r3 => exact cp_8_1_3 a0 a1 a2 b0 b1 b2 heq
      | r4 => exact cp_8_1_4 a0 a1 a2 b0 b1 b2 heq
      | r5 => exact cp_8_1_5 a0 a1 a2 b0 b1 b2 heq
      | r6 => exact cp_8_1_6 a0 a1 a2 b0 b1 b2 heq
      | r7 => exact cp_8_1_7 a0 a1 a2 b0 b1 b2 heq
      | r8 => exact cp_8_1_8 a0 a1 a2 b0 b1 b2 heq
      | r9 => exact cp_8_1_9 a0 a1 a2 b0 b1 b2 heq
    ·
      rcases step_sq_cases h1 with hr | ⟨u2, rfl, h2⟩
      · rcases hr with ⟨k, b0, b1, b2, heq, rfl⟩
        cases k with
        | r0 => exact cp_8_11_0 a0 a1 a2 b0 b1 b2 heq
        | r1 => exact cp_8_11_1 a0 a1 a2 b0 b1 b2 heq
        | r2 => exact cp_8_11_2 a0 a1 a2 b0 b1 b2 heq
        | r3 => exact cp_8_11_3 a0 a1 a2 b0 b1 b2 heq
        | r4 => exact cp_8_11_4 a0 a1 a2 b0 b1 b2 heq
        | r5 => exact cp_8_11_5 a0 a1 a2 b0 b1 b2 heq
        | r6 => exact cp_8_11_6 a0 a1 a2 b0 b1 b2 heq
        | r7 => exact cp_8_11_7 a0 a1 a2 b0 b1 b2 heq
        | r8 => exact cp_8_11_8 a0 a1 a2 b0 b1 b2 heq
        | r9 => exact cp_8_11_9 a0 a1 a2 b0 b1 b2 heq
      ·
        exact vp_8_111 a0 a1 a2 u2 h2
    ·
      rcases step_sq_cases h1 with hr | ⟨u2, rfl, h2⟩
      · rcases hr with ⟨k, b0, b1, b2, heq, rfl⟩
        cases k with
        | r0 => exact cp_8_12_0 a0 a1 a2 b0 b1 b2 heq
        | r1 => exact cp_8_12_1 a0 a1 a2 b0 b1 b2 heq
        | r2 => exact cp_8_12_2 a0 a1 a2 b0 b1 b2 heq
        | r3 => exact cp_8_12_3 a0 a1 a2 b0 b1 b2 heq
        | r4 => exact cp_8_12_4 a0 a1 a2 b0 b1 b2 heq
        | r5 => exact cp_8_12_5 a0 a1 a2 b0 b1 b2 heq
        | r6 => exact cp_8_12_6 a0 a1 a2 b0 b1 b2 heq
        | r7 => exact cp_8_12_7 a0 a1 a2 b0 b1 b2 heq
        | r8 => exact cp_8_12_8 a0 a1 a2 b0 b1 b2 heq
        | r9 => exact cp_8_12_9 a0 a1 a2 b0 b1 b2 heq
      ·
        exact vp_8_121 a0 a1 a2 u2 h2

theorem peak_9 (a0 a1 a2 : T) {u : T} (h : Step (op (sq a0) (op (sq a1) (sq a0))) u) :
    Join (op (sq a0) (sq (sq a1))) u := by
  rcases step_op_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
  · rcases hr with ⟨k, b0, b1, b2, heq, rfl⟩
    cases k with
    | r0 => exact cp_9_root_0 a0 a1 a2 b0 b1 b2 heq
    | r1 => exact cp_9_root_1 a0 a1 a2 b0 b1 b2 heq
    | r2 => exact cp_9_root_2 a0 a1 a2 b0 b1 b2 heq
    | r3 => exact cp_9_root_3 a0 a1 a2 b0 b1 b2 heq
    | r4 => exact cp_9_root_4 a0 a1 a2 b0 b1 b2 heq
    | r5 => exact cp_9_root_5 a0 a1 a2 b0 b1 b2 heq
    | r6 => exact cp_9_root_6 a0 a1 a2 b0 b1 b2 heq
    | r7 => exact cp_9_root_7 a0 a1 a2 b0 b1 b2 heq
    | r8 => exact cp_9_root_8 a0 a1 a2 b0 b1 b2 heq
    | r9 => exact cp_9_root_9 a0 a1 a2 b0 b1 b2 heq
  ·
    rcases step_sq_cases h0 with hr | ⟨u1, rfl, h1⟩
    · rcases hr with ⟨k, b0, b1, b2, heq, rfl⟩
      cases k with
      | r0 => exact cp_9_1_0 a0 a1 a2 b0 b1 b2 heq
      | r1 => exact cp_9_1_1 a0 a1 a2 b0 b1 b2 heq
      | r2 => exact cp_9_1_2 a0 a1 a2 b0 b1 b2 heq
      | r3 => exact cp_9_1_3 a0 a1 a2 b0 b1 b2 heq
      | r4 => exact cp_9_1_4 a0 a1 a2 b0 b1 b2 heq
      | r5 => exact cp_9_1_5 a0 a1 a2 b0 b1 b2 heq
      | r6 => exact cp_9_1_6 a0 a1 a2 b0 b1 b2 heq
      | r7 => exact cp_9_1_7 a0 a1 a2 b0 b1 b2 heq
      | r8 => exact cp_9_1_8 a0 a1 a2 b0 b1 b2 heq
      | r9 => exact cp_9_1_9 a0 a1 a2 b0 b1 b2 heq
    ·
      exact vp_9_11 a0 a1 a2 u1 h1
  ·
    rcases step_op_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
    · rcases hr with ⟨k, b0, b1, b2, heq, rfl⟩
      cases k with
      | r0 => exact cp_9_2_0 a0 a1 a2 b0 b1 b2 heq
      | r1 => exact cp_9_2_1 a0 a1 a2 b0 b1 b2 heq
      | r2 => exact cp_9_2_2 a0 a1 a2 b0 b1 b2 heq
      | r3 => exact cp_9_2_3 a0 a1 a2 b0 b1 b2 heq
      | r4 => exact cp_9_2_4 a0 a1 a2 b0 b1 b2 heq
      | r5 => exact cp_9_2_5 a0 a1 a2 b0 b1 b2 heq
      | r6 => exact cp_9_2_6 a0 a1 a2 b0 b1 b2 heq
      | r7 => exact cp_9_2_7 a0 a1 a2 b0 b1 b2 heq
      | r8 => exact cp_9_2_8 a0 a1 a2 b0 b1 b2 heq
      | r9 => exact cp_9_2_9 a0 a1 a2 b0 b1 b2 heq
    ·
      rcases step_sq_cases h1 with hr | ⟨u2, rfl, h2⟩
      · rcases hr with ⟨k, b0, b1, b2, heq, rfl⟩
        cases k with
        | r0 => exact cp_9_21_0 a0 a1 a2 b0 b1 b2 heq
        | r1 => exact cp_9_21_1 a0 a1 a2 b0 b1 b2 heq
        | r2 => exact cp_9_21_2 a0 a1 a2 b0 b1 b2 heq
        | r3 => exact cp_9_21_3 a0 a1 a2 b0 b1 b2 heq
        | r4 => exact cp_9_21_4 a0 a1 a2 b0 b1 b2 heq
        | r5 => exact cp_9_21_5 a0 a1 a2 b0 b1 b2 heq
        | r6 => exact cp_9_21_6 a0 a1 a2 b0 b1 b2 heq
        | r7 => exact cp_9_21_7 a0 a1 a2 b0 b1 b2 heq
        | r8 => exact cp_9_21_8 a0 a1 a2 b0 b1 b2 heq
        | r9 => exact cp_9_21_9 a0 a1 a2 b0 b1 b2 heq
      ·
        exact vp_9_211 a0 a1 a2 u2 h2
    ·
      rcases step_sq_cases h1 with hr | ⟨u2, rfl, h2⟩
      · rcases hr with ⟨k, b0, b1, b2, heq, rfl⟩
        cases k with
        | r0 => exact cp_9_22_0 a0 a1 a2 b0 b1 b2 heq
        | r1 => exact cp_9_22_1 a0 a1 a2 b0 b1 b2 heq
        | r2 => exact cp_9_22_2 a0 a1 a2 b0 b1 b2 heq
        | r3 => exact cp_9_22_3 a0 a1 a2 b0 b1 b2 heq
        | r4 => exact cp_9_22_4 a0 a1 a2 b0 b1 b2 heq
        | r5 => exact cp_9_22_5 a0 a1 a2 b0 b1 b2 heq
        | r6 => exact cp_9_22_6 a0 a1 a2 b0 b1 b2 heq
        | r7 => exact cp_9_22_7 a0 a1 a2 b0 b1 b2 heq
        | r8 => exact cp_9_22_8 a0 a1 a2 b0 b1 b2 heq
        | r9 => exact cp_9_22_9 a0 a1 a2 b0 b1 b2 heq
      ·
        exact vp_9_221 a0 a1 a2 u2 h2

theorem root_peak {a b c : T} (h : Root a b) (hs : Step a c) : Join b c := by
  rcases h with ⟨k, x, y, z, rfl, rfl⟩
  cases k with
  | r0 => exact peak_0 x y z hs
  | r1 => exact peak_1 x y z hs
  | r2 => exact peak_2 x y z hs
  | r3 => exact peak_3 x y z hs
  | r4 => exact peak_4 x y z hs
  | r5 => exact peak_5 x y z hs
  | r6 => exact peak_6 x y z hs
  | r7 => exact peak_7 x y z hs
  | r8 => exact peak_8 x y z hs
  | r9 => exact peak_9 x y z hs

end submission


set_option autoImplicit false
namespace submission
open T

theorem local_confluence {a b c : T} (h : Step a b) (hs : Step a c) : Join b c := by
  induction h generalizing c with
  | root h => exact root_peak h hs
  | @sq a b h ih =>
    rcases step_sq_cases hs with hr | ⟨v, rfl, hv⟩
    · exact join_symm (root_peak hr (.sq h))
    · exact join_sq (ih hv)
  | @left a b d h ih =>
    rcases step_op_cases hs with hr | ⟨v, rfl, hv⟩ | ⟨v, rfl, hv⟩
    · exact join_symm (root_peak hr (.left d h))
    · exact join_left d (ih hv)
    · exact ⟨op b v, .single (.right b hv), .single (.left v h)⟩
  | @right a b d h ih =>
    rcases step_op_cases hs with hr | ⟨v, rfl, hv⟩ | ⟨v, rfl, hv⟩
    · exact join_symm (root_peak hr (.right d h))
    · exact ⟨op v b, .single (.left b hv), .single (.right v h)⟩
    · exact join_right d (ih hv)

theorem confluence (a : T) : ∀ {b c : T}, Reach a b → Reach a c → Join b c := by
  induction a using (measure sz).wf.induction with
  | h a ih =>
    intro b c hab hac
    rcases hab.cases_head with rfl | ⟨p, hap, hpb⟩
    · exact ⟨c, hac, .refl⟩
    rcases hac.cases_head with rfl | ⟨q, haq, hqc⟩
    · exact ⟨b, .refl, hab⟩
    rcases local_confluence hap haq with ⟨d, hpd, hqd⟩
    rcases ih p (step_decrease hap) hpb hpd with ⟨e, hbe, hde⟩
    rcases ih q (step_decrease haq) hqc hqd with ⟨f, hcf, hdf⟩
    have hd : sz d < sz a := Nat.lt_of_le_of_lt (reach_size hpd) (step_decrease hap)
    rcases ih d hd hde hdf with ⟨g, heg, hfg⟩
    exact ⟨g, hbe.trans heg, hcf.trans hfg⟩

theorem join_equivalence : Equivalence Join := by
  refine ⟨fun a => ⟨a, .refl, .refl⟩, fun h => join_symm h, ?_⟩
  intro a b c hab hbc
  rcases hab with ⟨x, hax, hbx⟩
  rcases hbc with ⟨y, hby, hcy⟩
  rcases confluence b hbx hby with ⟨z, hxz, hyz⟩
  exact ⟨z, hax.trans hxz, hcy.trans hyz⟩

def treeSetoid : Setoid T := ⟨Join, join_equivalence⟩
def Carrier := Quotient treeSetoid
def project : T → Carrier := Quotient.mk treeSetoid

def product : Carrier → Carrier → Carrier :=
  Quotient.lift₂ (fun a b => project (op a b)) (by
    intro a b c d hac hbd
    apply Quotient.sound
    exact join_equivalence.trans (join_left b hac) (join_right c hbd))

instance : Magma Carrier := ⟨product⟩

theorem project_op (a b : T) : project (op a b) = project a ◇ project b := rfl

theorem project_reach {a b : T} (h : Reach a b) : project a = project b :=
  Quotient.sound ⟨b, h, .refl⟩

theorem source : ∀ x y z : Carrier, x = y ◇ ((x ◇ (y ◇ (z ◇ z))) ◇ y) := by
  intro x y z
  refine Quotient.inductionOn₃ x y z ?_
  intro a b c
  change project a = project (op b (op (op a (op b (op c c))) b))
  symm
  apply project_reach
  exact (Relation.ReflTransGen.single
    (Step.right b (Step.left b (Step.right a (Step.right b
      (root_step .r0 c (leaf 0) (leaf 0))))))).tail
    (root_step .r1 b a c)

theorem leaf_irreducible (n : Nat) {u : T} (h : Step (leaf n) u) : False := by
  have hd := step_decrease h
  have hu := sz_pos u
  simp only [sz] at hd
  omega

theorem leaf_reach (n : Nat) {u : T} (h : Reach (leaf n) u) : leaf n = u := by
  rcases h.cases_head with he | ⟨v, hv, _⟩
  · exact he
  · exact False.elim (leaf_irreducible n hv)

theorem generators_injective : Function.Injective (fun n => project (leaf n)) := by
  intro n m he
  rcases Quotient.exact he with ⟨u, hn, hm⟩
  exact T.leaf.inj ((leaf_reach n hn).trans (leaf_reach m hm).symm)

theorem nontrivial : ¬ ∀ x y : Carrier, x = y := by
  intro h
  have he : (0 : Nat) = 1 := generators_injective (h (project (leaf 0)) (project (leaf 1)))
  omega

theorem model : ∃ (G : Type) (_ : Magma G),
    (∀ x y z : G, x = y ◇ ((x ◇ (y ◇ (z ◇ z))) ◇ y)) ∧ ¬ (∀ x y : G, x = y) :=
  ⟨Carrier, inferInstance, source, nontrivial⟩

#print axioms model
#print axioms generators_injective
end submission

namespace submission
def oppositeMagma : Magma Carrier := ⟨fun a b => product b a⟩
theorem opposite_source : @EquationLHS Carrier oppositeMagma := by
  intro x y z
  change x = product y (product (product x (product y (product z z))) y)
  exact source x y z
theorem opposite_target : ¬ @EquationRHS Carrier oppositeMagma := nontrivial
def opposite_result : Goal := ⟨Carrier, oppositeMagma, opposite_source, opposite_target⟩
end submission
def submission : Goal := submission.opposite_result
#print axioms submission

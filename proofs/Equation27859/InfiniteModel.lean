import JudgeProblem
import Mathlib.Logic.Relation
import Lean
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 20000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
namespace submission
inductive T where
  | leaf : Nat → T
  | aux0 : T → T → T
  | aux1 : T → T → T
  | op : T → T → T
  | shared : T
open T
def sz : T → Nat
  | .leaf _ => 1
  | .aux0 x0 x1 => 1 * sz x0 + 1 * sz x1 + 1
  | .aux1 x0 x1 => 1 * sz x0 + 1 * sz x1 + 1
  | .op x0 x1 => 2 * sz x0 + 2 * sz x1 + 1
  | .shared  => 1
theorem sz_pos (a : T) : 0 < sz a := by
  cases a <;> simp only [sz] <;> omega
inductive Rule where
  | r0 | r1 | r2 | r3 | r4 | r5 | r6 | r7 | r8 | r9 | r10 | r11 | r12 | r13 | r14 | r15 | r16
def L : Rule → T → T → T → T
  | .r0, v0, v1, v2 => (op v0 v0)
  | .r1, v0, v1, v2 => (op (op v0 v1) v1)
  | .r2, v0, v1, v2 => (op (shared ) v0)
  | .r3, v0, v1, v2 => (op v0 (aux0 v0 v1))
  | .r4, v0, v1, v2 => (op (aux0 v0 v1) v1)
  | .r5, v0, v1, v2 => (aux0 (shared ) (shared ))
  | .r6, v0, v1, v2 => (aux1 (shared ) (shared ))
  | .r7, v0, v1, v2 => (aux0 (aux1 v0 v1) (aux1 v0 v1))
  | .r8, v0, v1, v2 => (op (aux1 v0 v1) (aux0 v0 v1))
  | .r9, v0, v1, v2 => (op (aux1 v0 v1) v0)
  | .r10, v0, v1, v2 => (op v0 (aux1 v0 v1))
  | .r11, v0, v1, v2 => (aux0 (shared ) (aux1 (shared ) v0))
  | .r12, v0, v1, v2 => (aux1 (shared ) (aux1 (shared ) v0))
  | .r13, v0, v1, v2 => (op (aux1 (aux1 v0 v1) (aux1 v0 v1)) v0)
  | .r14, v0, v1, v2 => (aux0 (aux0 (shared ) v0) (aux0 (shared ) v0))
  | .r15, v0, v1, v2 => (op (aux0 (shared ) v0) (aux1 (shared ) v0))
  | .r16, v0, v1, v2 => (op (aux1 (aux0 (shared ) v0) (aux0 (shared ) v0)) (aux1 (shared ) v0))
def R : Rule → T → T → T → T
  | .r0, v0, v1, v2 => (shared )
  | .r1, v0, v1, v2 => (aux0 v0 v1)
  | .r2, v0, v1, v2 => (aux0 v0 v0)
  | .r3, v0, v1, v2 => (aux1 v0 v1)
  | .r4, v0, v1, v2 => (aux0 (op v0 v1) v1)
  | .r5, v0, v1, v2 => (shared )
  | .r6, v0, v1, v2 => (shared )
  | .r7, v0, v1, v2 => v0
  | .r8, v0, v1, v2 => (aux0 v0 (aux0 v0 v1))
  | .r9, v0, v1, v2 => (aux1 (aux1 v0 v1) (aux1 v0 v1))
  | .r10, v0, v1, v2 => (aux0 (shared ) (aux1 v0 v1))
  | .r11, v0, v1, v2 => (shared )
  | .r12, v0, v1, v2 => (shared )
  | .r13, v0, v1, v2 => (aux0 (aux1 v0 v1) v0)
  | .r14, v0, v1, v2 => (aux1 (shared ) v0)
  | .r15, v0, v1, v2 => (aux1 (aux0 (shared ) v0) (aux0 (shared ) v0))
  | .r16, v0, v1, v2 => (aux0 (aux0 (shared ) v0) (aux1 (shared ) v0))
def Root (t u : T) : Prop :=
  ∃ k v0 v1 v2, t = L k v0 v1 v2 ∧ u = R k v0 v1 v2
inductive Step : T → T → Prop where
  | root {a b : T} : Root a b → Step a b
  | c_aux0_1 {a b : T} (x2 : T) : Step a b → Step (aux0 a x2) (aux0 b x2)
  | c_aux0_2 {a b : T} (x1 : T) : Step a b → Step (aux0 x1 a) (aux0 x1 b)
  | c_aux1_1 {a b : T} (x2 : T) : Step a b → Step (aux1 a x2) (aux1 b x2)
  | c_aux1_2 {a b : T} (x1 : T) : Step a b → Step (aux1 x1 a) (aux1 x1 b)
  | c_op_1 {a b : T} (x2 : T) : Step a b → Step (op a x2) (op b x2)
  | c_op_2 {a b : T} (x1 : T) : Step a b → Step (op x1 a) (op x1 b)
abbrev Reach := Relation.ReflTransGen Step
def Join (a b : T) : Prop := ∃ c, Reach a c ∧ Reach b c
theorem root_step (k : Rule) (v0 v1 v2 : T) : Step (L k v0 v1 v2) (R k v0 v1 v2) :=
  .root ⟨k, v0, v1, v2, rfl, rfl⟩
theorem root_decrease {a b : T} (h : Root a b) : sz b < sz a := by
  rcases h with ⟨k, v0, v1, v2, hl, hr⟩
  rw [hl, hr]
  have hp_v0 := sz_pos v0
  have hp_v1 := sz_pos v1
  have hp_v2 := sz_pos v2
  cases k <;> simp only [L, R, sz] <;> omega
theorem step_decrease {a b : T} (h : Step a b) : sz b < sz a := by
  induction h with
  | root h => exact root_decrease h
  | c_aux0_1 x2 h ih => simp only [sz]; omega
  | c_aux0_2 x1 h ih => simp only [sz]; omega
  | c_aux1_1 x2 h ih => simp only [sz]; omega
  | c_aux1_2 x1 h ih => simp only [sz]; omega
  | c_op_1 x2 h ih => simp only [sz]; omega
  | c_op_2 x1 h ih => simp only [sz]; omega
theorem reach_size {a b : T} (h : Reach a b) : sz b ≤ sz a := by
  induction h with
  | refl => exact Nat.le_refl _
  | tail h hs ih => have hd := step_decrease hs; omega
theorem join_symm {a b : T} (h : Join a b) : Join b a := by
  rcases h with ⟨c, h1, h2⟩
  exact ⟨c, h2, h1⟩
theorem reach_aux0_1 {a b : T} (x2 : T) (h : Reach a b) : Reach (aux0 a x2) (aux0 b x2) :=
  h.lift (fun a => (aux0 a x2)) (fun _ _ h => (Step.c_aux0_1 x2 h))
theorem join_aux0_1 {a b : T} (x2 : T) (h : Join a b) : Join (aux0 a x2) (aux0 b x2) := by
  rcases h with ⟨c, h1, h2⟩
  exact ⟨(aux0 c x2), reach_aux0_1 x2 h1, reach_aux0_1 x2 h2⟩
theorem reach_aux0_2 {a b : T} (x1 : T) (h : Reach a b) : Reach (aux0 x1 a) (aux0 x1 b) :=
  h.lift (fun a => (aux0 x1 a)) (fun _ _ h => (Step.c_aux0_2 x1 h))
theorem join_aux0_2 {a b : T} (x1 : T) (h : Join a b) : Join (aux0 x1 a) (aux0 x1 b) := by
  rcases h with ⟨c, h1, h2⟩
  exact ⟨(aux0 x1 c), reach_aux0_2 x1 h1, reach_aux0_2 x1 h2⟩
theorem step_aux0_cases {x1 x2 u : T} (h : Step (aux0 x1 x2) u) :
    Root (aux0 x1 x2) u ∨ (∃ v, u = (aux0 v x2) ∧ Step x1 v) ∨ (∃ v, u = (aux0 x1 v) ∧ Step x2 v) := by
  cases h with
  | root h => exact Or.inl h
  | c_aux0_1 _ h => exact (Or.inr (Or.inl ⟨_, rfl, h⟩))
  | c_aux0_2 _ h => exact (Or.inr (Or.inr ⟨_, rfl, h⟩))
theorem reach_aux1_1 {a b : T} (x2 : T) (h : Reach a b) : Reach (aux1 a x2) (aux1 b x2) :=
  h.lift (fun a => (aux1 a x2)) (fun _ _ h => (Step.c_aux1_1 x2 h))
theorem join_aux1_1 {a b : T} (x2 : T) (h : Join a b) : Join (aux1 a x2) (aux1 b x2) := by
  rcases h with ⟨c, h1, h2⟩
  exact ⟨(aux1 c x2), reach_aux1_1 x2 h1, reach_aux1_1 x2 h2⟩
theorem reach_aux1_2 {a b : T} (x1 : T) (h : Reach a b) : Reach (aux1 x1 a) (aux1 x1 b) :=
  h.lift (fun a => (aux1 x1 a)) (fun _ _ h => (Step.c_aux1_2 x1 h))
theorem join_aux1_2 {a b : T} (x1 : T) (h : Join a b) : Join (aux1 x1 a) (aux1 x1 b) := by
  rcases h with ⟨c, h1, h2⟩
  exact ⟨(aux1 x1 c), reach_aux1_2 x1 h1, reach_aux1_2 x1 h2⟩
theorem step_aux1_cases {x1 x2 u : T} (h : Step (aux1 x1 x2) u) :
    Root (aux1 x1 x2) u ∨ (∃ v, u = (aux1 v x2) ∧ Step x1 v) ∨ (∃ v, u = (aux1 x1 v) ∧ Step x2 v) := by
  cases h with
  | root h => exact Or.inl h
  | c_aux1_1 _ h => exact (Or.inr (Or.inl ⟨_, rfl, h⟩))
  | c_aux1_2 _ h => exact (Or.inr (Or.inr ⟨_, rfl, h⟩))
theorem reach_op_1 {a b : T} (x2 : T) (h : Reach a b) : Reach (op a x2) (op b x2) :=
  h.lift (fun a => (op a x2)) (fun _ _ h => (Step.c_op_1 x2 h))
theorem join_op_1 {a b : T} (x2 : T) (h : Join a b) : Join (op a x2) (op b x2) := by
  rcases h with ⟨c, h1, h2⟩
  exact ⟨(op c x2), reach_op_1 x2 h1, reach_op_1 x2 h2⟩
theorem reach_op_2 {a b : T} (x1 : T) (h : Reach a b) : Reach (op x1 a) (op x1 b) :=
  h.lift (fun a => (op x1 a)) (fun _ _ h => (Step.c_op_2 x1 h))
theorem join_op_2 {a b : T} (x1 : T) (h : Join a b) : Join (op x1 a) (op x1 b) := by
  rcases h with ⟨c, h1, h2⟩
  exact ⟨(op x1 c), reach_op_2 x1 h1, reach_op_2 x1 h2⟩
theorem step_op_cases {x1 x2 u : T} (h : Step (op x1 x2) u) :
    Root (op x1 x2) u ∨ (∃ v, u = (op v x2) ∧ Step x1 v) ∨ (∃ v, u = (op x1 v) ∧ Step x2 v) := by
  cases h with
  | root h => exact Or.inl h
  | c_op_1 _ h => exact (Or.inr (Or.inl ⟨_, rfl, h⟩))
  | c_op_2 _ h => exact (Or.inr (Or.inr ⟨_, rfl, h⟩))
theorem step_shared_cases { u : T} (h : Step (shared ) u) :
    Root (shared ) u := by
  cases h with
  | root h => exact h
theorem cp_0_root_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 a0) = (op b0 b0)) :
    Join (shared ) (shared ) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  clear he0
  exact ⟨(shared ), (Relation.ReflTransGen.refl), (Relation.ReflTransGen.refl)⟩
theorem cp_0_root_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 a0) = (op (op b0 b1) b1)) :
    Join (shared ) (aux0 b0 b1) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  have hsize := congrArg sz he0
  have hp_b0 := sz_pos b0
  have hp_b1 := sz_pos b1
  simp only [sz] at hsize
  omega
theorem cp_0_root_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 a0) = (op (shared ) b0)) :
    Join (shared ) (aux0 b0 b0) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  subst b0
  exact ⟨(shared ), (Relation.ReflTransGen.refl), ((Relation.ReflTransGen.refl).tail (root_step .r5 (leaf 0) (leaf 0) (leaf 0)))⟩
theorem cp_0_root_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 a0) = (op b0 (aux0 b0 b1))) :
    Join (shared ) (aux1 b0 b1) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  have hsize := congrArg sz he0
  have hp_b0 := sz_pos b0
  have hp_b1 := sz_pos b1
  simp only [sz] at hsize
  omega
theorem cp_0_root_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 a0) = (op (aux0 b0 b1) b1)) :
    Join (shared ) (aux0 (op b0 b1) b1) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  have hsize := congrArg sz he0
  have hp_b0 := sz_pos b0
  have hp_b1 := sz_pos b1
  simp only [sz] at hsize
  omega
theorem cp_0_root_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 a0) = (aux0 (shared ) (shared ))) :
    Join (shared ) (shared ) := by
  cases heq
theorem cp_0_root_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 a0) = (aux1 (shared ) (shared ))) :
    Join (shared ) (shared ) := by
  cases heq
theorem cp_0_root_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 a0) = (aux0 (aux1 b0 b1) (aux1 b0 b1))) :
    Join (shared ) b0 := by
  cases heq
theorem cp_0_root_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 a0) = (op (aux1 b0 b1) (aux0 b0 b1))) :
    Join (shared ) (aux0 b0 (aux0 b0 b1)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  cases he0
theorem cp_0_root_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 a0) = (op (aux1 b0 b1) b0)) :
    Join (shared ) (aux1 (aux1 b0 b1) (aux1 b0 b1)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  have hsize := congrArg sz he0
  have hp_b0 := sz_pos b0
  have hp_b1 := sz_pos b1
  simp only [sz] at hsize
  omega
theorem cp_0_root_10 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 a0) = (op b0 (aux1 b0 b1))) :
    Join (shared ) (aux0 (shared ) (aux1 b0 b1)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  have hsize := congrArg sz he0
  have hp_b0 := sz_pos b0
  have hp_b1 := sz_pos b1
  simp only [sz] at hsize
  omega
theorem cp_0_root_11 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 a0) = (aux0 (shared ) (aux1 (shared ) b0))) :
    Join (shared ) (shared ) := by
  cases heq
theorem cp_0_root_12 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 a0) = (aux1 (shared ) (aux1 (shared ) b0))) :
    Join (shared ) (shared ) := by
  cases heq
theorem cp_0_root_13 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 a0) = (op (aux1 (aux1 b0 b1) (aux1 b0 b1)) b0)) :
    Join (shared ) (aux0 (aux1 b0 b1) b0) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  have hsize := congrArg sz he0
  have hp_b0 := sz_pos b0
  have hp_b1 := sz_pos b1
  simp only [sz] at hsize
  omega
theorem cp_0_root_14 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 a0) = (aux0 (aux0 (shared ) b0) (aux0 (shared ) b0))) :
    Join (shared ) (aux1 (shared ) b0) := by
  cases heq
theorem cp_0_root_15 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 a0) = (op (aux0 (shared ) b0) (aux1 (shared ) b0))) :
    Join (shared ) (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  cases he0
theorem cp_0_root_16 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 a0) = (op (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) (aux1 (shared ) b0))) :
    Join (shared ) (aux0 (aux0 (shared ) b0) (aux1 (shared ) b0)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  rcases T.aux1.inj he0 with ⟨he2, he3⟩
  clear he0
  have hsize := congrArg sz he3
  have hp_b0 := sz_pos b0
  simp only [sz] at hsize
  omega
theorem cp_1_root_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (op a0 a1) a1) = (op b0 b0)) :
    Join (aux0 a0 a1) (shared ) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  have hsize := congrArg sz he0
  have hp_a0 := sz_pos a0
  have hp_b0 := sz_pos b0
  simp only [sz] at hsize
  omega
theorem cp_1_1_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 a1) = (op b0 b0)) :
    Join (aux0 a0 a1) (op (shared ) a1) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  subst a0
  exact ⟨(aux0 b0 b0), (Relation.ReflTransGen.refl), ((Relation.ReflTransGen.refl).tail (root_step .r2 b0 (leaf 0) (leaf 0)))⟩
theorem cp_1_root_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (op a0 a1) a1) = (op (op b0 b1) b1)) :
    Join (aux0 a0 a1) (aux0 b0 b1) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  rcases T.op.inj he0 with ⟨he2, he3⟩
  clear he0
  clear he3
  subst a0
  exact ⟨(aux0 b0 b1), (Relation.ReflTransGen.refl), (Relation.ReflTransGen.refl)⟩
theorem cp_1_1_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 a1) = (op (op b0 b1) b1)) :
    Join (aux0 a0 a1) (op (aux0 b0 b1) a1) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  subst a0
  exact ⟨(aux0 (op b0 b1) b1), (Relation.ReflTransGen.refl), ((Relation.ReflTransGen.refl).tail (root_step .r4 b0 b1 (leaf 0)))⟩
theorem cp_1_root_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (op a0 a1) a1) = (op (shared ) b0)) :
    Join (aux0 a0 a1) (aux0 b0 b0) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  cases he0
theorem cp_1_1_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 a1) = (op (shared ) b0)) :
    Join (aux0 a0 a1) (op (aux0 b0 b0) a1) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  subst a0
  exact ⟨(aux0 (shared ) b0), (Relation.ReflTransGen.refl), (((Relation.ReflTransGen.refl).tail (root_step .r4 b0 b0 (leaf 0))).tail (Step.c_aux0_1 b0 (root_step .r0 b0 (leaf 0) (leaf 0))))⟩
theorem cp_1_root_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (op a0 a1) a1) = (op b0 (aux0 b0 b1))) :
    Join (aux0 a0 a1) (aux1 b0 b1) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  have hsize := congrArg sz he0
  have hp_a0 := sz_pos a0
  have hp_b0 := sz_pos b0
  have hp_b1 := sz_pos b1
  simp only [sz] at hsize
  omega
theorem cp_1_1_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 a1) = (op b0 (aux0 b0 b1))) :
    Join (aux0 a0 a1) (op (aux1 b0 b1) a1) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  subst a0
  exact ⟨(aux0 b0 (aux0 b0 b1)), (Relation.ReflTransGen.refl), ((Relation.ReflTransGen.refl).tail (root_step .r8 b0 b1 (leaf 0)))⟩
theorem cp_1_root_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (op a0 a1) a1) = (op (aux0 b0 b1) b1)) :
    Join (aux0 a0 a1) (aux0 (op b0 b1) b1) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  cases he0
theorem cp_1_1_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 a1) = (op (aux0 b0 b1) b1)) :
    Join (aux0 a0 a1) (op (aux0 (op b0 b1) b1) a1) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  subst a0
  exact ⟨(aux0 (aux0 b0 b1) b1), (Relation.ReflTransGen.refl), (((Relation.ReflTransGen.refl).tail (root_step .r4 (op b0 b1) b1 (leaf 0))).tail (Step.c_aux0_1 b1 (root_step .r1 b0 b1 (leaf 0))))⟩
theorem cp_1_root_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (op a0 a1) a1) = (aux0 (shared ) (shared ))) :
    Join (aux0 a0 a1) (shared ) := by
  cases heq
theorem cp_1_1_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 a1) = (aux0 (shared ) (shared ))) :
    Join (aux0 a0 a1) (op (shared ) a1) := by
  cases heq
theorem cp_1_root_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (op a0 a1) a1) = (aux1 (shared ) (shared ))) :
    Join (aux0 a0 a1) (shared ) := by
  cases heq
theorem cp_1_1_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 a1) = (aux1 (shared ) (shared ))) :
    Join (aux0 a0 a1) (op (shared ) a1) := by
  cases heq
theorem cp_1_root_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (op a0 a1) a1) = (aux0 (aux1 b0 b1) (aux1 b0 b1))) :
    Join (aux0 a0 a1) b0 := by
  cases heq
theorem cp_1_1_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 a1) = (aux0 (aux1 b0 b1) (aux1 b0 b1))) :
    Join (aux0 a0 a1) (op b0 a1) := by
  cases heq
theorem cp_1_root_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (op a0 a1) a1) = (op (aux1 b0 b1) (aux0 b0 b1))) :
    Join (aux0 a0 a1) (aux0 b0 (aux0 b0 b1)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  cases he0
theorem cp_1_1_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 a1) = (op (aux1 b0 b1) (aux0 b0 b1))) :
    Join (aux0 a0 a1) (op (aux0 b0 (aux0 b0 b1)) a1) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  subst a0
  exact ⟨(aux0 (aux1 b0 b1) (aux0 b0 b1)), (Relation.ReflTransGen.refl), (((Relation.ReflTransGen.refl).tail (root_step .r4 b0 (aux0 b0 b1) (leaf 0))).tail (Step.c_aux0_1 (aux0 b0 b1) (root_step .r3 b0 b1 (leaf 0))))⟩
theorem cp_1_root_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (op a0 a1) a1) = (op (aux1 b0 b1) b0)) :
    Join (aux0 a0 a1) (aux1 (aux1 b0 b1) (aux1 b0 b1)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  cases he0
theorem cp_1_1_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 a1) = (op (aux1 b0 b1) b0)) :
    Join (aux0 a0 a1) (op (aux1 (aux1 b0 b1) (aux1 b0 b1)) a1) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  subst a0
  exact ⟨(aux0 (aux1 b0 b1) b0), (Relation.ReflTransGen.refl), ((Relation.ReflTransGen.refl).tail (root_step .r13 b0 b1 (leaf 0)))⟩
theorem cp_1_root_10 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (op a0 a1) a1) = (op b0 (aux1 b0 b1))) :
    Join (aux0 a0 a1) (aux0 (shared ) (aux1 b0 b1)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  have hsize := congrArg sz he0
  have hp_a0 := sz_pos a0
  have hp_b0 := sz_pos b0
  have hp_b1 := sz_pos b1
  simp only [sz] at hsize
  omega
theorem cp_1_1_10 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 a1) = (op b0 (aux1 b0 b1))) :
    Join (aux0 a0 a1) (op (aux0 (shared ) (aux1 b0 b1)) a1) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  subst a0
  exact ⟨(aux0 b0 (aux1 b0 b1)), (Relation.ReflTransGen.refl), ((((Relation.ReflTransGen.refl).tail (root_step .r4 (shared ) (aux1 b0 b1) (leaf 0))).tail (Step.c_aux0_1 (aux1 b0 b1) (root_step .r2 (aux1 b0 b1) (leaf 0) (leaf 0)))).tail (Step.c_aux0_1 (aux1 b0 b1) (root_step .r7 b0 b1 (leaf 0))))⟩
theorem cp_1_root_11 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (op a0 a1) a1) = (aux0 (shared ) (aux1 (shared ) b0))) :
    Join (aux0 a0 a1) (shared ) := by
  cases heq
theorem cp_1_1_11 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 a1) = (aux0 (shared ) (aux1 (shared ) b0))) :
    Join (aux0 a0 a1) (op (shared ) a1) := by
  cases heq
theorem cp_1_root_12 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (op a0 a1) a1) = (aux1 (shared ) (aux1 (shared ) b0))) :
    Join (aux0 a0 a1) (shared ) := by
  cases heq
theorem cp_1_1_12 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 a1) = (aux1 (shared ) (aux1 (shared ) b0))) :
    Join (aux0 a0 a1) (op (shared ) a1) := by
  cases heq
theorem cp_1_root_13 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (op a0 a1) a1) = (op (aux1 (aux1 b0 b1) (aux1 b0 b1)) b0)) :
    Join (aux0 a0 a1) (aux0 (aux1 b0 b1) b0) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  cases he0
theorem cp_1_1_13 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 a1) = (op (aux1 (aux1 b0 b1) (aux1 b0 b1)) b0)) :
    Join (aux0 a0 a1) (op (aux0 (aux1 b0 b1) b0) a1) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  subst a0
  exact ⟨(aux0 (aux1 (aux1 b0 b1) (aux1 b0 b1)) b0), (Relation.ReflTransGen.refl), (((Relation.ReflTransGen.refl).tail (root_step .r4 (aux1 b0 b1) b0 (leaf 0))).tail (Step.c_aux0_1 b0 (root_step .r9 b0 b1 (leaf 0))))⟩
theorem cp_1_root_14 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (op a0 a1) a1) = (aux0 (aux0 (shared ) b0) (aux0 (shared ) b0))) :
    Join (aux0 a0 a1) (aux1 (shared ) b0) := by
  cases heq
theorem cp_1_1_14 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 a1) = (aux0 (aux0 (shared ) b0) (aux0 (shared ) b0))) :
    Join (aux0 a0 a1) (op (aux1 (shared ) b0) a1) := by
  cases heq
theorem cp_1_root_15 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (op a0 a1) a1) = (op (aux0 (shared ) b0) (aux1 (shared ) b0))) :
    Join (aux0 a0 a1) (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  cases he0
theorem cp_1_1_15 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 a1) = (op (aux0 (shared ) b0) (aux1 (shared ) b0))) :
    Join (aux0 a0 a1) (op (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) a1) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  subst a0
  exact ⟨(aux0 (aux0 (shared ) b0) (aux1 (shared ) b0)), (Relation.ReflTransGen.refl), ((Relation.ReflTransGen.refl).tail (root_step .r16 b0 (leaf 0) (leaf 0)))⟩
theorem cp_1_root_16 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (op a0 a1) a1) = (op (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) (aux1 (shared ) b0))) :
    Join (aux0 a0 a1) (aux0 (aux0 (shared ) b0) (aux1 (shared ) b0)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  cases he0
theorem cp_1_1_16 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 a1) = (op (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) (aux1 (shared ) b0))) :
    Join (aux0 a0 a1) (op (aux0 (aux0 (shared ) b0) (aux1 (shared ) b0)) a1) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  subst a0
  exact ⟨(aux0 (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) (aux1 (shared ) b0)), (Relation.ReflTransGen.refl), (((Relation.ReflTransGen.refl).tail (root_step .r4 (aux0 (shared ) b0) (aux1 (shared ) b0) (leaf 0))).tail (Step.c_aux0_1 (aux1 (shared ) b0) (root_step .r15 b0 (leaf 0) (leaf 0))))⟩
theorem cp_2_root_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (shared ) a0) = (op b0 b0)) :
    Join (aux0 a0 a0) (shared ) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  subst b0
  exact ⟨(shared ), ((Relation.ReflTransGen.refl).tail (root_step .r5 (leaf 0) (leaf 0) (leaf 0))), (Relation.ReflTransGen.refl)⟩
theorem cp_2_1_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op b0 b0)) :
    Join (aux0 a0 a0) (op (shared ) a0) := by
  cases heq
theorem cp_2_root_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (shared ) a0) = (op (op b0 b1) b1)) :
    Join (aux0 a0 a0) (aux0 b0 b1) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  cases he0
theorem cp_2_1_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (op b0 b1) b1)) :
    Join (aux0 a0 a0) (op (aux0 b0 b1) a0) := by
  cases heq
theorem cp_2_root_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (shared ) a0) = (op (shared ) b0)) :
    Join (aux0 a0 a0) (aux0 b0 b0) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  clear he0
  exact ⟨(aux0 b0 b0), (Relation.ReflTransGen.refl), (Relation.ReflTransGen.refl)⟩
theorem cp_2_1_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (shared ) b0)) :
    Join (aux0 a0 a0) (op (aux0 b0 b0) a0) := by
  cases heq
theorem cp_2_root_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (shared ) a0) = (op b0 (aux0 b0 b1))) :
    Join (aux0 a0 a0) (aux1 b0 b1) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  subst b0
  exact ⟨(aux1 (shared ) b1), ((Relation.ReflTransGen.refl).tail (root_step .r14 b1 (leaf 0) (leaf 0))), (Relation.ReflTransGen.refl)⟩
theorem cp_2_1_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op b0 (aux0 b0 b1))) :
    Join (aux0 a0 a0) (op (aux1 b0 b1) a0) := by
  cases heq
theorem cp_2_root_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (shared ) a0) = (op (aux0 b0 b1) b1)) :
    Join (aux0 a0 a0) (aux0 (op b0 b1) b1) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  cases he0
theorem cp_2_1_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux0 b0 b1) b1)) :
    Join (aux0 a0 a0) (op (aux0 (op b0 b1) b1) a0) := by
  cases heq
theorem cp_2_root_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (shared ) a0) = (aux0 (shared ) (shared ))) :
    Join (aux0 a0 a0) (shared ) := by
  cases heq
theorem cp_2_1_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux0 (shared ) (shared ))) :
    Join (aux0 a0 a0) (op (shared ) a0) := by
  cases heq
theorem cp_2_root_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (shared ) a0) = (aux1 (shared ) (shared ))) :
    Join (aux0 a0 a0) (shared ) := by
  cases heq
theorem cp_2_1_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux1 (shared ) (shared ))) :
    Join (aux0 a0 a0) (op (shared ) a0) := by
  cases heq
theorem cp_2_root_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (shared ) a0) = (aux0 (aux1 b0 b1) (aux1 b0 b1))) :
    Join (aux0 a0 a0) b0 := by
  cases heq
theorem cp_2_1_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux0 (aux1 b0 b1) (aux1 b0 b1))) :
    Join (aux0 a0 a0) (op b0 a0) := by
  cases heq
theorem cp_2_root_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (shared ) a0) = (op (aux1 b0 b1) (aux0 b0 b1))) :
    Join (aux0 a0 a0) (aux0 b0 (aux0 b0 b1)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  cases he0
theorem cp_2_1_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux1 b0 b1) (aux0 b0 b1))) :
    Join (aux0 a0 a0) (op (aux0 b0 (aux0 b0 b1)) a0) := by
  cases heq
theorem cp_2_root_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (shared ) a0) = (op (aux1 b0 b1) b0)) :
    Join (aux0 a0 a0) (aux1 (aux1 b0 b1) (aux1 b0 b1)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  cases he0
theorem cp_2_1_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux1 b0 b1) b0)) :
    Join (aux0 a0 a0) (op (aux1 (aux1 b0 b1) (aux1 b0 b1)) a0) := by
  cases heq
theorem cp_2_root_10 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (shared ) a0) = (op b0 (aux1 b0 b1))) :
    Join (aux0 a0 a0) (aux0 (shared ) (aux1 b0 b1)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  subst b0
  exact ⟨(shared ), ((Relation.ReflTransGen.refl).tail (root_step .r7 (shared ) b1 (leaf 0))), ((Relation.ReflTransGen.refl).tail (root_step .r11 b1 (leaf 0) (leaf 0)))⟩
theorem cp_2_1_10 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op b0 (aux1 b0 b1))) :
    Join (aux0 a0 a0) (op (aux0 (shared ) (aux1 b0 b1)) a0) := by
  cases heq
theorem cp_2_root_11 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (shared ) a0) = (aux0 (shared ) (aux1 (shared ) b0))) :
    Join (aux0 a0 a0) (shared ) := by
  cases heq
theorem cp_2_1_11 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux0 (shared ) (aux1 (shared ) b0))) :
    Join (aux0 a0 a0) (op (shared ) a0) := by
  cases heq
theorem cp_2_root_12 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (shared ) a0) = (aux1 (shared ) (aux1 (shared ) b0))) :
    Join (aux0 a0 a0) (shared ) := by
  cases heq
theorem cp_2_1_12 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux1 (shared ) (aux1 (shared ) b0))) :
    Join (aux0 a0 a0) (op (shared ) a0) := by
  cases heq
theorem cp_2_root_13 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (shared ) a0) = (op (aux1 (aux1 b0 b1) (aux1 b0 b1)) b0)) :
    Join (aux0 a0 a0) (aux0 (aux1 b0 b1) b0) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  cases he0
theorem cp_2_1_13 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux1 (aux1 b0 b1) (aux1 b0 b1)) b0)) :
    Join (aux0 a0 a0) (op (aux0 (aux1 b0 b1) b0) a0) := by
  cases heq
theorem cp_2_root_14 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (shared ) a0) = (aux0 (aux0 (shared ) b0) (aux0 (shared ) b0))) :
    Join (aux0 a0 a0) (aux1 (shared ) b0) := by
  cases heq
theorem cp_2_1_14 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux0 (aux0 (shared ) b0) (aux0 (shared ) b0))) :
    Join (aux0 a0 a0) (op (aux1 (shared ) b0) a0) := by
  cases heq
theorem cp_2_root_15 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (shared ) a0) = (op (aux0 (shared ) b0) (aux1 (shared ) b0))) :
    Join (aux0 a0 a0) (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  cases he0
theorem cp_2_1_15 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux0 (shared ) b0) (aux1 (shared ) b0))) :
    Join (aux0 a0 a0) (op (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) a0) := by
  cases heq
theorem cp_2_root_16 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (shared ) a0) = (op (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) (aux1 (shared ) b0))) :
    Join (aux0 a0 a0) (aux0 (aux0 (shared ) b0) (aux1 (shared ) b0)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  cases he0
theorem cp_2_1_16 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) (aux1 (shared ) b0))) :
    Join (aux0 a0 a0) (op (aux0 (aux0 (shared ) b0) (aux1 (shared ) b0)) a0) := by
  cases heq
theorem cp_3_root_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (aux0 a0 a1)) = (op b0 b0)) :
    Join (aux1 a0 a1) (shared ) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst b0
  intro he0
  have hsize := congrArg sz he0
  have hp_a0 := sz_pos a0
  have hp_a1 := sz_pos a1
  simp only [sz] at hsize
  omega
theorem cp_3_2_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 a0 a1) = (op b0 b0)) :
    Join (aux1 a0 a1) (op a0 (shared )) := by
  cases heq
theorem cp_3_root_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (aux0 a0 a1)) = (op (op b0 b1) b1)) :
    Join (aux1 a0 a1) (aux0 b0 b1) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst b1
  intro he0
  have hsize := congrArg sz he0
  have hp_a0 := sz_pos a0
  have hp_a1 := sz_pos a1
  have hp_b0 := sz_pos b0
  simp only [sz] at hsize
  omega
theorem cp_3_2_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 a0 a1) = (op (op b0 b1) b1)) :
    Join (aux1 a0 a1) (op a0 (aux0 b0 b1)) := by
  cases heq
theorem cp_3_root_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (aux0 a0 a1)) = (op (shared ) b0)) :
    Join (aux1 a0 a1) (aux0 b0 b0) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst b0
  intro he0
  subst a0
  exact ⟨(aux1 (shared ) a1), (Relation.ReflTransGen.refl), ((Relation.ReflTransGen.refl).tail (root_step .r14 a1 (leaf 0) (leaf 0)))⟩
theorem cp_3_2_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 a0 a1) = (op (shared ) b0)) :
    Join (aux1 a0 a1) (op a0 (aux0 b0 b0)) := by
  cases heq
theorem cp_3_root_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (aux0 a0 a1)) = (op b0 (aux0 b0 b1))) :
    Join (aux1 a0 a1) (aux1 b0 b1) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  rcases T.aux0.inj he1 with ⟨he2, he3⟩
  clear he1
  revert he0 he2
  subst a1
  intro he0 he2
  revert he0
  subst a0
  intro he0
  clear he0
  exact ⟨(aux1 b0 b1), (Relation.ReflTransGen.refl), (Relation.ReflTransGen.refl)⟩
theorem cp_3_2_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 a0 a1) = (op b0 (aux0 b0 b1))) :
    Join (aux1 a0 a1) (op a0 (aux1 b0 b1)) := by
  cases heq
theorem cp_3_root_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (aux0 a0 a1)) = (op (aux0 b0 b1) b1)) :
    Join (aux1 a0 a1) (aux0 (op b0 b1) b1) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst b1
  intro he0
  have hsize := congrArg sz he0
  have hp_a0 := sz_pos a0
  have hp_a1 := sz_pos a1
  have hp_b0 := sz_pos b0
  simp only [sz] at hsize
  omega
theorem cp_3_2_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 a0 a1) = (op (aux0 b0 b1) b1)) :
    Join (aux1 a0 a1) (op a0 (aux0 (op b0 b1) b1)) := by
  cases heq
theorem cp_3_root_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (aux0 a0 a1)) = (aux0 (shared ) (shared ))) :
    Join (aux1 a0 a1) (shared ) := by
  cases heq
theorem cp_3_2_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 a0 a1) = (aux0 (shared ) (shared ))) :
    Join (aux1 a0 a1) (op a0 (shared )) := by
  rcases T.aux0.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  subst a0
  exact ⟨(shared ), ((Relation.ReflTransGen.refl).tail (root_step .r6 (leaf 0) (leaf 0) (leaf 0))), ((Relation.ReflTransGen.refl).tail (root_step .r0 (shared ) (leaf 0) (leaf 0)))⟩
theorem cp_3_root_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (aux0 a0 a1)) = (aux1 (shared ) (shared ))) :
    Join (aux1 a0 a1) (shared ) := by
  cases heq
theorem cp_3_2_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 a0 a1) = (aux1 (shared ) (shared ))) :
    Join (aux1 a0 a1) (op a0 (shared )) := by
  cases heq
theorem cp_3_root_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (aux0 a0 a1)) = (aux0 (aux1 b0 b1) (aux1 b0 b1))) :
    Join (aux1 a0 a1) b0 := by
  cases heq
theorem cp_3_2_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 a0 a1) = (aux0 (aux1 b0 b1) (aux1 b0 b1))) :
    Join (aux1 a0 a1) (op a0 b0) := by
  rcases T.aux0.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  subst a0
  exact ⟨(aux1 (aux1 b0 b1) (aux1 b0 b1)), (Relation.ReflTransGen.refl), ((Relation.ReflTransGen.refl).tail (root_step .r9 b0 b1 (leaf 0)))⟩
theorem cp_3_root_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (aux0 a0 a1)) = (op (aux1 b0 b1) (aux0 b0 b1))) :
    Join (aux1 a0 a1) (aux0 b0 (aux0 b0 b1)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  rcases T.aux0.inj he1 with ⟨he2, he3⟩
  clear he1
  revert he0 he2
  subst a1
  intro he0 he2
  revert he0
  subst a0
  intro he0
  have hsize := congrArg sz he0
  have hp_b0 := sz_pos b0
  have hp_b1 := sz_pos b1
  simp only [sz] at hsize
  omega
theorem cp_3_2_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 a0 a1) = (op (aux1 b0 b1) (aux0 b0 b1))) :
    Join (aux1 a0 a1) (op a0 (aux0 b0 (aux0 b0 b1))) := by
  cases heq
theorem cp_3_root_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (aux0 a0 a1)) = (op (aux1 b0 b1) b0)) :
    Join (aux1 a0 a1) (aux1 (aux1 b0 b1) (aux1 b0 b1)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst b0
  intro he0
  have hsize := congrArg sz he0
  have hp_a0 := sz_pos a0
  have hp_a1 := sz_pos a1
  have hp_b1 := sz_pos b1
  simp only [sz] at hsize
  omega
theorem cp_3_2_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 a0 a1) = (op (aux1 b0 b1) b0)) :
    Join (aux1 a0 a1) (op a0 (aux1 (aux1 b0 b1) (aux1 b0 b1))) := by
  cases heq
theorem cp_3_root_10 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (aux0 a0 a1)) = (op b0 (aux1 b0 b1))) :
    Join (aux1 a0 a1) (aux0 (shared ) (aux1 b0 b1)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  cases he1
theorem cp_3_2_10 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 a0 a1) = (op b0 (aux1 b0 b1))) :
    Join (aux1 a0 a1) (op a0 (aux0 (shared ) (aux1 b0 b1))) := by
  cases heq
theorem cp_3_root_11 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (aux0 a0 a1)) = (aux0 (shared ) (aux1 (shared ) b0))) :
    Join (aux1 a0 a1) (shared ) := by
  cases heq
theorem cp_3_2_11 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 a0 a1) = (aux0 (shared ) (aux1 (shared ) b0))) :
    Join (aux1 a0 a1) (op a0 (shared )) := by
  rcases T.aux0.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  subst a0
  exact ⟨(shared ), ((Relation.ReflTransGen.refl).tail (root_step .r12 b0 (leaf 0) (leaf 0))), ((Relation.ReflTransGen.refl).tail (root_step .r0 (shared ) (leaf 0) (leaf 0)))⟩
theorem cp_3_root_12 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (aux0 a0 a1)) = (aux1 (shared ) (aux1 (shared ) b0))) :
    Join (aux1 a0 a1) (shared ) := by
  cases heq
theorem cp_3_2_12 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 a0 a1) = (aux1 (shared ) (aux1 (shared ) b0))) :
    Join (aux1 a0 a1) (op a0 (shared )) := by
  cases heq
theorem cp_3_root_13 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (aux0 a0 a1)) = (op (aux1 (aux1 b0 b1) (aux1 b0 b1)) b0)) :
    Join (aux1 a0 a1) (aux0 (aux1 b0 b1) b0) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst b0
  intro he0
  have hsize := congrArg sz he0
  have hp_a0 := sz_pos a0
  have hp_a1 := sz_pos a1
  have hp_b1 := sz_pos b1
  simp only [sz] at hsize
  omega
theorem cp_3_2_13 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 a0 a1) = (op (aux1 (aux1 b0 b1) (aux1 b0 b1)) b0)) :
    Join (aux1 a0 a1) (op a0 (aux0 (aux1 b0 b1) b0)) := by
  cases heq
theorem cp_3_root_14 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (aux0 a0 a1)) = (aux0 (aux0 (shared ) b0) (aux0 (shared ) b0))) :
    Join (aux1 a0 a1) (aux1 (shared ) b0) := by
  cases heq
theorem cp_3_2_14 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 a0 a1) = (aux0 (aux0 (shared ) b0) (aux0 (shared ) b0))) :
    Join (aux1 a0 a1) (op a0 (aux1 (shared ) b0)) := by
  rcases T.aux0.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  subst a0
  exact ⟨(aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)), (Relation.ReflTransGen.refl), ((Relation.ReflTransGen.refl).tail (root_step .r15 b0 (leaf 0) (leaf 0)))⟩
theorem cp_3_root_15 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (aux0 a0 a1)) = (op (aux0 (shared ) b0) (aux1 (shared ) b0))) :
    Join (aux1 a0 a1) (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  cases he1
theorem cp_3_2_15 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 a0 a1) = (op (aux0 (shared ) b0) (aux1 (shared ) b0))) :
    Join (aux1 a0 a1) (op a0 (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0))) := by
  cases heq
theorem cp_3_root_16 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (aux0 a0 a1)) = (op (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) (aux1 (shared ) b0))) :
    Join (aux1 a0 a1) (aux0 (aux0 (shared ) b0) (aux1 (shared ) b0)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  cases he1
theorem cp_3_2_16 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 a0 a1) = (op (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) (aux1 (shared ) b0))) :
    Join (aux1 a0 a1) (op a0 (aux0 (aux0 (shared ) b0) (aux1 (shared ) b0))) := by
  cases heq
theorem cp_4_root_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux0 a0 a1) a1) = (op b0 b0)) :
    Join (aux0 (op a0 a1) a1) (shared ) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  have hsize := congrArg sz he0
  have hp_a0 := sz_pos a0
  have hp_b0 := sz_pos b0
  simp only [sz] at hsize
  omega
theorem cp_4_1_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 a0 a1) = (op b0 b0)) :
    Join (aux0 (op a0 a1) a1) (op (shared ) a1) := by
  cases heq
theorem cp_4_root_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux0 a0 a1) a1) = (op (op b0 b1) b1)) :
    Join (aux0 (op a0 a1) a1) (aux0 b0 b1) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  cases he0
theorem cp_4_1_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 a0 a1) = (op (op b0 b1) b1)) :
    Join (aux0 (op a0 a1) a1) (op (aux0 b0 b1) a1) := by
  cases heq
theorem cp_4_root_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux0 a0 a1) a1) = (op (shared ) b0)) :
    Join (aux0 (op a0 a1) a1) (aux0 b0 b0) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  cases he0
theorem cp_4_1_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 a0 a1) = (op (shared ) b0)) :
    Join (aux0 (op a0 a1) a1) (op (aux0 b0 b0) a1) := by
  cases heq
theorem cp_4_root_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux0 a0 a1) a1) = (op b0 (aux0 b0 b1))) :
    Join (aux0 (op a0 a1) a1) (aux1 b0 b1) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  have hsize := congrArg sz he0
  have hp_a0 := sz_pos a0
  have hp_b0 := sz_pos b0
  have hp_b1 := sz_pos b1
  simp only [sz] at hsize
  omega
theorem cp_4_1_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 a0 a1) = (op b0 (aux0 b0 b1))) :
    Join (aux0 (op a0 a1) a1) (op (aux1 b0 b1) a1) := by
  cases heq
theorem cp_4_root_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux0 a0 a1) a1) = (op (aux0 b0 b1) b1)) :
    Join (aux0 (op a0 a1) a1) (aux0 (op b0 b1) b1) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  rcases T.aux0.inj he0 with ⟨he2, he3⟩
  clear he0
  clear he3
  subst a0
  exact ⟨(aux0 (op b0 b1) b1), (Relation.ReflTransGen.refl), (Relation.ReflTransGen.refl)⟩
theorem cp_4_1_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 a0 a1) = (op (aux0 b0 b1) b1)) :
    Join (aux0 (op a0 a1) a1) (op (aux0 (op b0 b1) b1) a1) := by
  cases heq
theorem cp_4_root_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux0 a0 a1) a1) = (aux0 (shared ) (shared ))) :
    Join (aux0 (op a0 a1) a1) (shared ) := by
  cases heq
theorem cp_4_1_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 a0 a1) = (aux0 (shared ) (shared ))) :
    Join (aux0 (op a0 a1) a1) (op (shared ) a1) := by
  rcases T.aux0.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  subst a0
  exact ⟨(shared ), (((Relation.ReflTransGen.refl).tail (Step.c_aux0_1 (shared ) (root_step .r0 (shared ) (leaf 0) (leaf 0)))).tail (root_step .r5 (leaf 0) (leaf 0) (leaf 0))), ((Relation.ReflTransGen.refl).tail (root_step .r0 (shared ) (leaf 0) (leaf 0)))⟩
theorem cp_4_root_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux0 a0 a1) a1) = (aux1 (shared ) (shared ))) :
    Join (aux0 (op a0 a1) a1) (shared ) := by
  cases heq
theorem cp_4_1_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 a0 a1) = (aux1 (shared ) (shared ))) :
    Join (aux0 (op a0 a1) a1) (op (shared ) a1) := by
  cases heq
theorem cp_4_root_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux0 a0 a1) a1) = (aux0 (aux1 b0 b1) (aux1 b0 b1))) :
    Join (aux0 (op a0 a1) a1) b0 := by
  cases heq
theorem cp_4_1_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 a0 a1) = (aux0 (aux1 b0 b1) (aux1 b0 b1))) :
    Join (aux0 (op a0 a1) a1) (op b0 a1) := by
  rcases T.aux0.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  subst a0
  exact ⟨(aux0 (shared ) (aux1 b0 b1)), ((Relation.ReflTransGen.refl).tail (Step.c_aux0_1 (aux1 b0 b1) (root_step .r0 (aux1 b0 b1) (leaf 0) (leaf 0)))), ((Relation.ReflTransGen.refl).tail (root_step .r10 b0 b1 (leaf 0)))⟩
theorem cp_4_root_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux0 a0 a1) a1) = (op (aux1 b0 b1) (aux0 b0 b1))) :
    Join (aux0 (op a0 a1) a1) (aux0 b0 (aux0 b0 b1)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  cases he0
theorem cp_4_1_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 a0 a1) = (op (aux1 b0 b1) (aux0 b0 b1))) :
    Join (aux0 (op a0 a1) a1) (op (aux0 b0 (aux0 b0 b1)) a1) := by
  cases heq
theorem cp_4_root_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux0 a0 a1) a1) = (op (aux1 b0 b1) b0)) :
    Join (aux0 (op a0 a1) a1) (aux1 (aux1 b0 b1) (aux1 b0 b1)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  cases he0
theorem cp_4_1_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 a0 a1) = (op (aux1 b0 b1) b0)) :
    Join (aux0 (op a0 a1) a1) (op (aux1 (aux1 b0 b1) (aux1 b0 b1)) a1) := by
  cases heq
theorem cp_4_root_10 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux0 a0 a1) a1) = (op b0 (aux1 b0 b1))) :
    Join (aux0 (op a0 a1) a1) (aux0 (shared ) (aux1 b0 b1)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  have hsize := congrArg sz he0
  have hp_a0 := sz_pos a0
  have hp_b0 := sz_pos b0
  have hp_b1 := sz_pos b1
  simp only [sz] at hsize
  omega
theorem cp_4_1_10 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 a0 a1) = (op b0 (aux1 b0 b1))) :
    Join (aux0 (op a0 a1) a1) (op (aux0 (shared ) (aux1 b0 b1)) a1) := by
  cases heq
theorem cp_4_root_11 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux0 a0 a1) a1) = (aux0 (shared ) (aux1 (shared ) b0))) :
    Join (aux0 (op a0 a1) a1) (shared ) := by
  cases heq
theorem cp_4_1_11 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 a0 a1) = (aux0 (shared ) (aux1 (shared ) b0))) :
    Join (aux0 (op a0 a1) a1) (op (shared ) a1) := by
  rcases T.aux0.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  subst a0
  exact ⟨(shared ), ((((Relation.ReflTransGen.refl).tail (Step.c_aux0_1 (aux1 (shared ) b0) (root_step .r2 (aux1 (shared ) b0) (leaf 0) (leaf 0)))).tail (Step.c_aux0_1 (aux1 (shared ) b0) (root_step .r7 (shared ) b0 (leaf 0)))).tail (root_step .r11 b0 (leaf 0) (leaf 0))), (((Relation.ReflTransGen.refl).tail (root_step .r2 (aux1 (shared ) b0) (leaf 0) (leaf 0))).tail (root_step .r7 (shared ) b0 (leaf 0)))⟩
theorem cp_4_root_12 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux0 a0 a1) a1) = (aux1 (shared ) (aux1 (shared ) b0))) :
    Join (aux0 (op a0 a1) a1) (shared ) := by
  cases heq
theorem cp_4_1_12 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 a0 a1) = (aux1 (shared ) (aux1 (shared ) b0))) :
    Join (aux0 (op a0 a1) a1) (op (shared ) a1) := by
  cases heq
theorem cp_4_root_13 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux0 a0 a1) a1) = (op (aux1 (aux1 b0 b1) (aux1 b0 b1)) b0)) :
    Join (aux0 (op a0 a1) a1) (aux0 (aux1 b0 b1) b0) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  cases he0
theorem cp_4_1_13 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 a0 a1) = (op (aux1 (aux1 b0 b1) (aux1 b0 b1)) b0)) :
    Join (aux0 (op a0 a1) a1) (op (aux0 (aux1 b0 b1) b0) a1) := by
  cases heq
theorem cp_4_root_14 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux0 a0 a1) a1) = (aux0 (aux0 (shared ) b0) (aux0 (shared ) b0))) :
    Join (aux0 (op a0 a1) a1) (aux1 (shared ) b0) := by
  cases heq
theorem cp_4_1_14 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 a0 a1) = (aux0 (aux0 (shared ) b0) (aux0 (shared ) b0))) :
    Join (aux0 (op a0 a1) a1) (op (aux1 (shared ) b0) a1) := by
  rcases T.aux0.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  subst a0
  exact ⟨(aux0 (shared ) (aux0 (shared ) b0)), ((Relation.ReflTransGen.refl).tail (Step.c_aux0_1 (aux0 (shared ) b0) (root_step .r0 (aux0 (shared ) b0) (leaf 0) (leaf 0)))), ((Relation.ReflTransGen.refl).tail (root_step .r8 (shared ) b0 (leaf 0)))⟩
theorem cp_4_root_15 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux0 a0 a1) a1) = (op (aux0 (shared ) b0) (aux1 (shared ) b0))) :
    Join (aux0 (op a0 a1) a1) (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  rcases T.aux0.inj he0 with ⟨he2, he3⟩
  clear he0
  have hsize := congrArg sz he3
  have hp_b0 := sz_pos b0
  simp only [sz] at hsize
  omega
theorem cp_4_1_15 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 a0 a1) = (op (aux0 (shared ) b0) (aux1 (shared ) b0))) :
    Join (aux0 (op a0 a1) a1) (op (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) a1) := by
  cases heq
theorem cp_4_root_16 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux0 a0 a1) a1) = (op (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) (aux1 (shared ) b0))) :
    Join (aux0 (op a0 a1) a1) (aux0 (aux0 (shared ) b0) (aux1 (shared ) b0)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  cases he0
theorem cp_4_1_16 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 a0 a1) = (op (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) (aux1 (shared ) b0))) :
    Join (aux0 (op a0 a1) a1) (op (aux0 (aux0 (shared ) b0) (aux1 (shared ) b0)) a1) := by
  cases heq
theorem cp_5_root_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) (shared )) = (op b0 b0)) :
    Join (shared ) (shared ) := by
  cases heq
theorem cp_5_1_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op b0 b0)) :
    Join (shared ) (aux0 (shared ) (shared )) := by
  cases heq
theorem cp_5_2_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op b0 b0)) :
    Join (shared ) (aux0 (shared ) (shared )) := by
  cases heq
theorem cp_5_root_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) (shared )) = (op (op b0 b1) b1)) :
    Join (shared ) (aux0 b0 b1) := by
  cases heq
theorem cp_5_1_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (op b0 b1) b1)) :
    Join (shared ) (aux0 (aux0 b0 b1) (shared )) := by
  cases heq
theorem cp_5_2_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (op b0 b1) b1)) :
    Join (shared ) (aux0 (shared ) (aux0 b0 b1)) := by
  cases heq
theorem cp_5_root_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) (shared )) = (op (shared ) b0)) :
    Join (shared ) (aux0 b0 b0) := by
  cases heq
theorem cp_5_1_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (shared ) b0)) :
    Join (shared ) (aux0 (aux0 b0 b0) (shared )) := by
  cases heq
theorem cp_5_2_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (shared ) b0)) :
    Join (shared ) (aux0 (shared ) (aux0 b0 b0)) := by
  cases heq
theorem cp_5_root_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) (shared )) = (op b0 (aux0 b0 b1))) :
    Join (shared ) (aux1 b0 b1) := by
  cases heq
theorem cp_5_1_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op b0 (aux0 b0 b1))) :
    Join (shared ) (aux0 (aux1 b0 b1) (shared )) := by
  cases heq
theorem cp_5_2_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op b0 (aux0 b0 b1))) :
    Join (shared ) (aux0 (shared ) (aux1 b0 b1)) := by
  cases heq
theorem cp_5_root_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) (shared )) = (op (aux0 b0 b1) b1)) :
    Join (shared ) (aux0 (op b0 b1) b1) := by
  cases heq
theorem cp_5_1_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux0 b0 b1) b1)) :
    Join (shared ) (aux0 (aux0 (op b0 b1) b1) (shared )) := by
  cases heq
theorem cp_5_2_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux0 b0 b1) b1)) :
    Join (shared ) (aux0 (shared ) (aux0 (op b0 b1) b1)) := by
  cases heq
theorem cp_5_root_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) (shared )) = (aux0 (shared ) (shared ))) :
    Join (shared ) (shared ) := by
  clear heq
  exact ⟨(shared ), (Relation.ReflTransGen.refl), (Relation.ReflTransGen.refl)⟩
theorem cp_5_1_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux0 (shared ) (shared ))) :
    Join (shared ) (aux0 (shared ) (shared )) := by
  cases heq
theorem cp_5_2_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux0 (shared ) (shared ))) :
    Join (shared ) (aux0 (shared ) (shared )) := by
  cases heq
theorem cp_5_root_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) (shared )) = (aux1 (shared ) (shared ))) :
    Join (shared ) (shared ) := by
  cases heq
theorem cp_5_1_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux1 (shared ) (shared ))) :
    Join (shared ) (aux0 (shared ) (shared )) := by
  cases heq
theorem cp_5_2_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux1 (shared ) (shared ))) :
    Join (shared ) (aux0 (shared ) (shared )) := by
  cases heq
theorem cp_5_root_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) (shared )) = (aux0 (aux1 b0 b1) (aux1 b0 b1))) :
    Join (shared ) b0 := by
  rcases T.aux0.inj heq with ⟨he0, he1⟩
  clear heq
  cases he1
theorem cp_5_1_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux0 (aux1 b0 b1) (aux1 b0 b1))) :
    Join (shared ) (aux0 b0 (shared )) := by
  cases heq
theorem cp_5_2_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux0 (aux1 b0 b1) (aux1 b0 b1))) :
    Join (shared ) (aux0 (shared ) b0) := by
  cases heq
theorem cp_5_root_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) (shared )) = (op (aux1 b0 b1) (aux0 b0 b1))) :
    Join (shared ) (aux0 b0 (aux0 b0 b1)) := by
  cases heq
theorem cp_5_1_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux1 b0 b1) (aux0 b0 b1))) :
    Join (shared ) (aux0 (aux0 b0 (aux0 b0 b1)) (shared )) := by
  cases heq
theorem cp_5_2_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux1 b0 b1) (aux0 b0 b1))) :
    Join (shared ) (aux0 (shared ) (aux0 b0 (aux0 b0 b1))) := by
  cases heq
theorem cp_5_root_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) (shared )) = (op (aux1 b0 b1) b0)) :
    Join (shared ) (aux1 (aux1 b0 b1) (aux1 b0 b1)) := by
  cases heq
theorem cp_5_1_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux1 b0 b1) b0)) :
    Join (shared ) (aux0 (aux1 (aux1 b0 b1) (aux1 b0 b1)) (shared )) := by
  cases heq
theorem cp_5_2_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux1 b0 b1) b0)) :
    Join (shared ) (aux0 (shared ) (aux1 (aux1 b0 b1) (aux1 b0 b1))) := by
  cases heq
theorem cp_5_root_10 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) (shared )) = (op b0 (aux1 b0 b1))) :
    Join (shared ) (aux0 (shared ) (aux1 b0 b1)) := by
  cases heq
theorem cp_5_1_10 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op b0 (aux1 b0 b1))) :
    Join (shared ) (aux0 (aux0 (shared ) (aux1 b0 b1)) (shared )) := by
  cases heq
theorem cp_5_2_10 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op b0 (aux1 b0 b1))) :
    Join (shared ) (aux0 (shared ) (aux0 (shared ) (aux1 b0 b1))) := by
  cases heq
theorem cp_5_root_11 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) (shared )) = (aux0 (shared ) (aux1 (shared ) b0))) :
    Join (shared ) (shared ) := by
  rcases T.aux0.inj heq with ⟨he0, he1⟩
  clear heq
  cases he1
theorem cp_5_1_11 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux0 (shared ) (aux1 (shared ) b0))) :
    Join (shared ) (aux0 (shared ) (shared )) := by
  cases heq
theorem cp_5_2_11 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux0 (shared ) (aux1 (shared ) b0))) :
    Join (shared ) (aux0 (shared ) (shared )) := by
  cases heq
theorem cp_5_root_12 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) (shared )) = (aux1 (shared ) (aux1 (shared ) b0))) :
    Join (shared ) (shared ) := by
  cases heq
theorem cp_5_1_12 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux1 (shared ) (aux1 (shared ) b0))) :
    Join (shared ) (aux0 (shared ) (shared )) := by
  cases heq
theorem cp_5_2_12 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux1 (shared ) (aux1 (shared ) b0))) :
    Join (shared ) (aux0 (shared ) (shared )) := by
  cases heq
theorem cp_5_root_13 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) (shared )) = (op (aux1 (aux1 b0 b1) (aux1 b0 b1)) b0)) :
    Join (shared ) (aux0 (aux1 b0 b1) b0) := by
  cases heq
theorem cp_5_1_13 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux1 (aux1 b0 b1) (aux1 b0 b1)) b0)) :
    Join (shared ) (aux0 (aux0 (aux1 b0 b1) b0) (shared )) := by
  cases heq
theorem cp_5_2_13 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux1 (aux1 b0 b1) (aux1 b0 b1)) b0)) :
    Join (shared ) (aux0 (shared ) (aux0 (aux1 b0 b1) b0)) := by
  cases heq
theorem cp_5_root_14 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) (shared )) = (aux0 (aux0 (shared ) b0) (aux0 (shared ) b0))) :
    Join (shared ) (aux1 (shared ) b0) := by
  rcases T.aux0.inj heq with ⟨he0, he1⟩
  clear heq
  cases he1
theorem cp_5_1_14 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux0 (aux0 (shared ) b0) (aux0 (shared ) b0))) :
    Join (shared ) (aux0 (aux1 (shared ) b0) (shared )) := by
  cases heq
theorem cp_5_2_14 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux0 (aux0 (shared ) b0) (aux0 (shared ) b0))) :
    Join (shared ) (aux0 (shared ) (aux1 (shared ) b0)) := by
  cases heq
theorem cp_5_root_15 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) (shared )) = (op (aux0 (shared ) b0) (aux1 (shared ) b0))) :
    Join (shared ) (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) := by
  cases heq
theorem cp_5_1_15 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux0 (shared ) b0) (aux1 (shared ) b0))) :
    Join (shared ) (aux0 (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) (shared )) := by
  cases heq
theorem cp_5_2_15 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux0 (shared ) b0) (aux1 (shared ) b0))) :
    Join (shared ) (aux0 (shared ) (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0))) := by
  cases heq
theorem cp_5_root_16 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) (shared )) = (op (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) (aux1 (shared ) b0))) :
    Join (shared ) (aux0 (aux0 (shared ) b0) (aux1 (shared ) b0)) := by
  cases heq
theorem cp_5_1_16 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) (aux1 (shared ) b0))) :
    Join (shared ) (aux0 (aux0 (aux0 (shared ) b0) (aux1 (shared ) b0)) (shared )) := by
  cases heq
theorem cp_5_2_16 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) (aux1 (shared ) b0))) :
    Join (shared ) (aux0 (shared ) (aux0 (aux0 (shared ) b0) (aux1 (shared ) b0))) := by
  cases heq
theorem cp_6_root_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) (shared )) = (op b0 b0)) :
    Join (shared ) (shared ) := by
  cases heq
theorem cp_6_1_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op b0 b0)) :
    Join (shared ) (aux1 (shared ) (shared )) := by
  cases heq
theorem cp_6_2_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op b0 b0)) :
    Join (shared ) (aux1 (shared ) (shared )) := by
  cases heq
theorem cp_6_root_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) (shared )) = (op (op b0 b1) b1)) :
    Join (shared ) (aux0 b0 b1) := by
  cases heq
theorem cp_6_1_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (op b0 b1) b1)) :
    Join (shared ) (aux1 (aux0 b0 b1) (shared )) := by
  cases heq
theorem cp_6_2_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (op b0 b1) b1)) :
    Join (shared ) (aux1 (shared ) (aux0 b0 b1)) := by
  cases heq
theorem cp_6_root_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) (shared )) = (op (shared ) b0)) :
    Join (shared ) (aux0 b0 b0) := by
  cases heq
theorem cp_6_1_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (shared ) b0)) :
    Join (shared ) (aux1 (aux0 b0 b0) (shared )) := by
  cases heq
theorem cp_6_2_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (shared ) b0)) :
    Join (shared ) (aux1 (shared ) (aux0 b0 b0)) := by
  cases heq
theorem cp_6_root_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) (shared )) = (op b0 (aux0 b0 b1))) :
    Join (shared ) (aux1 b0 b1) := by
  cases heq
theorem cp_6_1_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op b0 (aux0 b0 b1))) :
    Join (shared ) (aux1 (aux1 b0 b1) (shared )) := by
  cases heq
theorem cp_6_2_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op b0 (aux0 b0 b1))) :
    Join (shared ) (aux1 (shared ) (aux1 b0 b1)) := by
  cases heq
theorem cp_6_root_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) (shared )) = (op (aux0 b0 b1) b1)) :
    Join (shared ) (aux0 (op b0 b1) b1) := by
  cases heq
theorem cp_6_1_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux0 b0 b1) b1)) :
    Join (shared ) (aux1 (aux0 (op b0 b1) b1) (shared )) := by
  cases heq
theorem cp_6_2_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux0 b0 b1) b1)) :
    Join (shared ) (aux1 (shared ) (aux0 (op b0 b1) b1)) := by
  cases heq
theorem cp_6_root_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) (shared )) = (aux0 (shared ) (shared ))) :
    Join (shared ) (shared ) := by
  cases heq
theorem cp_6_1_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux0 (shared ) (shared ))) :
    Join (shared ) (aux1 (shared ) (shared )) := by
  cases heq
theorem cp_6_2_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux0 (shared ) (shared ))) :
    Join (shared ) (aux1 (shared ) (shared )) := by
  cases heq
theorem cp_6_root_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) (shared )) = (aux1 (shared ) (shared ))) :
    Join (shared ) (shared ) := by
  clear heq
  exact ⟨(shared ), (Relation.ReflTransGen.refl), (Relation.ReflTransGen.refl)⟩
theorem cp_6_1_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux1 (shared ) (shared ))) :
    Join (shared ) (aux1 (shared ) (shared )) := by
  cases heq
theorem cp_6_2_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux1 (shared ) (shared ))) :
    Join (shared ) (aux1 (shared ) (shared )) := by
  cases heq
theorem cp_6_root_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) (shared )) = (aux0 (aux1 b0 b1) (aux1 b0 b1))) :
    Join (shared ) b0 := by
  cases heq
theorem cp_6_1_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux0 (aux1 b0 b1) (aux1 b0 b1))) :
    Join (shared ) (aux1 b0 (shared )) := by
  cases heq
theorem cp_6_2_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux0 (aux1 b0 b1) (aux1 b0 b1))) :
    Join (shared ) (aux1 (shared ) b0) := by
  cases heq
theorem cp_6_root_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) (shared )) = (op (aux1 b0 b1) (aux0 b0 b1))) :
    Join (shared ) (aux0 b0 (aux0 b0 b1)) := by
  cases heq
theorem cp_6_1_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux1 b0 b1) (aux0 b0 b1))) :
    Join (shared ) (aux1 (aux0 b0 (aux0 b0 b1)) (shared )) := by
  cases heq
theorem cp_6_2_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux1 b0 b1) (aux0 b0 b1))) :
    Join (shared ) (aux1 (shared ) (aux0 b0 (aux0 b0 b1))) := by
  cases heq
theorem cp_6_root_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) (shared )) = (op (aux1 b0 b1) b0)) :
    Join (shared ) (aux1 (aux1 b0 b1) (aux1 b0 b1)) := by
  cases heq
theorem cp_6_1_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux1 b0 b1) b0)) :
    Join (shared ) (aux1 (aux1 (aux1 b0 b1) (aux1 b0 b1)) (shared )) := by
  cases heq
theorem cp_6_2_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux1 b0 b1) b0)) :
    Join (shared ) (aux1 (shared ) (aux1 (aux1 b0 b1) (aux1 b0 b1))) := by
  cases heq
theorem cp_6_root_10 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) (shared )) = (op b0 (aux1 b0 b1))) :
    Join (shared ) (aux0 (shared ) (aux1 b0 b1)) := by
  cases heq
theorem cp_6_1_10 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op b0 (aux1 b0 b1))) :
    Join (shared ) (aux1 (aux0 (shared ) (aux1 b0 b1)) (shared )) := by
  cases heq
theorem cp_6_2_10 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op b0 (aux1 b0 b1))) :
    Join (shared ) (aux1 (shared ) (aux0 (shared ) (aux1 b0 b1))) := by
  cases heq
theorem cp_6_root_11 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) (shared )) = (aux0 (shared ) (aux1 (shared ) b0))) :
    Join (shared ) (shared ) := by
  cases heq
theorem cp_6_1_11 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux0 (shared ) (aux1 (shared ) b0))) :
    Join (shared ) (aux1 (shared ) (shared )) := by
  cases heq
theorem cp_6_2_11 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux0 (shared ) (aux1 (shared ) b0))) :
    Join (shared ) (aux1 (shared ) (shared )) := by
  cases heq
theorem cp_6_root_12 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) (shared )) = (aux1 (shared ) (aux1 (shared ) b0))) :
    Join (shared ) (shared ) := by
  rcases T.aux1.inj heq with ⟨he0, he1⟩
  clear heq
  cases he1
theorem cp_6_1_12 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux1 (shared ) (aux1 (shared ) b0))) :
    Join (shared ) (aux1 (shared ) (shared )) := by
  cases heq
theorem cp_6_2_12 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux1 (shared ) (aux1 (shared ) b0))) :
    Join (shared ) (aux1 (shared ) (shared )) := by
  cases heq
theorem cp_6_root_13 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) (shared )) = (op (aux1 (aux1 b0 b1) (aux1 b0 b1)) b0)) :
    Join (shared ) (aux0 (aux1 b0 b1) b0) := by
  cases heq
theorem cp_6_1_13 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux1 (aux1 b0 b1) (aux1 b0 b1)) b0)) :
    Join (shared ) (aux1 (aux0 (aux1 b0 b1) b0) (shared )) := by
  cases heq
theorem cp_6_2_13 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux1 (aux1 b0 b1) (aux1 b0 b1)) b0)) :
    Join (shared ) (aux1 (shared ) (aux0 (aux1 b0 b1) b0)) := by
  cases heq
theorem cp_6_root_14 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) (shared )) = (aux0 (aux0 (shared ) b0) (aux0 (shared ) b0))) :
    Join (shared ) (aux1 (shared ) b0) := by
  cases heq
theorem cp_6_1_14 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux0 (aux0 (shared ) b0) (aux0 (shared ) b0))) :
    Join (shared ) (aux1 (aux1 (shared ) b0) (shared )) := by
  cases heq
theorem cp_6_2_14 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux0 (aux0 (shared ) b0) (aux0 (shared ) b0))) :
    Join (shared ) (aux1 (shared ) (aux1 (shared ) b0)) := by
  cases heq
theorem cp_6_root_15 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) (shared )) = (op (aux0 (shared ) b0) (aux1 (shared ) b0))) :
    Join (shared ) (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) := by
  cases heq
theorem cp_6_1_15 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux0 (shared ) b0) (aux1 (shared ) b0))) :
    Join (shared ) (aux1 (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) (shared )) := by
  cases heq
theorem cp_6_2_15 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux0 (shared ) b0) (aux1 (shared ) b0))) :
    Join (shared ) (aux1 (shared ) (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0))) := by
  cases heq
theorem cp_6_root_16 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) (shared )) = (op (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) (aux1 (shared ) b0))) :
    Join (shared ) (aux0 (aux0 (shared ) b0) (aux1 (shared ) b0)) := by
  cases heq
theorem cp_6_1_16 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) (aux1 (shared ) b0))) :
    Join (shared ) (aux1 (aux0 (aux0 (shared ) b0) (aux1 (shared ) b0)) (shared )) := by
  cases heq
theorem cp_6_2_16 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) (aux1 (shared ) b0))) :
    Join (shared ) (aux1 (shared ) (aux0 (aux0 (shared ) b0) (aux1 (shared ) b0))) := by
  cases heq
theorem cp_7_root_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (aux1 a0 a1) (aux1 a0 a1)) = (op b0 b0)) :
    Join a0 (shared ) := by
  cases heq
theorem cp_7_1_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (op b0 b0)) :
    Join a0 (aux0 (shared ) (aux1 a0 a1)) := by
  cases heq
theorem cp_7_2_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (op b0 b0)) :
    Join a0 (aux0 (aux1 a0 a1) (shared )) := by
  cases heq
theorem cp_7_root_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (aux1 a0 a1) (aux1 a0 a1)) = (op (op b0 b1) b1)) :
    Join a0 (aux0 b0 b1) := by
  cases heq
theorem cp_7_1_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (op (op b0 b1) b1)) :
    Join a0 (aux0 (aux0 b0 b1) (aux1 a0 a1)) := by
  cases heq
theorem cp_7_2_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (op (op b0 b1) b1)) :
    Join a0 (aux0 (aux1 a0 a1) (aux0 b0 b1)) := by
  cases heq
theorem cp_7_root_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (aux1 a0 a1) (aux1 a0 a1)) = (op (shared ) b0)) :
    Join a0 (aux0 b0 b0) := by
  cases heq
theorem cp_7_1_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (op (shared ) b0)) :
    Join a0 (aux0 (aux0 b0 b0) (aux1 a0 a1)) := by
  cases heq
theorem cp_7_2_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (op (shared ) b0)) :
    Join a0 (aux0 (aux1 a0 a1) (aux0 b0 b0)) := by
  cases heq
theorem cp_7_root_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (aux1 a0 a1) (aux1 a0 a1)) = (op b0 (aux0 b0 b1))) :
    Join a0 (aux1 b0 b1) := by
  cases heq
theorem cp_7_1_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (op b0 (aux0 b0 b1))) :
    Join a0 (aux0 (aux1 b0 b1) (aux1 a0 a1)) := by
  cases heq
theorem cp_7_2_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (op b0 (aux0 b0 b1))) :
    Join a0 (aux0 (aux1 a0 a1) (aux1 b0 b1)) := by
  cases heq
theorem cp_7_root_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (aux1 a0 a1) (aux1 a0 a1)) = (op (aux0 b0 b1) b1)) :
    Join a0 (aux0 (op b0 b1) b1) := by
  cases heq
theorem cp_7_1_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (op (aux0 b0 b1) b1)) :
    Join a0 (aux0 (aux0 (op b0 b1) b1) (aux1 a0 a1)) := by
  cases heq
theorem cp_7_2_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (op (aux0 b0 b1) b1)) :
    Join a0 (aux0 (aux1 a0 a1) (aux0 (op b0 b1) b1)) := by
  cases heq
theorem cp_7_root_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (aux1 a0 a1) (aux1 a0 a1)) = (aux0 (shared ) (shared ))) :
    Join a0 (shared ) := by
  rcases T.aux0.inj heq with ⟨he0, he1⟩
  clear heq
  cases he1
theorem cp_7_1_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (aux0 (shared ) (shared ))) :
    Join a0 (aux0 (shared ) (aux1 a0 a1)) := by
  cases heq
theorem cp_7_2_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (aux0 (shared ) (shared ))) :
    Join a0 (aux0 (aux1 a0 a1) (shared )) := by
  cases heq
theorem cp_7_root_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (aux1 a0 a1) (aux1 a0 a1)) = (aux1 (shared ) (shared ))) :
    Join a0 (shared ) := by
  cases heq
theorem cp_7_1_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (aux1 (shared ) (shared ))) :
    Join a0 (aux0 (shared ) (aux1 a0 a1)) := by
  rcases T.aux1.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  subst a0
  exact ⟨(shared ), (Relation.ReflTransGen.refl), ((Relation.ReflTransGen.refl).tail (root_step .r11 (shared ) (leaf 0) (leaf 0)))⟩
theorem cp_7_2_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (aux1 (shared ) (shared ))) :
    Join a0 (aux0 (aux1 a0 a1) (shared )) := by
  rcases T.aux1.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  subst a0
  exact ⟨(shared ), (Relation.ReflTransGen.refl), (((Relation.ReflTransGen.refl).tail (Step.c_aux0_1 (shared ) (root_step .r6 (leaf 0) (leaf 0) (leaf 0)))).tail (root_step .r5 (leaf 0) (leaf 0) (leaf 0)))⟩
theorem cp_7_root_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (aux1 a0 a1) (aux1 a0 a1)) = (aux0 (aux1 b0 b1) (aux1 b0 b1))) :
    Join a0 b0 := by
  rcases T.aux0.inj heq with ⟨he0, he1⟩
  clear heq
  rcases T.aux1.inj he1 with ⟨he2, he3⟩
  clear he1
  revert he0 he2
  subst a1
  intro he0 he2
  revert he0
  subst a0
  intro he0
  clear he0
  exact ⟨b0, (Relation.ReflTransGen.refl), (Relation.ReflTransGen.refl)⟩
theorem cp_7_1_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (aux0 (aux1 b0 b1) (aux1 b0 b1))) :
    Join a0 (aux0 b0 (aux1 a0 a1)) := by
  cases heq
theorem cp_7_2_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (aux0 (aux1 b0 b1) (aux1 b0 b1))) :
    Join a0 (aux0 (aux1 a0 a1) b0) := by
  cases heq
theorem cp_7_root_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (aux1 a0 a1) (aux1 a0 a1)) = (op (aux1 b0 b1) (aux0 b0 b1))) :
    Join a0 (aux0 b0 (aux0 b0 b1)) := by
  cases heq
theorem cp_7_1_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (op (aux1 b0 b1) (aux0 b0 b1))) :
    Join a0 (aux0 (aux0 b0 (aux0 b0 b1)) (aux1 a0 a1)) := by
  cases heq
theorem cp_7_2_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (op (aux1 b0 b1) (aux0 b0 b1))) :
    Join a0 (aux0 (aux1 a0 a1) (aux0 b0 (aux0 b0 b1))) := by
  cases heq
theorem cp_7_root_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (aux1 a0 a1) (aux1 a0 a1)) = (op (aux1 b0 b1) b0)) :
    Join a0 (aux1 (aux1 b0 b1) (aux1 b0 b1)) := by
  cases heq
theorem cp_7_1_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (op (aux1 b0 b1) b0)) :
    Join a0 (aux0 (aux1 (aux1 b0 b1) (aux1 b0 b1)) (aux1 a0 a1)) := by
  cases heq
theorem cp_7_2_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (op (aux1 b0 b1) b0)) :
    Join a0 (aux0 (aux1 a0 a1) (aux1 (aux1 b0 b1) (aux1 b0 b1))) := by
  cases heq
theorem cp_7_root_10 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (aux1 a0 a1) (aux1 a0 a1)) = (op b0 (aux1 b0 b1))) :
    Join a0 (aux0 (shared ) (aux1 b0 b1)) := by
  cases heq
theorem cp_7_1_10 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (op b0 (aux1 b0 b1))) :
    Join a0 (aux0 (aux0 (shared ) (aux1 b0 b1)) (aux1 a0 a1)) := by
  cases heq
theorem cp_7_2_10 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (op b0 (aux1 b0 b1))) :
    Join a0 (aux0 (aux1 a0 a1) (aux0 (shared ) (aux1 b0 b1))) := by
  cases heq
theorem cp_7_root_11 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (aux1 a0 a1) (aux1 a0 a1)) = (aux0 (shared ) (aux1 (shared ) b0))) :
    Join a0 (shared ) := by
  rcases T.aux0.inj heq with ⟨he0, he1⟩
  clear heq
  rcases T.aux1.inj he1 with ⟨he2, he3⟩
  clear he1
  revert he0 he2
  subst a1
  intro he0 he2
  revert he0
  subst a0
  intro he0
  cases he0
theorem cp_7_1_11 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (aux0 (shared ) (aux1 (shared ) b0))) :
    Join a0 (aux0 (shared ) (aux1 a0 a1)) := by
  cases heq
theorem cp_7_2_11 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (aux0 (shared ) (aux1 (shared ) b0))) :
    Join a0 (aux0 (aux1 a0 a1) (shared )) := by
  cases heq
theorem cp_7_root_12 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (aux1 a0 a1) (aux1 a0 a1)) = (aux1 (shared ) (aux1 (shared ) b0))) :
    Join a0 (shared ) := by
  cases heq
theorem cp_7_1_12 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (aux1 (shared ) (aux1 (shared ) b0))) :
    Join a0 (aux0 (shared ) (aux1 a0 a1)) := by
  rcases T.aux1.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  subst a0
  exact ⟨(shared ), (Relation.ReflTransGen.refl), ((Relation.ReflTransGen.refl).tail (root_step .r11 (aux1 (shared ) b0) (leaf 0) (leaf 0)))⟩
theorem cp_7_2_12 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (aux1 (shared ) (aux1 (shared ) b0))) :
    Join a0 (aux0 (aux1 a0 a1) (shared )) := by
  rcases T.aux1.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  subst a0
  exact ⟨(shared ), (Relation.ReflTransGen.refl), (((Relation.ReflTransGen.refl).tail (Step.c_aux0_1 (shared ) (root_step .r12 b0 (leaf 0) (leaf 0)))).tail (root_step .r5 (leaf 0) (leaf 0) (leaf 0)))⟩
theorem cp_7_root_13 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (aux1 a0 a1) (aux1 a0 a1)) = (op (aux1 (aux1 b0 b1) (aux1 b0 b1)) b0)) :
    Join a0 (aux0 (aux1 b0 b1) b0) := by
  cases heq
theorem cp_7_1_13 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (op (aux1 (aux1 b0 b1) (aux1 b0 b1)) b0)) :
    Join a0 (aux0 (aux0 (aux1 b0 b1) b0) (aux1 a0 a1)) := by
  cases heq
theorem cp_7_2_13 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (op (aux1 (aux1 b0 b1) (aux1 b0 b1)) b0)) :
    Join a0 (aux0 (aux1 a0 a1) (aux0 (aux1 b0 b1) b0)) := by
  cases heq
theorem cp_7_root_14 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (aux1 a0 a1) (aux1 a0 a1)) = (aux0 (aux0 (shared ) b0) (aux0 (shared ) b0))) :
    Join a0 (aux1 (shared ) b0) := by
  rcases T.aux0.inj heq with ⟨he0, he1⟩
  clear heq
  cases he1
theorem cp_7_1_14 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (aux0 (aux0 (shared ) b0) (aux0 (shared ) b0))) :
    Join a0 (aux0 (aux1 (shared ) b0) (aux1 a0 a1)) := by
  cases heq
theorem cp_7_2_14 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (aux0 (aux0 (shared ) b0) (aux0 (shared ) b0))) :
    Join a0 (aux0 (aux1 a0 a1) (aux1 (shared ) b0)) := by
  cases heq
theorem cp_7_root_15 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (aux1 a0 a1) (aux1 a0 a1)) = (op (aux0 (shared ) b0) (aux1 (shared ) b0))) :
    Join a0 (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) := by
  cases heq
theorem cp_7_1_15 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (op (aux0 (shared ) b0) (aux1 (shared ) b0))) :
    Join a0 (aux0 (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) (aux1 a0 a1)) := by
  cases heq
theorem cp_7_2_15 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (op (aux0 (shared ) b0) (aux1 (shared ) b0))) :
    Join a0 (aux0 (aux1 a0 a1) (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0))) := by
  cases heq
theorem cp_7_root_16 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (aux1 a0 a1) (aux1 a0 a1)) = (op (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) (aux1 (shared ) b0))) :
    Join a0 (aux0 (aux0 (shared ) b0) (aux1 (shared ) b0)) := by
  cases heq
theorem cp_7_1_16 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (op (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) (aux1 (shared ) b0))) :
    Join a0 (aux0 (aux0 (aux0 (shared ) b0) (aux1 (shared ) b0)) (aux1 a0 a1)) := by
  cases heq
theorem cp_7_2_16 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (op (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) (aux1 (shared ) b0))) :
    Join a0 (aux0 (aux1 a0 a1) (aux0 (aux0 (shared ) b0) (aux1 (shared ) b0))) := by
  cases heq
theorem cp_8_root_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux1 a0 a1) (aux0 a0 a1)) = (op b0 b0)) :
    Join (aux0 a0 (aux0 a0 a1)) (shared ) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst b0
  intro he0
  cases he0
theorem cp_8_1_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (op b0 b0)) :
    Join (aux0 a0 (aux0 a0 a1)) (op (shared ) (aux0 a0 a1)) := by
  cases heq
theorem cp_8_2_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 a0 a1) = (op b0 b0)) :
    Join (aux0 a0 (aux0 a0 a1)) (op (aux1 a0 a1) (shared )) := by
  cases heq
theorem cp_8_root_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux1 a0 a1) (aux0 a0 a1)) = (op (op b0 b1) b1)) :
    Join (aux0 a0 (aux0 a0 a1)) (aux0 b0 b1) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst b1
  intro he0
  cases he0
theorem cp_8_1_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (op (op b0 b1) b1)) :
    Join (aux0 a0 (aux0 a0 a1)) (op (aux0 b0 b1) (aux0 a0 a1)) := by
  cases heq
theorem cp_8_2_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 a0 a1) = (op (op b0 b1) b1)) :
    Join (aux0 a0 (aux0 a0 a1)) (op (aux1 a0 a1) (aux0 b0 b1)) := by
  cases heq
theorem cp_8_root_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux1 a0 a1) (aux0 a0 a1)) = (op (shared ) b0)) :
    Join (aux0 a0 (aux0 a0 a1)) (aux0 b0 b0) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst b0
  intro he0
  cases he0
theorem cp_8_1_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (op (shared ) b0)) :
    Join (aux0 a0 (aux0 a0 a1)) (op (aux0 b0 b0) (aux0 a0 a1)) := by
  cases heq
theorem cp_8_2_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 a0 a1) = (op (shared ) b0)) :
    Join (aux0 a0 (aux0 a0 a1)) (op (aux1 a0 a1) (aux0 b0 b0)) := by
  cases heq
theorem cp_8_root_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux1 a0 a1) (aux0 a0 a1)) = (op b0 (aux0 b0 b1))) :
    Join (aux0 a0 (aux0 a0 a1)) (aux1 b0 b1) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  rcases T.aux0.inj he1 with ⟨he2, he3⟩
  clear he1
  revert he0 he2
  subst a1
  intro he0 he2
  revert he0
  subst a0
  intro he0
  have hsize := congrArg sz he0
  have hp_b0 := sz_pos b0
  have hp_b1 := sz_pos b1
  simp only [sz] at hsize
  omega
theorem cp_8_1_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (op b0 (aux0 b0 b1))) :
    Join (aux0 a0 (aux0 a0 a1)) (op (aux1 b0 b1) (aux0 a0 a1)) := by
  cases heq
theorem cp_8_2_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 a0 a1) = (op b0 (aux0 b0 b1))) :
    Join (aux0 a0 (aux0 a0 a1)) (op (aux1 a0 a1) (aux1 b0 b1)) := by
  cases heq
theorem cp_8_root_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux1 a0 a1) (aux0 a0 a1)) = (op (aux0 b0 b1) b1)) :
    Join (aux0 a0 (aux0 a0 a1)) (aux0 (op b0 b1) b1) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst b1
  intro he0
  cases he0
theorem cp_8_1_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (op (aux0 b0 b1) b1)) :
    Join (aux0 a0 (aux0 a0 a1)) (op (aux0 (op b0 b1) b1) (aux0 a0 a1)) := by
  cases heq
theorem cp_8_2_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 a0 a1) = (op (aux0 b0 b1) b1)) :
    Join (aux0 a0 (aux0 a0 a1)) (op (aux1 a0 a1) (aux0 (op b0 b1) b1)) := by
  cases heq
theorem cp_8_root_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux1 a0 a1) (aux0 a0 a1)) = (aux0 (shared ) (shared ))) :
    Join (aux0 a0 (aux0 a0 a1)) (shared ) := by
  cases heq
theorem cp_8_1_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (aux0 (shared ) (shared ))) :
    Join (aux0 a0 (aux0 a0 a1)) (op (shared ) (aux0 a0 a1)) := by
  cases heq
theorem cp_8_2_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 a0 a1) = (aux0 (shared ) (shared ))) :
    Join (aux0 a0 (aux0 a0 a1)) (op (aux1 a0 a1) (shared )) := by
  rcases T.aux0.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  subst a0
  exact ⟨(shared ), (((Relation.ReflTransGen.refl).tail (Step.c_aux0_2 (shared ) (root_step .r5 (leaf 0) (leaf 0) (leaf 0)))).tail (root_step .r5 (leaf 0) (leaf 0) (leaf 0))), ((((Relation.ReflTransGen.refl).tail (root_step .r9 (shared ) (shared ) (leaf 0))).tail (Step.c_aux1_1 (aux1 (shared ) (shared )) (root_step .r6 (leaf 0) (leaf 0) (leaf 0)))).tail (root_step .r12 (shared ) (leaf 0) (leaf 0)))⟩
theorem cp_8_root_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux1 a0 a1) (aux0 a0 a1)) = (aux1 (shared ) (shared ))) :
    Join (aux0 a0 (aux0 a0 a1)) (shared ) := by
  cases heq
theorem cp_8_1_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (aux1 (shared ) (shared ))) :
    Join (aux0 a0 (aux0 a0 a1)) (op (shared ) (aux0 a0 a1)) := by
  rcases T.aux1.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  subst a0
  exact ⟨(shared ), (((Relation.ReflTransGen.refl).tail (Step.c_aux0_2 (shared ) (root_step .r5 (leaf 0) (leaf 0) (leaf 0)))).tail (root_step .r5 (leaf 0) (leaf 0) (leaf 0))), ((((Relation.ReflTransGen.refl).tail (root_step .r2 (aux0 (shared ) (shared )) (leaf 0) (leaf 0))).tail (root_step .r14 (shared ) (leaf 0) (leaf 0))).tail (root_step .r6 (leaf 0) (leaf 0) (leaf 0)))⟩
theorem cp_8_2_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 a0 a1) = (aux1 (shared ) (shared ))) :
    Join (aux0 a0 (aux0 a0 a1)) (op (aux1 a0 a1) (shared )) := by
  cases heq
theorem cp_8_root_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux1 a0 a1) (aux0 a0 a1)) = (aux0 (aux1 b0 b1) (aux1 b0 b1))) :
    Join (aux0 a0 (aux0 a0 a1)) b0 := by
  cases heq
theorem cp_8_1_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (aux0 (aux1 b0 b1) (aux1 b0 b1))) :
    Join (aux0 a0 (aux0 a0 a1)) (op b0 (aux0 a0 a1)) := by
  cases heq
theorem cp_8_2_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 a0 a1) = (aux0 (aux1 b0 b1) (aux1 b0 b1))) :
    Join (aux0 a0 (aux0 a0 a1)) (op (aux1 a0 a1) b0) := by
  rcases T.aux0.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  subst a0
  exact ⟨(aux0 (aux1 b0 b1) b0), ((Relation.ReflTransGen.refl).tail (Step.c_aux0_2 (aux1 b0 b1) (root_step .r7 b0 b1 (leaf 0)))), ((Relation.ReflTransGen.refl).tail (root_step .r13 b0 b1 (leaf 0)))⟩
theorem cp_8_root_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux1 a0 a1) (aux0 a0 a1)) = (op (aux1 b0 b1) (aux0 b0 b1))) :
    Join (aux0 a0 (aux0 a0 a1)) (aux0 b0 (aux0 b0 b1)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  rcases T.aux0.inj he1 with ⟨he2, he3⟩
  clear he1
  revert he0 he2
  subst a1
  intro he0 he2
  revert he0
  subst a0
  intro he0
  clear he0
  exact ⟨(aux0 b0 (aux0 b0 b1)), (Relation.ReflTransGen.refl), (Relation.ReflTransGen.refl)⟩
theorem cp_8_1_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (op (aux1 b0 b1) (aux0 b0 b1))) :
    Join (aux0 a0 (aux0 a0 a1)) (op (aux0 b0 (aux0 b0 b1)) (aux0 a0 a1)) := by
  cases heq
theorem cp_8_2_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 a0 a1) = (op (aux1 b0 b1) (aux0 b0 b1))) :
    Join (aux0 a0 (aux0 a0 a1)) (op (aux1 a0 a1) (aux0 b0 (aux0 b0 b1))) := by
  cases heq
theorem cp_8_root_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux1 a0 a1) (aux0 a0 a1)) = (op (aux1 b0 b1) b0)) :
    Join (aux0 a0 (aux0 a0 a1)) (aux1 (aux1 b0 b1) (aux1 b0 b1)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst b0
  intro he0
  rcases T.aux1.inj he0 with ⟨he2, he3⟩
  clear he0
  revert he2
  subst a1
  intro he2
  have hsize := congrArg sz he2
  have hp_a0 := sz_pos a0
  have hp_b1 := sz_pos b1
  simp only [sz] at hsize
  omega
theorem cp_8_1_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (op (aux1 b0 b1) b0)) :
    Join (aux0 a0 (aux0 a0 a1)) (op (aux1 (aux1 b0 b1) (aux1 b0 b1)) (aux0 a0 a1)) := by
  cases heq
theorem cp_8_2_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 a0 a1) = (op (aux1 b0 b1) b0)) :
    Join (aux0 a0 (aux0 a0 a1)) (op (aux1 a0 a1) (aux1 (aux1 b0 b1) (aux1 b0 b1))) := by
  cases heq
theorem cp_8_root_10 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux1 a0 a1) (aux0 a0 a1)) = (op b0 (aux1 b0 b1))) :
    Join (aux0 a0 (aux0 a0 a1)) (aux0 (shared ) (aux1 b0 b1)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  cases he1
theorem cp_8_1_10 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (op b0 (aux1 b0 b1))) :
    Join (aux0 a0 (aux0 a0 a1)) (op (aux0 (shared ) (aux1 b0 b1)) (aux0 a0 a1)) := by
  cases heq
theorem cp_8_2_10 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 a0 a1) = (op b0 (aux1 b0 b1))) :
    Join (aux0 a0 (aux0 a0 a1)) (op (aux1 a0 a1) (aux0 (shared ) (aux1 b0 b1))) := by
  cases heq
theorem cp_8_root_11 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux1 a0 a1) (aux0 a0 a1)) = (aux0 (shared ) (aux1 (shared ) b0))) :
    Join (aux0 a0 (aux0 a0 a1)) (shared ) := by
  cases heq
theorem cp_8_1_11 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (aux0 (shared ) (aux1 (shared ) b0))) :
    Join (aux0 a0 (aux0 a0 a1)) (op (shared ) (aux0 a0 a1)) := by
  cases heq
theorem cp_8_2_11 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 a0 a1) = (aux0 (shared ) (aux1 (shared ) b0))) :
    Join (aux0 a0 (aux0 a0 a1)) (op (aux1 a0 a1) (shared )) := by
  rcases T.aux0.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  subst a0
  exact ⟨(shared ), (((Relation.ReflTransGen.refl).tail (Step.c_aux0_2 (shared ) (root_step .r11 b0 (leaf 0) (leaf 0)))).tail (root_step .r5 (leaf 0) (leaf 0) (leaf 0))), ((((Relation.ReflTransGen.refl).tail (root_step .r9 (shared ) (aux1 (shared ) b0) (leaf 0))).tail (Step.c_aux1_1 (aux1 (shared ) (aux1 (shared ) b0)) (root_step .r12 b0 (leaf 0) (leaf 0)))).tail (root_step .r12 (aux1 (shared ) b0) (leaf 0) (leaf 0)))⟩
theorem cp_8_root_12 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux1 a0 a1) (aux0 a0 a1)) = (aux1 (shared ) (aux1 (shared ) b0))) :
    Join (aux0 a0 (aux0 a0 a1)) (shared ) := by
  cases heq
theorem cp_8_1_12 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (aux1 (shared ) (aux1 (shared ) b0))) :
    Join (aux0 a0 (aux0 a0 a1)) (op (shared ) (aux0 a0 a1)) := by
  rcases T.aux1.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  subst a0
  exact ⟨(shared ), (((Relation.ReflTransGen.refl).tail (Step.c_aux0_2 (shared ) (root_step .r11 b0 (leaf 0) (leaf 0)))).tail (root_step .r5 (leaf 0) (leaf 0) (leaf 0))), ((((Relation.ReflTransGen.refl).tail (root_step .r2 (aux0 (shared ) (aux1 (shared ) b0)) (leaf 0) (leaf 0))).tail (root_step .r14 (aux1 (shared ) b0) (leaf 0) (leaf 0))).tail (root_step .r12 b0 (leaf 0) (leaf 0)))⟩
theorem cp_8_2_12 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 a0 a1) = (aux1 (shared ) (aux1 (shared ) b0))) :
    Join (aux0 a0 (aux0 a0 a1)) (op (aux1 a0 a1) (shared )) := by
  cases heq
theorem cp_8_root_13 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux1 a0 a1) (aux0 a0 a1)) = (op (aux1 (aux1 b0 b1) (aux1 b0 b1)) b0)) :
    Join (aux0 a0 (aux0 a0 a1)) (aux0 (aux1 b0 b1) b0) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst b0
  intro he0
  rcases T.aux1.inj he0 with ⟨he2, he3⟩
  clear he0
  have hsize := congrArg sz he3
  have hp_a0 := sz_pos a0
  have hp_a1 := sz_pos a1
  have hp_b1 := sz_pos b1
  simp only [sz] at hsize
  omega
theorem cp_8_1_13 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (op (aux1 (aux1 b0 b1) (aux1 b0 b1)) b0)) :
    Join (aux0 a0 (aux0 a0 a1)) (op (aux0 (aux1 b0 b1) b0) (aux0 a0 a1)) := by
  cases heq
theorem cp_8_2_13 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 a0 a1) = (op (aux1 (aux1 b0 b1) (aux1 b0 b1)) b0)) :
    Join (aux0 a0 (aux0 a0 a1)) (op (aux1 a0 a1) (aux0 (aux1 b0 b1) b0)) := by
  cases heq
theorem cp_8_root_14 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux1 a0 a1) (aux0 a0 a1)) = (aux0 (aux0 (shared ) b0) (aux0 (shared ) b0))) :
    Join (aux0 a0 (aux0 a0 a1)) (aux1 (shared ) b0) := by
  cases heq
theorem cp_8_1_14 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (aux0 (aux0 (shared ) b0) (aux0 (shared ) b0))) :
    Join (aux0 a0 (aux0 a0 a1)) (op (aux1 (shared ) b0) (aux0 a0 a1)) := by
  cases heq
theorem cp_8_2_14 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 a0 a1) = (aux0 (aux0 (shared ) b0) (aux0 (shared ) b0))) :
    Join (aux0 a0 (aux0 a0 a1)) (op (aux1 a0 a1) (aux1 (shared ) b0)) := by
  rcases T.aux0.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  subst a0
  exact ⟨(aux0 (aux0 (shared ) b0) (aux1 (shared ) b0)), ((Relation.ReflTransGen.refl).tail (Step.c_aux0_2 (aux0 (shared ) b0) (root_step .r14 b0 (leaf 0) (leaf 0)))), ((Relation.ReflTransGen.refl).tail (root_step .r16 b0 (leaf 0) (leaf 0)))⟩
theorem cp_8_root_15 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux1 a0 a1) (aux0 a0 a1)) = (op (aux0 (shared ) b0) (aux1 (shared ) b0))) :
    Join (aux0 a0 (aux0 a0 a1)) (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  cases he1
theorem cp_8_1_15 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (op (aux0 (shared ) b0) (aux1 (shared ) b0))) :
    Join (aux0 a0 (aux0 a0 a1)) (op (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) (aux0 a0 a1)) := by
  cases heq
theorem cp_8_2_15 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 a0 a1) = (op (aux0 (shared ) b0) (aux1 (shared ) b0))) :
    Join (aux0 a0 (aux0 a0 a1)) (op (aux1 a0 a1) (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0))) := by
  cases heq
theorem cp_8_root_16 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux1 a0 a1) (aux0 a0 a1)) = (op (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) (aux1 (shared ) b0))) :
    Join (aux0 a0 (aux0 a0 a1)) (aux0 (aux0 (shared ) b0) (aux1 (shared ) b0)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  cases he1
theorem cp_8_1_16 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (op (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) (aux1 (shared ) b0))) :
    Join (aux0 a0 (aux0 a0 a1)) (op (aux0 (aux0 (shared ) b0) (aux1 (shared ) b0)) (aux0 a0 a1)) := by
  cases heq
theorem cp_8_2_16 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 a0 a1) = (op (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) (aux1 (shared ) b0))) :
    Join (aux0 a0 (aux0 a0 a1)) (op (aux1 a0 a1) (aux0 (aux0 (shared ) b0) (aux1 (shared ) b0))) := by
  cases heq
theorem cp_9_root_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux1 a0 a1) a0) = (op b0 b0)) :
    Join (aux1 (aux1 a0 a1) (aux1 a0 a1)) (shared ) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  have hsize := congrArg sz he0
  have hp_a1 := sz_pos a1
  have hp_b0 := sz_pos b0
  simp only [sz] at hsize
  omega
theorem cp_9_1_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (op b0 b0)) :
    Join (aux1 (aux1 a0 a1) (aux1 a0 a1)) (op (shared ) a0) := by
  cases heq
theorem cp_9_root_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux1 a0 a1) a0) = (op (op b0 b1) b1)) :
    Join (aux1 (aux1 a0 a1) (aux1 a0 a1)) (aux0 b0 b1) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  cases he0
theorem cp_9_1_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (op (op b0 b1) b1)) :
    Join (aux1 (aux1 a0 a1) (aux1 a0 a1)) (op (aux0 b0 b1) a0) := by
  cases heq
theorem cp_9_root_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux1 a0 a1) a0) = (op (shared ) b0)) :
    Join (aux1 (aux1 a0 a1) (aux1 a0 a1)) (aux0 b0 b0) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  cases he0
theorem cp_9_1_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (op (shared ) b0)) :
    Join (aux1 (aux1 a0 a1) (aux1 a0 a1)) (op (aux0 b0 b0) a0) := by
  cases heq
theorem cp_9_root_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux1 a0 a1) a0) = (op b0 (aux0 b0 b1))) :
    Join (aux1 (aux1 a0 a1) (aux1 a0 a1)) (aux1 b0 b1) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  have hsize := congrArg sz he0
  have hp_a1 := sz_pos a1
  have hp_b0 := sz_pos b0
  have hp_b1 := sz_pos b1
  simp only [sz] at hsize
  omega
theorem cp_9_1_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (op b0 (aux0 b0 b1))) :
    Join (aux1 (aux1 a0 a1) (aux1 a0 a1)) (op (aux1 b0 b1) a0) := by
  cases heq
theorem cp_9_root_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux1 a0 a1) a0) = (op (aux0 b0 b1) b1)) :
    Join (aux1 (aux1 a0 a1) (aux1 a0 a1)) (aux0 (op b0 b1) b1) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  cases he0
theorem cp_9_1_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (op (aux0 b0 b1) b1)) :
    Join (aux1 (aux1 a0 a1) (aux1 a0 a1)) (op (aux0 (op b0 b1) b1) a0) := by
  cases heq
theorem cp_9_root_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux1 a0 a1) a0) = (aux0 (shared ) (shared ))) :
    Join (aux1 (aux1 a0 a1) (aux1 a0 a1)) (shared ) := by
  cases heq
theorem cp_9_1_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (aux0 (shared ) (shared ))) :
    Join (aux1 (aux1 a0 a1) (aux1 a0 a1)) (op (shared ) a0) := by
  cases heq
theorem cp_9_root_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux1 a0 a1) a0) = (aux1 (shared ) (shared ))) :
    Join (aux1 (aux1 a0 a1) (aux1 a0 a1)) (shared ) := by
  cases heq
theorem cp_9_1_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (aux1 (shared ) (shared ))) :
    Join (aux1 (aux1 a0 a1) (aux1 a0 a1)) (op (shared ) a0) := by
  rcases T.aux1.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  subst a0
  exact ⟨(shared ), (((Relation.ReflTransGen.refl).tail (Step.c_aux1_1 (aux1 (shared ) (shared )) (root_step .r6 (leaf 0) (leaf 0) (leaf 0)))).tail (root_step .r12 (shared ) (leaf 0) (leaf 0))), ((Relation.ReflTransGen.refl).tail (root_step .r0 (shared ) (leaf 0) (leaf 0)))⟩
theorem cp_9_root_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux1 a0 a1) a0) = (aux0 (aux1 b0 b1) (aux1 b0 b1))) :
    Join (aux1 (aux1 a0 a1) (aux1 a0 a1)) b0 := by
  cases heq
theorem cp_9_1_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (aux0 (aux1 b0 b1) (aux1 b0 b1))) :
    Join (aux1 (aux1 a0 a1) (aux1 a0 a1)) (op b0 a0) := by
  cases heq
theorem cp_9_root_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux1 a0 a1) a0) = (op (aux1 b0 b1) (aux0 b0 b1))) :
    Join (aux1 (aux1 a0 a1) (aux1 a0 a1)) (aux0 b0 (aux0 b0 b1)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  rcases T.aux1.inj he0 with ⟨he2, he3⟩
  clear he0
  revert he2
  subst a1
  intro he2
  have hsize := congrArg sz he2
  have hp_b0 := sz_pos b0
  have hp_b1 := sz_pos b1
  simp only [sz] at hsize
  omega
theorem cp_9_1_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (op (aux1 b0 b1) (aux0 b0 b1))) :
    Join (aux1 (aux1 a0 a1) (aux1 a0 a1)) (op (aux0 b0 (aux0 b0 b1)) a0) := by
  cases heq
theorem cp_9_root_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux1 a0 a1) a0) = (op (aux1 b0 b1) b0)) :
    Join (aux1 (aux1 a0 a1) (aux1 a0 a1)) (aux1 (aux1 b0 b1) (aux1 b0 b1)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  rcases T.aux1.inj he0 with ⟨he2, he3⟩
  clear he0
  revert he2
  subst a1
  intro he2
  clear he2
  exact ⟨(aux1 (aux1 b0 b1) (aux1 b0 b1)), (Relation.ReflTransGen.refl), (Relation.ReflTransGen.refl)⟩
theorem cp_9_1_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (op (aux1 b0 b1) b0)) :
    Join (aux1 (aux1 a0 a1) (aux1 a0 a1)) (op (aux1 (aux1 b0 b1) (aux1 b0 b1)) a0) := by
  cases heq
theorem cp_9_root_10 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux1 a0 a1) a0) = (op b0 (aux1 b0 b1))) :
    Join (aux1 (aux1 a0 a1) (aux1 a0 a1)) (aux0 (shared ) (aux1 b0 b1)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  have hsize := congrArg sz he0
  have hp_a1 := sz_pos a1
  have hp_b0 := sz_pos b0
  have hp_b1 := sz_pos b1
  simp only [sz] at hsize
  omega
theorem cp_9_1_10 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (op b0 (aux1 b0 b1))) :
    Join (aux1 (aux1 a0 a1) (aux1 a0 a1)) (op (aux0 (shared ) (aux1 b0 b1)) a0) := by
  cases heq
theorem cp_9_root_11 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux1 a0 a1) a0) = (aux0 (shared ) (aux1 (shared ) b0))) :
    Join (aux1 (aux1 a0 a1) (aux1 a0 a1)) (shared ) := by
  cases heq
theorem cp_9_1_11 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (aux0 (shared ) (aux1 (shared ) b0))) :
    Join (aux1 (aux1 a0 a1) (aux1 a0 a1)) (op (shared ) a0) := by
  cases heq
theorem cp_9_root_12 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux1 a0 a1) a0) = (aux1 (shared ) (aux1 (shared ) b0))) :
    Join (aux1 (aux1 a0 a1) (aux1 a0 a1)) (shared ) := by
  cases heq
theorem cp_9_1_12 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (aux1 (shared ) (aux1 (shared ) b0))) :
    Join (aux1 (aux1 a0 a1) (aux1 a0 a1)) (op (shared ) a0) := by
  rcases T.aux1.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  subst a0
  exact ⟨(shared ), (((Relation.ReflTransGen.refl).tail (Step.c_aux1_1 (aux1 (shared ) (aux1 (shared ) b0)) (root_step .r12 b0 (leaf 0) (leaf 0)))).tail (root_step .r12 (aux1 (shared ) b0) (leaf 0) (leaf 0))), ((Relation.ReflTransGen.refl).tail (root_step .r0 (shared ) (leaf 0) (leaf 0)))⟩
theorem cp_9_root_13 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux1 a0 a1) a0) = (op (aux1 (aux1 b0 b1) (aux1 b0 b1)) b0)) :
    Join (aux1 (aux1 a0 a1) (aux1 a0 a1)) (aux0 (aux1 b0 b1) b0) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  rcases T.aux1.inj he0 with ⟨he2, he3⟩
  clear he0
  revert he2
  subst a1
  intro he2
  have hsize := congrArg sz he2
  have hp_b0 := sz_pos b0
  have hp_b1 := sz_pos b1
  simp only [sz] at hsize
  omega
theorem cp_9_1_13 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (op (aux1 (aux1 b0 b1) (aux1 b0 b1)) b0)) :
    Join (aux1 (aux1 a0 a1) (aux1 a0 a1)) (op (aux0 (aux1 b0 b1) b0) a0) := by
  cases heq
theorem cp_9_root_14 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux1 a0 a1) a0) = (aux0 (aux0 (shared ) b0) (aux0 (shared ) b0))) :
    Join (aux1 (aux1 a0 a1) (aux1 a0 a1)) (aux1 (shared ) b0) := by
  cases heq
theorem cp_9_1_14 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (aux0 (aux0 (shared ) b0) (aux0 (shared ) b0))) :
    Join (aux1 (aux1 a0 a1) (aux1 a0 a1)) (op (aux1 (shared ) b0) a0) := by
  cases heq
theorem cp_9_root_15 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux1 a0 a1) a0) = (op (aux0 (shared ) b0) (aux1 (shared ) b0))) :
    Join (aux1 (aux1 a0 a1) (aux1 a0 a1)) (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  cases he0
theorem cp_9_1_15 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (op (aux0 (shared ) b0) (aux1 (shared ) b0))) :
    Join (aux1 (aux1 a0 a1) (aux1 a0 a1)) (op (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) a0) := by
  cases heq
theorem cp_9_root_16 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux1 a0 a1) a0) = (op (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) (aux1 (shared ) b0))) :
    Join (aux1 (aux1 a0 a1) (aux1 a0 a1)) (aux0 (aux0 (shared ) b0) (aux1 (shared ) b0)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  rcases T.aux1.inj he0 with ⟨he2, he3⟩
  clear he0
  revert he2
  subst a1
  intro he2
  cases he2
theorem cp_9_1_16 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (op (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) (aux1 (shared ) b0))) :
    Join (aux1 (aux1 a0 a1) (aux1 a0 a1)) (op (aux0 (aux0 (shared ) b0) (aux1 (shared ) b0)) a0) := by
  cases heq
theorem cp_10_root_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (aux1 a0 a1)) = (op b0 b0)) :
    Join (aux0 (shared ) (aux1 a0 a1)) (shared ) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst b0
  intro he0
  have hsize := congrArg sz he0
  have hp_a0 := sz_pos a0
  have hp_a1 := sz_pos a1
  simp only [sz] at hsize
  omega
theorem cp_10_2_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (op b0 b0)) :
    Join (aux0 (shared ) (aux1 a0 a1)) (op a0 (shared )) := by
  cases heq
theorem cp_10_root_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (aux1 a0 a1)) = (op (op b0 b1) b1)) :
    Join (aux0 (shared ) (aux1 a0 a1)) (aux0 b0 b1) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst b1
  intro he0
  have hsize := congrArg sz he0
  have hp_a0 := sz_pos a0
  have hp_a1 := sz_pos a1
  have hp_b0 := sz_pos b0
  simp only [sz] at hsize
  omega
theorem cp_10_2_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (op (op b0 b1) b1)) :
    Join (aux0 (shared ) (aux1 a0 a1)) (op a0 (aux0 b0 b1)) := by
  cases heq
theorem cp_10_root_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (aux1 a0 a1)) = (op (shared ) b0)) :
    Join (aux0 (shared ) (aux1 a0 a1)) (aux0 b0 b0) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst b0
  intro he0
  subst a0
  exact ⟨(shared ), ((Relation.ReflTransGen.refl).tail (root_step .r11 a1 (leaf 0) (leaf 0))), ((Relation.ReflTransGen.refl).tail (root_step .r7 (shared ) a1 (leaf 0)))⟩
theorem cp_10_2_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (op (shared ) b0)) :
    Join (aux0 (shared ) (aux1 a0 a1)) (op a0 (aux0 b0 b0)) := by
  cases heq
theorem cp_10_root_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (aux1 a0 a1)) = (op b0 (aux0 b0 b1))) :
    Join (aux0 (shared ) (aux1 a0 a1)) (aux1 b0 b1) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  cases he1
theorem cp_10_2_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (op b0 (aux0 b0 b1))) :
    Join (aux0 (shared ) (aux1 a0 a1)) (op a0 (aux1 b0 b1)) := by
  cases heq
theorem cp_10_root_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (aux1 a0 a1)) = (op (aux0 b0 b1) b1)) :
    Join (aux0 (shared ) (aux1 a0 a1)) (aux0 (op b0 b1) b1) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst b1
  intro he0
  have hsize := congrArg sz he0
  have hp_a0 := sz_pos a0
  have hp_a1 := sz_pos a1
  have hp_b0 := sz_pos b0
  simp only [sz] at hsize
  omega
theorem cp_10_2_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (op (aux0 b0 b1) b1)) :
    Join (aux0 (shared ) (aux1 a0 a1)) (op a0 (aux0 (op b0 b1) b1)) := by
  cases heq
theorem cp_10_root_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (aux1 a0 a1)) = (aux0 (shared ) (shared ))) :
    Join (aux0 (shared ) (aux1 a0 a1)) (shared ) := by
  cases heq
theorem cp_10_2_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (aux0 (shared ) (shared ))) :
    Join (aux0 (shared ) (aux1 a0 a1)) (op a0 (shared )) := by
  cases heq
theorem cp_10_root_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (aux1 a0 a1)) = (aux1 (shared ) (shared ))) :
    Join (aux0 (shared ) (aux1 a0 a1)) (shared ) := by
  cases heq
theorem cp_10_2_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (aux1 (shared ) (shared ))) :
    Join (aux0 (shared ) (aux1 a0 a1)) (op a0 (shared )) := by
  rcases T.aux1.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  subst a0
  exact ⟨(shared ), ((Relation.ReflTransGen.refl).tail (root_step .r11 (shared ) (leaf 0) (leaf 0))), ((Relation.ReflTransGen.refl).tail (root_step .r0 (shared ) (leaf 0) (leaf 0)))⟩
theorem cp_10_root_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (aux1 a0 a1)) = (aux0 (aux1 b0 b1) (aux1 b0 b1))) :
    Join (aux0 (shared ) (aux1 a0 a1)) b0 := by
  cases heq
theorem cp_10_2_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (aux0 (aux1 b0 b1) (aux1 b0 b1))) :
    Join (aux0 (shared ) (aux1 a0 a1)) (op a0 b0) := by
  cases heq
theorem cp_10_root_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (aux1 a0 a1)) = (op (aux1 b0 b1) (aux0 b0 b1))) :
    Join (aux0 (shared ) (aux1 a0 a1)) (aux0 b0 (aux0 b0 b1)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  cases he1
theorem cp_10_2_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (op (aux1 b0 b1) (aux0 b0 b1))) :
    Join (aux0 (shared ) (aux1 a0 a1)) (op a0 (aux0 b0 (aux0 b0 b1))) := by
  cases heq
theorem cp_10_root_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (aux1 a0 a1)) = (op (aux1 b0 b1) b0)) :
    Join (aux0 (shared ) (aux1 a0 a1)) (aux1 (aux1 b0 b1) (aux1 b0 b1)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst b0
  intro he0
  have hsize := congrArg sz he0
  have hp_a0 := sz_pos a0
  have hp_a1 := sz_pos a1
  have hp_b1 := sz_pos b1
  simp only [sz] at hsize
  omega
theorem cp_10_2_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (op (aux1 b0 b1) b0)) :
    Join (aux0 (shared ) (aux1 a0 a1)) (op a0 (aux1 (aux1 b0 b1) (aux1 b0 b1))) := by
  cases heq
theorem cp_10_root_10 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (aux1 a0 a1)) = (op b0 (aux1 b0 b1))) :
    Join (aux0 (shared ) (aux1 a0 a1)) (aux0 (shared ) (aux1 b0 b1)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  rcases T.aux1.inj he1 with ⟨he2, he3⟩
  clear he1
  revert he0 he2
  subst a1
  intro he0 he2
  revert he0
  subst a0
  intro he0
  clear he0
  exact ⟨(aux0 (shared ) (aux1 b0 b1)), (Relation.ReflTransGen.refl), (Relation.ReflTransGen.refl)⟩
theorem cp_10_2_10 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (op b0 (aux1 b0 b1))) :
    Join (aux0 (shared ) (aux1 a0 a1)) (op a0 (aux0 (shared ) (aux1 b0 b1))) := by
  cases heq
theorem cp_10_root_11 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (aux1 a0 a1)) = (aux0 (shared ) (aux1 (shared ) b0))) :
    Join (aux0 (shared ) (aux1 a0 a1)) (shared ) := by
  cases heq
theorem cp_10_2_11 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (aux0 (shared ) (aux1 (shared ) b0))) :
    Join (aux0 (shared ) (aux1 a0 a1)) (op a0 (shared )) := by
  cases heq
theorem cp_10_root_12 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (aux1 a0 a1)) = (aux1 (shared ) (aux1 (shared ) b0))) :
    Join (aux0 (shared ) (aux1 a0 a1)) (shared ) := by
  cases heq
theorem cp_10_2_12 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (aux1 (shared ) (aux1 (shared ) b0))) :
    Join (aux0 (shared ) (aux1 a0 a1)) (op a0 (shared )) := by
  rcases T.aux1.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  subst a0
  exact ⟨(shared ), ((Relation.ReflTransGen.refl).tail (root_step .r11 (aux1 (shared ) b0) (leaf 0) (leaf 0))), ((Relation.ReflTransGen.refl).tail (root_step .r0 (shared ) (leaf 0) (leaf 0)))⟩
theorem cp_10_root_13 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (aux1 a0 a1)) = (op (aux1 (aux1 b0 b1) (aux1 b0 b1)) b0)) :
    Join (aux0 (shared ) (aux1 a0 a1)) (aux0 (aux1 b0 b1) b0) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst b0
  intro he0
  have hsize := congrArg sz he0
  have hp_a0 := sz_pos a0
  have hp_a1 := sz_pos a1
  have hp_b1 := sz_pos b1
  simp only [sz] at hsize
  omega
theorem cp_10_2_13 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (op (aux1 (aux1 b0 b1) (aux1 b0 b1)) b0)) :
    Join (aux0 (shared ) (aux1 a0 a1)) (op a0 (aux0 (aux1 b0 b1) b0)) := by
  cases heq
theorem cp_10_root_14 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (aux1 a0 a1)) = (aux0 (aux0 (shared ) b0) (aux0 (shared ) b0))) :
    Join (aux0 (shared ) (aux1 a0 a1)) (aux1 (shared ) b0) := by
  cases heq
theorem cp_10_2_14 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (aux0 (aux0 (shared ) b0) (aux0 (shared ) b0))) :
    Join (aux0 (shared ) (aux1 a0 a1)) (op a0 (aux1 (shared ) b0)) := by
  cases heq
theorem cp_10_root_15 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (aux1 a0 a1)) = (op (aux0 (shared ) b0) (aux1 (shared ) b0))) :
    Join (aux0 (shared ) (aux1 a0 a1)) (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  rcases T.aux1.inj he1 with ⟨he2, he3⟩
  clear he1
  revert he0 he2
  subst a1
  intro he0 he2
  revert he0
  subst a0
  intro he0
  cases he0
theorem cp_10_2_15 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (op (aux0 (shared ) b0) (aux1 (shared ) b0))) :
    Join (aux0 (shared ) (aux1 a0 a1)) (op a0 (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0))) := by
  cases heq
theorem cp_10_root_16 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op a0 (aux1 a0 a1)) = (op (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) (aux1 (shared ) b0))) :
    Join (aux0 (shared ) (aux1 a0 a1)) (aux0 (aux0 (shared ) b0) (aux1 (shared ) b0)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  rcases T.aux1.inj he1 with ⟨he2, he3⟩
  clear he1
  revert he0 he2
  subst a1
  intro he0 he2
  revert he0
  subst a0
  intro he0
  cases he0
theorem cp_10_2_16 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (op (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) (aux1 (shared ) b0))) :
    Join (aux0 (shared ) (aux1 a0 a1)) (op a0 (aux0 (aux0 (shared ) b0) (aux1 (shared ) b0))) := by
  cases heq
theorem cp_11_root_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) (aux1 (shared ) a0)) = (op b0 b0)) :
    Join (shared ) (shared ) := by
  cases heq
theorem cp_11_1_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op b0 b0)) :
    Join (shared ) (aux0 (shared ) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_11_2_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) a0) = (op b0 b0)) :
    Join (shared ) (aux0 (shared ) (shared )) := by
  cases heq
theorem cp_11_2_1_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op b0 b0)) :
    Join (shared ) (aux0 (shared ) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_11_root_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) (aux1 (shared ) a0)) = (op (op b0 b1) b1)) :
    Join (shared ) (aux0 b0 b1) := by
  cases heq
theorem cp_11_1_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (op b0 b1) b1)) :
    Join (shared ) (aux0 (aux0 b0 b1) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_11_2_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) a0) = (op (op b0 b1) b1)) :
    Join (shared ) (aux0 (shared ) (aux0 b0 b1)) := by
  cases heq
theorem cp_11_2_1_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (op b0 b1) b1)) :
    Join (shared ) (aux0 (shared ) (aux1 (aux0 b0 b1) a0)) := by
  cases heq
theorem cp_11_root_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) (aux1 (shared ) a0)) = (op (shared ) b0)) :
    Join (shared ) (aux0 b0 b0) := by
  cases heq
theorem cp_11_1_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (shared ) b0)) :
    Join (shared ) (aux0 (aux0 b0 b0) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_11_2_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) a0) = (op (shared ) b0)) :
    Join (shared ) (aux0 (shared ) (aux0 b0 b0)) := by
  cases heq
theorem cp_11_2_1_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (shared ) b0)) :
    Join (shared ) (aux0 (shared ) (aux1 (aux0 b0 b0) a0)) := by
  cases heq
theorem cp_11_root_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) (aux1 (shared ) a0)) = (op b0 (aux0 b0 b1))) :
    Join (shared ) (aux1 b0 b1) := by
  cases heq
theorem cp_11_1_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op b0 (aux0 b0 b1))) :
    Join (shared ) (aux0 (aux1 b0 b1) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_11_2_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) a0) = (op b0 (aux0 b0 b1))) :
    Join (shared ) (aux0 (shared ) (aux1 b0 b1)) := by
  cases heq
theorem cp_11_2_1_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op b0 (aux0 b0 b1))) :
    Join (shared ) (aux0 (shared ) (aux1 (aux1 b0 b1) a0)) := by
  cases heq
theorem cp_11_root_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) (aux1 (shared ) a0)) = (op (aux0 b0 b1) b1)) :
    Join (shared ) (aux0 (op b0 b1) b1) := by
  cases heq
theorem cp_11_1_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux0 b0 b1) b1)) :
    Join (shared ) (aux0 (aux0 (op b0 b1) b1) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_11_2_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) a0) = (op (aux0 b0 b1) b1)) :
    Join (shared ) (aux0 (shared ) (aux0 (op b0 b1) b1)) := by
  cases heq
theorem cp_11_2_1_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux0 b0 b1) b1)) :
    Join (shared ) (aux0 (shared ) (aux1 (aux0 (op b0 b1) b1) a0)) := by
  cases heq
theorem cp_11_root_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) (aux1 (shared ) a0)) = (aux0 (shared ) (shared ))) :
    Join (shared ) (shared ) := by
  rcases T.aux0.inj heq with ⟨he0, he1⟩
  clear heq
  cases he1
theorem cp_11_1_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux0 (shared ) (shared ))) :
    Join (shared ) (aux0 (shared ) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_11_2_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) a0) = (aux0 (shared ) (shared ))) :
    Join (shared ) (aux0 (shared ) (shared )) := by
  cases heq
theorem cp_11_2_1_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux0 (shared ) (shared ))) :
    Join (shared ) (aux0 (shared ) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_11_root_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) (aux1 (shared ) a0)) = (aux1 (shared ) (shared ))) :
    Join (shared ) (shared ) := by
  cases heq
theorem cp_11_1_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux1 (shared ) (shared ))) :
    Join (shared ) (aux0 (shared ) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_11_2_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) a0) = (aux1 (shared ) (shared ))) :
    Join (shared ) (aux0 (shared ) (shared )) := by
  rcases T.aux1.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  clear he0
  exact ⟨(shared ), (Relation.ReflTransGen.refl), ((Relation.ReflTransGen.refl).tail (root_step .r5 (leaf 0) (leaf 0) (leaf 0)))⟩
theorem cp_11_2_1_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux1 (shared ) (shared ))) :
    Join (shared ) (aux0 (shared ) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_11_root_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) (aux1 (shared ) a0)) = (aux0 (aux1 b0 b1) (aux1 b0 b1))) :
    Join (shared ) b0 := by
  rcases T.aux0.inj heq with ⟨he0, he1⟩
  clear heq
  rcases T.aux1.inj he1 with ⟨he2, he3⟩
  clear he1
  revert he0 he2
  subst a0
  intro he0 he2
  revert he0
  subst b0
  intro he0
  cases he0
theorem cp_11_1_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux0 (aux1 b0 b1) (aux1 b0 b1))) :
    Join (shared ) (aux0 b0 (aux1 (shared ) a0)) := by
  cases heq
theorem cp_11_2_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) a0) = (aux0 (aux1 b0 b1) (aux1 b0 b1))) :
    Join (shared ) (aux0 (shared ) b0) := by
  cases heq
theorem cp_11_2_1_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux0 (aux1 b0 b1) (aux1 b0 b1))) :
    Join (shared ) (aux0 (shared ) (aux1 b0 a0)) := by
  cases heq
theorem cp_11_root_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) (aux1 (shared ) a0)) = (op (aux1 b0 b1) (aux0 b0 b1))) :
    Join (shared ) (aux0 b0 (aux0 b0 b1)) := by
  cases heq
theorem cp_11_1_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux1 b0 b1) (aux0 b0 b1))) :
    Join (shared ) (aux0 (aux0 b0 (aux0 b0 b1)) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_11_2_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) a0) = (op (aux1 b0 b1) (aux0 b0 b1))) :
    Join (shared ) (aux0 (shared ) (aux0 b0 (aux0 b0 b1))) := by
  cases heq
theorem cp_11_2_1_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux1 b0 b1) (aux0 b0 b1))) :
    Join (shared ) (aux0 (shared ) (aux1 (aux0 b0 (aux0 b0 b1)) a0)) := by
  cases heq
theorem cp_11_root_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) (aux1 (shared ) a0)) = (op (aux1 b0 b1) b0)) :
    Join (shared ) (aux1 (aux1 b0 b1) (aux1 b0 b1)) := by
  cases heq
theorem cp_11_1_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux1 b0 b1) b0)) :
    Join (shared ) (aux0 (aux1 (aux1 b0 b1) (aux1 b0 b1)) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_11_2_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) a0) = (op (aux1 b0 b1) b0)) :
    Join (shared ) (aux0 (shared ) (aux1 (aux1 b0 b1) (aux1 b0 b1))) := by
  cases heq
theorem cp_11_2_1_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux1 b0 b1) b0)) :
    Join (shared ) (aux0 (shared ) (aux1 (aux1 (aux1 b0 b1) (aux1 b0 b1)) a0)) := by
  cases heq
theorem cp_11_root_10 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) (aux1 (shared ) a0)) = (op b0 (aux1 b0 b1))) :
    Join (shared ) (aux0 (shared ) (aux1 b0 b1)) := by
  cases heq
theorem cp_11_1_10 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op b0 (aux1 b0 b1))) :
    Join (shared ) (aux0 (aux0 (shared ) (aux1 b0 b1)) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_11_2_10 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) a0) = (op b0 (aux1 b0 b1))) :
    Join (shared ) (aux0 (shared ) (aux0 (shared ) (aux1 b0 b1))) := by
  cases heq
theorem cp_11_2_1_10 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op b0 (aux1 b0 b1))) :
    Join (shared ) (aux0 (shared ) (aux1 (aux0 (shared ) (aux1 b0 b1)) a0)) := by
  cases heq
theorem cp_11_root_11 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) (aux1 (shared ) a0)) = (aux0 (shared ) (aux1 (shared ) b0))) :
    Join (shared ) (shared ) := by
  rcases T.aux0.inj heq with ⟨he0, he1⟩
  clear heq
  rcases T.aux1.inj he1 with ⟨he2, he3⟩
  clear he1
  revert he0 he2
  subst a0
  intro he0 he2
  clear he2
  clear he0
  exact ⟨(shared ), (Relation.ReflTransGen.refl), (Relation.ReflTransGen.refl)⟩
theorem cp_11_1_11 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux0 (shared ) (aux1 (shared ) b0))) :
    Join (shared ) (aux0 (shared ) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_11_2_11 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) a0) = (aux0 (shared ) (aux1 (shared ) b0))) :
    Join (shared ) (aux0 (shared ) (shared )) := by
  cases heq
theorem cp_11_2_1_11 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux0 (shared ) (aux1 (shared ) b0))) :
    Join (shared ) (aux0 (shared ) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_11_root_12 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) (aux1 (shared ) a0)) = (aux1 (shared ) (aux1 (shared ) b0))) :
    Join (shared ) (shared ) := by
  cases heq
theorem cp_11_1_12 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux1 (shared ) (aux1 (shared ) b0))) :
    Join (shared ) (aux0 (shared ) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_11_2_12 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) a0) = (aux1 (shared ) (aux1 (shared ) b0))) :
    Join (shared ) (aux0 (shared ) (shared )) := by
  rcases T.aux1.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  clear he0
  exact ⟨(shared ), (Relation.ReflTransGen.refl), ((Relation.ReflTransGen.refl).tail (root_step .r5 (leaf 0) (leaf 0) (leaf 0)))⟩
theorem cp_11_2_1_12 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux1 (shared ) (aux1 (shared ) b0))) :
    Join (shared ) (aux0 (shared ) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_11_root_13 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) (aux1 (shared ) a0)) = (op (aux1 (aux1 b0 b1) (aux1 b0 b1)) b0)) :
    Join (shared ) (aux0 (aux1 b0 b1) b0) := by
  cases heq
theorem cp_11_1_13 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux1 (aux1 b0 b1) (aux1 b0 b1)) b0)) :
    Join (shared ) (aux0 (aux0 (aux1 b0 b1) b0) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_11_2_13 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) a0) = (op (aux1 (aux1 b0 b1) (aux1 b0 b1)) b0)) :
    Join (shared ) (aux0 (shared ) (aux0 (aux1 b0 b1) b0)) := by
  cases heq
theorem cp_11_2_1_13 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux1 (aux1 b0 b1) (aux1 b0 b1)) b0)) :
    Join (shared ) (aux0 (shared ) (aux1 (aux0 (aux1 b0 b1) b0) a0)) := by
  cases heq
theorem cp_11_root_14 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) (aux1 (shared ) a0)) = (aux0 (aux0 (shared ) b0) (aux0 (shared ) b0))) :
    Join (shared ) (aux1 (shared ) b0) := by
  rcases T.aux0.inj heq with ⟨he0, he1⟩
  clear heq
  cases he1
theorem cp_11_1_14 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux0 (aux0 (shared ) b0) (aux0 (shared ) b0))) :
    Join (shared ) (aux0 (aux1 (shared ) b0) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_11_2_14 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) a0) = (aux0 (aux0 (shared ) b0) (aux0 (shared ) b0))) :
    Join (shared ) (aux0 (shared ) (aux1 (shared ) b0)) := by
  cases heq
theorem cp_11_2_1_14 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux0 (aux0 (shared ) b0) (aux0 (shared ) b0))) :
    Join (shared ) (aux0 (shared ) (aux1 (aux1 (shared ) b0) a0)) := by
  cases heq
theorem cp_11_root_15 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) (aux1 (shared ) a0)) = (op (aux0 (shared ) b0) (aux1 (shared ) b0))) :
    Join (shared ) (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) := by
  cases heq
theorem cp_11_1_15 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux0 (shared ) b0) (aux1 (shared ) b0))) :
    Join (shared ) (aux0 (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_11_2_15 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) a0) = (op (aux0 (shared ) b0) (aux1 (shared ) b0))) :
    Join (shared ) (aux0 (shared ) (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0))) := by
  cases heq
theorem cp_11_2_1_15 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux0 (shared ) b0) (aux1 (shared ) b0))) :
    Join (shared ) (aux0 (shared ) (aux1 (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) a0)) := by
  cases heq
theorem cp_11_root_16 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) (aux1 (shared ) a0)) = (op (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) (aux1 (shared ) b0))) :
    Join (shared ) (aux0 (aux0 (shared ) b0) (aux1 (shared ) b0)) := by
  cases heq
theorem cp_11_1_16 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) (aux1 (shared ) b0))) :
    Join (shared ) (aux0 (aux0 (aux0 (shared ) b0) (aux1 (shared ) b0)) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_11_2_16 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) a0) = (op (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) (aux1 (shared ) b0))) :
    Join (shared ) (aux0 (shared ) (aux0 (aux0 (shared ) b0) (aux1 (shared ) b0))) := by
  cases heq
theorem cp_11_2_1_16 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) (aux1 (shared ) b0))) :
    Join (shared ) (aux0 (shared ) (aux1 (aux0 (aux0 (shared ) b0) (aux1 (shared ) b0)) a0)) := by
  cases heq
theorem cp_12_root_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) (aux1 (shared ) a0)) = (op b0 b0)) :
    Join (shared ) (shared ) := by
  cases heq
theorem cp_12_1_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op b0 b0)) :
    Join (shared ) (aux1 (shared ) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_12_2_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) a0) = (op b0 b0)) :
    Join (shared ) (aux1 (shared ) (shared )) := by
  cases heq
theorem cp_12_2_1_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op b0 b0)) :
    Join (shared ) (aux1 (shared ) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_12_root_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) (aux1 (shared ) a0)) = (op (op b0 b1) b1)) :
    Join (shared ) (aux0 b0 b1) := by
  cases heq
theorem cp_12_1_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (op b0 b1) b1)) :
    Join (shared ) (aux1 (aux0 b0 b1) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_12_2_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) a0) = (op (op b0 b1) b1)) :
    Join (shared ) (aux1 (shared ) (aux0 b0 b1)) := by
  cases heq
theorem cp_12_2_1_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (op b0 b1) b1)) :
    Join (shared ) (aux1 (shared ) (aux1 (aux0 b0 b1) a0)) := by
  cases heq
theorem cp_12_root_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) (aux1 (shared ) a0)) = (op (shared ) b0)) :
    Join (shared ) (aux0 b0 b0) := by
  cases heq
theorem cp_12_1_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (shared ) b0)) :
    Join (shared ) (aux1 (aux0 b0 b0) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_12_2_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) a0) = (op (shared ) b0)) :
    Join (shared ) (aux1 (shared ) (aux0 b0 b0)) := by
  cases heq
theorem cp_12_2_1_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (shared ) b0)) :
    Join (shared ) (aux1 (shared ) (aux1 (aux0 b0 b0) a0)) := by
  cases heq
theorem cp_12_root_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) (aux1 (shared ) a0)) = (op b0 (aux0 b0 b1))) :
    Join (shared ) (aux1 b0 b1) := by
  cases heq
theorem cp_12_1_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op b0 (aux0 b0 b1))) :
    Join (shared ) (aux1 (aux1 b0 b1) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_12_2_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) a0) = (op b0 (aux0 b0 b1))) :
    Join (shared ) (aux1 (shared ) (aux1 b0 b1)) := by
  cases heq
theorem cp_12_2_1_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op b0 (aux0 b0 b1))) :
    Join (shared ) (aux1 (shared ) (aux1 (aux1 b0 b1) a0)) := by
  cases heq
theorem cp_12_root_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) (aux1 (shared ) a0)) = (op (aux0 b0 b1) b1)) :
    Join (shared ) (aux0 (op b0 b1) b1) := by
  cases heq
theorem cp_12_1_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux0 b0 b1) b1)) :
    Join (shared ) (aux1 (aux0 (op b0 b1) b1) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_12_2_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) a0) = (op (aux0 b0 b1) b1)) :
    Join (shared ) (aux1 (shared ) (aux0 (op b0 b1) b1)) := by
  cases heq
theorem cp_12_2_1_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux0 b0 b1) b1)) :
    Join (shared ) (aux1 (shared ) (aux1 (aux0 (op b0 b1) b1) a0)) := by
  cases heq
theorem cp_12_root_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) (aux1 (shared ) a0)) = (aux0 (shared ) (shared ))) :
    Join (shared ) (shared ) := by
  cases heq
theorem cp_12_1_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux0 (shared ) (shared ))) :
    Join (shared ) (aux1 (shared ) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_12_2_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) a0) = (aux0 (shared ) (shared ))) :
    Join (shared ) (aux1 (shared ) (shared )) := by
  cases heq
theorem cp_12_2_1_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux0 (shared ) (shared ))) :
    Join (shared ) (aux1 (shared ) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_12_root_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) (aux1 (shared ) a0)) = (aux1 (shared ) (shared ))) :
    Join (shared ) (shared ) := by
  rcases T.aux1.inj heq with ⟨he0, he1⟩
  clear heq
  cases he1
theorem cp_12_1_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux1 (shared ) (shared ))) :
    Join (shared ) (aux1 (shared ) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_12_2_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) a0) = (aux1 (shared ) (shared ))) :
    Join (shared ) (aux1 (shared ) (shared )) := by
  rcases T.aux1.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  clear he0
  exact ⟨(shared ), (Relation.ReflTransGen.refl), ((Relation.ReflTransGen.refl).tail (root_step .r6 (leaf 0) (leaf 0) (leaf 0)))⟩
theorem cp_12_2_1_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux1 (shared ) (shared ))) :
    Join (shared ) (aux1 (shared ) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_12_root_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) (aux1 (shared ) a0)) = (aux0 (aux1 b0 b1) (aux1 b0 b1))) :
    Join (shared ) b0 := by
  cases heq
theorem cp_12_1_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux0 (aux1 b0 b1) (aux1 b0 b1))) :
    Join (shared ) (aux1 b0 (aux1 (shared ) a0)) := by
  cases heq
theorem cp_12_2_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) a0) = (aux0 (aux1 b0 b1) (aux1 b0 b1))) :
    Join (shared ) (aux1 (shared ) b0) := by
  cases heq
theorem cp_12_2_1_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux0 (aux1 b0 b1) (aux1 b0 b1))) :
    Join (shared ) (aux1 (shared ) (aux1 b0 a0)) := by
  cases heq
theorem cp_12_root_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) (aux1 (shared ) a0)) = (op (aux1 b0 b1) (aux0 b0 b1))) :
    Join (shared ) (aux0 b0 (aux0 b0 b1)) := by
  cases heq
theorem cp_12_1_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux1 b0 b1) (aux0 b0 b1))) :
    Join (shared ) (aux1 (aux0 b0 (aux0 b0 b1)) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_12_2_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) a0) = (op (aux1 b0 b1) (aux0 b0 b1))) :
    Join (shared ) (aux1 (shared ) (aux0 b0 (aux0 b0 b1))) := by
  cases heq
theorem cp_12_2_1_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux1 b0 b1) (aux0 b0 b1))) :
    Join (shared ) (aux1 (shared ) (aux1 (aux0 b0 (aux0 b0 b1)) a0)) := by
  cases heq
theorem cp_12_root_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) (aux1 (shared ) a0)) = (op (aux1 b0 b1) b0)) :
    Join (shared ) (aux1 (aux1 b0 b1) (aux1 b0 b1)) := by
  cases heq
theorem cp_12_1_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux1 b0 b1) b0)) :
    Join (shared ) (aux1 (aux1 (aux1 b0 b1) (aux1 b0 b1)) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_12_2_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) a0) = (op (aux1 b0 b1) b0)) :
    Join (shared ) (aux1 (shared ) (aux1 (aux1 b0 b1) (aux1 b0 b1))) := by
  cases heq
theorem cp_12_2_1_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux1 b0 b1) b0)) :
    Join (shared ) (aux1 (shared ) (aux1 (aux1 (aux1 b0 b1) (aux1 b0 b1)) a0)) := by
  cases heq
theorem cp_12_root_10 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) (aux1 (shared ) a0)) = (op b0 (aux1 b0 b1))) :
    Join (shared ) (aux0 (shared ) (aux1 b0 b1)) := by
  cases heq
theorem cp_12_1_10 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op b0 (aux1 b0 b1))) :
    Join (shared ) (aux1 (aux0 (shared ) (aux1 b0 b1)) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_12_2_10 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) a0) = (op b0 (aux1 b0 b1))) :
    Join (shared ) (aux1 (shared ) (aux0 (shared ) (aux1 b0 b1))) := by
  cases heq
theorem cp_12_2_1_10 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op b0 (aux1 b0 b1))) :
    Join (shared ) (aux1 (shared ) (aux1 (aux0 (shared ) (aux1 b0 b1)) a0)) := by
  cases heq
theorem cp_12_root_11 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) (aux1 (shared ) a0)) = (aux0 (shared ) (aux1 (shared ) b0))) :
    Join (shared ) (shared ) := by
  cases heq
theorem cp_12_1_11 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux0 (shared ) (aux1 (shared ) b0))) :
    Join (shared ) (aux1 (shared ) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_12_2_11 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) a0) = (aux0 (shared ) (aux1 (shared ) b0))) :
    Join (shared ) (aux1 (shared ) (shared )) := by
  cases heq
theorem cp_12_2_1_11 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux0 (shared ) (aux1 (shared ) b0))) :
    Join (shared ) (aux1 (shared ) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_12_root_12 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) (aux1 (shared ) a0)) = (aux1 (shared ) (aux1 (shared ) b0))) :
    Join (shared ) (shared ) := by
  rcases T.aux1.inj heq with ⟨he0, he1⟩
  clear heq
  rcases T.aux1.inj he1 with ⟨he2, he3⟩
  clear he1
  revert he0 he2
  subst a0
  intro he0 he2
  clear he2
  clear he0
  exact ⟨(shared ), (Relation.ReflTransGen.refl), (Relation.ReflTransGen.refl)⟩
theorem cp_12_1_12 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux1 (shared ) (aux1 (shared ) b0))) :
    Join (shared ) (aux1 (shared ) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_12_2_12 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) a0) = (aux1 (shared ) (aux1 (shared ) b0))) :
    Join (shared ) (aux1 (shared ) (shared )) := by
  rcases T.aux1.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  clear he0
  exact ⟨(shared ), (Relation.ReflTransGen.refl), ((Relation.ReflTransGen.refl).tail (root_step .r6 (leaf 0) (leaf 0) (leaf 0)))⟩
theorem cp_12_2_1_12 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux1 (shared ) (aux1 (shared ) b0))) :
    Join (shared ) (aux1 (shared ) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_12_root_13 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) (aux1 (shared ) a0)) = (op (aux1 (aux1 b0 b1) (aux1 b0 b1)) b0)) :
    Join (shared ) (aux0 (aux1 b0 b1) b0) := by
  cases heq
theorem cp_12_1_13 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux1 (aux1 b0 b1) (aux1 b0 b1)) b0)) :
    Join (shared ) (aux1 (aux0 (aux1 b0 b1) b0) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_12_2_13 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) a0) = (op (aux1 (aux1 b0 b1) (aux1 b0 b1)) b0)) :
    Join (shared ) (aux1 (shared ) (aux0 (aux1 b0 b1) b0)) := by
  cases heq
theorem cp_12_2_1_13 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux1 (aux1 b0 b1) (aux1 b0 b1)) b0)) :
    Join (shared ) (aux1 (shared ) (aux1 (aux0 (aux1 b0 b1) b0) a0)) := by
  cases heq
theorem cp_12_root_14 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) (aux1 (shared ) a0)) = (aux0 (aux0 (shared ) b0) (aux0 (shared ) b0))) :
    Join (shared ) (aux1 (shared ) b0) := by
  cases heq
theorem cp_12_1_14 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux0 (aux0 (shared ) b0) (aux0 (shared ) b0))) :
    Join (shared ) (aux1 (aux1 (shared ) b0) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_12_2_14 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) a0) = (aux0 (aux0 (shared ) b0) (aux0 (shared ) b0))) :
    Join (shared ) (aux1 (shared ) (aux1 (shared ) b0)) := by
  cases heq
theorem cp_12_2_1_14 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux0 (aux0 (shared ) b0) (aux0 (shared ) b0))) :
    Join (shared ) (aux1 (shared ) (aux1 (aux1 (shared ) b0) a0)) := by
  cases heq
theorem cp_12_root_15 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) (aux1 (shared ) a0)) = (op (aux0 (shared ) b0) (aux1 (shared ) b0))) :
    Join (shared ) (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) := by
  cases heq
theorem cp_12_1_15 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux0 (shared ) b0) (aux1 (shared ) b0))) :
    Join (shared ) (aux1 (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_12_2_15 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) a0) = (op (aux0 (shared ) b0) (aux1 (shared ) b0))) :
    Join (shared ) (aux1 (shared ) (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0))) := by
  cases heq
theorem cp_12_2_1_15 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux0 (shared ) b0) (aux1 (shared ) b0))) :
    Join (shared ) (aux1 (shared ) (aux1 (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) a0)) := by
  cases heq
theorem cp_12_root_16 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) (aux1 (shared ) a0)) = (op (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) (aux1 (shared ) b0))) :
    Join (shared ) (aux0 (aux0 (shared ) b0) (aux1 (shared ) b0)) := by
  cases heq
theorem cp_12_1_16 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) (aux1 (shared ) b0))) :
    Join (shared ) (aux1 (aux0 (aux0 (shared ) b0) (aux1 (shared ) b0)) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_12_2_16 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) a0) = (op (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) (aux1 (shared ) b0))) :
    Join (shared ) (aux1 (shared ) (aux0 (aux0 (shared ) b0) (aux1 (shared ) b0))) := by
  cases heq
theorem cp_12_2_1_16 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) (aux1 (shared ) b0))) :
    Join (shared ) (aux1 (shared ) (aux1 (aux0 (aux0 (shared ) b0) (aux1 (shared ) b0)) a0)) := by
  cases heq
theorem cp_13_root_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux1 (aux1 a0 a1) (aux1 a0 a1)) a0) = (op b0 b0)) :
    Join (aux0 (aux1 a0 a1) a0) (shared ) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  have hsize := congrArg sz he0
  have hp_a1 := sz_pos a1
  have hp_b0 := sz_pos b0
  simp only [sz] at hsize
  omega
theorem cp_13_1_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (aux1 a0 a1) (aux1 a0 a1)) = (op b0 b0)) :
    Join (aux0 (aux1 a0 a1) a0) (op (shared ) a0) := by
  cases heq
theorem cp_13_1_1_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (op b0 b0)) :
    Join (aux0 (aux1 a0 a1) a0) (op (aux1 (shared ) (aux1 a0 a1)) a0) := by
  cases heq
theorem cp_13_1_2_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (op b0 b0)) :
    Join (aux0 (aux1 a0 a1) a0) (op (aux1 (aux1 a0 a1) (shared )) a0) := by
  cases heq
theorem cp_13_root_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux1 (aux1 a0 a1) (aux1 a0 a1)) a0) = (op (op b0 b1) b1)) :
    Join (aux0 (aux1 a0 a1) a0) (aux0 b0 b1) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  cases he0
theorem cp_13_1_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (aux1 a0 a1) (aux1 a0 a1)) = (op (op b0 b1) b1)) :
    Join (aux0 (aux1 a0 a1) a0) (op (aux0 b0 b1) a0) := by
  cases heq
theorem cp_13_1_1_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (op (op b0 b1) b1)) :
    Join (aux0 (aux1 a0 a1) a0) (op (aux1 (aux0 b0 b1) (aux1 a0 a1)) a0) := by
  cases heq
theorem cp_13_1_2_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (op (op b0 b1) b1)) :
    Join (aux0 (aux1 a0 a1) a0) (op (aux1 (aux1 a0 a1) (aux0 b0 b1)) a0) := by
  cases heq
theorem cp_13_root_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux1 (aux1 a0 a1) (aux1 a0 a1)) a0) = (op (shared ) b0)) :
    Join (aux0 (aux1 a0 a1) a0) (aux0 b0 b0) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  cases he0
theorem cp_13_1_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (aux1 a0 a1) (aux1 a0 a1)) = (op (shared ) b0)) :
    Join (aux0 (aux1 a0 a1) a0) (op (aux0 b0 b0) a0) := by
  cases heq
theorem cp_13_1_1_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (op (shared ) b0)) :
    Join (aux0 (aux1 a0 a1) a0) (op (aux1 (aux0 b0 b0) (aux1 a0 a1)) a0) := by
  cases heq
theorem cp_13_1_2_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (op (shared ) b0)) :
    Join (aux0 (aux1 a0 a1) a0) (op (aux1 (aux1 a0 a1) (aux0 b0 b0)) a0) := by
  cases heq
theorem cp_13_root_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux1 (aux1 a0 a1) (aux1 a0 a1)) a0) = (op b0 (aux0 b0 b1))) :
    Join (aux0 (aux1 a0 a1) a0) (aux1 b0 b1) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  have hsize := congrArg sz he0
  have hp_a1 := sz_pos a1
  have hp_b0 := sz_pos b0
  have hp_b1 := sz_pos b1
  simp only [sz] at hsize
  omega
theorem cp_13_1_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (aux1 a0 a1) (aux1 a0 a1)) = (op b0 (aux0 b0 b1))) :
    Join (aux0 (aux1 a0 a1) a0) (op (aux1 b0 b1) a0) := by
  cases heq
theorem cp_13_1_1_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (op b0 (aux0 b0 b1))) :
    Join (aux0 (aux1 a0 a1) a0) (op (aux1 (aux1 b0 b1) (aux1 a0 a1)) a0) := by
  cases heq
theorem cp_13_1_2_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (op b0 (aux0 b0 b1))) :
    Join (aux0 (aux1 a0 a1) a0) (op (aux1 (aux1 a0 a1) (aux1 b0 b1)) a0) := by
  cases heq
theorem cp_13_root_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux1 (aux1 a0 a1) (aux1 a0 a1)) a0) = (op (aux0 b0 b1) b1)) :
    Join (aux0 (aux1 a0 a1) a0) (aux0 (op b0 b1) b1) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  cases he0
theorem cp_13_1_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (aux1 a0 a1) (aux1 a0 a1)) = (op (aux0 b0 b1) b1)) :
    Join (aux0 (aux1 a0 a1) a0) (op (aux0 (op b0 b1) b1) a0) := by
  cases heq
theorem cp_13_1_1_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (op (aux0 b0 b1) b1)) :
    Join (aux0 (aux1 a0 a1) a0) (op (aux1 (aux0 (op b0 b1) b1) (aux1 a0 a1)) a0) := by
  cases heq
theorem cp_13_1_2_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (op (aux0 b0 b1) b1)) :
    Join (aux0 (aux1 a0 a1) a0) (op (aux1 (aux1 a0 a1) (aux0 (op b0 b1) b1)) a0) := by
  cases heq
theorem cp_13_root_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux1 (aux1 a0 a1) (aux1 a0 a1)) a0) = (aux0 (shared ) (shared ))) :
    Join (aux0 (aux1 a0 a1) a0) (shared ) := by
  cases heq
theorem cp_13_1_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (aux1 a0 a1) (aux1 a0 a1)) = (aux0 (shared ) (shared ))) :
    Join (aux0 (aux1 a0 a1) a0) (op (shared ) a0) := by
  cases heq
theorem cp_13_1_1_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (aux0 (shared ) (shared ))) :
    Join (aux0 (aux1 a0 a1) a0) (op (aux1 (shared ) (aux1 a0 a1)) a0) := by
  cases heq
theorem cp_13_1_2_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (aux0 (shared ) (shared ))) :
    Join (aux0 (aux1 a0 a1) a0) (op (aux1 (aux1 a0 a1) (shared )) a0) := by
  cases heq
theorem cp_13_root_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux1 (aux1 a0 a1) (aux1 a0 a1)) a0) = (aux1 (shared ) (shared ))) :
    Join (aux0 (aux1 a0 a1) a0) (shared ) := by
  cases heq
theorem cp_13_1_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (aux1 a0 a1) (aux1 a0 a1)) = (aux1 (shared ) (shared ))) :
    Join (aux0 (aux1 a0 a1) a0) (op (shared ) a0) := by
  rcases T.aux1.inj heq with ⟨he0, he1⟩
  clear heq
  cases he1
theorem cp_13_1_1_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (aux1 (shared ) (shared ))) :
    Join (aux0 (aux1 a0 a1) a0) (op (aux1 (shared ) (aux1 a0 a1)) a0) := by
  rcases T.aux1.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  subst a0
  exact ⟨(shared ), (((Relation.ReflTransGen.refl).tail (Step.c_aux0_1 (shared ) (root_step .r6 (leaf 0) (leaf 0) (leaf 0)))).tail (root_step .r5 (leaf 0) (leaf 0) (leaf 0))), ((((Relation.ReflTransGen.refl).tail (root_step .r9 (shared ) (aux1 (shared ) (shared )) (leaf 0))).tail (Step.c_aux1_1 (aux1 (shared ) (aux1 (shared ) (shared ))) (root_step .r12 (shared ) (leaf 0) (leaf 0)))).tail (root_step .r12 (aux1 (shared ) (shared )) (leaf 0) (leaf 0)))⟩
theorem cp_13_1_2_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (aux1 (shared ) (shared ))) :
    Join (aux0 (aux1 a0 a1) a0) (op (aux1 (aux1 a0 a1) (shared )) a0) := by
  rcases T.aux1.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  subst a0
  exact ⟨(shared ), (((Relation.ReflTransGen.refl).tail (Step.c_aux0_1 (shared ) (root_step .r6 (leaf 0) (leaf 0) (leaf 0)))).tail (root_step .r5 (leaf 0) (leaf 0) (leaf 0))), (((((Relation.ReflTransGen.refl).tail (Step.c_op_1 (shared ) (Step.c_aux1_1 (shared ) (root_step .r6 (leaf 0) (leaf 0) (leaf 0))))).tail (root_step .r9 (shared ) (shared ) (leaf 0))).tail (Step.c_aux1_1 (aux1 (shared ) (shared )) (root_step .r6 (leaf 0) (leaf 0) (leaf 0)))).tail (root_step .r12 (shared ) (leaf 0) (leaf 0)))⟩
theorem cp_13_root_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux1 (aux1 a0 a1) (aux1 a0 a1)) a0) = (aux0 (aux1 b0 b1) (aux1 b0 b1))) :
    Join (aux0 (aux1 a0 a1) a0) b0 := by
  cases heq
theorem cp_13_1_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (aux1 a0 a1) (aux1 a0 a1)) = (aux0 (aux1 b0 b1) (aux1 b0 b1))) :
    Join (aux0 (aux1 a0 a1) a0) (op b0 a0) := by
  cases heq
theorem cp_13_1_1_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (aux0 (aux1 b0 b1) (aux1 b0 b1))) :
    Join (aux0 (aux1 a0 a1) a0) (op (aux1 b0 (aux1 a0 a1)) a0) := by
  cases heq
theorem cp_13_1_2_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (aux0 (aux1 b0 b1) (aux1 b0 b1))) :
    Join (aux0 (aux1 a0 a1) a0) (op (aux1 (aux1 a0 a1) b0) a0) := by
  cases heq
theorem cp_13_root_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux1 (aux1 a0 a1) (aux1 a0 a1)) a0) = (op (aux1 b0 b1) (aux0 b0 b1))) :
    Join (aux0 (aux1 a0 a1) a0) (aux0 b0 (aux0 b0 b1)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  rcases T.aux1.inj he0 with ⟨he2, he3⟩
  clear he0
  have hsize := congrArg sz he3
  have hp_a1 := sz_pos a1
  have hp_b0 := sz_pos b0
  have hp_b1 := sz_pos b1
  simp only [sz] at hsize
  omega
theorem cp_13_1_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (aux1 a0 a1) (aux1 a0 a1)) = (op (aux1 b0 b1) (aux0 b0 b1))) :
    Join (aux0 (aux1 a0 a1) a0) (op (aux0 b0 (aux0 b0 b1)) a0) := by
  cases heq
theorem cp_13_1_1_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (op (aux1 b0 b1) (aux0 b0 b1))) :
    Join (aux0 (aux1 a0 a1) a0) (op (aux1 (aux0 b0 (aux0 b0 b1)) (aux1 a0 a1)) a0) := by
  cases heq
theorem cp_13_1_2_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (op (aux1 b0 b1) (aux0 b0 b1))) :
    Join (aux0 (aux1 a0 a1) a0) (op (aux1 (aux1 a0 a1) (aux0 b0 (aux0 b0 b1))) a0) := by
  cases heq
theorem cp_13_root_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux1 (aux1 a0 a1) (aux1 a0 a1)) a0) = (op (aux1 b0 b1) b0)) :
    Join (aux0 (aux1 a0 a1) a0) (aux1 (aux1 b0 b1) (aux1 b0 b1)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  rcases T.aux1.inj he0 with ⟨he2, he3⟩
  clear he0
  revert he2
  subst b1
  intro he2
  have hsize := congrArg sz he2
  have hp_a1 := sz_pos a1
  have hp_b0 := sz_pos b0
  simp only [sz] at hsize
  omega
theorem cp_13_1_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (aux1 a0 a1) (aux1 a0 a1)) = (op (aux1 b0 b1) b0)) :
    Join (aux0 (aux1 a0 a1) a0) (op (aux1 (aux1 b0 b1) (aux1 b0 b1)) a0) := by
  cases heq
theorem cp_13_1_1_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (op (aux1 b0 b1) b0)) :
    Join (aux0 (aux1 a0 a1) a0) (op (aux1 (aux1 (aux1 b0 b1) (aux1 b0 b1)) (aux1 a0 a1)) a0) := by
  cases heq
theorem cp_13_1_2_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (op (aux1 b0 b1) b0)) :
    Join (aux0 (aux1 a0 a1) a0) (op (aux1 (aux1 a0 a1) (aux1 (aux1 b0 b1) (aux1 b0 b1))) a0) := by
  cases heq
theorem cp_13_root_10 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux1 (aux1 a0 a1) (aux1 a0 a1)) a0) = (op b0 (aux1 b0 b1))) :
    Join (aux0 (aux1 a0 a1) a0) (aux0 (shared ) (aux1 b0 b1)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  have hsize := congrArg sz he0
  have hp_a1 := sz_pos a1
  have hp_b0 := sz_pos b0
  have hp_b1 := sz_pos b1
  simp only [sz] at hsize
  omega
theorem cp_13_1_10 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (aux1 a0 a1) (aux1 a0 a1)) = (op b0 (aux1 b0 b1))) :
    Join (aux0 (aux1 a0 a1) a0) (op (aux0 (shared ) (aux1 b0 b1)) a0) := by
  cases heq
theorem cp_13_1_1_10 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (op b0 (aux1 b0 b1))) :
    Join (aux0 (aux1 a0 a1) a0) (op (aux1 (aux0 (shared ) (aux1 b0 b1)) (aux1 a0 a1)) a0) := by
  cases heq
theorem cp_13_1_2_10 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (op b0 (aux1 b0 b1))) :
    Join (aux0 (aux1 a0 a1) a0) (op (aux1 (aux1 a0 a1) (aux0 (shared ) (aux1 b0 b1))) a0) := by
  cases heq
theorem cp_13_root_11 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux1 (aux1 a0 a1) (aux1 a0 a1)) a0) = (aux0 (shared ) (aux1 (shared ) b0))) :
    Join (aux0 (aux1 a0 a1) a0) (shared ) := by
  cases heq
theorem cp_13_1_11 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (aux1 a0 a1) (aux1 a0 a1)) = (aux0 (shared ) (aux1 (shared ) b0))) :
    Join (aux0 (aux1 a0 a1) a0) (op (shared ) a0) := by
  cases heq
theorem cp_13_1_1_11 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (aux0 (shared ) (aux1 (shared ) b0))) :
    Join (aux0 (aux1 a0 a1) a0) (op (aux1 (shared ) (aux1 a0 a1)) a0) := by
  cases heq
theorem cp_13_1_2_11 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (aux0 (shared ) (aux1 (shared ) b0))) :
    Join (aux0 (aux1 a0 a1) a0) (op (aux1 (aux1 a0 a1) (shared )) a0) := by
  cases heq
theorem cp_13_root_12 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux1 (aux1 a0 a1) (aux1 a0 a1)) a0) = (aux1 (shared ) (aux1 (shared ) b0))) :
    Join (aux0 (aux1 a0 a1) a0) (shared ) := by
  cases heq
theorem cp_13_1_12 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (aux1 a0 a1) (aux1 a0 a1)) = (aux1 (shared ) (aux1 (shared ) b0))) :
    Join (aux0 (aux1 a0 a1) a0) (op (shared ) a0) := by
  rcases T.aux1.inj heq with ⟨he0, he1⟩
  clear heq
  rcases T.aux1.inj he1 with ⟨he2, he3⟩
  clear he1
  revert he0 he2
  subst a1
  intro he0 he2
  revert he0
  subst a0
  intro he0
  cases he0
theorem cp_13_1_1_12 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (aux1 (shared ) (aux1 (shared ) b0))) :
    Join (aux0 (aux1 a0 a1) a0) (op (aux1 (shared ) (aux1 a0 a1)) a0) := by
  rcases T.aux1.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  subst a0
  exact ⟨(shared ), (((Relation.ReflTransGen.refl).tail (Step.c_aux0_1 (shared ) (root_step .r12 b0 (leaf 0) (leaf 0)))).tail (root_step .r5 (leaf 0) (leaf 0) (leaf 0))), ((((Relation.ReflTransGen.refl).tail (root_step .r9 (shared ) (aux1 (shared ) (aux1 (shared ) b0)) (leaf 0))).tail (Step.c_aux1_1 (aux1 (shared ) (aux1 (shared ) (aux1 (shared ) b0))) (root_step .r12 (aux1 (shared ) b0) (leaf 0) (leaf 0)))).tail (root_step .r12 (aux1 (shared ) (aux1 (shared ) b0)) (leaf 0) (leaf 0)))⟩
theorem cp_13_1_2_12 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (aux1 (shared ) (aux1 (shared ) b0))) :
    Join (aux0 (aux1 a0 a1) a0) (op (aux1 (aux1 a0 a1) (shared )) a0) := by
  rcases T.aux1.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  subst a0
  exact ⟨(shared ), (((Relation.ReflTransGen.refl).tail (Step.c_aux0_1 (shared ) (root_step .r12 b0 (leaf 0) (leaf 0)))).tail (root_step .r5 (leaf 0) (leaf 0) (leaf 0))), (((((Relation.ReflTransGen.refl).tail (Step.c_op_1 (shared ) (Step.c_aux1_1 (shared ) (root_step .r12 b0 (leaf 0) (leaf 0))))).tail (root_step .r9 (shared ) (shared ) (leaf 0))).tail (Step.c_aux1_1 (aux1 (shared ) (shared )) (root_step .r6 (leaf 0) (leaf 0) (leaf 0)))).tail (root_step .r12 (shared ) (leaf 0) (leaf 0)))⟩
theorem cp_13_root_13 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux1 (aux1 a0 a1) (aux1 a0 a1)) a0) = (op (aux1 (aux1 b0 b1) (aux1 b0 b1)) b0)) :
    Join (aux0 (aux1 a0 a1) a0) (aux0 (aux1 b0 b1) b0) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  rcases T.aux1.inj he0 with ⟨he2, he3⟩
  clear he0
  rcases T.aux1.inj he3 with ⟨he4, he5⟩
  clear he3
  revert he2 he4
  subst a1
  intro he2 he4
  clear he4
  clear he2
  exact ⟨(aux0 (aux1 b0 b1) b0), (Relation.ReflTransGen.refl), (Relation.ReflTransGen.refl)⟩
theorem cp_13_1_13 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (aux1 a0 a1) (aux1 a0 a1)) = (op (aux1 (aux1 b0 b1) (aux1 b0 b1)) b0)) :
    Join (aux0 (aux1 a0 a1) a0) (op (aux0 (aux1 b0 b1) b0) a0) := by
  cases heq
theorem cp_13_1_1_13 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (op (aux1 (aux1 b0 b1) (aux1 b0 b1)) b0)) :
    Join (aux0 (aux1 a0 a1) a0) (op (aux1 (aux0 (aux1 b0 b1) b0) (aux1 a0 a1)) a0) := by
  cases heq
theorem cp_13_1_2_13 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (op (aux1 (aux1 b0 b1) (aux1 b0 b1)) b0)) :
    Join (aux0 (aux1 a0 a1) a0) (op (aux1 (aux1 a0 a1) (aux0 (aux1 b0 b1) b0)) a0) := by
  cases heq
theorem cp_13_root_14 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux1 (aux1 a0 a1) (aux1 a0 a1)) a0) = (aux0 (aux0 (shared ) b0) (aux0 (shared ) b0))) :
    Join (aux0 (aux1 a0 a1) a0) (aux1 (shared ) b0) := by
  cases heq
theorem cp_13_1_14 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (aux1 a0 a1) (aux1 a0 a1)) = (aux0 (aux0 (shared ) b0) (aux0 (shared ) b0))) :
    Join (aux0 (aux1 a0 a1) a0) (op (aux1 (shared ) b0) a0) := by
  cases heq
theorem cp_13_1_1_14 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (aux0 (aux0 (shared ) b0) (aux0 (shared ) b0))) :
    Join (aux0 (aux1 a0 a1) a0) (op (aux1 (aux1 (shared ) b0) (aux1 a0 a1)) a0) := by
  cases heq
theorem cp_13_1_2_14 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (aux0 (aux0 (shared ) b0) (aux0 (shared ) b0))) :
    Join (aux0 (aux1 a0 a1) a0) (op (aux1 (aux1 a0 a1) (aux1 (shared ) b0)) a0) := by
  cases heq
theorem cp_13_root_15 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux1 (aux1 a0 a1) (aux1 a0 a1)) a0) = (op (aux0 (shared ) b0) (aux1 (shared ) b0))) :
    Join (aux0 (aux1 a0 a1) a0) (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  cases he0
theorem cp_13_1_15 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (aux1 a0 a1) (aux1 a0 a1)) = (op (aux0 (shared ) b0) (aux1 (shared ) b0))) :
    Join (aux0 (aux1 a0 a1) a0) (op (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) a0) := by
  cases heq
theorem cp_13_1_1_15 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (op (aux0 (shared ) b0) (aux1 (shared ) b0))) :
    Join (aux0 (aux1 a0 a1) a0) (op (aux1 (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) (aux1 a0 a1)) a0) := by
  cases heq
theorem cp_13_1_2_15 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (op (aux0 (shared ) b0) (aux1 (shared ) b0))) :
    Join (aux0 (aux1 a0 a1) a0) (op (aux1 (aux1 a0 a1) (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0))) a0) := by
  cases heq
theorem cp_13_root_16 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux1 (aux1 a0 a1) (aux1 a0 a1)) a0) = (op (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) (aux1 (shared ) b0))) :
    Join (aux0 (aux1 a0 a1) a0) (aux0 (aux0 (shared ) b0) (aux1 (shared ) b0)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  rcases T.aux1.inj he0 with ⟨he2, he3⟩
  clear he0
  cases he3
theorem cp_13_1_16 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (aux1 a0 a1) (aux1 a0 a1)) = (op (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) (aux1 (shared ) b0))) :
    Join (aux0 (aux1 a0 a1) a0) (op (aux0 (aux0 (shared ) b0) (aux1 (shared ) b0)) a0) := by
  cases heq
theorem cp_13_1_1_16 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (op (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) (aux1 (shared ) b0))) :
    Join (aux0 (aux1 a0 a1) a0) (op (aux1 (aux0 (aux0 (shared ) b0) (aux1 (shared ) b0)) (aux1 a0 a1)) a0) := by
  cases heq
theorem cp_13_1_2_16 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 a0 a1) = (op (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) (aux1 (shared ) b0))) :
    Join (aux0 (aux1 a0 a1) a0) (op (aux1 (aux1 a0 a1) (aux0 (aux0 (shared ) b0) (aux1 (shared ) b0))) a0) := by
  cases heq
theorem cp_14_root_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (aux0 (shared ) a0) (aux0 (shared ) a0)) = (op b0 b0)) :
    Join (aux1 (shared ) a0) (shared ) := by
  cases heq
theorem cp_14_1_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (op b0 b0)) :
    Join (aux1 (shared ) a0) (aux0 (shared ) (aux0 (shared ) a0)) := by
  cases heq
theorem cp_14_1_1_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op b0 b0)) :
    Join (aux1 (shared ) a0) (aux0 (aux0 (shared ) a0) (aux0 (shared ) a0)) := by
  cases heq
theorem cp_14_2_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (op b0 b0)) :
    Join (aux1 (shared ) a0) (aux0 (aux0 (shared ) a0) (shared )) := by
  cases heq
theorem cp_14_2_1_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op b0 b0)) :
    Join (aux1 (shared ) a0) (aux0 (aux0 (shared ) a0) (aux0 (shared ) a0)) := by
  cases heq
theorem cp_14_root_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (aux0 (shared ) a0) (aux0 (shared ) a0)) = (op (op b0 b1) b1)) :
    Join (aux1 (shared ) a0) (aux0 b0 b1) := by
  cases heq
theorem cp_14_1_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (op (op b0 b1) b1)) :
    Join (aux1 (shared ) a0) (aux0 (aux0 b0 b1) (aux0 (shared ) a0)) := by
  cases heq
theorem cp_14_1_1_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (op b0 b1) b1)) :
    Join (aux1 (shared ) a0) (aux0 (aux0 (aux0 b0 b1) a0) (aux0 (shared ) a0)) := by
  cases heq
theorem cp_14_2_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (op (op b0 b1) b1)) :
    Join (aux1 (shared ) a0) (aux0 (aux0 (shared ) a0) (aux0 b0 b1)) := by
  cases heq
theorem cp_14_2_1_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (op b0 b1) b1)) :
    Join (aux1 (shared ) a0) (aux0 (aux0 (shared ) a0) (aux0 (aux0 b0 b1) a0)) := by
  cases heq
theorem cp_14_root_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (aux0 (shared ) a0) (aux0 (shared ) a0)) = (op (shared ) b0)) :
    Join (aux1 (shared ) a0) (aux0 b0 b0) := by
  cases heq
theorem cp_14_1_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (op (shared ) b0)) :
    Join (aux1 (shared ) a0) (aux0 (aux0 b0 b0) (aux0 (shared ) a0)) := by
  cases heq
theorem cp_14_1_1_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (shared ) b0)) :
    Join (aux1 (shared ) a0) (aux0 (aux0 (aux0 b0 b0) a0) (aux0 (shared ) a0)) := by
  cases heq
theorem cp_14_2_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (op (shared ) b0)) :
    Join (aux1 (shared ) a0) (aux0 (aux0 (shared ) a0) (aux0 b0 b0)) := by
  cases heq
theorem cp_14_2_1_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (shared ) b0)) :
    Join (aux1 (shared ) a0) (aux0 (aux0 (shared ) a0) (aux0 (aux0 b0 b0) a0)) := by
  cases heq
theorem cp_14_root_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (aux0 (shared ) a0) (aux0 (shared ) a0)) = (op b0 (aux0 b0 b1))) :
    Join (aux1 (shared ) a0) (aux1 b0 b1) := by
  cases heq
theorem cp_14_1_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (op b0 (aux0 b0 b1))) :
    Join (aux1 (shared ) a0) (aux0 (aux1 b0 b1) (aux0 (shared ) a0)) := by
  cases heq
theorem cp_14_1_1_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op b0 (aux0 b0 b1))) :
    Join (aux1 (shared ) a0) (aux0 (aux0 (aux1 b0 b1) a0) (aux0 (shared ) a0)) := by
  cases heq
theorem cp_14_2_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (op b0 (aux0 b0 b1))) :
    Join (aux1 (shared ) a0) (aux0 (aux0 (shared ) a0) (aux1 b0 b1)) := by
  cases heq
theorem cp_14_2_1_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op b0 (aux0 b0 b1))) :
    Join (aux1 (shared ) a0) (aux0 (aux0 (shared ) a0) (aux0 (aux1 b0 b1) a0)) := by
  cases heq
theorem cp_14_root_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (aux0 (shared ) a0) (aux0 (shared ) a0)) = (op (aux0 b0 b1) b1)) :
    Join (aux1 (shared ) a0) (aux0 (op b0 b1) b1) := by
  cases heq
theorem cp_14_1_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (op (aux0 b0 b1) b1)) :
    Join (aux1 (shared ) a0) (aux0 (aux0 (op b0 b1) b1) (aux0 (shared ) a0)) := by
  cases heq
theorem cp_14_1_1_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux0 b0 b1) b1)) :
    Join (aux1 (shared ) a0) (aux0 (aux0 (aux0 (op b0 b1) b1) a0) (aux0 (shared ) a0)) := by
  cases heq
theorem cp_14_2_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (op (aux0 b0 b1) b1)) :
    Join (aux1 (shared ) a0) (aux0 (aux0 (shared ) a0) (aux0 (op b0 b1) b1)) := by
  cases heq
theorem cp_14_2_1_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux0 b0 b1) b1)) :
    Join (aux1 (shared ) a0) (aux0 (aux0 (shared ) a0) (aux0 (aux0 (op b0 b1) b1) a0)) := by
  cases heq
theorem cp_14_root_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (aux0 (shared ) a0) (aux0 (shared ) a0)) = (aux0 (shared ) (shared ))) :
    Join (aux1 (shared ) a0) (shared ) := by
  rcases T.aux0.inj heq with ⟨he0, he1⟩
  clear heq
  cases he1
theorem cp_14_1_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (aux0 (shared ) (shared ))) :
    Join (aux1 (shared ) a0) (aux0 (shared ) (aux0 (shared ) a0)) := by
  rcases T.aux0.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  clear he0
  exact ⟨(shared ), ((Relation.ReflTransGen.refl).tail (root_step .r6 (leaf 0) (leaf 0) (leaf 0))), (((Relation.ReflTransGen.refl).tail (Step.c_aux0_2 (shared ) (root_step .r5 (leaf 0) (leaf 0) (leaf 0)))).tail (root_step .r5 (leaf 0) (leaf 0) (leaf 0)))⟩
theorem cp_14_1_1_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux0 (shared ) (shared ))) :
    Join (aux1 (shared ) a0) (aux0 (aux0 (shared ) a0) (aux0 (shared ) a0)) := by
  cases heq
theorem cp_14_2_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (aux0 (shared ) (shared ))) :
    Join (aux1 (shared ) a0) (aux0 (aux0 (shared ) a0) (shared )) := by
  rcases T.aux0.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  clear he0
  exact ⟨(shared ), ((Relation.ReflTransGen.refl).tail (root_step .r6 (leaf 0) (leaf 0) (leaf 0))), (((Relation.ReflTransGen.refl).tail (Step.c_aux0_1 (shared ) (root_step .r5 (leaf 0) (leaf 0) (leaf 0)))).tail (root_step .r5 (leaf 0) (leaf 0) (leaf 0)))⟩
theorem cp_14_2_1_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux0 (shared ) (shared ))) :
    Join (aux1 (shared ) a0) (aux0 (aux0 (shared ) a0) (aux0 (shared ) a0)) := by
  cases heq
theorem cp_14_root_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (aux0 (shared ) a0) (aux0 (shared ) a0)) = (aux1 (shared ) (shared ))) :
    Join (aux1 (shared ) a0) (shared ) := by
  cases heq
theorem cp_14_1_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (aux1 (shared ) (shared ))) :
    Join (aux1 (shared ) a0) (aux0 (shared ) (aux0 (shared ) a0)) := by
  cases heq
theorem cp_14_1_1_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux1 (shared ) (shared ))) :
    Join (aux1 (shared ) a0) (aux0 (aux0 (shared ) a0) (aux0 (shared ) a0)) := by
  cases heq
theorem cp_14_2_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (aux1 (shared ) (shared ))) :
    Join (aux1 (shared ) a0) (aux0 (aux0 (shared ) a0) (shared )) := by
  cases heq
theorem cp_14_2_1_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux1 (shared ) (shared ))) :
    Join (aux1 (shared ) a0) (aux0 (aux0 (shared ) a0) (aux0 (shared ) a0)) := by
  cases heq
theorem cp_14_root_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (aux0 (shared ) a0) (aux0 (shared ) a0)) = (aux0 (aux1 b0 b1) (aux1 b0 b1))) :
    Join (aux1 (shared ) a0) b0 := by
  rcases T.aux0.inj heq with ⟨he0, he1⟩
  clear heq
  cases he1
theorem cp_14_1_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (aux0 (aux1 b0 b1) (aux1 b0 b1))) :
    Join (aux1 (shared ) a0) (aux0 b0 (aux0 (shared ) a0)) := by
  rcases T.aux0.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  cases he0
theorem cp_14_1_1_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux0 (aux1 b0 b1) (aux1 b0 b1))) :
    Join (aux1 (shared ) a0) (aux0 (aux0 b0 a0) (aux0 (shared ) a0)) := by
  cases heq
theorem cp_14_2_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (aux0 (aux1 b0 b1) (aux1 b0 b1))) :
    Join (aux1 (shared ) a0) (aux0 (aux0 (shared ) a0) b0) := by
  rcases T.aux0.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  cases he0
theorem cp_14_2_1_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux0 (aux1 b0 b1) (aux1 b0 b1))) :
    Join (aux1 (shared ) a0) (aux0 (aux0 (shared ) a0) (aux0 b0 a0)) := by
  cases heq
theorem cp_14_root_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (aux0 (shared ) a0) (aux0 (shared ) a0)) = (op (aux1 b0 b1) (aux0 b0 b1))) :
    Join (aux1 (shared ) a0) (aux0 b0 (aux0 b0 b1)) := by
  cases heq
theorem cp_14_1_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (op (aux1 b0 b1) (aux0 b0 b1))) :
    Join (aux1 (shared ) a0) (aux0 (aux0 b0 (aux0 b0 b1)) (aux0 (shared ) a0)) := by
  cases heq
theorem cp_14_1_1_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux1 b0 b1) (aux0 b0 b1))) :
    Join (aux1 (shared ) a0) (aux0 (aux0 (aux0 b0 (aux0 b0 b1)) a0) (aux0 (shared ) a0)) := by
  cases heq
theorem cp_14_2_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (op (aux1 b0 b1) (aux0 b0 b1))) :
    Join (aux1 (shared ) a0) (aux0 (aux0 (shared ) a0) (aux0 b0 (aux0 b0 b1))) := by
  cases heq
theorem cp_14_2_1_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux1 b0 b1) (aux0 b0 b1))) :
    Join (aux1 (shared ) a0) (aux0 (aux0 (shared ) a0) (aux0 (aux0 b0 (aux0 b0 b1)) a0)) := by
  cases heq
theorem cp_14_root_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (aux0 (shared ) a0) (aux0 (shared ) a0)) = (op (aux1 b0 b1) b0)) :
    Join (aux1 (shared ) a0) (aux1 (aux1 b0 b1) (aux1 b0 b1)) := by
  cases heq
theorem cp_14_1_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (op (aux1 b0 b1) b0)) :
    Join (aux1 (shared ) a0) (aux0 (aux1 (aux1 b0 b1) (aux1 b0 b1)) (aux0 (shared ) a0)) := by
  cases heq
theorem cp_14_1_1_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux1 b0 b1) b0)) :
    Join (aux1 (shared ) a0) (aux0 (aux0 (aux1 (aux1 b0 b1) (aux1 b0 b1)) a0) (aux0 (shared ) a0)) := by
  cases heq
theorem cp_14_2_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (op (aux1 b0 b1) b0)) :
    Join (aux1 (shared ) a0) (aux0 (aux0 (shared ) a0) (aux1 (aux1 b0 b1) (aux1 b0 b1))) := by
  cases heq
theorem cp_14_2_1_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux1 b0 b1) b0)) :
    Join (aux1 (shared ) a0) (aux0 (aux0 (shared ) a0) (aux0 (aux1 (aux1 b0 b1) (aux1 b0 b1)) a0)) := by
  cases heq
theorem cp_14_root_10 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (aux0 (shared ) a0) (aux0 (shared ) a0)) = (op b0 (aux1 b0 b1))) :
    Join (aux1 (shared ) a0) (aux0 (shared ) (aux1 b0 b1)) := by
  cases heq
theorem cp_14_1_10 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (op b0 (aux1 b0 b1))) :
    Join (aux1 (shared ) a0) (aux0 (aux0 (shared ) (aux1 b0 b1)) (aux0 (shared ) a0)) := by
  cases heq
theorem cp_14_1_1_10 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op b0 (aux1 b0 b1))) :
    Join (aux1 (shared ) a0) (aux0 (aux0 (aux0 (shared ) (aux1 b0 b1)) a0) (aux0 (shared ) a0)) := by
  cases heq
theorem cp_14_2_10 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (op b0 (aux1 b0 b1))) :
    Join (aux1 (shared ) a0) (aux0 (aux0 (shared ) a0) (aux0 (shared ) (aux1 b0 b1))) := by
  cases heq
theorem cp_14_2_1_10 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op b0 (aux1 b0 b1))) :
    Join (aux1 (shared ) a0) (aux0 (aux0 (shared ) a0) (aux0 (aux0 (shared ) (aux1 b0 b1)) a0)) := by
  cases heq
theorem cp_14_root_11 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (aux0 (shared ) a0) (aux0 (shared ) a0)) = (aux0 (shared ) (aux1 (shared ) b0))) :
    Join (aux1 (shared ) a0) (shared ) := by
  rcases T.aux0.inj heq with ⟨he0, he1⟩
  clear heq
  cases he1
theorem cp_14_1_11 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (aux0 (shared ) (aux1 (shared ) b0))) :
    Join (aux1 (shared ) a0) (aux0 (shared ) (aux0 (shared ) a0)) := by
  rcases T.aux0.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  clear he0
  exact ⟨(shared ), ((Relation.ReflTransGen.refl).tail (root_step .r12 b0 (leaf 0) (leaf 0))), (((Relation.ReflTransGen.refl).tail (Step.c_aux0_2 (shared ) (root_step .r11 b0 (leaf 0) (leaf 0)))).tail (root_step .r5 (leaf 0) (leaf 0) (leaf 0)))⟩
theorem cp_14_1_1_11 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux0 (shared ) (aux1 (shared ) b0))) :
    Join (aux1 (shared ) a0) (aux0 (aux0 (shared ) a0) (aux0 (shared ) a0)) := by
  cases heq
theorem cp_14_2_11 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (aux0 (shared ) (aux1 (shared ) b0))) :
    Join (aux1 (shared ) a0) (aux0 (aux0 (shared ) a0) (shared )) := by
  rcases T.aux0.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  clear he0
  exact ⟨(shared ), ((Relation.ReflTransGen.refl).tail (root_step .r12 b0 (leaf 0) (leaf 0))), (((Relation.ReflTransGen.refl).tail (Step.c_aux0_1 (shared ) (root_step .r11 b0 (leaf 0) (leaf 0)))).tail (root_step .r5 (leaf 0) (leaf 0) (leaf 0)))⟩
theorem cp_14_2_1_11 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux0 (shared ) (aux1 (shared ) b0))) :
    Join (aux1 (shared ) a0) (aux0 (aux0 (shared ) a0) (aux0 (shared ) a0)) := by
  cases heq
theorem cp_14_root_12 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (aux0 (shared ) a0) (aux0 (shared ) a0)) = (aux1 (shared ) (aux1 (shared ) b0))) :
    Join (aux1 (shared ) a0) (shared ) := by
  cases heq
theorem cp_14_1_12 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (aux1 (shared ) (aux1 (shared ) b0))) :
    Join (aux1 (shared ) a0) (aux0 (shared ) (aux0 (shared ) a0)) := by
  cases heq
theorem cp_14_1_1_12 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux1 (shared ) (aux1 (shared ) b0))) :
    Join (aux1 (shared ) a0) (aux0 (aux0 (shared ) a0) (aux0 (shared ) a0)) := by
  cases heq
theorem cp_14_2_12 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (aux1 (shared ) (aux1 (shared ) b0))) :
    Join (aux1 (shared ) a0) (aux0 (aux0 (shared ) a0) (shared )) := by
  cases heq
theorem cp_14_2_1_12 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux1 (shared ) (aux1 (shared ) b0))) :
    Join (aux1 (shared ) a0) (aux0 (aux0 (shared ) a0) (aux0 (shared ) a0)) := by
  cases heq
theorem cp_14_root_13 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (aux0 (shared ) a0) (aux0 (shared ) a0)) = (op (aux1 (aux1 b0 b1) (aux1 b0 b1)) b0)) :
    Join (aux1 (shared ) a0) (aux0 (aux1 b0 b1) b0) := by
  cases heq
theorem cp_14_1_13 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (op (aux1 (aux1 b0 b1) (aux1 b0 b1)) b0)) :
    Join (aux1 (shared ) a0) (aux0 (aux0 (aux1 b0 b1) b0) (aux0 (shared ) a0)) := by
  cases heq
theorem cp_14_1_1_13 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux1 (aux1 b0 b1) (aux1 b0 b1)) b0)) :
    Join (aux1 (shared ) a0) (aux0 (aux0 (aux0 (aux1 b0 b1) b0) a0) (aux0 (shared ) a0)) := by
  cases heq
theorem cp_14_2_13 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (op (aux1 (aux1 b0 b1) (aux1 b0 b1)) b0)) :
    Join (aux1 (shared ) a0) (aux0 (aux0 (shared ) a0) (aux0 (aux1 b0 b1) b0)) := by
  cases heq
theorem cp_14_2_1_13 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux1 (aux1 b0 b1) (aux1 b0 b1)) b0)) :
    Join (aux1 (shared ) a0) (aux0 (aux0 (shared ) a0) (aux0 (aux0 (aux1 b0 b1) b0) a0)) := by
  cases heq
theorem cp_14_root_14 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (aux0 (shared ) a0) (aux0 (shared ) a0)) = (aux0 (aux0 (shared ) b0) (aux0 (shared ) b0))) :
    Join (aux1 (shared ) a0) (aux1 (shared ) b0) := by
  rcases T.aux0.inj heq with ⟨he0, he1⟩
  clear heq
  rcases T.aux0.inj he1 with ⟨he2, he3⟩
  clear he1
  revert he0 he2
  subst a0
  intro he0 he2
  clear he2
  clear he0
  exact ⟨(aux1 (shared ) b0), (Relation.ReflTransGen.refl), (Relation.ReflTransGen.refl)⟩
theorem cp_14_1_14 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (aux0 (aux0 (shared ) b0) (aux0 (shared ) b0))) :
    Join (aux1 (shared ) a0) (aux0 (aux1 (shared ) b0) (aux0 (shared ) a0)) := by
  rcases T.aux0.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  cases he0
theorem cp_14_1_1_14 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux0 (aux0 (shared ) b0) (aux0 (shared ) b0))) :
    Join (aux1 (shared ) a0) (aux0 (aux0 (aux1 (shared ) b0) a0) (aux0 (shared ) a0)) := by
  cases heq
theorem cp_14_2_14 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (aux0 (aux0 (shared ) b0) (aux0 (shared ) b0))) :
    Join (aux1 (shared ) a0) (aux0 (aux0 (shared ) a0) (aux1 (shared ) b0)) := by
  rcases T.aux0.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  cases he0
theorem cp_14_2_1_14 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux0 (aux0 (shared ) b0) (aux0 (shared ) b0))) :
    Join (aux1 (shared ) a0) (aux0 (aux0 (shared ) a0) (aux0 (aux1 (shared ) b0) a0)) := by
  cases heq
theorem cp_14_root_15 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (aux0 (shared ) a0) (aux0 (shared ) a0)) = (op (aux0 (shared ) b0) (aux1 (shared ) b0))) :
    Join (aux1 (shared ) a0) (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) := by
  cases heq
theorem cp_14_1_15 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (op (aux0 (shared ) b0) (aux1 (shared ) b0))) :
    Join (aux1 (shared ) a0) (aux0 (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) (aux0 (shared ) a0)) := by
  cases heq
theorem cp_14_1_1_15 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux0 (shared ) b0) (aux1 (shared ) b0))) :
    Join (aux1 (shared ) a0) (aux0 (aux0 (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) a0) (aux0 (shared ) a0)) := by
  cases heq
theorem cp_14_2_15 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (op (aux0 (shared ) b0) (aux1 (shared ) b0))) :
    Join (aux1 (shared ) a0) (aux0 (aux0 (shared ) a0) (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0))) := by
  cases heq
theorem cp_14_2_1_15 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux0 (shared ) b0) (aux1 (shared ) b0))) :
    Join (aux1 (shared ) a0) (aux0 (aux0 (shared ) a0) (aux0 (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) a0)) := by
  cases heq
theorem cp_14_root_16 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (aux0 (shared ) a0) (aux0 (shared ) a0)) = (op (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) (aux1 (shared ) b0))) :
    Join (aux1 (shared ) a0) (aux0 (aux0 (shared ) b0) (aux1 (shared ) b0)) := by
  cases heq
theorem cp_14_1_16 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (op (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) (aux1 (shared ) b0))) :
    Join (aux1 (shared ) a0) (aux0 (aux0 (aux0 (shared ) b0) (aux1 (shared ) b0)) (aux0 (shared ) a0)) := by
  cases heq
theorem cp_14_1_1_16 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) (aux1 (shared ) b0))) :
    Join (aux1 (shared ) a0) (aux0 (aux0 (aux0 (aux0 (shared ) b0) (aux1 (shared ) b0)) a0) (aux0 (shared ) a0)) := by
  cases heq
theorem cp_14_2_16 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (op (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) (aux1 (shared ) b0))) :
    Join (aux1 (shared ) a0) (aux0 (aux0 (shared ) a0) (aux0 (aux0 (shared ) b0) (aux1 (shared ) b0))) := by
  cases heq
theorem cp_14_2_1_16 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) (aux1 (shared ) b0))) :
    Join (aux1 (shared ) a0) (aux0 (aux0 (shared ) a0) (aux0 (aux0 (aux0 (shared ) b0) (aux1 (shared ) b0)) a0)) := by
  cases heq
theorem cp_15_root_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux0 (shared ) a0) (aux1 (shared ) a0)) = (op b0 b0)) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (shared ) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst b0
  intro he0
  cases he0
theorem cp_15_1_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (op b0 b0)) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (op (shared ) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_15_1_1_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op b0 b0)) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (op (aux0 (shared ) a0) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_15_2_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) a0) = (op b0 b0)) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (op (aux0 (shared ) a0) (shared )) := by
  cases heq
theorem cp_15_2_1_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op b0 b0)) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (op (aux0 (shared ) a0) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_15_root_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux0 (shared ) a0) (aux1 (shared ) a0)) = (op (op b0 b1) b1)) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (aux0 b0 b1) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst b1
  intro he0
  cases he0
theorem cp_15_1_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (op (op b0 b1) b1)) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (op (aux0 b0 b1) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_15_1_1_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (op b0 b1) b1)) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (op (aux0 (aux0 b0 b1) a0) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_15_2_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) a0) = (op (op b0 b1) b1)) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (op (aux0 (shared ) a0) (aux0 b0 b1)) := by
  cases heq
theorem cp_15_2_1_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (op b0 b1) b1)) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (op (aux0 (shared ) a0) (aux1 (aux0 b0 b1) a0)) := by
  cases heq
theorem cp_15_root_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux0 (shared ) a0) (aux1 (shared ) a0)) = (op (shared ) b0)) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (aux0 b0 b0) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst b0
  intro he0
  cases he0
theorem cp_15_1_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (op (shared ) b0)) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (op (aux0 b0 b0) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_15_1_1_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (shared ) b0)) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (op (aux0 (aux0 b0 b0) a0) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_15_2_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) a0) = (op (shared ) b0)) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (op (aux0 (shared ) a0) (aux0 b0 b0)) := by
  cases heq
theorem cp_15_2_1_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (shared ) b0)) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (op (aux0 (shared ) a0) (aux1 (aux0 b0 b0) a0)) := by
  cases heq
theorem cp_15_root_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux0 (shared ) a0) (aux1 (shared ) a0)) = (op b0 (aux0 b0 b1))) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (aux1 b0 b1) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  cases he1
theorem cp_15_1_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (op b0 (aux0 b0 b1))) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (op (aux1 b0 b1) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_15_1_1_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op b0 (aux0 b0 b1))) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (op (aux0 (aux1 b0 b1) a0) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_15_2_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) a0) = (op b0 (aux0 b0 b1))) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (op (aux0 (shared ) a0) (aux1 b0 b1)) := by
  cases heq
theorem cp_15_2_1_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op b0 (aux0 b0 b1))) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (op (aux0 (shared ) a0) (aux1 (aux1 b0 b1) a0)) := by
  cases heq
theorem cp_15_root_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux0 (shared ) a0) (aux1 (shared ) a0)) = (op (aux0 b0 b1) b1)) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (aux0 (op b0 b1) b1) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst b1
  intro he0
  rcases T.aux0.inj he0 with ⟨he2, he3⟩
  clear he0
  have hsize := congrArg sz he3
  have hp_a0 := sz_pos a0
  simp only [sz] at hsize
  omega
theorem cp_15_1_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (op (aux0 b0 b1) b1)) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (op (aux0 (op b0 b1) b1) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_15_1_1_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux0 b0 b1) b1)) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (op (aux0 (aux0 (op b0 b1) b1) a0) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_15_2_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) a0) = (op (aux0 b0 b1) b1)) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (op (aux0 (shared ) a0) (aux0 (op b0 b1) b1)) := by
  cases heq
theorem cp_15_2_1_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux0 b0 b1) b1)) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (op (aux0 (shared ) a0) (aux1 (aux0 (op b0 b1) b1) a0)) := by
  cases heq
theorem cp_15_root_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux0 (shared ) a0) (aux1 (shared ) a0)) = (aux0 (shared ) (shared ))) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (shared ) := by
  cases heq
theorem cp_15_1_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (aux0 (shared ) (shared ))) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (op (shared ) (aux1 (shared ) a0)) := by
  rcases T.aux0.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  clear he0
  exact ⟨(shared ), ((((Relation.ReflTransGen.refl).tail (Step.c_aux1_1 (aux0 (shared ) (shared )) (root_step .r5 (leaf 0) (leaf 0) (leaf 0)))).tail (Step.c_aux1_2 (shared ) (root_step .r5 (leaf 0) (leaf 0) (leaf 0)))).tail (root_step .r6 (leaf 0) (leaf 0) (leaf 0))), (((Relation.ReflTransGen.refl).tail (root_step .r2 (aux1 (shared ) (shared )) (leaf 0) (leaf 0))).tail (root_step .r7 (shared ) (shared ) (leaf 0)))⟩
theorem cp_15_1_1_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux0 (shared ) (shared ))) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (op (aux0 (shared ) a0) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_15_2_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) a0) = (aux0 (shared ) (shared ))) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (op (aux0 (shared ) a0) (shared )) := by
  cases heq
theorem cp_15_2_1_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux0 (shared ) (shared ))) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (op (aux0 (shared ) a0) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_15_root_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux0 (shared ) a0) (aux1 (shared ) a0)) = (aux1 (shared ) (shared ))) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (shared ) := by
  cases heq
theorem cp_15_1_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (aux1 (shared ) (shared ))) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (op (shared ) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_15_1_1_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux1 (shared ) (shared ))) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (op (aux0 (shared ) a0) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_15_2_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) a0) = (aux1 (shared ) (shared ))) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (op (aux0 (shared ) a0) (shared )) := by
  rcases T.aux1.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  clear he0
  exact ⟨(shared ), ((((Relation.ReflTransGen.refl).tail (Step.c_aux1_1 (aux0 (shared ) (shared )) (root_step .r5 (leaf 0) (leaf 0) (leaf 0)))).tail (Step.c_aux1_2 (shared ) (root_step .r5 (leaf 0) (leaf 0) (leaf 0)))).tail (root_step .r6 (leaf 0) (leaf 0) (leaf 0))), ((((Relation.ReflTransGen.refl).tail (root_step .r4 (shared ) (shared ) (leaf 0))).tail (Step.c_aux0_1 (shared ) (root_step .r0 (shared ) (leaf 0) (leaf 0)))).tail (root_step .r5 (leaf 0) (leaf 0) (leaf 0)))⟩
theorem cp_15_2_1_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux1 (shared ) (shared ))) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (op (aux0 (shared ) a0) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_15_root_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux0 (shared ) a0) (aux1 (shared ) a0)) = (aux0 (aux1 b0 b1) (aux1 b0 b1))) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) b0 := by
  cases heq
theorem cp_15_1_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (aux0 (aux1 b0 b1) (aux1 b0 b1))) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (op b0 (aux1 (shared ) a0)) := by
  rcases T.aux0.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  cases he0
theorem cp_15_1_1_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux0 (aux1 b0 b1) (aux1 b0 b1))) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (op (aux0 b0 a0) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_15_2_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) a0) = (aux0 (aux1 b0 b1) (aux1 b0 b1))) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (op (aux0 (shared ) a0) b0) := by
  cases heq
theorem cp_15_2_1_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux0 (aux1 b0 b1) (aux1 b0 b1))) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (op (aux0 (shared ) a0) (aux1 b0 a0)) := by
  cases heq
theorem cp_15_root_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux0 (shared ) a0) (aux1 (shared ) a0)) = (op (aux1 b0 b1) (aux0 b0 b1))) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (aux0 b0 (aux0 b0 b1)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  cases he1
theorem cp_15_1_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (op (aux1 b0 b1) (aux0 b0 b1))) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (op (aux0 b0 (aux0 b0 b1)) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_15_1_1_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux1 b0 b1) (aux0 b0 b1))) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (op (aux0 (aux0 b0 (aux0 b0 b1)) a0) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_15_2_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) a0) = (op (aux1 b0 b1) (aux0 b0 b1))) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (op (aux0 (shared ) a0) (aux0 b0 (aux0 b0 b1))) := by
  cases heq
theorem cp_15_2_1_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux1 b0 b1) (aux0 b0 b1))) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (op (aux0 (shared ) a0) (aux1 (aux0 b0 (aux0 b0 b1)) a0)) := by
  cases heq
theorem cp_15_root_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux0 (shared ) a0) (aux1 (shared ) a0)) = (op (aux1 b0 b1) b0)) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (aux1 (aux1 b0 b1) (aux1 b0 b1)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst b0
  intro he0
  cases he0
theorem cp_15_1_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (op (aux1 b0 b1) b0)) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (op (aux1 (aux1 b0 b1) (aux1 b0 b1)) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_15_1_1_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux1 b0 b1) b0)) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (op (aux0 (aux1 (aux1 b0 b1) (aux1 b0 b1)) a0) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_15_2_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) a0) = (op (aux1 b0 b1) b0)) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (op (aux0 (shared ) a0) (aux1 (aux1 b0 b1) (aux1 b0 b1))) := by
  cases heq
theorem cp_15_2_1_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux1 b0 b1) b0)) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (op (aux0 (shared ) a0) (aux1 (aux1 (aux1 b0 b1) (aux1 b0 b1)) a0)) := by
  cases heq
theorem cp_15_root_10 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux0 (shared ) a0) (aux1 (shared ) a0)) = (op b0 (aux1 b0 b1))) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (aux0 (shared ) (aux1 b0 b1)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  rcases T.aux1.inj he1 with ⟨he2, he3⟩
  clear he1
  revert he0 he2
  subst a0
  intro he0 he2
  revert he0
  subst b0
  intro he0
  cases he0
theorem cp_15_1_10 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (op b0 (aux1 b0 b1))) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (op (aux0 (shared ) (aux1 b0 b1)) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_15_1_1_10 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op b0 (aux1 b0 b1))) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (op (aux0 (aux0 (shared ) (aux1 b0 b1)) a0) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_15_2_10 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) a0) = (op b0 (aux1 b0 b1))) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (op (aux0 (shared ) a0) (aux0 (shared ) (aux1 b0 b1))) := by
  cases heq
theorem cp_15_2_1_10 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op b0 (aux1 b0 b1))) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (op (aux0 (shared ) a0) (aux1 (aux0 (shared ) (aux1 b0 b1)) a0)) := by
  cases heq
theorem cp_15_root_11 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux0 (shared ) a0) (aux1 (shared ) a0)) = (aux0 (shared ) (aux1 (shared ) b0))) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (shared ) := by
  cases heq
theorem cp_15_1_11 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (aux0 (shared ) (aux1 (shared ) b0))) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (op (shared ) (aux1 (shared ) a0)) := by
  rcases T.aux0.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  clear he0
  exact ⟨(shared ), ((((Relation.ReflTransGen.refl).tail (Step.c_aux1_1 (aux0 (shared ) (aux1 (shared ) b0)) (root_step .r11 b0 (leaf 0) (leaf 0)))).tail (Step.c_aux1_2 (shared ) (root_step .r11 b0 (leaf 0) (leaf 0)))).tail (root_step .r6 (leaf 0) (leaf 0) (leaf 0))), (((Relation.ReflTransGen.refl).tail (root_step .r2 (aux1 (shared ) (aux1 (shared ) b0)) (leaf 0) (leaf 0))).tail (root_step .r7 (shared ) (aux1 (shared ) b0) (leaf 0)))⟩
theorem cp_15_1_1_11 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux0 (shared ) (aux1 (shared ) b0))) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (op (aux0 (shared ) a0) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_15_2_11 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) a0) = (aux0 (shared ) (aux1 (shared ) b0))) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (op (aux0 (shared ) a0) (shared )) := by
  cases heq
theorem cp_15_2_1_11 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux0 (shared ) (aux1 (shared ) b0))) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (op (aux0 (shared ) a0) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_15_root_12 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux0 (shared ) a0) (aux1 (shared ) a0)) = (aux1 (shared ) (aux1 (shared ) b0))) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (shared ) := by
  cases heq
theorem cp_15_1_12 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (aux1 (shared ) (aux1 (shared ) b0))) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (op (shared ) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_15_1_1_12 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux1 (shared ) (aux1 (shared ) b0))) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (op (aux0 (shared ) a0) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_15_2_12 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) a0) = (aux1 (shared ) (aux1 (shared ) b0))) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (op (aux0 (shared ) a0) (shared )) := by
  rcases T.aux1.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  clear he0
  exact ⟨(shared ), ((((Relation.ReflTransGen.refl).tail (Step.c_aux1_1 (aux0 (shared ) (aux1 (shared ) b0)) (root_step .r11 b0 (leaf 0) (leaf 0)))).tail (Step.c_aux1_2 (shared ) (root_step .r11 b0 (leaf 0) (leaf 0)))).tail (root_step .r6 (leaf 0) (leaf 0) (leaf 0))), (((Relation.ReflTransGen.refl).tail (Step.c_op_1 (shared ) (root_step .r11 b0 (leaf 0) (leaf 0)))).tail (root_step .r0 (shared ) (leaf 0) (leaf 0)))⟩
theorem cp_15_2_1_12 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux1 (shared ) (aux1 (shared ) b0))) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (op (aux0 (shared ) a0) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_15_root_13 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux0 (shared ) a0) (aux1 (shared ) a0)) = (op (aux1 (aux1 b0 b1) (aux1 b0 b1)) b0)) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (aux0 (aux1 b0 b1) b0) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst b0
  intro he0
  cases he0
theorem cp_15_1_13 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (op (aux1 (aux1 b0 b1) (aux1 b0 b1)) b0)) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (op (aux0 (aux1 b0 b1) b0) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_15_1_1_13 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux1 (aux1 b0 b1) (aux1 b0 b1)) b0)) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (op (aux0 (aux0 (aux1 b0 b1) b0) a0) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_15_2_13 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) a0) = (op (aux1 (aux1 b0 b1) (aux1 b0 b1)) b0)) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (op (aux0 (shared ) a0) (aux0 (aux1 b0 b1) b0)) := by
  cases heq
theorem cp_15_2_1_13 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux1 (aux1 b0 b1) (aux1 b0 b1)) b0)) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (op (aux0 (shared ) a0) (aux1 (aux0 (aux1 b0 b1) b0) a0)) := by
  cases heq
theorem cp_15_root_14 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux0 (shared ) a0) (aux1 (shared ) a0)) = (aux0 (aux0 (shared ) b0) (aux0 (shared ) b0))) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (aux1 (shared ) b0) := by
  cases heq
theorem cp_15_1_14 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (aux0 (aux0 (shared ) b0) (aux0 (shared ) b0))) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (op (aux1 (shared ) b0) (aux1 (shared ) a0)) := by
  rcases T.aux0.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  cases he0
theorem cp_15_1_1_14 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux0 (aux0 (shared ) b0) (aux0 (shared ) b0))) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (op (aux0 (aux1 (shared ) b0) a0) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_15_2_14 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) a0) = (aux0 (aux0 (shared ) b0) (aux0 (shared ) b0))) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (op (aux0 (shared ) a0) (aux1 (shared ) b0)) := by
  cases heq
theorem cp_15_2_1_14 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux0 (aux0 (shared ) b0) (aux0 (shared ) b0))) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (op (aux0 (shared ) a0) (aux1 (aux1 (shared ) b0) a0)) := by
  cases heq
theorem cp_15_root_15 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux0 (shared ) a0) (aux1 (shared ) a0)) = (op (aux0 (shared ) b0) (aux1 (shared ) b0))) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  rcases T.aux1.inj he1 with ⟨he2, he3⟩
  clear he1
  revert he0 he2
  subst a0
  intro he0 he2
  clear he2
  clear he0
  exact ⟨(aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)), (Relation.ReflTransGen.refl), (Relation.ReflTransGen.refl)⟩
theorem cp_15_1_15 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (op (aux0 (shared ) b0) (aux1 (shared ) b0))) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (op (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_15_1_1_15 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux0 (shared ) b0) (aux1 (shared ) b0))) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (op (aux0 (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) a0) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_15_2_15 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) a0) = (op (aux0 (shared ) b0) (aux1 (shared ) b0))) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (op (aux0 (shared ) a0) (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0))) := by
  cases heq
theorem cp_15_2_1_15 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux0 (shared ) b0) (aux1 (shared ) b0))) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (op (aux0 (shared ) a0) (aux1 (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) a0)) := by
  cases heq
theorem cp_15_root_16 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux0 (shared ) a0) (aux1 (shared ) a0)) = (op (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) (aux1 (shared ) b0))) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (aux0 (aux0 (shared ) b0) (aux1 (shared ) b0)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  rcases T.aux1.inj he1 with ⟨he2, he3⟩
  clear he1
  revert he0 he2
  subst a0
  intro he0 he2
  clear he2
  cases he0
theorem cp_15_1_16 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (op (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) (aux1 (shared ) b0))) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (op (aux0 (aux0 (shared ) b0) (aux1 (shared ) b0)) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_15_1_1_16 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) (aux1 (shared ) b0))) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (op (aux0 (aux0 (aux0 (shared ) b0) (aux1 (shared ) b0)) a0) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_15_2_16 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) a0) = (op (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) (aux1 (shared ) b0))) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (op (aux0 (shared ) a0) (aux0 (aux0 (shared ) b0) (aux1 (shared ) b0))) := by
  cases heq
theorem cp_15_2_1_16 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) (aux1 (shared ) b0))) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (op (aux0 (shared ) a0) (aux1 (aux0 (aux0 (shared ) b0) (aux1 (shared ) b0)) a0)) := by
  cases heq
theorem cp_16_root_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (aux1 (shared ) a0)) = (op b0 b0)) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (shared ) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst b0
  intro he0
  rcases T.aux1.inj he0 with ⟨he2, he3⟩
  clear he0
  have hsize := congrArg sz he3
  have hp_a0 := sz_pos a0
  simp only [sz] at hsize
  omega
theorem cp_16_1_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) = (op b0 b0)) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (shared ) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_16_1_1_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (op b0 b0)) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (shared ) (aux0 (shared ) a0)) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_16_1_1_1_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op b0 b0)) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_16_1_2_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (op b0 b0)) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (shared ) a0) (shared )) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_16_1_2_1_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op b0 b0)) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_16_2_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) a0) = (op b0 b0)) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (shared )) := by
  cases heq
theorem cp_16_2_1_0 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op b0 b0)) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_16_root_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (aux1 (shared ) a0)) = (op (op b0 b1) b1)) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (aux0 b0 b1) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst b1
  intro he0
  cases he0
theorem cp_16_1_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) = (op (op b0 b1) b1)) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux0 b0 b1) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_16_1_1_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (op (op b0 b1) b1)) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 b0 b1) (aux0 (shared ) a0)) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_16_1_1_1_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (op b0 b1) b1)) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (aux0 b0 b1) a0) (aux0 (shared ) a0)) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_16_1_2_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (op (op b0 b1) b1)) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (shared ) a0) (aux0 b0 b1)) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_16_1_2_1_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (op b0 b1) b1)) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (shared ) a0) (aux0 (aux0 b0 b1) a0)) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_16_2_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) a0) = (op (op b0 b1) b1)) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (aux0 b0 b1)) := by
  cases heq
theorem cp_16_2_1_1 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (op b0 b1) b1)) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (aux1 (aux0 b0 b1) a0)) := by
  cases heq
theorem cp_16_root_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (aux1 (shared ) a0)) = (op (shared ) b0)) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (aux0 b0 b0) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst b0
  intro he0
  cases he0
theorem cp_16_1_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) = (op (shared ) b0)) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux0 b0 b0) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_16_1_1_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (op (shared ) b0)) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 b0 b0) (aux0 (shared ) a0)) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_16_1_1_1_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (shared ) b0)) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (aux0 b0 b0) a0) (aux0 (shared ) a0)) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_16_1_2_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (op (shared ) b0)) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (shared ) a0) (aux0 b0 b0)) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_16_1_2_1_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (shared ) b0)) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (shared ) a0) (aux0 (aux0 b0 b0) a0)) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_16_2_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) a0) = (op (shared ) b0)) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (aux0 b0 b0)) := by
  cases heq
theorem cp_16_2_1_2 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (shared ) b0)) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (aux1 (aux0 b0 b0) a0)) := by
  cases heq
theorem cp_16_root_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (aux1 (shared ) a0)) = (op b0 (aux0 b0 b1))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (aux1 b0 b1) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  cases he1
theorem cp_16_1_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) = (op b0 (aux0 b0 b1))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 b0 b1) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_16_1_1_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (op b0 (aux0 b0 b1))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux1 b0 b1) (aux0 (shared ) a0)) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_16_1_1_1_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op b0 (aux0 b0 b1))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (aux1 b0 b1) a0) (aux0 (shared ) a0)) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_16_1_2_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (op b0 (aux0 b0 b1))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (shared ) a0) (aux1 b0 b1)) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_16_1_2_1_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op b0 (aux0 b0 b1))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (shared ) a0) (aux0 (aux1 b0 b1) a0)) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_16_2_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) a0) = (op b0 (aux0 b0 b1))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (aux1 b0 b1)) := by
  cases heq
theorem cp_16_2_1_3 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op b0 (aux0 b0 b1))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (aux1 (aux1 b0 b1) a0)) := by
  cases heq
theorem cp_16_root_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (aux1 (shared ) a0)) = (op (aux0 b0 b1) b1)) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (aux0 (op b0 b1) b1) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst b1
  intro he0
  cases he0
theorem cp_16_1_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) = (op (aux0 b0 b1) b1)) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux0 (op b0 b1) b1) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_16_1_1_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (op (aux0 b0 b1) b1)) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (op b0 b1) b1) (aux0 (shared ) a0)) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_16_1_1_1_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux0 b0 b1) b1)) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (aux0 (op b0 b1) b1) a0) (aux0 (shared ) a0)) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_16_1_2_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (op (aux0 b0 b1) b1)) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (shared ) a0) (aux0 (op b0 b1) b1)) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_16_1_2_1_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux0 b0 b1) b1)) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (shared ) a0) (aux0 (aux0 (op b0 b1) b1) a0)) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_16_2_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) a0) = (op (aux0 b0 b1) b1)) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (aux0 (op b0 b1) b1)) := by
  cases heq
theorem cp_16_2_1_4 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux0 b0 b1) b1)) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (aux1 (aux0 (op b0 b1) b1) a0)) := by
  cases heq
theorem cp_16_root_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (aux1 (shared ) a0)) = (aux0 (shared ) (shared ))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (shared ) := by
  cases heq
theorem cp_16_1_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) = (aux0 (shared ) (shared ))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (shared ) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_16_1_1_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (aux0 (shared ) (shared ))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (shared ) (aux0 (shared ) a0)) (aux1 (shared ) a0)) := by
  rcases T.aux0.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  clear he0
  exact ⟨(shared ), (((Relation.ReflTransGen.refl).tail (Step.c_aux0_1 (aux1 (shared ) (shared )) (root_step .r5 (leaf 0) (leaf 0) (leaf 0)))).tail (root_step .r11 (shared ) (leaf 0) (leaf 0))), (((Relation.ReflTransGen.refl).tail (Step.c_op_1 (aux1 (shared ) (shared )) (Step.c_aux1_2 (shared ) (root_step .r5 (leaf 0) (leaf 0) (leaf 0))))).tail (root_step .r0 (aux1 (shared ) (shared )) (leaf 0) (leaf 0)))⟩
theorem cp_16_1_1_1_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux0 (shared ) (shared ))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_16_1_2_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (aux0 (shared ) (shared ))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (shared ) a0) (shared )) (aux1 (shared ) a0)) := by
  rcases T.aux0.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  clear he0
  exact ⟨(shared ), (((Relation.ReflTransGen.refl).tail (Step.c_aux0_1 (aux1 (shared ) (shared )) (root_step .r5 (leaf 0) (leaf 0) (leaf 0)))).tail (root_step .r11 (shared ) (leaf 0) (leaf 0))), (((Relation.ReflTransGen.refl).tail (Step.c_op_1 (aux1 (shared ) (shared )) (Step.c_aux1_1 (shared ) (root_step .r5 (leaf 0) (leaf 0) (leaf 0))))).tail (root_step .r0 (aux1 (shared ) (shared )) (leaf 0) (leaf 0)))⟩
theorem cp_16_1_2_1_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux0 (shared ) (shared ))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_16_2_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) a0) = (aux0 (shared ) (shared ))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (shared )) := by
  cases heq
theorem cp_16_2_1_5 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux0 (shared ) (shared ))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_16_root_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (aux1 (shared ) a0)) = (aux1 (shared ) (shared ))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (shared ) := by
  cases heq
theorem cp_16_1_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) = (aux1 (shared ) (shared ))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (shared ) (aux1 (shared ) a0)) := by
  rcases T.aux1.inj heq with ⟨he0, he1⟩
  clear heq
  cases he1
theorem cp_16_1_1_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (aux1 (shared ) (shared ))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (shared ) (aux0 (shared ) a0)) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_16_1_1_1_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux1 (shared ) (shared ))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_16_1_2_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (aux1 (shared ) (shared ))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (shared ) a0) (shared )) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_16_1_2_1_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux1 (shared ) (shared ))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_16_2_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) a0) = (aux1 (shared ) (shared ))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (shared )) := by
  rcases T.aux1.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  clear he0
  exact ⟨(shared ), (((Relation.ReflTransGen.refl).tail (Step.c_aux0_1 (aux1 (shared ) (shared )) (root_step .r5 (leaf 0) (leaf 0) (leaf 0)))).tail (root_step .r11 (shared ) (leaf 0) (leaf 0))), ((((((Relation.ReflTransGen.refl).tail (Step.c_op_1 (shared ) (Step.c_aux1_1 (aux0 (shared ) (shared )) (root_step .r5 (leaf 0) (leaf 0) (leaf 0))))).tail (root_step .r9 (shared ) (aux0 (shared ) (shared )) (leaf 0))).tail (Step.c_aux1_1 (aux1 (shared ) (aux0 (shared ) (shared ))) (Step.c_aux1_2 (shared ) (root_step .r5 (leaf 0) (leaf 0) (leaf 0))))).tail (Step.c_aux1_1 (aux1 (shared ) (aux0 (shared ) (shared ))) (root_step .r6 (leaf 0) (leaf 0) (leaf 0)))).tail (root_step .r12 (aux0 (shared ) (shared )) (leaf 0) (leaf 0)))⟩
theorem cp_16_2_1_6 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux1 (shared ) (shared ))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_16_root_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (aux1 (shared ) a0)) = (aux0 (aux1 b0 b1) (aux1 b0 b1))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) b0 := by
  cases heq
theorem cp_16_1_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) = (aux0 (aux1 b0 b1) (aux1 b0 b1))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op b0 (aux1 (shared ) a0)) := by
  cases heq
theorem cp_16_1_1_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (aux0 (aux1 b0 b1) (aux1 b0 b1))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 b0 (aux0 (shared ) a0)) (aux1 (shared ) a0)) := by
  rcases T.aux0.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  cases he0
theorem cp_16_1_1_1_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux0 (aux1 b0 b1) (aux1 b0 b1))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 b0 a0) (aux0 (shared ) a0)) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_16_1_2_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (aux0 (aux1 b0 b1) (aux1 b0 b1))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (shared ) a0) b0) (aux1 (shared ) a0)) := by
  rcases T.aux0.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  cases he0
theorem cp_16_1_2_1_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux0 (aux1 b0 b1) (aux1 b0 b1))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (shared ) a0) (aux0 b0 a0)) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_16_2_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) a0) = (aux0 (aux1 b0 b1) (aux1 b0 b1))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) b0) := by
  cases heq
theorem cp_16_2_1_7 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux0 (aux1 b0 b1) (aux1 b0 b1))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (aux1 b0 a0)) := by
  cases heq
theorem cp_16_root_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (aux1 (shared ) a0)) = (op (aux1 b0 b1) (aux0 b0 b1))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (aux0 b0 (aux0 b0 b1)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  cases he1
theorem cp_16_1_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) = (op (aux1 b0 b1) (aux0 b0 b1))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux0 b0 (aux0 b0 b1)) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_16_1_1_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (op (aux1 b0 b1) (aux0 b0 b1))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 b0 (aux0 b0 b1)) (aux0 (shared ) a0)) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_16_1_1_1_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux1 b0 b1) (aux0 b0 b1))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (aux0 b0 (aux0 b0 b1)) a0) (aux0 (shared ) a0)) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_16_1_2_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (op (aux1 b0 b1) (aux0 b0 b1))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (shared ) a0) (aux0 b0 (aux0 b0 b1))) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_16_1_2_1_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux1 b0 b1) (aux0 b0 b1))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (shared ) a0) (aux0 (aux0 b0 (aux0 b0 b1)) a0)) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_16_2_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) a0) = (op (aux1 b0 b1) (aux0 b0 b1))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (aux0 b0 (aux0 b0 b1))) := by
  cases heq
theorem cp_16_2_1_8 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux1 b0 b1) (aux0 b0 b1))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (aux1 (aux0 b0 (aux0 b0 b1)) a0)) := by
  cases heq
theorem cp_16_root_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (aux1 (shared ) a0)) = (op (aux1 b0 b1) b0)) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (aux1 (aux1 b0 b1) (aux1 b0 b1)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst b0
  intro he0
  rcases T.aux1.inj he0 with ⟨he2, he3⟩
  clear he0
  revert he2
  subst b1
  intro he2
  cases he2
theorem cp_16_1_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) = (op (aux1 b0 b1) b0)) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux1 b0 b1) (aux1 b0 b1)) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_16_1_1_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (op (aux1 b0 b1) b0)) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux1 (aux1 b0 b1) (aux1 b0 b1)) (aux0 (shared ) a0)) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_16_1_1_1_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux1 b0 b1) b0)) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (aux1 (aux1 b0 b1) (aux1 b0 b1)) a0) (aux0 (shared ) a0)) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_16_1_2_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (op (aux1 b0 b1) b0)) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (shared ) a0) (aux1 (aux1 b0 b1) (aux1 b0 b1))) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_16_1_2_1_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux1 b0 b1) b0)) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (shared ) a0) (aux0 (aux1 (aux1 b0 b1) (aux1 b0 b1)) a0)) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_16_2_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) a0) = (op (aux1 b0 b1) b0)) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (aux1 (aux1 b0 b1) (aux1 b0 b1))) := by
  cases heq
theorem cp_16_2_1_9 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux1 b0 b1) b0)) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (aux1 (aux1 (aux1 b0 b1) (aux1 b0 b1)) a0)) := by
  cases heq
theorem cp_16_root_10 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (aux1 (shared ) a0)) = (op b0 (aux1 b0 b1))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (aux0 (shared ) (aux1 b0 b1)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  rcases T.aux1.inj he1 with ⟨he2, he3⟩
  clear he1
  revert he0 he2
  subst a0
  intro he0 he2
  revert he0
  subst b0
  intro he0
  cases he0
theorem cp_16_1_10 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) = (op b0 (aux1 b0 b1))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux0 (shared ) (aux1 b0 b1)) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_16_1_1_10 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (op b0 (aux1 b0 b1))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (shared ) (aux1 b0 b1)) (aux0 (shared ) a0)) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_16_1_1_1_10 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op b0 (aux1 b0 b1))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (aux0 (shared ) (aux1 b0 b1)) a0) (aux0 (shared ) a0)) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_16_1_2_10 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (op b0 (aux1 b0 b1))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (shared ) a0) (aux0 (shared ) (aux1 b0 b1))) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_16_1_2_1_10 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op b0 (aux1 b0 b1))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (shared ) a0) (aux0 (aux0 (shared ) (aux1 b0 b1)) a0)) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_16_2_10 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) a0) = (op b0 (aux1 b0 b1))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (aux0 (shared ) (aux1 b0 b1))) := by
  cases heq
theorem cp_16_2_1_10 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op b0 (aux1 b0 b1))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (aux1 (aux0 (shared ) (aux1 b0 b1)) a0)) := by
  cases heq
theorem cp_16_root_11 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (aux1 (shared ) a0)) = (aux0 (shared ) (aux1 (shared ) b0))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (shared ) := by
  cases heq
theorem cp_16_1_11 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) = (aux0 (shared ) (aux1 (shared ) b0))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (shared ) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_16_1_1_11 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (aux0 (shared ) (aux1 (shared ) b0))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (shared ) (aux0 (shared ) a0)) (aux1 (shared ) a0)) := by
  rcases T.aux0.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  clear he0
  exact ⟨(shared ), (((Relation.ReflTransGen.refl).tail (Step.c_aux0_1 (aux1 (shared ) (aux1 (shared ) b0)) (root_step .r11 b0 (leaf 0) (leaf 0)))).tail (root_step .r11 (aux1 (shared ) b0) (leaf 0) (leaf 0))), (((((Relation.ReflTransGen.refl).tail (Step.c_op_1 (aux1 (shared ) (aux1 (shared ) b0)) (Step.c_aux1_2 (shared ) (root_step .r11 b0 (leaf 0) (leaf 0))))).tail (Step.c_op_1 (aux1 (shared ) (aux1 (shared ) b0)) (root_step .r6 (leaf 0) (leaf 0) (leaf 0)))).tail (root_step .r2 (aux1 (shared ) (aux1 (shared ) b0)) (leaf 0) (leaf 0))).tail (root_step .r7 (shared ) (aux1 (shared ) b0) (leaf 0)))⟩
theorem cp_16_1_1_1_11 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux0 (shared ) (aux1 (shared ) b0))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_16_1_2_11 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (aux0 (shared ) (aux1 (shared ) b0))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (shared ) a0) (shared )) (aux1 (shared ) a0)) := by
  rcases T.aux0.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  clear he0
  exact ⟨(shared ), (((Relation.ReflTransGen.refl).tail (Step.c_aux0_1 (aux1 (shared ) (aux1 (shared ) b0)) (root_step .r11 b0 (leaf 0) (leaf 0)))).tail (root_step .r11 (aux1 (shared ) b0) (leaf 0) (leaf 0))), (((((Relation.ReflTransGen.refl).tail (Step.c_op_1 (aux1 (shared ) (aux1 (shared ) b0)) (Step.c_aux1_1 (shared ) (root_step .r11 b0 (leaf 0) (leaf 0))))).tail (Step.c_op_1 (aux1 (shared ) (aux1 (shared ) b0)) (root_step .r6 (leaf 0) (leaf 0) (leaf 0)))).tail (root_step .r2 (aux1 (shared ) (aux1 (shared ) b0)) (leaf 0) (leaf 0))).tail (root_step .r7 (shared ) (aux1 (shared ) b0) (leaf 0)))⟩
theorem cp_16_1_2_1_11 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux0 (shared ) (aux1 (shared ) b0))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_16_2_11 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) a0) = (aux0 (shared ) (aux1 (shared ) b0))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (shared )) := by
  cases heq
theorem cp_16_2_1_11 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux0 (shared ) (aux1 (shared ) b0))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_16_root_12 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (aux1 (shared ) a0)) = (aux1 (shared ) (aux1 (shared ) b0))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (shared ) := by
  cases heq
theorem cp_16_1_12 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) = (aux1 (shared ) (aux1 (shared ) b0))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (shared ) (aux1 (shared ) a0)) := by
  rcases T.aux1.inj heq with ⟨he0, he1⟩
  clear heq
  cases he1
theorem cp_16_1_1_12 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (aux1 (shared ) (aux1 (shared ) b0))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (shared ) (aux0 (shared ) a0)) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_16_1_1_1_12 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux1 (shared ) (aux1 (shared ) b0))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_16_1_2_12 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (aux1 (shared ) (aux1 (shared ) b0))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (shared ) a0) (shared )) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_16_1_2_1_12 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux1 (shared ) (aux1 (shared ) b0))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_16_2_12 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) a0) = (aux1 (shared ) (aux1 (shared ) b0))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (shared )) := by
  rcases T.aux1.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  clear he0
  exact ⟨(shared ), (((Relation.ReflTransGen.refl).tail (Step.c_aux0_1 (aux1 (shared ) (aux1 (shared ) b0)) (root_step .r11 b0 (leaf 0) (leaf 0)))).tail (root_step .r11 (aux1 (shared ) b0) (leaf 0) (leaf 0))), ((((((Relation.ReflTransGen.refl).tail (Step.c_op_1 (shared ) (Step.c_aux1_1 (aux0 (shared ) (aux1 (shared ) b0)) (root_step .r11 b0 (leaf 0) (leaf 0))))).tail (root_step .r9 (shared ) (aux0 (shared ) (aux1 (shared ) b0)) (leaf 0))).tail (Step.c_aux1_1 (aux1 (shared ) (aux0 (shared ) (aux1 (shared ) b0))) (Step.c_aux1_2 (shared ) (root_step .r11 b0 (leaf 0) (leaf 0))))).tail (Step.c_aux1_1 (aux1 (shared ) (aux0 (shared ) (aux1 (shared ) b0))) (root_step .r6 (leaf 0) (leaf 0) (leaf 0)))).tail (root_step .r12 (aux0 (shared ) (aux1 (shared ) b0)) (leaf 0) (leaf 0)))⟩
theorem cp_16_2_1_12 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux1 (shared ) (aux1 (shared ) b0))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_16_root_13 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (aux1 (shared ) a0)) = (op (aux1 (aux1 b0 b1) (aux1 b0 b1)) b0)) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (aux0 (aux1 b0 b1) b0) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst b0
  intro he0
  rcases T.aux1.inj he0 with ⟨he2, he3⟩
  clear he0
  cases he3
theorem cp_16_1_13 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) = (op (aux1 (aux1 b0 b1) (aux1 b0 b1)) b0)) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux0 (aux1 b0 b1) b0) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_16_1_1_13 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (op (aux1 (aux1 b0 b1) (aux1 b0 b1)) b0)) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (aux1 b0 b1) b0) (aux0 (shared ) a0)) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_16_1_1_1_13 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux1 (aux1 b0 b1) (aux1 b0 b1)) b0)) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (aux0 (aux1 b0 b1) b0) a0) (aux0 (shared ) a0)) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_16_1_2_13 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (op (aux1 (aux1 b0 b1) (aux1 b0 b1)) b0)) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (shared ) a0) (aux0 (aux1 b0 b1) b0)) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_16_1_2_1_13 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux1 (aux1 b0 b1) (aux1 b0 b1)) b0)) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (shared ) a0) (aux0 (aux0 (aux1 b0 b1) b0) a0)) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_16_2_13 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) a0) = (op (aux1 (aux1 b0 b1) (aux1 b0 b1)) b0)) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (aux0 (aux1 b0 b1) b0)) := by
  cases heq
theorem cp_16_2_1_13 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux1 (aux1 b0 b1) (aux1 b0 b1)) b0)) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (aux1 (aux0 (aux1 b0 b1) b0) a0)) := by
  cases heq
theorem cp_16_root_14 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (aux1 (shared ) a0)) = (aux0 (aux0 (shared ) b0) (aux0 (shared ) b0))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (aux1 (shared ) b0) := by
  cases heq
theorem cp_16_1_14 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) = (aux0 (aux0 (shared ) b0) (aux0 (shared ) b0))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (shared ) b0) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_16_1_1_14 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (aux0 (aux0 (shared ) b0) (aux0 (shared ) b0))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux1 (shared ) b0) (aux0 (shared ) a0)) (aux1 (shared ) a0)) := by
  rcases T.aux0.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  cases he0
theorem cp_16_1_1_1_14 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux0 (aux0 (shared ) b0) (aux0 (shared ) b0))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (aux1 (shared ) b0) a0) (aux0 (shared ) a0)) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_16_1_2_14 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (aux0 (aux0 (shared ) b0) (aux0 (shared ) b0))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (shared ) a0) (aux1 (shared ) b0)) (aux1 (shared ) a0)) := by
  rcases T.aux0.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  cases he0
theorem cp_16_1_2_1_14 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux0 (aux0 (shared ) b0) (aux0 (shared ) b0))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (shared ) a0) (aux0 (aux1 (shared ) b0) a0)) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_16_2_14 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) a0) = (aux0 (aux0 (shared ) b0) (aux0 (shared ) b0))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (aux1 (shared ) b0)) := by
  cases heq
theorem cp_16_2_1_14 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (aux0 (aux0 (shared ) b0) (aux0 (shared ) b0))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (aux1 (aux1 (shared ) b0) a0)) := by
  cases heq
theorem cp_16_root_15 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (aux1 (shared ) a0)) = (op (aux0 (shared ) b0) (aux1 (shared ) b0))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  rcases T.aux1.inj he1 with ⟨he2, he3⟩
  clear he1
  revert he0 he2
  subst a0
  intro he0 he2
  clear he2
  cases he0
theorem cp_16_1_15 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) = (op (aux0 (shared ) b0) (aux1 (shared ) b0))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_16_1_1_15 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (op (aux0 (shared ) b0) (aux1 (shared ) b0))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) (aux0 (shared ) a0)) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_16_1_1_1_15 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux0 (shared ) b0) (aux1 (shared ) b0))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) a0) (aux0 (shared ) a0)) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_16_1_2_15 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (op (aux0 (shared ) b0) (aux1 (shared ) b0))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (shared ) a0) (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0))) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_16_1_2_1_15 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux0 (shared ) b0) (aux1 (shared ) b0))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (shared ) a0) (aux0 (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) a0)) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_16_2_15 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) a0) = (op (aux0 (shared ) b0) (aux1 (shared ) b0))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0))) := by
  cases heq
theorem cp_16_2_1_15 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux0 (shared ) b0) (aux1 (shared ) b0))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (aux1 (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) a0)) := by
  cases heq
theorem cp_16_root_16 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (op (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (aux1 (shared ) a0)) = (op (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) (aux1 (shared ) b0))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (aux0 (aux0 (shared ) b0) (aux1 (shared ) b0)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  rcases T.aux1.inj he1 with ⟨he2, he3⟩
  clear he1
  revert he0 he2
  subst a0
  intro he0 he2
  clear he2
  clear he0
  exact ⟨(aux0 (aux0 (shared ) b0) (aux1 (shared ) b0)), (Relation.ReflTransGen.refl), (Relation.ReflTransGen.refl)⟩
theorem cp_16_1_16 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) = (op (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) (aux1 (shared ) b0))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux0 (aux0 (shared ) b0) (aux1 (shared ) b0)) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_16_1_1_16 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (op (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) (aux1 (shared ) b0))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (aux0 (shared ) b0) (aux1 (shared ) b0)) (aux0 (shared ) a0)) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_16_1_1_1_16 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) (aux1 (shared ) b0))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (aux0 (aux0 (shared ) b0) (aux1 (shared ) b0)) a0) (aux0 (shared ) a0)) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_16_1_2_16 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux0 (shared ) a0) = (op (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) (aux1 (shared ) b0))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (shared ) a0) (aux0 (aux0 (shared ) b0) (aux1 (shared ) b0))) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_16_1_2_1_16 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) (aux1 (shared ) b0))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (shared ) a0) (aux0 (aux0 (aux0 (shared ) b0) (aux1 (shared ) b0)) a0)) (aux1 (shared ) a0)) := by
  cases heq
theorem cp_16_2_16 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (aux1 (shared ) a0) = (op (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) (aux1 (shared ) b0))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (aux0 (aux0 (shared ) b0) (aux1 (shared ) b0))) := by
  cases heq
theorem cp_16_2_1_16 (a0 a1 a2 b0 b1 b2 : T)
    (heq : (shared ) = (op (aux1 (aux0 (shared ) b0) (aux0 (shared ) b0)) (aux1 (shared ) b0))) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (aux1 (aux0 (aux0 (shared ) b0) (aux1 (shared ) b0)) a0)) := by
  cases heq
theorem var_0_1 (a0 a1 a2 v : T) (hv : Step a0 v) :
    Join (shared ) (op v a0) := by
  exact ⟨(shared ), (Relation.ReflTransGen.refl), (((Relation.ReflTransGen.refl).tail (Step.c_op_2 v hv)).tail (root_step .r0 v a1 a2))⟩
theorem var_0_2 (a0 a1 a2 v : T) (hv : Step a0 v) :
    Join (shared ) (op a0 v) := by
  exact ⟨(shared ), (Relation.ReflTransGen.refl), (((Relation.ReflTransGen.refl).tail (Step.c_op_1 v hv)).tail (root_step .r0 v a1 a2))⟩
theorem var_1_1_1 (a0 a1 a2 v : T) (hv : Step a0 v) :
    Join (aux0 a0 a1) (op (op v a1) a1) := by
  exact ⟨(aux0 v a1), ((Relation.ReflTransGen.refl).tail (Step.c_aux0_1 a1 hv)), ((Relation.ReflTransGen.refl).tail (root_step .r1 v a1 a2))⟩
theorem var_1_1_2 (a0 a1 a2 v : T) (hv : Step a1 v) :
    Join (aux0 a0 a1) (op (op a0 v) a1) := by
  exact ⟨(aux0 a0 v), ((Relation.ReflTransGen.refl).tail (Step.c_aux0_2 a0 hv)), (((Relation.ReflTransGen.refl).tail (Step.c_op_2 (op a0 v) hv)).tail (root_step .r1 a0 v a2))⟩
theorem var_1_2 (a0 a1 a2 v : T) (hv : Step a1 v) :
    Join (aux0 a0 a1) (op (op a0 a1) v) := by
  exact ⟨(aux0 a0 v), ((Relation.ReflTransGen.refl).tail (Step.c_aux0_2 a0 hv)), (((Relation.ReflTransGen.refl).tail (Step.c_op_1 v (Step.c_op_2 a0 hv))).tail (root_step .r1 a0 v a2))⟩
theorem var_2_2 (a0 a1 a2 v : T) (hv : Step a0 v) :
    Join (aux0 a0 a0) (op (shared ) v) := by
  exact ⟨(aux0 v v), (((Relation.ReflTransGen.refl).tail (Step.c_aux0_1 a0 hv)).tail (Step.c_aux0_2 v hv)), ((Relation.ReflTransGen.refl).tail (root_step .r2 v a1 a2))⟩
theorem var_3_1 (a0 a1 a2 v : T) (hv : Step a0 v) :
    Join (aux1 a0 a1) (op v (aux0 a0 a1)) := by
  exact ⟨(aux1 v a1), ((Relation.ReflTransGen.refl).tail (Step.c_aux1_1 a1 hv)), (((Relation.ReflTransGen.refl).tail (Step.c_op_2 v (Step.c_aux0_1 a1 hv))).tail (root_step .r3 v a1 a2))⟩
theorem var_3_2_1 (a0 a1 a2 v : T) (hv : Step a0 v) :
    Join (aux1 a0 a1) (op a0 (aux0 v a1)) := by
  exact ⟨(aux1 v a1), ((Relation.ReflTransGen.refl).tail (Step.c_aux1_1 a1 hv)), (((Relation.ReflTransGen.refl).tail (Step.c_op_1 (aux0 v a1) hv)).tail (root_step .r3 v a1 a2))⟩
theorem var_3_2_2 (a0 a1 a2 v : T) (hv : Step a1 v) :
    Join (aux1 a0 a1) (op a0 (aux0 a0 v)) := by
  exact ⟨(aux1 a0 v), ((Relation.ReflTransGen.refl).tail (Step.c_aux1_2 a0 hv)), ((Relation.ReflTransGen.refl).tail (root_step .r3 a0 v a2))⟩
theorem var_4_1_1 (a0 a1 a2 v : T) (hv : Step a0 v) :
    Join (aux0 (op a0 a1) a1) (op (aux0 v a1) a1) := by
  exact ⟨(aux0 (op v a1) a1), ((Relation.ReflTransGen.refl).tail (Step.c_aux0_1 a1 (Step.c_op_1 a1 hv))), ((Relation.ReflTransGen.refl).tail (root_step .r4 v a1 a2))⟩
theorem var_4_1_2 (a0 a1 a2 v : T) (hv : Step a1 v) :
    Join (aux0 (op a0 a1) a1) (op (aux0 a0 v) a1) := by
  exact ⟨(aux0 (op a0 v) v), (((Relation.ReflTransGen.refl).tail (Step.c_aux0_1 a1 (Step.c_op_2 a0 hv))).tail (Step.c_aux0_2 (op a0 v) hv)), (((Relation.ReflTransGen.refl).tail (Step.c_op_2 (aux0 a0 v) hv)).tail (root_step .r4 a0 v a2))⟩
theorem var_4_2 (a0 a1 a2 v : T) (hv : Step a1 v) :
    Join (aux0 (op a0 a1) a1) (op (aux0 a0 a1) v) := by
  exact ⟨(aux0 (op a0 v) v), (((Relation.ReflTransGen.refl).tail (Step.c_aux0_1 a1 (Step.c_op_2 a0 hv))).tail (Step.c_aux0_2 (op a0 v) hv)), (((Relation.ReflTransGen.refl).tail (Step.c_op_1 v (Step.c_aux0_2 a0 hv))).tail (root_step .r4 a0 v a2))⟩
theorem var_7_1_1 (a0 a1 a2 v : T) (hv : Step a0 v) :
    Join a0 (aux0 (aux1 v a1) (aux1 a0 a1)) := by
  exact ⟨v, ((Relation.ReflTransGen.refl).tail hv), (((Relation.ReflTransGen.refl).tail (Step.c_aux0_2 (aux1 v a1) (Step.c_aux1_1 a1 hv))).tail (root_step .r7 v a1 a2))⟩
theorem var_7_1_2 (a0 a1 a2 v : T) (hv : Step a1 v) :
    Join a0 (aux0 (aux1 a0 v) (aux1 a0 a1)) := by
  exact ⟨a0, (Relation.ReflTransGen.refl), (((Relation.ReflTransGen.refl).tail (Step.c_aux0_2 (aux1 a0 v) (Step.c_aux1_2 a0 hv))).tail (root_step .r7 a0 v a2))⟩
theorem var_7_2_1 (a0 a1 a2 v : T) (hv : Step a0 v) :
    Join a0 (aux0 (aux1 a0 a1) (aux1 v a1)) := by
  exact ⟨v, ((Relation.ReflTransGen.refl).tail hv), (((Relation.ReflTransGen.refl).tail (Step.c_aux0_1 (aux1 v a1) (Step.c_aux1_1 a1 hv))).tail (root_step .r7 v a1 a2))⟩
theorem var_7_2_2 (a0 a1 a2 v : T) (hv : Step a1 v) :
    Join a0 (aux0 (aux1 a0 a1) (aux1 a0 v)) := by
  exact ⟨a0, (Relation.ReflTransGen.refl), (((Relation.ReflTransGen.refl).tail (Step.c_aux0_1 (aux1 a0 v) (Step.c_aux1_2 a0 hv))).tail (root_step .r7 a0 v a2))⟩
theorem var_8_1_1 (a0 a1 a2 v : T) (hv : Step a0 v) :
    Join (aux0 a0 (aux0 a0 a1)) (op (aux1 v a1) (aux0 a0 a1)) := by
  exact ⟨(aux0 v (aux0 v a1)), (((Relation.ReflTransGen.refl).tail (Step.c_aux0_1 (aux0 a0 a1) hv)).tail (Step.c_aux0_2 v (Step.c_aux0_1 a1 hv))), (((Relation.ReflTransGen.refl).tail (Step.c_op_2 (aux1 v a1) (Step.c_aux0_1 a1 hv))).tail (root_step .r8 v a1 a2))⟩
theorem var_8_1_2 (a0 a1 a2 v : T) (hv : Step a1 v) :
    Join (aux0 a0 (aux0 a0 a1)) (op (aux1 a0 v) (aux0 a0 a1)) := by
  exact ⟨(aux0 a0 (aux0 a0 v)), ((Relation.ReflTransGen.refl).tail (Step.c_aux0_2 a0 (Step.c_aux0_2 a0 hv))), (((Relation.ReflTransGen.refl).tail (Step.c_op_2 (aux1 a0 v) (Step.c_aux0_2 a0 hv))).tail (root_step .r8 a0 v a2))⟩
theorem var_8_2_1 (a0 a1 a2 v : T) (hv : Step a0 v) :
    Join (aux0 a0 (aux0 a0 a1)) (op (aux1 a0 a1) (aux0 v a1)) := by
  exact ⟨(aux0 v (aux0 v a1)), (((Relation.ReflTransGen.refl).tail (Step.c_aux0_1 (aux0 a0 a1) hv)).tail (Step.c_aux0_2 v (Step.c_aux0_1 a1 hv))), (((Relation.ReflTransGen.refl).tail (Step.c_op_1 (aux0 v a1) (Step.c_aux1_1 a1 hv))).tail (root_step .r8 v a1 a2))⟩
theorem var_8_2_2 (a0 a1 a2 v : T) (hv : Step a1 v) :
    Join (aux0 a0 (aux0 a0 a1)) (op (aux1 a0 a1) (aux0 a0 v)) := by
  exact ⟨(aux0 a0 (aux0 a0 v)), ((Relation.ReflTransGen.refl).tail (Step.c_aux0_2 a0 (Step.c_aux0_2 a0 hv))), (((Relation.ReflTransGen.refl).tail (Step.c_op_1 (aux0 a0 v) (Step.c_aux1_2 a0 hv))).tail (root_step .r8 a0 v a2))⟩
theorem var_9_1_1 (a0 a1 a2 v : T) (hv : Step a0 v) :
    Join (aux1 (aux1 a0 a1) (aux1 a0 a1)) (op (aux1 v a1) a0) := by
  exact ⟨(aux1 (aux1 v a1) (aux1 v a1)), (((Relation.ReflTransGen.refl).tail (Step.c_aux1_1 (aux1 a0 a1) (Step.c_aux1_1 a1 hv))).tail (Step.c_aux1_2 (aux1 v a1) (Step.c_aux1_1 a1 hv))), (((Relation.ReflTransGen.refl).tail (Step.c_op_2 (aux1 v a1) hv)).tail (root_step .r9 v a1 a2))⟩
theorem var_9_1_2 (a0 a1 a2 v : T) (hv : Step a1 v) :
    Join (aux1 (aux1 a0 a1) (aux1 a0 a1)) (op (aux1 a0 v) a0) := by
  exact ⟨(aux1 (aux1 a0 v) (aux1 a0 v)), (((Relation.ReflTransGen.refl).tail (Step.c_aux1_1 (aux1 a0 a1) (Step.c_aux1_2 a0 hv))).tail (Step.c_aux1_2 (aux1 a0 v) (Step.c_aux1_2 a0 hv))), ((Relation.ReflTransGen.refl).tail (root_step .r9 a0 v a2))⟩
theorem var_9_2 (a0 a1 a2 v : T) (hv : Step a0 v) :
    Join (aux1 (aux1 a0 a1) (aux1 a0 a1)) (op (aux1 a0 a1) v) := by
  exact ⟨(aux1 (aux1 v a1) (aux1 v a1)), (((Relation.ReflTransGen.refl).tail (Step.c_aux1_1 (aux1 a0 a1) (Step.c_aux1_1 a1 hv))).tail (Step.c_aux1_2 (aux1 v a1) (Step.c_aux1_1 a1 hv))), (((Relation.ReflTransGen.refl).tail (Step.c_op_1 v (Step.c_aux1_1 a1 hv))).tail (root_step .r9 v a1 a2))⟩
theorem var_10_1 (a0 a1 a2 v : T) (hv : Step a0 v) :
    Join (aux0 (shared ) (aux1 a0 a1)) (op v (aux1 a0 a1)) := by
  exact ⟨(aux0 (shared ) (aux1 v a1)), ((Relation.ReflTransGen.refl).tail (Step.c_aux0_2 (shared ) (Step.c_aux1_1 a1 hv))), (((Relation.ReflTransGen.refl).tail (Step.c_op_2 v (Step.c_aux1_1 a1 hv))).tail (root_step .r10 v a1 a2))⟩
theorem var_10_2_1 (a0 a1 a2 v : T) (hv : Step a0 v) :
    Join (aux0 (shared ) (aux1 a0 a1)) (op a0 (aux1 v a1)) := by
  exact ⟨(aux0 (shared ) (aux1 v a1)), ((Relation.ReflTransGen.refl).tail (Step.c_aux0_2 (shared ) (Step.c_aux1_1 a1 hv))), (((Relation.ReflTransGen.refl).tail (Step.c_op_1 (aux1 v a1) hv)).tail (root_step .r10 v a1 a2))⟩
theorem var_10_2_2 (a0 a1 a2 v : T) (hv : Step a1 v) :
    Join (aux0 (shared ) (aux1 a0 a1)) (op a0 (aux1 a0 v)) := by
  exact ⟨(aux0 (shared ) (aux1 a0 v)), ((Relation.ReflTransGen.refl).tail (Step.c_aux0_2 (shared ) (Step.c_aux1_2 a0 hv))), ((Relation.ReflTransGen.refl).tail (root_step .r10 a0 v a2))⟩
theorem var_11_2_2 (a0 a1 a2 v : T) (hv : Step a0 v) :
    Join (shared ) (aux0 (shared ) (aux1 (shared ) v)) := by
  exact ⟨(shared ), (Relation.ReflTransGen.refl), ((Relation.ReflTransGen.refl).tail (root_step .r11 v a1 a2))⟩
theorem var_12_2_2 (a0 a1 a2 v : T) (hv : Step a0 v) :
    Join (shared ) (aux1 (shared ) (aux1 (shared ) v)) := by
  exact ⟨(shared ), (Relation.ReflTransGen.refl), ((Relation.ReflTransGen.refl).tail (root_step .r12 v a1 a2))⟩
theorem var_13_1_1_1 (a0 a1 a2 v : T) (hv : Step a0 v) :
    Join (aux0 (aux1 a0 a1) a0) (op (aux1 (aux1 v a1) (aux1 a0 a1)) a0) := by
  exact ⟨(aux0 (aux1 v a1) v), (((Relation.ReflTransGen.refl).tail (Step.c_aux0_1 a0 (Step.c_aux1_1 a1 hv))).tail (Step.c_aux0_2 (aux1 v a1) hv)), ((((Relation.ReflTransGen.refl).tail (Step.c_op_1 a0 (Step.c_aux1_2 (aux1 v a1) (Step.c_aux1_1 a1 hv)))).tail (Step.c_op_2 (aux1 (aux1 v a1) (aux1 v a1)) hv)).tail (root_step .r13 v a1 a2))⟩
theorem var_13_1_1_2 (a0 a1 a2 v : T) (hv : Step a1 v) :
    Join (aux0 (aux1 a0 a1) a0) (op (aux1 (aux1 a0 v) (aux1 a0 a1)) a0) := by
  exact ⟨(aux0 (aux1 a0 v) a0), ((Relation.ReflTransGen.refl).tail (Step.c_aux0_1 a0 (Step.c_aux1_2 a0 hv))), (((Relation.ReflTransGen.refl).tail (Step.c_op_1 a0 (Step.c_aux1_2 (aux1 a0 v) (Step.c_aux1_2 a0 hv)))).tail (root_step .r13 a0 v a2))⟩
theorem var_13_1_2_1 (a0 a1 a2 v : T) (hv : Step a0 v) :
    Join (aux0 (aux1 a0 a1) a0) (op (aux1 (aux1 a0 a1) (aux1 v a1)) a0) := by
  exact ⟨(aux0 (aux1 v a1) v), (((Relation.ReflTransGen.refl).tail (Step.c_aux0_1 a0 (Step.c_aux1_1 a1 hv))).tail (Step.c_aux0_2 (aux1 v a1) hv)), ((((Relation.ReflTransGen.refl).tail (Step.c_op_1 a0 (Step.c_aux1_1 (aux1 v a1) (Step.c_aux1_1 a1 hv)))).tail (Step.c_op_2 (aux1 (aux1 v a1) (aux1 v a1)) hv)).tail (root_step .r13 v a1 a2))⟩
theorem var_13_1_2_2 (a0 a1 a2 v : T) (hv : Step a1 v) :
    Join (aux0 (aux1 a0 a1) a0) (op (aux1 (aux1 a0 a1) (aux1 a0 v)) a0) := by
  exact ⟨(aux0 (aux1 a0 v) a0), ((Relation.ReflTransGen.refl).tail (Step.c_aux0_1 a0 (Step.c_aux1_2 a0 hv))), (((Relation.ReflTransGen.refl).tail (Step.c_op_1 a0 (Step.c_aux1_1 (aux1 a0 v) (Step.c_aux1_2 a0 hv)))).tail (root_step .r13 a0 v a2))⟩
theorem var_13_2 (a0 a1 a2 v : T) (hv : Step a0 v) :
    Join (aux0 (aux1 a0 a1) a0) (op (aux1 (aux1 a0 a1) (aux1 a0 a1)) v) := by
  exact ⟨(aux0 (aux1 v a1) v), (((Relation.ReflTransGen.refl).tail (Step.c_aux0_1 a0 (Step.c_aux1_1 a1 hv))).tail (Step.c_aux0_2 (aux1 v a1) hv)), ((((Relation.ReflTransGen.refl).tail (Step.c_op_1 v (Step.c_aux1_1 (aux1 a0 a1) (Step.c_aux1_1 a1 hv)))).tail (Step.c_op_1 v (Step.c_aux1_2 (aux1 v a1) (Step.c_aux1_1 a1 hv)))).tail (root_step .r13 v a1 a2))⟩
theorem var_14_1_2 (a0 a1 a2 v : T) (hv : Step a0 v) :
    Join (aux1 (shared ) a0) (aux0 (aux0 (shared ) v) (aux0 (shared ) a0)) := by
  exact ⟨(aux1 (shared ) v), ((Relation.ReflTransGen.refl).tail (Step.c_aux1_2 (shared ) hv)), (((Relation.ReflTransGen.refl).tail (Step.c_aux0_2 (aux0 (shared ) v) (Step.c_aux0_2 (shared ) hv))).tail (root_step .r14 v a1 a2))⟩
theorem var_14_2_2 (a0 a1 a2 v : T) (hv : Step a0 v) :
    Join (aux1 (shared ) a0) (aux0 (aux0 (shared ) a0) (aux0 (shared ) v)) := by
  exact ⟨(aux1 (shared ) v), ((Relation.ReflTransGen.refl).tail (Step.c_aux1_2 (shared ) hv)), (((Relation.ReflTransGen.refl).tail (Step.c_aux0_1 (aux0 (shared ) v) (Step.c_aux0_2 (shared ) hv))).tail (root_step .r14 v a1 a2))⟩
theorem var_15_1_2 (a0 a1 a2 v : T) (hv : Step a0 v) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (op (aux0 (shared ) v) (aux1 (shared ) a0)) := by
  exact ⟨(aux1 (aux0 (shared ) v) (aux0 (shared ) v)), (((Relation.ReflTransGen.refl).tail (Step.c_aux1_1 (aux0 (shared ) a0) (Step.c_aux0_2 (shared ) hv))).tail (Step.c_aux1_2 (aux0 (shared ) v) (Step.c_aux0_2 (shared ) hv))), (((Relation.ReflTransGen.refl).tail (Step.c_op_2 (aux0 (shared ) v) (Step.c_aux1_2 (shared ) hv))).tail (root_step .r15 v a1 a2))⟩
theorem var_15_2_2 (a0 a1 a2 v : T) (hv : Step a0 v) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (op (aux0 (shared ) a0) (aux1 (shared ) v)) := by
  exact ⟨(aux1 (aux0 (shared ) v) (aux0 (shared ) v)), (((Relation.ReflTransGen.refl).tail (Step.c_aux1_1 (aux0 (shared ) a0) (Step.c_aux0_2 (shared ) hv))).tail (Step.c_aux1_2 (aux0 (shared ) v) (Step.c_aux0_2 (shared ) hv))), (((Relation.ReflTransGen.refl).tail (Step.c_op_1 (aux1 (shared ) v) (Step.c_aux0_2 (shared ) hv))).tail (root_step .r15 v a1 a2))⟩
theorem var_16_1_1_2 (a0 a1 a2 v : T) (hv : Step a0 v) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (shared ) v) (aux0 (shared ) a0)) (aux1 (shared ) a0)) := by
  exact ⟨(aux0 (aux0 (shared ) v) (aux1 (shared ) v)), (((Relation.ReflTransGen.refl).tail (Step.c_aux0_1 (aux1 (shared ) a0) (Step.c_aux0_2 (shared ) hv))).tail (Step.c_aux0_2 (aux0 (shared ) v) (Step.c_aux1_2 (shared ) hv))), ((((Relation.ReflTransGen.refl).tail (Step.c_op_1 (aux1 (shared ) a0) (Step.c_aux1_2 (aux0 (shared ) v) (Step.c_aux0_2 (shared ) hv)))).tail (Step.c_op_2 (aux1 (aux0 (shared ) v) (aux0 (shared ) v)) (Step.c_aux1_2 (shared ) hv))).tail (root_step .r16 v a1 a2))⟩
theorem var_16_1_2_2 (a0 a1 a2 v : T) (hv : Step a0 v) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (shared ) a0) (aux0 (shared ) v)) (aux1 (shared ) a0)) := by
  exact ⟨(aux0 (aux0 (shared ) v) (aux1 (shared ) v)), (((Relation.ReflTransGen.refl).tail (Step.c_aux0_1 (aux1 (shared ) a0) (Step.c_aux0_2 (shared ) hv))).tail (Step.c_aux0_2 (aux0 (shared ) v) (Step.c_aux1_2 (shared ) hv))), ((((Relation.ReflTransGen.refl).tail (Step.c_op_1 (aux1 (shared ) a0) (Step.c_aux1_1 (aux0 (shared ) v) (Step.c_aux0_2 (shared ) hv)))).tail (Step.c_op_2 (aux1 (aux0 (shared ) v) (aux0 (shared ) v)) (Step.c_aux1_2 (shared ) hv))).tail (root_step .r16 v a1 a2))⟩
theorem var_16_2_2 (a0 a1 a2 v : T) (hv : Step a0 v) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) (op (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (aux1 (shared ) v)) := by
  exact ⟨(aux0 (aux0 (shared ) v) (aux1 (shared ) v)), (((Relation.ReflTransGen.refl).tail (Step.c_aux0_1 (aux1 (shared ) a0) (Step.c_aux0_2 (shared ) hv))).tail (Step.c_aux0_2 (aux0 (shared ) v) (Step.c_aux1_2 (shared ) hv))), ((((Relation.ReflTransGen.refl).tail (Step.c_op_1 (aux1 (shared ) v) (Step.c_aux1_1 (aux0 (shared ) a0) (Step.c_aux0_2 (shared ) hv)))).tail (Step.c_op_1 (aux1 (shared ) v) (Step.c_aux1_2 (aux0 (shared ) v) (Step.c_aux0_2 (shared ) hv)))).tail (root_step .r16 v a1 a2))⟩
theorem peak_0 (a0 a1 a2 : T) {u : T} (h : Step (op a0 a0) u) :
    Join (shared ) u := by
  rcases step_op_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
  · rcases hr with ⟨k, b0, b1, b2, heq, hout⟩
    rw [hout]
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
    | r10 => exact cp_0_root_10 a0 a1 a2 b0 b1 b2 heq
    | r11 => exact cp_0_root_11 a0 a1 a2 b0 b1 b2 heq
    | r12 => exact cp_0_root_12 a0 a1 a2 b0 b1 b2 heq
    | r13 => exact cp_0_root_13 a0 a1 a2 b0 b1 b2 heq
    | r14 => exact cp_0_root_14 a0 a1 a2 b0 b1 b2 heq
    | r15 => exact cp_0_root_15 a0 a1 a2 b0 b1 b2 heq
    | r16 => exact cp_0_root_16 a0 a1 a2 b0 b1 b2 heq
  ·
    exact var_0_1 a0 a1 a2 u0 h0
  ·
    exact var_0_2 a0 a1 a2 u0 h0
theorem peak_1 (a0 a1 a2 : T) {u : T} (h : Step (op (op a0 a1) a1) u) :
    Join (aux0 a0 a1) u := by
  rcases step_op_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
  · rcases hr with ⟨k, b0, b1, b2, heq, hout⟩
    rw [hout]
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
    | r10 => exact cp_1_root_10 a0 a1 a2 b0 b1 b2 heq
    | r11 => exact cp_1_root_11 a0 a1 a2 b0 b1 b2 heq
    | r12 => exact cp_1_root_12 a0 a1 a2 b0 b1 b2 heq
    | r13 => exact cp_1_root_13 a0 a1 a2 b0 b1 b2 heq
    | r14 => exact cp_1_root_14 a0 a1 a2 b0 b1 b2 heq
    | r15 => exact cp_1_root_15 a0 a1 a2 b0 b1 b2 heq
    | r16 => exact cp_1_root_16 a0 a1 a2 b0 b1 b2 heq
  ·
    rcases step_op_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
    · rcases hr with ⟨k, b0, b1, b2, heq, hout⟩
      rw [hout]
      cases k with
      | r0 => exact cp_1_1_0 a0 a1 a2 b0 b1 b2 heq
      | r1 => exact cp_1_1_1 a0 a1 a2 b0 b1 b2 heq
      | r2 => exact cp_1_1_2 a0 a1 a2 b0 b1 b2 heq
      | r3 => exact cp_1_1_3 a0 a1 a2 b0 b1 b2 heq
      | r4 => exact cp_1_1_4 a0 a1 a2 b0 b1 b2 heq
      | r5 => exact cp_1_1_5 a0 a1 a2 b0 b1 b2 heq
      | r6 => exact cp_1_1_6 a0 a1 a2 b0 b1 b2 heq
      | r7 => exact cp_1_1_7 a0 a1 a2 b0 b1 b2 heq
      | r8 => exact cp_1_1_8 a0 a1 a2 b0 b1 b2 heq
      | r9 => exact cp_1_1_9 a0 a1 a2 b0 b1 b2 heq
      | r10 => exact cp_1_1_10 a0 a1 a2 b0 b1 b2 heq
      | r11 => exact cp_1_1_11 a0 a1 a2 b0 b1 b2 heq
      | r12 => exact cp_1_1_12 a0 a1 a2 b0 b1 b2 heq
      | r13 => exact cp_1_1_13 a0 a1 a2 b0 b1 b2 heq
      | r14 => exact cp_1_1_14 a0 a1 a2 b0 b1 b2 heq
      | r15 => exact cp_1_1_15 a0 a1 a2 b0 b1 b2 heq
      | r16 => exact cp_1_1_16 a0 a1 a2 b0 b1 b2 heq
    ·
      exact var_1_1_1 a0 a1 a2 u1 h1
    ·
      exact var_1_1_2 a0 a1 a2 u1 h1
  ·
    exact var_1_2 a0 a1 a2 u0 h0
theorem peak_2 (a0 a1 a2 : T) {u : T} (h : Step (op (shared ) a0) u) :
    Join (aux0 a0 a0) u := by
  rcases step_op_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
  · rcases hr with ⟨k, b0, b1, b2, heq, hout⟩
    rw [hout]
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
    | r10 => exact cp_2_root_10 a0 a1 a2 b0 b1 b2 heq
    | r11 => exact cp_2_root_11 a0 a1 a2 b0 b1 b2 heq
    | r12 => exact cp_2_root_12 a0 a1 a2 b0 b1 b2 heq
    | r13 => exact cp_2_root_13 a0 a1 a2 b0 b1 b2 heq
    | r14 => exact cp_2_root_14 a0 a1 a2 b0 b1 b2 heq
    | r15 => exact cp_2_root_15 a0 a1 a2 b0 b1 b2 heq
    | r16 => exact cp_2_root_16 a0 a1 a2 b0 b1 b2 heq
  ·
    rcases step_shared_cases h0 with hr
    · rcases hr with ⟨k, b0, b1, b2, heq, hout⟩
      rw [hout]
      cases k with
      | r0 => exact cp_2_1_0 a0 a1 a2 b0 b1 b2 heq
      | r1 => exact cp_2_1_1 a0 a1 a2 b0 b1 b2 heq
      | r2 => exact cp_2_1_2 a0 a1 a2 b0 b1 b2 heq
      | r3 => exact cp_2_1_3 a0 a1 a2 b0 b1 b2 heq
      | r4 => exact cp_2_1_4 a0 a1 a2 b0 b1 b2 heq
      | r5 => exact cp_2_1_5 a0 a1 a2 b0 b1 b2 heq
      | r6 => exact cp_2_1_6 a0 a1 a2 b0 b1 b2 heq
      | r7 => exact cp_2_1_7 a0 a1 a2 b0 b1 b2 heq
      | r8 => exact cp_2_1_8 a0 a1 a2 b0 b1 b2 heq
      | r9 => exact cp_2_1_9 a0 a1 a2 b0 b1 b2 heq
      | r10 => exact cp_2_1_10 a0 a1 a2 b0 b1 b2 heq
      | r11 => exact cp_2_1_11 a0 a1 a2 b0 b1 b2 heq
      | r12 => exact cp_2_1_12 a0 a1 a2 b0 b1 b2 heq
      | r13 => exact cp_2_1_13 a0 a1 a2 b0 b1 b2 heq
      | r14 => exact cp_2_1_14 a0 a1 a2 b0 b1 b2 heq
      | r15 => exact cp_2_1_15 a0 a1 a2 b0 b1 b2 heq
      | r16 => exact cp_2_1_16 a0 a1 a2 b0 b1 b2 heq
  ·
    exact var_2_2 a0 a1 a2 u0 h0
theorem peak_3 (a0 a1 a2 : T) {u : T} (h : Step (op a0 (aux0 a0 a1)) u) :
    Join (aux1 a0 a1) u := by
  rcases step_op_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
  · rcases hr with ⟨k, b0, b1, b2, heq, hout⟩
    rw [hout]
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
    | r10 => exact cp_3_root_10 a0 a1 a2 b0 b1 b2 heq
    | r11 => exact cp_3_root_11 a0 a1 a2 b0 b1 b2 heq
    | r12 => exact cp_3_root_12 a0 a1 a2 b0 b1 b2 heq
    | r13 => exact cp_3_root_13 a0 a1 a2 b0 b1 b2 heq
    | r14 => exact cp_3_root_14 a0 a1 a2 b0 b1 b2 heq
    | r15 => exact cp_3_root_15 a0 a1 a2 b0 b1 b2 heq
    | r16 => exact cp_3_root_16 a0 a1 a2 b0 b1 b2 heq
  ·
    exact var_3_1 a0 a1 a2 u0 h0
  ·
    rcases step_aux0_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
    · rcases hr with ⟨k, b0, b1, b2, heq, hout⟩
      rw [hout]
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
      | r10 => exact cp_3_2_10 a0 a1 a2 b0 b1 b2 heq
      | r11 => exact cp_3_2_11 a0 a1 a2 b0 b1 b2 heq
      | r12 => exact cp_3_2_12 a0 a1 a2 b0 b1 b2 heq
      | r13 => exact cp_3_2_13 a0 a1 a2 b0 b1 b2 heq
      | r14 => exact cp_3_2_14 a0 a1 a2 b0 b1 b2 heq
      | r15 => exact cp_3_2_15 a0 a1 a2 b0 b1 b2 heq
      | r16 => exact cp_3_2_16 a0 a1 a2 b0 b1 b2 heq
    ·
      exact var_3_2_1 a0 a1 a2 u1 h1
    ·
      exact var_3_2_2 a0 a1 a2 u1 h1
theorem peak_4 (a0 a1 a2 : T) {u : T} (h : Step (op (aux0 a0 a1) a1) u) :
    Join (aux0 (op a0 a1) a1) u := by
  rcases step_op_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
  · rcases hr with ⟨k, b0, b1, b2, heq, hout⟩
    rw [hout]
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
    | r10 => exact cp_4_root_10 a0 a1 a2 b0 b1 b2 heq
    | r11 => exact cp_4_root_11 a0 a1 a2 b0 b1 b2 heq
    | r12 => exact cp_4_root_12 a0 a1 a2 b0 b1 b2 heq
    | r13 => exact cp_4_root_13 a0 a1 a2 b0 b1 b2 heq
    | r14 => exact cp_4_root_14 a0 a1 a2 b0 b1 b2 heq
    | r15 => exact cp_4_root_15 a0 a1 a2 b0 b1 b2 heq
    | r16 => exact cp_4_root_16 a0 a1 a2 b0 b1 b2 heq
  ·
    rcases step_aux0_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
    · rcases hr with ⟨k, b0, b1, b2, heq, hout⟩
      rw [hout]
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
      | r10 => exact cp_4_1_10 a0 a1 a2 b0 b1 b2 heq
      | r11 => exact cp_4_1_11 a0 a1 a2 b0 b1 b2 heq
      | r12 => exact cp_4_1_12 a0 a1 a2 b0 b1 b2 heq
      | r13 => exact cp_4_1_13 a0 a1 a2 b0 b1 b2 heq
      | r14 => exact cp_4_1_14 a0 a1 a2 b0 b1 b2 heq
      | r15 => exact cp_4_1_15 a0 a1 a2 b0 b1 b2 heq
      | r16 => exact cp_4_1_16 a0 a1 a2 b0 b1 b2 heq
    ·
      exact var_4_1_1 a0 a1 a2 u1 h1
    ·
      exact var_4_1_2 a0 a1 a2 u1 h1
  ·
    exact var_4_2 a0 a1 a2 u0 h0
theorem peak_5 (a0 a1 a2 : T) {u : T} (h : Step (aux0 (shared ) (shared )) u) :
    Join (shared ) u := by
  rcases step_aux0_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
  · rcases hr with ⟨k, b0, b1, b2, heq, hout⟩
    rw [hout]
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
    | r10 => exact cp_5_root_10 a0 a1 a2 b0 b1 b2 heq
    | r11 => exact cp_5_root_11 a0 a1 a2 b0 b1 b2 heq
    | r12 => exact cp_5_root_12 a0 a1 a2 b0 b1 b2 heq
    | r13 => exact cp_5_root_13 a0 a1 a2 b0 b1 b2 heq
    | r14 => exact cp_5_root_14 a0 a1 a2 b0 b1 b2 heq
    | r15 => exact cp_5_root_15 a0 a1 a2 b0 b1 b2 heq
    | r16 => exact cp_5_root_16 a0 a1 a2 b0 b1 b2 heq
  ·
    rcases step_shared_cases h0 with hr
    · rcases hr with ⟨k, b0, b1, b2, heq, hout⟩
      rw [hout]
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
      | r10 => exact cp_5_1_10 a0 a1 a2 b0 b1 b2 heq
      | r11 => exact cp_5_1_11 a0 a1 a2 b0 b1 b2 heq
      | r12 => exact cp_5_1_12 a0 a1 a2 b0 b1 b2 heq
      | r13 => exact cp_5_1_13 a0 a1 a2 b0 b1 b2 heq
      | r14 => exact cp_5_1_14 a0 a1 a2 b0 b1 b2 heq
      | r15 => exact cp_5_1_15 a0 a1 a2 b0 b1 b2 heq
      | r16 => exact cp_5_1_16 a0 a1 a2 b0 b1 b2 heq
  ·
    rcases step_shared_cases h0 with hr
    · rcases hr with ⟨k, b0, b1, b2, heq, hout⟩
      rw [hout]
      cases k with
      | r0 => exact cp_5_2_0 a0 a1 a2 b0 b1 b2 heq
      | r1 => exact cp_5_2_1 a0 a1 a2 b0 b1 b2 heq
      | r2 => exact cp_5_2_2 a0 a1 a2 b0 b1 b2 heq
      | r3 => exact cp_5_2_3 a0 a1 a2 b0 b1 b2 heq
      | r4 => exact cp_5_2_4 a0 a1 a2 b0 b1 b2 heq
      | r5 => exact cp_5_2_5 a0 a1 a2 b0 b1 b2 heq
      | r6 => exact cp_5_2_6 a0 a1 a2 b0 b1 b2 heq
      | r7 => exact cp_5_2_7 a0 a1 a2 b0 b1 b2 heq
      | r8 => exact cp_5_2_8 a0 a1 a2 b0 b1 b2 heq
      | r9 => exact cp_5_2_9 a0 a1 a2 b0 b1 b2 heq
      | r10 => exact cp_5_2_10 a0 a1 a2 b0 b1 b2 heq
      | r11 => exact cp_5_2_11 a0 a1 a2 b0 b1 b2 heq
      | r12 => exact cp_5_2_12 a0 a1 a2 b0 b1 b2 heq
      | r13 => exact cp_5_2_13 a0 a1 a2 b0 b1 b2 heq
      | r14 => exact cp_5_2_14 a0 a1 a2 b0 b1 b2 heq
      | r15 => exact cp_5_2_15 a0 a1 a2 b0 b1 b2 heq
      | r16 => exact cp_5_2_16 a0 a1 a2 b0 b1 b2 heq
theorem peak_6 (a0 a1 a2 : T) {u : T} (h : Step (aux1 (shared ) (shared )) u) :
    Join (shared ) u := by
  rcases step_aux1_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
  · rcases hr with ⟨k, b0, b1, b2, heq, hout⟩
    rw [hout]
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
    | r10 => exact cp_6_root_10 a0 a1 a2 b0 b1 b2 heq
    | r11 => exact cp_6_root_11 a0 a1 a2 b0 b1 b2 heq
    | r12 => exact cp_6_root_12 a0 a1 a2 b0 b1 b2 heq
    | r13 => exact cp_6_root_13 a0 a1 a2 b0 b1 b2 heq
    | r14 => exact cp_6_root_14 a0 a1 a2 b0 b1 b2 heq
    | r15 => exact cp_6_root_15 a0 a1 a2 b0 b1 b2 heq
    | r16 => exact cp_6_root_16 a0 a1 a2 b0 b1 b2 heq
  ·
    rcases step_shared_cases h0 with hr
    · rcases hr with ⟨k, b0, b1, b2, heq, hout⟩
      rw [hout]
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
      | r10 => exact cp_6_1_10 a0 a1 a2 b0 b1 b2 heq
      | r11 => exact cp_6_1_11 a0 a1 a2 b0 b1 b2 heq
      | r12 => exact cp_6_1_12 a0 a1 a2 b0 b1 b2 heq
      | r13 => exact cp_6_1_13 a0 a1 a2 b0 b1 b2 heq
      | r14 => exact cp_6_1_14 a0 a1 a2 b0 b1 b2 heq
      | r15 => exact cp_6_1_15 a0 a1 a2 b0 b1 b2 heq
      | r16 => exact cp_6_1_16 a0 a1 a2 b0 b1 b2 heq
  ·
    rcases step_shared_cases h0 with hr
    · rcases hr with ⟨k, b0, b1, b2, heq, hout⟩
      rw [hout]
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
      | r10 => exact cp_6_2_10 a0 a1 a2 b0 b1 b2 heq
      | r11 => exact cp_6_2_11 a0 a1 a2 b0 b1 b2 heq
      | r12 => exact cp_6_2_12 a0 a1 a2 b0 b1 b2 heq
      | r13 => exact cp_6_2_13 a0 a1 a2 b0 b1 b2 heq
      | r14 => exact cp_6_2_14 a0 a1 a2 b0 b1 b2 heq
      | r15 => exact cp_6_2_15 a0 a1 a2 b0 b1 b2 heq
      | r16 => exact cp_6_2_16 a0 a1 a2 b0 b1 b2 heq
theorem peak_7 (a0 a1 a2 : T) {u : T} (h : Step (aux0 (aux1 a0 a1) (aux1 a0 a1)) u) :
    Join a0 u := by
  rcases step_aux0_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
  · rcases hr with ⟨k, b0, b1, b2, heq, hout⟩
    rw [hout]
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
    | r10 => exact cp_7_root_10 a0 a1 a2 b0 b1 b2 heq
    | r11 => exact cp_7_root_11 a0 a1 a2 b0 b1 b2 heq
    | r12 => exact cp_7_root_12 a0 a1 a2 b0 b1 b2 heq
    | r13 => exact cp_7_root_13 a0 a1 a2 b0 b1 b2 heq
    | r14 => exact cp_7_root_14 a0 a1 a2 b0 b1 b2 heq
    | r15 => exact cp_7_root_15 a0 a1 a2 b0 b1 b2 heq
    | r16 => exact cp_7_root_16 a0 a1 a2 b0 b1 b2 heq
  ·
    rcases step_aux1_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
    · rcases hr with ⟨k, b0, b1, b2, heq, hout⟩
      rw [hout]
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
      | r10 => exact cp_7_1_10 a0 a1 a2 b0 b1 b2 heq
      | r11 => exact cp_7_1_11 a0 a1 a2 b0 b1 b2 heq
      | r12 => exact cp_7_1_12 a0 a1 a2 b0 b1 b2 heq
      | r13 => exact cp_7_1_13 a0 a1 a2 b0 b1 b2 heq
      | r14 => exact cp_7_1_14 a0 a1 a2 b0 b1 b2 heq
      | r15 => exact cp_7_1_15 a0 a1 a2 b0 b1 b2 heq
      | r16 => exact cp_7_1_16 a0 a1 a2 b0 b1 b2 heq
    ·
      exact var_7_1_1 a0 a1 a2 u1 h1
    ·
      exact var_7_1_2 a0 a1 a2 u1 h1
  ·
    rcases step_aux1_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
    · rcases hr with ⟨k, b0, b1, b2, heq, hout⟩
      rw [hout]
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
      | r10 => exact cp_7_2_10 a0 a1 a2 b0 b1 b2 heq
      | r11 => exact cp_7_2_11 a0 a1 a2 b0 b1 b2 heq
      | r12 => exact cp_7_2_12 a0 a1 a2 b0 b1 b2 heq
      | r13 => exact cp_7_2_13 a0 a1 a2 b0 b1 b2 heq
      | r14 => exact cp_7_2_14 a0 a1 a2 b0 b1 b2 heq
      | r15 => exact cp_7_2_15 a0 a1 a2 b0 b1 b2 heq
      | r16 => exact cp_7_2_16 a0 a1 a2 b0 b1 b2 heq
    ·
      exact var_7_2_1 a0 a1 a2 u1 h1
    ·
      exact var_7_2_2 a0 a1 a2 u1 h1
theorem peak_8 (a0 a1 a2 : T) {u : T} (h : Step (op (aux1 a0 a1) (aux0 a0 a1)) u) :
    Join (aux0 a0 (aux0 a0 a1)) u := by
  rcases step_op_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
  · rcases hr with ⟨k, b0, b1, b2, heq, hout⟩
    rw [hout]
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
    | r10 => exact cp_8_root_10 a0 a1 a2 b0 b1 b2 heq
    | r11 => exact cp_8_root_11 a0 a1 a2 b0 b1 b2 heq
    | r12 => exact cp_8_root_12 a0 a1 a2 b0 b1 b2 heq
    | r13 => exact cp_8_root_13 a0 a1 a2 b0 b1 b2 heq
    | r14 => exact cp_8_root_14 a0 a1 a2 b0 b1 b2 heq
    | r15 => exact cp_8_root_15 a0 a1 a2 b0 b1 b2 heq
    | r16 => exact cp_8_root_16 a0 a1 a2 b0 b1 b2 heq
  ·
    rcases step_aux1_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
    · rcases hr with ⟨k, b0, b1, b2, heq, hout⟩
      rw [hout]
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
      | r10 => exact cp_8_1_10 a0 a1 a2 b0 b1 b2 heq
      | r11 => exact cp_8_1_11 a0 a1 a2 b0 b1 b2 heq
      | r12 => exact cp_8_1_12 a0 a1 a2 b0 b1 b2 heq
      | r13 => exact cp_8_1_13 a0 a1 a2 b0 b1 b2 heq
      | r14 => exact cp_8_1_14 a0 a1 a2 b0 b1 b2 heq
      | r15 => exact cp_8_1_15 a0 a1 a2 b0 b1 b2 heq
      | r16 => exact cp_8_1_16 a0 a1 a2 b0 b1 b2 heq
    ·
      exact var_8_1_1 a0 a1 a2 u1 h1
    ·
      exact var_8_1_2 a0 a1 a2 u1 h1
  ·
    rcases step_aux0_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
    · rcases hr with ⟨k, b0, b1, b2, heq, hout⟩
      rw [hout]
      cases k with
      | r0 => exact cp_8_2_0 a0 a1 a2 b0 b1 b2 heq
      | r1 => exact cp_8_2_1 a0 a1 a2 b0 b1 b2 heq
      | r2 => exact cp_8_2_2 a0 a1 a2 b0 b1 b2 heq
      | r3 => exact cp_8_2_3 a0 a1 a2 b0 b1 b2 heq
      | r4 => exact cp_8_2_4 a0 a1 a2 b0 b1 b2 heq
      | r5 => exact cp_8_2_5 a0 a1 a2 b0 b1 b2 heq
      | r6 => exact cp_8_2_6 a0 a1 a2 b0 b1 b2 heq
      | r7 => exact cp_8_2_7 a0 a1 a2 b0 b1 b2 heq
      | r8 => exact cp_8_2_8 a0 a1 a2 b0 b1 b2 heq
      | r9 => exact cp_8_2_9 a0 a1 a2 b0 b1 b2 heq
      | r10 => exact cp_8_2_10 a0 a1 a2 b0 b1 b2 heq
      | r11 => exact cp_8_2_11 a0 a1 a2 b0 b1 b2 heq
      | r12 => exact cp_8_2_12 a0 a1 a2 b0 b1 b2 heq
      | r13 => exact cp_8_2_13 a0 a1 a2 b0 b1 b2 heq
      | r14 => exact cp_8_2_14 a0 a1 a2 b0 b1 b2 heq
      | r15 => exact cp_8_2_15 a0 a1 a2 b0 b1 b2 heq
      | r16 => exact cp_8_2_16 a0 a1 a2 b0 b1 b2 heq
    ·
      exact var_8_2_1 a0 a1 a2 u1 h1
    ·
      exact var_8_2_2 a0 a1 a2 u1 h1
theorem peak_9 (a0 a1 a2 : T) {u : T} (h : Step (op (aux1 a0 a1) a0) u) :
    Join (aux1 (aux1 a0 a1) (aux1 a0 a1)) u := by
  rcases step_op_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
  · rcases hr with ⟨k, b0, b1, b2, heq, hout⟩
    rw [hout]
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
    | r10 => exact cp_9_root_10 a0 a1 a2 b0 b1 b2 heq
    | r11 => exact cp_9_root_11 a0 a1 a2 b0 b1 b2 heq
    | r12 => exact cp_9_root_12 a0 a1 a2 b0 b1 b2 heq
    | r13 => exact cp_9_root_13 a0 a1 a2 b0 b1 b2 heq
    | r14 => exact cp_9_root_14 a0 a1 a2 b0 b1 b2 heq
    | r15 => exact cp_9_root_15 a0 a1 a2 b0 b1 b2 heq
    | r16 => exact cp_9_root_16 a0 a1 a2 b0 b1 b2 heq
  ·
    rcases step_aux1_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
    · rcases hr with ⟨k, b0, b1, b2, heq, hout⟩
      rw [hout]
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
      | r10 => exact cp_9_1_10 a0 a1 a2 b0 b1 b2 heq
      | r11 => exact cp_9_1_11 a0 a1 a2 b0 b1 b2 heq
      | r12 => exact cp_9_1_12 a0 a1 a2 b0 b1 b2 heq
      | r13 => exact cp_9_1_13 a0 a1 a2 b0 b1 b2 heq
      | r14 => exact cp_9_1_14 a0 a1 a2 b0 b1 b2 heq
      | r15 => exact cp_9_1_15 a0 a1 a2 b0 b1 b2 heq
      | r16 => exact cp_9_1_16 a0 a1 a2 b0 b1 b2 heq
    ·
      exact var_9_1_1 a0 a1 a2 u1 h1
    ·
      exact var_9_1_2 a0 a1 a2 u1 h1
  ·
    exact var_9_2 a0 a1 a2 u0 h0
theorem peak_10 (a0 a1 a2 : T) {u : T} (h : Step (op a0 (aux1 a0 a1)) u) :
    Join (aux0 (shared ) (aux1 a0 a1)) u := by
  rcases step_op_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
  · rcases hr with ⟨k, b0, b1, b2, heq, hout⟩
    rw [hout]
    cases k with
    | r0 => exact cp_10_root_0 a0 a1 a2 b0 b1 b2 heq
    | r1 => exact cp_10_root_1 a0 a1 a2 b0 b1 b2 heq
    | r2 => exact cp_10_root_2 a0 a1 a2 b0 b1 b2 heq
    | r3 => exact cp_10_root_3 a0 a1 a2 b0 b1 b2 heq
    | r4 => exact cp_10_root_4 a0 a1 a2 b0 b1 b2 heq
    | r5 => exact cp_10_root_5 a0 a1 a2 b0 b1 b2 heq
    | r6 => exact cp_10_root_6 a0 a1 a2 b0 b1 b2 heq
    | r7 => exact cp_10_root_7 a0 a1 a2 b0 b1 b2 heq
    | r8 => exact cp_10_root_8 a0 a1 a2 b0 b1 b2 heq
    | r9 => exact cp_10_root_9 a0 a1 a2 b0 b1 b2 heq
    | r10 => exact cp_10_root_10 a0 a1 a2 b0 b1 b2 heq
    | r11 => exact cp_10_root_11 a0 a1 a2 b0 b1 b2 heq
    | r12 => exact cp_10_root_12 a0 a1 a2 b0 b1 b2 heq
    | r13 => exact cp_10_root_13 a0 a1 a2 b0 b1 b2 heq
    | r14 => exact cp_10_root_14 a0 a1 a2 b0 b1 b2 heq
    | r15 => exact cp_10_root_15 a0 a1 a2 b0 b1 b2 heq
    | r16 => exact cp_10_root_16 a0 a1 a2 b0 b1 b2 heq
  ·
    exact var_10_1 a0 a1 a2 u0 h0
  ·
    rcases step_aux1_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
    · rcases hr with ⟨k, b0, b1, b2, heq, hout⟩
      rw [hout]
      cases k with
      | r0 => exact cp_10_2_0 a0 a1 a2 b0 b1 b2 heq
      | r1 => exact cp_10_2_1 a0 a1 a2 b0 b1 b2 heq
      | r2 => exact cp_10_2_2 a0 a1 a2 b0 b1 b2 heq
      | r3 => exact cp_10_2_3 a0 a1 a2 b0 b1 b2 heq
      | r4 => exact cp_10_2_4 a0 a1 a2 b0 b1 b2 heq
      | r5 => exact cp_10_2_5 a0 a1 a2 b0 b1 b2 heq
      | r6 => exact cp_10_2_6 a0 a1 a2 b0 b1 b2 heq
      | r7 => exact cp_10_2_7 a0 a1 a2 b0 b1 b2 heq
      | r8 => exact cp_10_2_8 a0 a1 a2 b0 b1 b2 heq
      | r9 => exact cp_10_2_9 a0 a1 a2 b0 b1 b2 heq
      | r10 => exact cp_10_2_10 a0 a1 a2 b0 b1 b2 heq
      | r11 => exact cp_10_2_11 a0 a1 a2 b0 b1 b2 heq
      | r12 => exact cp_10_2_12 a0 a1 a2 b0 b1 b2 heq
      | r13 => exact cp_10_2_13 a0 a1 a2 b0 b1 b2 heq
      | r14 => exact cp_10_2_14 a0 a1 a2 b0 b1 b2 heq
      | r15 => exact cp_10_2_15 a0 a1 a2 b0 b1 b2 heq
      | r16 => exact cp_10_2_16 a0 a1 a2 b0 b1 b2 heq
    ·
      exact var_10_2_1 a0 a1 a2 u1 h1
    ·
      exact var_10_2_2 a0 a1 a2 u1 h1
theorem peak_11 (a0 a1 a2 : T) {u : T} (h : Step (aux0 (shared ) (aux1 (shared ) a0)) u) :
    Join (shared ) u := by
  rcases step_aux0_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
  · rcases hr with ⟨k, b0, b1, b2, heq, hout⟩
    rw [hout]
    cases k with
    | r0 => exact cp_11_root_0 a0 a1 a2 b0 b1 b2 heq
    | r1 => exact cp_11_root_1 a0 a1 a2 b0 b1 b2 heq
    | r2 => exact cp_11_root_2 a0 a1 a2 b0 b1 b2 heq
    | r3 => exact cp_11_root_3 a0 a1 a2 b0 b1 b2 heq
    | r4 => exact cp_11_root_4 a0 a1 a2 b0 b1 b2 heq
    | r5 => exact cp_11_root_5 a0 a1 a2 b0 b1 b2 heq
    | r6 => exact cp_11_root_6 a0 a1 a2 b0 b1 b2 heq
    | r7 => exact cp_11_root_7 a0 a1 a2 b0 b1 b2 heq
    | r8 => exact cp_11_root_8 a0 a1 a2 b0 b1 b2 heq
    | r9 => exact cp_11_root_9 a0 a1 a2 b0 b1 b2 heq
    | r10 => exact cp_11_root_10 a0 a1 a2 b0 b1 b2 heq
    | r11 => exact cp_11_root_11 a0 a1 a2 b0 b1 b2 heq
    | r12 => exact cp_11_root_12 a0 a1 a2 b0 b1 b2 heq
    | r13 => exact cp_11_root_13 a0 a1 a2 b0 b1 b2 heq
    | r14 => exact cp_11_root_14 a0 a1 a2 b0 b1 b2 heq
    | r15 => exact cp_11_root_15 a0 a1 a2 b0 b1 b2 heq
    | r16 => exact cp_11_root_16 a0 a1 a2 b0 b1 b2 heq
  ·
    rcases step_shared_cases h0 with hr
    · rcases hr with ⟨k, b0, b1, b2, heq, hout⟩
      rw [hout]
      cases k with
      | r0 => exact cp_11_1_0 a0 a1 a2 b0 b1 b2 heq
      | r1 => exact cp_11_1_1 a0 a1 a2 b0 b1 b2 heq
      | r2 => exact cp_11_1_2 a0 a1 a2 b0 b1 b2 heq
      | r3 => exact cp_11_1_3 a0 a1 a2 b0 b1 b2 heq
      | r4 => exact cp_11_1_4 a0 a1 a2 b0 b1 b2 heq
      | r5 => exact cp_11_1_5 a0 a1 a2 b0 b1 b2 heq
      | r6 => exact cp_11_1_6 a0 a1 a2 b0 b1 b2 heq
      | r7 => exact cp_11_1_7 a0 a1 a2 b0 b1 b2 heq
      | r8 => exact cp_11_1_8 a0 a1 a2 b0 b1 b2 heq
      | r9 => exact cp_11_1_9 a0 a1 a2 b0 b1 b2 heq
      | r10 => exact cp_11_1_10 a0 a1 a2 b0 b1 b2 heq
      | r11 => exact cp_11_1_11 a0 a1 a2 b0 b1 b2 heq
      | r12 => exact cp_11_1_12 a0 a1 a2 b0 b1 b2 heq
      | r13 => exact cp_11_1_13 a0 a1 a2 b0 b1 b2 heq
      | r14 => exact cp_11_1_14 a0 a1 a2 b0 b1 b2 heq
      | r15 => exact cp_11_1_15 a0 a1 a2 b0 b1 b2 heq
      | r16 => exact cp_11_1_16 a0 a1 a2 b0 b1 b2 heq
  ·
    rcases step_aux1_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
    · rcases hr with ⟨k, b0, b1, b2, heq, hout⟩
      rw [hout]
      cases k with
      | r0 => exact cp_11_2_0 a0 a1 a2 b0 b1 b2 heq
      | r1 => exact cp_11_2_1 a0 a1 a2 b0 b1 b2 heq
      | r2 => exact cp_11_2_2 a0 a1 a2 b0 b1 b2 heq
      | r3 => exact cp_11_2_3 a0 a1 a2 b0 b1 b2 heq
      | r4 => exact cp_11_2_4 a0 a1 a2 b0 b1 b2 heq
      | r5 => exact cp_11_2_5 a0 a1 a2 b0 b1 b2 heq
      | r6 => exact cp_11_2_6 a0 a1 a2 b0 b1 b2 heq
      | r7 => exact cp_11_2_7 a0 a1 a2 b0 b1 b2 heq
      | r8 => exact cp_11_2_8 a0 a1 a2 b0 b1 b2 heq
      | r9 => exact cp_11_2_9 a0 a1 a2 b0 b1 b2 heq
      | r10 => exact cp_11_2_10 a0 a1 a2 b0 b1 b2 heq
      | r11 => exact cp_11_2_11 a0 a1 a2 b0 b1 b2 heq
      | r12 => exact cp_11_2_12 a0 a1 a2 b0 b1 b2 heq
      | r13 => exact cp_11_2_13 a0 a1 a2 b0 b1 b2 heq
      | r14 => exact cp_11_2_14 a0 a1 a2 b0 b1 b2 heq
      | r15 => exact cp_11_2_15 a0 a1 a2 b0 b1 b2 heq
      | r16 => exact cp_11_2_16 a0 a1 a2 b0 b1 b2 heq
    ·
      rcases step_shared_cases h1 with hr
      · rcases hr with ⟨k, b0, b1, b2, heq, hout⟩
        rw [hout]
        cases k with
        | r0 => exact cp_11_2_1_0 a0 a1 a2 b0 b1 b2 heq
        | r1 => exact cp_11_2_1_1 a0 a1 a2 b0 b1 b2 heq
        | r2 => exact cp_11_2_1_2 a0 a1 a2 b0 b1 b2 heq
        | r3 => exact cp_11_2_1_3 a0 a1 a2 b0 b1 b2 heq
        | r4 => exact cp_11_2_1_4 a0 a1 a2 b0 b1 b2 heq
        | r5 => exact cp_11_2_1_5 a0 a1 a2 b0 b1 b2 heq
        | r6 => exact cp_11_2_1_6 a0 a1 a2 b0 b1 b2 heq
        | r7 => exact cp_11_2_1_7 a0 a1 a2 b0 b1 b2 heq
        | r8 => exact cp_11_2_1_8 a0 a1 a2 b0 b1 b2 heq
        | r9 => exact cp_11_2_1_9 a0 a1 a2 b0 b1 b2 heq
        | r10 => exact cp_11_2_1_10 a0 a1 a2 b0 b1 b2 heq
        | r11 => exact cp_11_2_1_11 a0 a1 a2 b0 b1 b2 heq
        | r12 => exact cp_11_2_1_12 a0 a1 a2 b0 b1 b2 heq
        | r13 => exact cp_11_2_1_13 a0 a1 a2 b0 b1 b2 heq
        | r14 => exact cp_11_2_1_14 a0 a1 a2 b0 b1 b2 heq
        | r15 => exact cp_11_2_1_15 a0 a1 a2 b0 b1 b2 heq
        | r16 => exact cp_11_2_1_16 a0 a1 a2 b0 b1 b2 heq
    ·
      exact var_11_2_2 a0 a1 a2 u1 h1
theorem peak_12 (a0 a1 a2 : T) {u : T} (h : Step (aux1 (shared ) (aux1 (shared ) a0)) u) :
    Join (shared ) u := by
  rcases step_aux1_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
  · rcases hr with ⟨k, b0, b1, b2, heq, hout⟩
    rw [hout]
    cases k with
    | r0 => exact cp_12_root_0 a0 a1 a2 b0 b1 b2 heq
    | r1 => exact cp_12_root_1 a0 a1 a2 b0 b1 b2 heq
    | r2 => exact cp_12_root_2 a0 a1 a2 b0 b1 b2 heq
    | r3 => exact cp_12_root_3 a0 a1 a2 b0 b1 b2 heq
    | r4 => exact cp_12_root_4 a0 a1 a2 b0 b1 b2 heq
    | r5 => exact cp_12_root_5 a0 a1 a2 b0 b1 b2 heq
    | r6 => exact cp_12_root_6 a0 a1 a2 b0 b1 b2 heq
    | r7 => exact cp_12_root_7 a0 a1 a2 b0 b1 b2 heq
    | r8 => exact cp_12_root_8 a0 a1 a2 b0 b1 b2 heq
    | r9 => exact cp_12_root_9 a0 a1 a2 b0 b1 b2 heq
    | r10 => exact cp_12_root_10 a0 a1 a2 b0 b1 b2 heq
    | r11 => exact cp_12_root_11 a0 a1 a2 b0 b1 b2 heq
    | r12 => exact cp_12_root_12 a0 a1 a2 b0 b1 b2 heq
    | r13 => exact cp_12_root_13 a0 a1 a2 b0 b1 b2 heq
    | r14 => exact cp_12_root_14 a0 a1 a2 b0 b1 b2 heq
    | r15 => exact cp_12_root_15 a0 a1 a2 b0 b1 b2 heq
    | r16 => exact cp_12_root_16 a0 a1 a2 b0 b1 b2 heq
  ·
    rcases step_shared_cases h0 with hr
    · rcases hr with ⟨k, b0, b1, b2, heq, hout⟩
      rw [hout]
      cases k with
      | r0 => exact cp_12_1_0 a0 a1 a2 b0 b1 b2 heq
      | r1 => exact cp_12_1_1 a0 a1 a2 b0 b1 b2 heq
      | r2 => exact cp_12_1_2 a0 a1 a2 b0 b1 b2 heq
      | r3 => exact cp_12_1_3 a0 a1 a2 b0 b1 b2 heq
      | r4 => exact cp_12_1_4 a0 a1 a2 b0 b1 b2 heq
      | r5 => exact cp_12_1_5 a0 a1 a2 b0 b1 b2 heq
      | r6 => exact cp_12_1_6 a0 a1 a2 b0 b1 b2 heq
      | r7 => exact cp_12_1_7 a0 a1 a2 b0 b1 b2 heq
      | r8 => exact cp_12_1_8 a0 a1 a2 b0 b1 b2 heq
      | r9 => exact cp_12_1_9 a0 a1 a2 b0 b1 b2 heq
      | r10 => exact cp_12_1_10 a0 a1 a2 b0 b1 b2 heq
      | r11 => exact cp_12_1_11 a0 a1 a2 b0 b1 b2 heq
      | r12 => exact cp_12_1_12 a0 a1 a2 b0 b1 b2 heq
      | r13 => exact cp_12_1_13 a0 a1 a2 b0 b1 b2 heq
      | r14 => exact cp_12_1_14 a0 a1 a2 b0 b1 b2 heq
      | r15 => exact cp_12_1_15 a0 a1 a2 b0 b1 b2 heq
      | r16 => exact cp_12_1_16 a0 a1 a2 b0 b1 b2 heq
  ·
    rcases step_aux1_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
    · rcases hr with ⟨k, b0, b1, b2, heq, hout⟩
      rw [hout]
      cases k with
      | r0 => exact cp_12_2_0 a0 a1 a2 b0 b1 b2 heq
      | r1 => exact cp_12_2_1 a0 a1 a2 b0 b1 b2 heq
      | r2 => exact cp_12_2_2 a0 a1 a2 b0 b1 b2 heq
      | r3 => exact cp_12_2_3 a0 a1 a2 b0 b1 b2 heq
      | r4 => exact cp_12_2_4 a0 a1 a2 b0 b1 b2 heq
      | r5 => exact cp_12_2_5 a0 a1 a2 b0 b1 b2 heq
      | r6 => exact cp_12_2_6 a0 a1 a2 b0 b1 b2 heq
      | r7 => exact cp_12_2_7 a0 a1 a2 b0 b1 b2 heq
      | r8 => exact cp_12_2_8 a0 a1 a2 b0 b1 b2 heq
      | r9 => exact cp_12_2_9 a0 a1 a2 b0 b1 b2 heq
      | r10 => exact cp_12_2_10 a0 a1 a2 b0 b1 b2 heq
      | r11 => exact cp_12_2_11 a0 a1 a2 b0 b1 b2 heq
      | r12 => exact cp_12_2_12 a0 a1 a2 b0 b1 b2 heq
      | r13 => exact cp_12_2_13 a0 a1 a2 b0 b1 b2 heq
      | r14 => exact cp_12_2_14 a0 a1 a2 b0 b1 b2 heq
      | r15 => exact cp_12_2_15 a0 a1 a2 b0 b1 b2 heq
      | r16 => exact cp_12_2_16 a0 a1 a2 b0 b1 b2 heq
    ·
      rcases step_shared_cases h1 with hr
      · rcases hr with ⟨k, b0, b1, b2, heq, hout⟩
        rw [hout]
        cases k with
        | r0 => exact cp_12_2_1_0 a0 a1 a2 b0 b1 b2 heq
        | r1 => exact cp_12_2_1_1 a0 a1 a2 b0 b1 b2 heq
        | r2 => exact cp_12_2_1_2 a0 a1 a2 b0 b1 b2 heq
        | r3 => exact cp_12_2_1_3 a0 a1 a2 b0 b1 b2 heq
        | r4 => exact cp_12_2_1_4 a0 a1 a2 b0 b1 b2 heq
        | r5 => exact cp_12_2_1_5 a0 a1 a2 b0 b1 b2 heq
        | r6 => exact cp_12_2_1_6 a0 a1 a2 b0 b1 b2 heq
        | r7 => exact cp_12_2_1_7 a0 a1 a2 b0 b1 b2 heq
        | r8 => exact cp_12_2_1_8 a0 a1 a2 b0 b1 b2 heq
        | r9 => exact cp_12_2_1_9 a0 a1 a2 b0 b1 b2 heq
        | r10 => exact cp_12_2_1_10 a0 a1 a2 b0 b1 b2 heq
        | r11 => exact cp_12_2_1_11 a0 a1 a2 b0 b1 b2 heq
        | r12 => exact cp_12_2_1_12 a0 a1 a2 b0 b1 b2 heq
        | r13 => exact cp_12_2_1_13 a0 a1 a2 b0 b1 b2 heq
        | r14 => exact cp_12_2_1_14 a0 a1 a2 b0 b1 b2 heq
        | r15 => exact cp_12_2_1_15 a0 a1 a2 b0 b1 b2 heq
        | r16 => exact cp_12_2_1_16 a0 a1 a2 b0 b1 b2 heq
    ·
      exact var_12_2_2 a0 a1 a2 u1 h1
theorem peak_13 (a0 a1 a2 : T) {u : T} (h : Step (op (aux1 (aux1 a0 a1) (aux1 a0 a1)) a0) u) :
    Join (aux0 (aux1 a0 a1) a0) u := by
  rcases step_op_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
  · rcases hr with ⟨k, b0, b1, b2, heq, hout⟩
    rw [hout]
    cases k with
    | r0 => exact cp_13_root_0 a0 a1 a2 b0 b1 b2 heq
    | r1 => exact cp_13_root_1 a0 a1 a2 b0 b1 b2 heq
    | r2 => exact cp_13_root_2 a0 a1 a2 b0 b1 b2 heq
    | r3 => exact cp_13_root_3 a0 a1 a2 b0 b1 b2 heq
    | r4 => exact cp_13_root_4 a0 a1 a2 b0 b1 b2 heq
    | r5 => exact cp_13_root_5 a0 a1 a2 b0 b1 b2 heq
    | r6 => exact cp_13_root_6 a0 a1 a2 b0 b1 b2 heq
    | r7 => exact cp_13_root_7 a0 a1 a2 b0 b1 b2 heq
    | r8 => exact cp_13_root_8 a0 a1 a2 b0 b1 b2 heq
    | r9 => exact cp_13_root_9 a0 a1 a2 b0 b1 b2 heq
    | r10 => exact cp_13_root_10 a0 a1 a2 b0 b1 b2 heq
    | r11 => exact cp_13_root_11 a0 a1 a2 b0 b1 b2 heq
    | r12 => exact cp_13_root_12 a0 a1 a2 b0 b1 b2 heq
    | r13 => exact cp_13_root_13 a0 a1 a2 b0 b1 b2 heq
    | r14 => exact cp_13_root_14 a0 a1 a2 b0 b1 b2 heq
    | r15 => exact cp_13_root_15 a0 a1 a2 b0 b1 b2 heq
    | r16 => exact cp_13_root_16 a0 a1 a2 b0 b1 b2 heq
  ·
    rcases step_aux1_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
    · rcases hr with ⟨k, b0, b1, b2, heq, hout⟩
      rw [hout]
      cases k with
      | r0 => exact cp_13_1_0 a0 a1 a2 b0 b1 b2 heq
      | r1 => exact cp_13_1_1 a0 a1 a2 b0 b1 b2 heq
      | r2 => exact cp_13_1_2 a0 a1 a2 b0 b1 b2 heq
      | r3 => exact cp_13_1_3 a0 a1 a2 b0 b1 b2 heq
      | r4 => exact cp_13_1_4 a0 a1 a2 b0 b1 b2 heq
      | r5 => exact cp_13_1_5 a0 a1 a2 b0 b1 b2 heq
      | r6 => exact cp_13_1_6 a0 a1 a2 b0 b1 b2 heq
      | r7 => exact cp_13_1_7 a0 a1 a2 b0 b1 b2 heq
      | r8 => exact cp_13_1_8 a0 a1 a2 b0 b1 b2 heq
      | r9 => exact cp_13_1_9 a0 a1 a2 b0 b1 b2 heq
      | r10 => exact cp_13_1_10 a0 a1 a2 b0 b1 b2 heq
      | r11 => exact cp_13_1_11 a0 a1 a2 b0 b1 b2 heq
      | r12 => exact cp_13_1_12 a0 a1 a2 b0 b1 b2 heq
      | r13 => exact cp_13_1_13 a0 a1 a2 b0 b1 b2 heq
      | r14 => exact cp_13_1_14 a0 a1 a2 b0 b1 b2 heq
      | r15 => exact cp_13_1_15 a0 a1 a2 b0 b1 b2 heq
      | r16 => exact cp_13_1_16 a0 a1 a2 b0 b1 b2 heq
    ·
      rcases step_aux1_cases h1 with hr | ⟨u2, rfl, h2⟩ | ⟨u2, rfl, h2⟩
      · rcases hr with ⟨k, b0, b1, b2, heq, hout⟩
        rw [hout]
        cases k with
        | r0 => exact cp_13_1_1_0 a0 a1 a2 b0 b1 b2 heq
        | r1 => exact cp_13_1_1_1 a0 a1 a2 b0 b1 b2 heq
        | r2 => exact cp_13_1_1_2 a0 a1 a2 b0 b1 b2 heq
        | r3 => exact cp_13_1_1_3 a0 a1 a2 b0 b1 b2 heq
        | r4 => exact cp_13_1_1_4 a0 a1 a2 b0 b1 b2 heq
        | r5 => exact cp_13_1_1_5 a0 a1 a2 b0 b1 b2 heq
        | r6 => exact cp_13_1_1_6 a0 a1 a2 b0 b1 b2 heq
        | r7 => exact cp_13_1_1_7 a0 a1 a2 b0 b1 b2 heq
        | r8 => exact cp_13_1_1_8 a0 a1 a2 b0 b1 b2 heq
        | r9 => exact cp_13_1_1_9 a0 a1 a2 b0 b1 b2 heq
        | r10 => exact cp_13_1_1_10 a0 a1 a2 b0 b1 b2 heq
        | r11 => exact cp_13_1_1_11 a0 a1 a2 b0 b1 b2 heq
        | r12 => exact cp_13_1_1_12 a0 a1 a2 b0 b1 b2 heq
        | r13 => exact cp_13_1_1_13 a0 a1 a2 b0 b1 b2 heq
        | r14 => exact cp_13_1_1_14 a0 a1 a2 b0 b1 b2 heq
        | r15 => exact cp_13_1_1_15 a0 a1 a2 b0 b1 b2 heq
        | r16 => exact cp_13_1_1_16 a0 a1 a2 b0 b1 b2 heq
      ·
        exact var_13_1_1_1 a0 a1 a2 u2 h2
      ·
        exact var_13_1_1_2 a0 a1 a2 u2 h2
    ·
      rcases step_aux1_cases h1 with hr | ⟨u2, rfl, h2⟩ | ⟨u2, rfl, h2⟩
      · rcases hr with ⟨k, b0, b1, b2, heq, hout⟩
        rw [hout]
        cases k with
        | r0 => exact cp_13_1_2_0 a0 a1 a2 b0 b1 b2 heq
        | r1 => exact cp_13_1_2_1 a0 a1 a2 b0 b1 b2 heq
        | r2 => exact cp_13_1_2_2 a0 a1 a2 b0 b1 b2 heq
        | r3 => exact cp_13_1_2_3 a0 a1 a2 b0 b1 b2 heq
        | r4 => exact cp_13_1_2_4 a0 a1 a2 b0 b1 b2 heq
        | r5 => exact cp_13_1_2_5 a0 a1 a2 b0 b1 b2 heq
        | r6 => exact cp_13_1_2_6 a0 a1 a2 b0 b1 b2 heq
        | r7 => exact cp_13_1_2_7 a0 a1 a2 b0 b1 b2 heq
        | r8 => exact cp_13_1_2_8 a0 a1 a2 b0 b1 b2 heq
        | r9 => exact cp_13_1_2_9 a0 a1 a2 b0 b1 b2 heq
        | r10 => exact cp_13_1_2_10 a0 a1 a2 b0 b1 b2 heq
        | r11 => exact cp_13_1_2_11 a0 a1 a2 b0 b1 b2 heq
        | r12 => exact cp_13_1_2_12 a0 a1 a2 b0 b1 b2 heq
        | r13 => exact cp_13_1_2_13 a0 a1 a2 b0 b1 b2 heq
        | r14 => exact cp_13_1_2_14 a0 a1 a2 b0 b1 b2 heq
        | r15 => exact cp_13_1_2_15 a0 a1 a2 b0 b1 b2 heq
        | r16 => exact cp_13_1_2_16 a0 a1 a2 b0 b1 b2 heq
      ·
        exact var_13_1_2_1 a0 a1 a2 u2 h2
      ·
        exact var_13_1_2_2 a0 a1 a2 u2 h2
  ·
    exact var_13_2 a0 a1 a2 u0 h0
theorem peak_14 (a0 a1 a2 : T) {u : T} (h : Step (aux0 (aux0 (shared ) a0) (aux0 (shared ) a0)) u) :
    Join (aux1 (shared ) a0) u := by
  rcases step_aux0_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
  · rcases hr with ⟨k, b0, b1, b2, heq, hout⟩
    rw [hout]
    cases k with
    | r0 => exact cp_14_root_0 a0 a1 a2 b0 b1 b2 heq
    | r1 => exact cp_14_root_1 a0 a1 a2 b0 b1 b2 heq
    | r2 => exact cp_14_root_2 a0 a1 a2 b0 b1 b2 heq
    | r3 => exact cp_14_root_3 a0 a1 a2 b0 b1 b2 heq
    | r4 => exact cp_14_root_4 a0 a1 a2 b0 b1 b2 heq
    | r5 => exact cp_14_root_5 a0 a1 a2 b0 b1 b2 heq
    | r6 => exact cp_14_root_6 a0 a1 a2 b0 b1 b2 heq
    | r7 => exact cp_14_root_7 a0 a1 a2 b0 b1 b2 heq
    | r8 => exact cp_14_root_8 a0 a1 a2 b0 b1 b2 heq
    | r9 => exact cp_14_root_9 a0 a1 a2 b0 b1 b2 heq
    | r10 => exact cp_14_root_10 a0 a1 a2 b0 b1 b2 heq
    | r11 => exact cp_14_root_11 a0 a1 a2 b0 b1 b2 heq
    | r12 => exact cp_14_root_12 a0 a1 a2 b0 b1 b2 heq
    | r13 => exact cp_14_root_13 a0 a1 a2 b0 b1 b2 heq
    | r14 => exact cp_14_root_14 a0 a1 a2 b0 b1 b2 heq
    | r15 => exact cp_14_root_15 a0 a1 a2 b0 b1 b2 heq
    | r16 => exact cp_14_root_16 a0 a1 a2 b0 b1 b2 heq
  ·
    rcases step_aux0_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
    · rcases hr with ⟨k, b0, b1, b2, heq, hout⟩
      rw [hout]
      cases k with
      | r0 => exact cp_14_1_0 a0 a1 a2 b0 b1 b2 heq
      | r1 => exact cp_14_1_1 a0 a1 a2 b0 b1 b2 heq
      | r2 => exact cp_14_1_2 a0 a1 a2 b0 b1 b2 heq
      | r3 => exact cp_14_1_3 a0 a1 a2 b0 b1 b2 heq
      | r4 => exact cp_14_1_4 a0 a1 a2 b0 b1 b2 heq
      | r5 => exact cp_14_1_5 a0 a1 a2 b0 b1 b2 heq
      | r6 => exact cp_14_1_6 a0 a1 a2 b0 b1 b2 heq
      | r7 => exact cp_14_1_7 a0 a1 a2 b0 b1 b2 heq
      | r8 => exact cp_14_1_8 a0 a1 a2 b0 b1 b2 heq
      | r9 => exact cp_14_1_9 a0 a1 a2 b0 b1 b2 heq
      | r10 => exact cp_14_1_10 a0 a1 a2 b0 b1 b2 heq
      | r11 => exact cp_14_1_11 a0 a1 a2 b0 b1 b2 heq
      | r12 => exact cp_14_1_12 a0 a1 a2 b0 b1 b2 heq
      | r13 => exact cp_14_1_13 a0 a1 a2 b0 b1 b2 heq
      | r14 => exact cp_14_1_14 a0 a1 a2 b0 b1 b2 heq
      | r15 => exact cp_14_1_15 a0 a1 a2 b0 b1 b2 heq
      | r16 => exact cp_14_1_16 a0 a1 a2 b0 b1 b2 heq
    ·
      rcases step_shared_cases h1 with hr
      · rcases hr with ⟨k, b0, b1, b2, heq, hout⟩
        rw [hout]
        cases k with
        | r0 => exact cp_14_1_1_0 a0 a1 a2 b0 b1 b2 heq
        | r1 => exact cp_14_1_1_1 a0 a1 a2 b0 b1 b2 heq
        | r2 => exact cp_14_1_1_2 a0 a1 a2 b0 b1 b2 heq
        | r3 => exact cp_14_1_1_3 a0 a1 a2 b0 b1 b2 heq
        | r4 => exact cp_14_1_1_4 a0 a1 a2 b0 b1 b2 heq
        | r5 => exact cp_14_1_1_5 a0 a1 a2 b0 b1 b2 heq
        | r6 => exact cp_14_1_1_6 a0 a1 a2 b0 b1 b2 heq
        | r7 => exact cp_14_1_1_7 a0 a1 a2 b0 b1 b2 heq
        | r8 => exact cp_14_1_1_8 a0 a1 a2 b0 b1 b2 heq
        | r9 => exact cp_14_1_1_9 a0 a1 a2 b0 b1 b2 heq
        | r10 => exact cp_14_1_1_10 a0 a1 a2 b0 b1 b2 heq
        | r11 => exact cp_14_1_1_11 a0 a1 a2 b0 b1 b2 heq
        | r12 => exact cp_14_1_1_12 a0 a1 a2 b0 b1 b2 heq
        | r13 => exact cp_14_1_1_13 a0 a1 a2 b0 b1 b2 heq
        | r14 => exact cp_14_1_1_14 a0 a1 a2 b0 b1 b2 heq
        | r15 => exact cp_14_1_1_15 a0 a1 a2 b0 b1 b2 heq
        | r16 => exact cp_14_1_1_16 a0 a1 a2 b0 b1 b2 heq
    ·
      exact var_14_1_2 a0 a1 a2 u1 h1
  ·
    rcases step_aux0_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
    · rcases hr with ⟨k, b0, b1, b2, heq, hout⟩
      rw [hout]
      cases k with
      | r0 => exact cp_14_2_0 a0 a1 a2 b0 b1 b2 heq
      | r1 => exact cp_14_2_1 a0 a1 a2 b0 b1 b2 heq
      | r2 => exact cp_14_2_2 a0 a1 a2 b0 b1 b2 heq
      | r3 => exact cp_14_2_3 a0 a1 a2 b0 b1 b2 heq
      | r4 => exact cp_14_2_4 a0 a1 a2 b0 b1 b2 heq
      | r5 => exact cp_14_2_5 a0 a1 a2 b0 b1 b2 heq
      | r6 => exact cp_14_2_6 a0 a1 a2 b0 b1 b2 heq
      | r7 => exact cp_14_2_7 a0 a1 a2 b0 b1 b2 heq
      | r8 => exact cp_14_2_8 a0 a1 a2 b0 b1 b2 heq
      | r9 => exact cp_14_2_9 a0 a1 a2 b0 b1 b2 heq
      | r10 => exact cp_14_2_10 a0 a1 a2 b0 b1 b2 heq
      | r11 => exact cp_14_2_11 a0 a1 a2 b0 b1 b2 heq
      | r12 => exact cp_14_2_12 a0 a1 a2 b0 b1 b2 heq
      | r13 => exact cp_14_2_13 a0 a1 a2 b0 b1 b2 heq
      | r14 => exact cp_14_2_14 a0 a1 a2 b0 b1 b2 heq
      | r15 => exact cp_14_2_15 a0 a1 a2 b0 b1 b2 heq
      | r16 => exact cp_14_2_16 a0 a1 a2 b0 b1 b2 heq
    ·
      rcases step_shared_cases h1 with hr
      · rcases hr with ⟨k, b0, b1, b2, heq, hout⟩
        rw [hout]
        cases k with
        | r0 => exact cp_14_2_1_0 a0 a1 a2 b0 b1 b2 heq
        | r1 => exact cp_14_2_1_1 a0 a1 a2 b0 b1 b2 heq
        | r2 => exact cp_14_2_1_2 a0 a1 a2 b0 b1 b2 heq
        | r3 => exact cp_14_2_1_3 a0 a1 a2 b0 b1 b2 heq
        | r4 => exact cp_14_2_1_4 a0 a1 a2 b0 b1 b2 heq
        | r5 => exact cp_14_2_1_5 a0 a1 a2 b0 b1 b2 heq
        | r6 => exact cp_14_2_1_6 a0 a1 a2 b0 b1 b2 heq
        | r7 => exact cp_14_2_1_7 a0 a1 a2 b0 b1 b2 heq
        | r8 => exact cp_14_2_1_8 a0 a1 a2 b0 b1 b2 heq
        | r9 => exact cp_14_2_1_9 a0 a1 a2 b0 b1 b2 heq
        | r10 => exact cp_14_2_1_10 a0 a1 a2 b0 b1 b2 heq
        | r11 => exact cp_14_2_1_11 a0 a1 a2 b0 b1 b2 heq
        | r12 => exact cp_14_2_1_12 a0 a1 a2 b0 b1 b2 heq
        | r13 => exact cp_14_2_1_13 a0 a1 a2 b0 b1 b2 heq
        | r14 => exact cp_14_2_1_14 a0 a1 a2 b0 b1 b2 heq
        | r15 => exact cp_14_2_1_15 a0 a1 a2 b0 b1 b2 heq
        | r16 => exact cp_14_2_1_16 a0 a1 a2 b0 b1 b2 heq
    ·
      exact var_14_2_2 a0 a1 a2 u1 h1
theorem peak_15 (a0 a1 a2 : T) {u : T} (h : Step (op (aux0 (shared ) a0) (aux1 (shared ) a0)) u) :
    Join (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) u := by
  rcases step_op_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
  · rcases hr with ⟨k, b0, b1, b2, heq, hout⟩
    rw [hout]
    cases k with
    | r0 => exact cp_15_root_0 a0 a1 a2 b0 b1 b2 heq
    | r1 => exact cp_15_root_1 a0 a1 a2 b0 b1 b2 heq
    | r2 => exact cp_15_root_2 a0 a1 a2 b0 b1 b2 heq
    | r3 => exact cp_15_root_3 a0 a1 a2 b0 b1 b2 heq
    | r4 => exact cp_15_root_4 a0 a1 a2 b0 b1 b2 heq
    | r5 => exact cp_15_root_5 a0 a1 a2 b0 b1 b2 heq
    | r6 => exact cp_15_root_6 a0 a1 a2 b0 b1 b2 heq
    | r7 => exact cp_15_root_7 a0 a1 a2 b0 b1 b2 heq
    | r8 => exact cp_15_root_8 a0 a1 a2 b0 b1 b2 heq
    | r9 => exact cp_15_root_9 a0 a1 a2 b0 b1 b2 heq
    | r10 => exact cp_15_root_10 a0 a1 a2 b0 b1 b2 heq
    | r11 => exact cp_15_root_11 a0 a1 a2 b0 b1 b2 heq
    | r12 => exact cp_15_root_12 a0 a1 a2 b0 b1 b2 heq
    | r13 => exact cp_15_root_13 a0 a1 a2 b0 b1 b2 heq
    | r14 => exact cp_15_root_14 a0 a1 a2 b0 b1 b2 heq
    | r15 => exact cp_15_root_15 a0 a1 a2 b0 b1 b2 heq
    | r16 => exact cp_15_root_16 a0 a1 a2 b0 b1 b2 heq
  ·
    rcases step_aux0_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
    · rcases hr with ⟨k, b0, b1, b2, heq, hout⟩
      rw [hout]
      cases k with
      | r0 => exact cp_15_1_0 a0 a1 a2 b0 b1 b2 heq
      | r1 => exact cp_15_1_1 a0 a1 a2 b0 b1 b2 heq
      | r2 => exact cp_15_1_2 a0 a1 a2 b0 b1 b2 heq
      | r3 => exact cp_15_1_3 a0 a1 a2 b0 b1 b2 heq
      | r4 => exact cp_15_1_4 a0 a1 a2 b0 b1 b2 heq
      | r5 => exact cp_15_1_5 a0 a1 a2 b0 b1 b2 heq
      | r6 => exact cp_15_1_6 a0 a1 a2 b0 b1 b2 heq
      | r7 => exact cp_15_1_7 a0 a1 a2 b0 b1 b2 heq
      | r8 => exact cp_15_1_8 a0 a1 a2 b0 b1 b2 heq
      | r9 => exact cp_15_1_9 a0 a1 a2 b0 b1 b2 heq
      | r10 => exact cp_15_1_10 a0 a1 a2 b0 b1 b2 heq
      | r11 => exact cp_15_1_11 a0 a1 a2 b0 b1 b2 heq
      | r12 => exact cp_15_1_12 a0 a1 a2 b0 b1 b2 heq
      | r13 => exact cp_15_1_13 a0 a1 a2 b0 b1 b2 heq
      | r14 => exact cp_15_1_14 a0 a1 a2 b0 b1 b2 heq
      | r15 => exact cp_15_1_15 a0 a1 a2 b0 b1 b2 heq
      | r16 => exact cp_15_1_16 a0 a1 a2 b0 b1 b2 heq
    ·
      rcases step_shared_cases h1 with hr
      · rcases hr with ⟨k, b0, b1, b2, heq, hout⟩
        rw [hout]
        cases k with
        | r0 => exact cp_15_1_1_0 a0 a1 a2 b0 b1 b2 heq
        | r1 => exact cp_15_1_1_1 a0 a1 a2 b0 b1 b2 heq
        | r2 => exact cp_15_1_1_2 a0 a1 a2 b0 b1 b2 heq
        | r3 => exact cp_15_1_1_3 a0 a1 a2 b0 b1 b2 heq
        | r4 => exact cp_15_1_1_4 a0 a1 a2 b0 b1 b2 heq
        | r5 => exact cp_15_1_1_5 a0 a1 a2 b0 b1 b2 heq
        | r6 => exact cp_15_1_1_6 a0 a1 a2 b0 b1 b2 heq
        | r7 => exact cp_15_1_1_7 a0 a1 a2 b0 b1 b2 heq
        | r8 => exact cp_15_1_1_8 a0 a1 a2 b0 b1 b2 heq
        | r9 => exact cp_15_1_1_9 a0 a1 a2 b0 b1 b2 heq
        | r10 => exact cp_15_1_1_10 a0 a1 a2 b0 b1 b2 heq
        | r11 => exact cp_15_1_1_11 a0 a1 a2 b0 b1 b2 heq
        | r12 => exact cp_15_1_1_12 a0 a1 a2 b0 b1 b2 heq
        | r13 => exact cp_15_1_1_13 a0 a1 a2 b0 b1 b2 heq
        | r14 => exact cp_15_1_1_14 a0 a1 a2 b0 b1 b2 heq
        | r15 => exact cp_15_1_1_15 a0 a1 a2 b0 b1 b2 heq
        | r16 => exact cp_15_1_1_16 a0 a1 a2 b0 b1 b2 heq
    ·
      exact var_15_1_2 a0 a1 a2 u1 h1
  ·
    rcases step_aux1_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
    · rcases hr with ⟨k, b0, b1, b2, heq, hout⟩
      rw [hout]
      cases k with
      | r0 => exact cp_15_2_0 a0 a1 a2 b0 b1 b2 heq
      | r1 => exact cp_15_2_1 a0 a1 a2 b0 b1 b2 heq
      | r2 => exact cp_15_2_2 a0 a1 a2 b0 b1 b2 heq
      | r3 => exact cp_15_2_3 a0 a1 a2 b0 b1 b2 heq
      | r4 => exact cp_15_2_4 a0 a1 a2 b0 b1 b2 heq
      | r5 => exact cp_15_2_5 a0 a1 a2 b0 b1 b2 heq
      | r6 => exact cp_15_2_6 a0 a1 a2 b0 b1 b2 heq
      | r7 => exact cp_15_2_7 a0 a1 a2 b0 b1 b2 heq
      | r8 => exact cp_15_2_8 a0 a1 a2 b0 b1 b2 heq
      | r9 => exact cp_15_2_9 a0 a1 a2 b0 b1 b2 heq
      | r10 => exact cp_15_2_10 a0 a1 a2 b0 b1 b2 heq
      | r11 => exact cp_15_2_11 a0 a1 a2 b0 b1 b2 heq
      | r12 => exact cp_15_2_12 a0 a1 a2 b0 b1 b2 heq
      | r13 => exact cp_15_2_13 a0 a1 a2 b0 b1 b2 heq
      | r14 => exact cp_15_2_14 a0 a1 a2 b0 b1 b2 heq
      | r15 => exact cp_15_2_15 a0 a1 a2 b0 b1 b2 heq
      | r16 => exact cp_15_2_16 a0 a1 a2 b0 b1 b2 heq
    ·
      rcases step_shared_cases h1 with hr
      · rcases hr with ⟨k, b0, b1, b2, heq, hout⟩
        rw [hout]
        cases k with
        | r0 => exact cp_15_2_1_0 a0 a1 a2 b0 b1 b2 heq
        | r1 => exact cp_15_2_1_1 a0 a1 a2 b0 b1 b2 heq
        | r2 => exact cp_15_2_1_2 a0 a1 a2 b0 b1 b2 heq
        | r3 => exact cp_15_2_1_3 a0 a1 a2 b0 b1 b2 heq
        | r4 => exact cp_15_2_1_4 a0 a1 a2 b0 b1 b2 heq
        | r5 => exact cp_15_2_1_5 a0 a1 a2 b0 b1 b2 heq
        | r6 => exact cp_15_2_1_6 a0 a1 a2 b0 b1 b2 heq
        | r7 => exact cp_15_2_1_7 a0 a1 a2 b0 b1 b2 heq
        | r8 => exact cp_15_2_1_8 a0 a1 a2 b0 b1 b2 heq
        | r9 => exact cp_15_2_1_9 a0 a1 a2 b0 b1 b2 heq
        | r10 => exact cp_15_2_1_10 a0 a1 a2 b0 b1 b2 heq
        | r11 => exact cp_15_2_1_11 a0 a1 a2 b0 b1 b2 heq
        | r12 => exact cp_15_2_1_12 a0 a1 a2 b0 b1 b2 heq
        | r13 => exact cp_15_2_1_13 a0 a1 a2 b0 b1 b2 heq
        | r14 => exact cp_15_2_1_14 a0 a1 a2 b0 b1 b2 heq
        | r15 => exact cp_15_2_1_15 a0 a1 a2 b0 b1 b2 heq
        | r16 => exact cp_15_2_1_16 a0 a1 a2 b0 b1 b2 heq
    ·
      exact var_15_2_2 a0 a1 a2 u1 h1
theorem peak_16 (a0 a1 a2 : T) {u : T} (h : Step (op (aux1 (aux0 (shared ) a0) (aux0 (shared ) a0)) (aux1 (shared ) a0)) u) :
    Join (aux0 (aux0 (shared ) a0) (aux1 (shared ) a0)) u := by
  rcases step_op_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
  · rcases hr with ⟨k, b0, b1, b2, heq, hout⟩
    rw [hout]
    cases k with
    | r0 => exact cp_16_root_0 a0 a1 a2 b0 b1 b2 heq
    | r1 => exact cp_16_root_1 a0 a1 a2 b0 b1 b2 heq
    | r2 => exact cp_16_root_2 a0 a1 a2 b0 b1 b2 heq
    | r3 => exact cp_16_root_3 a0 a1 a2 b0 b1 b2 heq
    | r4 => exact cp_16_root_4 a0 a1 a2 b0 b1 b2 heq
    | r5 => exact cp_16_root_5 a0 a1 a2 b0 b1 b2 heq
    | r6 => exact cp_16_root_6 a0 a1 a2 b0 b1 b2 heq
    | r7 => exact cp_16_root_7 a0 a1 a2 b0 b1 b2 heq
    | r8 => exact cp_16_root_8 a0 a1 a2 b0 b1 b2 heq
    | r9 => exact cp_16_root_9 a0 a1 a2 b0 b1 b2 heq
    | r10 => exact cp_16_root_10 a0 a1 a2 b0 b1 b2 heq
    | r11 => exact cp_16_root_11 a0 a1 a2 b0 b1 b2 heq
    | r12 => exact cp_16_root_12 a0 a1 a2 b0 b1 b2 heq
    | r13 => exact cp_16_root_13 a0 a1 a2 b0 b1 b2 heq
    | r14 => exact cp_16_root_14 a0 a1 a2 b0 b1 b2 heq
    | r15 => exact cp_16_root_15 a0 a1 a2 b0 b1 b2 heq
    | r16 => exact cp_16_root_16 a0 a1 a2 b0 b1 b2 heq
  ·
    rcases step_aux1_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
    · rcases hr with ⟨k, b0, b1, b2, heq, hout⟩
      rw [hout]
      cases k with
      | r0 => exact cp_16_1_0 a0 a1 a2 b0 b1 b2 heq
      | r1 => exact cp_16_1_1 a0 a1 a2 b0 b1 b2 heq
      | r2 => exact cp_16_1_2 a0 a1 a2 b0 b1 b2 heq
      | r3 => exact cp_16_1_3 a0 a1 a2 b0 b1 b2 heq
      | r4 => exact cp_16_1_4 a0 a1 a2 b0 b1 b2 heq
      | r5 => exact cp_16_1_5 a0 a1 a2 b0 b1 b2 heq
      | r6 => exact cp_16_1_6 a0 a1 a2 b0 b1 b2 heq
      | r7 => exact cp_16_1_7 a0 a1 a2 b0 b1 b2 heq
      | r8 => exact cp_16_1_8 a0 a1 a2 b0 b1 b2 heq
      | r9 => exact cp_16_1_9 a0 a1 a2 b0 b1 b2 heq
      | r10 => exact cp_16_1_10 a0 a1 a2 b0 b1 b2 heq
      | r11 => exact cp_16_1_11 a0 a1 a2 b0 b1 b2 heq
      | r12 => exact cp_16_1_12 a0 a1 a2 b0 b1 b2 heq
      | r13 => exact cp_16_1_13 a0 a1 a2 b0 b1 b2 heq
      | r14 => exact cp_16_1_14 a0 a1 a2 b0 b1 b2 heq
      | r15 => exact cp_16_1_15 a0 a1 a2 b0 b1 b2 heq
      | r16 => exact cp_16_1_16 a0 a1 a2 b0 b1 b2 heq
    ·
      rcases step_aux0_cases h1 with hr | ⟨u2, rfl, h2⟩ | ⟨u2, rfl, h2⟩
      · rcases hr with ⟨k, b0, b1, b2, heq, hout⟩
        rw [hout]
        cases k with
        | r0 => exact cp_16_1_1_0 a0 a1 a2 b0 b1 b2 heq
        | r1 => exact cp_16_1_1_1 a0 a1 a2 b0 b1 b2 heq
        | r2 => exact cp_16_1_1_2 a0 a1 a2 b0 b1 b2 heq
        | r3 => exact cp_16_1_1_3 a0 a1 a2 b0 b1 b2 heq
        | r4 => exact cp_16_1_1_4 a0 a1 a2 b0 b1 b2 heq
        | r5 => exact cp_16_1_1_5 a0 a1 a2 b0 b1 b2 heq
        | r6 => exact cp_16_1_1_6 a0 a1 a2 b0 b1 b2 heq
        | r7 => exact cp_16_1_1_7 a0 a1 a2 b0 b1 b2 heq
        | r8 => exact cp_16_1_1_8 a0 a1 a2 b0 b1 b2 heq
        | r9 => exact cp_16_1_1_9 a0 a1 a2 b0 b1 b2 heq
        | r10 => exact cp_16_1_1_10 a0 a1 a2 b0 b1 b2 heq
        | r11 => exact cp_16_1_1_11 a0 a1 a2 b0 b1 b2 heq
        | r12 => exact cp_16_1_1_12 a0 a1 a2 b0 b1 b2 heq
        | r13 => exact cp_16_1_1_13 a0 a1 a2 b0 b1 b2 heq
        | r14 => exact cp_16_1_1_14 a0 a1 a2 b0 b1 b2 heq
        | r15 => exact cp_16_1_1_15 a0 a1 a2 b0 b1 b2 heq
        | r16 => exact cp_16_1_1_16 a0 a1 a2 b0 b1 b2 heq
      ·
        rcases step_shared_cases h2 with hr
        · rcases hr with ⟨k, b0, b1, b2, heq, hout⟩
          rw [hout]
          cases k with
          | r0 => exact cp_16_1_1_1_0 a0 a1 a2 b0 b1 b2 heq
          | r1 => exact cp_16_1_1_1_1 a0 a1 a2 b0 b1 b2 heq
          | r2 => exact cp_16_1_1_1_2 a0 a1 a2 b0 b1 b2 heq
          | r3 => exact cp_16_1_1_1_3 a0 a1 a2 b0 b1 b2 heq
          | r4 => exact cp_16_1_1_1_4 a0 a1 a2 b0 b1 b2 heq
          | r5 => exact cp_16_1_1_1_5 a0 a1 a2 b0 b1 b2 heq
          | r6 => exact cp_16_1_1_1_6 a0 a1 a2 b0 b1 b2 heq
          | r7 => exact cp_16_1_1_1_7 a0 a1 a2 b0 b1 b2 heq
          | r8 => exact cp_16_1_1_1_8 a0 a1 a2 b0 b1 b2 heq
          | r9 => exact cp_16_1_1_1_9 a0 a1 a2 b0 b1 b2 heq
          | r10 => exact cp_16_1_1_1_10 a0 a1 a2 b0 b1 b2 heq
          | r11 => exact cp_16_1_1_1_11 a0 a1 a2 b0 b1 b2 heq
          | r12 => exact cp_16_1_1_1_12 a0 a1 a2 b0 b1 b2 heq
          | r13 => exact cp_16_1_1_1_13 a0 a1 a2 b0 b1 b2 heq
          | r14 => exact cp_16_1_1_1_14 a0 a1 a2 b0 b1 b2 heq
          | r15 => exact cp_16_1_1_1_15 a0 a1 a2 b0 b1 b2 heq
          | r16 => exact cp_16_1_1_1_16 a0 a1 a2 b0 b1 b2 heq
      ·
        exact var_16_1_1_2 a0 a1 a2 u2 h2
    ·
      rcases step_aux0_cases h1 with hr | ⟨u2, rfl, h2⟩ | ⟨u2, rfl, h2⟩
      · rcases hr with ⟨k, b0, b1, b2, heq, hout⟩
        rw [hout]
        cases k with
        | r0 => exact cp_16_1_2_0 a0 a1 a2 b0 b1 b2 heq
        | r1 => exact cp_16_1_2_1 a0 a1 a2 b0 b1 b2 heq
        | r2 => exact cp_16_1_2_2 a0 a1 a2 b0 b1 b2 heq
        | r3 => exact cp_16_1_2_3 a0 a1 a2 b0 b1 b2 heq
        | r4 => exact cp_16_1_2_4 a0 a1 a2 b0 b1 b2 heq
        | r5 => exact cp_16_1_2_5 a0 a1 a2 b0 b1 b2 heq
        | r6 => exact cp_16_1_2_6 a0 a1 a2 b0 b1 b2 heq
        | r7 => exact cp_16_1_2_7 a0 a1 a2 b0 b1 b2 heq
        | r8 => exact cp_16_1_2_8 a0 a1 a2 b0 b1 b2 heq
        | r9 => exact cp_16_1_2_9 a0 a1 a2 b0 b1 b2 heq
        | r10 => exact cp_16_1_2_10 a0 a1 a2 b0 b1 b2 heq
        | r11 => exact cp_16_1_2_11 a0 a1 a2 b0 b1 b2 heq
        | r12 => exact cp_16_1_2_12 a0 a1 a2 b0 b1 b2 heq
        | r13 => exact cp_16_1_2_13 a0 a1 a2 b0 b1 b2 heq
        | r14 => exact cp_16_1_2_14 a0 a1 a2 b0 b1 b2 heq
        | r15 => exact cp_16_1_2_15 a0 a1 a2 b0 b1 b2 heq
        | r16 => exact cp_16_1_2_16 a0 a1 a2 b0 b1 b2 heq
      ·
        rcases step_shared_cases h2 with hr
        · rcases hr with ⟨k, b0, b1, b2, heq, hout⟩
          rw [hout]
          cases k with
          | r0 => exact cp_16_1_2_1_0 a0 a1 a2 b0 b1 b2 heq
          | r1 => exact cp_16_1_2_1_1 a0 a1 a2 b0 b1 b2 heq
          | r2 => exact cp_16_1_2_1_2 a0 a1 a2 b0 b1 b2 heq
          | r3 => exact cp_16_1_2_1_3 a0 a1 a2 b0 b1 b2 heq
          | r4 => exact cp_16_1_2_1_4 a0 a1 a2 b0 b1 b2 heq
          | r5 => exact cp_16_1_2_1_5 a0 a1 a2 b0 b1 b2 heq
          | r6 => exact cp_16_1_2_1_6 a0 a1 a2 b0 b1 b2 heq
          | r7 => exact cp_16_1_2_1_7 a0 a1 a2 b0 b1 b2 heq
          | r8 => exact cp_16_1_2_1_8 a0 a1 a2 b0 b1 b2 heq
          | r9 => exact cp_16_1_2_1_9 a0 a1 a2 b0 b1 b2 heq
          | r10 => exact cp_16_1_2_1_10 a0 a1 a2 b0 b1 b2 heq
          | r11 => exact cp_16_1_2_1_11 a0 a1 a2 b0 b1 b2 heq
          | r12 => exact cp_16_1_2_1_12 a0 a1 a2 b0 b1 b2 heq
          | r13 => exact cp_16_1_2_1_13 a0 a1 a2 b0 b1 b2 heq
          | r14 => exact cp_16_1_2_1_14 a0 a1 a2 b0 b1 b2 heq
          | r15 => exact cp_16_1_2_1_15 a0 a1 a2 b0 b1 b2 heq
          | r16 => exact cp_16_1_2_1_16 a0 a1 a2 b0 b1 b2 heq
      ·
        exact var_16_1_2_2 a0 a1 a2 u2 h2
  ·
    rcases step_aux1_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
    · rcases hr with ⟨k, b0, b1, b2, heq, hout⟩
      rw [hout]
      cases k with
      | r0 => exact cp_16_2_0 a0 a1 a2 b0 b1 b2 heq
      | r1 => exact cp_16_2_1 a0 a1 a2 b0 b1 b2 heq
      | r2 => exact cp_16_2_2 a0 a1 a2 b0 b1 b2 heq
      | r3 => exact cp_16_2_3 a0 a1 a2 b0 b1 b2 heq
      | r4 => exact cp_16_2_4 a0 a1 a2 b0 b1 b2 heq
      | r5 => exact cp_16_2_5 a0 a1 a2 b0 b1 b2 heq
      | r6 => exact cp_16_2_6 a0 a1 a2 b0 b1 b2 heq
      | r7 => exact cp_16_2_7 a0 a1 a2 b0 b1 b2 heq
      | r8 => exact cp_16_2_8 a0 a1 a2 b0 b1 b2 heq
      | r9 => exact cp_16_2_9 a0 a1 a2 b0 b1 b2 heq
      | r10 => exact cp_16_2_10 a0 a1 a2 b0 b1 b2 heq
      | r11 => exact cp_16_2_11 a0 a1 a2 b0 b1 b2 heq
      | r12 => exact cp_16_2_12 a0 a1 a2 b0 b1 b2 heq
      | r13 => exact cp_16_2_13 a0 a1 a2 b0 b1 b2 heq
      | r14 => exact cp_16_2_14 a0 a1 a2 b0 b1 b2 heq
      | r15 => exact cp_16_2_15 a0 a1 a2 b0 b1 b2 heq
      | r16 => exact cp_16_2_16 a0 a1 a2 b0 b1 b2 heq
    ·
      rcases step_shared_cases h1 with hr
      · rcases hr with ⟨k, b0, b1, b2, heq, hout⟩
        rw [hout]
        cases k with
        | r0 => exact cp_16_2_1_0 a0 a1 a2 b0 b1 b2 heq
        | r1 => exact cp_16_2_1_1 a0 a1 a2 b0 b1 b2 heq
        | r2 => exact cp_16_2_1_2 a0 a1 a2 b0 b1 b2 heq
        | r3 => exact cp_16_2_1_3 a0 a1 a2 b0 b1 b2 heq
        | r4 => exact cp_16_2_1_4 a0 a1 a2 b0 b1 b2 heq
        | r5 => exact cp_16_2_1_5 a0 a1 a2 b0 b1 b2 heq
        | r6 => exact cp_16_2_1_6 a0 a1 a2 b0 b1 b2 heq
        | r7 => exact cp_16_2_1_7 a0 a1 a2 b0 b1 b2 heq
        | r8 => exact cp_16_2_1_8 a0 a1 a2 b0 b1 b2 heq
        | r9 => exact cp_16_2_1_9 a0 a1 a2 b0 b1 b2 heq
        | r10 => exact cp_16_2_1_10 a0 a1 a2 b0 b1 b2 heq
        | r11 => exact cp_16_2_1_11 a0 a1 a2 b0 b1 b2 heq
        | r12 => exact cp_16_2_1_12 a0 a1 a2 b0 b1 b2 heq
        | r13 => exact cp_16_2_1_13 a0 a1 a2 b0 b1 b2 heq
        | r14 => exact cp_16_2_1_14 a0 a1 a2 b0 b1 b2 heq
        | r15 => exact cp_16_2_1_15 a0 a1 a2 b0 b1 b2 heq
        | r16 => exact cp_16_2_1_16 a0 a1 a2 b0 b1 b2 heq
    ·
      exact var_16_2_2 a0 a1 a2 u1 h1
theorem root_peak {a b c : T} (h : Root a b) (hs : Step a c) : Join b c := by
  rcases h with ⟨k, v0, v1, v2, hl, hr⟩
  rw [hl] at hs
  rw [hr]
  cases k with
  | r0 => exact peak_0 v0 v1 v2 hs
  | r1 => exact peak_1 v0 v1 v2 hs
  | r2 => exact peak_2 v0 v1 v2 hs
  | r3 => exact peak_3 v0 v1 v2 hs
  | r4 => exact peak_4 v0 v1 v2 hs
  | r5 => exact peak_5 v0 v1 v2 hs
  | r6 => exact peak_6 v0 v1 v2 hs
  | r7 => exact peak_7 v0 v1 v2 hs
  | r8 => exact peak_8 v0 v1 v2 hs
  | r9 => exact peak_9 v0 v1 v2 hs
  | r10 => exact peak_10 v0 v1 v2 hs
  | r11 => exact peak_11 v0 v1 v2 hs
  | r12 => exact peak_12 v0 v1 v2 hs
  | r13 => exact peak_13 v0 v1 v2 hs
  | r14 => exact peak_14 v0 v1 v2 hs
  | r15 => exact peak_15 v0 v1 v2 hs
  | r16 => exact peak_16 v0 v1 v2 hs
theorem local_confluence {a b c : T} (h : Step a b) (hs : Step a c) : Join b c := by
  induction h generalizing c with
  | root h => exact root_peak h hs
  | @c_aux0_1 a b x2 h ih =>
    rcases step_aux0_cases hs with hr | ⟨v, rfl, hv⟩ | ⟨v, rfl, hv⟩
    · exact join_symm (root_peak hr (Step.c_aux0_1 x2 h))
    · exact join_aux0_1 x2 (ih hv)
    · exact ⟨(aux0 b v), .single (Step.c_aux0_2 b hv), .single (Step.c_aux0_1 v h)⟩
  | @c_aux0_2 a b x1 h ih =>
    rcases step_aux0_cases hs with hr | ⟨v, rfl, hv⟩ | ⟨v, rfl, hv⟩
    · exact join_symm (root_peak hr (Step.c_aux0_2 x1 h))
    · exact ⟨(aux0 v b), .single (Step.c_aux0_1 b hv), .single (Step.c_aux0_2 v h)⟩
    · exact join_aux0_2 x1 (ih hv)
  | @c_aux1_1 a b x2 h ih =>
    rcases step_aux1_cases hs with hr | ⟨v, rfl, hv⟩ | ⟨v, rfl, hv⟩
    · exact join_symm (root_peak hr (Step.c_aux1_1 x2 h))
    · exact join_aux1_1 x2 (ih hv)
    · exact ⟨(aux1 b v), .single (Step.c_aux1_2 b hv), .single (Step.c_aux1_1 v h)⟩
  | @c_aux1_2 a b x1 h ih =>
    rcases step_aux1_cases hs with hr | ⟨v, rfl, hv⟩ | ⟨v, rfl, hv⟩
    · exact join_symm (root_peak hr (Step.c_aux1_2 x1 h))
    · exact ⟨(aux1 v b), .single (Step.c_aux1_1 b hv), .single (Step.c_aux1_2 v h)⟩
    · exact join_aux1_2 x1 (ih hv)
  | @c_op_1 a b x2 h ih =>
    rcases step_op_cases hs with hr | ⟨v, rfl, hv⟩ | ⟨v, rfl, hv⟩
    · exact join_symm (root_peak hr (Step.c_op_1 x2 h))
    · exact join_op_1 x2 (ih hv)
    · exact ⟨(op b v), .single (Step.c_op_2 b hv), .single (Step.c_op_1 v h)⟩
  | @c_op_2 a b x1 h ih =>
    rcases step_op_cases hs with hr | ⟨v, rfl, hv⟩ | ⟨v, rfl, hv⟩
    · exact join_symm (root_peak hr (Step.c_op_2 x1 h))
    · exact ⟨(op v b), .single (Step.c_op_1 b hv), .single (Step.c_op_2 v h)⟩
    · exact join_op_2 x1 (ih hv)

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
    exact join_equivalence.trans (join_op_1 b hac) (join_op_2 c hbd))

instance : Magma Carrier := ⟨product⟩
theorem project_op (a b : T) : project (op a b) = project a ◇ project b := rfl
theorem project_reach {a b : T} (h : Reach a b) : project a = project b :=
  Quotient.sound ⟨b, h, .refl⟩

theorem source : ∀ x y z : Carrier, x = (y ◇ y) ◇ (x ◇ ((x ◇ z) ◇ z)) := by
  intro q0 q1 q2
  refine Quotient.inductionOn q0 ?_
  intro a0
  refine Quotient.inductionOn q1 ?_
  intro a1
  refine Quotient.inductionOn q2 ?_
  intro a2
  change project a0 = project (op (op a1 a1) (op a0 (op (op a0 a2) a2)))
  exact (project_reach (Relation.ReflTransGen.refl)).trans (project_reach ((((((((Relation.ReflTransGen.refl).tail (Step.c_op_1 (op a0 (op (op a0 a2) a2)) (root_step .r0 a1 (leaf 0) (leaf 0)))).tail (root_step .r2 (op a0 (op (op a0 a2) a2)) (leaf 0) (leaf 0))).tail (Step.c_aux0_1 (op a0 (op (op a0 a2) a2)) (Step.c_op_2 a0 (root_step .r1 a0 a2 (leaf 0))))).tail (Step.c_aux0_1 (op a0 (op (op a0 a2) a2)) (root_step .r3 a0 a2 (leaf 0)))).tail (Step.c_aux0_2 (aux1 a0 a2) (Step.c_op_2 a0 (root_step .r1 a0 a2 (leaf 0))))).tail (Step.c_aux0_2 (aux1 a0 a2) (root_step .r3 a0 a2 (leaf 0)))).tail (root_step .r7 a0 a2 (leaf 0)))).symm

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

end submission
namespace submission
def oppositeMagma : Magma Carrier := ⟨fun a b => product b a⟩
theorem opposite_source : @EquationLHS Carrier oppositeMagma := by
  intro x y z
  change x = (product (product z z) (product x (product (product x y) y)))
  exact source x z y
theorem opposite_target : ¬ @EquationRHS Carrier oppositeMagma := nontrivial
def opposite_result : Goal := ⟨Carrier, oppositeMagma, opposite_source, opposite_target⟩
end submission
def submission : Goal := submission.opposite_result
#print axioms submission

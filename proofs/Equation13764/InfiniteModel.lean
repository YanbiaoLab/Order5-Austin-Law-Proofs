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
  | ab2 : T → T → T → T
  | op : T → T → T
  | rd : T → T → T
open T
def sz : T → Nat
  | .leaf _ => 1
  | .ab2 x0 x1 x2 => 1 * sz x0 + 1 * sz x1 + 1 * sz x2 + 1
  | .op x0 x1 => 4 * sz x0 + 3 * sz x1 + 1
  | .rd x0 x1 => 1 * sz x0 + 1 * sz x1 + 1
theorem sz_pos (a : T) : 0 < sz a := by
  cases a <;> simp only [sz] <;> omega
inductive Rule where
  | r0 | r1 | r2 | r3 | r4 | r5 | r6 | r7 | r8 | r9 | r10 | r11 | r12
def L : Rule → T → T → T → T → T
  | .r0, v0, v1, v2, v3 => (op (op v0 v1) v1)
  | .r1, v0, v1, v2, v3 => (op (rd v0 v1) v0)
  | .r2, v0, v1, v2, v3 => (op (op v0 (rd v1 v2)) v1)
  | .r3, v0, v1, v2, v3 => (op v0 (ab2 v1 v2 v0))
  | .r4, v0, v1, v2, v3 => (op v0 (ab2 v0 v1 v2))
  | .r5, v0, v1, v2, v3 => (rd (ab2 v0 v1 v0) v0)
  | .r6, v0, v1, v2, v3 => (op (ab2 v0 v1 v2) v2)
  | .r7, v0, v1, v2, v3 => (op (op v0 v1) (ab2 v1 v2 v1))
  | .r8, v0, v1, v2, v3 => (op (rd (rd v0 v1) v2) v0)
  | .r9, v0, v1, v2, v3 => (op (rd v0 v1) (ab2 v0 v2 v0))
  | .r10, v0, v1, v2, v3 => (op (ab2 v0 v1 (rd v2 v3)) v2)
  | .r11, v0, v1, v2, v3 => (op (ab2 v0 v1 v2) (ab2 v2 v3 v2))
  | .r12, v0, v1, v2, v3 => (op v0 (ab2 (ab2 v0 v1 v2) v3 (ab2 v0 v1 v2)))
def R : Rule → T → T → T → T → T
  | .r0, v0, v1, v2, v3 => (rd v1 v0)
  | .r1, v0, v1, v2, v3 => (rd v0 (op v1 v0))
  | .r2, v0, v1, v2, v3 => (ab2 v0 v2 v1)
  | .r3, v0, v1, v2, v3 => v1
  | .r4, v0, v1, v2, v3 => (rd (ab2 v0 v1 v2) v2)
  | .r5, v0, v1, v2, v3 => v0
  | .r6, v0, v1, v2, v3 => (rd v2 (op v0 (rd v2 v1)))
  | .r7, v0, v1, v2, v3 => (ab2 v0 v1 (ab2 v1 v2 v1))
  | .r8, v0, v1, v2, v3 => (ab2 (op v2 (rd v0 v1)) v1 v0)
  | .r9, v0, v1, v2, v3 => (ab2 (op v1 v0) v0 (ab2 v0 v2 v0))
  | .r10, v0, v1, v2, v3 => (ab2 (op v0 (rd (rd v2 v3) v1)) v3 v2)
  | .r11, v0, v1, v2, v3 => (ab2 (op v0 (rd v2 v1)) v2 (ab2 v2 v3 v2))
  | .r12, v0, v1, v2, v3 => (ab2 v2 (ab2 v0 v1 v2) (ab2 (ab2 v0 v1 v2) v3 (ab2 v0 v1 v2)))
def Root (t u : T) : Prop :=
  ∃ k v0 v1 v2 v3, t = L k v0 v1 v2 v3 ∧ u = R k v0 v1 v2 v3
inductive Step : T → T → Prop where
  | root {a b : T} : Root a b → Step a b
  | c_ab2_1 {a b : T} (x2 x3 : T) : Step a b → Step (ab2 a x2 x3) (ab2 b x2 x3)
  | c_ab2_2 {a b : T} (x1 x3 : T) : Step a b → Step (ab2 x1 a x3) (ab2 x1 b x3)
  | c_ab2_3 {a b : T} (x1 x2 : T) : Step a b → Step (ab2 x1 x2 a) (ab2 x1 x2 b)
  | c_op_1 {a b : T} (x2 : T) : Step a b → Step (op a x2) (op b x2)
  | c_op_2 {a b : T} (x1 : T) : Step a b → Step (op x1 a) (op x1 b)
  | c_rd_1 {a b : T} (x2 : T) : Step a b → Step (rd a x2) (rd b x2)
  | c_rd_2 {a b : T} (x1 : T) : Step a b → Step (rd x1 a) (rd x1 b)
abbrev Reach := Relation.ReflTransGen Step
def Join (a b : T) : Prop := ∃ c, Reach a c ∧ Reach b c
theorem root_step (k : Rule) (v0 v1 v2 v3 : T) : Step (L k v0 v1 v2 v3) (R k v0 v1 v2 v3) :=
  .root ⟨k, v0, v1, v2, v3, rfl, rfl⟩
theorem root_decrease {a b : T} (h : Root a b) : sz b < sz a := by
  rcases h with ⟨k, v0, v1, v2, v3, rfl, rfl⟩
  have hp_v0 := sz_pos v0
  have hp_v1 := sz_pos v1
  have hp_v2 := sz_pos v2
  have hp_v3 := sz_pos v3
  cases k <;> simp only [L, R, sz] <;> omega
theorem step_decrease {a b : T} (h : Step a b) : sz b < sz a := by
  induction h with
  | root h => exact root_decrease h
  | c_ab2_1 x2 x3 h ih => simp only [sz]; omega
  | c_ab2_2 x1 x3 h ih => simp only [sz]; omega
  | c_ab2_3 x1 x2 h ih => simp only [sz]; omega
  | c_op_1 x2 h ih => simp only [sz]; omega
  | c_op_2 x1 h ih => simp only [sz]; omega
  | c_rd_1 x2 h ih => simp only [sz]; omega
  | c_rd_2 x1 h ih => simp only [sz]; omega
theorem reach_size {a b : T} (h : Reach a b) : sz b ≤ sz a := by
  induction h with
  | refl => exact Nat.le_refl _
  | tail h hs ih => have hd := step_decrease hs; omega
theorem join_symm {a b : T} (h : Join a b) : Join b a := by
  rcases h with ⟨c, h1, h2⟩
  exact ⟨c, h2, h1⟩
theorem reach_ab2_1 {a b : T} (x2 x3 : T) (h : Reach a b) : Reach (ab2 a x2 x3) (ab2 b x2 x3) :=
  h.lift (fun a => (ab2 a x2 x3)) (fun _ _ h => (Step.c_ab2_1 x2 x3 h))
theorem join_ab2_1 {a b : T} (x2 x3 : T) (h : Join a b) : Join (ab2 a x2 x3) (ab2 b x2 x3) := by
  rcases h with ⟨c, h1, h2⟩
  exact ⟨(ab2 c x2 x3), reach_ab2_1 x2 x3 h1, reach_ab2_1 x2 x3 h2⟩
theorem reach_ab2_2 {a b : T} (x1 x3 : T) (h : Reach a b) : Reach (ab2 x1 a x3) (ab2 x1 b x3) :=
  h.lift (fun a => (ab2 x1 a x3)) (fun _ _ h => (Step.c_ab2_2 x1 x3 h))
theorem join_ab2_2 {a b : T} (x1 x3 : T) (h : Join a b) : Join (ab2 x1 a x3) (ab2 x1 b x3) := by
  rcases h with ⟨c, h1, h2⟩
  exact ⟨(ab2 x1 c x3), reach_ab2_2 x1 x3 h1, reach_ab2_2 x1 x3 h2⟩
theorem reach_ab2_3 {a b : T} (x1 x2 : T) (h : Reach a b) : Reach (ab2 x1 x2 a) (ab2 x1 x2 b) :=
  h.lift (fun a => (ab2 x1 x2 a)) (fun _ _ h => (Step.c_ab2_3 x1 x2 h))
theorem join_ab2_3 {a b : T} (x1 x2 : T) (h : Join a b) : Join (ab2 x1 x2 a) (ab2 x1 x2 b) := by
  rcases h with ⟨c, h1, h2⟩
  exact ⟨(ab2 x1 x2 c), reach_ab2_3 x1 x2 h1, reach_ab2_3 x1 x2 h2⟩
theorem step_ab2_cases {x1 x2 x3 u : T} (h : Step (ab2 x1 x2 x3) u) :
    Root (ab2 x1 x2 x3) u ∨ (∃ v, u = (ab2 v x2 x3) ∧ Step x1 v) ∨ (∃ v, u = (ab2 x1 v x3) ∧ Step x2 v) ∨ (∃ v, u = (ab2 x1 x2 v) ∧ Step x3 v) := by
  cases h with
  | root h => exact Or.inl h
  | c_ab2_1 _ _ h => exact (Or.inr (Or.inl ⟨_, rfl, h⟩))
  | c_ab2_2 _ _ h => exact (Or.inr (Or.inr (Or.inl ⟨_, rfl, h⟩)))
  | c_ab2_3 _ _ h => exact (Or.inr (Or.inr (Or.inr ⟨_, rfl, h⟩)))
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
theorem reach_rd_1 {a b : T} (x2 : T) (h : Reach a b) : Reach (rd a x2) (rd b x2) :=
  h.lift (fun a => (rd a x2)) (fun _ _ h => (Step.c_rd_1 x2 h))
theorem join_rd_1 {a b : T} (x2 : T) (h : Join a b) : Join (rd a x2) (rd b x2) := by
  rcases h with ⟨c, h1, h2⟩
  exact ⟨(rd c x2), reach_rd_1 x2 h1, reach_rd_1 x2 h2⟩
theorem reach_rd_2 {a b : T} (x1 : T) (h : Reach a b) : Reach (rd x1 a) (rd x1 b) :=
  h.lift (fun a => (rd x1 a)) (fun _ _ h => (Step.c_rd_2 x1 h))
theorem join_rd_2 {a b : T} (x1 : T) (h : Join a b) : Join (rd x1 a) (rd x1 b) := by
  rcases h with ⟨c, h1, h2⟩
  exact ⟨(rd x1 c), reach_rd_2 x1 h1, reach_rd_2 x1 h2⟩
theorem step_rd_cases {x1 x2 u : T} (h : Step (rd x1 x2) u) :
    Root (rd x1 x2) u ∨ (∃ v, u = (rd v x2) ∧ Step x1 v) ∨ (∃ v, u = (rd x1 v) ∧ Step x2 v) := by
  cases h with
  | root h => exact Or.inl h
  | c_rd_1 _ h => exact (Or.inr (Or.inl ⟨_, rfl, h⟩))
  | c_rd_2 _ h => exact (Or.inr (Or.inr ⟨_, rfl, h⟩))
theorem cp_0_root_0 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (op a0 a1) a1) = (op (op b0 b1) b1)) :
    Join (rd a1 a0) (rd b1 b0) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  rcases T.op.inj he0 with ⟨he2, he3⟩
  clear he0
  clear he3
  subst a0
  exact ⟨(rd b1 b0), (Relation.ReflTransGen.refl), (Relation.ReflTransGen.refl)⟩
theorem cp_0_1_0 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op a0 a1) = (op (op b0 b1) b1)) :
    Join (rd a1 a0) (op (rd b1 b0) a1) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  subst a0
  exact ⟨(rd b1 (op b0 b1)), (Relation.ReflTransGen.refl), ((Relation.ReflTransGen.refl).tail (root_step .r1 b1 b0 (leaf 0) (leaf 0)))⟩
theorem cp_0_root_1 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (op a0 a1) a1) = (op (rd b0 b1) b0)) :
    Join (rd a1 a0) (rd b0 (op b1 b0)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  cases he0
theorem cp_0_1_1 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op a0 a1) = (op (rd b0 b1) b0)) :
    Join (rd a1 a0) (op (rd b0 (op b1 b0)) a1) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  subst a0
  exact ⟨(rd b0 (rd b0 b1)), (Relation.ReflTransGen.refl), (((Relation.ReflTransGen.refl).tail (root_step .r1 b0 (op b1 b0) (leaf 0) (leaf 0))).tail (Step.c_rd_2 b0 (root_step .r0 b1 b0 (leaf 0) (leaf 0))))⟩
theorem cp_0_root_2 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (op a0 a1) a1) = (op (op b0 (rd b1 b2)) b1)) :
    Join (rd a1 a0) (ab2 b0 b2 b1) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  rcases T.op.inj he0 with ⟨he2, he3⟩
  clear he0
  have hsize := congrArg sz he3
  have hp_b1 := sz_pos b1
  have hp_b2 := sz_pos b2
  simp only [sz] at hsize
  omega
theorem cp_0_1_2 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op a0 a1) = (op (op b0 (rd b1 b2)) b1)) :
    Join (rd a1 a0) (op (ab2 b0 b2 b1) a1) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  subst a0
  exact ⟨(rd b1 (op b0 (rd b1 b2))), (Relation.ReflTransGen.refl), ((Relation.ReflTransGen.refl).tail (root_step .r6 b0 b2 b1 (leaf 0)))⟩
theorem cp_0_root_3 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (op a0 a1) a1) = (op b0 (ab2 b1 b2 b0))) :
    Join (rd a1 a0) b1 := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  have hsize := congrArg sz he0
  have hp_a0 := sz_pos a0
  have hp_b0 := sz_pos b0
  have hp_b1 := sz_pos b1
  have hp_b2 := sz_pos b2
  simp only [sz] at hsize
  omega
theorem cp_0_1_3 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op a0 a1) = (op b0 (ab2 b1 b2 b0))) :
    Join (rd a1 a0) (op b1 a1) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  subst a0
  exact ⟨(rd (ab2 b1 b2 b0) b0), (Relation.ReflTransGen.refl), ((Relation.ReflTransGen.refl).tail (root_step .r4 b1 b2 b0 (leaf 0)))⟩
theorem cp_0_root_4 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (op a0 a1) a1) = (op b0 (ab2 b0 b1 b2))) :
    Join (rd a1 a0) (rd (ab2 b0 b1 b2) b2) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  have hsize := congrArg sz he0
  have hp_a0 := sz_pos a0
  have hp_b0 := sz_pos b0
  have hp_b1 := sz_pos b1
  have hp_b2 := sz_pos b2
  simp only [sz] at hsize
  omega
theorem cp_0_1_4 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op a0 a1) = (op b0 (ab2 b0 b1 b2))) :
    Join (rd a1 a0) (op (rd (ab2 b0 b1 b2) b2) a1) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  subst a0
  exact ⟨(rd (ab2 b0 b1 b2) b0), (Relation.ReflTransGen.refl), (((Relation.ReflTransGen.refl).tail (root_step .r1 (ab2 b0 b1 b2) b2 (leaf 0) (leaf 0))).tail (Step.c_rd_2 (ab2 b0 b1 b2) (root_step .r3 b2 b0 b1 (leaf 0))))⟩
theorem cp_0_root_5 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (op a0 a1) a1) = (rd (ab2 b0 b1 b0) b0)) :
    Join (rd a1 a0) b0 := by
  cases heq
theorem cp_0_1_5 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op a0 a1) = (rd (ab2 b0 b1 b0) b0)) :
    Join (rd a1 a0) (op b0 a1) := by
  cases heq
theorem cp_0_root_6 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (op a0 a1) a1) = (op (ab2 b0 b1 b2) b2)) :
    Join (rd a1 a0) (rd b2 (op b0 (rd b2 b1))) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  cases he0
theorem cp_0_1_6 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op a0 a1) = (op (ab2 b0 b1 b2) b2)) :
    Join (rd a1 a0) (op (rd b2 (op b0 (rd b2 b1))) a1) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  subst a0
  exact ⟨(rd b2 (ab2 b0 b1 b2)), (Relation.ReflTransGen.refl), (((Relation.ReflTransGen.refl).tail (root_step .r1 b2 (op b0 (rd b2 b1)) (leaf 0) (leaf 0))).tail (Step.c_rd_2 b2 (root_step .r2 b0 b2 b1 (leaf 0))))⟩
theorem cp_0_root_7 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (op a0 a1) a1) = (op (op b0 b1) (ab2 b1 b2 b1))) :
    Join (rd a1 a0) (ab2 b0 b1 (ab2 b1 b2 b1)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  rcases T.op.inj he0 with ⟨he2, he3⟩
  clear he0
  have hsize := congrArg sz he3
  have hp_b1 := sz_pos b1
  have hp_b2 := sz_pos b2
  simp only [sz] at hsize
  omega
theorem cp_0_1_7 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op a0 a1) = (op (op b0 b1) (ab2 b1 b2 b1))) :
    Join (rd a1 a0) (op (ab2 b0 b1 (ab2 b1 b2 b1)) a1) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  subst a0
  exact ⟨(rd (ab2 b1 b2 b1) (op b0 b1)), (Relation.ReflTransGen.refl), (((Relation.ReflTransGen.refl).tail (root_step .r6 b0 b1 (ab2 b1 b2 b1) (leaf 0))).tail (Step.c_rd_2 (ab2 b1 b2 b1) (Step.c_op_2 b0 (root_step .r5 b1 b2 (leaf 0) (leaf 0)))))⟩
theorem cp_0_root_8 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (op a0 a1) a1) = (op (rd (rd b0 b1) b2) b0)) :
    Join (rd a1 a0) (ab2 (op b2 (rd b0 b1)) b1 b0) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  cases he0
theorem cp_0_1_8 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op a0 a1) = (op (rd (rd b0 b1) b2) b0)) :
    Join (rd a1 a0) (op (ab2 (op b2 (rd b0 b1)) b1 b0) a1) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  subst a0
  exact ⟨(rd b0 (rd (rd b0 b1) b2)), (Relation.ReflTransGen.refl), (((Relation.ReflTransGen.refl).tail (root_step .r6 (op b2 (rd b0 b1)) b1 b0 (leaf 0))).tail (Step.c_rd_2 b0 (root_step .r0 b2 (rd b0 b1) (leaf 0) (leaf 0))))⟩
theorem cp_0_root_9 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (op a0 a1) a1) = (op (rd b0 b1) (ab2 b0 b2 b0))) :
    Join (rd a1 a0) (ab2 (op b1 b0) b0 (ab2 b0 b2 b0)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  cases he0
theorem cp_0_1_9 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op a0 a1) = (op (rd b0 b1) (ab2 b0 b2 b0))) :
    Join (rd a1 a0) (op (ab2 (op b1 b0) b0 (ab2 b0 b2 b0)) a1) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  subst a0
  exact ⟨(rd (ab2 b0 b2 b0) (rd b0 b1)), (Relation.ReflTransGen.refl), ((((Relation.ReflTransGen.refl).tail (root_step .r6 (op b1 b0) b0 (ab2 b0 b2 b0) (leaf 0))).tail (Step.c_rd_2 (ab2 b0 b2 b0) (Step.c_op_2 (op b1 b0) (root_step .r5 b0 b2 (leaf 0) (leaf 0))))).tail (Step.c_rd_2 (ab2 b0 b2 b0) (root_step .r0 b1 b0 (leaf 0) (leaf 0))))⟩
theorem cp_0_root_10 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (op a0 a1) a1) = (op (ab2 b0 b1 (rd b2 b3)) b2)) :
    Join (rd a1 a0) (ab2 (op b0 (rd (rd b2 b3) b1)) b3 b2) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  cases he0
theorem cp_0_1_10 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op a0 a1) = (op (ab2 b0 b1 (rd b2 b3)) b2)) :
    Join (rd a1 a0) (op (ab2 (op b0 (rd (rd b2 b3) b1)) b3 b2) a1) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  subst a0
  exact ⟨(rd b2 (ab2 b0 b1 (rd b2 b3))), (Relation.ReflTransGen.refl), (((Relation.ReflTransGen.refl).tail (root_step .r6 (op b0 (rd (rd b2 b3) b1)) b3 b2 (leaf 0))).tail (Step.c_rd_2 b2 (root_step .r2 b0 (rd b2 b3) b1 (leaf 0))))⟩
theorem cp_0_root_11 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (op a0 a1) a1) = (op (ab2 b0 b1 b2) (ab2 b2 b3 b2))) :
    Join (rd a1 a0) (ab2 (op b0 (rd b2 b1)) b2 (ab2 b2 b3 b2)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  cases he0
theorem cp_0_1_11 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op a0 a1) = (op (ab2 b0 b1 b2) (ab2 b2 b3 b2))) :
    Join (rd a1 a0) (op (ab2 (op b0 (rd b2 b1)) b2 (ab2 b2 b3 b2)) a1) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  subst a0
  exact ⟨(rd (ab2 b2 b3 b2) (ab2 b0 b1 b2)), (Relation.ReflTransGen.refl), ((((Relation.ReflTransGen.refl).tail (root_step .r6 (op b0 (rd b2 b1)) b2 (ab2 b2 b3 b2) (leaf 0))).tail (Step.c_rd_2 (ab2 b2 b3 b2) (Step.c_op_2 (op b0 (rd b2 b1)) (root_step .r5 b2 b3 (leaf 0) (leaf 0))))).tail (Step.c_rd_2 (ab2 b2 b3 b2) (root_step .r2 b0 b2 b1 (leaf 0))))⟩
theorem cp_0_root_12 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (op a0 a1) a1) = (op b0 (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2)))) :
    Join (rd a1 a0) (ab2 b2 (ab2 b0 b1 b2) (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2))) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  have hsize := congrArg sz he0
  have hp_a0 := sz_pos a0
  have hp_b0 := sz_pos b0
  have hp_b1 := sz_pos b1
  have hp_b2 := sz_pos b2
  have hp_b3 := sz_pos b3
  simp only [sz] at hsize
  omega
theorem cp_0_1_12 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op a0 a1) = (op b0 (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2)))) :
    Join (rd a1 a0) (op (ab2 b2 (ab2 b0 b1 b2) (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2))) a1) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  subst a0
  exact ⟨(rd (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2)) b0), (Relation.ReflTransGen.refl), ((((Relation.ReflTransGen.refl).tail (root_step .r6 b2 (ab2 b0 b1 b2) (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2)) (leaf 0))).tail (Step.c_rd_2 (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2)) (Step.c_op_2 b2 (root_step .r5 (ab2 b0 b1 b2) b3 (leaf 0) (leaf 0))))).tail (Step.c_rd_2 (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2)) (root_step .r3 b2 b0 b1 (leaf 0))))⟩
theorem cp_1_root_0 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (rd a0 a1) a0) = (op (op b0 b1) b1)) :
    Join (rd a0 (op a1 a0)) (rd b1 b0) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  cases he0
theorem cp_1_1_0 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd a0 a1) = (op (op b0 b1) b1)) :
    Join (rd a0 (op a1 a0)) (op (rd b1 b0) a0) := by
  cases heq
theorem cp_1_root_1 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (rd a0 a1) a0) = (op (rd b0 b1) b0)) :
    Join (rd a0 (op a1 a0)) (rd b0 (op b1 b0)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  rcases T.rd.inj he0 with ⟨he2, he3⟩
  clear he0
  revert he2
  subst a1
  intro he2
  clear he2
  exact ⟨(rd b0 (op b1 b0)), (Relation.ReflTransGen.refl), (Relation.ReflTransGen.refl)⟩
theorem cp_1_1_1 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd a0 a1) = (op (rd b0 b1) b0)) :
    Join (rd a0 (op a1 a0)) (op (rd b0 (op b1 b0)) a0) := by
  cases heq
theorem cp_1_root_2 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (rd a0 a1) a0) = (op (op b0 (rd b1 b2)) b1)) :
    Join (rd a0 (op a1 a0)) (ab2 b0 b2 b1) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  cases he0
theorem cp_1_1_2 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd a0 a1) = (op (op b0 (rd b1 b2)) b1)) :
    Join (rd a0 (op a1 a0)) (op (ab2 b0 b2 b1) a0) := by
  cases heq
theorem cp_1_root_3 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (rd a0 a1) a0) = (op b0 (ab2 b1 b2 b0))) :
    Join (rd a0 (op a1 a0)) b1 := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  have hsize := congrArg sz he0
  have hp_a1 := sz_pos a1
  have hp_b0 := sz_pos b0
  have hp_b1 := sz_pos b1
  have hp_b2 := sz_pos b2
  simp only [sz] at hsize
  omega
theorem cp_1_1_3 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd a0 a1) = (op b0 (ab2 b1 b2 b0))) :
    Join (rd a0 (op a1 a0)) (op b1 a0) := by
  cases heq
theorem cp_1_root_4 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (rd a0 a1) a0) = (op b0 (ab2 b0 b1 b2))) :
    Join (rd a0 (op a1 a0)) (rd (ab2 b0 b1 b2) b2) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  have hsize := congrArg sz he0
  have hp_a1 := sz_pos a1
  have hp_b0 := sz_pos b0
  have hp_b1 := sz_pos b1
  have hp_b2 := sz_pos b2
  simp only [sz] at hsize
  omega
theorem cp_1_1_4 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd a0 a1) = (op b0 (ab2 b0 b1 b2))) :
    Join (rd a0 (op a1 a0)) (op (rd (ab2 b0 b1 b2) b2) a0) := by
  cases heq
theorem cp_1_root_5 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (rd a0 a1) a0) = (rd (ab2 b0 b1 b0) b0)) :
    Join (rd a0 (op a1 a0)) b0 := by
  cases heq
theorem cp_1_1_5 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd a0 a1) = (rd (ab2 b0 b1 b0) b0)) :
    Join (rd a0 (op a1 a0)) (op b0 a0) := by
  rcases T.rd.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  subst a0
  exact ⟨b0, (((Relation.ReflTransGen.refl).tail (Step.c_rd_2 (ab2 b0 b1 b0) (root_step .r3 b0 b0 b1 (leaf 0)))).tail (root_step .r5 b0 b1 (leaf 0) (leaf 0))), ((Relation.ReflTransGen.refl).tail (root_step .r3 b0 b0 b1 (leaf 0)))⟩
theorem cp_1_root_6 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (rd a0 a1) a0) = (op (ab2 b0 b1 b2) b2)) :
    Join (rd a0 (op a1 a0)) (rd b2 (op b0 (rd b2 b1))) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  cases he0
theorem cp_1_1_6 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd a0 a1) = (op (ab2 b0 b1 b2) b2)) :
    Join (rd a0 (op a1 a0)) (op (rd b2 (op b0 (rd b2 b1))) a0) := by
  cases heq
theorem cp_1_root_7 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (rd a0 a1) a0) = (op (op b0 b1) (ab2 b1 b2 b1))) :
    Join (rd a0 (op a1 a0)) (ab2 b0 b1 (ab2 b1 b2 b1)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  cases he0
theorem cp_1_1_7 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd a0 a1) = (op (op b0 b1) (ab2 b1 b2 b1))) :
    Join (rd a0 (op a1 a0)) (op (ab2 b0 b1 (ab2 b1 b2 b1)) a0) := by
  cases heq
theorem cp_1_root_8 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (rd a0 a1) a0) = (op (rd (rd b0 b1) b2) b0)) :
    Join (rd a0 (op a1 a0)) (ab2 (op b2 (rd b0 b1)) b1 b0) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  rcases T.rd.inj he0 with ⟨he2, he3⟩
  clear he0
  revert he2
  subst a1
  intro he2
  have hsize := congrArg sz he2
  have hp_b0 := sz_pos b0
  have hp_b1 := sz_pos b1
  simp only [sz] at hsize
  omega
theorem cp_1_1_8 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd a0 a1) = (op (rd (rd b0 b1) b2) b0)) :
    Join (rd a0 (op a1 a0)) (op (ab2 (op b2 (rd b0 b1)) b1 b0) a0) := by
  cases heq
theorem cp_1_root_9 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (rd a0 a1) a0) = (op (rd b0 b1) (ab2 b0 b2 b0))) :
    Join (rd a0 (op a1 a0)) (ab2 (op b1 b0) b0 (ab2 b0 b2 b0)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  rcases T.rd.inj he0 with ⟨he2, he3⟩
  clear he0
  revert he2
  subst a1
  intro he2
  have hsize := congrArg sz he2
  have hp_b0 := sz_pos b0
  have hp_b2 := sz_pos b2
  simp only [sz] at hsize
  omega
theorem cp_1_1_9 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd a0 a1) = (op (rd b0 b1) (ab2 b0 b2 b0))) :
    Join (rd a0 (op a1 a0)) (op (ab2 (op b1 b0) b0 (ab2 b0 b2 b0)) a0) := by
  cases heq
theorem cp_1_root_10 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (rd a0 a1) a0) = (op (ab2 b0 b1 (rd b2 b3)) b2)) :
    Join (rd a0 (op a1 a0)) (ab2 (op b0 (rd (rd b2 b3) b1)) b3 b2) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  cases he0
theorem cp_1_1_10 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd a0 a1) = (op (ab2 b0 b1 (rd b2 b3)) b2)) :
    Join (rd a0 (op a1 a0)) (op (ab2 (op b0 (rd (rd b2 b3) b1)) b3 b2) a0) := by
  cases heq
theorem cp_1_root_11 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (rd a0 a1) a0) = (op (ab2 b0 b1 b2) (ab2 b2 b3 b2))) :
    Join (rd a0 (op a1 a0)) (ab2 (op b0 (rd b2 b1)) b2 (ab2 b2 b3 b2)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  cases he0
theorem cp_1_1_11 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd a0 a1) = (op (ab2 b0 b1 b2) (ab2 b2 b3 b2))) :
    Join (rd a0 (op a1 a0)) (op (ab2 (op b0 (rd b2 b1)) b2 (ab2 b2 b3 b2)) a0) := by
  cases heq
theorem cp_1_root_12 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (rd a0 a1) a0) = (op b0 (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2)))) :
    Join (rd a0 (op a1 a0)) (ab2 b2 (ab2 b0 b1 b2) (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2))) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  have hsize := congrArg sz he0
  have hp_a1 := sz_pos a1
  have hp_b0 := sz_pos b0
  have hp_b1 := sz_pos b1
  have hp_b2 := sz_pos b2
  have hp_b3 := sz_pos b3
  simp only [sz] at hsize
  omega
theorem cp_1_1_12 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd a0 a1) = (op b0 (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2)))) :
    Join (rd a0 (op a1 a0)) (op (ab2 b2 (ab2 b0 b1 b2) (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2))) a0) := by
  cases heq
theorem cp_2_root_0 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (op a0 (rd a1 a2)) a1) = (op (op b0 b1) b1)) :
    Join (ab2 a0 a2 a1) (rd b1 b0) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  rcases T.op.inj he0 with ⟨he2, he3⟩
  clear he0
  have hsize := congrArg sz he3
  have hp_a2 := sz_pos a2
  have hp_b1 := sz_pos b1
  simp only [sz] at hsize
  omega
theorem cp_2_1_0 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op a0 (rd a1 a2)) = (op (op b0 b1) b1)) :
    Join (ab2 a0 a2 a1) (op (rd b1 b0) a1) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst b1
  intro he0
  subst a0
  exact ⟨(ab2 (op b0 (rd a1 a2)) a2 a1), (Relation.ReflTransGen.refl), ((Relation.ReflTransGen.refl).tail (root_step .r8 a1 a2 b0 (leaf 0)))⟩
theorem cp_2_12_0 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd a1 a2) = (op (op b0 b1) b1)) :
    Join (ab2 a0 a2 a1) (op (op a0 (rd b1 b0)) a1) := by
  cases heq
theorem cp_2_root_1 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (op a0 (rd a1 a2)) a1) = (op (rd b0 b1) b0)) :
    Join (ab2 a0 a2 a1) (rd b0 (op b1 b0)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  cases he0
theorem cp_2_1_1 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op a0 (rd a1 a2)) = (op (rd b0 b1) b0)) :
    Join (ab2 a0 a2 a1) (op (rd b0 (op b1 b0)) a1) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst b0
  intro he0
  subst a0
  exact ⟨(ab2 (rd (rd a1 a2) b1) a2 a1), (Relation.ReflTransGen.refl), (((Relation.ReflTransGen.refl).tail (root_step .r8 a1 a2 (op b1 (rd a1 a2)) (leaf 0))).tail (Step.c_ab2_1 a2 a1 (root_step .r0 b1 (rd a1 a2) (leaf 0) (leaf 0))))⟩
theorem cp_2_12_1 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd a1 a2) = (op (rd b0 b1) b0)) :
    Join (ab2 a0 a2 a1) (op (op a0 (rd b0 (op b1 b0))) a1) := by
  cases heq
theorem cp_2_root_2 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (op a0 (rd a1 a2)) a1) = (op (op b0 (rd b1 b2)) b1)) :
    Join (ab2 a0 a2 a1) (ab2 b0 b2 b1) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  rcases T.op.inj he0 with ⟨he2, he3⟩
  clear he0
  rcases T.rd.inj he3 with ⟨he4, he5⟩
  clear he3
  revert he2 he4
  subst a2
  intro he2 he4
  clear he4
  subst a0
  exact ⟨(ab2 b0 b2 b1), (Relation.ReflTransGen.refl), (Relation.ReflTransGen.refl)⟩
theorem cp_2_1_2 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op a0 (rd a1 a2)) = (op (op b0 (rd b1 b2)) b1)) :
    Join (ab2 a0 a2 a1) (op (ab2 b0 b2 b1) a1) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst b1
  intro he0
  subst a0
  exact ⟨(ab2 (op b0 (rd (rd a1 a2) b2)) a2 a1), (Relation.ReflTransGen.refl), ((Relation.ReflTransGen.refl).tail (root_step .r10 b0 b2 a1 a2))⟩
theorem cp_2_12_2 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd a1 a2) = (op (op b0 (rd b1 b2)) b1)) :
    Join (ab2 a0 a2 a1) (op (op a0 (ab2 b0 b2 b1)) a1) := by
  cases heq
theorem cp_2_root_3 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (op a0 (rd a1 a2)) a1) = (op b0 (ab2 b1 b2 b0))) :
    Join (ab2 a0 a2 a1) b1 := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  have hsize := congrArg sz he0
  have hp_a0 := sz_pos a0
  have hp_a2 := sz_pos a2
  have hp_b0 := sz_pos b0
  have hp_b1 := sz_pos b1
  have hp_b2 := sz_pos b2
  simp only [sz] at hsize
  omega
theorem cp_2_1_3 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op a0 (rd a1 a2)) = (op b0 (ab2 b1 b2 b0))) :
    Join (ab2 a0 a2 a1) (op b1 a1) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  cases he1
theorem cp_2_12_3 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd a1 a2) = (op b0 (ab2 b1 b2 b0))) :
    Join (ab2 a0 a2 a1) (op (op a0 b1) a1) := by
  cases heq
theorem cp_2_root_4 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (op a0 (rd a1 a2)) a1) = (op b0 (ab2 b0 b1 b2))) :
    Join (ab2 a0 a2 a1) (rd (ab2 b0 b1 b2) b2) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  have hsize := congrArg sz he0
  have hp_a0 := sz_pos a0
  have hp_a2 := sz_pos a2
  have hp_b0 := sz_pos b0
  have hp_b1 := sz_pos b1
  have hp_b2 := sz_pos b2
  simp only [sz] at hsize
  omega
theorem cp_2_1_4 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op a0 (rd a1 a2)) = (op b0 (ab2 b0 b1 b2))) :
    Join (ab2 a0 a2 a1) (op (rd (ab2 b0 b1 b2) b2) a1) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  cases he1
theorem cp_2_12_4 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd a1 a2) = (op b0 (ab2 b0 b1 b2))) :
    Join (ab2 a0 a2 a1) (op (op a0 (rd (ab2 b0 b1 b2) b2)) a1) := by
  cases heq
theorem cp_2_root_5 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (op a0 (rd a1 a2)) a1) = (rd (ab2 b0 b1 b0) b0)) :
    Join (ab2 a0 a2 a1) b0 := by
  cases heq
theorem cp_2_1_5 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op a0 (rd a1 a2)) = (rd (ab2 b0 b1 b0) b0)) :
    Join (ab2 a0 a2 a1) (op b0 a1) := by
  cases heq
theorem cp_2_12_5 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd a1 a2) = (rd (ab2 b0 b1 b0) b0)) :
    Join (ab2 a0 a2 a1) (op (op a0 b0) a1) := by
  rcases T.rd.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a2
  intro he0
  subst a1
  exact ⟨(ab2 a0 b0 (ab2 b0 b1 b0)), (Relation.ReflTransGen.refl), ((Relation.ReflTransGen.refl).tail (root_step .r7 a0 b0 b1 (leaf 0)))⟩
theorem cp_2_root_6 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (op a0 (rd a1 a2)) a1) = (op (ab2 b0 b1 b2) b2)) :
    Join (ab2 a0 a2 a1) (rd b2 (op b0 (rd b2 b1))) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  cases he0
theorem cp_2_1_6 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op a0 (rd a1 a2)) = (op (ab2 b0 b1 b2) b2)) :
    Join (ab2 a0 a2 a1) (op (rd b2 (op b0 (rd b2 b1))) a1) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst b2
  intro he0
  subst a0
  exact ⟨(ab2 (ab2 b0 b1 (rd a1 a2)) a2 a1), (Relation.ReflTransGen.refl), (((Relation.ReflTransGen.refl).tail (root_step .r8 a1 a2 (op b0 (rd (rd a1 a2) b1)) (leaf 0))).tail (Step.c_ab2_1 a2 a1 (root_step .r2 b0 (rd a1 a2) b1 (leaf 0))))⟩
theorem cp_2_12_6 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd a1 a2) = (op (ab2 b0 b1 b2) b2)) :
    Join (ab2 a0 a2 a1) (op (op a0 (rd b2 (op b0 (rd b2 b1)))) a1) := by
  cases heq
theorem cp_2_root_7 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (op a0 (rd a1 a2)) a1) = (op (op b0 b1) (ab2 b1 b2 b1))) :
    Join (ab2 a0 a2 a1) (ab2 b0 b1 (ab2 b1 b2 b1)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  rcases T.op.inj he0 with ⟨he2, he3⟩
  clear he0
  have hsize := congrArg sz he3
  have hp_a2 := sz_pos a2
  have hp_b1 := sz_pos b1
  have hp_b2 := sz_pos b2
  simp only [sz] at hsize
  omega
theorem cp_2_1_7 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op a0 (rd a1 a2)) = (op (op b0 b1) (ab2 b1 b2 b1))) :
    Join (ab2 a0 a2 a1) (op (ab2 b0 b1 (ab2 b1 b2 b1)) a1) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  cases he1
theorem cp_2_12_7 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd a1 a2) = (op (op b0 b1) (ab2 b1 b2 b1))) :
    Join (ab2 a0 a2 a1) (op (op a0 (ab2 b0 b1 (ab2 b1 b2 b1))) a1) := by
  cases heq
theorem cp_2_root_8 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (op a0 (rd a1 a2)) a1) = (op (rd (rd b0 b1) b2) b0)) :
    Join (ab2 a0 a2 a1) (ab2 (op b2 (rd b0 b1)) b1 b0) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  cases he0
theorem cp_2_1_8 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op a0 (rd a1 a2)) = (op (rd (rd b0 b1) b2) b0)) :
    Join (ab2 a0 a2 a1) (op (ab2 (op b2 (rd b0 b1)) b1 b0) a1) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst b0
  intro he0
  subst a0
  exact ⟨(ab2 (rd (rd (rd a1 a2) b1) b2) a2 a1), (Relation.ReflTransGen.refl), (((Relation.ReflTransGen.refl).tail (root_step .r10 (op b2 (rd (rd a1 a2) b1)) b1 a1 a2)).tail (Step.c_ab2_1 a2 a1 (root_step .r0 b2 (rd (rd a1 a2) b1) (leaf 0) (leaf 0))))⟩
theorem cp_2_12_8 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd a1 a2) = (op (rd (rd b0 b1) b2) b0)) :
    Join (ab2 a0 a2 a1) (op (op a0 (ab2 (op b2 (rd b0 b1)) b1 b0)) a1) := by
  cases heq
theorem cp_2_root_9 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (op a0 (rd a1 a2)) a1) = (op (rd b0 b1) (ab2 b0 b2 b0))) :
    Join (ab2 a0 a2 a1) (ab2 (op b1 b0) b0 (ab2 b0 b2 b0)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  cases he0
theorem cp_2_1_9 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op a0 (rd a1 a2)) = (op (rd b0 b1) (ab2 b0 b2 b0))) :
    Join (ab2 a0 a2 a1) (op (ab2 (op b1 b0) b0 (ab2 b0 b2 b0)) a1) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  cases he1
theorem cp_2_12_9 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd a1 a2) = (op (rd b0 b1) (ab2 b0 b2 b0))) :
    Join (ab2 a0 a2 a1) (op (op a0 (ab2 (op b1 b0) b0 (ab2 b0 b2 b0))) a1) := by
  cases heq
theorem cp_2_root_10 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (op a0 (rd a1 a2)) a1) = (op (ab2 b0 b1 (rd b2 b3)) b2)) :
    Join (ab2 a0 a2 a1) (ab2 (op b0 (rd (rd b2 b3) b1)) b3 b2) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  cases he0
theorem cp_2_1_10 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op a0 (rd a1 a2)) = (op (ab2 b0 b1 (rd b2 b3)) b2)) :
    Join (ab2 a0 a2 a1) (op (ab2 (op b0 (rd (rd b2 b3) b1)) b3 b2) a1) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst b2
  intro he0
  subst a0
  exact ⟨(ab2 (ab2 b0 b1 (rd (rd a1 a2) b3)) a2 a1), (Relation.ReflTransGen.refl), (((Relation.ReflTransGen.refl).tail (root_step .r10 (op b0 (rd (rd (rd a1 a2) b3) b1)) b3 a1 a2)).tail (Step.c_ab2_1 a2 a1 (root_step .r2 b0 (rd (rd a1 a2) b3) b1 (leaf 0))))⟩
theorem cp_2_12_10 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd a1 a2) = (op (ab2 b0 b1 (rd b2 b3)) b2)) :
    Join (ab2 a0 a2 a1) (op (op a0 (ab2 (op b0 (rd (rd b2 b3) b1)) b3 b2)) a1) := by
  cases heq
theorem cp_2_root_11 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (op a0 (rd a1 a2)) a1) = (op (ab2 b0 b1 b2) (ab2 b2 b3 b2))) :
    Join (ab2 a0 a2 a1) (ab2 (op b0 (rd b2 b1)) b2 (ab2 b2 b3 b2)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  cases he0
theorem cp_2_1_11 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op a0 (rd a1 a2)) = (op (ab2 b0 b1 b2) (ab2 b2 b3 b2))) :
    Join (ab2 a0 a2 a1) (op (ab2 (op b0 (rd b2 b1)) b2 (ab2 b2 b3 b2)) a1) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  cases he1
theorem cp_2_12_11 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd a1 a2) = (op (ab2 b0 b1 b2) (ab2 b2 b3 b2))) :
    Join (ab2 a0 a2 a1) (op (op a0 (ab2 (op b0 (rd b2 b1)) b2 (ab2 b2 b3 b2))) a1) := by
  cases heq
theorem cp_2_root_12 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (op a0 (rd a1 a2)) a1) = (op b0 (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2)))) :
    Join (ab2 a0 a2 a1) (ab2 b2 (ab2 b0 b1 b2) (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2))) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  have hsize := congrArg sz he0
  have hp_a0 := sz_pos a0
  have hp_a2 := sz_pos a2
  have hp_b0 := sz_pos b0
  have hp_b1 := sz_pos b1
  have hp_b2 := sz_pos b2
  have hp_b3 := sz_pos b3
  simp only [sz] at hsize
  omega
theorem cp_2_1_12 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op a0 (rd a1 a2)) = (op b0 (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2)))) :
    Join (ab2 a0 a2 a1) (op (ab2 b2 (ab2 b0 b1 b2) (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2))) a1) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  cases he1
theorem cp_2_12_12 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd a1 a2) = (op b0 (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2)))) :
    Join (ab2 a0 a2 a1) (op (op a0 (ab2 b2 (ab2 b0 b1 b2) (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2)))) a1) := by
  cases heq
theorem cp_3_root_0 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op a0 (ab2 a1 a2 a0)) = (op (op b0 b1) b1)) :
    Join a1 (rd b1 b0) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst b1
  intro he0
  have hsize := congrArg sz he0
  have hp_a0 := sz_pos a0
  have hp_a1 := sz_pos a1
  have hp_a2 := sz_pos a2
  have hp_b0 := sz_pos b0
  simp only [sz] at hsize
  omega
theorem cp_3_2_0 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a1 a2 a0) = (op (op b0 b1) b1)) :
    Join a1 (op a0 (rd b1 b0)) := by
  cases heq
theorem cp_3_root_1 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op a0 (ab2 a1 a2 a0)) = (op (rd b0 b1) b0)) :
    Join a1 (rd b0 (op b1 b0)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst b0
  intro he0
  have hsize := congrArg sz he0
  have hp_a0 := sz_pos a0
  have hp_a1 := sz_pos a1
  have hp_a2 := sz_pos a2
  have hp_b1 := sz_pos b1
  simp only [sz] at hsize
  omega
theorem cp_3_2_1 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a1 a2 a0) = (op (rd b0 b1) b0)) :
    Join a1 (op a0 (rd b0 (op b1 b0))) := by
  cases heq
theorem cp_3_root_2 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op a0 (ab2 a1 a2 a0)) = (op (op b0 (rd b1 b2)) b1)) :
    Join a1 (ab2 b0 b2 b1) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst b1
  intro he0
  have hsize := congrArg sz he0
  have hp_a0 := sz_pos a0
  have hp_a1 := sz_pos a1
  have hp_a2 := sz_pos a2
  have hp_b0 := sz_pos b0
  have hp_b2 := sz_pos b2
  simp only [sz] at hsize
  omega
theorem cp_3_2_2 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a1 a2 a0) = (op (op b0 (rd b1 b2)) b1)) :
    Join a1 (op a0 (ab2 b0 b2 b1)) := by
  cases heq
theorem cp_3_root_3 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op a0 (ab2 a1 a2 a0)) = (op b0 (ab2 b1 b2 b0))) :
    Join a1 b1 := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  rcases T.ab2.inj he1 with ⟨he2, he3, he4⟩
  clear he1
  revert he0 he2 he3
  subst a0
  intro he0 he2 he3
  revert he0 he2
  subst a2
  intro he0 he2
  revert he0
  subst a1
  intro he0
  clear he0
  exact ⟨b1, (Relation.ReflTransGen.refl), (Relation.ReflTransGen.refl)⟩
theorem cp_3_2_3 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a1 a2 a0) = (op b0 (ab2 b1 b2 b0))) :
    Join a1 (op a0 b1) := by
  cases heq
theorem cp_3_root_4 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op a0 (ab2 a1 a2 a0)) = (op b0 (ab2 b0 b1 b2))) :
    Join a1 (rd (ab2 b0 b1 b2) b2) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  rcases T.ab2.inj he1 with ⟨he2, he3, he4⟩
  clear he1
  revert he0 he2 he3
  subst a0
  intro he0 he2 he3
  revert he0 he2
  subst a2
  intro he0 he2
  revert he0
  subst a1
  intro he0
  subst b2
  exact ⟨b0, (Relation.ReflTransGen.refl), ((Relation.ReflTransGen.refl).tail (root_step .r5 b0 b1 (leaf 0) (leaf 0)))⟩
theorem cp_3_2_4 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a1 a2 a0) = (op b0 (ab2 b0 b1 b2))) :
    Join a1 (op a0 (rd (ab2 b0 b1 b2) b2)) := by
  cases heq
theorem cp_3_root_5 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op a0 (ab2 a1 a2 a0)) = (rd (ab2 b0 b1 b0) b0)) :
    Join a1 b0 := by
  cases heq
theorem cp_3_2_5 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a1 a2 a0) = (rd (ab2 b0 b1 b0) b0)) :
    Join a1 (op a0 b0) := by
  cases heq
theorem cp_3_root_6 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op a0 (ab2 a1 a2 a0)) = (op (ab2 b0 b1 b2) b2)) :
    Join a1 (rd b2 (op b0 (rd b2 b1))) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst b2
  intro he0
  have hsize := congrArg sz he0
  have hp_a0 := sz_pos a0
  have hp_a1 := sz_pos a1
  have hp_a2 := sz_pos a2
  have hp_b0 := sz_pos b0
  have hp_b1 := sz_pos b1
  simp only [sz] at hsize
  omega
theorem cp_3_2_6 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a1 a2 a0) = (op (ab2 b0 b1 b2) b2)) :
    Join a1 (op a0 (rd b2 (op b0 (rd b2 b1)))) := by
  cases heq
theorem cp_3_root_7 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op a0 (ab2 a1 a2 a0)) = (op (op b0 b1) (ab2 b1 b2 b1))) :
    Join a1 (ab2 b0 b1 (ab2 b1 b2 b1)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  rcases T.ab2.inj he1 with ⟨he2, he3, he4⟩
  clear he1
  revert he0 he2 he3
  subst a0
  intro he0 he2 he3
  revert he0 he2
  subst a2
  intro he0 he2
  revert he0
  subst a1
  intro he0
  have hsize := congrArg sz he0
  have hp_b0 := sz_pos b0
  have hp_b1 := sz_pos b1
  simp only [sz] at hsize
  omega
theorem cp_3_2_7 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a1 a2 a0) = (op (op b0 b1) (ab2 b1 b2 b1))) :
    Join a1 (op a0 (ab2 b0 b1 (ab2 b1 b2 b1))) := by
  cases heq
theorem cp_3_root_8 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op a0 (ab2 a1 a2 a0)) = (op (rd (rd b0 b1) b2) b0)) :
    Join a1 (ab2 (op b2 (rd b0 b1)) b1 b0) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst b0
  intro he0
  have hsize := congrArg sz he0
  have hp_a0 := sz_pos a0
  have hp_a1 := sz_pos a1
  have hp_a2 := sz_pos a2
  have hp_b1 := sz_pos b1
  have hp_b2 := sz_pos b2
  simp only [sz] at hsize
  omega
theorem cp_3_2_8 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a1 a2 a0) = (op (rd (rd b0 b1) b2) b0)) :
    Join a1 (op a0 (ab2 (op b2 (rd b0 b1)) b1 b0)) := by
  cases heq
theorem cp_3_root_9 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op a0 (ab2 a1 a2 a0)) = (op (rd b0 b1) (ab2 b0 b2 b0))) :
    Join a1 (ab2 (op b1 b0) b0 (ab2 b0 b2 b0)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  rcases T.ab2.inj he1 with ⟨he2, he3, he4⟩
  clear he1
  revert he0 he2 he3
  subst a0
  intro he0 he2 he3
  revert he0 he2
  subst a2
  intro he0 he2
  revert he0
  subst a1
  intro he0
  have hsize := congrArg sz he0
  have hp_b0 := sz_pos b0
  have hp_b1 := sz_pos b1
  simp only [sz] at hsize
  omega
theorem cp_3_2_9 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a1 a2 a0) = (op (rd b0 b1) (ab2 b0 b2 b0))) :
    Join a1 (op a0 (ab2 (op b1 b0) b0 (ab2 b0 b2 b0))) := by
  cases heq
theorem cp_3_root_10 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op a0 (ab2 a1 a2 a0)) = (op (ab2 b0 b1 (rd b2 b3)) b2)) :
    Join a1 (ab2 (op b0 (rd (rd b2 b3) b1)) b3 b2) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst b2
  intro he0
  have hsize := congrArg sz he0
  have hp_a0 := sz_pos a0
  have hp_a1 := sz_pos a1
  have hp_a2 := sz_pos a2
  have hp_b0 := sz_pos b0
  have hp_b1 := sz_pos b1
  have hp_b3 := sz_pos b3
  simp only [sz] at hsize
  omega
theorem cp_3_2_10 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a1 a2 a0) = (op (ab2 b0 b1 (rd b2 b3)) b2)) :
    Join a1 (op a0 (ab2 (op b0 (rd (rd b2 b3) b1)) b3 b2)) := by
  cases heq
theorem cp_3_root_11 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op a0 (ab2 a1 a2 a0)) = (op (ab2 b0 b1 b2) (ab2 b2 b3 b2))) :
    Join a1 (ab2 (op b0 (rd b2 b1)) b2 (ab2 b2 b3 b2)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  rcases T.ab2.inj he1 with ⟨he2, he3, he4⟩
  clear he1
  revert he0 he2 he3
  subst a0
  intro he0 he2 he3
  revert he0 he2
  subst a2
  intro he0 he2
  revert he0
  subst a1
  intro he0
  have hsize := congrArg sz he0
  have hp_b0 := sz_pos b0
  have hp_b1 := sz_pos b1
  have hp_b2 := sz_pos b2
  simp only [sz] at hsize
  omega
theorem cp_3_2_11 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a1 a2 a0) = (op (ab2 b0 b1 b2) (ab2 b2 b3 b2))) :
    Join a1 (op a0 (ab2 (op b0 (rd b2 b1)) b2 (ab2 b2 b3 b2))) := by
  cases heq
theorem cp_3_root_12 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op a0 (ab2 a1 a2 a0)) = (op b0 (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2)))) :
    Join a1 (ab2 b2 (ab2 b0 b1 b2) (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2))) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  rcases T.ab2.inj he1 with ⟨he2, he3, he4⟩
  clear he1
  revert he0 he2 he3
  subst a0
  intro he0 he2 he3
  revert he0 he2
  subst a2
  intro he0 he2
  revert he0
  subst a1
  intro he0
  have hsize := congrArg sz he0
  have hp_b0 := sz_pos b0
  have hp_b1 := sz_pos b1
  have hp_b2 := sz_pos b2
  simp only [sz] at hsize
  omega
theorem cp_3_2_12 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a1 a2 a0) = (op b0 (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2)))) :
    Join a1 (op a0 (ab2 b2 (ab2 b0 b1 b2) (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2)))) := by
  cases heq
theorem cp_4_root_0 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op a0 (ab2 a0 a1 a2)) = (op (op b0 b1) b1)) :
    Join (rd (ab2 a0 a1 a2) a2) (rd b1 b0) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst b1
  intro he0
  have hsize := congrArg sz he0
  have hp_a0 := sz_pos a0
  have hp_a1 := sz_pos a1
  have hp_a2 := sz_pos a2
  have hp_b0 := sz_pos b0
  simp only [sz] at hsize
  omega
theorem cp_4_2_0 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 a2) = (op (op b0 b1) b1)) :
    Join (rd (ab2 a0 a1 a2) a2) (op a0 (rd b1 b0)) := by
  cases heq
theorem cp_4_root_1 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op a0 (ab2 a0 a1 a2)) = (op (rd b0 b1) b0)) :
    Join (rd (ab2 a0 a1 a2) a2) (rd b0 (op b1 b0)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst b0
  intro he0
  have hsize := congrArg sz he0
  have hp_a0 := sz_pos a0
  have hp_a1 := sz_pos a1
  have hp_a2 := sz_pos a2
  have hp_b1 := sz_pos b1
  simp only [sz] at hsize
  omega
theorem cp_4_2_1 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 a2) = (op (rd b0 b1) b0)) :
    Join (rd (ab2 a0 a1 a2) a2) (op a0 (rd b0 (op b1 b0))) := by
  cases heq
theorem cp_4_root_2 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op a0 (ab2 a0 a1 a2)) = (op (op b0 (rd b1 b2)) b1)) :
    Join (rd (ab2 a0 a1 a2) a2) (ab2 b0 b2 b1) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst b1
  intro he0
  have hsize := congrArg sz he0
  have hp_a0 := sz_pos a0
  have hp_a1 := sz_pos a1
  have hp_a2 := sz_pos a2
  have hp_b0 := sz_pos b0
  have hp_b2 := sz_pos b2
  simp only [sz] at hsize
  omega
theorem cp_4_2_2 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 a2) = (op (op b0 (rd b1 b2)) b1)) :
    Join (rd (ab2 a0 a1 a2) a2) (op a0 (ab2 b0 b2 b1)) := by
  cases heq
theorem cp_4_root_3 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op a0 (ab2 a0 a1 a2)) = (op b0 (ab2 b1 b2 b0))) :
    Join (rd (ab2 a0 a1 a2) a2) b1 := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  rcases T.ab2.inj he1 with ⟨he2, he3, he4⟩
  clear he1
  revert he0 he2 he3
  subst a2
  intro he0 he2 he3
  revert he0 he2
  subst a1
  intro he0 he2
  revert he0
  subst a0
  intro he0
  subst b1
  exact ⟨b0, ((Relation.ReflTransGen.refl).tail (root_step .r5 b0 b2 (leaf 0) (leaf 0))), (Relation.ReflTransGen.refl)⟩
theorem cp_4_2_3 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 a2) = (op b0 (ab2 b1 b2 b0))) :
    Join (rd (ab2 a0 a1 a2) a2) (op a0 b1) := by
  cases heq
theorem cp_4_root_4 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op a0 (ab2 a0 a1 a2)) = (op b0 (ab2 b0 b1 b2))) :
    Join (rd (ab2 a0 a1 a2) a2) (rd (ab2 b0 b1 b2) b2) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  rcases T.ab2.inj he1 with ⟨he2, he3, he4⟩
  clear he1
  revert he0 he2 he3
  subst a2
  intro he0 he2 he3
  revert he0 he2
  subst a1
  intro he0 he2
  revert he0
  subst a0
  intro he0
  clear he0
  exact ⟨(rd (ab2 b0 b1 b2) b2), (Relation.ReflTransGen.refl), (Relation.ReflTransGen.refl)⟩
theorem cp_4_2_4 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 a2) = (op b0 (ab2 b0 b1 b2))) :
    Join (rd (ab2 a0 a1 a2) a2) (op a0 (rd (ab2 b0 b1 b2) b2)) := by
  cases heq
theorem cp_4_root_5 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op a0 (ab2 a0 a1 a2)) = (rd (ab2 b0 b1 b0) b0)) :
    Join (rd (ab2 a0 a1 a2) a2) b0 := by
  cases heq
theorem cp_4_2_5 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 a2) = (rd (ab2 b0 b1 b0) b0)) :
    Join (rd (ab2 a0 a1 a2) a2) (op a0 b0) := by
  cases heq
theorem cp_4_root_6 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op a0 (ab2 a0 a1 a2)) = (op (ab2 b0 b1 b2) b2)) :
    Join (rd (ab2 a0 a1 a2) a2) (rd b2 (op b0 (rd b2 b1))) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst b2
  intro he0
  have hsize := congrArg sz he0
  have hp_a0 := sz_pos a0
  have hp_a1 := sz_pos a1
  have hp_a2 := sz_pos a2
  have hp_b0 := sz_pos b0
  have hp_b1 := sz_pos b1
  simp only [sz] at hsize
  omega
theorem cp_4_2_6 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 a2) = (op (ab2 b0 b1 b2) b2)) :
    Join (rd (ab2 a0 a1 a2) a2) (op a0 (rd b2 (op b0 (rd b2 b1)))) := by
  cases heq
theorem cp_4_root_7 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op a0 (ab2 a0 a1 a2)) = (op (op b0 b1) (ab2 b1 b2 b1))) :
    Join (rd (ab2 a0 a1 a2) a2) (ab2 b0 b1 (ab2 b1 b2 b1)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  rcases T.ab2.inj he1 with ⟨he2, he3, he4⟩
  clear he1
  revert he0 he2 he3
  subst a2
  intro he0 he2 he3
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
theorem cp_4_2_7 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 a2) = (op (op b0 b1) (ab2 b1 b2 b1))) :
    Join (rd (ab2 a0 a1 a2) a2) (op a0 (ab2 b0 b1 (ab2 b1 b2 b1))) := by
  cases heq
theorem cp_4_root_8 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op a0 (ab2 a0 a1 a2)) = (op (rd (rd b0 b1) b2) b0)) :
    Join (rd (ab2 a0 a1 a2) a2) (ab2 (op b2 (rd b0 b1)) b1 b0) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst b0
  intro he0
  have hsize := congrArg sz he0
  have hp_a0 := sz_pos a0
  have hp_a1 := sz_pos a1
  have hp_a2 := sz_pos a2
  have hp_b1 := sz_pos b1
  have hp_b2 := sz_pos b2
  simp only [sz] at hsize
  omega
theorem cp_4_2_8 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 a2) = (op (rd (rd b0 b1) b2) b0)) :
    Join (rd (ab2 a0 a1 a2) a2) (op a0 (ab2 (op b2 (rd b0 b1)) b1 b0)) := by
  cases heq
theorem cp_4_root_9 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op a0 (ab2 a0 a1 a2)) = (op (rd b0 b1) (ab2 b0 b2 b0))) :
    Join (rd (ab2 a0 a1 a2) a2) (ab2 (op b1 b0) b0 (ab2 b0 b2 b0)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  rcases T.ab2.inj he1 with ⟨he2, he3, he4⟩
  clear he1
  revert he0 he2 he3
  subst a2
  intro he0 he2 he3
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
theorem cp_4_2_9 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 a2) = (op (rd b0 b1) (ab2 b0 b2 b0))) :
    Join (rd (ab2 a0 a1 a2) a2) (op a0 (ab2 (op b1 b0) b0 (ab2 b0 b2 b0))) := by
  cases heq
theorem cp_4_root_10 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op a0 (ab2 a0 a1 a2)) = (op (ab2 b0 b1 (rd b2 b3)) b2)) :
    Join (rd (ab2 a0 a1 a2) a2) (ab2 (op b0 (rd (rd b2 b3) b1)) b3 b2) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst b2
  intro he0
  have hsize := congrArg sz he0
  have hp_a0 := sz_pos a0
  have hp_a1 := sz_pos a1
  have hp_a2 := sz_pos a2
  have hp_b0 := sz_pos b0
  have hp_b1 := sz_pos b1
  have hp_b3 := sz_pos b3
  simp only [sz] at hsize
  omega
theorem cp_4_2_10 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 a2) = (op (ab2 b0 b1 (rd b2 b3)) b2)) :
    Join (rd (ab2 a0 a1 a2) a2) (op a0 (ab2 (op b0 (rd (rd b2 b3) b1)) b3 b2)) := by
  cases heq
theorem cp_4_root_11 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op a0 (ab2 a0 a1 a2)) = (op (ab2 b0 b1 b2) (ab2 b2 b3 b2))) :
    Join (rd (ab2 a0 a1 a2) a2) (ab2 (op b0 (rd b2 b1)) b2 (ab2 b2 b3 b2)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  rcases T.ab2.inj he1 with ⟨he2, he3, he4⟩
  clear he1
  revert he0 he2 he3
  subst a2
  intro he0 he2 he3
  revert he0 he2
  subst a1
  intro he0 he2
  revert he0
  subst a0
  intro he0
  have hsize := congrArg sz he0
  have hp_b0 := sz_pos b0
  have hp_b1 := sz_pos b1
  have hp_b2 := sz_pos b2
  simp only [sz] at hsize
  omega
theorem cp_4_2_11 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 a2) = (op (ab2 b0 b1 b2) (ab2 b2 b3 b2))) :
    Join (rd (ab2 a0 a1 a2) a2) (op a0 (ab2 (op b0 (rd b2 b1)) b2 (ab2 b2 b3 b2))) := by
  cases heq
theorem cp_4_root_12 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op a0 (ab2 a0 a1 a2)) = (op b0 (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2)))) :
    Join (rd (ab2 a0 a1 a2) a2) (ab2 b2 (ab2 b0 b1 b2) (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2))) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  rcases T.ab2.inj he1 with ⟨he2, he3, he4⟩
  clear he1
  revert he0 he2 he3
  subst a2
  intro he0 he2 he3
  revert he0 he2
  subst a1
  intro he0 he2
  revert he0
  subst a0
  intro he0
  have hsize := congrArg sz he0
  have hp_b0 := sz_pos b0
  have hp_b1 := sz_pos b1
  have hp_b2 := sz_pos b2
  simp only [sz] at hsize
  omega
theorem cp_4_2_12 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 a2) = (op b0 (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2)))) :
    Join (rd (ab2 a0 a1 a2) a2) (op a0 (ab2 b2 (ab2 b0 b1 b2) (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2)))) := by
  cases heq
theorem cp_5_root_0 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd (ab2 a0 a1 a0) a0) = (op (op b0 b1) b1)) :
    Join a0 (rd b1 b0) := by
  cases heq
theorem cp_5_1_0 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 a0) = (op (op b0 b1) b1)) :
    Join a0 (rd (rd b1 b0) a0) := by
  cases heq
theorem cp_5_root_1 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd (ab2 a0 a1 a0) a0) = (op (rd b0 b1) b0)) :
    Join a0 (rd b0 (op b1 b0)) := by
  cases heq
theorem cp_5_1_1 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 a0) = (op (rd b0 b1) b0)) :
    Join a0 (rd (rd b0 (op b1 b0)) a0) := by
  cases heq
theorem cp_5_root_2 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd (ab2 a0 a1 a0) a0) = (op (op b0 (rd b1 b2)) b1)) :
    Join a0 (ab2 b0 b2 b1) := by
  cases heq
theorem cp_5_1_2 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 a0) = (op (op b0 (rd b1 b2)) b1)) :
    Join a0 (rd (ab2 b0 b2 b1) a0) := by
  cases heq
theorem cp_5_root_3 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd (ab2 a0 a1 a0) a0) = (op b0 (ab2 b1 b2 b0))) :
    Join a0 b1 := by
  cases heq
theorem cp_5_1_3 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 a0) = (op b0 (ab2 b1 b2 b0))) :
    Join a0 (rd b1 a0) := by
  cases heq
theorem cp_5_root_4 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd (ab2 a0 a1 a0) a0) = (op b0 (ab2 b0 b1 b2))) :
    Join a0 (rd (ab2 b0 b1 b2) b2) := by
  cases heq
theorem cp_5_1_4 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 a0) = (op b0 (ab2 b0 b1 b2))) :
    Join a0 (rd (rd (ab2 b0 b1 b2) b2) a0) := by
  cases heq
theorem cp_5_root_5 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd (ab2 a0 a1 a0) a0) = (rd (ab2 b0 b1 b0) b0)) :
    Join a0 b0 := by
  rcases T.rd.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  rcases T.ab2.inj he0 with ⟨he2, he3, he4⟩
  clear he0
  clear he4
  revert he2
  subst a1
  intro he2
  clear he2
  exact ⟨b0, (Relation.ReflTransGen.refl), (Relation.ReflTransGen.refl)⟩
theorem cp_5_1_5 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 a0) = (rd (ab2 b0 b1 b0) b0)) :
    Join a0 (rd b0 a0) := by
  cases heq
theorem cp_5_root_6 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd (ab2 a0 a1 a0) a0) = (op (ab2 b0 b1 b2) b2)) :
    Join a0 (rd b2 (op b0 (rd b2 b1))) := by
  cases heq
theorem cp_5_1_6 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 a0) = (op (ab2 b0 b1 b2) b2)) :
    Join a0 (rd (rd b2 (op b0 (rd b2 b1))) a0) := by
  cases heq
theorem cp_5_root_7 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd (ab2 a0 a1 a0) a0) = (op (op b0 b1) (ab2 b1 b2 b1))) :
    Join a0 (ab2 b0 b1 (ab2 b1 b2 b1)) := by
  cases heq
theorem cp_5_1_7 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 a0) = (op (op b0 b1) (ab2 b1 b2 b1))) :
    Join a0 (rd (ab2 b0 b1 (ab2 b1 b2 b1)) a0) := by
  cases heq
theorem cp_5_root_8 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd (ab2 a0 a1 a0) a0) = (op (rd (rd b0 b1) b2) b0)) :
    Join a0 (ab2 (op b2 (rd b0 b1)) b1 b0) := by
  cases heq
theorem cp_5_1_8 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 a0) = (op (rd (rd b0 b1) b2) b0)) :
    Join a0 (rd (ab2 (op b2 (rd b0 b1)) b1 b0) a0) := by
  cases heq
theorem cp_5_root_9 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd (ab2 a0 a1 a0) a0) = (op (rd b0 b1) (ab2 b0 b2 b0))) :
    Join a0 (ab2 (op b1 b0) b0 (ab2 b0 b2 b0)) := by
  cases heq
theorem cp_5_1_9 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 a0) = (op (rd b0 b1) (ab2 b0 b2 b0))) :
    Join a0 (rd (ab2 (op b1 b0) b0 (ab2 b0 b2 b0)) a0) := by
  cases heq
theorem cp_5_root_10 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd (ab2 a0 a1 a0) a0) = (op (ab2 b0 b1 (rd b2 b3)) b2)) :
    Join a0 (ab2 (op b0 (rd (rd b2 b3) b1)) b3 b2) := by
  cases heq
theorem cp_5_1_10 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 a0) = (op (ab2 b0 b1 (rd b2 b3)) b2)) :
    Join a0 (rd (ab2 (op b0 (rd (rd b2 b3) b1)) b3 b2) a0) := by
  cases heq
theorem cp_5_root_11 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd (ab2 a0 a1 a0) a0) = (op (ab2 b0 b1 b2) (ab2 b2 b3 b2))) :
    Join a0 (ab2 (op b0 (rd b2 b1)) b2 (ab2 b2 b3 b2)) := by
  cases heq
theorem cp_5_1_11 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 a0) = (op (ab2 b0 b1 b2) (ab2 b2 b3 b2))) :
    Join a0 (rd (ab2 (op b0 (rd b2 b1)) b2 (ab2 b2 b3 b2)) a0) := by
  cases heq
theorem cp_5_root_12 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd (ab2 a0 a1 a0) a0) = (op b0 (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2)))) :
    Join a0 (ab2 b2 (ab2 b0 b1 b2) (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2))) := by
  cases heq
theorem cp_5_1_12 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 a0) = (op b0 (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2)))) :
    Join a0 (rd (ab2 b2 (ab2 b0 b1 b2) (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2))) a0) := by
  cases heq
theorem cp_6_root_0 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (ab2 a0 a1 a2) a2) = (op (op b0 b1) b1)) :
    Join (rd a2 (op a0 (rd a2 a1))) (rd b1 b0) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a2
  intro he0
  cases he0
theorem cp_6_1_0 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 a2) = (op (op b0 b1) b1)) :
    Join (rd a2 (op a0 (rd a2 a1))) (op (rd b1 b0) a2) := by
  cases heq
theorem cp_6_root_1 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (ab2 a0 a1 a2) a2) = (op (rd b0 b1) b0)) :
    Join (rd a2 (op a0 (rd a2 a1))) (rd b0 (op b1 b0)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a2
  intro he0
  cases he0
theorem cp_6_1_1 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 a2) = (op (rd b0 b1) b0)) :
    Join (rd a2 (op a0 (rd a2 a1))) (op (rd b0 (op b1 b0)) a2) := by
  cases heq
theorem cp_6_root_2 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (ab2 a0 a1 a2) a2) = (op (op b0 (rd b1 b2)) b1)) :
    Join (rd a2 (op a0 (rd a2 a1))) (ab2 b0 b2 b1) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a2
  intro he0
  cases he0
theorem cp_6_1_2 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 a2) = (op (op b0 (rd b1 b2)) b1)) :
    Join (rd a2 (op a0 (rd a2 a1))) (op (ab2 b0 b2 b1) a2) := by
  cases heq
theorem cp_6_root_3 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (ab2 a0 a1 a2) a2) = (op b0 (ab2 b1 b2 b0))) :
    Join (rd a2 (op a0 (rd a2 a1))) b1 := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a2
  intro he0
  have hsize := congrArg sz he0
  have hp_a0 := sz_pos a0
  have hp_a1 := sz_pos a1
  have hp_b0 := sz_pos b0
  have hp_b1 := sz_pos b1
  have hp_b2 := sz_pos b2
  simp only [sz] at hsize
  omega
theorem cp_6_1_3 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 a2) = (op b0 (ab2 b1 b2 b0))) :
    Join (rd a2 (op a0 (rd a2 a1))) (op b1 a2) := by
  cases heq
theorem cp_6_root_4 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (ab2 a0 a1 a2) a2) = (op b0 (ab2 b0 b1 b2))) :
    Join (rd a2 (op a0 (rd a2 a1))) (rd (ab2 b0 b1 b2) b2) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a2
  intro he0
  have hsize := congrArg sz he0
  have hp_a0 := sz_pos a0
  have hp_a1 := sz_pos a1
  have hp_b0 := sz_pos b0
  have hp_b1 := sz_pos b1
  have hp_b2 := sz_pos b2
  simp only [sz] at hsize
  omega
theorem cp_6_1_4 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 a2) = (op b0 (ab2 b0 b1 b2))) :
    Join (rd a2 (op a0 (rd a2 a1))) (op (rd (ab2 b0 b1 b2) b2) a2) := by
  cases heq
theorem cp_6_root_5 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (ab2 a0 a1 a2) a2) = (rd (ab2 b0 b1 b0) b0)) :
    Join (rd a2 (op a0 (rd a2 a1))) b0 := by
  cases heq
theorem cp_6_1_5 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 a2) = (rd (ab2 b0 b1 b0) b0)) :
    Join (rd a2 (op a0 (rd a2 a1))) (op b0 a2) := by
  cases heq
theorem cp_6_root_6 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (ab2 a0 a1 a2) a2) = (op (ab2 b0 b1 b2) b2)) :
    Join (rd a2 (op a0 (rd a2 a1))) (rd b2 (op b0 (rd b2 b1))) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a2
  intro he0
  rcases T.ab2.inj he0 with ⟨he2, he3, he4⟩
  clear he0
  clear he4
  revert he2
  subst a1
  intro he2
  subst a0
  exact ⟨(rd b2 (op b0 (rd b2 b1))), (Relation.ReflTransGen.refl), (Relation.ReflTransGen.refl)⟩
theorem cp_6_1_6 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 a2) = (op (ab2 b0 b1 b2) b2)) :
    Join (rd a2 (op a0 (rd a2 a1))) (op (rd b2 (op b0 (rd b2 b1))) a2) := by
  cases heq
theorem cp_6_root_7 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (ab2 a0 a1 a2) a2) = (op (op b0 b1) (ab2 b1 b2 b1))) :
    Join (rd a2 (op a0 (rd a2 a1))) (ab2 b0 b1 (ab2 b1 b2 b1)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a2
  intro he0
  cases he0
theorem cp_6_1_7 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 a2) = (op (op b0 b1) (ab2 b1 b2 b1))) :
    Join (rd a2 (op a0 (rd a2 a1))) (op (ab2 b0 b1 (ab2 b1 b2 b1)) a2) := by
  cases heq
theorem cp_6_root_8 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (ab2 a0 a1 a2) a2) = (op (rd (rd b0 b1) b2) b0)) :
    Join (rd a2 (op a0 (rd a2 a1))) (ab2 (op b2 (rd b0 b1)) b1 b0) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a2
  intro he0
  cases he0
theorem cp_6_1_8 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 a2) = (op (rd (rd b0 b1) b2) b0)) :
    Join (rd a2 (op a0 (rd a2 a1))) (op (ab2 (op b2 (rd b0 b1)) b1 b0) a2) := by
  cases heq
theorem cp_6_root_9 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (ab2 a0 a1 a2) a2) = (op (rd b0 b1) (ab2 b0 b2 b0))) :
    Join (rd a2 (op a0 (rd a2 a1))) (ab2 (op b1 b0) b0 (ab2 b0 b2 b0)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a2
  intro he0
  cases he0
theorem cp_6_1_9 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 a2) = (op (rd b0 b1) (ab2 b0 b2 b0))) :
    Join (rd a2 (op a0 (rd a2 a1))) (op (ab2 (op b1 b0) b0 (ab2 b0 b2 b0)) a2) := by
  cases heq
theorem cp_6_root_10 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (ab2 a0 a1 a2) a2) = (op (ab2 b0 b1 (rd b2 b3)) b2)) :
    Join (rd a2 (op a0 (rd a2 a1))) (ab2 (op b0 (rd (rd b2 b3) b1)) b3 b2) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a2
  intro he0
  rcases T.ab2.inj he0 with ⟨he2, he3, he4⟩
  clear he0
  have hsize := congrArg sz he4
  have hp_b2 := sz_pos b2
  have hp_b3 := sz_pos b3
  simp only [sz] at hsize
  omega
theorem cp_6_1_10 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 a2) = (op (ab2 b0 b1 (rd b2 b3)) b2)) :
    Join (rd a2 (op a0 (rd a2 a1))) (op (ab2 (op b0 (rd (rd b2 b3) b1)) b3 b2) a2) := by
  cases heq
theorem cp_6_root_11 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (ab2 a0 a1 a2) a2) = (op (ab2 b0 b1 b2) (ab2 b2 b3 b2))) :
    Join (rd a2 (op a0 (rd a2 a1))) (ab2 (op b0 (rd b2 b1)) b2 (ab2 b2 b3 b2)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a2
  intro he0
  rcases T.ab2.inj he0 with ⟨he2, he3, he4⟩
  clear he0
  have hsize := congrArg sz he4
  have hp_b2 := sz_pos b2
  have hp_b3 := sz_pos b3
  simp only [sz] at hsize
  omega
theorem cp_6_1_11 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 a2) = (op (ab2 b0 b1 b2) (ab2 b2 b3 b2))) :
    Join (rd a2 (op a0 (rd a2 a1))) (op (ab2 (op b0 (rd b2 b1)) b2 (ab2 b2 b3 b2)) a2) := by
  cases heq
theorem cp_6_root_12 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (ab2 a0 a1 a2) a2) = (op b0 (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2)))) :
    Join (rd a2 (op a0 (rd a2 a1))) (ab2 b2 (ab2 b0 b1 b2) (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2))) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a2
  intro he0
  have hsize := congrArg sz he0
  have hp_a0 := sz_pos a0
  have hp_a1 := sz_pos a1
  have hp_b0 := sz_pos b0
  have hp_b1 := sz_pos b1
  have hp_b2 := sz_pos b2
  have hp_b3 := sz_pos b3
  simp only [sz] at hsize
  omega
theorem cp_6_1_12 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 a2) = (op b0 (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2)))) :
    Join (rd a2 (op a0 (rd a2 a1))) (op (ab2 b2 (ab2 b0 b1 b2) (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2))) a2) := by
  cases heq
theorem cp_7_root_0 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (op a0 a1) (ab2 a1 a2 a1)) = (op (op b0 b1) b1)) :
    Join (ab2 a0 a1 (ab2 a1 a2 a1)) (rd b1 b0) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst b1
  intro he0
  rcases T.op.inj he0 with ⟨he2, he3⟩
  clear he0
  have hsize := congrArg sz he3
  have hp_a1 := sz_pos a1
  have hp_a2 := sz_pos a2
  simp only [sz] at hsize
  omega
theorem cp_7_1_0 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op a0 a1) = (op (op b0 b1) b1)) :
    Join (ab2 a0 a1 (ab2 a1 a2 a1)) (op (rd b1 b0) (ab2 a1 a2 a1)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  subst a0
  exact ⟨(ab2 (op b0 b1) b1 (ab2 b1 a2 b1)), (Relation.ReflTransGen.refl), ((Relation.ReflTransGen.refl).tail (root_step .r9 b1 b0 a2 (leaf 0)))⟩
theorem cp_7_2_0 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a1 a2 a1) = (op (op b0 b1) b1)) :
    Join (ab2 a0 a1 (ab2 a1 a2 a1)) (op (op a0 a1) (rd b1 b0)) := by
  cases heq
theorem cp_7_root_1 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (op a0 a1) (ab2 a1 a2 a1)) = (op (rd b0 b1) b0)) :
    Join (ab2 a0 a1 (ab2 a1 a2 a1)) (rd b0 (op b1 b0)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst b0
  intro he0
  cases he0
theorem cp_7_1_1 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op a0 a1) = (op (rd b0 b1) b0)) :
    Join (ab2 a0 a1 (ab2 a1 a2 a1)) (op (rd b0 (op b1 b0)) (ab2 a1 a2 a1)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  subst a0
  exact ⟨(ab2 (rd b0 b1) b0 (ab2 b0 a2 b0)), (Relation.ReflTransGen.refl), (((Relation.ReflTransGen.refl).tail (root_step .r9 b0 (op b1 b0) a2 (leaf 0))).tail (Step.c_ab2_1 b0 (ab2 b0 a2 b0) (root_step .r0 b1 b0 (leaf 0) (leaf 0))))⟩
theorem cp_7_2_1 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a1 a2 a1) = (op (rd b0 b1) b0)) :
    Join (ab2 a0 a1 (ab2 a1 a2 a1)) (op (op a0 a1) (rd b0 (op b1 b0))) := by
  cases heq
theorem cp_7_root_2 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (op a0 a1) (ab2 a1 a2 a1)) = (op (op b0 (rd b1 b2)) b1)) :
    Join (ab2 a0 a1 (ab2 a1 a2 a1)) (ab2 b0 b2 b1) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst b1
  intro he0
  rcases T.op.inj he0 with ⟨he2, he3⟩
  clear he0
  have hsize := congrArg sz he3
  have hp_a1 := sz_pos a1
  have hp_a2 := sz_pos a2
  have hp_b2 := sz_pos b2
  simp only [sz] at hsize
  omega
theorem cp_7_1_2 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op a0 a1) = (op (op b0 (rd b1 b2)) b1)) :
    Join (ab2 a0 a1 (ab2 a1 a2 a1)) (op (ab2 b0 b2 b1) (ab2 a1 a2 a1)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  subst a0
  exact ⟨(ab2 (op b0 (rd b1 b2)) b1 (ab2 b1 a2 b1)), (Relation.ReflTransGen.refl), ((Relation.ReflTransGen.refl).tail (root_step .r11 b0 b2 b1 a2))⟩
theorem cp_7_2_2 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a1 a2 a1) = (op (op b0 (rd b1 b2)) b1)) :
    Join (ab2 a0 a1 (ab2 a1 a2 a1)) (op (op a0 a1) (ab2 b0 b2 b1)) := by
  cases heq
theorem cp_7_root_3 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (op a0 a1) (ab2 a1 a2 a1)) = (op b0 (ab2 b1 b2 b0))) :
    Join (ab2 a0 a1 (ab2 a1 a2 a1)) b1 := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  rcases T.ab2.inj he1 with ⟨he2, he3, he4⟩
  clear he1
  revert he0 he2 he3
  subst a1
  intro he0 he2 he3
  revert he0 he2
  subst a2
  intro he0 he2
  revert he0
  subst b0
  intro he0
  have hsize := congrArg sz he0
  have hp_a0 := sz_pos a0
  have hp_b1 := sz_pos b1
  simp only [sz] at hsize
  omega
theorem cp_7_1_3 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op a0 a1) = (op b0 (ab2 b1 b2 b0))) :
    Join (ab2 a0 a1 (ab2 a1 a2 a1)) (op b1 (ab2 a1 a2 a1)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  subst a0
  exact ⟨(ab2 b0 (ab2 b1 b2 b0) (ab2 (ab2 b1 b2 b0) a2 (ab2 b1 b2 b0))), (Relation.ReflTransGen.refl), ((Relation.ReflTransGen.refl).tail (root_step .r12 b1 b2 b0 a2))⟩
theorem cp_7_2_3 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a1 a2 a1) = (op b0 (ab2 b1 b2 b0))) :
    Join (ab2 a0 a1 (ab2 a1 a2 a1)) (op (op a0 a1) b1) := by
  cases heq
theorem cp_7_root_4 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (op a0 a1) (ab2 a1 a2 a1)) = (op b0 (ab2 b0 b1 b2))) :
    Join (ab2 a0 a1 (ab2 a1 a2 a1)) (rd (ab2 b0 b1 b2) b2) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  rcases T.ab2.inj he1 with ⟨he2, he3, he4⟩
  clear he1
  revert he0 he2 he3
  subst a1
  intro he0 he2 he3
  revert he0 he2
  subst a2
  intro he0 he2
  revert he0
  subst b2
  intro he0
  have hsize := congrArg sz he0
  have hp_a0 := sz_pos a0
  have hp_b0 := sz_pos b0
  simp only [sz] at hsize
  omega
theorem cp_7_1_4 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op a0 a1) = (op b0 (ab2 b0 b1 b2))) :
    Join (ab2 a0 a1 (ab2 a1 a2 a1)) (op (rd (ab2 b0 b1 b2) b2) (ab2 a1 a2 a1)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  subst a0
  exact ⟨(ab2 b0 (ab2 b0 b1 b2) (ab2 (ab2 b0 b1 b2) a2 (ab2 b0 b1 b2))), (Relation.ReflTransGen.refl), (((Relation.ReflTransGen.refl).tail (root_step .r9 (ab2 b0 b1 b2) b2 a2 (leaf 0))).tail (Step.c_ab2_1 (ab2 b0 b1 b2) (ab2 (ab2 b0 b1 b2) a2 (ab2 b0 b1 b2)) (root_step .r3 b2 b0 b1 (leaf 0))))⟩
theorem cp_7_2_4 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a1 a2 a1) = (op b0 (ab2 b0 b1 b2))) :
    Join (ab2 a0 a1 (ab2 a1 a2 a1)) (op (op a0 a1) (rd (ab2 b0 b1 b2) b2)) := by
  cases heq
theorem cp_7_root_5 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (op a0 a1) (ab2 a1 a2 a1)) = (rd (ab2 b0 b1 b0) b0)) :
    Join (ab2 a0 a1 (ab2 a1 a2 a1)) b0 := by
  cases heq
theorem cp_7_1_5 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op a0 a1) = (rd (ab2 b0 b1 b0) b0)) :
    Join (ab2 a0 a1 (ab2 a1 a2 a1)) (op b0 (ab2 a1 a2 a1)) := by
  cases heq
theorem cp_7_2_5 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a1 a2 a1) = (rd (ab2 b0 b1 b0) b0)) :
    Join (ab2 a0 a1 (ab2 a1 a2 a1)) (op (op a0 a1) b0) := by
  cases heq
theorem cp_7_root_6 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (op a0 a1) (ab2 a1 a2 a1)) = (op (ab2 b0 b1 b2) b2)) :
    Join (ab2 a0 a1 (ab2 a1 a2 a1)) (rd b2 (op b0 (rd b2 b1))) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst b2
  intro he0
  cases he0
theorem cp_7_1_6 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op a0 a1) = (op (ab2 b0 b1 b2) b2)) :
    Join (ab2 a0 a1 (ab2 a1 a2 a1)) (op (rd b2 (op b0 (rd b2 b1))) (ab2 a1 a2 a1)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  subst a0
  exact ⟨(ab2 (ab2 b0 b1 b2) b2 (ab2 b2 a2 b2)), (Relation.ReflTransGen.refl), (((Relation.ReflTransGen.refl).tail (root_step .r9 b2 (op b0 (rd b2 b1)) a2 (leaf 0))).tail (Step.c_ab2_1 b2 (ab2 b2 a2 b2) (root_step .r2 b0 b2 b1 (leaf 0))))⟩
theorem cp_7_2_6 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a1 a2 a1) = (op (ab2 b0 b1 b2) b2)) :
    Join (ab2 a0 a1 (ab2 a1 a2 a1)) (op (op a0 a1) (rd b2 (op b0 (rd b2 b1)))) := by
  cases heq
theorem cp_7_root_7 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (op a0 a1) (ab2 a1 a2 a1)) = (op (op b0 b1) (ab2 b1 b2 b1))) :
    Join (ab2 a0 a1 (ab2 a1 a2 a1)) (ab2 b0 b1 (ab2 b1 b2 b1)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  rcases T.ab2.inj he1 with ⟨he2, he3, he4⟩
  clear he1
  revert he0 he2 he3
  subst a1
  intro he0 he2 he3
  revert he0 he2
  subst a2
  intro he0 he2
  clear he2
  rcases T.op.inj he0 with ⟨he5, he6⟩
  clear he0
  clear he6
  subst a0
  exact ⟨(ab2 b0 b1 (ab2 b1 b2 b1)), (Relation.ReflTransGen.refl), (Relation.ReflTransGen.refl)⟩
theorem cp_7_1_7 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op a0 a1) = (op (op b0 b1) (ab2 b1 b2 b1))) :
    Join (ab2 a0 a1 (ab2 a1 a2 a1)) (op (ab2 b0 b1 (ab2 b1 b2 b1)) (ab2 a1 a2 a1)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  subst a0
  exact ⟨(ab2 (op b0 b1) (ab2 b1 b2 b1) (ab2 (ab2 b1 b2 b1) a2 (ab2 b1 b2 b1))), (Relation.ReflTransGen.refl), (((Relation.ReflTransGen.refl).tail (root_step .r11 b0 b1 (ab2 b1 b2 b1) a2)).tail (Step.c_ab2_1 (ab2 b1 b2 b1) (ab2 (ab2 b1 b2 b1) a2 (ab2 b1 b2 b1)) (Step.c_op_2 b0 (root_step .r5 b1 b2 (leaf 0) (leaf 0)))))⟩
theorem cp_7_2_7 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a1 a2 a1) = (op (op b0 b1) (ab2 b1 b2 b1))) :
    Join (ab2 a0 a1 (ab2 a1 a2 a1)) (op (op a0 a1) (ab2 b0 b1 (ab2 b1 b2 b1))) := by
  cases heq
theorem cp_7_root_8 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (op a0 a1) (ab2 a1 a2 a1)) = (op (rd (rd b0 b1) b2) b0)) :
    Join (ab2 a0 a1 (ab2 a1 a2 a1)) (ab2 (op b2 (rd b0 b1)) b1 b0) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst b0
  intro he0
  cases he0
theorem cp_7_1_8 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op a0 a1) = (op (rd (rd b0 b1) b2) b0)) :
    Join (ab2 a0 a1 (ab2 a1 a2 a1)) (op (ab2 (op b2 (rd b0 b1)) b1 b0) (ab2 a1 a2 a1)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  subst a0
  exact ⟨(ab2 (rd (rd b0 b1) b2) b0 (ab2 b0 a2 b0)), (Relation.ReflTransGen.refl), (((Relation.ReflTransGen.refl).tail (root_step .r11 (op b2 (rd b0 b1)) b1 b0 a2)).tail (Step.c_ab2_1 b0 (ab2 b0 a2 b0) (root_step .r0 b2 (rd b0 b1) (leaf 0) (leaf 0))))⟩
theorem cp_7_2_8 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a1 a2 a1) = (op (rd (rd b0 b1) b2) b0)) :
    Join (ab2 a0 a1 (ab2 a1 a2 a1)) (op (op a0 a1) (ab2 (op b2 (rd b0 b1)) b1 b0)) := by
  cases heq
theorem cp_7_root_9 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (op a0 a1) (ab2 a1 a2 a1)) = (op (rd b0 b1) (ab2 b0 b2 b0))) :
    Join (ab2 a0 a1 (ab2 a1 a2 a1)) (ab2 (op b1 b0) b0 (ab2 b0 b2 b0)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  rcases T.ab2.inj he1 with ⟨he2, he3, he4⟩
  clear he1
  revert he0 he2 he3
  subst a1
  intro he0 he2 he3
  revert he0 he2
  subst a2
  intro he0 he2
  clear he2
  cases he0
theorem cp_7_1_9 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op a0 a1) = (op (rd b0 b1) (ab2 b0 b2 b0))) :
    Join (ab2 a0 a1 (ab2 a1 a2 a1)) (op (ab2 (op b1 b0) b0 (ab2 b0 b2 b0)) (ab2 a1 a2 a1)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  subst a0
  exact ⟨(ab2 (rd b0 b1) (ab2 b0 b2 b0) (ab2 (ab2 b0 b2 b0) a2 (ab2 b0 b2 b0))), (Relation.ReflTransGen.refl), ((((Relation.ReflTransGen.refl).tail (root_step .r11 (op b1 b0) b0 (ab2 b0 b2 b0) a2)).tail (Step.c_ab2_1 (ab2 b0 b2 b0) (ab2 (ab2 b0 b2 b0) a2 (ab2 b0 b2 b0)) (Step.c_op_2 (op b1 b0) (root_step .r5 b0 b2 (leaf 0) (leaf 0))))).tail (Step.c_ab2_1 (ab2 b0 b2 b0) (ab2 (ab2 b0 b2 b0) a2 (ab2 b0 b2 b0)) (root_step .r0 b1 b0 (leaf 0) (leaf 0))))⟩
theorem cp_7_2_9 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a1 a2 a1) = (op (rd b0 b1) (ab2 b0 b2 b0))) :
    Join (ab2 a0 a1 (ab2 a1 a2 a1)) (op (op a0 a1) (ab2 (op b1 b0) b0 (ab2 b0 b2 b0))) := by
  cases heq
theorem cp_7_root_10 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (op a0 a1) (ab2 a1 a2 a1)) = (op (ab2 b0 b1 (rd b2 b3)) b2)) :
    Join (ab2 a0 a1 (ab2 a1 a2 a1)) (ab2 (op b0 (rd (rd b2 b3) b1)) b3 b2) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst b2
  intro he0
  cases he0
theorem cp_7_1_10 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op a0 a1) = (op (ab2 b0 b1 (rd b2 b3)) b2)) :
    Join (ab2 a0 a1 (ab2 a1 a2 a1)) (op (ab2 (op b0 (rd (rd b2 b3) b1)) b3 b2) (ab2 a1 a2 a1)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  subst a0
  exact ⟨(ab2 (ab2 b0 b1 (rd b2 b3)) b2 (ab2 b2 a2 b2)), (Relation.ReflTransGen.refl), (((Relation.ReflTransGen.refl).tail (root_step .r11 (op b0 (rd (rd b2 b3) b1)) b3 b2 a2)).tail (Step.c_ab2_1 b2 (ab2 b2 a2 b2) (root_step .r2 b0 (rd b2 b3) b1 (leaf 0))))⟩
theorem cp_7_2_10 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a1 a2 a1) = (op (ab2 b0 b1 (rd b2 b3)) b2)) :
    Join (ab2 a0 a1 (ab2 a1 a2 a1)) (op (op a0 a1) (ab2 (op b0 (rd (rd b2 b3) b1)) b3 b2)) := by
  cases heq
theorem cp_7_root_11 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (op a0 a1) (ab2 a1 a2 a1)) = (op (ab2 b0 b1 b2) (ab2 b2 b3 b2))) :
    Join (ab2 a0 a1 (ab2 a1 a2 a1)) (ab2 (op b0 (rd b2 b1)) b2 (ab2 b2 b3 b2)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  rcases T.ab2.inj he1 with ⟨he2, he3, he4⟩
  clear he1
  revert he0 he2 he3
  subst a1
  intro he0 he2 he3
  revert he0 he2
  subst a2
  intro he0 he2
  clear he2
  cases he0
theorem cp_7_1_11 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op a0 a1) = (op (ab2 b0 b1 b2) (ab2 b2 b3 b2))) :
    Join (ab2 a0 a1 (ab2 a1 a2 a1)) (op (ab2 (op b0 (rd b2 b1)) b2 (ab2 b2 b3 b2)) (ab2 a1 a2 a1)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  subst a0
  exact ⟨(ab2 (ab2 b0 b1 b2) (ab2 b2 b3 b2) (ab2 (ab2 b2 b3 b2) a2 (ab2 b2 b3 b2))), (Relation.ReflTransGen.refl), ((((Relation.ReflTransGen.refl).tail (root_step .r11 (op b0 (rd b2 b1)) b2 (ab2 b2 b3 b2) a2)).tail (Step.c_ab2_1 (ab2 b2 b3 b2) (ab2 (ab2 b2 b3 b2) a2 (ab2 b2 b3 b2)) (Step.c_op_2 (op b0 (rd b2 b1)) (root_step .r5 b2 b3 (leaf 0) (leaf 0))))).tail (Step.c_ab2_1 (ab2 b2 b3 b2) (ab2 (ab2 b2 b3 b2) a2 (ab2 b2 b3 b2)) (root_step .r2 b0 b2 b1 (leaf 0))))⟩
theorem cp_7_2_11 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a1 a2 a1) = (op (ab2 b0 b1 b2) (ab2 b2 b3 b2))) :
    Join (ab2 a0 a1 (ab2 a1 a2 a1)) (op (op a0 a1) (ab2 (op b0 (rd b2 b1)) b2 (ab2 b2 b3 b2))) := by
  cases heq
theorem cp_7_root_12 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (op a0 a1) (ab2 a1 a2 a1)) = (op b0 (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2)))) :
    Join (ab2 a0 a1 (ab2 a1 a2 a1)) (ab2 b2 (ab2 b0 b1 b2) (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2))) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  rcases T.ab2.inj he1 with ⟨he2, he3, he4⟩
  clear he1
  revert he0 he2 he3
  subst a1
  intro he0 he2 he3
  revert he0 he2
  subst a2
  intro he0 he2
  clear he2
  have hsize := congrArg sz he0
  have hp_a0 := sz_pos a0
  have hp_b0 := sz_pos b0
  have hp_b1 := sz_pos b1
  have hp_b2 := sz_pos b2
  simp only [sz] at hsize
  omega
theorem cp_7_1_12 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op a0 a1) = (op b0 (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2)))) :
    Join (ab2 a0 a1 (ab2 a1 a2 a1)) (op (ab2 b2 (ab2 b0 b1 b2) (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2))) (ab2 a1 a2 a1)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  subst a0
  exact ⟨(ab2 b0 (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2)) (ab2 (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2)) a2 (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2)))), (Relation.ReflTransGen.refl), ((((Relation.ReflTransGen.refl).tail (root_step .r11 b2 (ab2 b0 b1 b2) (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2)) a2)).tail (Step.c_ab2_1 (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2)) (ab2 (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2)) a2 (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2))) (Step.c_op_2 b2 (root_step .r5 (ab2 b0 b1 b2) b3 (leaf 0) (leaf 0))))).tail (Step.c_ab2_1 (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2)) (ab2 (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2)) a2 (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2))) (root_step .r3 b2 b0 b1 (leaf 0))))⟩
theorem cp_7_2_12 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a1 a2 a1) = (op b0 (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2)))) :
    Join (ab2 a0 a1 (ab2 a1 a2 a1)) (op (op a0 a1) (ab2 b2 (ab2 b0 b1 b2) (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2)))) := by
  cases heq
theorem cp_8_root_0 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (rd (rd a0 a1) a2) a0) = (op (op b0 b1) b1)) :
    Join (ab2 (op a2 (rd a0 a1)) a1 a0) (rd b1 b0) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  cases he0
theorem cp_8_1_0 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd (rd a0 a1) a2) = (op (op b0 b1) b1)) :
    Join (ab2 (op a2 (rd a0 a1)) a1 a0) (op (rd b1 b0) a0) := by
  cases heq
theorem cp_8_11_0 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd a0 a1) = (op (op b0 b1) b1)) :
    Join (ab2 (op a2 (rd a0 a1)) a1 a0) (op (rd (rd b1 b0) a2) a0) := by
  cases heq
theorem cp_8_root_1 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (rd (rd a0 a1) a2) a0) = (op (rd b0 b1) b0)) :
    Join (ab2 (op a2 (rd a0 a1)) a1 a0) (rd b0 (op b1 b0)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  rcases T.rd.inj he0 with ⟨he2, he3⟩
  clear he0
  revert he2
  subst a2
  intro he2
  have hsize := congrArg sz he2
  have hp_a1 := sz_pos a1
  have hp_b0 := sz_pos b0
  simp only [sz] at hsize
  omega
theorem cp_8_1_1 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd (rd a0 a1) a2) = (op (rd b0 b1) b0)) :
    Join (ab2 (op a2 (rd a0 a1)) a1 a0) (op (rd b0 (op b1 b0)) a0) := by
  cases heq
theorem cp_8_11_1 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd a0 a1) = (op (rd b0 b1) b0)) :
    Join (ab2 (op a2 (rd a0 a1)) a1 a0) (op (rd (rd b0 (op b1 b0)) a2) a0) := by
  cases heq
theorem cp_8_root_2 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (rd (rd a0 a1) a2) a0) = (op (op b0 (rd b1 b2)) b1)) :
    Join (ab2 (op a2 (rd a0 a1)) a1 a0) (ab2 b0 b2 b1) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  cases he0
theorem cp_8_1_2 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd (rd a0 a1) a2) = (op (op b0 (rd b1 b2)) b1)) :
    Join (ab2 (op a2 (rd a0 a1)) a1 a0) (op (ab2 b0 b2 b1) a0) := by
  cases heq
theorem cp_8_11_2 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd a0 a1) = (op (op b0 (rd b1 b2)) b1)) :
    Join (ab2 (op a2 (rd a0 a1)) a1 a0) (op (rd (ab2 b0 b2 b1) a2) a0) := by
  cases heq
theorem cp_8_root_3 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (rd (rd a0 a1) a2) a0) = (op b0 (ab2 b1 b2 b0))) :
    Join (ab2 (op a2 (rd a0 a1)) a1 a0) b1 := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  have hsize := congrArg sz he0
  have hp_a1 := sz_pos a1
  have hp_a2 := sz_pos a2
  have hp_b0 := sz_pos b0
  have hp_b1 := sz_pos b1
  have hp_b2 := sz_pos b2
  simp only [sz] at hsize
  omega
theorem cp_8_1_3 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd (rd a0 a1) a2) = (op b0 (ab2 b1 b2 b0))) :
    Join (ab2 (op a2 (rd a0 a1)) a1 a0) (op b1 a0) := by
  cases heq
theorem cp_8_11_3 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd a0 a1) = (op b0 (ab2 b1 b2 b0))) :
    Join (ab2 (op a2 (rd a0 a1)) a1 a0) (op (rd b1 a2) a0) := by
  cases heq
theorem cp_8_root_4 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (rd (rd a0 a1) a2) a0) = (op b0 (ab2 b0 b1 b2))) :
    Join (ab2 (op a2 (rd a0 a1)) a1 a0) (rd (ab2 b0 b1 b2) b2) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  have hsize := congrArg sz he0
  have hp_a1 := sz_pos a1
  have hp_a2 := sz_pos a2
  have hp_b0 := sz_pos b0
  have hp_b1 := sz_pos b1
  have hp_b2 := sz_pos b2
  simp only [sz] at hsize
  omega
theorem cp_8_1_4 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd (rd a0 a1) a2) = (op b0 (ab2 b0 b1 b2))) :
    Join (ab2 (op a2 (rd a0 a1)) a1 a0) (op (rd (ab2 b0 b1 b2) b2) a0) := by
  cases heq
theorem cp_8_11_4 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd a0 a1) = (op b0 (ab2 b0 b1 b2))) :
    Join (ab2 (op a2 (rd a0 a1)) a1 a0) (op (rd (rd (ab2 b0 b1 b2) b2) a2) a0) := by
  cases heq
theorem cp_8_root_5 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (rd (rd a0 a1) a2) a0) = (rd (ab2 b0 b1 b0) b0)) :
    Join (ab2 (op a2 (rd a0 a1)) a1 a0) b0 := by
  cases heq
theorem cp_8_1_5 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd (rd a0 a1) a2) = (rd (ab2 b0 b1 b0) b0)) :
    Join (ab2 (op a2 (rd a0 a1)) a1 a0) (op b0 a0) := by
  rcases T.rd.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a2
  intro he0
  cases he0
theorem cp_8_11_5 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd a0 a1) = (rd (ab2 b0 b1 b0) b0)) :
    Join (ab2 (op a2 (rd a0 a1)) a1 a0) (op (rd b0 a2) a0) := by
  rcases T.rd.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  subst a0
  exact ⟨(ab2 (op a2 b0) b0 (ab2 b0 b1 b0)), ((Relation.ReflTransGen.refl).tail (Step.c_ab2_1 b0 (ab2 b0 b1 b0) (Step.c_op_2 a2 (root_step .r5 b0 b1 (leaf 0) (leaf 0))))), ((Relation.ReflTransGen.refl).tail (root_step .r9 b0 a2 b1 (leaf 0)))⟩
theorem cp_8_root_6 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (rd (rd a0 a1) a2) a0) = (op (ab2 b0 b1 b2) b2)) :
    Join (ab2 (op a2 (rd a0 a1)) a1 a0) (rd b2 (op b0 (rd b2 b1))) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  cases he0
theorem cp_8_1_6 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd (rd a0 a1) a2) = (op (ab2 b0 b1 b2) b2)) :
    Join (ab2 (op a2 (rd a0 a1)) a1 a0) (op (rd b2 (op b0 (rd b2 b1))) a0) := by
  cases heq
theorem cp_8_11_6 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd a0 a1) = (op (ab2 b0 b1 b2) b2)) :
    Join (ab2 (op a2 (rd a0 a1)) a1 a0) (op (rd (rd b2 (op b0 (rd b2 b1))) a2) a0) := by
  cases heq
theorem cp_8_root_7 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (rd (rd a0 a1) a2) a0) = (op (op b0 b1) (ab2 b1 b2 b1))) :
    Join (ab2 (op a2 (rd a0 a1)) a1 a0) (ab2 b0 b1 (ab2 b1 b2 b1)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  cases he0
theorem cp_8_1_7 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd (rd a0 a1) a2) = (op (op b0 b1) (ab2 b1 b2 b1))) :
    Join (ab2 (op a2 (rd a0 a1)) a1 a0) (op (ab2 b0 b1 (ab2 b1 b2 b1)) a0) := by
  cases heq
theorem cp_8_11_7 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd a0 a1) = (op (op b0 b1) (ab2 b1 b2 b1))) :
    Join (ab2 (op a2 (rd a0 a1)) a1 a0) (op (rd (ab2 b0 b1 (ab2 b1 b2 b1)) a2) a0) := by
  cases heq
theorem cp_8_root_8 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (rd (rd a0 a1) a2) a0) = (op (rd (rd b0 b1) b2) b0)) :
    Join (ab2 (op a2 (rd a0 a1)) a1 a0) (ab2 (op b2 (rd b0 b1)) b1 b0) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  rcases T.rd.inj he0 with ⟨he2, he3⟩
  clear he0
  revert he2
  subst a2
  intro he2
  rcases T.rd.inj he2 with ⟨he4, he5⟩
  clear he2
  revert he4
  subst a1
  intro he4
  clear he4
  exact ⟨(ab2 (op b2 (rd b0 b1)) b1 b0), (Relation.ReflTransGen.refl), (Relation.ReflTransGen.refl)⟩
theorem cp_8_1_8 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd (rd a0 a1) a2) = (op (rd (rd b0 b1) b2) b0)) :
    Join (ab2 (op a2 (rd a0 a1)) a1 a0) (op (ab2 (op b2 (rd b0 b1)) b1 b0) a0) := by
  cases heq
theorem cp_8_11_8 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd a0 a1) = (op (rd (rd b0 b1) b2) b0)) :
    Join (ab2 (op a2 (rd a0 a1)) a1 a0) (op (rd (ab2 (op b2 (rd b0 b1)) b1 b0) a2) a0) := by
  cases heq
theorem cp_8_root_9 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (rd (rd a0 a1) a2) a0) = (op (rd b0 b1) (ab2 b0 b2 b0))) :
    Join (ab2 (op a2 (rd a0 a1)) a1 a0) (ab2 (op b1 b0) b0 (ab2 b0 b2 b0)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  rcases T.rd.inj he0 with ⟨he2, he3⟩
  clear he0
  revert he2
  subst a2
  intro he2
  have hsize := congrArg sz he2
  have hp_a1 := sz_pos a1
  have hp_b0 := sz_pos b0
  have hp_b2 := sz_pos b2
  simp only [sz] at hsize
  omega
theorem cp_8_1_9 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd (rd a0 a1) a2) = (op (rd b0 b1) (ab2 b0 b2 b0))) :
    Join (ab2 (op a2 (rd a0 a1)) a1 a0) (op (ab2 (op b1 b0) b0 (ab2 b0 b2 b0)) a0) := by
  cases heq
theorem cp_8_11_9 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd a0 a1) = (op (rd b0 b1) (ab2 b0 b2 b0))) :
    Join (ab2 (op a2 (rd a0 a1)) a1 a0) (op (rd (ab2 (op b1 b0) b0 (ab2 b0 b2 b0)) a2) a0) := by
  cases heq
theorem cp_8_root_10 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (rd (rd a0 a1) a2) a0) = (op (ab2 b0 b1 (rd b2 b3)) b2)) :
    Join (ab2 (op a2 (rd a0 a1)) a1 a0) (ab2 (op b0 (rd (rd b2 b3) b1)) b3 b2) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  cases he0
theorem cp_8_1_10 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd (rd a0 a1) a2) = (op (ab2 b0 b1 (rd b2 b3)) b2)) :
    Join (ab2 (op a2 (rd a0 a1)) a1 a0) (op (ab2 (op b0 (rd (rd b2 b3) b1)) b3 b2) a0) := by
  cases heq
theorem cp_8_11_10 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd a0 a1) = (op (ab2 b0 b1 (rd b2 b3)) b2)) :
    Join (ab2 (op a2 (rd a0 a1)) a1 a0) (op (rd (ab2 (op b0 (rd (rd b2 b3) b1)) b3 b2) a2) a0) := by
  cases heq
theorem cp_8_root_11 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (rd (rd a0 a1) a2) a0) = (op (ab2 b0 b1 b2) (ab2 b2 b3 b2))) :
    Join (ab2 (op a2 (rd a0 a1)) a1 a0) (ab2 (op b0 (rd b2 b1)) b2 (ab2 b2 b3 b2)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  cases he0
theorem cp_8_1_11 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd (rd a0 a1) a2) = (op (ab2 b0 b1 b2) (ab2 b2 b3 b2))) :
    Join (ab2 (op a2 (rd a0 a1)) a1 a0) (op (ab2 (op b0 (rd b2 b1)) b2 (ab2 b2 b3 b2)) a0) := by
  cases heq
theorem cp_8_11_11 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd a0 a1) = (op (ab2 b0 b1 b2) (ab2 b2 b3 b2))) :
    Join (ab2 (op a2 (rd a0 a1)) a1 a0) (op (rd (ab2 (op b0 (rd b2 b1)) b2 (ab2 b2 b3 b2)) a2) a0) := by
  cases heq
theorem cp_8_root_12 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (rd (rd a0 a1) a2) a0) = (op b0 (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2)))) :
    Join (ab2 (op a2 (rd a0 a1)) a1 a0) (ab2 b2 (ab2 b0 b1 b2) (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2))) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a0
  intro he0
  have hsize := congrArg sz he0
  have hp_a1 := sz_pos a1
  have hp_a2 := sz_pos a2
  have hp_b0 := sz_pos b0
  have hp_b1 := sz_pos b1
  have hp_b2 := sz_pos b2
  have hp_b3 := sz_pos b3
  simp only [sz] at hsize
  omega
theorem cp_8_1_12 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd (rd a0 a1) a2) = (op b0 (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2)))) :
    Join (ab2 (op a2 (rd a0 a1)) a1 a0) (op (ab2 b2 (ab2 b0 b1 b2) (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2))) a0) := by
  cases heq
theorem cp_8_11_12 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd a0 a1) = (op b0 (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2)))) :
    Join (ab2 (op a2 (rd a0 a1)) a1 a0) (op (rd (ab2 b2 (ab2 b0 b1 b2) (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2))) a2) a0) := by
  cases heq
theorem cp_9_root_0 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (rd a0 a1) (ab2 a0 a2 a0)) = (op (op b0 b1) b1)) :
    Join (ab2 (op a1 a0) a0 (ab2 a0 a2 a0)) (rd b1 b0) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst b1
  intro he0
  cases he0
theorem cp_9_1_0 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd a0 a1) = (op (op b0 b1) b1)) :
    Join (ab2 (op a1 a0) a0 (ab2 a0 a2 a0)) (op (rd b1 b0) (ab2 a0 a2 a0)) := by
  cases heq
theorem cp_9_2_0 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a2 a0) = (op (op b0 b1) b1)) :
    Join (ab2 (op a1 a0) a0 (ab2 a0 a2 a0)) (op (rd a0 a1) (rd b1 b0)) := by
  cases heq
theorem cp_9_root_1 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (rd a0 a1) (ab2 a0 a2 a0)) = (op (rd b0 b1) b0)) :
    Join (ab2 (op a1 a0) a0 (ab2 a0 a2 a0)) (rd b0 (op b1 b0)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst b0
  intro he0
  rcases T.rd.inj he0 with ⟨he2, he3⟩
  clear he0
  revert he2
  subst a1
  intro he2
  have hsize := congrArg sz he2
  have hp_a0 := sz_pos a0
  have hp_a2 := sz_pos a2
  simp only [sz] at hsize
  omega
theorem cp_9_1_1 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd a0 a1) = (op (rd b0 b1) b0)) :
    Join (ab2 (op a1 a0) a0 (ab2 a0 a2 a0)) (op (rd b0 (op b1 b0)) (ab2 a0 a2 a0)) := by
  cases heq
theorem cp_9_2_1 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a2 a0) = (op (rd b0 b1) b0)) :
    Join (ab2 (op a1 a0) a0 (ab2 a0 a2 a0)) (op (rd a0 a1) (rd b0 (op b1 b0))) := by
  cases heq
theorem cp_9_root_2 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (rd a0 a1) (ab2 a0 a2 a0)) = (op (op b0 (rd b1 b2)) b1)) :
    Join (ab2 (op a1 a0) a0 (ab2 a0 a2 a0)) (ab2 b0 b2 b1) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst b1
  intro he0
  cases he0
theorem cp_9_1_2 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd a0 a1) = (op (op b0 (rd b1 b2)) b1)) :
    Join (ab2 (op a1 a0) a0 (ab2 a0 a2 a0)) (op (ab2 b0 b2 b1) (ab2 a0 a2 a0)) := by
  cases heq
theorem cp_9_2_2 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a2 a0) = (op (op b0 (rd b1 b2)) b1)) :
    Join (ab2 (op a1 a0) a0 (ab2 a0 a2 a0)) (op (rd a0 a1) (ab2 b0 b2 b1)) := by
  cases heq
theorem cp_9_root_3 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (rd a0 a1) (ab2 a0 a2 a0)) = (op b0 (ab2 b1 b2 b0))) :
    Join (ab2 (op a1 a0) a0 (ab2 a0 a2 a0)) b1 := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  rcases T.ab2.inj he1 with ⟨he2, he3, he4⟩
  clear he1
  revert he0 he2 he3
  subst a0
  intro he0 he2 he3
  revert he0 he2
  subst a2
  intro he0 he2
  revert he0
  subst b0
  intro he0
  have hsize := congrArg sz he0
  have hp_a1 := sz_pos a1
  have hp_b1 := sz_pos b1
  simp only [sz] at hsize
  omega
theorem cp_9_1_3 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd a0 a1) = (op b0 (ab2 b1 b2 b0))) :
    Join (ab2 (op a1 a0) a0 (ab2 a0 a2 a0)) (op b1 (ab2 a0 a2 a0)) := by
  cases heq
theorem cp_9_2_3 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a2 a0) = (op b0 (ab2 b1 b2 b0))) :
    Join (ab2 (op a1 a0) a0 (ab2 a0 a2 a0)) (op (rd a0 a1) b1) := by
  cases heq
theorem cp_9_root_4 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (rd a0 a1) (ab2 a0 a2 a0)) = (op b0 (ab2 b0 b1 b2))) :
    Join (ab2 (op a1 a0) a0 (ab2 a0 a2 a0)) (rd (ab2 b0 b1 b2) b2) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  rcases T.ab2.inj he1 with ⟨he2, he3, he4⟩
  clear he1
  revert he0 he2 he3
  subst a0
  intro he0 he2 he3
  revert he0 he2
  subst a2
  intro he0 he2
  revert he0
  subst b2
  intro he0
  have hsize := congrArg sz he0
  have hp_a1 := sz_pos a1
  have hp_b0 := sz_pos b0
  simp only [sz] at hsize
  omega
theorem cp_9_1_4 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd a0 a1) = (op b0 (ab2 b0 b1 b2))) :
    Join (ab2 (op a1 a0) a0 (ab2 a0 a2 a0)) (op (rd (ab2 b0 b1 b2) b2) (ab2 a0 a2 a0)) := by
  cases heq
theorem cp_9_2_4 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a2 a0) = (op b0 (ab2 b0 b1 b2))) :
    Join (ab2 (op a1 a0) a0 (ab2 a0 a2 a0)) (op (rd a0 a1) (rd (ab2 b0 b1 b2) b2)) := by
  cases heq
theorem cp_9_root_5 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (rd a0 a1) (ab2 a0 a2 a0)) = (rd (ab2 b0 b1 b0) b0)) :
    Join (ab2 (op a1 a0) a0 (ab2 a0 a2 a0)) b0 := by
  cases heq
theorem cp_9_1_5 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd a0 a1) = (rd (ab2 b0 b1 b0) b0)) :
    Join (ab2 (op a1 a0) a0 (ab2 a0 a2 a0)) (op b0 (ab2 a0 a2 a0)) := by
  rcases T.rd.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a1
  intro he0
  subst a0
  exact ⟨(ab2 b0 (ab2 b0 b1 b0) (ab2 (ab2 b0 b1 b0) a2 (ab2 b0 b1 b0))), ((Relation.ReflTransGen.refl).tail (Step.c_ab2_1 (ab2 b0 b1 b0) (ab2 (ab2 b0 b1 b0) a2 (ab2 b0 b1 b0)) (root_step .r3 b0 b0 b1 (leaf 0)))), ((Relation.ReflTransGen.refl).tail (root_step .r12 b0 b1 b0 a2))⟩
theorem cp_9_2_5 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a2 a0) = (rd (ab2 b0 b1 b0) b0)) :
    Join (ab2 (op a1 a0) a0 (ab2 a0 a2 a0)) (op (rd a0 a1) b0) := by
  cases heq
theorem cp_9_root_6 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (rd a0 a1) (ab2 a0 a2 a0)) = (op (ab2 b0 b1 b2) b2)) :
    Join (ab2 (op a1 a0) a0 (ab2 a0 a2 a0)) (rd b2 (op b0 (rd b2 b1))) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst b2
  intro he0
  cases he0
theorem cp_9_1_6 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd a0 a1) = (op (ab2 b0 b1 b2) b2)) :
    Join (ab2 (op a1 a0) a0 (ab2 a0 a2 a0)) (op (rd b2 (op b0 (rd b2 b1))) (ab2 a0 a2 a0)) := by
  cases heq
theorem cp_9_2_6 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a2 a0) = (op (ab2 b0 b1 b2) b2)) :
    Join (ab2 (op a1 a0) a0 (ab2 a0 a2 a0)) (op (rd a0 a1) (rd b2 (op b0 (rd b2 b1)))) := by
  cases heq
theorem cp_9_root_7 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (rd a0 a1) (ab2 a0 a2 a0)) = (op (op b0 b1) (ab2 b1 b2 b1))) :
    Join (ab2 (op a1 a0) a0 (ab2 a0 a2 a0)) (ab2 b0 b1 (ab2 b1 b2 b1)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  rcases T.ab2.inj he1 with ⟨he2, he3, he4⟩
  clear he1
  revert he0 he2 he3
  subst a0
  intro he0 he2 he3
  revert he0 he2
  subst a2
  intro he0 he2
  clear he2
  cases he0
theorem cp_9_1_7 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd a0 a1) = (op (op b0 b1) (ab2 b1 b2 b1))) :
    Join (ab2 (op a1 a0) a0 (ab2 a0 a2 a0)) (op (ab2 b0 b1 (ab2 b1 b2 b1)) (ab2 a0 a2 a0)) := by
  cases heq
theorem cp_9_2_7 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a2 a0) = (op (op b0 b1) (ab2 b1 b2 b1))) :
    Join (ab2 (op a1 a0) a0 (ab2 a0 a2 a0)) (op (rd a0 a1) (ab2 b0 b1 (ab2 b1 b2 b1))) := by
  cases heq
theorem cp_9_root_8 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (rd a0 a1) (ab2 a0 a2 a0)) = (op (rd (rd b0 b1) b2) b0)) :
    Join (ab2 (op a1 a0) a0 (ab2 a0 a2 a0)) (ab2 (op b2 (rd b0 b1)) b1 b0) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst b0
  intro he0
  rcases T.rd.inj he0 with ⟨he2, he3⟩
  clear he0
  revert he2
  subst a1
  intro he2
  have hsize := congrArg sz he2
  have hp_a0 := sz_pos a0
  have hp_a2 := sz_pos a2
  have hp_b1 := sz_pos b1
  simp only [sz] at hsize
  omega
theorem cp_9_1_8 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd a0 a1) = (op (rd (rd b0 b1) b2) b0)) :
    Join (ab2 (op a1 a0) a0 (ab2 a0 a2 a0)) (op (ab2 (op b2 (rd b0 b1)) b1 b0) (ab2 a0 a2 a0)) := by
  cases heq
theorem cp_9_2_8 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a2 a0) = (op (rd (rd b0 b1) b2) b0)) :
    Join (ab2 (op a1 a0) a0 (ab2 a0 a2 a0)) (op (rd a0 a1) (ab2 (op b2 (rd b0 b1)) b1 b0)) := by
  cases heq
theorem cp_9_root_9 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (rd a0 a1) (ab2 a0 a2 a0)) = (op (rd b0 b1) (ab2 b0 b2 b0))) :
    Join (ab2 (op a1 a0) a0 (ab2 a0 a2 a0)) (ab2 (op b1 b0) b0 (ab2 b0 b2 b0)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  rcases T.ab2.inj he1 with ⟨he2, he3, he4⟩
  clear he1
  revert he0 he2 he3
  subst a0
  intro he0 he2 he3
  revert he0 he2
  subst a2
  intro he0 he2
  clear he2
  rcases T.rd.inj he0 with ⟨he5, he6⟩
  clear he0
  revert he5
  subst a1
  intro he5
  clear he5
  exact ⟨(ab2 (op b1 b0) b0 (ab2 b0 b2 b0)), (Relation.ReflTransGen.refl), (Relation.ReflTransGen.refl)⟩
theorem cp_9_1_9 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd a0 a1) = (op (rd b0 b1) (ab2 b0 b2 b0))) :
    Join (ab2 (op a1 a0) a0 (ab2 a0 a2 a0)) (op (ab2 (op b1 b0) b0 (ab2 b0 b2 b0)) (ab2 a0 a2 a0)) := by
  cases heq
theorem cp_9_2_9 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a2 a0) = (op (rd b0 b1) (ab2 b0 b2 b0))) :
    Join (ab2 (op a1 a0) a0 (ab2 a0 a2 a0)) (op (rd a0 a1) (ab2 (op b1 b0) b0 (ab2 b0 b2 b0))) := by
  cases heq
theorem cp_9_root_10 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (rd a0 a1) (ab2 a0 a2 a0)) = (op (ab2 b0 b1 (rd b2 b3)) b2)) :
    Join (ab2 (op a1 a0) a0 (ab2 a0 a2 a0)) (ab2 (op b0 (rd (rd b2 b3) b1)) b3 b2) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst b2
  intro he0
  cases he0
theorem cp_9_1_10 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd a0 a1) = (op (ab2 b0 b1 (rd b2 b3)) b2)) :
    Join (ab2 (op a1 a0) a0 (ab2 a0 a2 a0)) (op (ab2 (op b0 (rd (rd b2 b3) b1)) b3 b2) (ab2 a0 a2 a0)) := by
  cases heq
theorem cp_9_2_10 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a2 a0) = (op (ab2 b0 b1 (rd b2 b3)) b2)) :
    Join (ab2 (op a1 a0) a0 (ab2 a0 a2 a0)) (op (rd a0 a1) (ab2 (op b0 (rd (rd b2 b3) b1)) b3 b2)) := by
  cases heq
theorem cp_9_root_11 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (rd a0 a1) (ab2 a0 a2 a0)) = (op (ab2 b0 b1 b2) (ab2 b2 b3 b2))) :
    Join (ab2 (op a1 a0) a0 (ab2 a0 a2 a0)) (ab2 (op b0 (rd b2 b1)) b2 (ab2 b2 b3 b2)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  rcases T.ab2.inj he1 with ⟨he2, he3, he4⟩
  clear he1
  revert he0 he2 he3
  subst a0
  intro he0 he2 he3
  revert he0 he2
  subst a2
  intro he0 he2
  clear he2
  cases he0
theorem cp_9_1_11 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd a0 a1) = (op (ab2 b0 b1 b2) (ab2 b2 b3 b2))) :
    Join (ab2 (op a1 a0) a0 (ab2 a0 a2 a0)) (op (ab2 (op b0 (rd b2 b1)) b2 (ab2 b2 b3 b2)) (ab2 a0 a2 a0)) := by
  cases heq
theorem cp_9_2_11 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a2 a0) = (op (ab2 b0 b1 b2) (ab2 b2 b3 b2))) :
    Join (ab2 (op a1 a0) a0 (ab2 a0 a2 a0)) (op (rd a0 a1) (ab2 (op b0 (rd b2 b1)) b2 (ab2 b2 b3 b2))) := by
  cases heq
theorem cp_9_root_12 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (rd a0 a1) (ab2 a0 a2 a0)) = (op b0 (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2)))) :
    Join (ab2 (op a1 a0) a0 (ab2 a0 a2 a0)) (ab2 b2 (ab2 b0 b1 b2) (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2))) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  rcases T.ab2.inj he1 with ⟨he2, he3, he4⟩
  clear he1
  revert he0 he2 he3
  subst a0
  intro he0 he2 he3
  revert he0 he2
  subst a2
  intro he0 he2
  clear he2
  have hsize := congrArg sz he0
  have hp_a1 := sz_pos a1
  have hp_b0 := sz_pos b0
  have hp_b1 := sz_pos b1
  have hp_b2 := sz_pos b2
  simp only [sz] at hsize
  omega
theorem cp_9_1_12 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd a0 a1) = (op b0 (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2)))) :
    Join (ab2 (op a1 a0) a0 (ab2 a0 a2 a0)) (op (ab2 b2 (ab2 b0 b1 b2) (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2))) (ab2 a0 a2 a0)) := by
  cases heq
theorem cp_9_2_12 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a2 a0) = (op b0 (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2)))) :
    Join (ab2 (op a1 a0) a0 (ab2 a0 a2 a0)) (op (rd a0 a1) (ab2 b2 (ab2 b0 b1 b2) (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2)))) := by
  cases heq
theorem cp_10_root_0 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (ab2 a0 a1 (rd a2 a3)) a2) = (op (op b0 b1) b1)) :
    Join (ab2 (op a0 (rd (rd a2 a3) a1)) a3 a2) (rd b1 b0) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a2
  intro he0
  cases he0
theorem cp_10_1_0 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 (rd a2 a3)) = (op (op b0 b1) b1)) :
    Join (ab2 (op a0 (rd (rd a2 a3) a1)) a3 a2) (op (rd b1 b0) a2) := by
  cases heq
theorem cp_10_13_0 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd a2 a3) = (op (op b0 b1) b1)) :
    Join (ab2 (op a0 (rd (rd a2 a3) a1)) a3 a2) (op (ab2 a0 a1 (rd b1 b0)) a2) := by
  cases heq
theorem cp_10_root_1 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (ab2 a0 a1 (rd a2 a3)) a2) = (op (rd b0 b1) b0)) :
    Join (ab2 (op a0 (rd (rd a2 a3) a1)) a3 a2) (rd b0 (op b1 b0)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a2
  intro he0
  cases he0
theorem cp_10_1_1 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 (rd a2 a3)) = (op (rd b0 b1) b0)) :
    Join (ab2 (op a0 (rd (rd a2 a3) a1)) a3 a2) (op (rd b0 (op b1 b0)) a2) := by
  cases heq
theorem cp_10_13_1 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd a2 a3) = (op (rd b0 b1) b0)) :
    Join (ab2 (op a0 (rd (rd a2 a3) a1)) a3 a2) (op (ab2 a0 a1 (rd b0 (op b1 b0))) a2) := by
  cases heq
theorem cp_10_root_2 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (ab2 a0 a1 (rd a2 a3)) a2) = (op (op b0 (rd b1 b2)) b1)) :
    Join (ab2 (op a0 (rd (rd a2 a3) a1)) a3 a2) (ab2 b0 b2 b1) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a2
  intro he0
  cases he0
theorem cp_10_1_2 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 (rd a2 a3)) = (op (op b0 (rd b1 b2)) b1)) :
    Join (ab2 (op a0 (rd (rd a2 a3) a1)) a3 a2) (op (ab2 b0 b2 b1) a2) := by
  cases heq
theorem cp_10_13_2 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd a2 a3) = (op (op b0 (rd b1 b2)) b1)) :
    Join (ab2 (op a0 (rd (rd a2 a3) a1)) a3 a2) (op (ab2 a0 a1 (ab2 b0 b2 b1)) a2) := by
  cases heq
theorem cp_10_root_3 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (ab2 a0 a1 (rd a2 a3)) a2) = (op b0 (ab2 b1 b2 b0))) :
    Join (ab2 (op a0 (rd (rd a2 a3) a1)) a3 a2) b1 := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a2
  intro he0
  have hsize := congrArg sz he0
  have hp_a0 := sz_pos a0
  have hp_a1 := sz_pos a1
  have hp_a3 := sz_pos a3
  have hp_b0 := sz_pos b0
  have hp_b1 := sz_pos b1
  have hp_b2 := sz_pos b2
  simp only [sz] at hsize
  omega
theorem cp_10_1_3 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 (rd a2 a3)) = (op b0 (ab2 b1 b2 b0))) :
    Join (ab2 (op a0 (rd (rd a2 a3) a1)) a3 a2) (op b1 a2) := by
  cases heq
theorem cp_10_13_3 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd a2 a3) = (op b0 (ab2 b1 b2 b0))) :
    Join (ab2 (op a0 (rd (rd a2 a3) a1)) a3 a2) (op (ab2 a0 a1 b1) a2) := by
  cases heq
theorem cp_10_root_4 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (ab2 a0 a1 (rd a2 a3)) a2) = (op b0 (ab2 b0 b1 b2))) :
    Join (ab2 (op a0 (rd (rd a2 a3) a1)) a3 a2) (rd (ab2 b0 b1 b2) b2) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a2
  intro he0
  have hsize := congrArg sz he0
  have hp_a0 := sz_pos a0
  have hp_a1 := sz_pos a1
  have hp_a3 := sz_pos a3
  have hp_b0 := sz_pos b0
  have hp_b1 := sz_pos b1
  have hp_b2 := sz_pos b2
  simp only [sz] at hsize
  omega
theorem cp_10_1_4 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 (rd a2 a3)) = (op b0 (ab2 b0 b1 b2))) :
    Join (ab2 (op a0 (rd (rd a2 a3) a1)) a3 a2) (op (rd (ab2 b0 b1 b2) b2) a2) := by
  cases heq
theorem cp_10_13_4 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd a2 a3) = (op b0 (ab2 b0 b1 b2))) :
    Join (ab2 (op a0 (rd (rd a2 a3) a1)) a3 a2) (op (ab2 a0 a1 (rd (ab2 b0 b1 b2) b2)) a2) := by
  cases heq
theorem cp_10_root_5 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (ab2 a0 a1 (rd a2 a3)) a2) = (rd (ab2 b0 b1 b0) b0)) :
    Join (ab2 (op a0 (rd (rd a2 a3) a1)) a3 a2) b0 := by
  cases heq
theorem cp_10_1_5 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 (rd a2 a3)) = (rd (ab2 b0 b1 b0) b0)) :
    Join (ab2 (op a0 (rd (rd a2 a3) a1)) a3 a2) (op b0 a2) := by
  cases heq
theorem cp_10_13_5 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd a2 a3) = (rd (ab2 b0 b1 b0) b0)) :
    Join (ab2 (op a0 (rd (rd a2 a3) a1)) a3 a2) (op (ab2 a0 a1 b0) a2) := by
  rcases T.rd.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a3
  intro he0
  subst a2
  exact ⟨(ab2 (op a0 (rd b0 a1)) b0 (ab2 b0 b1 b0)), ((Relation.ReflTransGen.refl).tail (Step.c_ab2_1 b0 (ab2 b0 b1 b0) (Step.c_op_2 a0 (Step.c_rd_1 a1 (root_step .r5 b0 b1 (leaf 0) (leaf 0)))))), ((Relation.ReflTransGen.refl).tail (root_step .r11 a0 a1 b0 b1))⟩
theorem cp_10_root_6 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (ab2 a0 a1 (rd a2 a3)) a2) = (op (ab2 b0 b1 b2) b2)) :
    Join (ab2 (op a0 (rd (rd a2 a3) a1)) a3 a2) (rd b2 (op b0 (rd b2 b1))) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a2
  intro he0
  rcases T.ab2.inj he0 with ⟨he2, he3, he4⟩
  clear he0
  have hsize := congrArg sz he4
  have hp_a3 := sz_pos a3
  have hp_b2 := sz_pos b2
  simp only [sz] at hsize
  omega
theorem cp_10_1_6 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 (rd a2 a3)) = (op (ab2 b0 b1 b2) b2)) :
    Join (ab2 (op a0 (rd (rd a2 a3) a1)) a3 a2) (op (rd b2 (op b0 (rd b2 b1))) a2) := by
  cases heq
theorem cp_10_13_6 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd a2 a3) = (op (ab2 b0 b1 b2) b2)) :
    Join (ab2 (op a0 (rd (rd a2 a3) a1)) a3 a2) (op (ab2 a0 a1 (rd b2 (op b0 (rd b2 b1)))) a2) := by
  cases heq
theorem cp_10_root_7 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (ab2 a0 a1 (rd a2 a3)) a2) = (op (op b0 b1) (ab2 b1 b2 b1))) :
    Join (ab2 (op a0 (rd (rd a2 a3) a1)) a3 a2) (ab2 b0 b1 (ab2 b1 b2 b1)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a2
  intro he0
  cases he0
theorem cp_10_1_7 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 (rd a2 a3)) = (op (op b0 b1) (ab2 b1 b2 b1))) :
    Join (ab2 (op a0 (rd (rd a2 a3) a1)) a3 a2) (op (ab2 b0 b1 (ab2 b1 b2 b1)) a2) := by
  cases heq
theorem cp_10_13_7 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd a2 a3) = (op (op b0 b1) (ab2 b1 b2 b1))) :
    Join (ab2 (op a0 (rd (rd a2 a3) a1)) a3 a2) (op (ab2 a0 a1 (ab2 b0 b1 (ab2 b1 b2 b1))) a2) := by
  cases heq
theorem cp_10_root_8 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (ab2 a0 a1 (rd a2 a3)) a2) = (op (rd (rd b0 b1) b2) b0)) :
    Join (ab2 (op a0 (rd (rd a2 a3) a1)) a3 a2) (ab2 (op b2 (rd b0 b1)) b1 b0) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a2
  intro he0
  cases he0
theorem cp_10_1_8 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 (rd a2 a3)) = (op (rd (rd b0 b1) b2) b0)) :
    Join (ab2 (op a0 (rd (rd a2 a3) a1)) a3 a2) (op (ab2 (op b2 (rd b0 b1)) b1 b0) a2) := by
  cases heq
theorem cp_10_13_8 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd a2 a3) = (op (rd (rd b0 b1) b2) b0)) :
    Join (ab2 (op a0 (rd (rd a2 a3) a1)) a3 a2) (op (ab2 a0 a1 (ab2 (op b2 (rd b0 b1)) b1 b0)) a2) := by
  cases heq
theorem cp_10_root_9 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (ab2 a0 a1 (rd a2 a3)) a2) = (op (rd b0 b1) (ab2 b0 b2 b0))) :
    Join (ab2 (op a0 (rd (rd a2 a3) a1)) a3 a2) (ab2 (op b1 b0) b0 (ab2 b0 b2 b0)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a2
  intro he0
  cases he0
theorem cp_10_1_9 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 (rd a2 a3)) = (op (rd b0 b1) (ab2 b0 b2 b0))) :
    Join (ab2 (op a0 (rd (rd a2 a3) a1)) a3 a2) (op (ab2 (op b1 b0) b0 (ab2 b0 b2 b0)) a2) := by
  cases heq
theorem cp_10_13_9 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd a2 a3) = (op (rd b0 b1) (ab2 b0 b2 b0))) :
    Join (ab2 (op a0 (rd (rd a2 a3) a1)) a3 a2) (op (ab2 a0 a1 (ab2 (op b1 b0) b0 (ab2 b0 b2 b0))) a2) := by
  cases heq
theorem cp_10_root_10 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (ab2 a0 a1 (rd a2 a3)) a2) = (op (ab2 b0 b1 (rd b2 b3)) b2)) :
    Join (ab2 (op a0 (rd (rd a2 a3) a1)) a3 a2) (ab2 (op b0 (rd (rd b2 b3) b1)) b3 b2) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a2
  intro he0
  rcases T.ab2.inj he0 with ⟨he2, he3, he4⟩
  clear he0
  rcases T.rd.inj he4 with ⟨he5, he6⟩
  clear he4
  revert he2 he3 he5
  subst a3
  intro he2 he3 he5
  clear he5
  revert he2
  subst a1
  intro he2
  subst a0
  exact ⟨(ab2 (op b0 (rd (rd b2 b3) b1)) b3 b2), (Relation.ReflTransGen.refl), (Relation.ReflTransGen.refl)⟩
theorem cp_10_1_10 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 (rd a2 a3)) = (op (ab2 b0 b1 (rd b2 b3)) b2)) :
    Join (ab2 (op a0 (rd (rd a2 a3) a1)) a3 a2) (op (ab2 (op b0 (rd (rd b2 b3) b1)) b3 b2) a2) := by
  cases heq
theorem cp_10_13_10 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd a2 a3) = (op (ab2 b0 b1 (rd b2 b3)) b2)) :
    Join (ab2 (op a0 (rd (rd a2 a3) a1)) a3 a2) (op (ab2 a0 a1 (ab2 (op b0 (rd (rd b2 b3) b1)) b3 b2)) a2) := by
  cases heq
theorem cp_10_root_11 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (ab2 a0 a1 (rd a2 a3)) a2) = (op (ab2 b0 b1 b2) (ab2 b2 b3 b2))) :
    Join (ab2 (op a0 (rd (rd a2 a3) a1)) a3 a2) (ab2 (op b0 (rd b2 b1)) b2 (ab2 b2 b3 b2)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a2
  intro he0
  rcases T.ab2.inj he0 with ⟨he2, he3, he4⟩
  clear he0
  have hsize := congrArg sz he4
  have hp_a3 := sz_pos a3
  have hp_b2 := sz_pos b2
  have hp_b3 := sz_pos b3
  simp only [sz] at hsize
  omega
theorem cp_10_1_11 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 (rd a2 a3)) = (op (ab2 b0 b1 b2) (ab2 b2 b3 b2))) :
    Join (ab2 (op a0 (rd (rd a2 a3) a1)) a3 a2) (op (ab2 (op b0 (rd b2 b1)) b2 (ab2 b2 b3 b2)) a2) := by
  cases heq
theorem cp_10_13_11 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd a2 a3) = (op (ab2 b0 b1 b2) (ab2 b2 b3 b2))) :
    Join (ab2 (op a0 (rd (rd a2 a3) a1)) a3 a2) (op (ab2 a0 a1 (ab2 (op b0 (rd b2 b1)) b2 (ab2 b2 b3 b2))) a2) := by
  cases heq
theorem cp_10_root_12 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (ab2 a0 a1 (rd a2 a3)) a2) = (op b0 (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2)))) :
    Join (ab2 (op a0 (rd (rd a2 a3) a1)) a3 a2) (ab2 b2 (ab2 b0 b1 b2) (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2))) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst a2
  intro he0
  have hsize := congrArg sz he0
  have hp_a0 := sz_pos a0
  have hp_a1 := sz_pos a1
  have hp_a3 := sz_pos a3
  have hp_b0 := sz_pos b0
  have hp_b1 := sz_pos b1
  have hp_b2 := sz_pos b2
  have hp_b3 := sz_pos b3
  simp only [sz] at hsize
  omega
theorem cp_10_1_12 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 (rd a2 a3)) = (op b0 (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2)))) :
    Join (ab2 (op a0 (rd (rd a2 a3) a1)) a3 a2) (op (ab2 b2 (ab2 b0 b1 b2) (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2))) a2) := by
  cases heq
theorem cp_10_13_12 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (rd a2 a3) = (op b0 (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2)))) :
    Join (ab2 (op a0 (rd (rd a2 a3) a1)) a3 a2) (op (ab2 a0 a1 (ab2 b2 (ab2 b0 b1 b2) (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2)))) a2) := by
  cases heq
theorem cp_11_root_0 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (ab2 a0 a1 a2) (ab2 a2 a3 a2)) = (op (op b0 b1) b1)) :
    Join (ab2 (op a0 (rd a2 a1)) a2 (ab2 a2 a3 a2)) (rd b1 b0) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst b1
  intro he0
  cases he0
theorem cp_11_1_0 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 a2) = (op (op b0 b1) b1)) :
    Join (ab2 (op a0 (rd a2 a1)) a2 (ab2 a2 a3 a2)) (op (rd b1 b0) (ab2 a2 a3 a2)) := by
  cases heq
theorem cp_11_2_0 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a2 a3 a2) = (op (op b0 b1) b1)) :
    Join (ab2 (op a0 (rd a2 a1)) a2 (ab2 a2 a3 a2)) (op (ab2 a0 a1 a2) (rd b1 b0)) := by
  cases heq
theorem cp_11_root_1 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (ab2 a0 a1 a2) (ab2 a2 a3 a2)) = (op (rd b0 b1) b0)) :
    Join (ab2 (op a0 (rd a2 a1)) a2 (ab2 a2 a3 a2)) (rd b0 (op b1 b0)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst b0
  intro he0
  cases he0
theorem cp_11_1_1 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 a2) = (op (rd b0 b1) b0)) :
    Join (ab2 (op a0 (rd a2 a1)) a2 (ab2 a2 a3 a2)) (op (rd b0 (op b1 b0)) (ab2 a2 a3 a2)) := by
  cases heq
theorem cp_11_2_1 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a2 a3 a2) = (op (rd b0 b1) b0)) :
    Join (ab2 (op a0 (rd a2 a1)) a2 (ab2 a2 a3 a2)) (op (ab2 a0 a1 a2) (rd b0 (op b1 b0))) := by
  cases heq
theorem cp_11_root_2 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (ab2 a0 a1 a2) (ab2 a2 a3 a2)) = (op (op b0 (rd b1 b2)) b1)) :
    Join (ab2 (op a0 (rd a2 a1)) a2 (ab2 a2 a3 a2)) (ab2 b0 b2 b1) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst b1
  intro he0
  cases he0
theorem cp_11_1_2 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 a2) = (op (op b0 (rd b1 b2)) b1)) :
    Join (ab2 (op a0 (rd a2 a1)) a2 (ab2 a2 a3 a2)) (op (ab2 b0 b2 b1) (ab2 a2 a3 a2)) := by
  cases heq
theorem cp_11_2_2 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a2 a3 a2) = (op (op b0 (rd b1 b2)) b1)) :
    Join (ab2 (op a0 (rd a2 a1)) a2 (ab2 a2 a3 a2)) (op (ab2 a0 a1 a2) (ab2 b0 b2 b1)) := by
  cases heq
theorem cp_11_root_3 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (ab2 a0 a1 a2) (ab2 a2 a3 a2)) = (op b0 (ab2 b1 b2 b0))) :
    Join (ab2 (op a0 (rd a2 a1)) a2 (ab2 a2 a3 a2)) b1 := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  rcases T.ab2.inj he1 with ⟨he2, he3, he4⟩
  clear he1
  revert he0 he2 he3
  subst a2
  intro he0 he2 he3
  revert he0 he2
  subst a3
  intro he0 he2
  revert he0
  subst b0
  intro he0
  have hsize := congrArg sz he0
  have hp_a0 := sz_pos a0
  have hp_a1 := sz_pos a1
  have hp_b1 := sz_pos b1
  simp only [sz] at hsize
  omega
theorem cp_11_1_3 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 a2) = (op b0 (ab2 b1 b2 b0))) :
    Join (ab2 (op a0 (rd a2 a1)) a2 (ab2 a2 a3 a2)) (op b1 (ab2 a2 a3 a2)) := by
  cases heq
theorem cp_11_2_3 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a2 a3 a2) = (op b0 (ab2 b1 b2 b0))) :
    Join (ab2 (op a0 (rd a2 a1)) a2 (ab2 a2 a3 a2)) (op (ab2 a0 a1 a2) b1) := by
  cases heq
theorem cp_11_root_4 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (ab2 a0 a1 a2) (ab2 a2 a3 a2)) = (op b0 (ab2 b0 b1 b2))) :
    Join (ab2 (op a0 (rd a2 a1)) a2 (ab2 a2 a3 a2)) (rd (ab2 b0 b1 b2) b2) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  rcases T.ab2.inj he1 with ⟨he2, he3, he4⟩
  clear he1
  revert he0 he2 he3
  subst a2
  intro he0 he2 he3
  revert he0 he2
  subst a3
  intro he0 he2
  revert he0
  subst b2
  intro he0
  have hsize := congrArg sz he0
  have hp_a0 := sz_pos a0
  have hp_a1 := sz_pos a1
  have hp_b0 := sz_pos b0
  simp only [sz] at hsize
  omega
theorem cp_11_1_4 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 a2) = (op b0 (ab2 b0 b1 b2))) :
    Join (ab2 (op a0 (rd a2 a1)) a2 (ab2 a2 a3 a2)) (op (rd (ab2 b0 b1 b2) b2) (ab2 a2 a3 a2)) := by
  cases heq
theorem cp_11_2_4 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a2 a3 a2) = (op b0 (ab2 b0 b1 b2))) :
    Join (ab2 (op a0 (rd a2 a1)) a2 (ab2 a2 a3 a2)) (op (ab2 a0 a1 a2) (rd (ab2 b0 b1 b2) b2)) := by
  cases heq
theorem cp_11_root_5 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (ab2 a0 a1 a2) (ab2 a2 a3 a2)) = (rd (ab2 b0 b1 b0) b0)) :
    Join (ab2 (op a0 (rd a2 a1)) a2 (ab2 a2 a3 a2)) b0 := by
  cases heq
theorem cp_11_1_5 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 a2) = (rd (ab2 b0 b1 b0) b0)) :
    Join (ab2 (op a0 (rd a2 a1)) a2 (ab2 a2 a3 a2)) (op b0 (ab2 a2 a3 a2)) := by
  cases heq
theorem cp_11_2_5 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a2 a3 a2) = (rd (ab2 b0 b1 b0) b0)) :
    Join (ab2 (op a0 (rd a2 a1)) a2 (ab2 a2 a3 a2)) (op (ab2 a0 a1 a2) b0) := by
  cases heq
theorem cp_11_root_6 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (ab2 a0 a1 a2) (ab2 a2 a3 a2)) = (op (ab2 b0 b1 b2) b2)) :
    Join (ab2 (op a0 (rd a2 a1)) a2 (ab2 a2 a3 a2)) (rd b2 (op b0 (rd b2 b1))) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst b2
  intro he0
  rcases T.ab2.inj he0 with ⟨he2, he3, he4⟩
  clear he0
  have hsize := congrArg sz he4
  have hp_a2 := sz_pos a2
  have hp_a3 := sz_pos a3
  simp only [sz] at hsize
  omega
theorem cp_11_1_6 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 a2) = (op (ab2 b0 b1 b2) b2)) :
    Join (ab2 (op a0 (rd a2 a1)) a2 (ab2 a2 a3 a2)) (op (rd b2 (op b0 (rd b2 b1))) (ab2 a2 a3 a2)) := by
  cases heq
theorem cp_11_2_6 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a2 a3 a2) = (op (ab2 b0 b1 b2) b2)) :
    Join (ab2 (op a0 (rd a2 a1)) a2 (ab2 a2 a3 a2)) (op (ab2 a0 a1 a2) (rd b2 (op b0 (rd b2 b1)))) := by
  cases heq
theorem cp_11_root_7 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (ab2 a0 a1 a2) (ab2 a2 a3 a2)) = (op (op b0 b1) (ab2 b1 b2 b1))) :
    Join (ab2 (op a0 (rd a2 a1)) a2 (ab2 a2 a3 a2)) (ab2 b0 b1 (ab2 b1 b2 b1)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  rcases T.ab2.inj he1 with ⟨he2, he3, he4⟩
  clear he1
  revert he0 he2 he3
  subst a2
  intro he0 he2 he3
  revert he0 he2
  subst a3
  intro he0 he2
  clear he2
  cases he0
theorem cp_11_1_7 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 a2) = (op (op b0 b1) (ab2 b1 b2 b1))) :
    Join (ab2 (op a0 (rd a2 a1)) a2 (ab2 a2 a3 a2)) (op (ab2 b0 b1 (ab2 b1 b2 b1)) (ab2 a2 a3 a2)) := by
  cases heq
theorem cp_11_2_7 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a2 a3 a2) = (op (op b0 b1) (ab2 b1 b2 b1))) :
    Join (ab2 (op a0 (rd a2 a1)) a2 (ab2 a2 a3 a2)) (op (ab2 a0 a1 a2) (ab2 b0 b1 (ab2 b1 b2 b1))) := by
  cases heq
theorem cp_11_root_8 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (ab2 a0 a1 a2) (ab2 a2 a3 a2)) = (op (rd (rd b0 b1) b2) b0)) :
    Join (ab2 (op a0 (rd a2 a1)) a2 (ab2 a2 a3 a2)) (ab2 (op b2 (rd b0 b1)) b1 b0) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst b0
  intro he0
  cases he0
theorem cp_11_1_8 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 a2) = (op (rd (rd b0 b1) b2) b0)) :
    Join (ab2 (op a0 (rd a2 a1)) a2 (ab2 a2 a3 a2)) (op (ab2 (op b2 (rd b0 b1)) b1 b0) (ab2 a2 a3 a2)) := by
  cases heq
theorem cp_11_2_8 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a2 a3 a2) = (op (rd (rd b0 b1) b2) b0)) :
    Join (ab2 (op a0 (rd a2 a1)) a2 (ab2 a2 a3 a2)) (op (ab2 a0 a1 a2) (ab2 (op b2 (rd b0 b1)) b1 b0)) := by
  cases heq
theorem cp_11_root_9 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (ab2 a0 a1 a2) (ab2 a2 a3 a2)) = (op (rd b0 b1) (ab2 b0 b2 b0))) :
    Join (ab2 (op a0 (rd a2 a1)) a2 (ab2 a2 a3 a2)) (ab2 (op b1 b0) b0 (ab2 b0 b2 b0)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  rcases T.ab2.inj he1 with ⟨he2, he3, he4⟩
  clear he1
  revert he0 he2 he3
  subst a2
  intro he0 he2 he3
  revert he0 he2
  subst a3
  intro he0 he2
  clear he2
  cases he0
theorem cp_11_1_9 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 a2) = (op (rd b0 b1) (ab2 b0 b2 b0))) :
    Join (ab2 (op a0 (rd a2 a1)) a2 (ab2 a2 a3 a2)) (op (ab2 (op b1 b0) b0 (ab2 b0 b2 b0)) (ab2 a2 a3 a2)) := by
  cases heq
theorem cp_11_2_9 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a2 a3 a2) = (op (rd b0 b1) (ab2 b0 b2 b0))) :
    Join (ab2 (op a0 (rd a2 a1)) a2 (ab2 a2 a3 a2)) (op (ab2 a0 a1 a2) (ab2 (op b1 b0) b0 (ab2 b0 b2 b0))) := by
  cases heq
theorem cp_11_root_10 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (ab2 a0 a1 a2) (ab2 a2 a3 a2)) = (op (ab2 b0 b1 (rd b2 b3)) b2)) :
    Join (ab2 (op a0 (rd a2 a1)) a2 (ab2 a2 a3 a2)) (ab2 (op b0 (rd (rd b2 b3) b1)) b3 b2) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst b2
  intro he0
  rcases T.ab2.inj he0 with ⟨he2, he3, he4⟩
  clear he0
  have hsize := congrArg sz he4
  have hp_a2 := sz_pos a2
  have hp_a3 := sz_pos a3
  have hp_b3 := sz_pos b3
  simp only [sz] at hsize
  omega
theorem cp_11_1_10 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 a2) = (op (ab2 b0 b1 (rd b2 b3)) b2)) :
    Join (ab2 (op a0 (rd a2 a1)) a2 (ab2 a2 a3 a2)) (op (ab2 (op b0 (rd (rd b2 b3) b1)) b3 b2) (ab2 a2 a3 a2)) := by
  cases heq
theorem cp_11_2_10 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a2 a3 a2) = (op (ab2 b0 b1 (rd b2 b3)) b2)) :
    Join (ab2 (op a0 (rd a2 a1)) a2 (ab2 a2 a3 a2)) (op (ab2 a0 a1 a2) (ab2 (op b0 (rd (rd b2 b3) b1)) b3 b2)) := by
  cases heq
theorem cp_11_root_11 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (ab2 a0 a1 a2) (ab2 a2 a3 a2)) = (op (ab2 b0 b1 b2) (ab2 b2 b3 b2))) :
    Join (ab2 (op a0 (rd a2 a1)) a2 (ab2 a2 a3 a2)) (ab2 (op b0 (rd b2 b1)) b2 (ab2 b2 b3 b2)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  rcases T.ab2.inj he1 with ⟨he2, he3, he4⟩
  clear he1
  revert he0 he2 he3
  subst a2
  intro he0 he2 he3
  revert he0 he2
  subst a3
  intro he0 he2
  clear he2
  rcases T.ab2.inj he0 with ⟨he5, he6, he7⟩
  clear he0
  clear he7
  revert he5
  subst a1
  intro he5
  subst a0
  exact ⟨(ab2 (op b0 (rd b2 b1)) b2 (ab2 b2 b3 b2)), (Relation.ReflTransGen.refl), (Relation.ReflTransGen.refl)⟩
theorem cp_11_1_11 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 a2) = (op (ab2 b0 b1 b2) (ab2 b2 b3 b2))) :
    Join (ab2 (op a0 (rd a2 a1)) a2 (ab2 a2 a3 a2)) (op (ab2 (op b0 (rd b2 b1)) b2 (ab2 b2 b3 b2)) (ab2 a2 a3 a2)) := by
  cases heq
theorem cp_11_2_11 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a2 a3 a2) = (op (ab2 b0 b1 b2) (ab2 b2 b3 b2))) :
    Join (ab2 (op a0 (rd a2 a1)) a2 (ab2 a2 a3 a2)) (op (ab2 a0 a1 a2) (ab2 (op b0 (rd b2 b1)) b2 (ab2 b2 b3 b2))) := by
  cases heq
theorem cp_11_root_12 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op (ab2 a0 a1 a2) (ab2 a2 a3 a2)) = (op b0 (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2)))) :
    Join (ab2 (op a0 (rd a2 a1)) a2 (ab2 a2 a3 a2)) (ab2 b2 (ab2 b0 b1 b2) (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2))) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  rcases T.ab2.inj he1 with ⟨he2, he3, he4⟩
  clear he1
  revert he0 he2 he3
  subst a2
  intro he0 he2 he3
  revert he0 he2
  subst a3
  intro he0 he2
  clear he2
  have hsize := congrArg sz he0
  have hp_a0 := sz_pos a0
  have hp_a1 := sz_pos a1
  have hp_b0 := sz_pos b0
  have hp_b1 := sz_pos b1
  have hp_b2 := sz_pos b2
  simp only [sz] at hsize
  omega
theorem cp_11_1_12 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 a2) = (op b0 (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2)))) :
    Join (ab2 (op a0 (rd a2 a1)) a2 (ab2 a2 a3 a2)) (op (ab2 b2 (ab2 b0 b1 b2) (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2))) (ab2 a2 a3 a2)) := by
  cases heq
theorem cp_11_2_12 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a2 a3 a2) = (op b0 (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2)))) :
    Join (ab2 (op a0 (rd a2 a1)) a2 (ab2 a2 a3 a2)) (op (ab2 a0 a1 a2) (ab2 b2 (ab2 b0 b1 b2) (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2)))) := by
  cases heq
theorem cp_12_root_0 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op a0 (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2))) = (op (op b0 b1) b1)) :
    Join (ab2 a2 (ab2 a0 a1 a2) (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2))) (rd b1 b0) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst b1
  intro he0
  have hsize := congrArg sz he0
  have hp_a0 := sz_pos a0
  have hp_a1 := sz_pos a1
  have hp_a2 := sz_pos a2
  have hp_a3 := sz_pos a3
  have hp_b0 := sz_pos b0
  simp only [sz] at hsize
  omega
theorem cp_12_2_0 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2)) = (op (op b0 b1) b1)) :
    Join (ab2 a2 (ab2 a0 a1 a2) (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2))) (op a0 (rd b1 b0)) := by
  cases heq
theorem cp_12_21_0 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 a2) = (op (op b0 b1) b1)) :
    Join (ab2 a2 (ab2 a0 a1 a2) (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2))) (op a0 (ab2 (rd b1 b0) a3 (ab2 a0 a1 a2))) := by
  cases heq
theorem cp_12_23_0 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 a2) = (op (op b0 b1) b1)) :
    Join (ab2 a2 (ab2 a0 a1 a2) (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2))) (op a0 (ab2 (ab2 a0 a1 a2) a3 (rd b1 b0))) := by
  cases heq
theorem cp_12_root_1 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op a0 (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2))) = (op (rd b0 b1) b0)) :
    Join (ab2 a2 (ab2 a0 a1 a2) (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2))) (rd b0 (op b1 b0)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst b0
  intro he0
  have hsize := congrArg sz he0
  have hp_a0 := sz_pos a0
  have hp_a1 := sz_pos a1
  have hp_a2 := sz_pos a2
  have hp_a3 := sz_pos a3
  have hp_b1 := sz_pos b1
  simp only [sz] at hsize
  omega
theorem cp_12_2_1 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2)) = (op (rd b0 b1) b0)) :
    Join (ab2 a2 (ab2 a0 a1 a2) (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2))) (op a0 (rd b0 (op b1 b0))) := by
  cases heq
theorem cp_12_21_1 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 a2) = (op (rd b0 b1) b0)) :
    Join (ab2 a2 (ab2 a0 a1 a2) (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2))) (op a0 (ab2 (rd b0 (op b1 b0)) a3 (ab2 a0 a1 a2))) := by
  cases heq
theorem cp_12_23_1 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 a2) = (op (rd b0 b1) b0)) :
    Join (ab2 a2 (ab2 a0 a1 a2) (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2))) (op a0 (ab2 (ab2 a0 a1 a2) a3 (rd b0 (op b1 b0)))) := by
  cases heq
theorem cp_12_root_2 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op a0 (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2))) = (op (op b0 (rd b1 b2)) b1)) :
    Join (ab2 a2 (ab2 a0 a1 a2) (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2))) (ab2 b0 b2 b1) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst b1
  intro he0
  have hsize := congrArg sz he0
  have hp_a0 := sz_pos a0
  have hp_a1 := sz_pos a1
  have hp_a2 := sz_pos a2
  have hp_a3 := sz_pos a3
  have hp_b0 := sz_pos b0
  have hp_b2 := sz_pos b2
  simp only [sz] at hsize
  omega
theorem cp_12_2_2 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2)) = (op (op b0 (rd b1 b2)) b1)) :
    Join (ab2 a2 (ab2 a0 a1 a2) (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2))) (op a0 (ab2 b0 b2 b1)) := by
  cases heq
theorem cp_12_21_2 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 a2) = (op (op b0 (rd b1 b2)) b1)) :
    Join (ab2 a2 (ab2 a0 a1 a2) (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2))) (op a0 (ab2 (ab2 b0 b2 b1) a3 (ab2 a0 a1 a2))) := by
  cases heq
theorem cp_12_23_2 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 a2) = (op (op b0 (rd b1 b2)) b1)) :
    Join (ab2 a2 (ab2 a0 a1 a2) (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2))) (op a0 (ab2 (ab2 a0 a1 a2) a3 (ab2 b0 b2 b1))) := by
  cases heq
theorem cp_12_root_3 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op a0 (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2))) = (op b0 (ab2 b1 b2 b0))) :
    Join (ab2 a2 (ab2 a0 a1 a2) (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2))) b1 := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  rcases T.ab2.inj he1 with ⟨he2, he3, he4⟩
  clear he1
  revert he0 he2 he3
  subst b0
  intro he0 he2 he3
  revert he0 he2
  subst a3
  intro he0 he2
  revert he0
  subst b1
  intro he0
  have hsize := congrArg sz he0
  have hp_a0 := sz_pos a0
  have hp_a1 := sz_pos a1
  have hp_a2 := sz_pos a2
  simp only [sz] at hsize
  omega
theorem cp_12_2_3 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2)) = (op b0 (ab2 b1 b2 b0))) :
    Join (ab2 a2 (ab2 a0 a1 a2) (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2))) (op a0 b1) := by
  cases heq
theorem cp_12_21_3 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 a2) = (op b0 (ab2 b1 b2 b0))) :
    Join (ab2 a2 (ab2 a0 a1 a2) (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2))) (op a0 (ab2 b1 a3 (ab2 a0 a1 a2))) := by
  cases heq
theorem cp_12_23_3 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 a2) = (op b0 (ab2 b1 b2 b0))) :
    Join (ab2 a2 (ab2 a0 a1 a2) (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2))) (op a0 (ab2 (ab2 a0 a1 a2) a3 b1)) := by
  cases heq
theorem cp_12_root_4 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op a0 (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2))) = (op b0 (ab2 b0 b1 b2))) :
    Join (ab2 a2 (ab2 a0 a1 a2) (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2))) (rd (ab2 b0 b1 b2) b2) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  rcases T.ab2.inj he1 with ⟨he2, he3, he4⟩
  clear he1
  revert he0 he2 he3
  subst b2
  intro he0 he2 he3
  revert he0 he2
  subst a3
  intro he0 he2
  revert he0
  subst b0
  intro he0
  have hsize := congrArg sz he0
  have hp_a0 := sz_pos a0
  have hp_a1 := sz_pos a1
  have hp_a2 := sz_pos a2
  simp only [sz] at hsize
  omega
theorem cp_12_2_4 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2)) = (op b0 (ab2 b0 b1 b2))) :
    Join (ab2 a2 (ab2 a0 a1 a2) (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2))) (op a0 (rd (ab2 b0 b1 b2) b2)) := by
  cases heq
theorem cp_12_21_4 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 a2) = (op b0 (ab2 b0 b1 b2))) :
    Join (ab2 a2 (ab2 a0 a1 a2) (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2))) (op a0 (ab2 (rd (ab2 b0 b1 b2) b2) a3 (ab2 a0 a1 a2))) := by
  cases heq
theorem cp_12_23_4 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 a2) = (op b0 (ab2 b0 b1 b2))) :
    Join (ab2 a2 (ab2 a0 a1 a2) (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2))) (op a0 (ab2 (ab2 a0 a1 a2) a3 (rd (ab2 b0 b1 b2) b2))) := by
  cases heq
theorem cp_12_root_5 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op a0 (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2))) = (rd (ab2 b0 b1 b0) b0)) :
    Join (ab2 a2 (ab2 a0 a1 a2) (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2))) b0 := by
  cases heq
theorem cp_12_2_5 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2)) = (rd (ab2 b0 b1 b0) b0)) :
    Join (ab2 a2 (ab2 a0 a1 a2) (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2))) (op a0 b0) := by
  cases heq
theorem cp_12_21_5 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 a2) = (rd (ab2 b0 b1 b0) b0)) :
    Join (ab2 a2 (ab2 a0 a1 a2) (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2))) (op a0 (ab2 b0 a3 (ab2 a0 a1 a2))) := by
  cases heq
theorem cp_12_23_5 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 a2) = (rd (ab2 b0 b1 b0) b0)) :
    Join (ab2 a2 (ab2 a0 a1 a2) (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2))) (op a0 (ab2 (ab2 a0 a1 a2) a3 b0)) := by
  cases heq
theorem cp_12_root_6 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op a0 (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2))) = (op (ab2 b0 b1 b2) b2)) :
    Join (ab2 a2 (ab2 a0 a1 a2) (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2))) (rd b2 (op b0 (rd b2 b1))) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst b2
  intro he0
  have hsize := congrArg sz he0
  have hp_a0 := sz_pos a0
  have hp_a1 := sz_pos a1
  have hp_a2 := sz_pos a2
  have hp_a3 := sz_pos a3
  have hp_b0 := sz_pos b0
  have hp_b1 := sz_pos b1
  simp only [sz] at hsize
  omega
theorem cp_12_2_6 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2)) = (op (ab2 b0 b1 b2) b2)) :
    Join (ab2 a2 (ab2 a0 a1 a2) (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2))) (op a0 (rd b2 (op b0 (rd b2 b1)))) := by
  cases heq
theorem cp_12_21_6 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 a2) = (op (ab2 b0 b1 b2) b2)) :
    Join (ab2 a2 (ab2 a0 a1 a2) (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2))) (op a0 (ab2 (rd b2 (op b0 (rd b2 b1))) a3 (ab2 a0 a1 a2))) := by
  cases heq
theorem cp_12_23_6 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 a2) = (op (ab2 b0 b1 b2) b2)) :
    Join (ab2 a2 (ab2 a0 a1 a2) (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2))) (op a0 (ab2 (ab2 a0 a1 a2) a3 (rd b2 (op b0 (rd b2 b1))))) := by
  cases heq
theorem cp_12_root_7 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op a0 (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2))) = (op (op b0 b1) (ab2 b1 b2 b1))) :
    Join (ab2 a2 (ab2 a0 a1 a2) (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2))) (ab2 b0 b1 (ab2 b1 b2 b1)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  rcases T.ab2.inj he1 with ⟨he2, he3, he4⟩
  clear he1
  revert he0 he2 he3
  subst b1
  intro he0 he2 he3
  revert he0 he2
  subst a3
  intro he0 he2
  clear he2
  have hsize := congrArg sz he0
  have hp_a0 := sz_pos a0
  have hp_a1 := sz_pos a1
  have hp_a2 := sz_pos a2
  have hp_b0 := sz_pos b0
  simp only [sz] at hsize
  omega
theorem cp_12_2_7 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2)) = (op (op b0 b1) (ab2 b1 b2 b1))) :
    Join (ab2 a2 (ab2 a0 a1 a2) (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2))) (op a0 (ab2 b0 b1 (ab2 b1 b2 b1))) := by
  cases heq
theorem cp_12_21_7 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 a2) = (op (op b0 b1) (ab2 b1 b2 b1))) :
    Join (ab2 a2 (ab2 a0 a1 a2) (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2))) (op a0 (ab2 (ab2 b0 b1 (ab2 b1 b2 b1)) a3 (ab2 a0 a1 a2))) := by
  cases heq
theorem cp_12_23_7 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 a2) = (op (op b0 b1) (ab2 b1 b2 b1))) :
    Join (ab2 a2 (ab2 a0 a1 a2) (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2))) (op a0 (ab2 (ab2 a0 a1 a2) a3 (ab2 b0 b1 (ab2 b1 b2 b1)))) := by
  cases heq
theorem cp_12_root_8 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op a0 (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2))) = (op (rd (rd b0 b1) b2) b0)) :
    Join (ab2 a2 (ab2 a0 a1 a2) (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2))) (ab2 (op b2 (rd b0 b1)) b1 b0) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst b0
  intro he0
  have hsize := congrArg sz he0
  have hp_a0 := sz_pos a0
  have hp_a1 := sz_pos a1
  have hp_a2 := sz_pos a2
  have hp_a3 := sz_pos a3
  have hp_b1 := sz_pos b1
  have hp_b2 := sz_pos b2
  simp only [sz] at hsize
  omega
theorem cp_12_2_8 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2)) = (op (rd (rd b0 b1) b2) b0)) :
    Join (ab2 a2 (ab2 a0 a1 a2) (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2))) (op a0 (ab2 (op b2 (rd b0 b1)) b1 b0)) := by
  cases heq
theorem cp_12_21_8 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 a2) = (op (rd (rd b0 b1) b2) b0)) :
    Join (ab2 a2 (ab2 a0 a1 a2) (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2))) (op a0 (ab2 (ab2 (op b2 (rd b0 b1)) b1 b0) a3 (ab2 a0 a1 a2))) := by
  cases heq
theorem cp_12_23_8 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 a2) = (op (rd (rd b0 b1) b2) b0)) :
    Join (ab2 a2 (ab2 a0 a1 a2) (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2))) (op a0 (ab2 (ab2 a0 a1 a2) a3 (ab2 (op b2 (rd b0 b1)) b1 b0))) := by
  cases heq
theorem cp_12_root_9 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op a0 (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2))) = (op (rd b0 b1) (ab2 b0 b2 b0))) :
    Join (ab2 a2 (ab2 a0 a1 a2) (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2))) (ab2 (op b1 b0) b0 (ab2 b0 b2 b0)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  rcases T.ab2.inj he1 with ⟨he2, he3, he4⟩
  clear he1
  revert he0 he2 he3
  subst b0
  intro he0 he2 he3
  revert he0 he2
  subst a3
  intro he0 he2
  clear he2
  have hsize := congrArg sz he0
  have hp_a0 := sz_pos a0
  have hp_a1 := sz_pos a1
  have hp_a2 := sz_pos a2
  have hp_b1 := sz_pos b1
  simp only [sz] at hsize
  omega
theorem cp_12_2_9 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2)) = (op (rd b0 b1) (ab2 b0 b2 b0))) :
    Join (ab2 a2 (ab2 a0 a1 a2) (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2))) (op a0 (ab2 (op b1 b0) b0 (ab2 b0 b2 b0))) := by
  cases heq
theorem cp_12_21_9 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 a2) = (op (rd b0 b1) (ab2 b0 b2 b0))) :
    Join (ab2 a2 (ab2 a0 a1 a2) (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2))) (op a0 (ab2 (ab2 (op b1 b0) b0 (ab2 b0 b2 b0)) a3 (ab2 a0 a1 a2))) := by
  cases heq
theorem cp_12_23_9 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 a2) = (op (rd b0 b1) (ab2 b0 b2 b0))) :
    Join (ab2 a2 (ab2 a0 a1 a2) (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2))) (op a0 (ab2 (ab2 a0 a1 a2) a3 (ab2 (op b1 b0) b0 (ab2 b0 b2 b0)))) := by
  cases heq
theorem cp_12_root_10 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op a0 (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2))) = (op (ab2 b0 b1 (rd b2 b3)) b2)) :
    Join (ab2 a2 (ab2 a0 a1 a2) (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2))) (ab2 (op b0 (rd (rd b2 b3) b1)) b3 b2) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  revert he0
  subst b2
  intro he0
  have hsize := congrArg sz he0
  have hp_a0 := sz_pos a0
  have hp_a1 := sz_pos a1
  have hp_a2 := sz_pos a2
  have hp_a3 := sz_pos a3
  have hp_b0 := sz_pos b0
  have hp_b1 := sz_pos b1
  have hp_b3 := sz_pos b3
  simp only [sz] at hsize
  omega
theorem cp_12_2_10 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2)) = (op (ab2 b0 b1 (rd b2 b3)) b2)) :
    Join (ab2 a2 (ab2 a0 a1 a2) (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2))) (op a0 (ab2 (op b0 (rd (rd b2 b3) b1)) b3 b2)) := by
  cases heq
theorem cp_12_21_10 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 a2) = (op (ab2 b0 b1 (rd b2 b3)) b2)) :
    Join (ab2 a2 (ab2 a0 a1 a2) (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2))) (op a0 (ab2 (ab2 (op b0 (rd (rd b2 b3) b1)) b3 b2) a3 (ab2 a0 a1 a2))) := by
  cases heq
theorem cp_12_23_10 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 a2) = (op (ab2 b0 b1 (rd b2 b3)) b2)) :
    Join (ab2 a2 (ab2 a0 a1 a2) (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2))) (op a0 (ab2 (ab2 a0 a1 a2) a3 (ab2 (op b0 (rd (rd b2 b3) b1)) b3 b2))) := by
  cases heq
theorem cp_12_root_11 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op a0 (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2))) = (op (ab2 b0 b1 b2) (ab2 b2 b3 b2))) :
    Join (ab2 a2 (ab2 a0 a1 a2) (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2))) (ab2 (op b0 (rd b2 b1)) b2 (ab2 b2 b3 b2)) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  rcases T.ab2.inj he1 with ⟨he2, he3, he4⟩
  clear he1
  revert he0 he2 he3
  subst b2
  intro he0 he2 he3
  revert he0 he2
  subst a3
  intro he0 he2
  clear he2
  have hsize := congrArg sz he0
  have hp_a0 := sz_pos a0
  have hp_a1 := sz_pos a1
  have hp_a2 := sz_pos a2
  have hp_b0 := sz_pos b0
  have hp_b1 := sz_pos b1
  simp only [sz] at hsize
  omega
theorem cp_12_2_11 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2)) = (op (ab2 b0 b1 b2) (ab2 b2 b3 b2))) :
    Join (ab2 a2 (ab2 a0 a1 a2) (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2))) (op a0 (ab2 (op b0 (rd b2 b1)) b2 (ab2 b2 b3 b2))) := by
  cases heq
theorem cp_12_21_11 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 a2) = (op (ab2 b0 b1 b2) (ab2 b2 b3 b2))) :
    Join (ab2 a2 (ab2 a0 a1 a2) (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2))) (op a0 (ab2 (ab2 (op b0 (rd b2 b1)) b2 (ab2 b2 b3 b2)) a3 (ab2 a0 a1 a2))) := by
  cases heq
theorem cp_12_23_11 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 a2) = (op (ab2 b0 b1 b2) (ab2 b2 b3 b2))) :
    Join (ab2 a2 (ab2 a0 a1 a2) (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2))) (op a0 (ab2 (ab2 a0 a1 a2) a3 (ab2 (op b0 (rd b2 b1)) b2 (ab2 b2 b3 b2)))) := by
  cases heq
theorem cp_12_root_12 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (op a0 (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2))) = (op b0 (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2)))) :
    Join (ab2 a2 (ab2 a0 a1 a2) (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2))) (ab2 b2 (ab2 b0 b1 b2) (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2))) := by
  rcases T.op.inj heq with ⟨he0, he1⟩
  clear heq
  rcases T.ab2.inj he1 with ⟨he2, he3, he4⟩
  clear he1
  rcases T.ab2.inj he4 with ⟨he5, he6, he7⟩
  clear he4
  revert he0 he2 he3 he5 he6
  subst a2
  intro he0 he2 he3 he5 he6
  revert he0 he2 he3 he5
  subst a1
  intro he0 he2 he3 he5
  revert he0 he2 he3
  subst a0
  intro he0 he2 he3
  revert he0 he2
  subst a3
  intro he0 he2
  clear he2
  clear he0
  exact ⟨(ab2 b2 (ab2 b0 b1 b2) (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2))), (Relation.ReflTransGen.refl), (Relation.ReflTransGen.refl)⟩
theorem cp_12_2_12 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2)) = (op b0 (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2)))) :
    Join (ab2 a2 (ab2 a0 a1 a2) (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2))) (op a0 (ab2 b2 (ab2 b0 b1 b2) (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2)))) := by
  cases heq
theorem cp_12_21_12 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 a2) = (op b0 (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2)))) :
    Join (ab2 a2 (ab2 a0 a1 a2) (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2))) (op a0 (ab2 (ab2 b2 (ab2 b0 b1 b2) (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2))) a3 (ab2 a0 a1 a2))) := by
  cases heq
theorem cp_12_23_12 (a0 a1 a2 a3 b0 b1 b2 b3 : T)
    (heq : (ab2 a0 a1 a2) = (op b0 (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2)))) :
    Join (ab2 a2 (ab2 a0 a1 a2) (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2))) (op a0 (ab2 (ab2 a0 a1 a2) a3 (ab2 b2 (ab2 b0 b1 b2) (ab2 (ab2 b0 b1 b2) b3 (ab2 b0 b1 b2))))) := by
  cases heq
theorem vp_0_11 (a0 a1 a2 a3 v : T) (hv : Step a0 v) :
    Join (rd a1 a0) (op (op v a1) a1) := by
  exact ⟨(rd a1 v), ((Relation.ReflTransGen.refl).tail (Step.c_rd_2 a1 hv)), ((Relation.ReflTransGen.refl).tail (root_step .r0 v a1 a2 a3))⟩
theorem vp_0_12 (a0 a1 a2 a3 v : T) (hv : Step a1 v) :
    Join (rd a1 a0) (op (op a0 v) a1) := by
  exact ⟨(rd v a0), ((Relation.ReflTransGen.refl).tail (Step.c_rd_1 a0 hv)), (((Relation.ReflTransGen.refl).tail (Step.c_op_2 (op a0 v) hv)).tail (root_step .r0 a0 v a2 a3))⟩
theorem vp_0_2 (a0 a1 a2 a3 v : T) (hv : Step a1 v) :
    Join (rd a1 a0) (op (op a0 a1) v) := by
  exact ⟨(rd v a0), ((Relation.ReflTransGen.refl).tail (Step.c_rd_1 a0 hv)), (((Relation.ReflTransGen.refl).tail (Step.c_op_1 v (Step.c_op_2 a0 hv))).tail (root_step .r0 a0 v a2 a3))⟩
theorem vp_1_11 (a0 a1 a2 a3 v : T) (hv : Step a0 v) :
    Join (rd a0 (op a1 a0)) (op (rd v a1) a0) := by
  exact ⟨(rd v (op a1 v)), (((Relation.ReflTransGen.refl).tail (Step.c_rd_1 (op a1 a0) hv)).tail (Step.c_rd_2 v (Step.c_op_2 a1 hv))), (((Relation.ReflTransGen.refl).tail (Step.c_op_2 (rd v a1) hv)).tail (root_step .r1 v a1 a2 a3))⟩
theorem vp_1_12 (a0 a1 a2 a3 v : T) (hv : Step a1 v) :
    Join (rd a0 (op a1 a0)) (op (rd a0 v) a0) := by
  exact ⟨(rd a0 (op v a0)), ((Relation.ReflTransGen.refl).tail (Step.c_rd_2 a0 (Step.c_op_1 a0 hv))), ((Relation.ReflTransGen.refl).tail (root_step .r1 a0 v a2 a3))⟩
theorem vp_1_2 (a0 a1 a2 a3 v : T) (hv : Step a0 v) :
    Join (rd a0 (op a1 a0)) (op (rd a0 a1) v) := by
  exact ⟨(rd v (op a1 v)), (((Relation.ReflTransGen.refl).tail (Step.c_rd_1 (op a1 a0) hv)).tail (Step.c_rd_2 v (Step.c_op_2 a1 hv))), (((Relation.ReflTransGen.refl).tail (Step.c_op_1 v (Step.c_rd_1 a1 hv))).tail (root_step .r1 v a1 a2 a3))⟩
theorem vp_2_11 (a0 a1 a2 a3 v : T) (hv : Step a0 v) :
    Join (ab2 a0 a2 a1) (op (op v (rd a1 a2)) a1) := by
  exact ⟨(ab2 v a2 a1), ((Relation.ReflTransGen.refl).tail (Step.c_ab2_1 a2 a1 hv)), ((Relation.ReflTransGen.refl).tail (root_step .r2 v a1 a2 a3))⟩
theorem vp_2_121 (a0 a1 a2 a3 v : T) (hv : Step a1 v) :
    Join (ab2 a0 a2 a1) (op (op a0 (rd v a2)) a1) := by
  exact ⟨(ab2 a0 a2 v), ((Relation.ReflTransGen.refl).tail (Step.c_ab2_3 a0 a2 hv)), (((Relation.ReflTransGen.refl).tail (Step.c_op_2 (op a0 (rd v a2)) hv)).tail (root_step .r2 a0 v a2 a3))⟩
theorem vp_2_122 (a0 a1 a2 a3 v : T) (hv : Step a2 v) :
    Join (ab2 a0 a2 a1) (op (op a0 (rd a1 v)) a1) := by
  exact ⟨(ab2 a0 v a1), ((Relation.ReflTransGen.refl).tail (Step.c_ab2_2 a0 a1 hv)), ((Relation.ReflTransGen.refl).tail (root_step .r2 a0 a1 v a3))⟩
theorem vp_2_2 (a0 a1 a2 a3 v : T) (hv : Step a1 v) :
    Join (ab2 a0 a2 a1) (op (op a0 (rd a1 a2)) v) := by
  exact ⟨(ab2 a0 a2 v), ((Relation.ReflTransGen.refl).tail (Step.c_ab2_3 a0 a2 hv)), (((Relation.ReflTransGen.refl).tail (Step.c_op_1 v (Step.c_op_2 a0 (Step.c_rd_1 a2 hv)))).tail (root_step .r2 a0 v a2 a3))⟩
theorem vp_3_1 (a0 a1 a2 a3 v : T) (hv : Step a0 v) :
    Join a1 (op v (ab2 a1 a2 a0)) := by
  exact ⟨a1, (Relation.ReflTransGen.refl), (((Relation.ReflTransGen.refl).tail (Step.c_op_2 v (Step.c_ab2_3 a1 a2 hv))).tail (root_step .r3 v a1 a2 a3))⟩
theorem vp_3_21 (a0 a1 a2 a3 v : T) (hv : Step a1 v) :
    Join a1 (op a0 (ab2 v a2 a0)) := by
  exact ⟨v, ((Relation.ReflTransGen.refl).tail hv), ((Relation.ReflTransGen.refl).tail (root_step .r3 a0 v a2 a3))⟩
theorem vp_3_22 (a0 a1 a2 a3 v : T) (hv : Step a2 v) :
    Join a1 (op a0 (ab2 a1 v a0)) := by
  exact ⟨a1, (Relation.ReflTransGen.refl), ((Relation.ReflTransGen.refl).tail (root_step .r3 a0 a1 v a3))⟩
theorem vp_3_23 (a0 a1 a2 a3 v : T) (hv : Step a0 v) :
    Join a1 (op a0 (ab2 a1 a2 v)) := by
  exact ⟨a1, (Relation.ReflTransGen.refl), (((Relation.ReflTransGen.refl).tail (Step.c_op_1 (ab2 a1 a2 v) hv)).tail (root_step .r3 v a1 a2 a3))⟩
theorem vp_4_1 (a0 a1 a2 a3 v : T) (hv : Step a0 v) :
    Join (rd (ab2 a0 a1 a2) a2) (op v (ab2 a0 a1 a2)) := by
  exact ⟨(rd (ab2 v a1 a2) a2), ((Relation.ReflTransGen.refl).tail (Step.c_rd_1 a2 (Step.c_ab2_1 a1 a2 hv))), (((Relation.ReflTransGen.refl).tail (Step.c_op_2 v (Step.c_ab2_1 a1 a2 hv))).tail (root_step .r4 v a1 a2 a3))⟩
theorem vp_4_21 (a0 a1 a2 a3 v : T) (hv : Step a0 v) :
    Join (rd (ab2 a0 a1 a2) a2) (op a0 (ab2 v a1 a2)) := by
  exact ⟨(rd (ab2 v a1 a2) a2), ((Relation.ReflTransGen.refl).tail (Step.c_rd_1 a2 (Step.c_ab2_1 a1 a2 hv))), (((Relation.ReflTransGen.refl).tail (Step.c_op_1 (ab2 v a1 a2) hv)).tail (root_step .r4 v a1 a2 a3))⟩
theorem vp_4_22 (a0 a1 a2 a3 v : T) (hv : Step a1 v) :
    Join (rd (ab2 a0 a1 a2) a2) (op a0 (ab2 a0 v a2)) := by
  exact ⟨(rd (ab2 a0 v a2) a2), ((Relation.ReflTransGen.refl).tail (Step.c_rd_1 a2 (Step.c_ab2_2 a0 a2 hv))), ((Relation.ReflTransGen.refl).tail (root_step .r4 a0 v a2 a3))⟩
theorem vp_4_23 (a0 a1 a2 a3 v : T) (hv : Step a2 v) :
    Join (rd (ab2 a0 a1 a2) a2) (op a0 (ab2 a0 a1 v)) := by
  exact ⟨(rd (ab2 a0 a1 v) v), (((Relation.ReflTransGen.refl).tail (Step.c_rd_1 a2 (Step.c_ab2_3 a0 a1 hv))).tail (Step.c_rd_2 (ab2 a0 a1 v) hv)), ((Relation.ReflTransGen.refl).tail (root_step .r4 a0 a1 v a3))⟩
theorem vp_5_11 (a0 a1 a2 a3 v : T) (hv : Step a0 v) :
    Join a0 (rd (ab2 v a1 a0) a0) := by
  exact ⟨v, ((Relation.ReflTransGen.refl).tail hv), ((((Relation.ReflTransGen.refl).tail (Step.c_rd_1 a0 (Step.c_ab2_3 v a1 hv))).tail (Step.c_rd_2 (ab2 v a1 v) hv)).tail (root_step .r5 v a1 a2 a3))⟩
theorem vp_5_12 (a0 a1 a2 a3 v : T) (hv : Step a1 v) :
    Join a0 (rd (ab2 a0 v a0) a0) := by
  exact ⟨a0, (Relation.ReflTransGen.refl), ((Relation.ReflTransGen.refl).tail (root_step .r5 a0 v a2 a3))⟩
theorem vp_5_13 (a0 a1 a2 a3 v : T) (hv : Step a0 v) :
    Join a0 (rd (ab2 a0 a1 v) a0) := by
  exact ⟨v, ((Relation.ReflTransGen.refl).tail hv), ((((Relation.ReflTransGen.refl).tail (Step.c_rd_1 a0 (Step.c_ab2_1 a1 v hv))).tail (Step.c_rd_2 (ab2 v a1 v) hv)).tail (root_step .r5 v a1 a2 a3))⟩
theorem vp_5_2 (a0 a1 a2 a3 v : T) (hv : Step a0 v) :
    Join a0 (rd (ab2 a0 a1 a0) v) := by
  exact ⟨v, ((Relation.ReflTransGen.refl).tail hv), ((((Relation.ReflTransGen.refl).tail (Step.c_rd_1 v (Step.c_ab2_1 a1 a0 hv))).tail (Step.c_rd_1 v (Step.c_ab2_3 v a1 hv))).tail (root_step .r5 v a1 a2 a3))⟩
theorem vp_6_11 (a0 a1 a2 a3 v : T) (hv : Step a0 v) :
    Join (rd a2 (op a0 (rd a2 a1))) (op (ab2 v a1 a2) a2) := by
  exact ⟨(rd a2 (op v (rd a2 a1))), ((Relation.ReflTransGen.refl).tail (Step.c_rd_2 a2 (Step.c_op_1 (rd a2 a1) hv))), ((Relation.ReflTransGen.refl).tail (root_step .r6 v a1 a2 a3))⟩
theorem vp_6_12 (a0 a1 a2 a3 v : T) (hv : Step a1 v) :
    Join (rd a2 (op a0 (rd a2 a1))) (op (ab2 a0 v a2) a2) := by
  exact ⟨(rd a2 (op a0 (rd a2 v))), ((Relation.ReflTransGen.refl).tail (Step.c_rd_2 a2 (Step.c_op_2 a0 (Step.c_rd_2 a2 hv)))), ((Relation.ReflTransGen.refl).tail (root_step .r6 a0 v a2 a3))⟩
theorem vp_6_13 (a0 a1 a2 a3 v : T) (hv : Step a2 v) :
    Join (rd a2 (op a0 (rd a2 a1))) (op (ab2 a0 a1 v) a2) := by
  exact ⟨(rd v (op a0 (rd v a1))), (((Relation.ReflTransGen.refl).tail (Step.c_rd_1 (op a0 (rd a2 a1)) hv)).tail (Step.c_rd_2 v (Step.c_op_2 a0 (Step.c_rd_1 a1 hv)))), (((Relation.ReflTransGen.refl).tail (Step.c_op_2 (ab2 a0 a1 v) hv)).tail (root_step .r6 a0 a1 v a3))⟩
theorem vp_6_2 (a0 a1 a2 a3 v : T) (hv : Step a2 v) :
    Join (rd a2 (op a0 (rd a2 a1))) (op (ab2 a0 a1 a2) v) := by
  exact ⟨(rd v (op a0 (rd v a1))), (((Relation.ReflTransGen.refl).tail (Step.c_rd_1 (op a0 (rd a2 a1)) hv)).tail (Step.c_rd_2 v (Step.c_op_2 a0 (Step.c_rd_1 a1 hv)))), (((Relation.ReflTransGen.refl).tail (Step.c_op_1 v (Step.c_ab2_3 a0 a1 hv))).tail (root_step .r6 a0 a1 v a3))⟩
theorem vp_7_11 (a0 a1 a2 a3 v : T) (hv : Step a0 v) :
    Join (ab2 a0 a1 (ab2 a1 a2 a1)) (op (op v a1) (ab2 a1 a2 a1)) := by
  exact ⟨(ab2 v a1 (ab2 a1 a2 a1)), ((Relation.ReflTransGen.refl).tail (Step.c_ab2_1 a1 (ab2 a1 a2 a1) hv)), ((Relation.ReflTransGen.refl).tail (root_step .r7 v a1 a2 a3))⟩
theorem vp_7_12 (a0 a1 a2 a3 v : T) (hv : Step a1 v) :
    Join (ab2 a0 a1 (ab2 a1 a2 a1)) (op (op a0 v) (ab2 a1 a2 a1)) := by
  exact ⟨(ab2 a0 v (ab2 v a2 v)), ((((Relation.ReflTransGen.refl).tail (Step.c_ab2_2 a0 (ab2 a1 a2 a1) hv)).tail (Step.c_ab2_3 a0 v (Step.c_ab2_1 a2 a1 hv))).tail (Step.c_ab2_3 a0 v (Step.c_ab2_3 v a2 hv))), ((((Relation.ReflTransGen.refl).tail (Step.c_op_2 (op a0 v) (Step.c_ab2_1 a2 a1 hv))).tail (Step.c_op_2 (op a0 v) (Step.c_ab2_3 v a2 hv))).tail (root_step .r7 a0 v a2 a3))⟩
theorem vp_7_21 (a0 a1 a2 a3 v : T) (hv : Step a1 v) :
    Join (ab2 a0 a1 (ab2 a1 a2 a1)) (op (op a0 a1) (ab2 v a2 a1)) := by
  exact ⟨(ab2 a0 v (ab2 v a2 v)), ((((Relation.ReflTransGen.refl).tail (Step.c_ab2_2 a0 (ab2 a1 a2 a1) hv)).tail (Step.c_ab2_3 a0 v (Step.c_ab2_1 a2 a1 hv))).tail (Step.c_ab2_3 a0 v (Step.c_ab2_3 v a2 hv))), ((((Relation.ReflTransGen.refl).tail (Step.c_op_1 (ab2 v a2 a1) (Step.c_op_2 a0 hv))).tail (Step.c_op_2 (op a0 v) (Step.c_ab2_3 v a2 hv))).tail (root_step .r7 a0 v a2 a3))⟩
theorem vp_7_22 (a0 a1 a2 a3 v : T) (hv : Step a2 v) :
    Join (ab2 a0 a1 (ab2 a1 a2 a1)) (op (op a0 a1) (ab2 a1 v a1)) := by
  exact ⟨(ab2 a0 a1 (ab2 a1 v a1)), ((Relation.ReflTransGen.refl).tail (Step.c_ab2_3 a0 a1 (Step.c_ab2_2 a1 a1 hv))), ((Relation.ReflTransGen.refl).tail (root_step .r7 a0 a1 v a3))⟩
theorem vp_7_23 (a0 a1 a2 a3 v : T) (hv : Step a1 v) :
    Join (ab2 a0 a1 (ab2 a1 a2 a1)) (op (op a0 a1) (ab2 a1 a2 v)) := by
  exact ⟨(ab2 a0 v (ab2 v a2 v)), ((((Relation.ReflTransGen.refl).tail (Step.c_ab2_2 a0 (ab2 a1 a2 a1) hv)).tail (Step.c_ab2_3 a0 v (Step.c_ab2_1 a2 a1 hv))).tail (Step.c_ab2_3 a0 v (Step.c_ab2_3 v a2 hv))), ((((Relation.ReflTransGen.refl).tail (Step.c_op_1 (ab2 a1 a2 v) (Step.c_op_2 a0 hv))).tail (Step.c_op_2 (op a0 v) (Step.c_ab2_1 a2 v hv))).tail (root_step .r7 a0 v a2 a3))⟩
theorem vp_8_111 (a0 a1 a2 a3 v : T) (hv : Step a0 v) :
    Join (ab2 (op a2 (rd a0 a1)) a1 a0) (op (rd (rd v a1) a2) a0) := by
  exact ⟨(ab2 (op a2 (rd v a1)) a1 v), (((Relation.ReflTransGen.refl).tail (Step.c_ab2_1 a1 a0 (Step.c_op_2 a2 (Step.c_rd_1 a1 hv)))).tail (Step.c_ab2_3 (op a2 (rd v a1)) a1 hv)), (((Relation.ReflTransGen.refl).tail (Step.c_op_2 (rd (rd v a1) a2) hv)).tail (root_step .r8 v a1 a2 a3))⟩
theorem vp_8_112 (a0 a1 a2 a3 v : T) (hv : Step a1 v) :
    Join (ab2 (op a2 (rd a0 a1)) a1 a0) (op (rd (rd a0 v) a2) a0) := by
  exact ⟨(ab2 (op a2 (rd a0 v)) v a0), (((Relation.ReflTransGen.refl).tail (Step.c_ab2_1 a1 a0 (Step.c_op_2 a2 (Step.c_rd_2 a0 hv)))).tail (Step.c_ab2_2 (op a2 (rd a0 v)) a0 hv)), ((Relation.ReflTransGen.refl).tail (root_step .r8 a0 v a2 a3))⟩
theorem vp_8_12 (a0 a1 a2 a3 v : T) (hv : Step a2 v) :
    Join (ab2 (op a2 (rd a0 a1)) a1 a0) (op (rd (rd a0 a1) v) a0) := by
  exact ⟨(ab2 (op v (rd a0 a1)) a1 a0), ((Relation.ReflTransGen.refl).tail (Step.c_ab2_1 a1 a0 (Step.c_op_1 (rd a0 a1) hv))), ((Relation.ReflTransGen.refl).tail (root_step .r8 a0 a1 v a3))⟩
theorem vp_8_2 (a0 a1 a2 a3 v : T) (hv : Step a0 v) :
    Join (ab2 (op a2 (rd a0 a1)) a1 a0) (op (rd (rd a0 a1) a2) v) := by
  exact ⟨(ab2 (op a2 (rd v a1)) a1 v), (((Relation.ReflTransGen.refl).tail (Step.c_ab2_1 a1 a0 (Step.c_op_2 a2 (Step.c_rd_1 a1 hv)))).tail (Step.c_ab2_3 (op a2 (rd v a1)) a1 hv)), (((Relation.ReflTransGen.refl).tail (Step.c_op_1 v (Step.c_rd_1 a2 (Step.c_rd_1 a1 hv)))).tail (root_step .r8 v a1 a2 a3))⟩
theorem vp_9_11 (a0 a1 a2 a3 v : T) (hv : Step a0 v) :
    Join (ab2 (op a1 a0) a0 (ab2 a0 a2 a0)) (op (rd v a1) (ab2 a0 a2 a0)) := by
  exact ⟨(ab2 (op a1 v) v (ab2 v a2 v)), (((((Relation.ReflTransGen.refl).tail (Step.c_ab2_1 a0 (ab2 a0 a2 a0) (Step.c_op_2 a1 hv))).tail (Step.c_ab2_2 (op a1 v) (ab2 a0 a2 a0) hv)).tail (Step.c_ab2_3 (op a1 v) v (Step.c_ab2_1 a2 a0 hv))).tail (Step.c_ab2_3 (op a1 v) v (Step.c_ab2_3 v a2 hv))), ((((Relation.ReflTransGen.refl).tail (Step.c_op_2 (rd v a1) (Step.c_ab2_1 a2 a0 hv))).tail (Step.c_op_2 (rd v a1) (Step.c_ab2_3 v a2 hv))).tail (root_step .r9 v a1 a2 a3))⟩
theorem vp_9_12 (a0 a1 a2 a3 v : T) (hv : Step a1 v) :
    Join (ab2 (op a1 a0) a0 (ab2 a0 a2 a0)) (op (rd a0 v) (ab2 a0 a2 a0)) := by
  exact ⟨(ab2 (op v a0) a0 (ab2 a0 a2 a0)), ((Relation.ReflTransGen.refl).tail (Step.c_ab2_1 a0 (ab2 a0 a2 a0) (Step.c_op_1 a0 hv))), ((Relation.ReflTransGen.refl).tail (root_step .r9 a0 v a2 a3))⟩
theorem vp_9_21 (a0 a1 a2 a3 v : T) (hv : Step a0 v) :
    Join (ab2 (op a1 a0) a0 (ab2 a0 a2 a0)) (op (rd a0 a1) (ab2 v a2 a0)) := by
  exact ⟨(ab2 (op a1 v) v (ab2 v a2 v)), (((((Relation.ReflTransGen.refl).tail (Step.c_ab2_1 a0 (ab2 a0 a2 a0) (Step.c_op_2 a1 hv))).tail (Step.c_ab2_2 (op a1 v) (ab2 a0 a2 a0) hv)).tail (Step.c_ab2_3 (op a1 v) v (Step.c_ab2_1 a2 a0 hv))).tail (Step.c_ab2_3 (op a1 v) v (Step.c_ab2_3 v a2 hv))), ((((Relation.ReflTransGen.refl).tail (Step.c_op_1 (ab2 v a2 a0) (Step.c_rd_1 a1 hv))).tail (Step.c_op_2 (rd v a1) (Step.c_ab2_3 v a2 hv))).tail (root_step .r9 v a1 a2 a3))⟩
theorem vp_9_22 (a0 a1 a2 a3 v : T) (hv : Step a2 v) :
    Join (ab2 (op a1 a0) a0 (ab2 a0 a2 a0)) (op (rd a0 a1) (ab2 a0 v a0)) := by
  exact ⟨(ab2 (op a1 a0) a0 (ab2 a0 v a0)), ((Relation.ReflTransGen.refl).tail (Step.c_ab2_3 (op a1 a0) a0 (Step.c_ab2_2 a0 a0 hv))), ((Relation.ReflTransGen.refl).tail (root_step .r9 a0 a1 v a3))⟩
theorem vp_9_23 (a0 a1 a2 a3 v : T) (hv : Step a0 v) :
    Join (ab2 (op a1 a0) a0 (ab2 a0 a2 a0)) (op (rd a0 a1) (ab2 a0 a2 v)) := by
  exact ⟨(ab2 (op a1 v) v (ab2 v a2 v)), (((((Relation.ReflTransGen.refl).tail (Step.c_ab2_1 a0 (ab2 a0 a2 a0) (Step.c_op_2 a1 hv))).tail (Step.c_ab2_2 (op a1 v) (ab2 a0 a2 a0) hv)).tail (Step.c_ab2_3 (op a1 v) v (Step.c_ab2_1 a2 a0 hv))).tail (Step.c_ab2_3 (op a1 v) v (Step.c_ab2_3 v a2 hv))), ((((Relation.ReflTransGen.refl).tail (Step.c_op_1 (ab2 a0 a2 v) (Step.c_rd_1 a1 hv))).tail (Step.c_op_2 (rd v a1) (Step.c_ab2_1 a2 v hv))).tail (root_step .r9 v a1 a2 a3))⟩
theorem vp_10_11 (a0 a1 a2 a3 v : T) (hv : Step a0 v) :
    Join (ab2 (op a0 (rd (rd a2 a3) a1)) a3 a2) (op (ab2 v a1 (rd a2 a3)) a2) := by
  exact ⟨(ab2 (op v (rd (rd a2 a3) a1)) a3 a2), ((Relation.ReflTransGen.refl).tail (Step.c_ab2_1 a3 a2 (Step.c_op_1 (rd (rd a2 a3) a1) hv))), ((Relation.ReflTransGen.refl).tail (root_step .r10 v a1 a2 a3))⟩
theorem vp_10_12 (a0 a1 a2 a3 v : T) (hv : Step a1 v) :
    Join (ab2 (op a0 (rd (rd a2 a3) a1)) a3 a2) (op (ab2 a0 v (rd a2 a3)) a2) := by
  exact ⟨(ab2 (op a0 (rd (rd a2 a3) v)) a3 a2), ((Relation.ReflTransGen.refl).tail (Step.c_ab2_1 a3 a2 (Step.c_op_2 a0 (Step.c_rd_2 (rd a2 a3) hv)))), ((Relation.ReflTransGen.refl).tail (root_step .r10 a0 v a2 a3))⟩
theorem vp_10_131 (a0 a1 a2 a3 v : T) (hv : Step a2 v) :
    Join (ab2 (op a0 (rd (rd a2 a3) a1)) a3 a2) (op (ab2 a0 a1 (rd v a3)) a2) := by
  exact ⟨(ab2 (op a0 (rd (rd v a3) a1)) a3 v), (((Relation.ReflTransGen.refl).tail (Step.c_ab2_1 a3 a2 (Step.c_op_2 a0 (Step.c_rd_1 a1 (Step.c_rd_1 a3 hv))))).tail (Step.c_ab2_3 (op a0 (rd (rd v a3) a1)) a3 hv)), (((Relation.ReflTransGen.refl).tail (Step.c_op_2 (ab2 a0 a1 (rd v a3)) hv)).tail (root_step .r10 a0 a1 v a3))⟩
theorem vp_10_132 (a0 a1 a2 a3 v : T) (hv : Step a3 v) :
    Join (ab2 (op a0 (rd (rd a2 a3) a1)) a3 a2) (op (ab2 a0 a1 (rd a2 v)) a2) := by
  exact ⟨(ab2 (op a0 (rd (rd a2 v) a1)) v a2), (((Relation.ReflTransGen.refl).tail (Step.c_ab2_1 a3 a2 (Step.c_op_2 a0 (Step.c_rd_1 a1 (Step.c_rd_2 a2 hv))))).tail (Step.c_ab2_2 (op a0 (rd (rd a2 v) a1)) a2 hv)), ((Relation.ReflTransGen.refl).tail (root_step .r10 a0 a1 a2 v))⟩
theorem vp_10_2 (a0 a1 a2 a3 v : T) (hv : Step a2 v) :
    Join (ab2 (op a0 (rd (rd a2 a3) a1)) a3 a2) (op (ab2 a0 a1 (rd a2 a3)) v) := by
  exact ⟨(ab2 (op a0 (rd (rd v a3) a1)) a3 v), (((Relation.ReflTransGen.refl).tail (Step.c_ab2_1 a3 a2 (Step.c_op_2 a0 (Step.c_rd_1 a1 (Step.c_rd_1 a3 hv))))).tail (Step.c_ab2_3 (op a0 (rd (rd v a3) a1)) a3 hv)), (((Relation.ReflTransGen.refl).tail (Step.c_op_1 v (Step.c_ab2_3 a0 a1 (Step.c_rd_1 a3 hv)))).tail (root_step .r10 a0 a1 v a3))⟩
theorem vp_11_11 (a0 a1 a2 a3 v : T) (hv : Step a0 v) :
    Join (ab2 (op a0 (rd a2 a1)) a2 (ab2 a2 a3 a2)) (op (ab2 v a1 a2) (ab2 a2 a3 a2)) := by
  exact ⟨(ab2 (op v (rd a2 a1)) a2 (ab2 a2 a3 a2)), ((Relation.ReflTransGen.refl).tail (Step.c_ab2_1 a2 (ab2 a2 a3 a2) (Step.c_op_1 (rd a2 a1) hv))), ((Relation.ReflTransGen.refl).tail (root_step .r11 v a1 a2 a3))⟩
theorem vp_11_12 (a0 a1 a2 a3 v : T) (hv : Step a1 v) :
    Join (ab2 (op a0 (rd a2 a1)) a2 (ab2 a2 a3 a2)) (op (ab2 a0 v a2) (ab2 a2 a3 a2)) := by
  exact ⟨(ab2 (op a0 (rd a2 v)) a2 (ab2 a2 a3 a2)), ((Relation.ReflTransGen.refl).tail (Step.c_ab2_1 a2 (ab2 a2 a3 a2) (Step.c_op_2 a0 (Step.c_rd_2 a2 hv)))), ((Relation.ReflTransGen.refl).tail (root_step .r11 a0 v a2 a3))⟩
theorem vp_11_13 (a0 a1 a2 a3 v : T) (hv : Step a2 v) :
    Join (ab2 (op a0 (rd a2 a1)) a2 (ab2 a2 a3 a2)) (op (ab2 a0 a1 v) (ab2 a2 a3 a2)) := by
  exact ⟨(ab2 (op a0 (rd v a1)) v (ab2 v a3 v)), (((((Relation.ReflTransGen.refl).tail (Step.c_ab2_1 a2 (ab2 a2 a3 a2) (Step.c_op_2 a0 (Step.c_rd_1 a1 hv)))).tail (Step.c_ab2_2 (op a0 (rd v a1)) (ab2 a2 a3 a2) hv)).tail (Step.c_ab2_3 (op a0 (rd v a1)) v (Step.c_ab2_1 a3 a2 hv))).tail (Step.c_ab2_3 (op a0 (rd v a1)) v (Step.c_ab2_3 v a3 hv))), ((((Relation.ReflTransGen.refl).tail (Step.c_op_2 (ab2 a0 a1 v) (Step.c_ab2_1 a3 a2 hv))).tail (Step.c_op_2 (ab2 a0 a1 v) (Step.c_ab2_3 v a3 hv))).tail (root_step .r11 a0 a1 v a3))⟩
theorem vp_11_21 (a0 a1 a2 a3 v : T) (hv : Step a2 v) :
    Join (ab2 (op a0 (rd a2 a1)) a2 (ab2 a2 a3 a2)) (op (ab2 a0 a1 a2) (ab2 v a3 a2)) := by
  exact ⟨(ab2 (op a0 (rd v a1)) v (ab2 v a3 v)), (((((Relation.ReflTransGen.refl).tail (Step.c_ab2_1 a2 (ab2 a2 a3 a2) (Step.c_op_2 a0 (Step.c_rd_1 a1 hv)))).tail (Step.c_ab2_2 (op a0 (rd v a1)) (ab2 a2 a3 a2) hv)).tail (Step.c_ab2_3 (op a0 (rd v a1)) v (Step.c_ab2_1 a3 a2 hv))).tail (Step.c_ab2_3 (op a0 (rd v a1)) v (Step.c_ab2_3 v a3 hv))), ((((Relation.ReflTransGen.refl).tail (Step.c_op_1 (ab2 v a3 a2) (Step.c_ab2_3 a0 a1 hv))).tail (Step.c_op_2 (ab2 a0 a1 v) (Step.c_ab2_3 v a3 hv))).tail (root_step .r11 a0 a1 v a3))⟩
theorem vp_11_22 (a0 a1 a2 a3 v : T) (hv : Step a3 v) :
    Join (ab2 (op a0 (rd a2 a1)) a2 (ab2 a2 a3 a2)) (op (ab2 a0 a1 a2) (ab2 a2 v a2)) := by
  exact ⟨(ab2 (op a0 (rd a2 a1)) a2 (ab2 a2 v a2)), ((Relation.ReflTransGen.refl).tail (Step.c_ab2_3 (op a0 (rd a2 a1)) a2 (Step.c_ab2_2 a2 a2 hv))), ((Relation.ReflTransGen.refl).tail (root_step .r11 a0 a1 a2 v))⟩
theorem vp_11_23 (a0 a1 a2 a3 v : T) (hv : Step a2 v) :
    Join (ab2 (op a0 (rd a2 a1)) a2 (ab2 a2 a3 a2)) (op (ab2 a0 a1 a2) (ab2 a2 a3 v)) := by
  exact ⟨(ab2 (op a0 (rd v a1)) v (ab2 v a3 v)), (((((Relation.ReflTransGen.refl).tail (Step.c_ab2_1 a2 (ab2 a2 a3 a2) (Step.c_op_2 a0 (Step.c_rd_1 a1 hv)))).tail (Step.c_ab2_2 (op a0 (rd v a1)) (ab2 a2 a3 a2) hv)).tail (Step.c_ab2_3 (op a0 (rd v a1)) v (Step.c_ab2_1 a3 a2 hv))).tail (Step.c_ab2_3 (op a0 (rd v a1)) v (Step.c_ab2_3 v a3 hv))), ((((Relation.ReflTransGen.refl).tail (Step.c_op_1 (ab2 a2 a3 v) (Step.c_ab2_3 a0 a1 hv))).tail (Step.c_op_2 (ab2 a0 a1 v) (Step.c_ab2_1 a3 v hv))).tail (root_step .r11 a0 a1 v a3))⟩
theorem vp_12_1 (a0 a1 a2 a3 v : T) (hv : Step a0 v) :
    Join (ab2 a2 (ab2 a0 a1 a2) (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2))) (op v (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2))) := by
  exact ⟨(ab2 a2 (ab2 v a1 a2) (ab2 (ab2 v a1 a2) a3 (ab2 v a1 a2))), ((((Relation.ReflTransGen.refl).tail (Step.c_ab2_2 a2 (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2)) (Step.c_ab2_1 a1 a2 hv))).tail (Step.c_ab2_3 a2 (ab2 v a1 a2) (Step.c_ab2_1 a3 (ab2 a0 a1 a2) (Step.c_ab2_1 a1 a2 hv)))).tail (Step.c_ab2_3 a2 (ab2 v a1 a2) (Step.c_ab2_3 (ab2 v a1 a2) a3 (Step.c_ab2_1 a1 a2 hv)))), ((((Relation.ReflTransGen.refl).tail (Step.c_op_2 v (Step.c_ab2_1 a3 (ab2 a0 a1 a2) (Step.c_ab2_1 a1 a2 hv)))).tail (Step.c_op_2 v (Step.c_ab2_3 (ab2 v a1 a2) a3 (Step.c_ab2_1 a1 a2 hv)))).tail (root_step .r12 v a1 a2 a3))⟩
theorem vp_12_211 (a0 a1 a2 a3 v : T) (hv : Step a0 v) :
    Join (ab2 a2 (ab2 a0 a1 a2) (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2))) (op a0 (ab2 (ab2 v a1 a2) a3 (ab2 a0 a1 a2))) := by
  exact ⟨(ab2 a2 (ab2 v a1 a2) (ab2 (ab2 v a1 a2) a3 (ab2 v a1 a2))), ((((Relation.ReflTransGen.refl).tail (Step.c_ab2_2 a2 (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2)) (Step.c_ab2_1 a1 a2 hv))).tail (Step.c_ab2_3 a2 (ab2 v a1 a2) (Step.c_ab2_1 a3 (ab2 a0 a1 a2) (Step.c_ab2_1 a1 a2 hv)))).tail (Step.c_ab2_3 a2 (ab2 v a1 a2) (Step.c_ab2_3 (ab2 v a1 a2) a3 (Step.c_ab2_1 a1 a2 hv)))), ((((Relation.ReflTransGen.refl).tail (Step.c_op_1 (ab2 (ab2 v a1 a2) a3 (ab2 a0 a1 a2)) hv)).tail (Step.c_op_2 v (Step.c_ab2_3 (ab2 v a1 a2) a3 (Step.c_ab2_1 a1 a2 hv)))).tail (root_step .r12 v a1 a2 a3))⟩
theorem vp_12_212 (a0 a1 a2 a3 v : T) (hv : Step a1 v) :
    Join (ab2 a2 (ab2 a0 a1 a2) (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2))) (op a0 (ab2 (ab2 a0 v a2) a3 (ab2 a0 a1 a2))) := by
  exact ⟨(ab2 a2 (ab2 a0 v a2) (ab2 (ab2 a0 v a2) a3 (ab2 a0 v a2))), ((((Relation.ReflTransGen.refl).tail (Step.c_ab2_2 a2 (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2)) (Step.c_ab2_2 a0 a2 hv))).tail (Step.c_ab2_3 a2 (ab2 a0 v a2) (Step.c_ab2_1 a3 (ab2 a0 a1 a2) (Step.c_ab2_2 a0 a2 hv)))).tail (Step.c_ab2_3 a2 (ab2 a0 v a2) (Step.c_ab2_3 (ab2 a0 v a2) a3 (Step.c_ab2_2 a0 a2 hv)))), (((Relation.ReflTransGen.refl).tail (Step.c_op_2 a0 (Step.c_ab2_3 (ab2 a0 v a2) a3 (Step.c_ab2_2 a0 a2 hv)))).tail (root_step .r12 a0 v a2 a3))⟩
theorem vp_12_213 (a0 a1 a2 a3 v : T) (hv : Step a2 v) :
    Join (ab2 a2 (ab2 a0 a1 a2) (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2))) (op a0 (ab2 (ab2 a0 a1 v) a3 (ab2 a0 a1 a2))) := by
  exact ⟨(ab2 v (ab2 a0 a1 v) (ab2 (ab2 a0 a1 v) a3 (ab2 a0 a1 v))), (((((Relation.ReflTransGen.refl).tail (Step.c_ab2_1 (ab2 a0 a1 a2) (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2)) hv)).tail (Step.c_ab2_2 v (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2)) (Step.c_ab2_3 a0 a1 hv))).tail (Step.c_ab2_3 v (ab2 a0 a1 v) (Step.c_ab2_1 a3 (ab2 a0 a1 a2) (Step.c_ab2_3 a0 a1 hv)))).tail (Step.c_ab2_3 v (ab2 a0 a1 v) (Step.c_ab2_3 (ab2 a0 a1 v) a3 (Step.c_ab2_3 a0 a1 hv)))), (((Relation.ReflTransGen.refl).tail (Step.c_op_2 a0 (Step.c_ab2_3 (ab2 a0 a1 v) a3 (Step.c_ab2_3 a0 a1 hv)))).tail (root_step .r12 a0 a1 v a3))⟩
theorem vp_12_22 (a0 a1 a2 a3 v : T) (hv : Step a3 v) :
    Join (ab2 a2 (ab2 a0 a1 a2) (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2))) (op a0 (ab2 (ab2 a0 a1 a2) v (ab2 a0 a1 a2))) := by
  exact ⟨(ab2 a2 (ab2 a0 a1 a2) (ab2 (ab2 a0 a1 a2) v (ab2 a0 a1 a2))), ((Relation.ReflTransGen.refl).tail (Step.c_ab2_3 a2 (ab2 a0 a1 a2) (Step.c_ab2_2 (ab2 a0 a1 a2) (ab2 a0 a1 a2) hv))), ((Relation.ReflTransGen.refl).tail (root_step .r12 a0 a1 a2 v))⟩
theorem vp_12_231 (a0 a1 a2 a3 v : T) (hv : Step a0 v) :
    Join (ab2 a2 (ab2 a0 a1 a2) (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2))) (op a0 (ab2 (ab2 a0 a1 a2) a3 (ab2 v a1 a2))) := by
  exact ⟨(ab2 a2 (ab2 v a1 a2) (ab2 (ab2 v a1 a2) a3 (ab2 v a1 a2))), ((((Relation.ReflTransGen.refl).tail (Step.c_ab2_2 a2 (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2)) (Step.c_ab2_1 a1 a2 hv))).tail (Step.c_ab2_3 a2 (ab2 v a1 a2) (Step.c_ab2_1 a3 (ab2 a0 a1 a2) (Step.c_ab2_1 a1 a2 hv)))).tail (Step.c_ab2_3 a2 (ab2 v a1 a2) (Step.c_ab2_3 (ab2 v a1 a2) a3 (Step.c_ab2_1 a1 a2 hv)))), ((((Relation.ReflTransGen.refl).tail (Step.c_op_1 (ab2 (ab2 a0 a1 a2) a3 (ab2 v a1 a2)) hv)).tail (Step.c_op_2 v (Step.c_ab2_1 a3 (ab2 v a1 a2) (Step.c_ab2_1 a1 a2 hv)))).tail (root_step .r12 v a1 a2 a3))⟩
theorem vp_12_232 (a0 a1 a2 a3 v : T) (hv : Step a1 v) :
    Join (ab2 a2 (ab2 a0 a1 a2) (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2))) (op a0 (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 v a2))) := by
  exact ⟨(ab2 a2 (ab2 a0 v a2) (ab2 (ab2 a0 v a2) a3 (ab2 a0 v a2))), ((((Relation.ReflTransGen.refl).tail (Step.c_ab2_2 a2 (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2)) (Step.c_ab2_2 a0 a2 hv))).tail (Step.c_ab2_3 a2 (ab2 a0 v a2) (Step.c_ab2_1 a3 (ab2 a0 a1 a2) (Step.c_ab2_2 a0 a2 hv)))).tail (Step.c_ab2_3 a2 (ab2 a0 v a2) (Step.c_ab2_3 (ab2 a0 v a2) a3 (Step.c_ab2_2 a0 a2 hv)))), (((Relation.ReflTransGen.refl).tail (Step.c_op_2 a0 (Step.c_ab2_1 a3 (ab2 a0 v a2) (Step.c_ab2_2 a0 a2 hv)))).tail (root_step .r12 a0 v a2 a3))⟩
theorem vp_12_233 (a0 a1 a2 a3 v : T) (hv : Step a2 v) :
    Join (ab2 a2 (ab2 a0 a1 a2) (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2))) (op a0 (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 v))) := by
  exact ⟨(ab2 v (ab2 a0 a1 v) (ab2 (ab2 a0 a1 v) a3 (ab2 a0 a1 v))), (((((Relation.ReflTransGen.refl).tail (Step.c_ab2_1 (ab2 a0 a1 a2) (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2)) hv)).tail (Step.c_ab2_2 v (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2)) (Step.c_ab2_3 a0 a1 hv))).tail (Step.c_ab2_3 v (ab2 a0 a1 v) (Step.c_ab2_1 a3 (ab2 a0 a1 a2) (Step.c_ab2_3 a0 a1 hv)))).tail (Step.c_ab2_3 v (ab2 a0 a1 v) (Step.c_ab2_3 (ab2 a0 a1 v) a3 (Step.c_ab2_3 a0 a1 hv)))), (((Relation.ReflTransGen.refl).tail (Step.c_op_2 a0 (Step.c_ab2_1 a3 (ab2 a0 a1 v) (Step.c_ab2_3 a0 a1 hv)))).tail (root_step .r12 a0 a1 v a3))⟩
theorem peak_0 (a0 a1 a2 a3 : T) {u : T} (h : Step (op (op a0 a1) a1) u) :
    Join (rd a1 a0) u := by
  rcases step_op_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
  · rcases hr with ⟨k, b0, b1, b2, b3, heq, rfl⟩
    cases k with
    | r0 => exact cp_0_root_0 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r1 => exact cp_0_root_1 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r2 => exact cp_0_root_2 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r3 => exact cp_0_root_3 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r4 => exact cp_0_root_4 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r5 => exact cp_0_root_5 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r6 => exact cp_0_root_6 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r7 => exact cp_0_root_7 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r8 => exact cp_0_root_8 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r9 => exact cp_0_root_9 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r10 => exact cp_0_root_10 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r11 => exact cp_0_root_11 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r12 => exact cp_0_root_12 a0 a1 a2 a3 b0 b1 b2 b3 heq
  ·
    rcases step_op_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
    · rcases hr with ⟨k, b0, b1, b2, b3, heq, rfl⟩
      cases k with
      | r0 => exact cp_0_1_0 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r1 => exact cp_0_1_1 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r2 => exact cp_0_1_2 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r3 => exact cp_0_1_3 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r4 => exact cp_0_1_4 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r5 => exact cp_0_1_5 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r6 => exact cp_0_1_6 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r7 => exact cp_0_1_7 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r8 => exact cp_0_1_8 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r9 => exact cp_0_1_9 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r10 => exact cp_0_1_10 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r11 => exact cp_0_1_11 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r12 => exact cp_0_1_12 a0 a1 a2 a3 b0 b1 b2 b3 heq
    ·
      exact vp_0_11 a0 a1 a2 a3 u1 h1
    ·
      exact vp_0_12 a0 a1 a2 a3 u1 h1
  ·
    exact vp_0_2 a0 a1 a2 a3 u0 h0
theorem peak_1 (a0 a1 a2 a3 : T) {u : T} (h : Step (op (rd a0 a1) a0) u) :
    Join (rd a0 (op a1 a0)) u := by
  rcases step_op_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
  · rcases hr with ⟨k, b0, b1, b2, b3, heq, rfl⟩
    cases k with
    | r0 => exact cp_1_root_0 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r1 => exact cp_1_root_1 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r2 => exact cp_1_root_2 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r3 => exact cp_1_root_3 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r4 => exact cp_1_root_4 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r5 => exact cp_1_root_5 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r6 => exact cp_1_root_6 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r7 => exact cp_1_root_7 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r8 => exact cp_1_root_8 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r9 => exact cp_1_root_9 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r10 => exact cp_1_root_10 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r11 => exact cp_1_root_11 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r12 => exact cp_1_root_12 a0 a1 a2 a3 b0 b1 b2 b3 heq
  ·
    rcases step_rd_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
    · rcases hr with ⟨k, b0, b1, b2, b3, heq, rfl⟩
      cases k with
      | r0 => exact cp_1_1_0 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r1 => exact cp_1_1_1 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r2 => exact cp_1_1_2 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r3 => exact cp_1_1_3 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r4 => exact cp_1_1_4 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r5 => exact cp_1_1_5 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r6 => exact cp_1_1_6 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r7 => exact cp_1_1_7 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r8 => exact cp_1_1_8 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r9 => exact cp_1_1_9 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r10 => exact cp_1_1_10 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r11 => exact cp_1_1_11 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r12 => exact cp_1_1_12 a0 a1 a2 a3 b0 b1 b2 b3 heq
    ·
      exact vp_1_11 a0 a1 a2 a3 u1 h1
    ·
      exact vp_1_12 a0 a1 a2 a3 u1 h1
  ·
    exact vp_1_2 a0 a1 a2 a3 u0 h0
theorem peak_2 (a0 a1 a2 a3 : T) {u : T} (h : Step (op (op a0 (rd a1 a2)) a1) u) :
    Join (ab2 a0 a2 a1) u := by
  rcases step_op_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
  · rcases hr with ⟨k, b0, b1, b2, b3, heq, rfl⟩
    cases k with
    | r0 => exact cp_2_root_0 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r1 => exact cp_2_root_1 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r2 => exact cp_2_root_2 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r3 => exact cp_2_root_3 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r4 => exact cp_2_root_4 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r5 => exact cp_2_root_5 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r6 => exact cp_2_root_6 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r7 => exact cp_2_root_7 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r8 => exact cp_2_root_8 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r9 => exact cp_2_root_9 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r10 => exact cp_2_root_10 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r11 => exact cp_2_root_11 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r12 => exact cp_2_root_12 a0 a1 a2 a3 b0 b1 b2 b3 heq
  ·
    rcases step_op_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
    · rcases hr with ⟨k, b0, b1, b2, b3, heq, rfl⟩
      cases k with
      | r0 => exact cp_2_1_0 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r1 => exact cp_2_1_1 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r2 => exact cp_2_1_2 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r3 => exact cp_2_1_3 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r4 => exact cp_2_1_4 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r5 => exact cp_2_1_5 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r6 => exact cp_2_1_6 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r7 => exact cp_2_1_7 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r8 => exact cp_2_1_8 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r9 => exact cp_2_1_9 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r10 => exact cp_2_1_10 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r11 => exact cp_2_1_11 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r12 => exact cp_2_1_12 a0 a1 a2 a3 b0 b1 b2 b3 heq
    ·
      exact vp_2_11 a0 a1 a2 a3 u1 h1
    ·
      rcases step_rd_cases h1 with hr | ⟨u2, rfl, h2⟩ | ⟨u2, rfl, h2⟩
      · rcases hr with ⟨k, b0, b1, b2, b3, heq, rfl⟩
        cases k with
        | r0 => exact cp_2_12_0 a0 a1 a2 a3 b0 b1 b2 b3 heq
        | r1 => exact cp_2_12_1 a0 a1 a2 a3 b0 b1 b2 b3 heq
        | r2 => exact cp_2_12_2 a0 a1 a2 a3 b0 b1 b2 b3 heq
        | r3 => exact cp_2_12_3 a0 a1 a2 a3 b0 b1 b2 b3 heq
        | r4 => exact cp_2_12_4 a0 a1 a2 a3 b0 b1 b2 b3 heq
        | r5 => exact cp_2_12_5 a0 a1 a2 a3 b0 b1 b2 b3 heq
        | r6 => exact cp_2_12_6 a0 a1 a2 a3 b0 b1 b2 b3 heq
        | r7 => exact cp_2_12_7 a0 a1 a2 a3 b0 b1 b2 b3 heq
        | r8 => exact cp_2_12_8 a0 a1 a2 a3 b0 b1 b2 b3 heq
        | r9 => exact cp_2_12_9 a0 a1 a2 a3 b0 b1 b2 b3 heq
        | r10 => exact cp_2_12_10 a0 a1 a2 a3 b0 b1 b2 b3 heq
        | r11 => exact cp_2_12_11 a0 a1 a2 a3 b0 b1 b2 b3 heq
        | r12 => exact cp_2_12_12 a0 a1 a2 a3 b0 b1 b2 b3 heq
      ·
        exact vp_2_121 a0 a1 a2 a3 u2 h2
      ·
        exact vp_2_122 a0 a1 a2 a3 u2 h2
  ·
    exact vp_2_2 a0 a1 a2 a3 u0 h0
theorem peak_3 (a0 a1 a2 a3 : T) {u : T} (h : Step (op a0 (ab2 a1 a2 a0)) u) :
    Join a1 u := by
  rcases step_op_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
  · rcases hr with ⟨k, b0, b1, b2, b3, heq, rfl⟩
    cases k with
    | r0 => exact cp_3_root_0 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r1 => exact cp_3_root_1 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r2 => exact cp_3_root_2 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r3 => exact cp_3_root_3 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r4 => exact cp_3_root_4 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r5 => exact cp_3_root_5 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r6 => exact cp_3_root_6 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r7 => exact cp_3_root_7 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r8 => exact cp_3_root_8 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r9 => exact cp_3_root_9 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r10 => exact cp_3_root_10 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r11 => exact cp_3_root_11 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r12 => exact cp_3_root_12 a0 a1 a2 a3 b0 b1 b2 b3 heq
  ·
    exact vp_3_1 a0 a1 a2 a3 u0 h0
  ·
    rcases step_ab2_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
    · rcases hr with ⟨k, b0, b1, b2, b3, heq, rfl⟩
      cases k with
      | r0 => exact cp_3_2_0 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r1 => exact cp_3_2_1 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r2 => exact cp_3_2_2 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r3 => exact cp_3_2_3 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r4 => exact cp_3_2_4 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r5 => exact cp_3_2_5 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r6 => exact cp_3_2_6 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r7 => exact cp_3_2_7 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r8 => exact cp_3_2_8 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r9 => exact cp_3_2_9 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r10 => exact cp_3_2_10 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r11 => exact cp_3_2_11 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r12 => exact cp_3_2_12 a0 a1 a2 a3 b0 b1 b2 b3 heq
    ·
      exact vp_3_21 a0 a1 a2 a3 u1 h1
    ·
      exact vp_3_22 a0 a1 a2 a3 u1 h1
    ·
      exact vp_3_23 a0 a1 a2 a3 u1 h1
theorem peak_4 (a0 a1 a2 a3 : T) {u : T} (h : Step (op a0 (ab2 a0 a1 a2)) u) :
    Join (rd (ab2 a0 a1 a2) a2) u := by
  rcases step_op_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
  · rcases hr with ⟨k, b0, b1, b2, b3, heq, rfl⟩
    cases k with
    | r0 => exact cp_4_root_0 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r1 => exact cp_4_root_1 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r2 => exact cp_4_root_2 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r3 => exact cp_4_root_3 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r4 => exact cp_4_root_4 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r5 => exact cp_4_root_5 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r6 => exact cp_4_root_6 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r7 => exact cp_4_root_7 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r8 => exact cp_4_root_8 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r9 => exact cp_4_root_9 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r10 => exact cp_4_root_10 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r11 => exact cp_4_root_11 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r12 => exact cp_4_root_12 a0 a1 a2 a3 b0 b1 b2 b3 heq
  ·
    exact vp_4_1 a0 a1 a2 a3 u0 h0
  ·
    rcases step_ab2_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
    · rcases hr with ⟨k, b0, b1, b2, b3, heq, rfl⟩
      cases k with
      | r0 => exact cp_4_2_0 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r1 => exact cp_4_2_1 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r2 => exact cp_4_2_2 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r3 => exact cp_4_2_3 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r4 => exact cp_4_2_4 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r5 => exact cp_4_2_5 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r6 => exact cp_4_2_6 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r7 => exact cp_4_2_7 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r8 => exact cp_4_2_8 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r9 => exact cp_4_2_9 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r10 => exact cp_4_2_10 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r11 => exact cp_4_2_11 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r12 => exact cp_4_2_12 a0 a1 a2 a3 b0 b1 b2 b3 heq
    ·
      exact vp_4_21 a0 a1 a2 a3 u1 h1
    ·
      exact vp_4_22 a0 a1 a2 a3 u1 h1
    ·
      exact vp_4_23 a0 a1 a2 a3 u1 h1
theorem peak_5 (a0 a1 a2 a3 : T) {u : T} (h : Step (rd (ab2 a0 a1 a0) a0) u) :
    Join a0 u := by
  rcases step_rd_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
  · rcases hr with ⟨k, b0, b1, b2, b3, heq, rfl⟩
    cases k with
    | r0 => exact cp_5_root_0 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r1 => exact cp_5_root_1 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r2 => exact cp_5_root_2 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r3 => exact cp_5_root_3 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r4 => exact cp_5_root_4 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r5 => exact cp_5_root_5 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r6 => exact cp_5_root_6 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r7 => exact cp_5_root_7 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r8 => exact cp_5_root_8 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r9 => exact cp_5_root_9 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r10 => exact cp_5_root_10 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r11 => exact cp_5_root_11 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r12 => exact cp_5_root_12 a0 a1 a2 a3 b0 b1 b2 b3 heq
  ·
    rcases step_ab2_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
    · rcases hr with ⟨k, b0, b1, b2, b3, heq, rfl⟩
      cases k with
      | r0 => exact cp_5_1_0 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r1 => exact cp_5_1_1 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r2 => exact cp_5_1_2 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r3 => exact cp_5_1_3 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r4 => exact cp_5_1_4 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r5 => exact cp_5_1_5 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r6 => exact cp_5_1_6 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r7 => exact cp_5_1_7 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r8 => exact cp_5_1_8 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r9 => exact cp_5_1_9 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r10 => exact cp_5_1_10 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r11 => exact cp_5_1_11 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r12 => exact cp_5_1_12 a0 a1 a2 a3 b0 b1 b2 b3 heq
    ·
      exact vp_5_11 a0 a1 a2 a3 u1 h1
    ·
      exact vp_5_12 a0 a1 a2 a3 u1 h1
    ·
      exact vp_5_13 a0 a1 a2 a3 u1 h1
  ·
    exact vp_5_2 a0 a1 a2 a3 u0 h0
theorem peak_6 (a0 a1 a2 a3 : T) {u : T} (h : Step (op (ab2 a0 a1 a2) a2) u) :
    Join (rd a2 (op a0 (rd a2 a1))) u := by
  rcases step_op_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
  · rcases hr with ⟨k, b0, b1, b2, b3, heq, rfl⟩
    cases k with
    | r0 => exact cp_6_root_0 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r1 => exact cp_6_root_1 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r2 => exact cp_6_root_2 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r3 => exact cp_6_root_3 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r4 => exact cp_6_root_4 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r5 => exact cp_6_root_5 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r6 => exact cp_6_root_6 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r7 => exact cp_6_root_7 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r8 => exact cp_6_root_8 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r9 => exact cp_6_root_9 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r10 => exact cp_6_root_10 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r11 => exact cp_6_root_11 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r12 => exact cp_6_root_12 a0 a1 a2 a3 b0 b1 b2 b3 heq
  ·
    rcases step_ab2_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
    · rcases hr with ⟨k, b0, b1, b2, b3, heq, rfl⟩
      cases k with
      | r0 => exact cp_6_1_0 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r1 => exact cp_6_1_1 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r2 => exact cp_6_1_2 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r3 => exact cp_6_1_3 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r4 => exact cp_6_1_4 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r5 => exact cp_6_1_5 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r6 => exact cp_6_1_6 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r7 => exact cp_6_1_7 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r8 => exact cp_6_1_8 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r9 => exact cp_6_1_9 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r10 => exact cp_6_1_10 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r11 => exact cp_6_1_11 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r12 => exact cp_6_1_12 a0 a1 a2 a3 b0 b1 b2 b3 heq
    ·
      exact vp_6_11 a0 a1 a2 a3 u1 h1
    ·
      exact vp_6_12 a0 a1 a2 a3 u1 h1
    ·
      exact vp_6_13 a0 a1 a2 a3 u1 h1
  ·
    exact vp_6_2 a0 a1 a2 a3 u0 h0
theorem peak_7 (a0 a1 a2 a3 : T) {u : T} (h : Step (op (op a0 a1) (ab2 a1 a2 a1)) u) :
    Join (ab2 a0 a1 (ab2 a1 a2 a1)) u := by
  rcases step_op_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
  · rcases hr with ⟨k, b0, b1, b2, b3, heq, rfl⟩
    cases k with
    | r0 => exact cp_7_root_0 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r1 => exact cp_7_root_1 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r2 => exact cp_7_root_2 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r3 => exact cp_7_root_3 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r4 => exact cp_7_root_4 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r5 => exact cp_7_root_5 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r6 => exact cp_7_root_6 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r7 => exact cp_7_root_7 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r8 => exact cp_7_root_8 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r9 => exact cp_7_root_9 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r10 => exact cp_7_root_10 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r11 => exact cp_7_root_11 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r12 => exact cp_7_root_12 a0 a1 a2 a3 b0 b1 b2 b3 heq
  ·
    rcases step_op_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
    · rcases hr with ⟨k, b0, b1, b2, b3, heq, rfl⟩
      cases k with
      | r0 => exact cp_7_1_0 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r1 => exact cp_7_1_1 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r2 => exact cp_7_1_2 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r3 => exact cp_7_1_3 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r4 => exact cp_7_1_4 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r5 => exact cp_7_1_5 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r6 => exact cp_7_1_6 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r7 => exact cp_7_1_7 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r8 => exact cp_7_1_8 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r9 => exact cp_7_1_9 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r10 => exact cp_7_1_10 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r11 => exact cp_7_1_11 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r12 => exact cp_7_1_12 a0 a1 a2 a3 b0 b1 b2 b3 heq
    ·
      exact vp_7_11 a0 a1 a2 a3 u1 h1
    ·
      exact vp_7_12 a0 a1 a2 a3 u1 h1
  ·
    rcases step_ab2_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
    · rcases hr with ⟨k, b0, b1, b2, b3, heq, rfl⟩
      cases k with
      | r0 => exact cp_7_2_0 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r1 => exact cp_7_2_1 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r2 => exact cp_7_2_2 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r3 => exact cp_7_2_3 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r4 => exact cp_7_2_4 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r5 => exact cp_7_2_5 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r6 => exact cp_7_2_6 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r7 => exact cp_7_2_7 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r8 => exact cp_7_2_8 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r9 => exact cp_7_2_9 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r10 => exact cp_7_2_10 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r11 => exact cp_7_2_11 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r12 => exact cp_7_2_12 a0 a1 a2 a3 b0 b1 b2 b3 heq
    ·
      exact vp_7_21 a0 a1 a2 a3 u1 h1
    ·
      exact vp_7_22 a0 a1 a2 a3 u1 h1
    ·
      exact vp_7_23 a0 a1 a2 a3 u1 h1
theorem peak_8 (a0 a1 a2 a3 : T) {u : T} (h : Step (op (rd (rd a0 a1) a2) a0) u) :
    Join (ab2 (op a2 (rd a0 a1)) a1 a0) u := by
  rcases step_op_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
  · rcases hr with ⟨k, b0, b1, b2, b3, heq, rfl⟩
    cases k with
    | r0 => exact cp_8_root_0 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r1 => exact cp_8_root_1 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r2 => exact cp_8_root_2 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r3 => exact cp_8_root_3 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r4 => exact cp_8_root_4 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r5 => exact cp_8_root_5 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r6 => exact cp_8_root_6 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r7 => exact cp_8_root_7 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r8 => exact cp_8_root_8 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r9 => exact cp_8_root_9 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r10 => exact cp_8_root_10 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r11 => exact cp_8_root_11 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r12 => exact cp_8_root_12 a0 a1 a2 a3 b0 b1 b2 b3 heq
  ·
    rcases step_rd_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
    · rcases hr with ⟨k, b0, b1, b2, b3, heq, rfl⟩
      cases k with
      | r0 => exact cp_8_1_0 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r1 => exact cp_8_1_1 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r2 => exact cp_8_1_2 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r3 => exact cp_8_1_3 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r4 => exact cp_8_1_4 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r5 => exact cp_8_1_5 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r6 => exact cp_8_1_6 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r7 => exact cp_8_1_7 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r8 => exact cp_8_1_8 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r9 => exact cp_8_1_9 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r10 => exact cp_8_1_10 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r11 => exact cp_8_1_11 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r12 => exact cp_8_1_12 a0 a1 a2 a3 b0 b1 b2 b3 heq
    ·
      rcases step_rd_cases h1 with hr | ⟨u2, rfl, h2⟩ | ⟨u2, rfl, h2⟩
      · rcases hr with ⟨k, b0, b1, b2, b3, heq, rfl⟩
        cases k with
        | r0 => exact cp_8_11_0 a0 a1 a2 a3 b0 b1 b2 b3 heq
        | r1 => exact cp_8_11_1 a0 a1 a2 a3 b0 b1 b2 b3 heq
        | r2 => exact cp_8_11_2 a0 a1 a2 a3 b0 b1 b2 b3 heq
        | r3 => exact cp_8_11_3 a0 a1 a2 a3 b0 b1 b2 b3 heq
        | r4 => exact cp_8_11_4 a0 a1 a2 a3 b0 b1 b2 b3 heq
        | r5 => exact cp_8_11_5 a0 a1 a2 a3 b0 b1 b2 b3 heq
        | r6 => exact cp_8_11_6 a0 a1 a2 a3 b0 b1 b2 b3 heq
        | r7 => exact cp_8_11_7 a0 a1 a2 a3 b0 b1 b2 b3 heq
        | r8 => exact cp_8_11_8 a0 a1 a2 a3 b0 b1 b2 b3 heq
        | r9 => exact cp_8_11_9 a0 a1 a2 a3 b0 b1 b2 b3 heq
        | r10 => exact cp_8_11_10 a0 a1 a2 a3 b0 b1 b2 b3 heq
        | r11 => exact cp_8_11_11 a0 a1 a2 a3 b0 b1 b2 b3 heq
        | r12 => exact cp_8_11_12 a0 a1 a2 a3 b0 b1 b2 b3 heq
      ·
        exact vp_8_111 a0 a1 a2 a3 u2 h2
      ·
        exact vp_8_112 a0 a1 a2 a3 u2 h2
    ·
      exact vp_8_12 a0 a1 a2 a3 u1 h1
  ·
    exact vp_8_2 a0 a1 a2 a3 u0 h0
theorem peak_9 (a0 a1 a2 a3 : T) {u : T} (h : Step (op (rd a0 a1) (ab2 a0 a2 a0)) u) :
    Join (ab2 (op a1 a0) a0 (ab2 a0 a2 a0)) u := by
  rcases step_op_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
  · rcases hr with ⟨k, b0, b1, b2, b3, heq, rfl⟩
    cases k with
    | r0 => exact cp_9_root_0 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r1 => exact cp_9_root_1 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r2 => exact cp_9_root_2 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r3 => exact cp_9_root_3 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r4 => exact cp_9_root_4 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r5 => exact cp_9_root_5 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r6 => exact cp_9_root_6 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r7 => exact cp_9_root_7 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r8 => exact cp_9_root_8 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r9 => exact cp_9_root_9 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r10 => exact cp_9_root_10 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r11 => exact cp_9_root_11 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r12 => exact cp_9_root_12 a0 a1 a2 a3 b0 b1 b2 b3 heq
  ·
    rcases step_rd_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
    · rcases hr with ⟨k, b0, b1, b2, b3, heq, rfl⟩
      cases k with
      | r0 => exact cp_9_1_0 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r1 => exact cp_9_1_1 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r2 => exact cp_9_1_2 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r3 => exact cp_9_1_3 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r4 => exact cp_9_1_4 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r5 => exact cp_9_1_5 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r6 => exact cp_9_1_6 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r7 => exact cp_9_1_7 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r8 => exact cp_9_1_8 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r9 => exact cp_9_1_9 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r10 => exact cp_9_1_10 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r11 => exact cp_9_1_11 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r12 => exact cp_9_1_12 a0 a1 a2 a3 b0 b1 b2 b3 heq
    ·
      exact vp_9_11 a0 a1 a2 a3 u1 h1
    ·
      exact vp_9_12 a0 a1 a2 a3 u1 h1
  ·
    rcases step_ab2_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
    · rcases hr with ⟨k, b0, b1, b2, b3, heq, rfl⟩
      cases k with
      | r0 => exact cp_9_2_0 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r1 => exact cp_9_2_1 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r2 => exact cp_9_2_2 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r3 => exact cp_9_2_3 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r4 => exact cp_9_2_4 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r5 => exact cp_9_2_5 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r6 => exact cp_9_2_6 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r7 => exact cp_9_2_7 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r8 => exact cp_9_2_8 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r9 => exact cp_9_2_9 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r10 => exact cp_9_2_10 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r11 => exact cp_9_2_11 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r12 => exact cp_9_2_12 a0 a1 a2 a3 b0 b1 b2 b3 heq
    ·
      exact vp_9_21 a0 a1 a2 a3 u1 h1
    ·
      exact vp_9_22 a0 a1 a2 a3 u1 h1
    ·
      exact vp_9_23 a0 a1 a2 a3 u1 h1
theorem peak_10 (a0 a1 a2 a3 : T) {u : T} (h : Step (op (ab2 a0 a1 (rd a2 a3)) a2) u) :
    Join (ab2 (op a0 (rd (rd a2 a3) a1)) a3 a2) u := by
  rcases step_op_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
  · rcases hr with ⟨k, b0, b1, b2, b3, heq, rfl⟩
    cases k with
    | r0 => exact cp_10_root_0 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r1 => exact cp_10_root_1 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r2 => exact cp_10_root_2 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r3 => exact cp_10_root_3 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r4 => exact cp_10_root_4 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r5 => exact cp_10_root_5 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r6 => exact cp_10_root_6 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r7 => exact cp_10_root_7 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r8 => exact cp_10_root_8 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r9 => exact cp_10_root_9 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r10 => exact cp_10_root_10 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r11 => exact cp_10_root_11 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r12 => exact cp_10_root_12 a0 a1 a2 a3 b0 b1 b2 b3 heq
  ·
    rcases step_ab2_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
    · rcases hr with ⟨k, b0, b1, b2, b3, heq, rfl⟩
      cases k with
      | r0 => exact cp_10_1_0 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r1 => exact cp_10_1_1 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r2 => exact cp_10_1_2 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r3 => exact cp_10_1_3 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r4 => exact cp_10_1_4 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r5 => exact cp_10_1_5 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r6 => exact cp_10_1_6 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r7 => exact cp_10_1_7 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r8 => exact cp_10_1_8 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r9 => exact cp_10_1_9 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r10 => exact cp_10_1_10 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r11 => exact cp_10_1_11 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r12 => exact cp_10_1_12 a0 a1 a2 a3 b0 b1 b2 b3 heq
    ·
      exact vp_10_11 a0 a1 a2 a3 u1 h1
    ·
      exact vp_10_12 a0 a1 a2 a3 u1 h1
    ·
      rcases step_rd_cases h1 with hr | ⟨u2, rfl, h2⟩ | ⟨u2, rfl, h2⟩
      · rcases hr with ⟨k, b0, b1, b2, b3, heq, rfl⟩
        cases k with
        | r0 => exact cp_10_13_0 a0 a1 a2 a3 b0 b1 b2 b3 heq
        | r1 => exact cp_10_13_1 a0 a1 a2 a3 b0 b1 b2 b3 heq
        | r2 => exact cp_10_13_2 a0 a1 a2 a3 b0 b1 b2 b3 heq
        | r3 => exact cp_10_13_3 a0 a1 a2 a3 b0 b1 b2 b3 heq
        | r4 => exact cp_10_13_4 a0 a1 a2 a3 b0 b1 b2 b3 heq
        | r5 => exact cp_10_13_5 a0 a1 a2 a3 b0 b1 b2 b3 heq
        | r6 => exact cp_10_13_6 a0 a1 a2 a3 b0 b1 b2 b3 heq
        | r7 => exact cp_10_13_7 a0 a1 a2 a3 b0 b1 b2 b3 heq
        | r8 => exact cp_10_13_8 a0 a1 a2 a3 b0 b1 b2 b3 heq
        | r9 => exact cp_10_13_9 a0 a1 a2 a3 b0 b1 b2 b3 heq
        | r10 => exact cp_10_13_10 a0 a1 a2 a3 b0 b1 b2 b3 heq
        | r11 => exact cp_10_13_11 a0 a1 a2 a3 b0 b1 b2 b3 heq
        | r12 => exact cp_10_13_12 a0 a1 a2 a3 b0 b1 b2 b3 heq
      ·
        exact vp_10_131 a0 a1 a2 a3 u2 h2
      ·
        exact vp_10_132 a0 a1 a2 a3 u2 h2
  ·
    exact vp_10_2 a0 a1 a2 a3 u0 h0
theorem peak_11 (a0 a1 a2 a3 : T) {u : T} (h : Step (op (ab2 a0 a1 a2) (ab2 a2 a3 a2)) u) :
    Join (ab2 (op a0 (rd a2 a1)) a2 (ab2 a2 a3 a2)) u := by
  rcases step_op_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
  · rcases hr with ⟨k, b0, b1, b2, b3, heq, rfl⟩
    cases k with
    | r0 => exact cp_11_root_0 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r1 => exact cp_11_root_1 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r2 => exact cp_11_root_2 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r3 => exact cp_11_root_3 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r4 => exact cp_11_root_4 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r5 => exact cp_11_root_5 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r6 => exact cp_11_root_6 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r7 => exact cp_11_root_7 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r8 => exact cp_11_root_8 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r9 => exact cp_11_root_9 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r10 => exact cp_11_root_10 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r11 => exact cp_11_root_11 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r12 => exact cp_11_root_12 a0 a1 a2 a3 b0 b1 b2 b3 heq
  ·
    rcases step_ab2_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
    · rcases hr with ⟨k, b0, b1, b2, b3, heq, rfl⟩
      cases k with
      | r0 => exact cp_11_1_0 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r1 => exact cp_11_1_1 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r2 => exact cp_11_1_2 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r3 => exact cp_11_1_3 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r4 => exact cp_11_1_4 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r5 => exact cp_11_1_5 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r6 => exact cp_11_1_6 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r7 => exact cp_11_1_7 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r8 => exact cp_11_1_8 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r9 => exact cp_11_1_9 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r10 => exact cp_11_1_10 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r11 => exact cp_11_1_11 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r12 => exact cp_11_1_12 a0 a1 a2 a3 b0 b1 b2 b3 heq
    ·
      exact vp_11_11 a0 a1 a2 a3 u1 h1
    ·
      exact vp_11_12 a0 a1 a2 a3 u1 h1
    ·
      exact vp_11_13 a0 a1 a2 a3 u1 h1
  ·
    rcases step_ab2_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
    · rcases hr with ⟨k, b0, b1, b2, b3, heq, rfl⟩
      cases k with
      | r0 => exact cp_11_2_0 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r1 => exact cp_11_2_1 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r2 => exact cp_11_2_2 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r3 => exact cp_11_2_3 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r4 => exact cp_11_2_4 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r5 => exact cp_11_2_5 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r6 => exact cp_11_2_6 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r7 => exact cp_11_2_7 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r8 => exact cp_11_2_8 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r9 => exact cp_11_2_9 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r10 => exact cp_11_2_10 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r11 => exact cp_11_2_11 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r12 => exact cp_11_2_12 a0 a1 a2 a3 b0 b1 b2 b3 heq
    ·
      exact vp_11_21 a0 a1 a2 a3 u1 h1
    ·
      exact vp_11_22 a0 a1 a2 a3 u1 h1
    ·
      exact vp_11_23 a0 a1 a2 a3 u1 h1
theorem peak_12 (a0 a1 a2 a3 : T) {u : T} (h : Step (op a0 (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2))) u) :
    Join (ab2 a2 (ab2 a0 a1 a2) (ab2 (ab2 a0 a1 a2) a3 (ab2 a0 a1 a2))) u := by
  rcases step_op_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
  · rcases hr with ⟨k, b0, b1, b2, b3, heq, rfl⟩
    cases k with
    | r0 => exact cp_12_root_0 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r1 => exact cp_12_root_1 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r2 => exact cp_12_root_2 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r3 => exact cp_12_root_3 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r4 => exact cp_12_root_4 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r5 => exact cp_12_root_5 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r6 => exact cp_12_root_6 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r7 => exact cp_12_root_7 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r8 => exact cp_12_root_8 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r9 => exact cp_12_root_9 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r10 => exact cp_12_root_10 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r11 => exact cp_12_root_11 a0 a1 a2 a3 b0 b1 b2 b3 heq
    | r12 => exact cp_12_root_12 a0 a1 a2 a3 b0 b1 b2 b3 heq
  ·
    exact vp_12_1 a0 a1 a2 a3 u0 h0
  ·
    rcases step_ab2_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
    · rcases hr with ⟨k, b0, b1, b2, b3, heq, rfl⟩
      cases k with
      | r0 => exact cp_12_2_0 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r1 => exact cp_12_2_1 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r2 => exact cp_12_2_2 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r3 => exact cp_12_2_3 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r4 => exact cp_12_2_4 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r5 => exact cp_12_2_5 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r6 => exact cp_12_2_6 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r7 => exact cp_12_2_7 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r8 => exact cp_12_2_8 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r9 => exact cp_12_2_9 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r10 => exact cp_12_2_10 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r11 => exact cp_12_2_11 a0 a1 a2 a3 b0 b1 b2 b3 heq
      | r12 => exact cp_12_2_12 a0 a1 a2 a3 b0 b1 b2 b3 heq
    ·
      rcases step_ab2_cases h1 with hr | ⟨u2, rfl, h2⟩ | ⟨u2, rfl, h2⟩ | ⟨u2, rfl, h2⟩
      · rcases hr with ⟨k, b0, b1, b2, b3, heq, rfl⟩
        cases k with
        | r0 => exact cp_12_21_0 a0 a1 a2 a3 b0 b1 b2 b3 heq
        | r1 => exact cp_12_21_1 a0 a1 a2 a3 b0 b1 b2 b3 heq
        | r2 => exact cp_12_21_2 a0 a1 a2 a3 b0 b1 b2 b3 heq
        | r3 => exact cp_12_21_3 a0 a1 a2 a3 b0 b1 b2 b3 heq
        | r4 => exact cp_12_21_4 a0 a1 a2 a3 b0 b1 b2 b3 heq
        | r5 => exact cp_12_21_5 a0 a1 a2 a3 b0 b1 b2 b3 heq
        | r6 => exact cp_12_21_6 a0 a1 a2 a3 b0 b1 b2 b3 heq
        | r7 => exact cp_12_21_7 a0 a1 a2 a3 b0 b1 b2 b3 heq
        | r8 => exact cp_12_21_8 a0 a1 a2 a3 b0 b1 b2 b3 heq
        | r9 => exact cp_12_21_9 a0 a1 a2 a3 b0 b1 b2 b3 heq
        | r10 => exact cp_12_21_10 a0 a1 a2 a3 b0 b1 b2 b3 heq
        | r11 => exact cp_12_21_11 a0 a1 a2 a3 b0 b1 b2 b3 heq
        | r12 => exact cp_12_21_12 a0 a1 a2 a3 b0 b1 b2 b3 heq
      ·
        exact vp_12_211 a0 a1 a2 a3 u2 h2
      ·
        exact vp_12_212 a0 a1 a2 a3 u2 h2
      ·
        exact vp_12_213 a0 a1 a2 a3 u2 h2
    ·
      exact vp_12_22 a0 a1 a2 a3 u1 h1
    ·
      rcases step_ab2_cases h1 with hr | ⟨u2, rfl, h2⟩ | ⟨u2, rfl, h2⟩ | ⟨u2, rfl, h2⟩
      · rcases hr with ⟨k, b0, b1, b2, b3, heq, rfl⟩
        cases k with
        | r0 => exact cp_12_23_0 a0 a1 a2 a3 b0 b1 b2 b3 heq
        | r1 => exact cp_12_23_1 a0 a1 a2 a3 b0 b1 b2 b3 heq
        | r2 => exact cp_12_23_2 a0 a1 a2 a3 b0 b1 b2 b3 heq
        | r3 => exact cp_12_23_3 a0 a1 a2 a3 b0 b1 b2 b3 heq
        | r4 => exact cp_12_23_4 a0 a1 a2 a3 b0 b1 b2 b3 heq
        | r5 => exact cp_12_23_5 a0 a1 a2 a3 b0 b1 b2 b3 heq
        | r6 => exact cp_12_23_6 a0 a1 a2 a3 b0 b1 b2 b3 heq
        | r7 => exact cp_12_23_7 a0 a1 a2 a3 b0 b1 b2 b3 heq
        | r8 => exact cp_12_23_8 a0 a1 a2 a3 b0 b1 b2 b3 heq
        | r9 => exact cp_12_23_9 a0 a1 a2 a3 b0 b1 b2 b3 heq
        | r10 => exact cp_12_23_10 a0 a1 a2 a3 b0 b1 b2 b3 heq
        | r11 => exact cp_12_23_11 a0 a1 a2 a3 b0 b1 b2 b3 heq
        | r12 => exact cp_12_23_12 a0 a1 a2 a3 b0 b1 b2 b3 heq
      ·
        exact vp_12_231 a0 a1 a2 a3 u2 h2
      ·
        exact vp_12_232 a0 a1 a2 a3 u2 h2
      ·
        exact vp_12_233 a0 a1 a2 a3 u2 h2
theorem root_peak {a b c : T} (h : Root a b) (hs : Step a c) : Join b c := by
  rcases h with ⟨k, v0, v1, v2, v3, rfl, rfl⟩
  cases k with
  | r0 => exact peak_0 v0 v1 v2 v3 hs
  | r1 => exact peak_1 v0 v1 v2 v3 hs
  | r2 => exact peak_2 v0 v1 v2 v3 hs
  | r3 => exact peak_3 v0 v1 v2 v3 hs
  | r4 => exact peak_4 v0 v1 v2 v3 hs
  | r5 => exact peak_5 v0 v1 v2 v3 hs
  | r6 => exact peak_6 v0 v1 v2 v3 hs
  | r7 => exact peak_7 v0 v1 v2 v3 hs
  | r8 => exact peak_8 v0 v1 v2 v3 hs
  | r9 => exact peak_9 v0 v1 v2 v3 hs
  | r10 => exact peak_10 v0 v1 v2 v3 hs
  | r11 => exact peak_11 v0 v1 v2 v3 hs
  | r12 => exact peak_12 v0 v1 v2 v3 hs
theorem local_confluence {a b c : T} (h : Step a b) (hs : Step a c) : Join b c := by
  induction h generalizing c with
  | root h => exact root_peak h hs
  | @c_ab2_1 a b x2 x3 h ih =>
    rcases step_ab2_cases hs with hr | ⟨v, rfl, hv⟩ | ⟨v, rfl, hv⟩ | ⟨v, rfl, hv⟩
    · exact join_symm (root_peak hr (Step.c_ab2_1 x2 x3 h))
    · exact join_ab2_1 x2 x3 (ih hv)
    · exact ⟨(ab2 b v x3), .single (Step.c_ab2_2 b x3 hv), .single (Step.c_ab2_1 v x3 h)⟩
    · exact ⟨(ab2 b x2 v), .single (Step.c_ab2_3 b x2 hv), .single (Step.c_ab2_1 x2 v h)⟩
  | @c_ab2_2 a b x1 x3 h ih =>
    rcases step_ab2_cases hs with hr | ⟨v, rfl, hv⟩ | ⟨v, rfl, hv⟩ | ⟨v, rfl, hv⟩
    · exact join_symm (root_peak hr (Step.c_ab2_2 x1 x3 h))
    · exact ⟨(ab2 v b x3), .single (Step.c_ab2_1 b x3 hv), .single (Step.c_ab2_2 v x3 h)⟩
    · exact join_ab2_2 x1 x3 (ih hv)
    · exact ⟨(ab2 x1 b v), .single (Step.c_ab2_3 x1 b hv), .single (Step.c_ab2_2 x1 v h)⟩
  | @c_ab2_3 a b x1 x2 h ih =>
    rcases step_ab2_cases hs with hr | ⟨v, rfl, hv⟩ | ⟨v, rfl, hv⟩ | ⟨v, rfl, hv⟩
    · exact join_symm (root_peak hr (Step.c_ab2_3 x1 x2 h))
    · exact ⟨(ab2 v x2 b), .single (Step.c_ab2_1 x2 b hv), .single (Step.c_ab2_3 v x2 h)⟩
    · exact ⟨(ab2 x1 v b), .single (Step.c_ab2_2 x1 b hv), .single (Step.c_ab2_3 x1 v h)⟩
    · exact join_ab2_3 x1 x2 (ih hv)
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
  | @c_rd_1 a b x2 h ih =>
    rcases step_rd_cases hs with hr | ⟨v, rfl, hv⟩ | ⟨v, rfl, hv⟩
    · exact join_symm (root_peak hr (Step.c_rd_1 x2 h))
    · exact join_rd_1 x2 (ih hv)
    · exact ⟨(rd b v), .single (Step.c_rd_2 b hv), .single (Step.c_rd_1 v h)⟩
  | @c_rd_2 a b x1 h ih =>
    rcases step_rd_cases hs with hr | ⟨v, rfl, hv⟩ | ⟨v, rfl, hv⟩
    · exact join_symm (root_peak hr (Step.c_rd_2 x1 h))
    · exact ⟨(rd v b), .single (Step.c_rd_1 b hv), .single (Step.c_rd_2 v h)⟩
    · exact join_rd_2 x1 (ih hv)
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


theorem source : EquationLHS Carrier := by
  intro x y z
  refine Quotient.inductionOn₃ x y z ?_
  intro a0 a1 a2
  change project a0 = project (op a1 (op (op a0 (op (op a2 a1) a1)) a1))
  exact (project_reach (Relation.ReflTransGen.refl)).trans (project_reach ((((Relation.ReflTransGen.refl).tail (Step.c_op_2 a1 (Step.c_op_1 a1 (Step.c_op_2 a0 (root_step .r0 a2 a1 (leaf 0) (leaf 0)))))).tail (Step.c_op_2 a1 (root_step .r2 a0 a1 a2 (leaf 0)))).tail (root_step .r3 a1 a0 a2 (leaf 0)))).symm
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


def result : Goal := ⟨Carrier, inferInstance, source, nontrivial⟩
end submission
def submission : Goal := submission.result
#print axioms submission

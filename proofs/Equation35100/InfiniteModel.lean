import JudgeProblem
import Lean.Elab.Tactic.Omega
namespace submission

@[reducible] def BaseEquationLHS (G : Type _) [Magma G] : Prop :=
  ∀ («x» : G) («y» : G) («z» : G), «x» = («y» ◇ ((«y» ◇ («x» ◇ «y»)) ◇ («z» ◇ «y»)))

@[reducible] def BaseEquationRHS (G : Type _) [Magma G] : Prop :=
  ∀ («x» : G) («y» : G), «x» = «y»

abbrev BaseGoal : Prop :=
  ∃ (G : Type) (_ : Magma G), BaseEquationLHS G ∧ ¬ BaseEquationRHS G
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace base_model
inductive CM where
  | e : CM
  | k : CM → CM
  | p : CM → CM → CM
deriving DecidableEq
namespace CM
def L : CM → CM | e => e | k _ => e | p a _ => a
def R : CM → CM | e => e | k _ => e | p _ b => b
def U : CM → CM | e => e | k a => a | p _ _ => e
def sz : CM → Nat
  | e => 0
  | k a => sz a + 1
  | p a b => (sz a + 1) + (sz b + 1)
theorem sz_lt_p_left (a b : CM) : sz a < sz (p a b) := by
  change sz a < (sz a + 1) + (sz b + 1)
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self (sz a))
    (Nat.le_add_right (sz a + 1) (sz b + 1))
theorem sz_lt_p_right (a b : CM) : sz b < sz (p a b) := by
  change sz b < (sz a + 1) + (sz b + 1)
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self (sz b))
    (Nat.le_add_left (sz b + 1) (sz a + 1))
mutual
inductive Code : CM → CM → CM → Prop
  | law (x v0 v1 H0 H1 : CM)
      (s0 : Step x v0 H0)
      (s1 : Step v1 v0 H1) : Code v0 (p (p v0 H0) H1) x
inductive Step : CM → CM → CM → Prop
  | raw (a b : CM) : Step a b (p a b)
  | hit {a b o : CM} (h : Code a b o) : Step a b o
end
theorem code_shape {a b o : CM} (h : Code a b o) :
    ∃ q_x q_v0 q_v1 q_H0 q_H1 : CM, Step q_x q_v0 q_H0 ∧ Step q_v1 q_v0 q_H1 ∧ a = q_v0 ∧ b = (p (p q_v0 q_H0) q_H1) ∧ o = q_x := by
  cases h
  exact ⟨_, _, _, _, _, by assumption, by assumption, rfl, rfl, rfl⟩
def getKey (c : CM) : CM := (L (L c))
theorem code_key {a b o : CM} (h : Code a b o) : getKey b = a := by
  cases h <;> rfl
theorem code_key_small {a b o : CM} (h : Code a b o) : sz a < sz b := by
  cases h <;> simp only [sz] <;> omega
theorem code_bounds {a b o : CM} (h : Code a b o) :
    sz a < sz b ∧ sz o < sz b := by
  constructor
  · exact code_key_small h
  · cases h with
    | law x v0 v1 H0 H1 s0 s1 =>
      cases s0 with
      | raw =>
        cases s1 with
        | raw =>
          simp only [sz] <;> omega
        | hit h1 =>
          have b1 := code_key_small h1
          simp only [sz] at b1 ⊢ <;> omega
      | hit h0 =>
        have b0 := code_key_small h0
        cases s1 with
        | raw =>
          simp only [sz] at b0 ⊢ <;> omega
        | hit h1 =>
          have b1 := code_key_small h1
          simp only [sz] at b0 b1 ⊢ <;> omega
theorem code_key_unique {a b o q : CM} (h : Code a b o) (k : Code q b o) : a = q :=
  (code_key h).symm.trans (code_key k)
theorem step_key_unique {a b o q : CM} (h : Step a b o) (k : Step q b o) : a = q := by
  cases h with
  | raw =>
    cases k with
    | raw => rfl
    | hit hc =>
      have hb := code_bounds hc
      have hp := sz_lt_p_right a b
      exact (Nat.not_lt_of_ge (Nat.le_of_lt hp) hb.2).elim
  | hit hc =>
    cases k with
    | raw =>
      have hb := code_bounds hc
      have hp := sz_lt_p_right q b
      exact (Nat.not_lt_of_ge (Nat.le_of_lt hp) hb.2).elim
    | hit hk => exact code_key_unique hc hk
theorem step_key_transport {a b o qa qb qo : CM}
    (h : Step a b o) (k : Step qa qb qo) (eb : b = qb) (eo : o = qo) : a = qa := by
  subst qb
  subst qo
  exact step_key_unique h k
theorem code_unique {a b o q : CM} (h : Code a b o) (k : Code a b q) : o = q := by
  rcases code_shape h with ⟨x, v0, v1, H0, H1, s0, s1, ha, hb, ho⟩
  rcases code_shape k with ⟨q_x, q_v0, q_v1, q_H0, q_H1, qs0, qs1, ka, kb, ko⟩
  have given0 := ha.symm.trans ka
  have given1 := hb.symm.trans kb
  have fd0 := step_key_transport s0 qs0 (Eq.trans (Eq.trans (Eq.trans (Eq.symm (rfl)) (Eq.trans (given0) (rfl))) (rfl)) (Eq.symm (rfl))) (Eq.trans (Eq.trans (Eq.trans (Eq.symm (rfl)) (Eq.trans (congrArg (fun q => R q) (Eq.trans (Eq.symm (rfl)) (Eq.trans (congrArg (fun q => L q) (Eq.trans (Eq.symm (congrArg (fun q => p q H1) (congrArg (fun q => p q H0) (Eq.trans (Eq.trans (Eq.symm (rfl)) (Eq.trans (given0) (rfl))) (rfl))))) (Eq.trans (given1) (rfl)))) (rfl)))) (rfl))) (rfl)) (Eq.symm (rfl)))
  have fd1 := step_key_transport s1 qs1 (Eq.trans (Eq.trans (Eq.trans (Eq.symm (rfl)) (Eq.trans (given0) (rfl))) (rfl)) (Eq.symm (rfl))) (Eq.trans (Eq.trans (Eq.trans (Eq.symm (rfl)) (Eq.trans (congrArg (fun q => R q) (Eq.trans (Eq.symm (congrArg (fun q => p q H1) (congrArg (fun q => p q H0) (Eq.trans (Eq.trans (Eq.symm (rfl)) (Eq.trans (given0) (rfl))) (rfl))))) (Eq.trans (given1) (rfl)))) (rfl))) (rfl)) (Eq.symm (rfl)))
  exact ho.trans ((Eq.trans (Eq.trans (Eq.trans (Eq.symm (rfl)) (Eq.trans (fd0) (rfl))) (rfl)) (Eq.symm (rfl))).trans ko.symm)

theorem step_bound {a b o : CM} (h : Step a b o) : sz a < sz (p o b) := by
  cases h with
  | raw => simp only [sz]; omega
  | hit hc =>
    have hb := (code_bounds hc).1
    simp only [sz]
    omega

theorem step_ne_second {a b : CM} : ¬ Step a b b := by
  intro h
  cases h with
  | hit hc =>
    have hb := (code_bounds hc).2
    omega

theorem code_no_pair_output {a b c : CM} : ¬ Code a (p b c) b := by
  intro h
  rcases code_shape h with ⟨x, y, z, u, v, s0, s1, ha, hb, ho⟩
  subst x
  subst y
  have he : b = p a u := congrArg L hb
  have hs := step_bound s0
  rw [he] at hs
  simp only [sz] at hs
  omega

theorem step_no_pair_output {a b c : CM} : ¬ Step a (p b c) b := by
  intro h
  cases h with
  | hit hc => exact code_no_pair_output hc

theorem no_code_after {x y u : CM} (st : Step x y u) : ¬ ∃ o, Code y u o := by
  rintro ⟨o, hc⟩
  cases st with
  | raw =>
    rcases code_shape hc with ⟨qx, qy, qz, h0, h1, s0, s1, ha, hb, ho⟩
    have he : y = h1 := congrArg R hb
    have hs : Step qz y y := by simpa only [← ha, ← he] using s1
    exact step_ne_second hs
  | hit hh =>
    have h1 := (code_bounds hc).1
    have h2 := (code_bounds hh).2
    omega

theorem no_code_after_pair {z y v : CM} (u : CM) (st : Step z y v) :
    ¬ ∃ o, Code (p y u) v o := by
  rintro ⟨o, hc⟩
  cases st with
  | raw =>
    rcases code_shape hc with ⟨qx, qy, qz, h0, h1, s0, s1, ha, hb, ho⟩
    have he : y = h1 := congrArg R hb
    have hs : Step qz (p y u) y := by simpa only [← ha, ← he] using s1
    exact step_no_pair_output hs
  | hit hh =>
    have h1 := (code_bounds hc).1
    have h2 := (code_bounds hh).2
    simp only [sz] at h1
    omega

noncomputable def eval (a b : CM) : CM := by
  classical
  exact if h : ∃ o, Code a b o then Classical.choose h else p a b
theorem eval_hit {a b o : CM} (h : Code a b o) : eval a b = o := by
  rw [eval, dif_pos ⟨o, h⟩]
  exact code_unique (Classical.choose_spec ⟨o, h⟩) h
theorem eval_raw {a b : CM} (h : ¬ ∃ o, Code a b o) : eval a b = p a b := by
  rw [eval, dif_neg h]
theorem eval_step (a b : CM) : Step a b (eval a b) := by
  by_cases h : ∃ o, Code a b o
  · rcases h with ⟨o, hc⟩
    rw [eval_hit hc]
    exact Step.hit hc
  · rw [eval_raw h]
    exact Step.raw a b

theorem source_holds (x y z : CM) :
    x = eval y (eval (eval y (eval x y)) (eval z y)) := by
  have sx := eval_step x y
  have sz := eval_step z y
  have h1 := eval_raw (no_code_after sx)
  have h2 := eval_raw (no_code_after_pair (eval x y) sz)
  rw [h1, h2]
  exact (eval_hit (Code.law x y z (eval x y) (eval z y) sx sz)).symm
noncomputable instance instMagma : Magma CM where op := eval
end CM
end base_model
open base_model
noncomputable def base_certificate : BaseGoal := by
  refine ⟨CM, CM.instMagma, ?_, ?_⟩
  · intro x y z
    exact CM.source_holds x y z
  · intro h
    have bad := h CM.e (CM.k CM.e)
    exact Bool.noConfusion (congrArg (fun t => match t with | CM.e => true | _ => false) bad)
def result : Goal := by
  rcases base_certificate with ⟨G, originalMagma, hs, ht⟩
  let oppositeMagma : Magma G := ⟨fun a b => @Magma.op G originalMagma b a⟩
  refine ⟨G, oppositeMagma, ?_, ?_⟩
  · intro «x» «y» «z»
    change «x» = (@Magma.op G originalMagma «y» (@Magma.op G originalMagma (@Magma.op G originalMagma «y» (@Magma.op G originalMagma «x» «y»)) (@Magma.op G originalMagma «z» «y»)))
    exact hs «x» «y» «z»
  · exact ht
end submission
def submission : Goal := submission.result
#print axioms submission

import JudgeProblem
import Lean.Elab.Tactic.Omega
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace submission
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
      (s0 : Step v1 x H0)
      (s1 : Step x v0 H1) : Code v0 (p H0 (p v0 H1)) x
inductive Step : CM → CM → CM → Prop
  | raw (a b : CM) : Step a b (p a b)
  | hit {a b o : CM} (h : Code a b o) : Step a b o
end
theorem code_shape {a b o : CM} (h : Code a b o) :
    ∃ q_x q_v0 q_v1 q_H0 q_H1 : CM, Step q_v1 q_x q_H0 ∧ Step q_x q_v0 q_H1 ∧ a = q_v0 ∧ b = (p q_H0 (p q_v0 q_H1)) ∧ o = q_x := by
  cases h
  exact ⟨_, _, _, _, _, by assumption, by assumption, rfl, rfl, rfl⟩
def getKey (c : CM) : CM := (L (R c))
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
  have fd0 := step_key_transport s1 qs1 (Eq.trans (Eq.trans (Eq.trans (Eq.symm (rfl)) (Eq.trans (given0) (rfl))) (rfl)) (Eq.symm (rfl))) (Eq.trans (Eq.trans (Eq.trans (Eq.symm (rfl)) (Eq.trans (congrArg (fun q => R q) (Eq.trans (Eq.symm (rfl)) (Eq.trans (congrArg (fun q => R q) (Eq.trans (Eq.symm (congrArg (fun q => p H0 q) (congrArg (fun q => p q H1) (Eq.trans (Eq.trans (Eq.symm (rfl)) (Eq.trans (given0) (rfl))) (rfl))))) (Eq.trans (given1) (rfl)))) (rfl)))) (rfl))) (rfl)) (Eq.symm (rfl)))
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


theorem no_code_after {x y v : CM} (st : Step x y v) : ¬ ∃ o, Code y v o := by
  rintro ⟨o, hc⟩
  cases st with
  | raw =>
    rcases code_shape hc with ⟨qx, qy, qz, h0, h1, s0, s1, ha, hb, ho⟩
    subst qy
    have he : y = p y h1 := congrArg R hb
    have hs := sz_lt_p_left y h1
    rw [← he] at hs
    omega
  | hit hh =>
    have h1 := (code_bounds hc).1
    have h2 := (code_bounds hh).2
    omega

theorem no_code_outer {x y z u v : CM} (sx : Step z x u) (sy : Step x y v) :
    ¬ ∃ o, Code u (p y v) o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q, owner, aux, h0, h1, t0, t1, ha, hb, ho⟩
  subst owner
  have hy : y = h0 := congrArg L hb
  subst h0
  have hv : v = p u h1 := congrArg R hb
  have hqv : sz q < sz v := by
    have hq := step_bound t1
    rw [hv]
    simp only [sz] at hq ⊢
    omega
  cases sy with
  | raw =>
    have he : x = u := congrArg L hv
    rw [← he] at sx
    exact step_ne_second sx
  | hit hcy =>
    have hvy := (code_bounds hcy).2
    cases t0 with
    | hit hty =>
      have hyq := (code_bounds hty).2
      omega
    | raw =>
      rcases code_shape hcy with ⟨xx, yy, zz, v0, v1, s0, s1, hxa, hyb, hvo⟩
      subst yy
      subst xx
      have he : q = p x v1 := congrArg R hyb
      have hvq := step_bound s1
      rw [he] at hqv
      simp only [sz] at hqv hvq
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
    x = eval y (eval (eval z x) (eval y (eval x y))) := by
  have sx := eval_step z x
  have sy := eval_step x y
  have h1 := eval_raw (no_code_after sy)
  have h2 := eval_raw (no_code_outer sx sy)
  rw [h1, h2]
  exact (eval_hit (Code.law x y z (eval z x) (eval x y) sx sy)).symm
noncomputable instance instMagma : Magma CM where op := eval
end CM
end submission
open submission
noncomputable def submission : Goal := by
  refine ⟨CM, CM.instMagma, ?_, ?_⟩
  · intro x y z
    exact CM.source_holds x y z
  · intro h
    have bad := h CM.e (CM.k CM.e)
    exact Bool.noConfusion (congrArg (fun t => match t with | CM.e => true | _ => false) bad)
#print axioms submission

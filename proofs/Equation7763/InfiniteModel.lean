import Lean.Elab.Tactic.Omega
import JudgeProblem
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
      (s0 : Step x v1 H0)
      (s1 : Step (p v1 H0) v0 H1) :
      Code v0 (p v0 H1) x
inductive Step : CM → CM → CM → Prop
  | raw (a b : CM) : Step a b (p a b)
  | hit {a b o : CM} (h : Code a b o) : Step a b o
end
theorem code_shape {a b o : CM} (h : Code a b o) :
    ∃ q_x q_v0 q_v1 q_H0 q_H1 : CM, Step q_x q_v1 q_H0 ∧ Step (p q_v1 q_H0) q_v0 q_H1 ∧ a = q_v0 ∧ b = (p q_v0 q_H1) ∧ o = q_x := by
  cases h
  exact ⟨_, _, _, _, _, by assumption, by assumption, rfl, rfl, rfl⟩
def getKey (c : CM) : CM := (L c)
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
  have fd0 := step_key_transport s1 qs1 (Eq.trans (Eq.trans (Eq.trans (Eq.symm (rfl)) (Eq.trans (given0) (rfl))) (rfl)) (Eq.symm (rfl))) (Eq.trans (Eq.trans (Eq.trans (Eq.symm (rfl)) (Eq.trans (congrArg (fun q => R q) (Eq.trans (Eq.symm (congrArg (fun q => p q H1) (Eq.trans (Eq.trans (Eq.symm (rfl)) (Eq.trans (given0) (rfl))) (rfl)))) (Eq.trans (given1) (rfl)))) (rfl))) (rfl)) (Eq.symm (rfl)))
  have fd1 := step_key_transport s0 qs0 (Eq.trans (Eq.trans (Eq.trans (Eq.symm (rfl)) (Eq.trans (congrArg (fun q => L q) (Eq.trans (Eq.symm (rfl)) (Eq.trans (fd0) (rfl)))) (rfl))) (rfl)) (Eq.symm (rfl))) (Eq.trans (Eq.trans (Eq.trans (Eq.symm (rfl)) (Eq.trans (congrArg (fun q => R q) (Eq.trans (Eq.symm (rfl)) (Eq.trans (fd0) (rfl)))) (rfl))) (rfl)) (Eq.symm (rfl)))
  exact ho.trans ((Eq.trans (Eq.trans (Eq.trans (Eq.symm (rfl)) (Eq.trans (fd1) (rfl))) (rfl)) (Eq.symm (rfl))).trans ko.symm)
theorem step_ne_second {a b : CM} : ¬ Step a b b := by
  intro h
  cases h with
  | hit hc =>
    have hb := (code_bounds hc).2
    omega
theorem step_bound {a b o : CM} (h : Step a b o) :
    sz a < sz (p o b) := by
  cases h with
  | raw => simp [sz] <;> omega
  | hit hc =>
    have hb := (code_bounds hc).1
    simp [sz] at hb ⊢ <;> omega

noncomputable def eval (a b : CM) : CM := by
  classical
  exact if h : ∃ o, Code a b o then Classical.choose h else p a b
theorem eval_hit {{a b o : CM}} (h : Code a b o) : eval a b = o := by
  rw [eval, dif_pos ⟨o, h⟩]
  exact code_unique (Classical.choose_spec ⟨o, h⟩) h
theorem eval_raw {{a b : CM}} (h : ¬ ∃ o, Code a b o) : eval a b = p a b := by
  rw [eval, dif_neg h]
theorem eval_step (a b : CM) : Step a b (eval a b) := by
  by_cases h : ∃ o, Code a b o
  · rcases h with ⟨o, hc⟩
    rw [eval_hit hc]
    exact Step.hit hc
  · rw [eval_raw h]
    exact Step.raw a b
theorem code_no_pair_left (v k : CM) :
    ¬ ∃ o, Code (p v k) v o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
  have qs0B := step_bound qs0
  cases qs0 with
  | raw =>
    have qs1B := step_bound qs1
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change (p v k) = q_v0 at e0
      have e1 := congrArg (fun q => q) hb
      change v = (p q_v0 (p (p q_v1 (p q_x q_v1)) q_v0)) at e1
      have cyc : v = (p (p v k) (p (p q_v1 (p q_x q_v1)) (p v k))) := Eq.trans (Eq.symm (rfl)) (Eq.trans (e1) (Eq.trans (congrArg (fun q => p q (p (p q_v1 (p q_x q_v1)) q_v0)) (Eq.trans (Eq.symm (Eq.trans (Eq.symm (rfl)) (Eq.trans (e0) (rfl)))) (rfl))) (congrArg (fun q => p (p v k) q) (congrArg (fun q => p (p q_v1 (p q_x q_v1)) q) (Eq.trans (Eq.symm (Eq.trans (Eq.symm (rfl)) (Eq.trans (e0) (rfl)))) (rfl))))))
      have hlt : sz v < sz (p (p v k) (p (p q_v1 (p q_x q_v1)) (p v k))) := Nat.lt_trans (sz_lt_p_left v k) (sz_lt_p_left (p v k) (p (p q_v1 (p q_x q_v1)) (p v k)))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => q) ha
      change (p v k) = q_v0 at e0
      have e1 := congrArg (fun q => q) hb
      change v = (p q_v0 q_H1) at e1
      have cyc : v = (p (p v k) q_H1) := Eq.trans (Eq.symm (rfl)) (Eq.trans (e1) (congrArg (fun q => p q q_H1) (Eq.trans (Eq.symm (Eq.trans (Eq.symm (rfl)) (Eq.trans (e0) (rfl)))) (rfl))))
      have hlt : sz v < sz (p (p v k) q_H1) := Nat.lt_trans (sz_lt_p_left v k) (sz_lt_p_left (p v k) q_H1)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    have qs1B := step_bound qs1
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change (p v k) = q_v0 at e0
      have e1 := congrArg (fun q => q) hb
      change v = (p q_v0 (p (p q_v1 q_H0) q_v0)) at e1
      have cyc : v = (p (p v k) (p (p q_v1 q_H0) (p v k))) := Eq.trans (Eq.symm (rfl)) (Eq.trans (e1) (Eq.trans (congrArg (fun q => p q (p (p q_v1 q_H0) q_v0)) (Eq.trans (Eq.symm (Eq.trans (Eq.symm (rfl)) (Eq.trans (e0) (rfl)))) (rfl))) (congrArg (fun q => p (p v k) q) (congrArg (fun q => p (p q_v1 q_H0) q) (Eq.trans (Eq.symm (Eq.trans (Eq.symm (rfl)) (Eq.trans (e0) (rfl)))) (rfl))))))
      have hlt : sz v < sz (p (p v k) (p (p q_v1 q_H0) (p v k))) := Nat.lt_trans (sz_lt_p_left v k) (sz_lt_p_left (p v k) (p (p q_v1 q_H0) (p v k)))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => q) ha
      change (p v k) = q_v0 at e0
      have e1 := congrArg (fun q => q) hb
      change v = (p q_v0 q_H1) at e1
      have cyc : v = (p (p v k) q_H1) := Eq.trans (Eq.symm (rfl)) (Eq.trans (e1) (congrArg (fun q => p q q_H1) (Eq.trans (Eq.symm (Eq.trans (Eq.symm (rfl)) (Eq.trans (e0) (rfl)))) (rfl))))
      have hlt : sz v < sz (p (p v k) q_H1) := Nat.lt_trans (sz_lt_p_left v k) (sz_lt_p_left (p v k) q_H1)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr0 (x v0 v1 H0 : CM)
    (s0 : Step x v1 H0) :
    ¬ ∃ o, Code v1 H0 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
  have s0B := step_bound s0
  cases s0 with
  | raw =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      have he : q_H1 = q_v0 := Eq.trans (rfl) (Eq.symm (Eq.trans (Eq.trans (Eq.symm (Eq.trans (Eq.trans (Eq.symm (rfl)) (Eq.trans (ha) (rfl))) (rfl))) (Eq.trans (congrArg (fun q => (R q)) (hb)) (rfl))) (rfl)))
      exact step_ne_second (by simpa only [he] using qs1)
    | hit qs0h =>
      have he : q_H1 = q_v0 := Eq.trans (rfl) (Eq.symm (Eq.trans (Eq.trans (Eq.symm (Eq.trans (Eq.trans (Eq.symm (rfl)) (Eq.trans (ha) (rfl))) (rfl))) (Eq.trans (congrArg (fun q => (R q)) (hb)) (rfl))) (rfl)))
      exact step_ne_second (by simpa only [he] using qs1)
  | hit s0h =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      have qs1B := step_bound qs1
      cases qs1 with
      | raw =>
        have hcB := code_bounds hc
        have s0hB := code_bounds s0h
        have s0B := s0B
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := ha
        change v1 = q_v0 at p0
        have z0 := congrArg sz p0
        have p1 := hb
        change H0 = (p q_v0 (p (p q_v1 (p q_x q_v1)) q_v0)) at p1
        have z1 := congrArg sz p1
        have p2 := ho
        change o = q_x at p2
        have z2 := congrArg sz p2
        have hx : sz q_v0 < sz (p q_v0 (p (p q_v1 (p q_x q_v1)) q_v0)) := by
          have q := hcB.1
          have eu : sz v1 = sz q_v0 := congrArg sz (Eq.trans (p0) (rfl))
          have ev : sz H0 = sz (p q_v0 (p (p q_v1 (p q_x q_v1)) q_v0)) := congrArg sz (Eq.trans (p1) (rfl))
          have q1 : sz q_v0 < sz H0 := lt_of_eq_of_lt eu.symm q
          exact lt_of_lt_of_eq q1 ev
        have hy : sz (p q_v0 (p (p q_v1 (p q_x q_v1)) q_v0)) < sz q_v0 := by
          have q := s0hB.2
          have ev : sz H0 = sz (p q_v0 (p (p q_v1 (p q_x q_v1)) q_v0)) := congrArg sz (Eq.trans (p1) (rfl))
          have eu : sz v1 = sz q_v0 := congrArg sz (Eq.trans (p0) (rfl))
          have q1 : sz (p q_v0 (p (p q_v1 (p q_x q_v1)) q_v0)) < sz v1 := lt_of_eq_of_lt ev.symm q
          exact lt_of_lt_of_eq q1 eu
        exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
      | hit qs1h =>
        have hcB := code_bounds hc
        have s0hB := code_bounds s0h
        have qs1hB := code_bounds qs1h
        have s0B := s0B
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := ha
        change v1 = q_v0 at p0
        have z0 := congrArg sz p0
        have p1 := hb
        change H0 = (p q_v0 q_H1) at p1
        have z1 := congrArg sz p1
        have p2 := ho
        change o = q_x at p2
        have z2 := congrArg sz p2
        have hx : sz q_v0 < sz (p q_v0 q_H1) := by
          have q := hcB.1
          have eu : sz v1 = sz q_v0 := congrArg sz (Eq.trans (p0) (rfl))
          have ev : sz H0 = sz (p q_v0 q_H1) := congrArg sz (Eq.trans (p1) (rfl))
          have q1 : sz q_v0 < sz H0 := lt_of_eq_of_lt eu.symm q
          exact lt_of_lt_of_eq q1 ev
        have hy : sz (p q_v0 q_H1) < sz q_v0 := by
          have q := s0hB.2
          have ev : sz H0 = sz (p q_v0 q_H1) := congrArg sz (Eq.trans (p1) (rfl))
          have eu : sz v1 = sz q_v0 := congrArg sz (Eq.trans (p0) (rfl))
          have q1 : sz (p q_v0 q_H1) < sz v1 := lt_of_eq_of_lt ev.symm q
          exact lt_of_lt_of_eq q1 eu
        exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
    | hit qs0h =>
      have qs1B := step_bound qs1
      cases qs1 with
      | raw =>
        have hcB := code_bounds hc
        have s0hB := code_bounds s0h
        have qs0hB := code_bounds qs0h
        have s0B := s0B
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := ha
        change v1 = q_v0 at p0
        have z0 := congrArg sz p0
        have p1 := hb
        change H0 = (p q_v0 (p (p q_v1 q_H0) q_v0)) at p1
        have z1 := congrArg sz p1
        have p2 := ho
        change o = q_x at p2
        have z2 := congrArg sz p2
        have hx : sz q_v0 < sz (p q_v0 (p (p q_v1 q_H0) q_v0)) := by
          have q := hcB.1
          have eu : sz v1 = sz q_v0 := congrArg sz (Eq.trans (p0) (rfl))
          have ev : sz H0 = sz (p q_v0 (p (p q_v1 q_H0) q_v0)) := congrArg sz (Eq.trans (p1) (rfl))
          have q1 : sz q_v0 < sz H0 := lt_of_eq_of_lt eu.symm q
          exact lt_of_lt_of_eq q1 ev
        have hy : sz (p q_v0 (p (p q_v1 q_H0) q_v0)) < sz q_v0 := by
          have q := s0hB.2
          have ev : sz H0 = sz (p q_v0 (p (p q_v1 q_H0) q_v0)) := congrArg sz (Eq.trans (p1) (rfl))
          have eu : sz v1 = sz q_v0 := congrArg sz (Eq.trans (p0) (rfl))
          have q1 : sz (p q_v0 (p (p q_v1 q_H0) q_v0)) < sz v1 := lt_of_eq_of_lt ev.symm q
          exact lt_of_lt_of_eq q1 eu
        exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
      | hit qs1h =>
        have hcB := code_bounds hc
        have s0hB := code_bounds s0h
        have qs0hB := code_bounds qs0h
        have qs1hB := code_bounds qs1h
        have s0B := s0B
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := ha
        change v1 = q_v0 at p0
        have z0 := congrArg sz p0
        have p1 := hb
        change H0 = (p q_v0 q_H1) at p1
        have z1 := congrArg sz p1
        have p2 := ho
        change o = q_x at p2
        have z2 := congrArg sz p2
        have hx : sz q_v0 < sz (p q_v0 q_H1) := by
          have q := hcB.1
          have eu : sz v1 = sz q_v0 := congrArg sz (Eq.trans (p0) (rfl))
          have ev : sz H0 = sz (p q_v0 q_H1) := congrArg sz (Eq.trans (p1) (rfl))
          have q1 : sz q_v0 < sz H0 := lt_of_eq_of_lt eu.symm q
          exact lt_of_lt_of_eq q1 ev
        have hy : sz (p q_v0 q_H1) < sz q_v0 := by
          have q := s0hB.2
          have ev : sz H0 = sz (p q_v0 q_H1) := congrArg sz (Eq.trans (p1) (rfl))
          have eu : sz v1 = sz q_v0 := congrArg sz (Eq.trans (p0) (rfl))
          have q1 : sz (p q_v0 q_H1) < sz v1 := lt_of_eq_of_lt ev.symm q
          exact lt_of_lt_of_eq q1 eu
        exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
theorem nr1 (x v0 v1 H1 : CM)
    (s1 : Step (p v1 H0) v0 H1) :
    ¬ ∃ o, Code v0 H1 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
  have s1B := step_bound s1
  cases s1 with
  | raw =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      have he : q_H1 = q_v0 := Eq.trans (Eq.trans (Eq.symm (Eq.trans (Eq.symm (Eq.trans (Eq.trans (Eq.symm (rfl)) (Eq.trans (ha) (rfl))) (Eq.trans (Eq.symm (Eq.trans (Eq.symm (rfl)) (Eq.trans (congrArg (fun q => (L q)) (hb)) (rfl)))) (rfl)))) (Eq.trans (congrArg (fun q => (R q)) (hb)) (rfl)))) (rfl)) (Eq.symm (Eq.trans (Eq.symm (Eq.trans (Eq.symm (rfl)) (Eq.trans (congrArg (fun q => (L q)) (hb)) (rfl)))) (rfl)))
      exact step_ne_second (by simpa only [he] using qs1)
    | hit qs0h =>
      have he : q_H1 = q_v0 := Eq.trans (Eq.trans (Eq.symm (Eq.trans (Eq.symm (Eq.trans (Eq.trans (Eq.symm (rfl)) (Eq.trans (ha) (rfl))) (Eq.trans (Eq.symm (Eq.trans (Eq.symm (rfl)) (Eq.trans (congrArg (fun q => (L q)) (hb)) (rfl)))) (rfl)))) (Eq.trans (congrArg (fun q => (R q)) (hb)) (rfl)))) (rfl)) (Eq.symm (Eq.trans (Eq.symm (Eq.trans (Eq.symm (rfl)) (Eq.trans (congrArg (fun q => (L q)) (hb)) (rfl)))) (rfl)))
      exact step_ne_second (by simpa only [he] using qs1)
  | hit s1h =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      have qs1B := step_bound qs1
      cases qs1 with
      | raw =>
        have hcB := code_bounds hc
        have s1hB := code_bounds s1h
        have s1B := s1B
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := ha
        change v0 = q_v0 at p0
        have z0 := congrArg sz p0
        have p1 := hb
        change H1 = (p q_v0 (p (p q_v1 (p q_x q_v1)) q_v0)) at p1
        have z1 := congrArg sz p1
        have p2 := ho
        change o = q_x at p2
        have z2 := congrArg sz p2
        have hx : sz q_v0 < sz (p q_v0 (p (p q_v1 (p q_x q_v1)) q_v0)) := by
          have q := hcB.1
          have eu : sz v0 = sz q_v0 := congrArg sz (Eq.trans (p0) (rfl))
          have ev : sz H1 = sz (p q_v0 (p (p q_v1 (p q_x q_v1)) q_v0)) := congrArg sz (Eq.trans (p1) (rfl))
          have q1 : sz q_v0 < sz H1 := lt_of_eq_of_lt eu.symm q
          exact lt_of_lt_of_eq q1 ev
        have hy : sz (p q_v0 (p (p q_v1 (p q_x q_v1)) q_v0)) < sz q_v0 := by
          have q := s1hB.2
          have ev : sz H1 = sz (p q_v0 (p (p q_v1 (p q_x q_v1)) q_v0)) := congrArg sz (Eq.trans (p1) (rfl))
          have eu : sz v0 = sz q_v0 := congrArg sz (Eq.trans (p0) (rfl))
          have q1 : sz (p q_v0 (p (p q_v1 (p q_x q_v1)) q_v0)) < sz v0 := lt_of_eq_of_lt ev.symm q
          exact lt_of_lt_of_eq q1 eu
        exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
      | hit qs1h =>
        have hcB := code_bounds hc
        have s1hB := code_bounds s1h
        have qs1hB := code_bounds qs1h
        have s1B := s1B
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := ha
        change v0 = q_v0 at p0
        have z0 := congrArg sz p0
        have p1 := hb
        change H1 = (p q_v0 q_H1) at p1
        have z1 := congrArg sz p1
        have p2 := ho
        change o = q_x at p2
        have z2 := congrArg sz p2
        have hx : sz q_v0 < sz (p q_v0 q_H1) := by
          have q := hcB.1
          have eu : sz v0 = sz q_v0 := congrArg sz (Eq.trans (p0) (rfl))
          have ev : sz H1 = sz (p q_v0 q_H1) := congrArg sz (Eq.trans (p1) (rfl))
          have q1 : sz q_v0 < sz H1 := lt_of_eq_of_lt eu.symm q
          exact lt_of_lt_of_eq q1 ev
        have hy : sz (p q_v0 q_H1) < sz q_v0 := by
          have q := s1hB.2
          have ev : sz H1 = sz (p q_v0 q_H1) := congrArg sz (Eq.trans (p1) (rfl))
          have eu : sz v0 = sz q_v0 := congrArg sz (Eq.trans (p0) (rfl))
          have q1 : sz (p q_v0 q_H1) < sz v0 := lt_of_eq_of_lt ev.symm q
          exact lt_of_lt_of_eq q1 eu
        exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
    | hit qs0h =>
      have qs1B := step_bound qs1
      cases qs1 with
      | raw =>
        have hcB := code_bounds hc
        have s1hB := code_bounds s1h
        have qs0hB := code_bounds qs0h
        have s1B := s1B
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := ha
        change v0 = q_v0 at p0
        have z0 := congrArg sz p0
        have p1 := hb
        change H1 = (p q_v0 (p (p q_v1 q_H0) q_v0)) at p1
        have z1 := congrArg sz p1
        have p2 := ho
        change o = q_x at p2
        have z2 := congrArg sz p2
        have hx : sz q_v0 < sz (p q_v0 (p (p q_v1 q_H0) q_v0)) := by
          have q := hcB.1
          have eu : sz v0 = sz q_v0 := congrArg sz (Eq.trans (p0) (rfl))
          have ev : sz H1 = sz (p q_v0 (p (p q_v1 q_H0) q_v0)) := congrArg sz (Eq.trans (p1) (rfl))
          have q1 : sz q_v0 < sz H1 := lt_of_eq_of_lt eu.symm q
          exact lt_of_lt_of_eq q1 ev
        have hy : sz (p q_v0 (p (p q_v1 q_H0) q_v0)) < sz q_v0 := by
          have q := s1hB.2
          have ev : sz H1 = sz (p q_v0 (p (p q_v1 q_H0) q_v0)) := congrArg sz (Eq.trans (p1) (rfl))
          have eu : sz v0 = sz q_v0 := congrArg sz (Eq.trans (p0) (rfl))
          have q1 : sz (p q_v0 (p (p q_v1 q_H0) q_v0)) < sz v0 := lt_of_eq_of_lt ev.symm q
          exact lt_of_lt_of_eq q1 eu
        exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
      | hit qs1h =>
        have hcB := code_bounds hc
        have s1hB := code_bounds s1h
        have qs0hB := code_bounds qs0h
        have qs1hB := code_bounds qs1h
        have s1B := s1B
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := ha
        change v0 = q_v0 at p0
        have z0 := congrArg sz p0
        have p1 := hb
        change H1 = (p q_v0 q_H1) at p1
        have z1 := congrArg sz p1
        have p2 := ho
        change o = q_x at p2
        have z2 := congrArg sz p2
        have hx : sz q_v0 < sz (p q_v0 q_H1) := by
          have q := hcB.1
          have eu : sz v0 = sz q_v0 := congrArg sz (Eq.trans (p0) (rfl))
          have ev : sz H1 = sz (p q_v0 q_H1) := congrArg sz (Eq.trans (p1) (rfl))
          have q1 : sz q_v0 < sz H1 := lt_of_eq_of_lt eu.symm q
          exact lt_of_lt_of_eq q1 ev
        have hy : sz (p q_v0 q_H1) < sz q_v0 := by
          have q := s1hB.2
          have ev : sz H1 = sz (p q_v0 q_H1) := congrArg sz (Eq.trans (p1) (rfl))
          have eu : sz v0 = sz q_v0 := congrArg sz (Eq.trans (p0) (rfl))
          have q1 : sz (p q_v0 q_H1) < sz v0 := lt_of_eq_of_lt ev.symm q
          exact lt_of_lt_of_eq q1 eu
        exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
theorem source_holds (x v0 v1 : CM) :
    x = (eval v0 (eval v0 (eval (eval v1 (eval x v1)) v0))) := by
  let H0 := eval x v1
  have e0a : x = x := by
    change x = x
    rfl
  have e0b : v1 = v1 := by
    change v1 = v1
    rfl
  have s0 : Step x v1 H0 := by
    rw [← e0a, ← e0b]
    exact eval_step x v1
  let H1 := eval (eval v1 (eval x v1)) v0
  have e1a : (eval v1 (eval x v1)) = (p v1 H0) := by
    change (eval v1 H0) = (p v1 H0)
    exact (eval_raw (nr0 x v0 v1 H0 s0))
  have e1b : v0 = v0 := by
    change v0 = v0
    rfl
  have s1 : Step (p v1 H0) v0 H1 := by
    rw [← e1a, ← e1b]
    exact eval_step (eval v1 (eval x v1)) v0
  change x = (eval v0 (eval v0 H1))
  have rawEq : (eval v0 (eval v0 H1)) = (eval v0 (p v0 H1)) := congrArg (fun q => (eval v0 q)) (eval_raw (nr1 x v0 v1 H1 s1))
  exact (eval_hit (Code.law x v0 v1 H0 H1 s0 s1)).symm.trans rawEq.symm
noncomputable instance instMagma2 : Magma CM where op := eval
end CM
end submission
open submission
open submission.CM
noncomputable def submission : Goal := by
  refine ⟨CM, CM.instMagma2, ?_, ?_⟩
  · intro x v0 v1
    exact CM.source_holds x v0 v1
  · intro target
    have bad := target (CM.k CM.e) CM.e
    have hl : (CM.k CM.e) = (CM.k CM.e) := rfl
    have hr : CM.e = CM.e := rfl
    have bad2 := hl.symm.trans (bad.trans hr)
    exact Bool.noConfusion (congrArg (fun q => match q with | e => true | k _ => false | p _ _ => false) bad2)
#print axioms submission

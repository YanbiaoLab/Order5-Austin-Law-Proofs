import JudgeProblem
import Lean.Elab.Tactic.Omega
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
namespace submission
inductive CM where
  | e : CM
  | k : CM → CM
  | p : CM → CM → CM
deriving DecidableEq
namespace CM
def sz : CM → Nat
  | e => 0
  | k a => sz a + 1
  | p a b => sz a + sz b + 2
def L : CM → CM | p a _ => a | _ => e
def R : CM → CM | p _ b => b | _ => e
theorem size_left (a b : CM) : sz a < sz (p a b) := by simp only [sz]; omega
theorem size_right (a b : CM) : sz b < sz (p a b) := by simp only [sz]; omega

noncomputable def op (a b : CM) : CM := by
  classical
  exact match b with
    | p x (p y h) => if a = y ∧ ∃ z, op (op z x) y = h then x else p a b
    | _ => p a b
termination_by sz b
decreasing_by all_goals simp_all only [sz]; omega

def Code (a b o : CM) : Prop := ∃ z, b = p o (p a (op (op z o) a))

theorem op_hit {a b o : CM} (h : Code a b o) : op a b = o := by
  classical
  rcases h with ⟨z, rfl⟩
  rw [op]
  exact if_pos ⟨rfl, z, rfl⟩

theorem op_cases (a b : CM) : op a b = p a b ∨ Code a b (op a b) := by
  classical
  cases b with
  | e => exact Or.inl (by rw [op]; intro _ _ _ he; cases he)
  | k b => exact Or.inl (by rw [op]; intro _ _ _ he; cases he)
  | p x t =>
    cases t with
    | e => exact Or.inl (by rw [op]; intro _ _ _ he; cases he)
    | k t => exact Or.inl (by rw [op]; intro _ _ _ he; cases he)
    | p y h =>
      by_cases hc : a = y ∧ ∃ z, op (op z x) y = h
      · rcases hc with ⟨rfl, z, hz⟩
        have hh : Code a (p x (p a h)) x := ⟨z, by rw [hz]⟩
        exact Or.inr (by rw [op_hit hh]; exact hh)
      · exact Or.inl (by rw [op]; exact if_neg hc)

theorem op_raw {a b : CM} (h : ¬ ∃ o, Code a b o) : op a b = p a b := by
  rcases op_cases a b with hr | hc
  · exact hr
  · exact (h ⟨_, hc⟩).elim

theorem code_bounds {a b o : CM} (h : Code a b o) : sz a < sz b ∧ sz o < sz b := by
  rcases h with ⟨z, rfl⟩
  simp only [sz]
  omega

theorem code_key {a b o c q : CM} (h : Code a b o) (k : Code c b q) : a = c := by
  rcases h with ⟨z, hb⟩
  rcases k with ⟨w, kb⟩
  exact congrArg (fun t => L (R t)) (hb.symm.trans kb)

theorem op_ne_second (a b : CM) : op a b ≠ b := by
  intro h
  rcases op_cases a b with hr | hc
  · have hs := size_right a b
    rw [← hr, h] at hs
    omega
  · have hs := (code_bounds hc).2
    rw [h] at hs
    omega

theorem op_input_lt (a b : CM) : sz a < sz (op a b) ∨ sz a < sz b := by
  rcases op_cases a b with hr | hc
  · exact Or.inl (by rw [hr]; exact size_left a b)
  · exact Or.inr (code_bounds hc).1

theorem small_output_code {a b : CM} (h : sz (op a b) < sz b) : Code a b (op a b) := by
  rcases op_cases a b with hr | hc
  · have hs := size_right a b
    rw [hr] at h
    omega
  · exact hc

theorem no_code_after_right (u y : CM) : ¬ ∃ o, Code y (op u y) o := by
  rintro ⟨o, hc⟩
  rcases op_cases u y with hr | hh
  · rcases hc with ⟨z, hb⟩
    have hy : y = p y (op (op z o) y) := congrArg R (hr.symm.trans hb)
    have hs := size_left y (op (op z o) y)
    rw [← hy] at hs
    omega
  · have h1 := (code_bounds hc).1
    have h2 := (code_bounds hh).2
    omega

theorem no_code_outer (x y z : CM) :
    ¬ ∃ o, Code x (p y (op (op z x) y)) o := by
  let u := op z x
  let v := op u y
  change ¬ ∃ o, Code x (p y v) o
  rintro ⟨o, w, hb⟩
  have ho : y = o := congrArg L hb
  subst o
  have hv : v = p x (op (op w y) x) := congrArg R hb
  have hxv : sz x < sz v := by rw [hv]; exact size_left _ _
  have hrv : sz (op (op w y) x) < sz v := by rw [hv]; exact size_right _ _
  have hcv : Code u y v := by
    rcases op_cases u y with hr | hc
    · have hu : u = x := congrArg L (hr.symm.trans hv)
      exact (op_ne_second z x hu).elim
    · exact hc
  have hvy := (code_bounds hcv).2
  have hi := op_input_lt (op w y) x
  have hby : sz (op w y) < sz y := by rcases hi with hi | hi <;> omega
  have hcb := small_output_code hby
  have hu : u = w := code_key hcv hcb
  have hv2 : v = p x (op v x) := by simpa only [← hu] using hv
  have hr2 : sz (op v x) < sz v :=
    lt_of_lt_of_eq (size_right x (op v x)) (congrArg sz hv2.symm)
  have hi2 := op_input_lt v x
  rcases hi2 with hi2 | hi2 <;> omega

theorem source_holds (x y z : CM) :
    x = op y (op x (op y (op (op z x) y))) := by
  have h1 := op_raw (no_code_after_right (op z x) y)
  have h2 := op_raw (no_code_outer x y z)
  rw [h1, h2]
  exact (op_hit ⟨z, rfl⟩).symm

noncomputable instance instMagma : Magma CM where op := op
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

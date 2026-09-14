prelude
import JudgeProblem
import Init.Classical
import Init.Data.Nat.Basic
import Init.WF
set_option autoImplicit false
set_option Elab.async false

/- Complete nontrivial infinite tree model. Local Lean verification only.
   Reproduce: python3 proofs/validation/eq17286-formal/verify.py -/

/- Module: TreeSchema -/
set_option autoImplicit false

/- Relational presentation for Equation17286. TreeGeometry proves decoder
   uniqueness; TreeModel supplies all hypotheses of conditional_source.
   The right-child counterexample explains why the E18137 proof needed revision. -/
namespace submission.Equation17286Tree

inductive Tree where
  | atom : Nat → Tree
  | pair : Tree → Tree → Tree

open Tree

mutual
inductive Column : Tree → Tree → Prop where
  | raw (a b : Tree) : Column b (pair a b)
  | target {b o : Tree} : Target b o → Column b o
inductive Target : Tree → Tree → Prop where
  | single (x z : Tree) : Target (pair z (pair z (pair x z))) x
  | inherit {z v x : Tree} : Target z v → Column v x →
      Target (pair z (pair z v)) x
end

def Code (a b o : Tree) : Prop := Target b o ∧ Column o a

inductive Step : Tree → Tree → Tree → Prop where
  | raw (a b : Tree) : Step a b (pair a b)
  | hit {a b o : Tree} : Code a b o → Step a b o

theorem column_of_step {a b o : Tree} (h : Step a b o) : Column b o := by
  cases h with
  | raw => exact Column.raw a b
  | hit hc => exact Column.target hc.1

theorem target_of_step {x z v : Tree} (h : Step x z v) :
    Target (pair z (pair z v)) x := by
  cases h with
  | raw => exact Target.single x z
  | hit hc => exact Target.inherit hc.1 hc.2

/-- This is a list of proof obligations, not a construction of op. -/
theorem conditional_source (op : Tree → Tree → Tree)
    (hstep : ∀ a b, Step a b (op a b))
    (hhit : ∀ a b o, Code a b o → op a b = o)
    (hmiddle : ∀ x z, op z (op x z) = pair z (op x z))
    (houter : ∀ x z, op z (pair z (op x z)) = pair z (pair z (op x z))) :
    ∀ x y z, x = op (op y x) (op z (op z (op x z))) := by
  intro x y z
  have hc : Code (op y x) (pair z (pair z (op x z))) x :=
    ⟨target_of_step (hstep x z), column_of_step (hstep y x)⟩
  rw [hmiddle, houter]
  exact (hhit _ _ _ hc).symm

/-- The analogue of E18137's target_not_right is false for this relation. -/
theorem inherited_target_is_right_child {z v : Tree} (h : Target z v) :
    Target (pair z (pair z v)) (pair z v) :=
  Target.inherit h (Column.raw z v)

theorem explicit_right_child_target :
    let a := atom 0
    let q := pair a (pair a (pair a a))
    Target (pair q (pair q a)) (pair q a) :=
  inherited_target_is_right_child (Target.single (atom 0) (atom 0))

theorem right_child_exclusion_false :
    ¬ (∀ b o, Target b o → ∀ a, b ≠ pair a o) := by
  intro h
  exact h _ _ explicit_right_child_target _ rfl

end submission.Equation17286Tree


/- Module: TreeBounds -/
set_option autoImplicit false

namespace submission.Equation17286Tree
open Tree

def size : Tree → Nat
  | atom _ => 1
  | pair a b => Nat.succ (size a + size b)

def rank : Tree → Nat
  | atom _ => 0
  | pair _ b => size b

theorem left_lt_size (a b : Tree) : size a < size (pair a b) :=
  Nat.lt_succ_of_le (Nat.le_add_right _ _)
theorem right_lt_size (a b : Tree) : size b < size (pair a b) :=
  Nat.lt_succ_of_le (Nat.le_add_left _ _)
theorem rank_lt_size (a : Tree) : rank a < size a := by
  cases a with
  | atom _ => exact Nat.zero_lt_succ 0
  | pair a b => exact right_lt_size a b

theorem column_rank {b o : Tree} (hc : Column b o) : rank o ≤ size b := by
  apply Column.rec
    (motive_1 := fun b o _ => rank o ≤ size b)
    (motive_2 := fun b o _ => rank o < rank b)
    ?_ ?_ ?_ ?_ hc
  · intro a b
    exact Nat.le_refl _
  · intro b o hr ih
    exact Nat.le_of_lt (Nat.lt_trans ih (rank_lt_size b))
  · intro x z
    exact Nat.lt_trans (rank_lt_size x)
      (Nat.lt_trans (left_lt_size x z) (right_lt_size z (pair x z)))
  · intro z v x hz hc _ ih
    exact Nat.lt_of_le_of_lt ih (right_lt_size z v)

theorem target_rank {b o : Tree} (hr : Target b o) : rank o < rank b := by
  cases hr with
  | single x z =>
    exact Nat.lt_trans (rank_lt_size o)
      (Nat.lt_trans (left_lt_size o z) (right_lt_size z (pair o z)))
  | inherit hz hc => exact Nat.lt_of_le_of_lt (column_rank hc) (right_lt_size _ _)

theorem target_ne_self {b : Tree} (hr : Target b b) : False :=
  Nat.lt_irrefl _ (target_rank hr)
theorem target_not_raw {b a : Tree} (hr : Target b (pair a b)) : False :=
  Nat.lt_irrefl _ (Nat.lt_trans (target_rank hr) (rank_lt_size b))
theorem column_ne_identity {b o : Tree} (hc : Column b o) : o ≠ b := by
  cases hc with
  | raw a b =>
    intro he
    have hs := right_lt_size a b
    rw [he] at hs
    exact Nat.lt_irrefl _ hs
  | target hr =>
    intro he
    rw [he] at hr
    exact target_ne_self hr
theorem column_ne_self {b : Tree} (hc : Column b b) : False :=
  column_ne_identity hc rfl

theorem column_cases {b o : Tree} (hc : Column b o) :
    (∃ a, o = pair a b) ∨ Target b o := by
  cases hc with
  | raw a b => exact Or.inl ⟨a, rfl⟩
  | target hr => exact Or.inr hr

theorem target_decompose {b x : Tree} (hr : Target b x) :
    ∃ z v, b = pair z (pair z v) ∧ Step x z v := by
  cases hr with
  | single x z => exact ⟨z, pair x z, rfl, Step.raw x z⟩
  | inherit hz hc => exact ⟨_, _, rfl, Step.hit ⟨hz,hc⟩⟩

theorem target_cases {b o : Tree} (hr : Target b o) :
    (∃ z, b = pair z (pair z (pair o z))) ∨
    (∃ z v, b = pair z (pair z v) ∧ Target z v ∧ Column v o) := by
  cases hr with
  | single x z => exact Or.inl ⟨z, rfl⟩
  | inherit hz hc => exact Or.inr ⟨_, _, rfl, hz, hc⟩

theorem target_point_unique (x z y : Tree)
    (hr : Target (pair z (pair z (pair x z))) y) : y = x := by
  cases target_cases hr with
  | inl hh =>
    cases hh with
    | intro w he =>
      exact ((Tree.pair.inj (Tree.pair.inj (Tree.pair.inj he).2).2).1).symm
  | inr hh =>
    cases hh with
    | intro w hh =>
      cases hh with
      | intro v hh =>
        have hzw := (Tree.pair.inj hh.1).1
        have hxv := (Tree.pair.inj (Tree.pair.inj hh.1).2).2
        have hz := hh.2.1
        rw [← hzw, ← hxv] at hz
        exact False.elim (target_not_raw hz)

theorem target_inherit_cases (z v y : Tree) (hz : Target z v)
    (hr : Target (pair z (pair z v)) y) : Column v y := by
  cases target_cases hr with
  | inl hh =>
    cases hh with
    | intro w he =>
      have hzw := (Tree.pair.inj he).1
      have hvy := (Tree.pair.inj (Tree.pair.inj he).2).2
      rw [← hzw] at hvy
      rw [hvy] at hz
      exact False.elim (target_not_raw hz)
  | inr hh =>
    cases hh with
    | intro w hh =>
      cases hh with
      | intro t hh =>
        have hvt := (Tree.pair.inj (Tree.pair.inj hh.1).2).2
        rw [hvt]
        exact hh.2.2

end submission.Equation17286Tree


/- Module: TreeGeometry -/
set_option autoImplicit false

namespace submission.Equation17286Tree
open Tree

def Triangle (b : Tree) : Prop :=
  ∀ x y, Column b x → Column b y → Column x y → False
def Fork (b : Tree) : Prop :=
  ∀ x y u, Column b x → Column b y → Column x u → Column y u → x = y

/-- Nested code containers would create a triangle over a smaller tree. -/
theorem nested_targets_small (b : Tree)
    (ih : ∀ a, size a < size b → Triangle a)
    (a u x : Tree) (ho : Target (pair a b) u) (hi : Target b x) : False := by
  cases target_decompose ho with
  | intro z hz =>
    cases hz with
    | intro v hv =>
      have hb := (Tree.pair.inj hv.1).2
      cases target_decompose hi with
      | intro t ht =>
        cases ht with
        | intro w hw =>
          have hzt := (Tree.pair.inj (hb.symm.trans hw.1)).1
          have hvw := (Tree.pair.inj (hb.symm.trans hw.1)).2
          have cv := column_of_step hv.2
          have cw := column_of_step hw.2
          rw [← hzt] at cw hvw
          rw [hvw] at cv
          have small : size z < size b := by
            rw [hb]
            exact left_lt_size z v
          exact ih z small w (pair z w) cw cv (Column.raw z w)

theorem raw_columns_unique (a c b u : Tree)
    (hx : Column (pair a b) u) (hy : Column (pair c b) u) :
    pair a b = pair c b := by
  cases column_cases hx with
  | inl hh =>
    cases hh with
    | intro t ht =>
      cases column_cases hy with
      | inl hk =>
        cases hk with
        | intro s hs => exact (Tree.pair.inj (ht.symm.trans hs)).2
      | inr hy =>
        have h := target_rank hy
        rw [ht] at h
        exact False.elim (Nat.lt_irrefl _ (Nat.lt_trans h (right_lt_size a b)))
  | inr hx =>
    cases column_cases hy with
    | inl hh =>
      cases hh with
      | intro t ht =>
        have h := target_rank hx
        rw [ht] at h
        exact False.elim (Nat.lt_irrefl _ (Nat.lt_trans h (right_lt_size c b)))
    | inr hy =>
      cases target_decompose hx with
      | intro z hz =>
        cases hz with
        | intro v hv =>
          cases target_decompose hy with
          | intro w hw =>
            cases hw with
            | intro t ht =>
              have haz := (Tree.pair.inj hv.1).1
              have hcw := (Tree.pair.inj ht.1).1
              have hbz := (Tree.pair.inj hv.1).2
              have hbw := (Tree.pair.inj ht.1).2
              have hzw := (Tree.pair.inj (hbz.symm.trans hbw)).1
              exact congrArg (fun k => pair k b) (haz.trans (hzw.trans hcw.symm))

theorem raw_target_disjoint_small (b : Tree)
    (ih : ∀ a, size a < size b → Triangle a)
    (a x u : Tree) (hr : Target b x)
    (hx : Column (pair a b) u) (hy : Column x u) : False := by
  cases column_cases hx with
  | inr ht => exact nested_targets_small b ih a u x ht hr
  | inl hh =>
    cases hh with
    | intro t ht =>
      cases column_cases hy with
      | inl hk =>
        cases hk with
        | intro s hs =>
          have he := (Tree.pair.inj (ht.symm.trans hs)).2
          rw [← he] at hr
          exact target_not_raw hr
      | inr hu =>
        have h := target_rank hu
        rw [ht] at h
        have hh := Nat.lt_trans h (Nat.lt_trans (target_rank hr) (rank_lt_size b))
        exact Nat.lt_irrefl _ (Nat.lt_trans hh (right_lt_size a b))

theorem raw_columns_no_edge (a c b : Tree) : ¬ Column (pair a b) (pair c b) := by
  intro hc
  cases column_cases hc with
  | inl hh =>
    cases hh with
    | intro t ht =>
      have he := (Tree.pair.inj ht).2
      have hs := right_lt_size a b
      rw [← he] at hs
      exact Nat.lt_irrefl _ hs
  | inr ht =>
    have hs : size b < size b := target_rank ht
    exact Nat.lt_irrefl _ hs

theorem target_to_raw_no_edge (a b x : Tree) (hr : Target b x) :
    ¬ Column x (pair a b) := by
  intro hc
  cases column_cases hc with
  | inl hh =>
    cases hh with
    | intro t ht =>
      have he := (Tree.pair.inj ht).2
      rw [← he] at hr
      exact target_ne_self hr
  | inr ht =>
    exact Nat.lt_irrefl _ (Nat.lt_trans (target_rank ht)
      (Nat.lt_trans (target_rank hr) (rank_lt_size b)))

theorem raw_to_target_no_edge_small (b : Tree)
    (ih : ∀ a, size a < size b → Triangle a)
    (a x : Tree) (hr : Target b x) : ¬ Column (pair a b) x := by
  intro hc
  cases column_cases hc with
  | inl hh =>
    cases hh with
    | intro t ht =>
      have hs := target_rank hr
      rw [ht] at hs
      exact Nat.lt_irrefl _ (Nat.lt_trans hs
        (Nat.lt_trans (rank_lt_size b) (right_lt_size a b)))
  | inr ht => exact nested_targets_small b ih a x x ht hr

theorem geometry_step (b : Tree)
    (ih : ∀ a, size a < size b → Fork a ∧ Triangle a) : Fork b ∧ Triangle b := by
  have smalltri : ∀ a, size a < size b → Triangle a := fun a h => (ih a h).2
  have targetfork : ∀ x y u, Target b x → Target b y →
      Column x u → Column y u → x = y := by
    intro x y u hx hy hxu hyu
    cases hx with
    | single x z => exact (target_point_unique x z y hy).symm
    | @inherit z v x hz hc =>
      have hv : size v < size (pair z (pair z v)) :=
        Nat.lt_trans (right_lt_size z v) (right_lt_size z (pair z v))
      exact (ih v hv).1 x y u hc (target_inherit_cases z v y hz hy) hxu hyu
  have targettri : ∀ x y, Target b x → Target b y → Column x y → False := by
    intro x y hx hy hxy
    cases hx with
    | single x z =>
      have he := target_point_unique x z y hy
      rw [he] at hxy
      exact column_ne_self hxy
    | @inherit z v x hz hc =>
      have hv : size v < size (pair z (pair z v)) :=
        Nat.lt_trans (right_lt_size z v) (right_lt_size z (pair z v))
      exact (ih v hv).2 x y hc (target_inherit_cases z v y hz hy) hxy
  constructor
  · intro x y u hx hy hxu hyu
    cases column_cases hx with
    | inl hh =>
      cases hh with
      | intro a ha =>
        rw [ha] at hxu ⊢
        cases column_cases hy with
        | inl hk =>
          cases hk with
          | intro c hc =>
            rw [hc] at hyu ⊢
            exact raw_columns_unique a c b u hxu hyu
        | inr hr => exact False.elim (raw_target_disjoint_small b smalltri a y u hr hxu hyu)
    | inr hr =>
      cases column_cases hy with
      | inl hh =>
        cases hh with
        | intro a ha =>
          rw [ha] at hyu
          exact False.elim (raw_target_disjoint_small b smalltri a x u hr hyu hxu)
      | inr ht => exact targetfork x y u hr ht hxu hyu
  · intro x y hx hy hxy
    cases column_cases hx with
    | inl hh =>
      cases hh with
      | intro a ha =>
        rw [ha] at hxy
        cases column_cases hy with
        | inl hk =>
          cases hk with
          | intro c hc =>
            rw [hc] at hxy
            exact raw_columns_no_edge a c b hxy
        | inr hr => exact raw_to_target_no_edge_small b smalltri a y hr hxy
    | inr hr =>
      cases column_cases hy with
      | inl hh =>
        cases hh with
        | intro a ha =>
          rw [ha] at hxy
          exact target_to_raw_no_edge a b x hr hxy
      | inr ht => exact targettri x y hr ht hxy

theorem column_geometry (b : Tree) : Fork b ∧ Triangle b := by
  have all : ∀ n, ∀ b, size b = n → Fork b ∧ Triangle b := by
    intro n
    exact Nat.strongRecOn (motive := fun n => ∀ b, size b = n → Fork b ∧ Triangle b) n
      (fun n ih b hb => geometry_step b (fun a ha => ih (size a) (hb ▸ ha) a rfl))
  exact all (size b) b rfl

theorem column_fork_unique {b x : Tree} (hx : Column b x) :
    ∀ y u, Column b y → Column x u → Column y u → x = y :=
  fun y u hy hxu hyu => (column_geometry b).1 x y u hx hy hxu hyu

theorem column_triangle_free {b x : Tree} (hx : Column b x) :
    ∀ y, Column b y → Column x y → False :=
  fun y hy hxy => (column_geometry b).2 x y hx hy hxy

theorem target_right_empty {a b o : Tree} (hr : Target (pair a b) o)
    (p : Tree) : ¬ Target b p :=
  nested_targets_small b (fun t _ => (column_geometry t).2) a o p hr

theorem code_output_unique (a b x y : Tree) (hx : Code a b x) (hy : Code a b y) :
    x = y := by
  cases hx.1 with
  | single x z => exact (target_point_unique _ _ _ hy.1).symm
  | inherit hz hc =>
    exact column_fork_unique hc y a (target_inherit_cases _ _ _ hz hy.1) hx.2 hy.2

end submission.Equation17286Tree


/- Module: TreeModel -/
set_option autoImplicit false

namespace submission.Equation17286Tree
open Tree

theorem target_cannot_reach_right {a b o : Tree} (hr : Target (pair a b) o) :
    ¬ Column o b := by
  cases hr with
  | single =>
    intro hc
    have h : size (pair o a) ≤ size o := column_rank hc
    exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (left_lt_size o a) h)
  | inherit hz hc =>
    intro he
    exact column_triangle_free hc _ (Column.raw a _) he

theorem raw_three_cycle (a b y : Tree)
    (hxy : Column (pair a b) y) (hyb : Column y b) : False := by
  cases column_cases hxy with
  | inr ht => exact target_cannot_reach_right ht hyb
  | inl hh =>
    cases hh with
    | intro c he =>
      rw [he] at hyb
      cases column_cases hyb with
      | inr ht => exact target_cannot_reach_right ht (Column.raw a b)
      | inl hk =>
        cases hk with
        | intro d hd =>
          have hs : size b < size (pair d (pair c (pair a b))) :=
            Nat.lt_trans (right_lt_size a b)
              (Nat.lt_trans (right_lt_size c (pair a b)) (right_lt_size d (pair c (pair a b))))
          rw [← hd] at hs
          exact Nat.lt_irrefl _ hs

theorem column_no_three_cycle (b x y : Tree)
    (hbx : Column b x) (hxy : Column x y) (hyb : Column y b) : False := by
  cases column_cases hbx with
  | inl hh =>
    cases hh with
    | intro a ha =>
      rw [ha] at hxy
      exact raw_three_cycle a b y hxy hyb
  | inr hx =>
    cases column_cases hxy with
    | inl hh =>
      cases hh with
      | intro a ha =>
        rw [ha] at hyb
        exact raw_three_cycle a x b hyb hbx
    | inr hy =>
      cases column_cases hyb with
      | inl hh =>
        cases hh with
        | intro a ha =>
          rw [ha] at hbx
          exact raw_three_cycle a y x hbx hxy
      | inr hb =>
        exact Nat.lt_irrefl _ (Nat.lt_trans (target_rank hx)
          (Nat.lt_trans (target_rank hb) (target_rank hy)))

theorem column_prefix_no_target (z v : Tree) (hc : Column z v) (o : Tree) :
    ¬ Target (pair z v) o := by
  intro ht
  cases target_decompose ht with
  | intro t hh =>
    cases hh with
    | intro w hw =>
      have hzt := (Tree.pair.inj hw.1).1
      have hv := (Tree.pair.inj hw.1).2
      have cw := column_of_step hw.2
      rw [← hzt] at cw hv
      rw [hv] at hc
      exact column_triangle_free cw (pair z w) hc (Column.raw z w)

theorem step_middle_no_code {x z v : Tree} (hs : Step x z v) :
    ∀ o, ¬ Code z v o := by
  intro o hc
  exact column_no_three_cycle z v o (column_of_step hs) (Column.target hc.1) hc.2

theorem step_outer_no_code {x z v : Tree} (hs : Step x z v) :
    ∀ o, ¬ Code z (pair z v) o := by
  intro o hc
  exact column_prefix_no_target z v (column_of_step hs) o hc.1

noncomputable def op (a b : Tree) : Tree := by
  classical
  exact if h : ∃ o, Code a b o then Classical.choose h else pair a b

theorem op_hit (a b o : Tree) (hc : Code a b o) : op a b = o := by
  classical
  have he : ∃ o, Code a b o := ⟨o, hc⟩
  unfold op
  rw [dif_pos he]
  exact code_output_unique a b _ o (Classical.choose_spec he) hc

theorem op_miss (a b : Tree) (hn : ∀ o, ¬ Code a b o) : op a b = pair a b := by
  classical
  have he : ¬ ∃ o, Code a b o := fun h => h.elim hn
  unfold op
  rw [dif_neg he]

theorem op_step (a b : Tree) : Step a b (op a b) := by
  classical
  cases Classical.em (∃ o, Code a b o) with
  | inl he =>
    unfold op
    rw [dif_pos he]
    exact Step.hit (Classical.choose_spec he)
  | inr he =>
    unfold op
    rw [dif_neg he]
    exact Step.raw a b

theorem op_middle_raw (x z : Tree) : op z (op x z) = pair z (op x z) :=
  op_miss _ _ (step_middle_no_code (op_step x z))

theorem op_outer_raw (x z : Tree) :
    op z (pair z (op x z)) = pair z (pair z (op x z)) :=
  op_miss _ _ (step_outer_no_code (op_step x z))

theorem source_law_explicit (x y z : Tree) :
    x = op (op y x) (op z (op z (op x z))) :=
  conditional_source op op_step op_hit op_middle_raw op_outer_raw x y z

theorem atom_injective (m n : Nat) (he : atom m = atom n) : m = n :=
  Tree.atom.inj he

theorem nontrivial : ∃ a b : Tree, a ≠ b := by
  refine ⟨atom 0, atom 1, ?_⟩
  intro he
  exact Nat.noConfusion (Tree.atom.inj he)

theorem infinite_model : ∃ (G : Type) (f : G → G → G) (embed : Nat → G),
    (∀ x y z, x = f (f y x) (f z (f z (f x z)))) ∧
    (∀ m n, embed m = embed n → m = n) :=
  ⟨Tree, op, atom, source_law_explicit, atom_injective⟩

noncomputable def dualOp (a b : Tree) : Tree := op b a

theorem dual_source_law_explicit (x y z : Tree) :
    x = dualOp (dualOp (dualOp (dualOp y x) y) y) (dualOp x z) :=
  source_law_explicit x z y

theorem dual_infinite_model : ∃ (G : Type) (f : G → G → G) (embed : Nat → G),
    (∀ x y z, x = f (f (f (f y x) y) y) (f x z)) ∧
    (∀ m n, embed m = embed n → m = n) :=
  ⟨Tree, dualOp, atom, dual_source_law_explicit, atom_injective⟩

end submission.Equation17286Tree


namespace submission
abbrev CM := Equation17286Tree.Tree
noncomputable instance modelMagma : Magma CM := ⟨Equation17286Tree.dualOp⟩
namespace CM
theorem tower_injective (m n : Nat)
    (h : Equation17286Tree.Tree.atom m = Equation17286Tree.Tree.atom n) : m = n :=
  Equation17286Tree.atom_injective m n h
end CM
end submission

theorem submission : Goal := by
  refine ⟨submission.CM, submission.modelMagma, ?_, ?_⟩
  · exact submission.Equation17286Tree.dual_source_law_explicit
  · intro h
    exact Nat.noConfusion (submission.Equation17286Tree.Tree.atom.inj
      (h (submission.Equation17286Tree.Tree.atom 0) (submission.Equation17286Tree.Tree.atom 1)))

example : Goal := submission
example (x y z : submission.CM) : x = (((y ◇ x) ◇ y) ◇ y) ◇ (x ◇ z) :=
  submission.Equation17286Tree.dual_source_law_explicit x y z

#print axioms submission
#print axioms submission.CM.tower_injective
#print axioms submission.Equation17286Tree.dual_infinite_model

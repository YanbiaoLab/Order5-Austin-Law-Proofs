prelude
import JudgeProblem
import Init.Data.Nat.Basic
import Init.Classical
set_option autoImplicit false

/- Equation27863: the opposite operation on the Equation18137 infinite tree model.
   All construction proofs are included below. No external model assumption.
   Reproduce: python3 proofs/validation/eq27863-formal/verify.py -/


/- Module: TreeSchema -/
set_option autoImplicit false

/- Infinite-key schema. This module gives the relational reduction and a
   conditional assembly theorem. TreeUnique and TreeModel discharge all its
   hypotheses and construct the nontrivial infinite magma. -/
namespace submission.Equation18137TreeSchema

def SourceLaw {G : Type} (f : G → G → G) : Prop :=
  ∀ x y z, x = f (f y x) (f z (f (f x z) z))

inductive Tree where
  | atom : Nat → Tree
  | pair : Tree → Tree → Tree

open Tree

mutual
inductive Column : Tree → Tree → Prop where
  | raw (a b : Tree) : Column b (pair a b)
  | target {b o : Tree} : Target b o → Column b o
inductive Target : Tree → Tree → Prop where
  | single (x z : Tree) : Target (pair z (pair (pair x z) z)) x
  | inherit {z v x : Tree} : Target z v → Column v x →
      Target (pair z (pair v z)) x
end

def Code (a b o : Tree) : Prop := Target b o ∧ Column o a

inductive Step : Tree → Tree → Tree → Prop where
  | raw (a b : Tree) : Step a b (pair a b)
  | hit {a b o : Tree} : Code a b o → Step a b o

theorem column_of_step {a b o : Tree} (hs : Step a b o) : Column b o := by
  cases hs with
  | raw => exact Column.raw a b
  | hit hc => exact Column.target hc.1

theorem column_realized {b o : Tree} (hc : Column b o) : ∃ a, Step a b o := by
  cases hc with
  | raw a b => exact ⟨a, Step.raw a b⟩
  | target hr => exact ⟨pair (atom 0) o, Step.hit ⟨hr, Column.raw (atom 0) o⟩⟩

theorem target_decompose {b x : Tree} (hr : Target b x) :
    ∃ z v, b = pair z (pair v z) ∧ Step x z v := by
  cases hr with
  | single x z => exact ⟨z, pair x z, rfl, Step.raw x z⟩
  | inherit hz hc => exact ⟨_, _, rfl, Step.hit ⟨hz, hc⟩⟩

theorem target_of_step {x z v : Tree} (hs : Step x z v) :
    Target (pair z (pair v z)) x := by
  cases hs with
  | raw => exact Target.single x z
  | hit hc => exact Target.inherit hc.1 hc.2

theorem code_trace_iff (u b x : Tree) : Code u b x ↔
    ∃ y z v, b = pair z (pair v z) ∧ Step y x u ∧ Step x z v := by
  constructor
  · intro hc
    cases column_realized hc.2 with
    | intro y hy =>
      cases target_decompose hc.1 with
      | intro z hz =>
        cases hz with
        | intro v hv => exact ⟨y, z, v, hv.1, hy, hv.2⟩
  · intro h
    cases h with
    | intro y hy =>
      cases hy with
      | intro z hz =>
        cases hz with
        | intro v hv =>
          rw [hv.1]
          exact ⟨target_of_step hv.2.2, column_of_step hv.2.1⟩

theorem template_law (op : Tree → Tree → Tree)
    (hstep : ∀ a b, Step a b (op a b))
    (hhit : ∀ a b o, Code a b o → op a b = o)
    (hmiddle : ∀ x z, op (op x z) z = pair (op x z) z)
    (houter : ∀ x z, op z (pair (op x z) z) = pair z (pair (op x z) z)) :
    SourceLaw op := by
  intro x y z
  have hc : Code (op y x) (pair z (pair (op x z) z)) x :=
    ⟨target_of_step (hstep x z), column_of_step (hstep y x)⟩
  change x = op (op y x) (op z (op (op x z) z))
  rw [hmiddle, houter]
  exact (hhit _ _ _ hc).symm

theorem atom_injective (m n : Nat) (he : atom m = atom n) : m = n :=
  Tree.atom.inj he

end submission.Equation18137TreeSchema


/- Module: TreeBounds -/
set_option autoImplicit false

namespace submission.Equation18137TreeSchema
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
      (Nat.lt_trans (left_lt_size x z) (left_lt_size (pair x z) z))
  · intro z v x hz hc _ ih
    exact Nat.lt_of_le_of_lt ih (left_lt_size v z)

theorem target_rank {b o : Tree} (hr : Target b o) : rank o < rank b := by
  cases hr with
  | single x z =>
    exact Nat.lt_trans (rank_lt_size o)
      (Nat.lt_trans (left_lt_size o z) (left_lt_size (pair o z) z))
  | inherit hz hc => exact Nat.lt_of_le_of_lt (column_rank hc) (left_lt_size _ _)

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

theorem target_not_right {b o : Tree} (hr : Target b o) :
    ∀ a, b ≠ pair a o := by
  cases hr with
  | single x z =>
    intro a he
    have he' := (Tree.pair.inj he).2
    have hs := Nat.lt_trans (left_lt_size o z) (left_lt_size (pair o z) z)
    rw [he'] at hs
    exact Nat.lt_irrefl _ hs
  | inherit hz hc =>
    intro a he
    have he' := (Tree.pair.inj he).2
    cases hc with
    | raw y v =>
      have hzv := (Tree.pair.inj he').2
      rw [hzv] at hz
      exact target_ne_self hz
    | target ht =>
      have hs := target_rank ht
      rw [← he'] at hs
      exact Nat.lt_irrefl _ (Nat.lt_trans hs
        (Nat.lt_trans (target_rank hz) (rank_lt_size _)))

theorem raw_double_not_target (x z o : Tree) :
    ¬ Target (pair (pair x z) z) o := by
  intro hr
  cases target_decompose hr with
  | intro a ha =>
    cases ha with
    | intro v hv =>
      have hleft := (Tree.pair.inj hv.1).1
      have hright := (Tree.pair.inj hv.1).2
      rw [← hleft] at hright
      have hs := Nat.lt_trans (right_lt_size x z) (right_lt_size v (pair x z))
      rw [← hright] at hs
      exact Nat.lt_irrefl _ hs

theorem target_right_empty {a b o : Tree} (hr : Target (pair a b) o)
    (p : Tree) : ¬ Target b p := by
  cases hr with
  | single x z => exact raw_double_not_target o a p
  | inherit hz hc =>
    intro ht
    cases target_decompose ht with
    | intro u hu =>
      cases hu with
      | intro v hv =>
        have hleft := (Tree.pair.inj hv.1).1
        have hright := (Tree.pair.inj hv.1).2
        rw [← hleft] at hright
        exact target_not_right hz v hright

end submission.Equation18137TreeSchema


/- Module: TreeUnique -/
set_option autoImplicit false

namespace submission.Equation18137TreeSchema
open Tree

theorem column_cases {b o : Tree} (hc : Column b o) :
    (∃ a, o = pair a b) ∨ Target b o := by
  cases hc with
  | raw a b => exact Or.inl ⟨a, rfl⟩
  | target hr => exact Or.inr hr

theorem target_cases {b o : Tree} (hr : Target b o) :
    (∃ z, b = pair z (pair (pair o z) z)) ∨
    (∃ z v, b = pair z (pair v z) ∧ Target z v ∧ Column v o) := by
  cases hr with
  | single x z => exact Or.inl ⟨z, rfl⟩
  | inherit hz hc => exact Or.inr ⟨_, _, rfl, hz, hc⟩

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
              have hzw := (Tree.pair.inj (hbz.symm.trans hbw)).2
              exact congrArg (fun k => pair k b) (haz.trans (hzw.trans hcw.symm))

theorem raw_target_columns_disjoint (a b x u : Tree) (hr : Target b x)
    (hx : Column (pair a b) u) (hy : Column x u) : False := by
  cases column_cases hx with
  | inr ht => exact target_right_empty ht x hr
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

theorem target_point_unique (x z y : Tree)
    (hr : Target (pair z (pair (pair x z) z)) y) : y = x := by
  cases target_cases hr with
  | inl hh =>
    cases hh with
    | intro w he =>
      have hzw := (Tree.pair.inj he).1
      have hxy := (Tree.pair.inj (Tree.pair.inj (Tree.pair.inj he).2).1).1
      exact hxy.symm
  | inr hh =>
    cases hh with
    | intro w hw =>
      cases hw with
      | intro v hv =>
        have hzw := (Tree.pair.inj hv.1).1
        have hxv := (Tree.pair.inj (Tree.pair.inj hv.1).2).1
        have hr := hv.2.1
        rw [← hzw, ← hxv] at hr
        exact False.elim (target_not_raw hr)

theorem target_inherit_cases (z v y : Tree) (hz : Target z v)
    (hr : Target (pair z (pair v z)) y) : Column v y := by
  cases target_cases hr with
  | inl hh =>
    cases hh with
    | intro w he =>
      have hzw := (Tree.pair.inj he).1
      have hvy := (Tree.pair.inj (Tree.pair.inj he).2).1
      rw [← hzw] at hvy
      rw [hvy] at hz
      exact False.elim (target_not_raw hz)
  | inr hh =>
    cases hh with
    | intro w hw =>
      cases hw with
      | intro t ht =>
        have hvt := (Tree.pair.inj (Tree.pair.inj ht.1).2).1
        rw [hvt]
        exact ht.2.2

theorem column_fork_unique {b x : Tree} (hx : Column b x) :
    ∀ y u, Column b y → Column x u → Column y u → x = y := by
  apply Column.rec
    (motive_1 := fun b x _ => ∀ y u, Column b y → Column x u → Column y u → x = y)
    (motive_2 := fun b x _ => ∀ y u, Target b y → Column x u → Column y u → x = y)
    ?_ ?_ ?_ ?_ hx
  · intro a b y u hy hxu hyu
    cases column_cases hy with
    | inl hh =>
      cases hh with
      | intro c hc =>
        rw [hc] at hyu ⊢
        exact raw_columns_unique a c b u hxu hyu
    | inr hr => exact False.elim (raw_target_columns_disjoint a b y u hr hxu hyu)
  · intro b x hr ih y u hy hxu hyu
    cases column_cases hy with
    | inl hh =>
      cases hh with
      | intro a ha =>
        rw [ha] at hyu
        exact False.elim (raw_target_columns_disjoint a b x u hr hyu hxu)
    | inr ht => exact ih y u ht hxu hyu
  · intro x z y u hy _ _
    exact (target_point_unique x z y hy).symm
  · intro z v x hz hc _ ih y u hy hxu hyu
    exact ih y u (target_inherit_cases z v y hz hy) hxu hyu

theorem code_output_unique (a b x y : Tree) (hx : Code a b x) (hy : Code a b y) :
    x = y := by
  cases hx.1 with
  | single x z => exact (target_point_unique _ _ _ hy.1).symm
  | inherit hz hc =>
    exact column_fork_unique hc y a (target_inherit_cases _ _ _ hz hy.1) hx.2 hy.2

end submission.Equation18137TreeSchema


/- Module: TreeModel -/
set_option autoImplicit false

namespace submission.Equation18137TreeSchema
open Tree

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

theorem raw_to_target_no_edge (a b x : Tree) (hr : Target b x) :
    ¬ Column (pair a b) x := by
  intro hc
  cases column_cases hc with
  | inl hh =>
    cases hh with
    | intro t ht =>
      have hs := target_rank hr
      rw [ht] at hs
      exact Nat.lt_irrefl _ (Nat.lt_trans hs
        (Nat.lt_trans (rank_lt_size b) (right_lt_size a b)))
  | inr ht => exact target_right_empty ht x hr

theorem column_triangle_free {b x : Tree} (hx : Column b x) :
    ∀ y, Column b y → Column x y → False := by
  apply Column.rec
    (motive_1 := fun b x _ => ∀ y, Column b y → Column x y → False)
    (motive_2 := fun b x _ => ∀ y, Target b y → Column x y → False)
    ?_ ?_ ?_ ?_ hx
  · intro a b y hy hxy
    cases column_cases hy with
    | inl hh =>
      cases hh with
      | intro c hc =>
        rw [hc] at hxy
        exact raw_columns_no_edge a c b hxy
    | inr hr => exact raw_to_target_no_edge a b y hr hxy
  · intro b x hr ih y hy hxy
    cases column_cases hy with
    | inl hh =>
      cases hh with
      | intro a ha =>
        rw [ha] at hxy
        exact target_to_raw_no_edge a b x hr hxy
    | inr ht => exact ih y ht hxy
  · intro x z y hy hxy
    have he := target_point_unique x z y hy
    rw [he] at hxy
    exact column_ne_self hxy
  · intro z v x hz hc _ ih y hy hxy
    exact ih y (target_inherit_cases z v y hz hy) hxy

theorem step_middle_no_code {x z v : Tree} (hs : Step x z v) :
    ∀ o, ¬ Code v z o := by
  cases hs with
  | raw =>
    intro o hc
    exact target_to_raw_no_edge x z o hc.1 hc.2
  | hit hh =>
    intro o hc
    exact column_triangle_free (Column.target hc.1) v (Column.target hh.1) hc.2

theorem step_outer_no_code {x z v : Tree} (hs : Step x z v) :
    ∀ o, ¬ Code z (pair v z) o := by
  cases hs with
  | raw =>
    intro o hc
    exact raw_double_not_target x z o hc.1
  | hit hh =>
    intro o hc
    exact target_right_empty hc.1 v hh.1

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

theorem op_middle_raw (x z : Tree) : op (op x z) z = pair (op x z) z :=
  op_miss _ _ (step_middle_no_code (op_step x z))

theorem op_outer_raw (x z : Tree) :
    op z (pair (op x z) z) = pair z (pair (op x z) z) :=
  op_miss _ _ (step_outer_no_code (op_step x z))

theorem source_law : SourceLaw op :=
  template_law op op_step op_hit op_middle_raw op_outer_raw

theorem source_law_explicit (x y z : Tree) :
    x = op (op y x) (op z (op (op x z) z)) := source_law x y z

theorem nontrivial : ∃ a b : Tree, a ≠ b := by
  refine ⟨atom 0, atom 1, ?_⟩
  intro he
  exact Nat.noConfusion (Tree.atom.inj he)

theorem infinite_model : ∃ (G : Type) (f : G → G → G) (embed : Nat → G),
    (∀ x y z, x = f (f y x) (f z (f (f x z) z))) ∧
    (∀ m n, embed m = embed n → m = n) :=
  ⟨Tree, op, atom, source_law_explicit, atom_injective⟩

end submission.Equation18137TreeSchema


/- Module: DualModel -/
set_option autoImplicit false

namespace submission.Equation27863TreeModel

abbrev Carrier := submission.Equation18137TreeSchema.Tree

noncomputable def op (a b : Carrier) : Carrier := submission.Equation18137TreeSchema.op b a

/- Reversal of the operation, with the last two source variables exchanged. -/
theorem source_law_explicit (x y z : Carrier) :
    x = op (op (op y (op y x)) y) (op x z) :=
  submission.Equation18137TreeSchema.source_law_explicit x z y

def embed : Nat → Carrier := submission.Equation18137TreeSchema.Tree.atom

theorem embed_injective (m n : Nat) (he : embed m = embed n) : m = n :=
  submission.Equation18137TreeSchema.atom_injective m n he

theorem nontrivial : ∃ a b : Carrier, a ≠ b := submission.Equation18137TreeSchema.nontrivial

theorem infinite_model : ∃ (G : Type) (f : G → G → G) (e : Nat → G),
    (∀ x y z, x = f (f (f y (f y x)) y) (f x z)) ∧
    (∀ m n, e m = e n → m = n) :=
  ⟨Carrier, op, embed, source_law_explicit, embed_injective⟩

end submission.Equation27863TreeModel


namespace submission
abbrev CM := submission.Equation27863TreeModel.Carrier
noncomputable instance modelMagma : Magma CM := ⟨submission.Equation27863TreeModel.op⟩
namespace CM
theorem tower_injective (m n : Nat)
    (he : submission.Equation27863TreeModel.embed m = submission.Equation27863TreeModel.embed n) : m = n :=
  submission.Equation27863TreeModel.embed_injective m n he
end CM
end submission

theorem submission : Goal := by
  refine ⟨submission.CM, submission.modelMagma, ?_, ?_⟩
  · exact submission.Equation27863TreeModel.source_law_explicit
  · intro h
    exact Nat.noConfusion (submission.Equation27863TreeModel.embed_injective 0 1
      (h (submission.Equation27863TreeModel.embed 0) (submission.Equation27863TreeModel.embed 1)))

example : Goal := submission
example (x y z : submission.CM) :
    x = ((y ◇ (y ◇ x)) ◇ y) ◇ (x ◇ z) :=
  submission.Equation27863TreeModel.source_law_explicit x y z

#print axioms submission
#print axioms submission.CM.tower_injective
#print axioms submission.Equation27863TreeModel.infinite_model

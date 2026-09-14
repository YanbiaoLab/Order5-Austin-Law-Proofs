prelude
import TreeUnique
set_option autoImplicit false

namespace Equation18137TreeSchema
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

end Equation18137TreeSchema

#print axioms Equation18137TreeSchema.column_triangle_free
#print axioms Equation18137TreeSchema.step_middle_no_code
#print axioms Equation18137TreeSchema.step_outer_no_code
#print axioms Equation18137TreeSchema.op_step
#print axioms Equation18137TreeSchema.op_hit
#print axioms Equation18137TreeSchema.source_law_explicit
#print axioms Equation18137TreeSchema.nontrivial
#print axioms Equation18137TreeSchema.infinite_model

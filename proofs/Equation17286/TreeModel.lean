prelude
import TreeGeometry
set_option autoImplicit false

namespace Equation17286Tree
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

end Equation17286Tree

#print axioms Equation17286Tree.column_no_three_cycle
#print axioms Equation17286Tree.column_prefix_no_target
#print axioms Equation17286Tree.step_middle_no_code
#print axioms Equation17286Tree.step_outer_no_code
#print axioms Equation17286Tree.source_law_explicit
#print axioms Equation17286Tree.nontrivial
#print axioms Equation17286Tree.infinite_model
#print axioms Equation17286Tree.dual_source_law_explicit
#print axioms Equation17286Tree.dual_infinite_model

prelude
import TreeBounds
set_option autoImplicit false

namespace Equation17286Tree
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

end Equation17286Tree

#print axioms Equation17286Tree.column_geometry
#print axioms Equation17286Tree.column_fork_unique
#print axioms Equation17286Tree.column_triangle_free
#print axioms Equation17286Tree.target_right_empty
#print axioms Equation17286Tree.code_output_unique

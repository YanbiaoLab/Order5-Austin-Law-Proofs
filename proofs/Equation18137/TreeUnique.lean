prelude
import TreeBounds
set_option autoImplicit false

namespace Equation18137TreeSchema
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

end Equation18137TreeSchema

#print axioms Equation18137TreeSchema.raw_columns_unique
#print axioms Equation18137TreeSchema.raw_target_columns_disjoint
#print axioms Equation18137TreeSchema.target_point_unique
#print axioms Equation18137TreeSchema.target_inherit_cases
#print axioms Equation18137TreeSchema.column_fork_unique
#print axioms Equation18137TreeSchema.code_output_unique

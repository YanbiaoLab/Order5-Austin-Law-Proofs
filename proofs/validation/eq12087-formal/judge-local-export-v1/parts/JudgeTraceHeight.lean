prelude
import Init.Data.Option.Lemmas
import Init.Omega
import Init.RCases
import Init.WFTactics
import JudgeTraceFold
set_option Elab.async false
/- Checked module: TraceHeight -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

def ht : T → Nat
  | atom _ => 1
  | s a => ht a + 1
  | p a b => max (ht a) (ht b) + 1
  | c y x z a b => max (ht y) (max (ht x) (max (ht z) (max (ht a) (ht b)))) + 1

theorem origin_height {out a b : T} (h : origin out = some (a,b)) :
    ht a < ht out ∧ ht b < ht out := by
  cases out with
  | atom n => simp only [origin] at h; cases h
  | s t =>
    obtain ⟨ha,hb⟩ := Prod.mk.inj (Option.some.inj h)
    subst a; subst b; simp only [ht]; omega
  | p l r =>
    obtain ⟨ha,hb⟩ := Prod.mk.inj (Option.some.inj h)
    subst a; subst b; simp only [ht]; omega
  | c y x z l r =>
    obtain ⟨ha,hb⟩ := Prod.mk.inj (Option.some.inj h)
    subst a; subst b; simp only [ht]; omega

theorem mul_height_shape (a b : T) :
    (ht a < ht (mul a b) ∧ ht b < ht (mul a b) ∧ origin (mul a b) = some (a,b)) ∨
    ∃ x z l r, b = c a x z l r ∧ mul a b = x := by
  rcases mul_grows_or_returns a b with hg | hr
  · have hh := origin_height hg.2.2
    exact Or.inl ⟨hh.1,hh.2,hg.2.2⟩
  · exact Or.inr hr

theorem inverse_height_strict {b out a : T} (h : inverse b out = some a) :
    ht a < max (ht b) (ht out) := by
  rcases inverse_cases h with ⟨rfl,rfl⟩ | ⟨ho,_⟩ | hb
  · simp only [ht]; omega
  · have hh := origin_height ho; omega
  · obtain ⟨z,l,r,hb⟩ := basicInverse_cases hb
    rw [hb]; simp only [ht]; omega

theorem distinct_outputs_height_origin {u x z a b : T}
    (ha : mul u z = a) (hb : mul x z = b) (hne : a ≠ b)
    (hs : ht b ≤ ht a) : origin a = some (u,z) ∧ ht z < ht a := by
  rcases mul_height_shape u z with hg | ⟨v,k,l,r,hz,hm⟩
  · rw [ha] at hg; exact ⟨hg.2.2,hg.2.1⟩
  · have hv : v = a := hm.symm.trans ha
    rw [hv] at hz
    have hza : ht a < ht z := by rw [hz]; simp only [ht]; omega
    rcases mul_height_shape x z with hg | ⟨v',k',l',r',hz',hm'⟩
    · rw [hb] at hg; omega
    · have hv' : v' = b := hm'.symm.trans hb
      rw [hv'] at hz'
      have hp := T.c.inj (hz.symm.trans hz')
      exact False.elim (hne hp.2.1)

theorem common_column_height_bounds {a b y x z : T}
    (ha : mul (mul y x) z = a) (hb : mul x z = b) :
    ht y < max (ht a) (ht b) ∧ ht x < max (ht a) (ht b) ∧ ht z < max (ht a) (ht b) := by
  have hn : a ≠ b := by
    intro he
    exact mul_ne_right y x (right_injective _ _ z (ha.trans (he.trans hb.symm)))
  have ix := inverse_height_strict (inverse_complete x z)
  have iu := inverse_height_strict (inverse_complete (mul y x) z)
  have iy := inverse_height_strict (inverse_complete y x)
  rw [ha] at iu; rw [hb] at ix
  by_cases hs : ht b ≤ ht a
  · have ho := (distinct_outputs_height_origin ha hb hn hs).1
    have hh := origin_height ho
    exact ⟨by omega,by omega,by omega⟩
  · have ho := (distinct_outputs_height_origin hb ha (Ne.symm hn) (by omega)).1
    have hh := origin_height ho
    exact ⟨by omega,by omega,by omega⟩

theorem mul_height_growth_or_return (a b : T) :
    ht (mul a b) = max (ht a) (ht b) + 1 ∨
    ∃ x z l r, b = c a x z l r ∧ mul a b = x := by
  rcases mul_cases a b with ⟨he,hm⟩ | hr | hm | ⟨y,x,z,hm⟩
  · exact Or.inl (by rw [hm,he]; simp only [ht]; omega)
  · exact Or.inr hr
  · exact Or.inl (by rw [hm]; rfl)
  · have hc := mul_code_semantics hm
    have hh := common_column_height_bounds hc.1 hc.2
    apply Or.inl
    rw [hm]; simp only [ht]; omega

theorem mul_height_upper (a b : T) : ht (mul a b) ≤ max (ht a) (ht b) + 1 := by
  rcases mul_height_growth_or_return a b with hg | ⟨x,z,l,r,hb,hm⟩
  · omega
  · rw [hm,hb]; simp only [ht]; omega

theorem nf_code_height_gap {y x z a b : T} (hn : NF (c y x z a b)) :
    ht y + 2 ≤ ht (c y x z a b) ∧ ht x + 2 ≤ ht (c y x z a b) ∧
      ht z + 2 ≤ ht (c y x z a b) := by
  have hc := nf_code_actual hn
  have hh := common_column_height_bounds hc.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2
  simp only [ht]
  exact ⟨by omega,by omega,by omega⟩

theorem nf_mul_height_alternatives {a b : T} (hb : NF b) :
    ht (mul a b) = max (ht a) (ht b) + 1 ∨
      (ht a + 2 ≤ ht b ∧ ht (mul a b) + 2 ≤ ht b) := by
  rcases mul_height_growth_or_return a b with hg | ⟨x,z,l,r,hb',hm⟩
  · exact Or.inl hg
  · have hnf := hb' ▸ hb
    have hh := nf_code_height_gap hnf
    exact Or.inr (by rw [hm,hb']; exact ⟨hh.1,hh.2.1⟩)

end submission.Austin12087Trace

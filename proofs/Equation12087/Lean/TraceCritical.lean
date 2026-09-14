prelude
import TraceSource
set_option autoImplicit false

namespace Austin12087Trace
open T

theorem inverse_strict_size {b out a : T} (h : inverse b out = some a) :
    sz a < max (sz b) (sz out) := by
  rcases inverse_cases h with ⟨rfl,rfl⟩ | ⟨ho,_⟩ | hb
  · simp only [sz]; omega
  · have hs := origin_size ho; omega
  · obtain ⟨z,l,r,hb⟩ := basicInverse_cases hb
    rw [hb]; simp only [sz]; omega

theorem common_column_inputs_small {a b y x z : T}
    (ha : mul (mul y x) z = a) (hb : mul x z = b) :
    sz y < max (sz a) (sz b) ∧ sz x < max (sz a) (sz b) ∧ sz z < max (sz a) (sz b) := by
  have hn : a ≠ b := by
    intro h
    exact mul_ne_right y x (right_injective (mul y x) x z (ha.trans (h.trans hb.symm)))
  have ix := inverse_strict_size (inverse_complete x z)
  have iu := inverse_strict_size (inverse_complete (mul y x) z)
  have iy := inverse_strict_size (inverse_complete y x)
  rw [ha] at iu; rw [hb] at ix
  by_cases hs : sz b ≤ sz a
  · have ho := (distinct_outputs_large_origin ha hb hn hs).1
    have hsz := origin_size ho
    exact ⟨by omega,by omega,by omega⟩
  · have hs' : sz a ≤ sz b := by omega
    have ho := (distinct_outputs_large_origin hb ha (Ne.symm hn) hs').1
    have hsz := origin_size ho
    exact ⟨by omega,by omega,by omega⟩

theorem code_choices_agree {n : Nat} {a b v w : T}
    (hl : leftCode (queryM n) (queryI n) a b = some v)
    (hr : rightCode (queryM n) (queryI n) a b = some w) : v = w := by
  obtain ⟨y,x,z,hv,ha,hb⟩ := leftCode_sound hl
  obtain ⟨y',x',z',hw,ha',hb'⟩ := rightCode_sound hr
  obtain ⟨hy,hx,hz⟩ := common_column_data_unique ha hb ha' hb'
  rw [hv,hw,hy,hx,hz]

theorem critical_first_or_second_return {x y z q t l r : T}
    (h : mul x z = c (mul (mul y x) z) q t l r) :
    sz (mul y x) < sz x ∨ sz (mul (mul y x) z) < sz z := by
  obtain ⟨hl,hr,hx,hz⟩ := critical_return_trace h
  have bound := (common_column_inputs_small hx hz).1
  rcases mul_grows_or_returns y x with ⟨_,h1,_⟩ | ⟨v,s,a,b,hx',hm⟩
  · rcases mul_grows_or_returns (mul y x) z with ⟨h2,h3,_⟩ | ⟨v,s,a,b,hz',hm⟩
    · omega
    · exact Or.inr ((mul_small_iff _ _).mpr ⟨v,s,a,b,hz'⟩)
  · exact Or.inl ((mul_small_iff _ _).mpr ⟨v,s,a,b,hx'⟩)

theorem source_when_first_two_do_not_return (x y z : T)
    (h1 : sz x ≤ sz (mul y x))
    (h2 : sz z ≤ sz (mul (mul y x) z)) : Source12087 x y z := by
  apply source_without_middle_return
  intro q t l r h
  rcases critical_first_or_second_return h with hs | hs <;> omega

def PlainRight : T → Prop
  | c _ _ _ _ _ => False
  | _ => True

theorem plain_right_grows (a b : T) (h : PlainRight b) : sz b < sz (mul a b) := by
  rcases mul_grows_or_returns a b with hg | ⟨x,z,l,r,hb,hm⟩
  · exact hg.2.1
  · rw [hb] at h; exact False.elim h

theorem source_for_plain_right_inputs (x y z : T) (hx : PlainRight x) (hz : PlainRight z) :
    Source12087 x y z :=
  source_when_first_two_do_not_return x y z
    (Nat.le_of_lt (plain_right_grows y x hx))
    (Nat.le_of_lt (plain_right_grows (mul y x) z hz))

theorem source_square_parameters (a y b : T) : Source12087 (s a) y (s b) :=
  source_for_plain_right_inputs (s a) y (s b) True.intro True.intro

end Austin12087Trace
#print axioms Austin12087Trace.inverse_strict_size
#print axioms Austin12087Trace.common_column_inputs_small
#print axioms Austin12087Trace.code_choices_agree
#print axioms Austin12087Trace.critical_first_or_second_return
#print axioms Austin12087Trace.source_when_first_two_do_not_return
#print axioms Austin12087Trace.plain_right_grows
#print axioms Austin12087Trace.source_for_plain_right_inputs
#print axioms Austin12087Trace.source_square_parameters

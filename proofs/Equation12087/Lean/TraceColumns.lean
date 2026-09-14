prelude
import TraceInverse
set_option autoImplicit false

namespace Austin12087Trace
open T

theorem distinct_outputs_large_origin {a b u x z : T}
    (ha : mul u z = a) (hb : mul x z = b) (hne : a ≠ b) (hs : sz b ≤ sz a) :
    origin a = some (u,z) ∧ sz z < sz a := by
  rcases mul_grows_or_returns u z with ⟨hu,hz,ho⟩ | ⟨v,t,l,r,hz,hv⟩
  · exact ⟨by rw [←ha]; exact ho,by rw [←ha]; exact hz⟩
  · have hav : a = v := ha.symm.trans hv
    have has : sz a < sz z := by rw [hav,hz]; simp only [sz]; omega
    have hbs : sz (mul x z) < sz z := by rw [hb]; omega
    obtain ⟨v',t',l',r',hz'⟩ := (mul_small_iff x z).mp hbs
    have hux : u = x := (T.c.inj (hz.symm.trans hz')).1
    exact False.elim (hne (ha.symm.trans ((congrArg (fun k => mul k z) hux).trans hb)))

theorem common_column_key_unique {a b u x z v w t : T}
    (ha : mul u z = a) (hb : mul x z = b)
    (ha' : mul v t = a) (hb' : mul w t = b) (hne : a ≠ b) : z = t := by
  by_cases hs : sz b ≤ sz a
  · have h1 := (distinct_outputs_large_origin ha hb hne hs).1
    have h2 := (distinct_outputs_large_origin ha' hb' hne hs).1
    exact (Prod.mk.inj (Option.some.inj (h1.symm.trans h2))).2
  · have hsa : sz a ≤ sz b := by omega
    have h1 := (distinct_outputs_large_origin hb ha (Ne.symm hne) hsa).1
    have h2 := (distinct_outputs_large_origin hb' ha' (Ne.symm hne) hsa).1
    exact (Prod.mk.inj (Option.some.inj (h1.symm.trans h2))).2

theorem common_column_data_unique {a b y x z y' x' z' : T}
    (ha : mul (mul y x) z = a) (hb : mul x z = b)
    (ha' : mul (mul y' x') z' = a) (hb' : mul x' z' = b) :
    y = y' ∧ x = x' ∧ z = z' := by
  have hne : a ≠ b := by
    intro h
    have hu := right_injective (mul y x) x z (ha.trans (h.trans hb.symm))
    exact mul_ne_right y x hu
  have hz := common_column_key_unique ha hb ha' hb' hne
  subst z'
  have hx := right_injective x x' z (hb.trans hb'.symm)
  subst x'
  have hu := right_injective (mul y x) (mul y' x) z (ha.trans ha'.symm)
  exact ⟨right_injective y y' x hu,rfl,rfl⟩

theorem queryM_sound {n : Nat} {a b out : T} (h : queryM n a b = some out) : mul a b = out := by
  by_cases hn : rankM a b < n
  · simpa only [queryM,hn,↓reduceIte,Option.some.injEq] using h
  · simp only [queryM,hn,↓reduceIte] at h; cases h

theorem queryI_sound {n : Nat} {a b out : T} (h : queryI n a b = some out) : inverse a b = some out := by
  by_cases hn : rankI a b < n
  · simpa only [queryI,hn,↓reduceIte] using h
  · simp only [queryI,hn,↓reduceIte] at h; cases h

theorem leftCode_complete {a b y x z : T}
    (ho : origin a = some (mul y x,z))
    (ha : mul (mul y x) z = a) (hb : mul x z = b) :
    leftCode (queryM (rankM a b)) (queryI (rankM a b)) a b = some (c y x z a b) := by
  have hos := origin_size ho
  have hxb := inverse_size (inverse_complete x z)
  rw [hb] at hxb
  have hm : rankM (mul y x) z < rankM a b := by simp only [rankM]; omega
  have hi : rankI z b < rankM a b := by simp only [rankI,rankM]; omega
  have hi' : rankI x (mul y x) < rankM a b := by simp only [rankI,rankM]; omega
  have ix : inverse z b = some x := by rw [←hb]; exact inverse_complete x z
  have iy : inverse x (mul y x) = some y := inverse_complete y x
  simp only [leftCode,ho,queryM,queryI,hm,hi,hi',ha,ix,iy,↓reduceIte]

theorem rightCode_complete {a b y x z : T}
    (ho : origin b = some (x,z))
    (ha : mul (mul y x) z = a) (hb : mul x z = b) :
    rightCode (queryM (rankM a b)) (queryI (rankM a b)) a b = some (c y x z a b) := by
  have hos := origin_size ho
  have hub := inverse_size (inverse_complete (mul y x) z)
  rw [ha] at hub
  have hm : rankM x z < rankM a b := by simp only [rankM]; omega
  have hi : rankI z a < rankM a b := by simp only [rankI,rankM]; omega
  have hi' : rankI x (mul y x) < rankM a b := by simp only [rankI,rankM]; omega
  have iu : inverse z a = some (mul y x) := by rw [←ha]; exact inverse_complete (mul y x) z
  have iy : inverse x (mul y x) = some y := inverse_complete y x
  simp only [rightCode,ho,queryM,queryI,hm,hi,hi',hb,iu,iy,↓reduceIte]

end Austin12087Trace
#print axioms Austin12087Trace.distinct_outputs_large_origin
#print axioms Austin12087Trace.common_column_key_unique
#print axioms Austin12087Trace.common_column_data_unique
#print axioms Austin12087Trace.queryM_sound
#print axioms Austin12087Trace.queryI_sound
#print axioms Austin12087Trace.leftCode_complete
#print axioms Austin12087Trace.rightCode_complete

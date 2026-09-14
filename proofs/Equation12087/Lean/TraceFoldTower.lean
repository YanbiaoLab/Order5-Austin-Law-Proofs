prelude
import TraceFlip
set_option autoImplicit false

namespace Austin12087Trace
open T

theorem mul_origin_of_right_height_le {a b : T} (hh : ht b ≤ ht (mul a b)) :
    origin (mul a b) = some (a,b) := by
  rcases mul_height_shape a b with hg | ⟨x,z,l,r,hb,hm⟩
  · exact hg.2.2
  · rw [hm,hb] at hh; simp only [ht] at hh; omega

theorem mul_return_of_height_lt {a b : T} (hh : ht (mul a b) < ht b) :
    ∃ z l r, b = c a (mul a b) z l r := by
  rcases mul_height_shape a b with hg | ⟨x,z,l,r,hb,hm⟩
  · omega
  · exact ⟨z,l,r,by rw [hm]; exact hb⟩

theorem mul_height_growth_of_left_ge {a b : T} (hh : ht b ≤ ht a) :
    ht (mul a b) = max (ht a) (ht b) + 1 := by
  rcases mul_height_growth_or_return a b with hg | ⟨x,z,l,r,hb,_⟩
  · exact hg
  · rw [hb] at hh; simp only [ht] at hh; omega

theorem mul_height_growth_of_right_le {a b : T} (hh : ht b ≤ ht (mul a b)) :
    ht (mul a b) = max (ht a) (ht b) + 1 := by
  rcases mul_height_growth_or_return a b with hg | ⟨x,z,l,r,hb,hm⟩
  · exact hg
  · rw [hm,hb] at hh; simp only [ht] at hh; omega

theorem fold_next_trace {u a t j : T} (hf : FoldWitness u a t j) :
    ∃ h r s,
      j = c (mul u t) (mul u a) r t h ∧
      h = c (mul a t) t s (mul u a) r ∧
      mul (mul (mul a t) t) s = mul u a ∧ mul t s = r ∧
      mul (mul (mul u t) (mul u a)) r = t ∧ mul (mul u a) r = h ∧
      mul t h = j ∧ ht t < ht h := by
  obtain ⟨h,r,hj,het,hwh,_,_,_⟩ := fold_column_trace hf
  -- Recover the same h from the right input stored in j, without choosing an
  -- unrelated existential witness from the earlier outer trace.
  obtain ⟨h',hb',hth',hj',_,_,hhs⟩ := fold_outer_trace hf
  have hn : h' = h := by
    have ho := mul_origin_of_right_le (a:=t) (b:=h') (by
      rw [hj']; omega)
    rw [hj',hj,origin] at ho
    exact (Prod.mk.inj (Option.some.inj ho)).2.symm
  subst h'
  have hc := common_column_height_bounds het hwh
  have hth : ht t < ht h := by
    by_cases hh : ht t < ht h
    · exact hh
    apply False.elim
    have ho := mul_origin_of_right_height_le (a:=mul a t) (b:=h) (by rw [hth']; omega)
    have ho' := mul_origin_of_right_height_le (a:=mul (mul u t) (mul u a)) (b:=r) (by rw [het]; omega)
    rw [hth'] at ho
    rw [het,ho] at ho'
    have hp := Prod.mk.inj (Option.some.inj ho')
    exact mul_ne_right (mul u a) r (hwh.trans hp.2)
  obtain ⟨s,l,b,hcode⟩ := mul_return_of_height_lt (a:=mul a t) (b:=h) (by rw [hth']; exact hth)
  rw [hth'] at hcode
  have hor := mul_origin_of_right_height_le (a:=mul u a) (b:=r) (by rw [hwh]; omega)
  rw [hwh] at hor
  conv at hor => lhs; rw [hcode,origin]
  obtain ⟨hl,hb⟩ := Prod.mk.inj (Option.some.inj hor)
  subst l; subst b
  have hs := mul_code_semantics (hwh.trans hcode)
  exact ⟨h,r,s,hj,hcode,hs.1,hs.2,het,hwh,hj',hth⟩

theorem fold_trace_right_dominates {u a t r s : T}
    (hw : mul (mul (mul a t) t) s = mul u a) (hr : mul t s = r)
    (het : mul (mul (mul u t) (mul u a)) r = t) : ht (mul u a) < ht r := by
  have hc := common_column_height_bounds hw hr
  by_cases hwr : ht (mul u a) < ht r
  · exact hwr
  apply False.elim
  have hat := inverse_height_strict (inverse_complete a t)
  have ha : ht a < ht (mul u a) := by omega
  have hwg := mul_height_growth_of_right_le (a:=u) (b:=a) (by omega)
  have he := inverse_height_strict (inverse_complete (mul (mul u t) (mul u a)) r)
  rw [het] at he
  have hes : ht (mul (mul u t) (mul u a)) < ht (mul u a) := by omega
  obtain ⟨k,l,b,hcode⟩ := mul_return_of_height_lt hes
  have hq : ht (mul u t) < ht (mul u a) := by
    conv => rhs; rw [hcode]
    simp only [ht]; omega
  by_cases hua : ht u ≤ ht a
  · have hdt := mul_height_growth_of_left_ge (a:=a) (b:=t) (by omega)
    omega
  · have hqt := mul_height_growth_of_left_ge (a:=u) (b:=t) (by omega)
    omega

theorem fold_height_tower {u a t j : T} (hf : FoldWitness u a t j) :
    ∃ h r s,
      j = c (mul u t) (mul u a) r t h ∧
      h = c (mul a t) t s (mul u a) r ∧
      ht r = ht s + 1 ∧ ht h = ht s + 2 ∧ ht j = ht s + 3 ∧
      ht u < ht s ∧ ht a < ht s ∧ ht t < ht s ∧ ht (mul u a) < ht s := by
  obtain ⟨h,r,s,hj,hh,hw,hr,het,hwh,htj,hth⟩ := fold_next_trace hf
  have hc := common_column_height_bounds hw hr
  have hwr := fold_trace_right_dominates hw hr het
  have htr : ht t < ht r := by omega
  obtain ⟨k,l,b,hcode⟩ := mul_return_of_height_lt (a:=mul (mul u t) (mul u a)) (b:=r) (by rw [het]; exact htr)
  rw [het] at hcode
  have hor := mul_origin_of_right_height_le (a:=t) (b:=s) (by rw [hr]; omega)
  rw [hr] at hor
  conv at hor => lhs; rw [hcode,origin]
  obtain ⟨hl,hb⟩ := Prod.mk.inj (Option.some.inj hor)
  subst l; subst b
  have hsem := mul_code_semantics (hr.trans hcode)
  have hts : ht t < ht s := by
    have hb := common_column_height_bounds hsem.1 hsem.2
    omega
  have hrg := mul_height_growth_of_right_le (a:=t) (b:=s) (by rw [hr]; omega)
  rw [hr] at hrg
  have hhh : ht r < ht h := by rw [hh]; simp only [ht]; omega
  have hhg := mul_height_growth_of_right_le (a:=mul u a) (b:=r) (by rw [hwh]; omega)
  rw [hwh] at hhg
  have hjh : ht h < ht j := by rw [hj]; simp only [ht]; omega
  have hjg := mul_height_growth_of_right_le (a:=t) (b:=h) (by rw [htj]; omega)
  rw [htj] at hjg
  have hws : ht (mul u a) < ht s := by
    rcases mul_height_shape (mul (mul a t) t) s with hg | ⟨x,z,l,b,hs,hm⟩
    · rw [hw] at hg; omega
    · have hx : x = mul u a := hm.symm.trans hw
      rw [hx] at hs
      conv => rhs; rw [hs]
      simp only [ht]; omega
  have hai := inverse_height_strict (inverse_complete a t)
  have hui := inverse_height_strict (inverse_complete u a)
  exact ⟨h,r,s,hj,hh,by omega,by omega,by omega,by omega,by omega,hts,hws⟩

theorem normal_fold_height_parameter {u a t j : T} (hj : NF j) (hf : FoldWitness u a t j) :
    ∃ s, NF s ∧ ht j = ht s + 3 ∧
      ht u < ht s ∧ ht a < ht s ∧ ht t < ht s ∧ ht (mul u a) < ht s := by
  obtain ⟨h,r,s,hjc,hhc,_,_,hjs,hus,has,hts,hws⟩ := fold_height_tower hf
  rw [hjc] at hj
  have hh : NF h := (nf_code_actual hj).2.2.2.2.1
  rw [hhc] at hh
  exact ⟨s,(nf_code_actual hh).2.2.1,hjs,hus,has,hts,hws⟩

theorem common_column_key_height_gap {a b y x z : T}
    (ha : mul (mul y x) z = a) (hb : mul x z = b) :
    ht y + 2 ≤ max (ht a) (ht b) := by
  have hc := common_column_height_bounds ha hb
  by_cases hh : ht y + 2 ≤ max (ht a) (ht b)
  · exact hh
  apply False.elim
  have hu := mul_height_growth_of_left_ge (a:=y) (b:=x) (by omega)
  have haa := mul_height_growth_of_left_ge (a:=mul y x) (b:=z) (by omega)
  rw [ha] at haa
  omega

theorem nf_code_key_height_gap {y x z a b : T} (hn : NF (c y x z a b)) :
    ht y + 3 ≤ ht (c y x z a b) := by
  have hc := nf_code_actual hn
  have hh := common_column_key_height_gap hc.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2
  simp only [ht]
  omega

theorem nf_mul_height_key_gap {a b : T} (hn : NF b) :
    ht (mul a b) = max (ht a) (ht b) + 1 ∨
      (ht a + 3 ≤ ht b ∧ ht (mul a b) + 2 ≤ ht b) := by
  rcases mul_height_growth_or_return a b with hg | ⟨x,z,l,r,hb,hm⟩
  · exact Or.inl hg
  · have hc : NF (c a x z l r) := hb ▸ hn
    have hy := nf_code_key_height_gap hc
    have hx := (nf_code_height_gap hc).2.1
    exact Or.inr (by rw [hm,hb]; exact ⟨hy,hx⟩)

end Austin12087Trace
#print axioms Austin12087Trace.mul_origin_of_right_height_le
#print axioms Austin12087Trace.mul_return_of_height_lt
#print axioms Austin12087Trace.mul_height_growth_of_left_ge
#print axioms Austin12087Trace.mul_height_growth_of_right_le
#print axioms Austin12087Trace.fold_next_trace
#print axioms Austin12087Trace.fold_trace_right_dominates
#print axioms Austin12087Trace.fold_height_tower
#print axioms Austin12087Trace.normal_fold_height_parameter
#print axioms Austin12087Trace.common_column_key_height_gap
#print axioms Austin12087Trace.nf_code_key_height_gap
#print axioms Austin12087Trace.nf_mul_height_key_gap

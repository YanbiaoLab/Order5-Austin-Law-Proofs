prelude
import TraceNormalQueries
set_option autoImplicit false

namespace Austin12087Trace
open T

theorem no_untransposed_code (a b k : T) : mul a b ≠ c a b k a b := by
  intro h
  have hc := mul_code_semantics h
  have hs := common_column_inputs_small hc.1 hc.2
  omega

theorem no_left_two_cycle (a b : T) : mul a (mul a b) ≠ b := by
  intro he
  rcases mul_grows_or_returns a b with hg | ⟨v,k,l,r,hb,hv⟩
  · have hs : sz (mul a (mul a b)) < sz (mul a b) := by rw [he]; exact hg.2.1
    obtain ⟨v,k,l,r,hv⟩ := (mul_small_iff a (mul a b)).mp hs
    have hvb : v = b := by rw [hv,mul_code_return] at he; exact he
    subst v
    have ho := hg.2.2
    conv at ho => lhs; rw [hv,origin]
    obtain ⟨hl,hr⟩ := Prod.mk.inj (Option.some.inj ho)
    subst l; subst r
    exact no_untransposed_code a b k hv
  · have hav : mul a v = b := by rw [hv] at he; exact he
    have hs : sz v ≤ sz (mul a v) := by rw [hav,hb]; simp only [sz]; omega
    have ho := mul_origin_of_right_le hs
    rw [hav,hb,origin] at ho
    obtain ⟨hl,hr⟩ := Prod.mk.inj (Option.some.inj ho)
    subst l; subst r
    exact no_untransposed_code a v k (hav.trans hb)

def FoldWitness (u a t j : T) : Prop :=
  mul u a = mul (mul u t) j ∧ mul a (mul t j) = t

theorem fold_right_larger {u a t j : T} (hf : FoldWitness u a t j) :
    sz (mul u a) < sz (mul t j) := by
  obtain ⟨hw,ht⟩ := hf
  have hb := common_column_inputs_small hw.symm (show mul t j = mul t j from rfl)
  have ha := inverse_strict_size (inverse_complete a (mul t j))
  rw [ht] at ha
  by_cases hs : sz (mul u a) < sz (mul t j)
  · exact hs
  apply False.elim
  have hwa : sz a ≤ sz (mul u a) := by omega
  have hwj : sz j ≤ sz (mul (mul u t) j) := by rw [←hw]; omega
  have ho := mul_origin_of_right_le hwa
  have ho' := mul_origin_of_right_le hwj
  rw [←hw,ho] at ho'
  have hp := Prod.mk.inj (Option.some.inj ho')
  rw [←hp.2] at ht
  exact no_cross_two_cycle t a ht

theorem fold_outer_trace {u a t j : T} (hf : FoldWitness u a t j) :
    ∃ h, mul t j = c a t h t j ∧ mul (mul a t) h = t ∧ mul t h = j ∧
      sz a < sz j ∧ sz t < sz j ∧ sz h < sz j := by
  obtain ⟨hw,ht⟩ := hf
  have hwb := fold_right_larger ⟨hw,ht⟩
  have hb := common_column_inputs_small hw.symm (show mul t j = mul t j from rfl)
  have hsmall : sz (mul a (mul t j)) < sz (mul t j) := by rw [ht]; omega
  obtain ⟨v,h,l,r,hc⟩ := (mul_small_iff a (mul t j)).mp hsmall
  have hvt : v = t := by rw [hc,mul_code_return] at ht; exact ht
  subst v
  have hbj : sz j ≤ sz (mul t j) := by omega
  have ho := mul_origin_of_right_le hbj
  conv at ho => lhs; rw [hc,origin]
  obtain ⟨hl,hr⟩ := Prod.mk.inj (Option.some.inj ho)
  subst l; subst r
  have hsem := mul_code_semantics hc
  have hbound := common_column_inputs_small hsem.1 hsem.2
  exact ⟨h,hc,hsem.1,hsem.2,by omega,by omega,by omega⟩

theorem normal_first_diagonal_fold_descent {u k y : T} (hu : NF u) (hk : NF k)
    (hf : mul (mul y u) k = mul (mul u (mul k (mul u k))) k) :
    ∃ a t j, NF a ∧ NF t ∧ NF j ∧
      sz u < sz k ∧ sz a < sz k ∧ sz t < sz k ∧ sz j < sz k ∧ FoldWitness u a t j := by
  obtain ⟨a,h,hts,hus,has,hhs,_,hz⟩ := first_diagonal_descent_trace hf
  have hnz := nf_mul hk (nf_mul hu hk)
  rw [hz] at hnz
  have hn := nf_code_actual hnz
  have hs := mul_code_semantics hz
  have hka : mul (mul u a) h = k := hs.1
  have hat : mul a h = mul u k := hs.2
  obtain ⟨t,j,l,r,hkc⟩ := (mul_small_iff u k).mp hts
  have htt : t = mul u k := by rw [hkc,mul_code_return]
  have hok := mul_origin_of_right_le (a:=mul u a) (b:=h) (by rw [hka]; omega)
  rw [hka] at hok
  conv at hok => lhs; rw [hkc,origin]
  obtain ⟨hl,hr⟩ := Prod.mk.inj (Option.some.inj hok)
  subst l; subst r
  have hks := mul_code_semantics (hka.trans hkc)
  have hnk := hk
  rw [hkc] at hnk
  have hnj := (nf_code_actual hnk).2.2.1
  have hnt : NF t := htt.symm ▸ nf_mul hu hk
  have hj : sz j < sz k := by rw [hkc]; simp only [sz]; omega
  have hft : FoldWitness u a t j := by
    refine ⟨hks.1.symm,?_⟩
    rw [hks.2]
    exact hat.trans htt.symm
  exact ⟨a,t,j,hn.2.1,hnt,hnj,hus,has,by rw [htt]; exact hts,hj,hft⟩

end Austin12087Trace
#print axioms Austin12087Trace.no_untransposed_code
#print axioms Austin12087Trace.no_left_two_cycle
#print axioms Austin12087Trace.fold_right_larger
#print axioms Austin12087Trace.fold_outer_trace
#print axioms Austin12087Trace.normal_first_diagonal_fold_descent

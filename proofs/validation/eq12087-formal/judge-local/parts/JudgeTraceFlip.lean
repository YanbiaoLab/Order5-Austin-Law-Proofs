prelude
import Init.Data.Option.Lemmas
import Init.Omega
import Init.RCases
import Init.WFTactics
import JudgeTraceHeight
set_option Elab.async false
/- Checked module: TraceFlip -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem fold_column_trace {u a t j : T} (hf : FoldWitness u a t j) :
    ∃ h r, j = c (mul u t) (mul u a) r t h ∧
      mul (mul (mul u t) (mul u a)) r = t ∧ mul (mul u a) r = h ∧
      sz (mul u t) < sz j ∧ sz (mul u a) < sz j ∧ sz r < sz j := by
  obtain ⟨h,_,_,hj,has,_,hhs⟩ := fold_outer_trace hf
  have hne : a ≠ j := by intro he; rw [he] at has; omega
  obtain ⟨r,l,b,hc⟩ := distinct_columns_larger_returns rfl hf.1.symm hne (by omega)
  have ho := mul_origin_of_right_le (a:=t) (b:=h) (by rw [hj]; omega)
  rw [hj] at ho
  conv at ho => lhs; rw [hc,origin]
  obtain ⟨hl,hb⟩ := Prod.mk.inj (Option.some.inj ho)
  subst l; subst b
  have hs := mul_code_semantics (hj.trans hc)
  exact ⟨h,r,hc,hs.1,hs.2,by rw [hc]; simp only [sz]; omega,
    by rw [hc]; simp only [sz]; omega,by rw [hc]; simp only [sz]; omega⟩

theorem flip_fold_trace {u a k : T}
    (hf : mul u (mul (mul u a) k) = mul a k) :
    ∃ j, FoldWitness u a (mul a k) j ∧
      mul (mul u a) k = c u (mul a k) j (mul u a) k := by
  have hs := common_column_inputs_small
    (show mul (mul u a) k = mul (mul u a) k from rfl)
    (show mul a k = mul a k from rfl)
  have htq : sz (mul a k) < sz (mul (mul u a) k) := by
    by_cases hn : sz (mul a k) < sz (mul (mul u a) k)
    · exact hn
    apply False.elim
    have ho := mul_origin_of_right_le (a:=u) (b:=mul (mul u a) k) (by rw [hf]; omega)
    have ho' := mul_origin_of_right_le (a:=a) (b:=k) (by omega)
    rw [hf,ho'] at ho
    have hp := Prod.mk.inj (Option.some.inj ho)
    exact mul_ne_right (mul u a) k hp.2.symm
  have hsmall : sz (mul u (mul (mul u a) k)) < sz (mul (mul u a) k) := by
    rw [hf]; exact htq
  obtain ⟨v,j,l,r,hc⟩ := (mul_small_iff _ _).mp hsmall
  have hv : v = mul a k := by rw [hc,mul_code_return] at hf; exact hf
  subst v
  have ho := mul_origin_of_right_le (a:=mul u a) (b:=k) (by omega)
  conv at ho => lhs; rw [hc,origin]
  obtain ⟨hl,hr⟩ := Prod.mk.inj (Option.some.inj ho)
  subst l; subst r
  have hsem := mul_code_semantics hc
  refine ⟨j,⟨hsem.1.symm,?_⟩,hc⟩
  rw [hsem.2]

theorem no_flip_plain {u a k : T} (hk : PlainRight k) :
    mul u (mul (mul u a) k) ≠ mul a k := by
  intro hf
  obtain ⟨j,hfold,hc⟩ := flip_fold_trace hf
  have hs := (mul_code_semantics hc).2
  obtain ⟨h,hcode,_,_,_,_,_⟩ := fold_outer_trace hfold
  rw [hs] at hcode
  rw [hcode] at hk
  exact hk

end submission.Austin12087Trace

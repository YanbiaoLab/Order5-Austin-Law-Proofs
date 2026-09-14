prelude
import TraceNormalFoldExclusion
set_option autoImplicit false

namespace Austin12087Trace
open T

theorem nf_no_flip {u a k : T} (hu : NF u) (ha : NF a) (hk : NF k) :
    mul u (mul (mul u a) k) ≠ mul a k := by
  intro he
  obtain ⟨j,hfold,hcode⟩ := flip_fold_trace he
  have hn := nf_mul (nf_mul hu ha) hk
  rw [hcode] at hn
  exact nf_fold_impossible (nf_code_actual hn).2.2.1 hfold

theorem normal_first_diagonal_query_absent (u k : T) (hu : NF u) (hk : NF k) :
    (inverse k (mul (mul u (mul k (mul u k))) k)).bind (inverse u) = none := by
  cases h₁ : inverse k (mul (mul u (mul k (mul u k))) k) with
  | none => rfl
  | some w =>
    cases h₂ : inverse u w with
    | none => exact h₂
    | some y =>
      have hw := inverse_sound h₁
      have hy := inverse_sound h₂
      rw [←hy] at hw
      obtain ⟨a,t,j,_,_,hj,_,_,_,_,hfold⟩ := normal_first_diagonal_fold_descent hu hk hw
      exact False.elim (nf_fold_impossible hj hfold)

end Austin12087Trace
#print axioms Austin12087Trace.nf_no_flip
#print axioms Austin12087Trace.normal_first_diagonal_query_absent

prelude
import TraceFirstOffdiagonal
set_option autoImplicit false

namespace Austin12087Trace
open T

theorem first_larger_k_head_forces_same_key {u q k y t : T}
    (hu : NF u) (hnk : NF k)
    (hf : mul (mul y u) k = mul (mul u (mul q (mul u k))) q)
    (hne : q ≠ k) (hs : sz q ≤ sz k)
    (hc : mul u k = c q (mul q (mul u k)) t u k)
    (hh : ht t ≤ ht (mul q (mul u k))) : q = u := by
  let b := mul q (mul u k)
  have hsem := mul_code_semantics hc
  have huk := first_larger_k_height_dominates hu hnk hf hne hs
  obtain ⟨⟨s,l,r,hk⟩,_,_,_⟩ := first_offdiagonal_larger_k_return hf hne hs
  have hkg := mul_height_growth_of_left_ge hh
  rw [hsem.2] at hkg
  have hq := nf_code_key_height_gap (hc ▸ nf_mul hu hnk)
  rw [←hc] at hq
  have hvg := mul_height_growth_of_right_le (a:=u) (b:=k) (by
    rw [hc]
    simp only [ht]
    omega)
  have hw := (nf_code_height_gap (hk ▸ hnk)).2.1
  rw [←hk,hf] at hw
  have hai := inverse_height_strict (inverse_complete (mul u b) q)
  have ha : ht (mul u b) < ht b := by
    change ht (mul (mul u b) q) + 2 ≤ ht k at hw
    change ht k = max (ht b) (ht t) + 1 at hkg
    change ht t ≤ ht b at hh
    omega
  have hd : ht (mul q b) < ht b := by
    by_cases hn : ht (mul q b) < ht b
    · exact hn
    · have hdg := mul_height_growth_of_right_le (a:=q) (b:=b) (by omega)
      have hug := mul_height_growth_of_left_ge (a:=mul q b) (b:=t) (by
        change ht t ≤ ht b at hh
        omega)
      have hdu : mul (mul q b) t = u := hsem.1
      rw [hdu] at hug
      change ht k = max (ht b) (ht t) + 1 at hkg
      omega
  obtain ⟨za,la,ra,hba⟩ := mul_return_of_height_lt ha
  obtain ⟨zd,ld,rd,hbd⟩ := mul_return_of_height_lt hd
  exact (T.c.inj (hbd.symm.trans hba)).1

end Austin12087Trace
#print axioms Austin12087Trace.first_larger_k_head_forces_same_key

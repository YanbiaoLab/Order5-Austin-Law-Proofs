prelude
import TraceReturnProductGap
set_option autoImplicit false

namespace Austin12087Trace
open T

theorem normal_critical_excluded_by_lower_queries {x y z q t l r : T}
    (hnx : NF x) (hny : NF y) (hnz : NF z)
    (hf : ∀ u q' k : T, NF u → NF q' → NF k →
      ht u < max (ht x) (ht z) → ht q' < max (ht x) (ht z) → ht k < max (ht x) (ht z) →
      (inverse k (mul (mul u (mul q' (mul u k))) q')).bind (inverse u) = none)
    (hs : ∀ u a k : T, NF u → NF a → NF k →
      ht u < max (ht x) (ht z) → ht a < max (ht x) (ht z) → ht k < max (ht x) (ht z) →
      inverse (mul (mul a (mul (mul u a) k)) (mul a k)) u = none)
    (he : mul x z = c (mul (mul y x) z) q t l r) : False := by
  obtain ⟨hl,hr,hx,hz⟩ := critical_return_trace he
  subst l; subst r
  obtain ⟨hnu,hna,hnq,_⟩ := nf_critical_parameters hnx hny hnz he
  have hqgap := (nf_code_height_gap (he ▸ nf_mul hnx hnz)).2.1
  rw [←he] at hqgap
  have hbg := mul_height_growth_of_right_le (a:=x) (b:=z) (by
    rw [he]; simp only [ht]; omega)
  by_cases hsz : sz z ≤ sz x
  · obtain ⟨k,hcode,hv,ht⟩ := critical_x_max he hsz
    have hnc := nf_code_actual (hcode ▸ hnx)
    have hnk := hnc.2.2.1
    have hgap := nf_code_height_gap (hcode ▸ hnx)
    rw [←hcode] at hgap
    have h1 := inverse_complete (mul y (mul y x)) k
    rw [hv] at h1
    have h2 := inverse_complete y (mul y x)
    have hquery := hf (mul y x) q k hnu hnq hnk (by omega) (by omega) (by omega)
    rw [ht,hz,h1,Option.bind_some,h2] at hquery
    cases hquery
  · obtain ⟨k,hcode,hq,ht⟩ := critical_z_max he (by omega)
    have hnc := nf_code_actual (hcode ▸ hnz)
    have hnk := hnc.2.2.1
    have hgap := nf_code_height_gap (hcode ▸ hnz)
    rw [←hcode] at hgap
    have hquery := hs (mul y x) (mul (mul y x) z) k hnu hna hnk
      (by omega) (by omega) (by omega)
    rw [hq,ht,hx,inverse_complete] at hquery
    cases hquery

theorem normal_source_of_lower_queries {x y z : T}
    (hnx : NF x) (hny : NF y) (hnz : NF z)
    (hf : ∀ u q k : T, NF u → NF q → NF k →
      ht u < max (ht x) (ht z) → ht q < max (ht x) (ht z) → ht k < max (ht x) (ht z) →
      (inverse k (mul (mul u (mul q (mul u k))) q)).bind (inverse u) = none)
    (hs : ∀ u a k : T, NF u → NF a → NF k →
      ht u < max (ht x) (ht z) → ht a < max (ht x) (ht z) → ht k < max (ht x) (ht z) →
      inverse (mul (mul a (mul (mul u a) k)) (mul a k)) u = none) : Source12087 x y z := by
  apply source_without_middle_return
  intro q t l r he
  exact normal_critical_excluded_by_lower_queries hnx hny hnz hf hs he

end Austin12087Trace
#print axioms Austin12087Trace.normal_critical_excluded_by_lower_queries
#print axioms Austin12087Trace.normal_source_of_lower_queries

prelude
import TraceNormal
set_option autoImplicit false

namespace Austin12087Trace
open T

def NormalFirstCycleAbsent : Prop := ∀ u q k : T, NF u → NF q → NF k →
  (inverse k (mul (mul u (mul q (mul u k))) q)).bind (inverse u) = none

def NormalSecondCycleAbsent : Prop := ∀ u a k : T, NF u → NF a → NF k →
  inverse (mul (mul a (mul (mul u a) k)) (mul a k)) u = none

theorem normal_first_diagonal_descent {u k y : T} (hu : NF u) (hk : NF k)
    (hf : mul (mul y u) k = mul (mul u (mul k (mul u k))) k) :
    ∃ a h, NF a ∧ NF h ∧ sz u < sz k ∧ sz a < sz k ∧ sz h < sz k ∧
      mul y (mul (mul a (mul (mul u a) h)) (mul a h)) = u := by
  obtain ⟨a,h,_,hus,has,hhs,he,hcode⟩ := first_diagonal_descent_trace hf
  have hz := nf_mul hk (nf_mul hu hk)
  rw [hcode] at hz
  have hn := nf_code_actual hz
  exact ⟨a,h,hn.2.1,hn.2.2.1,hus,has,hhs,he⟩

theorem normal_first_diagonal_absent_of_smaller_second (u k : T)
    (hu : NF u) (hk : NF k)
    (hs : ∀ a h : T, NF a → NF h → sz u < sz k → sz a < sz k → sz h < sz k →
      inverse (mul (mul a (mul (mul u a) h)) (mul a h)) u = none) :
    (inverse k (mul (mul u (mul k (mul u k))) k)).bind (inverse u) = none := by
  cases h1 : inverse k (mul (mul u (mul k (mul u k))) k) with
  | none => rfl
  | some w =>
    cases h2 : inverse u w with
    | none => exact h2
    | some y =>
      have hw := inverse_sound h1
      have hy := inverse_sound h2
      rw [←hy] at hw
      obtain ⟨a,h,ha,hh,hus,has,hhs,he⟩ := normal_first_diagonal_descent hu hk hw
      have hi := inverse_complete y (mul (mul a (mul (mul u a) h)) (mul a h))
      rw [he,hs a h ha hh hus has hhs] at hi
      cases hi

theorem nf_critical_parameters {x y z q t l r : T}
    (hx : NF x) (hy : NF y) (hz : NF z)
    (he : mul x z = c (mul (mul y x) z) q t l r) :
    NF (mul y x) ∧ NF (mul (mul y x) z) ∧ NF q ∧ NF t := by
  have hu := nf_mul hy hx
  have ha := nf_mul hu hz
  have hb := nf_mul hx hz
  rw [he] at hb
  have hc := nf_code_actual hb
  exact ⟨hu,ha,hc.2.1,hc.2.2.1⟩

theorem normal_critical_excluded_by_queries
    (hf : NormalFirstCycleAbsent) (hs : NormalSecondCycleAbsent)
    {x y z q t l r : T}
    (hnx : NF x) (hny : NF y) (hnz : NF z)
    (he : mul x z = c (mul (mul y x) z) q t l r) : False := by
  obtain ⟨_,_,hx,hz⟩ := critical_return_trace he
  obtain ⟨hnu,hna,hnq,_⟩ := nf_critical_parameters hnx hny hnz he
  by_cases hsz : sz z ≤ sz x
  · obtain ⟨k,hcode,hv,ht⟩ := critical_x_max he hsz
    have hnx' := hnx
    rw [hcode] at hnx'
    have hnk := (nf_code_actual hnx').2.2.1
    have h1 := inverse_complete (mul y (mul y x)) k
    rw [hv] at h1
    have h2 := inverse_complete y (mul y x)
    have hquery := hf (mul y x) q k hnu hnq hnk
    rw [ht,hz,h1,Option.bind_some,h2] at hquery
    cases hquery
  · obtain ⟨k,hcode,hq,ht⟩ := critical_z_max he (by omega)
    have hnz' := hnz
    rw [hcode] at hnz'
    have hnk := (nf_code_actual hnz').2.2.1
    have hquery := hs (mul y x) (mul (mul y x) z) k hnu hna hnk
    rw [hq,ht,hx,inverse_complete] at hquery
    cases hquery

theorem nf_source_of_normal_queries
    (hf : NormalFirstCycleAbsent) (hs : NormalSecondCycleAbsent)
    (x y z : T) (hx : NF x) (hy : NF y) (hz : NF z) : Source12087 x y z := by
  apply source_without_middle_return
  intro q t l r he
  exact normal_critical_excluded_by_queries hf hs hx hy hz he

theorem normal_law_of_normal_queries
    (hf : NormalFirstCycleAbsent) (hs : NormalSecondCycleAbsent) :
    ∀ x y z : NormalTree,
      x = normalMul y (normalMul (normalMul (normalMul y x) z) (normalMul x z)) :=
  normal_law_of_nf_source (nf_source_of_normal_queries hf hs)

-- The two normal query-absence statements are still open. No law instance or
-- InfiniteModel certificate is declared by this conditional bridge.
end Austin12087Trace
#print axioms Austin12087Trace.normal_first_diagonal_descent
#print axioms Austin12087Trace.normal_first_diagonal_absent_of_smaller_second
#print axioms Austin12087Trace.nf_critical_parameters
#print axioms Austin12087Trace.normal_critical_excluded_by_queries
#print axioms Austin12087Trace.nf_source_of_normal_queries
#print axioms Austin12087Trace.normal_law_of_normal_queries

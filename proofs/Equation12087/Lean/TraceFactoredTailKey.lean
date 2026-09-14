prelude
import TraceSecondReturningQTail
set_option autoImplicit false

namespace Austin12087Trace
open T

theorem normal_factored_returning_tail_geometry {u a q h z : T}
    (hq : NF q)
    (hn : NF (c (mul a q) u h (mul (mul u a) q) z))
    (hfix : mul u (mul q z) = a)
    (hbz : ht (mul (mul u a) q) ≤ ht z)
    (htr : ht (mul q z) < ht z) :
    ht u + 3 ≤ ht z ∧ ht a + 3 ≤ ht z ∧
      ht h + 1 = ht z ∧ ht (mul (mul u a) q) + 2 ≤ ht h ∧
      origin z = some (u,h) := by
  let b := mul (mul u a) q
  let w := mul a q
  let e := c w u h b z
  let t := mul q z
  change NF e at hn
  change mul u t = a at hfix
  change ht b ≤ ht z at hbz
  change ht t < ht z at htr
  have hc := nf_code_actual hn
  have hgap := nf_code_height_gap hn
  have hkey := nf_code_key_height_gap hn
  change ht w + 2 ≤ ht e ∧ ht u + 2 ≤ ht e ∧ ht h + 2 ≤ ht e at hgap
  change ht w + 3 ≤ ht e at hkey
  have heact : mul b z = e := hc.2.2.2.2.2.1
  have heo : origin e = some (b,z) := rfl
  have heg := mul_height_growth_of_right_le (a:=b) (b:=z) (by
    rw [heact]
    exact Nat.le_of_lt (origin_height heo).2)
  rw [heact] at heg
  have hez : ht e = ht z + 1 := by omega
  have htgap := nf_mul_height_key_gap (a:=q) hc.2.2.2.2.1
  change ht t = max (ht q) (ht z) + 1 ∨ (ht q + 3 ≤ ht z ∧ ht t + 2 ≤ ht z) at htgap
  have hqt : ht q + 3 ≤ ht z ∧ ht t + 2 ≤ ht z := by rcases htgap with hh | hh <;> omega
  have hai := inverse_height_strict (inverse_complete a q)
  change ht a < max (ht q) (ht w) at hai
  have hui := inverse_height_strict (inverse_complete u t)
  rw [hfix] at hui
  have ha3 : ht a + 3 ≤ ht z := by omega
  have hu3 : ht u + 3 ≤ ht z := by omega
  have hg := mul_height_upper u a
  have hb := mul_height_upper (mul u a) q
  change ht b ≤ max (ht (mul u a)) (ht q) + 1 at hb
  have hbsmall : ht b < ht z := by omega
  have hzh : mul u h = z := hc.2.2.2.2.2.2.2
  have hzg := mul_height_growth_of_right_le (a:=u) (b:=h) (by rw [hzh]; omega)
  rw [hzh] at hzg
  have hoz := mul_origin_of_right_height_le (a:=u) (b:=h) (by rw [hzh]; omega)
  rw [hzh] at hoz
  have hbh : mul (mul w u) h = b := hc.2.2.2.2.2.2.1
  have hbret := nf_mul_height_key_gap (a:=mul w u) hc.2.2.1
  rw [hbh] at hbret
  have hb2 : ht b + 2 ≤ ht h := by rcases hbret with hh | hh <;> omega
  exact ⟨hu3,ha3,by omega,hb2,hoz⟩

theorem normal_factored_returning_tail_output_returns {u a q h z : T}
    (hq : NF q)
    (hn : NF (c (mul a q) u h (mul (mul u a) q) z))
    (hfix : mul u (mul q z) = a)
    (hbz : ht (mul (mul u a) q) ≤ ht z)
    (htr : ht (mul q z) < ht z) : ht a < ht (mul q z) := by
  let b := mul (mul u a) q
  let w := mul a q
  let t := mul q z
  let D := mul w u
  change mul u t = a at hfix
  change ht t < ht z at htr
  obtain ⟨hu3,ha3,hhz,hb2,hoz⟩ := normal_factored_returning_tail_geometry hq hn hfix hbz htr
  change ht b + 2 ≤ ht h at hb2
  have hc := nf_code_actual hn
  have hzh : mul u h = z := hc.2.2.2.2.2.2.2
  have hbh : mul D h = b := hc.2.2.2.2.2.2.1
  have hl : ReturnLadder q D u t b z h := ⟨hc.2.2.2.2.1,hzh,hoz,rfl,hbh⟩
  change ht a < ht t
  by_cases hh : ht a < ht t
  · exact hh
  · have hag := mul_height_growth_of_right_le (a:=u) (b:=t) (by rw [hfix]; omega)
    rw [hfix] at hag
    have hg := mul_height_upper u a
    have hb := mul_height_upper (mul u a) q
    change ht b ≤ max (ht (mul u a)) (ht q) + 1 at hb
    rcases mul_height_growth_or_return a q with hw | ⟨x,r,l,s,hqc,hwx⟩
    · change ht w = max (ht a) (ht q) + 1 at hw
      have hD := mul_height_growth_of_left_ge (a:=w) (b:=u) (by omega)
      change ht D = max (ht w) (ht u) + 1 at hD
      exact False.elim (return_ladder_second_dominant_impossible hl htr (by omega) (by omega) (by omega))
    · have haq : ht a < ht q := by rw [hqc]; simp only [ht]; omega
      have hB := mul_height_growth_of_left_ge (a:=q) (b:=t) (by omega)
      obtain ⟨s',hl',_⟩ := return_ladder_step hl htr (by omega)
      exact False.elim (return_ladder_second_dominant_impossible hl' (by omega) (by omega) (by omega) (by omega))

theorem normal_factored_returning_tail_key_repeats {u a q h z : T}
    (hq : NF q)
    (hn : NF (c (mul a q) u h (mul (mul u a) q) z))
    (hfix : mul u (mul q z) = a)
    (hbz : ht (mul (mul u a) q) ≤ ht z)
    (htr : ht (mul q z) < ht z) : q = u := by
  let b := mul (mul u a) q
  let w := mul a q
  let t := mul q z
  change mul u t = a at hfix
  change ht t < ht z at htr
  obtain ⟨hu3,_,hhz,hb2,hoz⟩ := normal_factored_returning_tail_geometry hq hn hfix hbz htr
  change ht b + 2 ≤ ht h at hb2
  have hat := normal_factored_returning_tail_output_returns hq hn hfix hbz htr
  change ht a < ht t at hat
  have hc := nf_code_actual hn
  have hnt : NF t := nf_mul hq hc.2.2.2.2.1
  have hgap := nf_mul_height_key_gap (a:=u) hnt
  rw [hfix] at hgap
  have hut : ht u + 3 ≤ ht t ∧ ht a + 2 ≤ ht t := by rcases hgap with hh | hh <;> omega
  by_cases hqu : q = u
  · exact hqu
  · obtain ⟨s,l,r,htc⟩ := mul_return_of_height_lt (a:=u) (b:=t) (by rw [hfix]; exact hat)
    have hB := mul_height_off_return_key (a:=q) htc hqu
    have hg := mul_height_upper u a
    have hb := mul_height_upper (mul u a) q
    change ht b ≤ max (ht (mul u a)) (ht q) + 1 at hb
    have hzh : mul u h = z := hc.2.2.2.2.2.2.2
    have hbh : mul (mul w u) h = b := hc.2.2.2.2.2.2.1
    have hl : ReturnLadder q (mul w u) u t b z h := ⟨hc.2.2.2.2.1,hzh,hoz,rfl,hbh⟩
    obtain ⟨s',hl',_⟩ := return_ladder_step hl htr (by omega)
    exact False.elim (return_ladder_second_dominant_impossible hl' (by omega) (by omega) (by omega) (by omega))

end Austin12087Trace
#print axioms Austin12087Trace.normal_factored_returning_tail_geometry
#print axioms Austin12087Trace.normal_factored_returning_tail_output_returns
#print axioms Austin12087Trace.normal_factored_returning_tail_key_repeats

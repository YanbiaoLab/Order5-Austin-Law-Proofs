prelude
import TraceSecondReturningQOuter
set_option autoImplicit false

namespace Austin12087Trace
open T

theorem factored_return_ladder_head_order {u a q e k t : T}
    (hq : NF q)
    (hl : ReturnLadder (mul u a) (mul (mul a q) e) e q a k t)
    (hqk : ht q < ht k) :
    max (ht a) (ht q) < ht e ∧ ht (mul u a) < ht e ∧
      ht (mul (mul a q) e) < ht e := by
  let g := mul u a
  let w := mul a q
  let A := mul w e
  change ReturnLadder g A e q a k t at hl
  have hem : max (ht a) (ht q) < ht e := by
    by_cases hh : max (ht a) (ht q) < ht e
    · exact hh
    · have hwq : ht w < ht q := by
        by_cases hwq : ht w < ht q
        · exact hwq
        · have hwg := mul_height_growth_of_right_le (a:=a) (b:=q) (by change ht q ≤ ht w; omega)
          change ht w = max (ht a) (ht q) + 1 at hwg
          have hAg := mul_height_growth_of_left_ge (a:=w) (b:=e) (by omega)
          change ht A = max (ht w) (ht e) + 1 at hAg
          exact False.elim (return_ladder_second_dominant_impossible hl hqk (by omega) (by omega) (by omega))
      have hwgap := nf_mul_height_key_gap (a:=a) hq
      change ht w = max (ht a) (ht q) + 1 ∨ (ht a + 3 ≤ ht q ∧ ht w + 2 ≤ ht q) at hwgap
      have haq : ht a < ht q := by rcases hwgap with hh | hh <;> omega
      have heq : ht e ≤ ht q := by omega
      obtain ⟨z,l,r,hqc⟩ := mul_return_of_height_lt (a:=a) (b:=q) hwq
      have hb := mul_height_off_return_key (a:=g) hqc (mul_ne_right u a)
      have hpg := nf_mul_height_key_gap (a:=g) hl.1
      rw [hl.2.2.2.1] at hpg
      have hq2 : ht q + 2 ≤ ht k := by rcases hpg with hh | hh <;> omega
      have hkg := mul_height_growth_of_right_le (a:=e) (b:=t) (by
        rw [hl.2.1]
        exact Nat.le_of_lt (origin_height hl.2.2.1).2)
      rw [hl.2.1] at hkg
      obtain ⟨r',hl',_⟩ := return_ladder_step hl hqk (by omega)
      exact False.elim (return_ladder_second_dominant_impossible hl' (by omega) (by omega) (by omega) (by omega))
  have hge : ht g < ht e := by
    by_cases hh : ht g < ht e
    · exact hh
    · exact False.elim (return_ladder_dominant_impossible hl (by omega) (by omega) (by omega))
  have hAe : ht A < ht e := by
    by_cases hh : ht A < ht e
    · exact hh
    · exact False.elim (return_ladder_second_dominant_impossible hl hqk (by omega) (by omega) (by omega))
  exact ⟨hem,hge,hAe⟩

theorem factored_return_ladder_tail_stops {u a q e k t z l r : T}
    (hl : ReturnLadder (mul u a) u e q a k t)
    (hec : e = c (mul a q) u z l r)
    (hae : ht a < ht e) (hqe : ht q < ht e) (hqk : ht q < ht k) :
    ht t ≤ ht e := by
  let g := mul u a
  let w := mul a q
  let b := mul g q
  change ReturnLadder g u e q a k t at hl
  have hte : ht t ≤ ht e := by
    by_cases hh : ht t ≤ ht e
    · exact hh
    · obtain ⟨s,hl₁,_⟩ := return_ladder_step hl hqk (by omega)
      have htg := mul_height_growth_of_right_le (a:=q) (b:=s) (by
        rw [hl₁.2.1]
        exact Nat.le_of_lt (origin_height hl₁.2.2.1).2)
      rw [hl₁.2.1] at htg
      have hns := (nf_origin hl₁.1 hl₁.2.2.1).2
      have hpg := nf_mul_height_key_gap (a:=b) hns
      rw [hl₁.2.2.2.2] at hpg
      have he2 : ht e + 2 ≤ ht s := by rcases hpg with hp | hp <;> omega
      obtain ⟨s',hl₂,_⟩ := return_ladder_step hl₁ (by omega) (by omega)
      have hsg := mul_height_growth_of_right_le (a:=a) (b:=s') (by
        rw [hl₂.2.1]
        exact Nat.le_of_lt (origin_height hl₂.2.2.1).2)
      rw [hl₂.2.1] at hsg
      obtain ⟨s'',hl₃,_⟩ := return_ladder_step hl₂ (by omega) (by omega)
      change ReturnLadder g (mul b e) e q a s' s'' at hl₃
      have hbw : b ≠ w := by
        intro heq
        exact mul_ne_right u a (right_injective _ _ q heq)
      have hbg := mul_height_off_return_key (a:=b) hec hbw
      exact False.elim (return_ladder_second_dominant_impossible hl₃ (by omega) (by omega) (by omega) (by omega))
  exact hte

end Austin12087Trace
#print axioms Austin12087Trace.factored_return_ladder_head_order
#print axioms Austin12087Trace.factored_return_ladder_tail_stops

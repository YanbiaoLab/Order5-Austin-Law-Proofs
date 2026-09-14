prelude
import Init.Data.Option.Lemmas
import Init.Omega
import Init.RCases
import Init.WFTactics
import JudgeTraceSecondStrictTail
set_option Elab.async false
/- Checked module: TraceSecondReturningQTail -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem rotated_product_column_order {u a q : T}
    (he : mul (mul a q) u = mul u a) (hne : u ≠ a) :
    ht (mul (mul u a) q) ≤ ht (mul u q) := by
  let w := mul a q
  let g := mul u a
  let b := mul g q
  let z := mul u q
  change mul w u = g at he
  change ht b ≤ ht z
  by_cases hh : ht b ≤ ht z
  · exact hh
  · have hbg := mul_height_upper g q
    change ht b ≤ max (ht g) (ht q) + 1 at hbg
    have hwg : ht w < ht g ∧ ht u < ht g ∧ origin g = some (w,u) := by
      rcases mul_height_shape u q with hz | ⟨x,r,l,s,hqc,hzx⟩
      · change ht u < ht z ∧ ht q < ht z ∧ origin z = some (u,q) at hz
        have ho := mul_origin_of_right_height_le (a:=w) (b:=u) (by rw [he]; omega)
        rw [he] at ho
        exact ⟨(origin_height ho).1,(origin_height ho).2,ho⟩
      · have hw := mul_height_off_return_key (a:=a) hqc (Ne.symm hne)
        change ht w = max (ht a) (ht q) + 1 at hw
        rcases mul_height_shape w u with hg | ⟨x',r',l',s',huc,hgx⟩
        · rw [he] at hg
          exact hg
        · have hu : ht w < ht u ∧ ht g < ht u := by
            rw [he] at hgx
            rw [huc,← hgx]
            simp only [ht]
            omega
          have hg := mul_height_growth_of_left_ge (a:=u) (b:=a) (by omega)
          change ht g = max (ht u) (ht a) + 1 at hg
          exact False.elim (by omega)
    have hag : ht a < ht g := by
      rcases mul_height_shape a q with hw | ⟨x,r,l,s,hqc,hwx⟩
      · change ht a < ht w ∧ ht q < ht w ∧ origin w = some (a,q) at hw
        omega
      · have hzg := mul_height_off_return_key (a:=u) hqc hne
        change ht z = max (ht u) (ht q) + 1 at hzg
        have haq : ht a < ht q := by rw [hqc]; simp only [ht]; omega
        omega
    have hog := mul_origin_of_right_height_le (a:=u) (b:=a) (by change ht a ≤ ht g; omega)
    change origin g = some (u,a) at hog
    exact False.elim (hne (Prod.mk.inj (Option.some.inj (hwg.2.2.symm.trans hog))).2)

theorem normal_factored_code_head_le_tail {u a q h z : T}
    (hn : NF (c (mul a q) u h (mul (mul u a) q) z))
    (hqe : ht q < ht (c (mul a q) u h (mul (mul u a) q) z))
    (hne : u ≠ a) : ht (mul (mul u a) q) ≤ ht z := by
  let b := mul (mul u a) q
  let w := mul a q
  let e := c w u h b z
  change NF e at hn
  change ht q < ht e at hqe
  change ht b ≤ ht z
  by_cases hh : ht b ≤ ht z
  · exact hh
  · have hc := nf_code_actual hn
    have hgap := nf_code_height_gap hn
    change ht w + 2 ≤ ht e ∧ ht u + 2 ≤ ht e ∧ ht h + 2 ≤ ht e at hgap
    have heact : mul b z = e := hc.2.2.2.2.2.1
    have heo : origin e = some (b,z) := rfl
    have heg := mul_height_growth_of_right_le (a:=b) (b:=z) (by
      rw [heact]
      exact Nat.le_of_lt (origin_height heo).2)
    rw [heact] at heg
    have hob := mul_origin_of_right_height_le (a:=mul u a) (b:=q) (by change ht q ≤ ht b; omega)
    change origin b = some (mul u a,q) at hob
    have hbh : mul (mul w u) h = b := hc.2.2.2.2.2.2.1
    have hzh : mul u h = z := hc.2.2.2.2.2.2.2
    have hob' := mul_origin_of_right_height_le (a:=mul w u) (b:=h) (by rw [hbh]; omega)
    rw [hbh] at hob'
    have hp := Prod.mk.inj (Option.some.inj (hob'.symm.trans hob))
    have ho := rotated_product_column_order hp.1 hne
    rw [hp.2] at hzh
    rw [hzh] at ho
    exact False.elim (by change ht b ≤ ht z at ho; omega)

theorem normal_second_returning_q_tail_returns {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hs : NormalSecondBelow (ht k))
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u)
    (hqr : ht (mul (mul u a) k) < ht k) :
    let g := mul u a
    let q := mul g k
    let v := mul a k
    let w := mul a q
    let e := mul w v
    ∃ t z h, NF t ∧ NF z ∧ NF h ∧
      v = c w e t a k ∧ k = c g q z e t ∧ e = c w u h (mul g q) z ∧
      mul u t = a ∧ mul q z = t ∧ ht (mul g q) ≤ ht z ∧
      ht t < ht z ∧ ht z + 1 = ht e ∧ ht e < ht k := by
  let g := mul u a
  let q := mul g k
  let v := mul a k
  let w := mul a q
  let e := mul w v
  obtain ⟨t,z,h,hnt,hnz,hnh,hvc,hkc,hec,hat,htz,hte,hek⟩ :=
    normal_second_returning_q_strict_tail hu ha hk hs hf hqr
  change e = c w u h (mul g q) z at hec
  change ht t < ht e at hte
  have hne : NF e := nf_mul (nf_mul ha (nf_mul (nf_mul hu ha) hk)) (nf_mul ha hk)
  have hqc : ht q < ht e := by
    have ho : origin e = some (mul g q,z) := by rw [hec]; rfl
    have hc := common_column_height_bounds
      (show mul (mul u a) q = mul g q from rfl) (show mul a q = w from rfl)
    have hb := (origin_height ho).1
    have hw := (nf_code_height_gap (hec ▸ hne)).1
    rw [← hec] at hw
    omega
  have hbz := normal_factored_code_head_le_tail (hec ▸ hne) (by rw [← hec]; exact hqc)
    (normal_second_returning_q_inputs_distinct hu ha hk hs hf hqr)
  change ht (mul g q) ≤ ht z at hbz
  have heact : mul (mul g q) z = e := by
    have hh := (nf_code_actual (hec ▸ hne)).2.2.2.2.2.1
    rw [← hec] at hh
    exact hh
  have heo : origin e = some (mul g q,z) := by rw [hec]; rfl
  have heg := mul_height_growth_of_right_le (a:=mul g q) (b:=z) (by
    rw [heact]
    exact Nat.le_of_lt (origin_height heo).2)
  rw [heact] at heg
  have hze : ht z + 1 = ht e := by omega
  have htr : ht t < ht z := by
    by_cases hh : ht t < ht z
    · exact hh
    · have hg := mul_height_growth_of_right_le (a:=q) (b:=z) (by rw [htz]; omega)
      rw [htz] at hg
      exact False.elim (by omega)
  exact ⟨t,z,h,hnt,hnz,hnh,hvc,hkc,hec,hat,htz,hbz,htr,hze,hek⟩

end submission.Austin12087Trace

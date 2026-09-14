prelude
import TraceSecondMaxHead
set_option autoImplicit false

namespace Austin12087Trace
open T

theorem nf_transposed_pair_no_preimage {a w y : T} (ha : NF a) (hw : NF w)
    (hau : ht a < ht (mul a w)) (hwu : ht w < ht (mul a w)) :
    mul y (mul w (mul a (mul w a))) ≠ mul a w := by
  intro hf
  let u := mul a w
  let k := mul w a
  let v := mul a k
  let e := mul w v
  change mul y e = u at hf
  change ht a < ht u at hau
  change ht w < ht u at hwu
  have hk : NF k := nf_mul hw ha
  have hv : NF v := nf_mul ha hk
  have he : NF e := nf_mul hw hv
  have hug := mul_height_growth_of_right_le (a:=a) (b:=w) (by change ht w ≤ ht u; omega)
  change ht u = max (ht a) (ht w) + 1 at hug
  have hku := mul_height_upper w a
  change ht k ≤ max (ht w) (ht a) + 1 at hku
  have hvu := mul_height_upper a k
  change ht v ≤ max (ht a) (ht k) + 1 at hvu
  have hpout := nf_mul_height_key_gap (a:=y) he
  rw [hf] at hpout
  by_cases hev : ht e < ht v
  · have hpv := nf_mul_height_key_gap (a:=w) hv
    change ht e = max (ht w) (ht v) + 1 ∨ (ht w + 3 ≤ ht v ∧ ht e + 2 ≤ ht v) at hpv
    have hret : ht w + 3 ≤ ht v ∧ ht e + 2 ≤ ht v := by
      rcases hpv with hpv | hpv
      · exact False.elim (by omega)
      · exact hpv
    have hou := mul_origin_of_right_height_le (a:=a) (b:=w) (by change ht w ≤ ht u; omega)
    change origin u = some (a,w) at hou
    have hou' := mul_origin_of_right_height_le (a:=y) (b:=e) (by rw [hf]; omega)
    rw [hf] at hou'
    have hew : e = w := (Prod.mk.inj (Option.some.inj (hou'.symm.trans hou))).2
    have hkv : ht k ≤ ht v := by
      have hp := nf_mul_height_key_gap (a:=a) hk
      change ht v = max (ht a) (ht k) + 1 ∨ (ht a + 3 ≤ ht k ∧ ht v + 2 ≤ ht k) at hp
      rcases hp with hp | hp
      · omega
      · have hp' := nf_mul_height_key_gap (a:=w) ha
        change ht k = max (ht w) (ht a) + 1 ∨ (ht w + 3 ≤ ht a ∧ ht k + 2 ≤ ht a) at hp'
        rcases hp' with hp' | hp' <;> exact False.elim (by omega)
    have hov := mul_origin_of_right_height_le (a:=a) (b:=k) hkv
    change origin v = some (a,k) at hov
    obtain ⟨t,_,hnt,_,hs,ht',_,_⟩ :=
      nf_return_origin_trace hv hov (show mul w v = e from rfl) hev
    rw [hew] at hs ht'
    have hflip : mul w (mul (mul w w) t) = mul w t := by
      rw [hs]
      exact ht'.symm
    exact nf_no_flip hw hw hnt hflip
  · have heg := mul_height_growth_of_right_le (a:=w) (b:=v) (by change ht v ≤ ht e; omega)
    change ht e = max (ht w) (ht v) + 1 at heg
    have hkv : ht k ≤ ht v := by
      have hp := nf_mul_height_key_gap (a:=a) hk
      change ht v = max (ht a) (ht k) + 1 ∨ (ht a + 3 ≤ ht k ∧ ht v + 2 ≤ ht k) at hp
      rcases hp with hp | hp
      · omega
      · have hp' := nf_mul_height_key_gap (a:=w) ha
        change ht k = max (ht w) (ht a) + 1 ∨ (ht w + 3 ≤ ht a ∧ ht k + 2 ≤ ht a) at hp'
        rcases hp' with hp' | hp'
        · rcases hpout with hpout | hpout <;> exact False.elim (by omega)
        · exact False.elim (by omega)
    have hvg := mul_height_growth_of_right_le (a:=a) (b:=k) hkv
    change ht v = max (ht a) (ht k) + 1 at hvg
    have hkg : ht k = ht u := by
      have hp := nf_mul_height_key_gap (a:=w) ha
      change ht k = max (ht w) (ht a) + 1 ∨ (ht w + 3 ≤ ht a ∧ ht k + 2 ≤ ht a) at hp
      rcases hp with hp | hp
      · omega
      · rcases hpout with hpout | hpout <;> exact False.elim (by omega)
    have hoe := mul_origin_of_right_height_le (a:=w) (b:=v) (by change ht v ≤ ht e; omega)
    change origin e = some (w,v) at hoe
    obtain ⟨t,_,_,_,hwt,hvt,_,_⟩ := nf_return_origin_trace he hoe hf (by omega)
    have hvw : v ≠ w := by intro heq; have hh := congrArg ht heq; omega
    have hov := (distinct_outputs_height_origin hvt hwt hvw (by omega)).1
    have hov' := mul_origin_of_right_height_le (a:=a) (b:=k) hkv
    change origin v = some (a,k) at hov'
    have hua := (Prod.mk.inj (Option.some.inj (hov.symm.trans hov'))).1
    have hh := congrArg ht hua
    omega

theorem normal_second_max_u_impossible {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hau : ht a ≤ ht u) (hku : ht k ≤ ht u)
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u) : False := by
  let w := mul a (mul (mul u a) k)
  obtain ⟨haw,hwa,ha',hw'⟩ := normal_second_max_u_head hu ha hk hau hku hf
  change mul a w = u at haw
  change mul w a = k at hwa
  change ht w < ht u at hw'
  have hnw : NF w := nf_mul ha (nf_mul (nf_mul hu ha) hk)
  have hh := nf_transposed_pair_no_preimage (y:=y) ha hnw (by rw [haw]; exact ha') (by rw [haw]; exact hw')
  rw [hwa,haw] at hh
  exact hh hf

theorem normal_second_query_height_order {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u) :
    ht u < max (ht a) (ht k) := by
  by_cases hh : ht u < max (ht a) (ht k)
  · exact hh
  · exact False.elim (normal_second_max_u_impossible hu ha hk (by omega) (by omega) hf)

end Austin12087Trace
#print axioms Austin12087Trace.nf_transposed_pair_no_preimage
#print axioms Austin12087Trace.normal_second_max_u_impossible
#print axioms Austin12087Trace.normal_second_query_height_order

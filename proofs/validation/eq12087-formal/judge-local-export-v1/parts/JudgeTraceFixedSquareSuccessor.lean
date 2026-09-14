prelude
import Init.Data.Option.Lemmas
import Init.Omega
import Init.RCases
import Init.WFTactics
import JudgeTraceSecondReturningQHead
set_option Elab.async false
/- Checked module: TraceFixedSquareSuccessor -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_small_left_alternative_impossible {a v : T}
    (ha : NF a) (hv : NF v)
    (heq : mul a (mul a v) = mul (mul a a) v)
    (hout : ht (mul (mul a a) v) ≤ ht a) : False := by
  let A := mul a a
  let r := mul a v
  let x := mul A v
  have hA : ht A = ht a + 1 := by dsimp only [A]; rw [mul_square]; rfl
  change ht x ≤ ht a at hout
  have hgap := nf_mul_height_key_gap (a:=A) hv
  change ht x = max (ht A) (ht v) + 1 ∨ (ht A + 3 ≤ ht v ∧ ht x + 2 ≤ ht v) at hgap
  have hxv : ht x < ht v := by rcases hgap with hp | hp <;> omega
  obtain ⟨z,l,t,hvc⟩ := mul_return_of_height_lt (a:=A) (b:=v) hxv
  have hag : a ≠ A := by intro he; have heh := congrArg ht he; omega
  have hrg := mul_height_off_return_key (a:=a) hvc hag
  change ht r = max (ht a) (ht v) + 1 at hrg
  have hor := mul_origin_of_right_height_le (a:=a) (b:=v) (by change ht v ≤ ht r; omega)
  change origin r = some (a,v) at hor
  have hl : ReturnLadder a A a x x r v := ⟨nf_mul ha hv,rfl,hor,heq,rfl⟩
  exact return_ladder_second_dominant_impossible hl (by omega) (by omega) (by omega) (by omega)

theorem normal_fixed_square_successor_impossible {u k : T}
    (hu : NF u) (hk : NF k) (hfixed : mul u k = u) :
    mul u (mul (mul u u) k) ≠ u := by
  let A := mul u u
  let q := mul A k
  intro hqfixed
  change mul u q = u at hqfixed
  have hA : ht A = ht u + 1 := by dsimp only [A]; rw [mul_square]; rfl
  have huk : ht u < ht k := by
    have hi := inverse_height_strict (inverse_complete u k)
    rw [hfixed] at hi
    omega
  obtain ⟨z,l,r,hkc⟩ := mul_return_of_height_lt (a:=u) (b:=k) (by rw [hfixed]; exact huk)
  rw [hfixed] at hkc
  have hAu : A ≠ u := by intro he; have heh := congrArg ht he; omega
  have hqg := mul_height_off_return_key (a:=A) hkc hAu
  change ht q = max (ht A) (ht k) + 1 at hqg
  have hoq := mul_origin_of_right_height_le (a:=A) (b:=k) (by change ht k ≤ ht q; omega)
  change origin q = some (A,k) at hoq
  have hnA : NF A := nf_mul hu hu
  have hnq : NF q := nf_mul hnA hk
  obtain ⟨s,_,hns,_,hAs,hks,hsgap,_⟩ := nf_return_origin_trace hnq hoq hqfixed (by omega)
  change mul A s = A at hAs
  have hAsize : ht A < ht s := by
    have hi := inverse_height_strict (inverse_complete A s)
    rw [hAs] at hi
    omega
  have hksize : ht s < ht k := by omega
  have hkg := mul_height_growth_of_right_le (a:=u) (b:=s) (by rw [hks]; omega)
  rw [hks] at hkg
  have hok := mul_origin_of_right_height_le (a:=u) (b:=s) (by rw [hks]; omega)
  rw [hks] at hok
  obtain ⟨t,_,hnt,_,hut,hst,htgap,_⟩ := nf_return_origin_trace hk hok hfixed huk
  change mul A t = u at hut
  have hos := mul_origin_of_right_height_le (a:=u) (b:=t) (by rw [hst]; omega)
  rw [hst] at hos
  obtain ⟨v,_,hnv,_,huv,htv,_,_⟩ := nf_return_origin_trace hns hos hAs hAsize
  have halt : mul A (mul A v) = mul (mul A A) v := by rw [htv,hut,huv]
  exact normal_small_left_alternative_impossible hnA hnv halt (by rw [huv]; omega)

end submission.Austin12087Trace

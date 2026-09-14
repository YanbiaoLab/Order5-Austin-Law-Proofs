prelude
import TraceFoldTower
set_option autoImplicit false

namespace Austin12087Trace
open T

def ReturnLadder (a b c x y j h : T) : Prop :=
  NF j ∧ mul c h = j ∧ origin j = some (c,h) ∧ mul a j = x ∧ mul b h = y

theorem nf_return_origin_trace {a j x c h : T} (hn : NF j)
    (ho : origin j = some (c,h)) (hm : mul a j = x) (hs : ht x < ht j) :
    ∃ r, j = T.c a x r c h ∧ NF r ∧ NF h ∧
      mul (mul a x) r = c ∧ mul x r = h ∧
      ht r + 2 ≤ ht j ∧ ht a + 3 ≤ ht j := by
  obtain ⟨r,l,b,hj⟩ := mul_return_of_height_lt (a:=a) (b:=j) (by rw [hm]; exact hs)
  rw [hm] at hj
  rw [hj,origin] at ho
  obtain ⟨hl,hb⟩ := Prod.mk.inj (Option.some.inj ho)
  subst l; subst b
  have hnf : NF (T.c a x r c h) := hj ▸ hn
  have hc := nf_code_actual hnf
  have hg := nf_code_height_gap hnf
  have hk := nf_code_key_height_gap hnf
  exact ⟨r,hj,hc.2.2.1,hc.2.2.2.2.1,hc.2.2.2.2.2.2.1,hc.2.2.2.2.2.2.2,
    by rw [hj]; exact hg.2.2,by rw [hj]; exact hk⟩

theorem return_ladder_step {a b c x y j h : T}
    (hl : ReturnLadder a b c x y j h) (hx : ht x < ht j) (hc : ht c < ht h) :
    ∃ r, ReturnLadder b (mul a x) x y c h r ∧ ht r < ht j := by
  obtain ⟨hn,hgen,hor,hfirst,hsecond⟩ := hl
  obtain ⟨r,_,hnr,hnh,hr,hh,hrgap,_⟩ := nf_return_origin_trace hn hor hfirst hx
  have hg := mul_height_growth_of_right_le (a:=c) (b:=h) (by
    rw [hgen]
    exact Nat.le_of_lt (origin_height hor).2)
  rw [hgen] at hg
  have hrs : ht r < ht h := by omega
  have hoh := mul_origin_of_right_height_le (a:=x) (b:=r) (by rw [hh]; omega)
  rw [hh] at hoh
  exact ⟨r,⟨hnh,hh,hoh,hsecond,hr⟩,by omega⟩

theorem return_ladder_dominant_impossible {a b c x y j h : T}
    (hl : ReturnLadder a b c x y j h)
    (hc : ht c ≤ ht a) (hx : ht x ≤ ht a) (hy : ht y ≤ ht a) : False := by
  have main : ∀ n, ∀ a b c x y j h : T, ht j = n →
      ReturnLadder a b c x y j h →
      ht c ≤ ht a → ht x ≤ ht a → ht y ≤ ht a → False := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro a b c x y j h hjn hl hc hx hy
      have ha := inverse_height_strict (inverse_complete a j)
      rw [hl.2.2.2.1] at ha
      have haj : ht a < ht j := by omega
      obtain ⟨_,_,_,_,_,_,_,hkey⟩ := nf_return_origin_trace hl.1 hl.2.2.1 hl.2.2.2.1 (by omega)
      have hg := mul_height_growth_of_right_le (a:=c) (b:=h) (by
        rw [hl.2.1]
        exact Nat.le_of_lt (origin_height hl.2.2.1).2)
      rw [hl.2.1] at hg
      have hah : ht a < ht h := by omega
      obtain ⟨r,hl₁,hrj⟩ := return_ladder_step hl (by omega) (by omega)
      have hag := mul_height_growth_of_left_ge (a:=a) (b:=x) hx
      have har := inverse_height_strict (inverse_complete (mul a x) r)
      rw [hl₁.2.2.2.2] at har
      have hxr : ht x < ht r := by omega
      obtain ⟨s,hl₂,_⟩ := return_ladder_step hl₁ (by omega) hxr
      exact ih (ht r) (by omega) (mul a x) (mul b y) y c x r s rfl hl₂
        (by omega) (by omega) (by omega)
  exact main (ht j) a b c x y j h rfl hl hc hx hy

theorem return_ladder_second_dominant_impossible {a b c x y j h : T}
    (hl : ReturnLadder a b c x y j h) (hj : ht x < ht j)
    (hc : ht c ≤ ht b) (hx : ht x ≤ ht b) (hy : ht y ≤ ht b) : False := by
  have hb := inverse_height_strict (inverse_complete b h)
  rw [hl.2.2.2.2] at hb
  obtain ⟨r,hl',_⟩ := return_ladder_step hl hj (by omega)
  exact return_ladder_dominant_impossible hl' hx hy hc

end Austin12087Trace
#print axioms Austin12087Trace.nf_return_origin_trace
#print axioms Austin12087Trace.return_ladder_step
#print axioms Austin12087Trace.return_ladder_dominant_impossible
#print axioms Austin12087Trace.return_ladder_second_dominant_impossible

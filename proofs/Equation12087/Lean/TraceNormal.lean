prelude
import TraceColumnReturn
set_option autoImplicit false

namespace Austin12087Trace
open T

-- Every non-square composite must be its recorded actual multiplication.
-- The atom/square clauses retain an explicit infinite supply of elements.
inductive NF : T → Prop where
  | atom (n : Nat) : NF (T.atom n)
  | square {a : T} : NF a → NF (s a)
  | pair {a b : T} : NF a → NF b → mul a b = p a b → NF (p a b)
  | code {y x z a b : T} : NF y → NF x → NF z → NF a → NF b →
      mul a b = c y x z a b → NF (c y x z a b)

theorem nf_origin {out a b : T} (hn : NF out) (ho : origin out = some (a,b)) :
    NF a ∧ NF b := by
  cases hn with
  | atom n => simp only [origin] at ho; cases ho
  | square ht =>
    have hp := Prod.mk.inj (Option.some.inj ho)
    exact ⟨hp.1 ▸ ht,hp.2 ▸ ht⟩
  | pair hl hr hm =>
    have hp := Prod.mk.inj (Option.some.inj ho)
    exact ⟨hp.1 ▸ hl,hp.2 ▸ hr⟩
  | code hy hx hz hl hr hm =>
    have hp := Prod.mk.inj (Option.some.inj ho)
    exact ⟨hp.1 ▸ hl,hp.2 ▸ hr⟩

theorem nf_inverse {b out a : T} (hb : NF b) (ho : NF out)
    (hi : inverse b out = some a) : NF a := by
  rcases inverse_cases hi with ⟨he,_⟩ | ⟨hor,_⟩ | hbasic
  · exact he ▸ hb
  · exact (nf_origin ho hor).1
  · obtain ⟨z,l,r,hb'⟩ := basicInverse_cases hbasic
    rw [hb'] at hb
    cases hb with
    | code ha _ _ _ _ _ => exact ha

theorem nf_common_column_parameters {a b y x z : T}
    (ha : NF a) (hb : NF b)
    (hma : mul (mul y x) z = a) (hmb : mul x z = b) : NF y ∧ NF x ∧ NF z := by
  have hn : a ≠ b := by
    intro he
    exact mul_ne_right y x (right_injective _ _ z (hma.trans (he.trans hmb.symm)))
  have hz : NF z := by
    by_cases hs : sz b ≤ sz a
    · exact (nf_origin ha (distinct_outputs_large_origin hma hmb hn hs).1).2
    · exact (nf_origin hb (distinct_outputs_large_origin hmb hma (Ne.symm hn) (by omega)).1).2
  have hx : NF x := nf_inverse hz hb (by rw [←hmb]; exact inverse_complete x z)
  have hu : NF (mul y x) := nf_inverse hz ha (by rw [←hma]; exact inverse_complete _ z)
  exact ⟨nf_inverse hx hu (inverse_complete y x),hx,hz⟩

theorem nf_mul {a b : T} (ha : NF a) (hb : NF b) : NF (mul a b) := by
  rcases mul_cases a b with ⟨_,hm⟩ | ⟨x,z,l,r,hb',hm⟩ | hm | ⟨y,x,z,hm⟩
  · rw [hm]; exact NF.square hb
  · rw [hm]
    have hcode : NF (c a x z l r) := hb' ▸ hb
    cases hcode with
    | code _ hx _ _ _ _ => exact hx
  · rw [hm]; exact NF.pair ha hb hm
  · have hc := mul_code_semantics hm
    obtain ⟨hy,hx,hz⟩ := nf_common_column_parameters ha hb hc.1 hc.2
    rw [hm]; exact NF.code hy hx hz ha hb hm

theorem nf_code_actual {y x z a b : T} (h : NF (c y x z a b)) :
    NF y ∧ NF x ∧ NF z ∧ NF a ∧ NF b ∧
      mul a b = c y x z a b ∧ mul (mul y x) z = a ∧ mul x z = b := by
  cases h with
  | code hy hx hz ha hb hm =>
    exact ⟨hy,hx,hz,ha,hb,hm,mul_code_semantics hm⟩

def NormalTree := {a : T // NF a}

def normalMul (a b : NormalTree) : NormalTree := ⟨mul a.val b.val,nf_mul a.property b.property⟩

def normalAtom (n : Nat) : NormalTree := ⟨T.atom n,NF.atom n⟩

theorem normalAtom_injective {m n : Nat} (h : normalAtom m = normalAtom n) : m = n :=
  T.atom.inj (congrArg Subtype.val h)

theorem normalAtom_nontrivial : normalAtom 0 ≠ normalAtom 1 := by
  intro h
  have he := normalAtom_injective h
  omega

theorem normal_law_of_nf_source
    (h : ∀ x y z : T, NF x → NF y → NF z → Source12087 x y z) :
    ∀ x y z : NormalTree,
      x = normalMul y (normalMul (normalMul (normalMul y x) z) (normalMul x z)) := by
  intro x y z
  apply Subtype.ext
  exact h x.val y.val z.val x.property y.property z.property

-- Closure and infinitude do not establish the source law on this carrier.
end Austin12087Trace
#print axioms Austin12087Trace.nf_origin
#print axioms Austin12087Trace.nf_inverse
#print axioms Austin12087Trace.nf_common_column_parameters
#print axioms Austin12087Trace.nf_mul
#print axioms Austin12087Trace.nf_code_actual
#print axioms Austin12087Trace.normalMul
#print axioms Austin12087Trace.normalAtom_injective
#print axioms Austin12087Trace.normalAtom_nontrivial
#print axioms Austin12087Trace.normal_law_of_nf_source

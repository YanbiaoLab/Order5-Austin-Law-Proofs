prelude
import LineageSyntax.Decoder
set_option autoImplicit false
set_option Elab.async false

namespace Equation22446Lineage
open Equation22446Guarded

/- Evaluation and multiplication relations for the NEW grammar. Neither
existence nor preservation of Normal asserts unique returns or Source. -/
inductive Eval : T → T → Prop where
  | atom (c : Shade) (n : Nat) : Eval (.e c n) (.e c n)
  | raw {a b a' b' : T} (c : Shade) : Eval a a' → Eval b b' →
      (¬ ∃ o, Guard a' b' o) → Eval (.p c a b) (.p c a' b')
  | hit {a b a' b' o : T} (c : Shade) : Eval a a' → Eval b b' →
      Guard a' b' o → Eval (.p c a b) (rotate c o)

theorem eval_normal {t n : T} (h : Eval t n) : Normal n := by
  induction h with
  | atom c n => trivial
  | raw c _ _ hn ha hb => exact ⟨ha,hb,hn⟩
  | hit c _ _ hg ha hb => exact normal_guard_output ha hb hg c

theorem eval_exists (t : T) : ∃ n, Eval t n := by
  classical
  induction t with
  | e c n => exact ⟨.e c n,.atom c n⟩
  | p c a b ha hb =>
      obtain ⟨a',ha'⟩ := ha
      obtain ⟨b',hb'⟩ := hb
      by_cases h : ∃ o, Guard a' b' o
      · obtain ⟨o,ho⟩ := h
        exact ⟨rotate c o,.hit c ha' hb' ho⟩
      · exact ⟨.p c a' b',.raw c ha' hb' h⟩

theorem normal_evaluates_self {t : T} (h : Normal t) : Eval t t := by
  induction t with
  | e c n => exact .atom c n
  | p c a b ha hb => exact .raw c (ha h.1) (hb h.2.1) h.2.2

theorem eval_normal_fixed {t n : T} (hn : Normal t) (h : Eval t n) : n = t := by
  induction h with
  | atom c n => rfl
  | raw c _ _ h ha hb => rw [ha hn.1,hb hn.2.1]
  | hit c _ _ h ha hb =>
      rw [ha hn.1,hb hn.2.1] at h
      exact False.elim (hn.2.2 ⟨_,h⟩)

inductive Product : T → T → T → Prop where
  | raw {a b : T} : (¬ ∃ o, Guard a b o) → Product a b (P a b)
  | hit {a b o : T} : Guard a b o → Product a b o

theorem normal_pair_eval_product {a b o : T} (ha : Normal a) (hb : Normal b)
    (he : Eval (P a b) o) : Product a b o := by
  cases he with
  | raw c ea eb hn =>
      rw [eval_normal_fixed ha ea,eval_normal_fixed hb eb] at hn ⊢
      exact .raw hn
  | hit c ea eb hg =>
      rw [eval_normal_fixed ha ea,eval_normal_fixed hb eb] at hg
      exact .hit hg

theorem product_exists (a b : T) : ∃ o, Product a b o := by
  classical
  by_cases h : ∃ o, Guard a b o
  · obtain ⟨o,ho⟩ := h
    exact ⟨o,.hit ho⟩
  · exact ⟨P a b,.raw h⟩

theorem product_normal {a b o : T} (ha : Normal a) (hb : Normal b)
    (h : Product a b o) : Normal o := by
  cases h with
  | raw hn => exact ⟨ha,hb,hn⟩
  | hit hg => exact normal_guard_output ha hb hg .zero

noncomputable def chosen (a b : T) : T := Classical.choose (product_exists a b)

theorem chosen_product (a b : T) : Product a b (chosen a b) :=
  Classical.choose_spec (product_exists a b)

theorem chosen_normal {a b : T} (ha : Normal a) (hb : Normal b) : Normal (chosen a b) :=
  product_normal ha hb (chosen_product a b)

noncomputable def multiplication (a b : NormalTree) : NormalTree :=
  ⟨chosen a.val b.val,chosen_normal a.property b.property⟩

theorem diagonal_guard (x : T) : Guard x x (S x) := by
  apply Guard.rectangle (Or.inl (.root .one x))
  · have h := column_canonical (S x)
    rwa [cube] at h
  · have h := Image.square (S x)
    rwa [cube] at h

#print axioms eval_normal
#print axioms eval_exists
#print axioms normal_evaluates_self
#print axioms eval_normal_fixed
#print axioms normal_pair_eval_product
#print axioms product_exists
#print axioms product_normal
#print axioms chosen_product
#print axioms chosen_normal
#print axioms diagonal_guard
end Equation22446Lineage

/- Standalone E12294 certificate. Only Lean Init imports.
   No finiteness, cancellation, auxiliary distinctness, or model assumptions.
   Every proof below is checked again in this file, without project oleans. -/
prelude
import Init.Prelude
import Init.Core
import Init.Notation
import Init.Tactics
set_option autoImplicit false
set_option Elab.async false
universe u
namespace Equation12294RightFibers
def Code {G : Type u} (op : G → G → G) (y x z : G) : G :=
  op (op (op z y) x) (op x y)

def Law {G : Type u} (op : G → G → G) : Prop :=
  ∀ x y z, x = op y (Code op y x z)

theorem code_decodes {G : Type u} (op : G → G → G) (law : Law op)
    (y x z : G) : op y (Code op y x z) = x := (law x y z).symm

def ReturnColumn {G : Type u} (op : G → G → G) (x u : G) : G :=
  op (op u x) u

theorem fiber_return {G : Type u} (op : G → G → G) (law : Law op)
    (x y u : G) (h : op x y = u) : op y (ReturnColumn op x u) = x := by
  have e := (law x y x).symm
  change op y (op (op (op x y) x) (op x y)) = x at e
  rw [h] at e
  exact e

def Recover {G : Type u} (op : G → G → G) (a u : G) : G :=
  op (op (op u a) u) (op u a)

theorem recover_input {G : Type u} (op : G → G → G) (law : Law op)
    (a b : G) : Recover op a (op a b) = b := by
  let c := Code op b a a
  have hc : op b c = a := code_decodes op law b a a
  have e := (law b c b).symm
  change op c (op (op (op b c) b) (op b c)) = b at e
  rw [hc] at e
  exact e

theorem left_cancel {G : Type u} (op : G → G → G) (law : Law op)
    (a b c : G) (h : op a b = op a c) : b = c :=
  (recover_input op law a b).symm.trans
    ((congrArg (Recover op a) h).trans (recover_input op law a c))

theorem middle_independent {G : Type u} (op : G → G → G) (law : Law op)
    (y x z t : G) : Code op y x z = Code op y x t :=
  left_cancel op law y (Code op y x z) (Code op y x t)
    ((code_decodes op law y x z).trans (code_decodes op law y x t).symm)

theorem recover_section {G : Type u} (op : G → G → G) (law : Law op)
    (a u : G) : op a (Recover op a u) = u := by
  have h := recover_input op law a (Code op a u a)
  rw [code_decodes op law a u a] at h
  exact (congrArg (op a) h).trans (code_decodes op law a u a)

end Equation12294RightFibers

namespace Equation12294FiberColumns
open Equation12294RightFibers
theorem shared_fiber_and_column_image {G : Type u} (op : G → G → G) (law : Law op)
    (q x y y' a b : G) (hy : op y q = x) (hy' : op y' q = x)
    (hi : op a y = op b y') : y = y' := by
  have h := left_cancel op law y _ _ ((code_decodes op law y x a).trans hy.symm)
  have h' := left_cancel op law y' _ _ ((code_decodes op law y' x b).trans hy'.symm)
  have hh := h.trans h'.symm
  unfold Code at hh
  rw [hi] at hh
  exact left_cancel op law x y y'
    (left_cancel op law (op (op b y') x) _ _ hh)

end Equation12294FiberColumns

namespace Equation12294ColumnPredecessor
open Equation12294RightFibers
def Companion {G : Type u} (op : G → G → G) (a : G) : G := op (op a a) a

def SelfDivision {G : Type u} (op : G → G → G) (a : G) : G := Code op a a a

theorem fixed_column_unique {G : Type u} (op : G → G → G) (law : Law op)
    (a q : G) (h : op a q = a) : q = SelfDivision op a :=
  left_cancel op law a q (SelfDivision op a) (h.trans (code_decodes op law a a a).symm)

end Equation12294ColumnPredecessor

namespace Equation12294SelfDivision
open Equation12294RightFibers Equation12294ColumnPredecessor
theorem column_image_predecessor {G : Type u} (op : G → G → G) (law : Law op)
    (a q z : G) (h : op a q = a) :
    op (op (op z q) a) a = Companion op a := by
  have first := code_decodes op law q a z
  change op q (op (op (op z q) a) (op a q)) = a at first
  rw [h] at first
  have second : op q (Companion op a) = a := fiber_return op law a q a h
  exact left_cancel op law q _ _ (first.trans second.symm)

theorem selfdivision_square_bridge {G : Type u} (op : G → G → G)
    (law : Law op) (a q : G) (h : op a q = a) :
    op a (op q q) = SelfDivision op q := by
  have bridge := middle_independent op law q q a q
  change op (op (op a q) q) (op q q) = SelfDivision op q at bridge
  rw [h, h] at bridge
  exact bridge

theorem canonical_square_bridge {G : Type u} (op : G → G → G)
    (law : Law op) (a : G) :
    op a (op (SelfDivision op a) (SelfDivision op a)) =
      SelfDivision op (SelfDivision op a) :=
  selfdivision_square_bridge op law a (SelfDivision op a)
    (code_decodes op law a a a)

end Equation12294SelfDivision

namespace Equation12294RightImageFirst
open Equation12294RightFibers Equation12294ColumnPredecessor Equation12294FiberColumns
theorem image_predecessor_unique {G : Type u} (op : G → G → G) (law : Law op)
    (a z : G) (hpre : op (op z a) a = Companion op a) : op z a = op a a := by
  let q := SelfDivision op a
  have hq : op a q = a := code_decodes op law a a a
  let b := op a a
  let p := op b a
  let m := op z a
  let t := op p m
  let r := op t p
  let v := op r q
  let d := op m v
  let s := op d b
  let u := op r s
  let w := op a s
  have hma : op m a = p := hpre
  have hqp : op q p = a := fiber_return op law a q a hq
  have hpb : op p b = q := (fixed_column_unique op law a q hq).symm
  have har : op a r = m := by
    have hr := recover_section op law a m
    change op a (op (op (op m a) m) (op m a)) = m at hr
    rw [hma] at hr
    exact hr
  have hva : op v a = b := by
    have hd := code_decodes op law p q t
    change op p (op v (op q p)) = q at hd
    rw [hqp] at hd
    exact left_cancel op law p _ b (hd.trans hpb.symm)
  have hqd : op q d = r := by
    have hd := code_decodes op law q r a
    change op q (op (op (op a q) r) (op r q)) = r at hd
    rw [hq, har] at hd
    exact hd
  have has : op a s = v := by
    have hd := code_decodes op law a v z
    change op a (op (op m v) (op v a)) = v at hd
    rw [hva] at hd
    exact hd
  have hbu : op b u = d := by
    have hd := code_decodes op law b d p
    change op b (op (op (op p b) d) (op d b)) = d at hd
    rw [hpb, hqd] at hd
    exact hd
  have hmw : op m w = d := by
    change op m (op a s) = d
    rw [has]
  have hright : op u (op s p) = op w (op s p) := by
    have hd := middle_independent op law p s t q
    change op (op (op t p) s) (op s p) = op (op (op q p) s) (op s p) at hd
    rw [hqp] at hd
    exact hd
  have huw : u = w := shared_fiber_and_column_image op law (op s p) (op w (op s p))
    u w b m hright rfl (hbu.trans hmw.symm)
  have hra : r = a := shared_fiber_and_column_image op law s w r a a z
    huw rfl har
  exact har.symm.trans (congrArg (op a) hra)

theorem fixed_column_image_first_step {G : Type u} (op : G → G → G) (law : Law op)
    (a q z : G) (hq : op a q = a) : op (op z q) a = op a a :=
  image_predecessor_unique op law a (op z q)
    (Equation12294SelfDivision.column_image_predecessor op law a q z hq)

end Equation12294RightImageFirst

namespace Equation12294AllModels
open Equation12294RightFibers Equation12294ColumnPredecessor Equation12294FiberColumns Equation12294RightImageFirst
theorem companion_of_selfdivision {G : Type u} (op : G → G → G) (law : Law op)
    (a : G) : Companion op (SelfDivision op a) = a := by
  let q := SelfDivision op a
  let h := SelfDivision op q
  let s := op (op h a) h
  have haq : op a q = a := code_decodes op law a a a
  have hqh : op q h = q := code_decodes op law q q q
  have hsq : op s q = op q q := fixed_column_image_first_step op law q h (op h a) hqh
  have hdecode : op (op q q) s = a := by
    have e := code_decodes op law (op q q) a a
    unfold Code at e
    have bridge : op a (op q q) = h := Equation12294SelfDivision.canonical_square_bridge op law a
    rw [bridge] at e
    exact e
  have heq : s = q := shared_fiber_and_column_image op law q (op q q)
    s q (op q q) a hsq rfl (hdecode.trans haq.symm)
  exact (congrArg (op (op q q)) heq).symm.trans hdecode

end Equation12294AllModels

namespace Equation12294Standalone
open Equation12294RightFibers Equation12294ColumnPredecessor
open Equation12294RightImageFirst Equation12294AllModels

theorem selfdivision_square {G : Type u} (op : G → G → G) (law : Law op)
    (a : G) : op (SelfDivision op a) (SelfDivision op a) = a := by
  let q := SelfDivision op a
  have haq : op a q = a := code_decodes op law a a a
  have hP : Companion op q = a := companion_of_selfdivision op law a
  have hpre : op (op a q) q = Companion op q := by
    rw [haq, haq]
    exact hP.symm
  have hs := image_predecessor_unique op law q a hpre
  rw [haq] at hs
  exact hs.symm

theorem companion_equals_selfdivision {G : Type u} (op : G → G → G) (law : Law op)
    (a : G) : Companion op a = SelfDivision op a := by
  let q := SelfDivision op a
  have haq : op a q = a := code_decodes op law a a a
  have hs : op q q = a := selfdivision_square op law a
  have hr := recover_input op law q q
  unfold Recover at hr
  rw [hs, haq] at hr
  exact hr

theorem every_element_idempotent {G : Type u} (op : G → G → G) (law : Law op)
    (a : G) : op a a = a := by
  have hQ : SelfDivision op (SelfDivision op a) = a :=
    (companion_equals_selfdivision op law (SelfDivision op a)).symm.trans
      (companion_of_selfdivision op law a)
  have hb := Equation12294SelfDivision.canonical_square_bridge op law a
  rw [selfdivision_square op law a, hQ] at hb
  exact hb

theorem right_projection {G : Type u} (op : G → G → G) (law : Law op)
    (a b : G) : op a b = b := by
  have hb : op b b = b := every_element_idempotent op law b
  have hp : Companion op b = b := by
    unfold Companion
    rw [hb, hb]
  have hpre : op (op a b) b = Companion op b :=
    (fixed_column_image_first_step op law b b a hb).trans (hb.trans hp.symm)
  exact (image_predecessor_unique op law b a hpre).trans hb

theorem all_models_trivial {G : Type u} (op : G → G → G) (law : Law op)
    (a b : G) : a = b := by
  have h := law a b b
  unfold Code at h
  rw [right_projection op law b b, right_projection op law b a,
    right_projection op law a b, right_projection op law a b,
    right_projection op law b b] at h
  exact h

theorem original_equation_forces_equality {G : Type u} (op : G → G → G)
    (equation : ∀ x y z, x = op y (op (op (op z y) x) (op x y)))
    (a b : G) : a = b :=
  all_models_trivial op equation a b

theorem nontrivial_model_impossible {G : Type u} (op : G → G → G)
    (equation : ∀ x y z, x = op y (op (op (op z y) x) (op x y)))
    (a b : G) (hne : a ≠ b) : False :=
  hne (original_equation_forces_equality op equation a b)

#print axioms selfdivision_square
#print axioms companion_equals_selfdivision
#print axioms every_element_idempotent
#print axioms right_projection
#print axioms all_models_trivial
#print axioms original_equation_forces_equality
#print axioms nontrivial_model_impossible
end Equation12294Standalone

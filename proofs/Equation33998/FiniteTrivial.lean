import Mathlib.Data.Fintype.Card
import JudgeMagma.Magma

@[reducible] def Equation2 (G : Type _) [Magma G] : Prop := ∀ (x y : G), x = y
@[reducible] def Equation12073 (G : Type _) [Magma G] : Prop := ∀ (x y z : G), x = y ◇ (((y ◇ x) ◇ x) ◇ (z ◇ z))

theorem finite_trivial (G : Type*) [Magma G] [Finite G] (h : Equation12073 G) : Equation2 G := by
  intro a b
  have ls (y : G) : Function.Surjective (fun t : G => y ◇ t) := by
    intro x
    exact ⟨(((y ◇ x) ◇ x) ◇ (a ◇ a)), (h x y a).symm⟩
  have li (y : G) : Function.Injective (fun t : G => y ◇ t) :=
    Finite.injective_iff_surjective.mpr (ls y)
  let d (x y : G) : G := Classical.choose (ls x y)
  have ld1 (x y : G) : x ◇ d x y = y := Classical.choose_spec (ls x y)
  have ld2 (x y : G) : d x (x ◇ y) = y := li x (ld1 x (x ◇ y))
  have p2 (x y z : G) : (x ◇ (((x ◇ y) ◇ y) ◇ (z ◇ z))) = y := by
    exact (h y x z).symm
  have p3 (x y : G) : (x ◇ (d x y)) = y := by
    exact (ld1 x y)
  have p4 (x y : G) : (d x (x ◇ y)) = y := by
    exact (ld2 x y)
  have p7 (x y z : G) : (x ◇ ((y ◇ (d x y)) ◇ (z ◇ z))) = (d x y) := by
    exact (((congrArg (fun _t : G => (x ◇ ((_t ◇ (d x y)) ◇ (z ◇ z)))) ((p3 x y)))).symm).trans ((p2 x (d x y) z))
  have p8 (x y z : G) : (d x y) = (((x ◇ y) ◇ y) ◇ (z ◇ z)) := by
    exact (((congrArg (fun _t : G => (d x _t)) ((p2 x y z)))).symm).trans ((p4 x (((x ◇ y) ◇ y) ◇ (z ◇ z))))
  have p18 (x y z : G) : (d ((x ◇ y) ◇ y) (d x y)) = (z ◇ z) := by
    exact (((congrArg (fun _t : G => (d ((x ◇ y) ◇ y) _t)) (((p8 x y z)).symm))).symm).trans ((p4 ((x ◇ y) ◇ y) (z ◇ z)))
  have p40 (x y : G) : (x ◇ x) = (y ◇ y) := by
    exact (((p4 ((a ◇ a) ◇ a) (x ◇ x))).symm).trans ((((congrArg (fun _t : G => (d ((a ◇ a) ◇ a) _t)) ((p8 a a x)))).symm).trans ((p18 a a y)))
  have p47 (x y : G) : (d x (y ◇ y)) = x := by
    exact (((congrArg (fun _t : G => (d x _t)) ((p40 x y)))).symm).trans ((p4 x x))
  have p58 (x y : G) : (d x x) = (x ◇ (x ◇ (y ◇ y))) := by
    exact ((((congrArg (fun _t : G => (x ◇ (_t ◇ (y ◇ y)))) ((p3 x x)))).symm).trans ((p7 x x y))).symm
  have p65 (x y : G) : (d x (d x x)) = (x ◇ (y ◇ y)) := by
    exact (((congrArg (fun _t : G => (d x _t)) (((p58 x y)).symm))).symm).trans ((p4 x (x ◇ (y ◇ y))))
  have p70 (x y z : G) : ((d x x) ◇ (x ◇ (y ◇ y))) = (z ◇ z) := by
    exact (((p47 ((d x x) ◇ (x ◇ (y ◇ y))) y)).symm).trans ((((congrArg (fun _t : G => (d ((d x x) ◇ (x ◇ (y ◇ y))) _t)) ((p4 x (y ◇ y))))).symm).trans ((((congrArg (fun _t : G => (d (_t ◇ (x ◇ (y ◇ y))) (d x (x ◇ (y ◇ y))))) (((p58 x y)).symm))).symm).trans ((p18 x (x ◇ (y ◇ y)) z))))
  have p82 (x y : G) : (d x (d x (d x x))) = (y ◇ y) := by
    exact (((congrArg (fun _t : G => (d x _t)) (((p65 x y)).symm))).symm).trans ((p4 x (y ◇ y)))
  have p417 (x y : G) : (d x x) = (x ◇ (y ◇ y)) := by
    exact (((p47 (d x x) a)).symm).trans ((((congrArg (fun _t : G => (d (d x x) _t)) ((p70 x y a)))).symm).trans ((p4 (d x x) (x ◇ (y ◇ y)))))
  have p459 (x y : G) : (x ◇ (x ◇ (y ◇ y))) = x := by
    exact (((congrArg (fun _t : G => (x ◇ _t)) ((p417 x y)))).symm).trans ((p3 x x))
  have p472 (x : G) : (d x x) = x := by
    exact ((((p459 x a)).symm).trans ((((congrArg (fun _t : G => (x ◇ (_t ◇ (a ◇ a)))) ((p459 x a)))).symm).trans ((((congrArg (fun _t : G => (x ◇ ((x ◇ _t) ◇ (a ◇ a)))) ((p417 x a)))).symm).trans ((p7 x x a))))).symm
  have p474 (x y : G) : (x ◇ (y ◇ y)) = x := by
    exact ((((p417 x y)).symm).trans ((p58 x a))).trans ((p459 x a))
  have p475 (x : G) : (x ◇ x) = x := by
    exact ((((((p472 x)).symm).trans (((p58 x (a ◇ a))).trans ((congrArg (fun _t : G => (x ◇ (x ◇ _t))) (((p417 (a ◇ a) a)).symm))))).trans ((congrArg (fun _t : G => (x ◇ (x ◇ _t))) ((p472 (a ◇ a)))))).trans ((congrArg (fun _t : G => (x ◇ _t)) ((p474 x a))))).symm
  have p479 (x y : G) : x = y := by
    exact ((((((p472 x)).symm).trans ((((congrArg (fun _t : G => (d x _t)) ((p472 x)))).symm).trans ((((congrArg (fun _t : G => (d x (d x _t))) ((p472 x)))).symm).trans (((p82 x (y ◇ y))).trans (((p417 (y ◇ y) y)).symm))))).trans ((congrArg (fun _t : G => (d _t (y ◇ y))) ((p475 y))))).trans ((congrArg (fun _t : G => (d y _t)) ((p475 y))))).trans ((p472 y))
  exact (p479 a a).trans (p479 b a).symm

@[reducible] def Equation33998 (G : Type _) [Magma G] : Prop := ∀ (x y z : G), x = ((y ◇ y) ◇ (x ◇ (x ◇ z))) ◇ z

theorem finite_trivial_dual (G : Type*) [Magma G] [Finite G] (h : Equation33998 G) : Equation2 G := by
  let opposite : Magma G := ⟨fun x y => y ◇ x⟩
  have hd : @ Equation12073 G opposite := by
    intro x y z
    exact h x z y
  exact @ finite_trivial G opposite inferInstance hd

#print axioms finite_trivial_dual

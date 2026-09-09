import Mathlib.Data.Fintype.Card
import JudgeMagma.Magma

@[reducible] def Equation2 (G : Type _) [Magma G] : Prop := ∀ (x y : G), x = y
@[reducible] def Equation11082 (G : Type _) [Magma G] : Prop := ∀ (x y z : G), x = y ◇ ((x ◇ (y ◇ x)) ◇ (z ◇ z))

theorem finite_trivial (G : Type*) [Magma G] [Finite G] (h : Equation11082 G) : Equation2 G := by
  intro a b
  have ls (y : G) : Function.Surjective (fun t : G => y ◇ t) := by
    intro x
    exact ⟨((x ◇ (y ◇ x)) ◇ (a ◇ a)), (h x y a).symm⟩
  have li (y : G) : Function.Injective (fun t : G => y ◇ t) :=
    Finite.injective_iff_surjective.mpr (ls y)
  let d (x y : G) : G := Classical.choose (ls x y)
  have ld1 (x y : G) : x ◇ d x y = y := Classical.choose_spec (ls x y)
  have ld2 (x y : G) : d x (x ◇ y) = y := li x (ld1 x (x ◇ y))
  have p2 (x y z : G) : (x ◇ ((y ◇ (x ◇ y)) ◇ (z ◇ z))) = y := by
    exact (h y x z).symm
  have p4 (x y : G) : (d x (x ◇ y)) = y := by
    exact (ld2 x y)
  have p6 (u x y z : G) : (x ◇ ((((y ◇ (x ◇ y)) ◇ (z ◇ z)) ◇ y) ◇ (u ◇ u))) = ((y ◇ (x ◇ y)) ◇ (z ◇ z)) := by
    exact (((congrArg (fun _t : G => (x ◇ ((((y ◇ (x ◇ y)) ◇ (z ◇ z)) ◇ _t) ◇ (u ◇ u)))) ((p2 x y z)))).symm).trans ((p2 x ((y ◇ (x ◇ y)) ◇ (z ◇ z)) u))
  have p9 (x y z : G) : (d x y) = ((y ◇ (x ◇ y)) ◇ (z ◇ z)) := by
    exact (((congrArg (fun _t : G => (d x _t)) ((p2 x y z)))).symm).trans ((p4 x ((y ◇ (x ◇ y)) ◇ (z ◇ z))))
  have p22 (x y z : G) : (d (x ◇ (y ◇ x)) (d y x)) = (z ◇ z) := by
    exact (((congrArg (fun _t : G => (d (x ◇ (y ◇ x)) _t)) (((p9 y x z)).symm))).symm).trans ((p4 (x ◇ (y ◇ x)) (z ◇ z)))
  have p45 (u x y z : G) : (d ((x ◇ ((y ◇ y) ◇ x)) ◇ (z ◇ z)) (d (((x ◇ ((y ◇ y) ◇ x)) ◇ (z ◇ z)) ◇ x) (y ◇ y))) = (u ◇ u) := by
    exact (((congrArg (fun _t : G => (d _t (d (((x ◇ ((y ◇ y) ◇ x)) ◇ (z ◇ z)) ◇ x) (y ◇ y)))) ((p6 y (y ◇ y) x z)))).symm).trans ((p22 (y ◇ y) (((x ◇ ((y ◇ y) ◇ x)) ◇ (z ◇ z)) ◇ x) u))
  have p49 (x y : G) : (x ◇ x) = (y ◇ y) := by
    exact (((p4 (a ◇ (a ◇ a)) (x ◇ x))).symm).trans ((((congrArg (fun _t : G => (d (a ◇ (a ◇ a)) _t)) ((p9 a a x)))).symm).trans ((p22 a a y)))
  have p56 (x y : G) : (d x (y ◇ y)) = x := by
    exact (((congrArg (fun _t : G => (d x _t)) ((p49 x y)))).symm).trans ((p4 x x))
  have p63 (x y : G) : (x ◇ x) = y := by
    exact ((((p4 ((y ◇ ((a ◇ a) ◇ y)) ◇ (a ◇ a)) y)).symm).trans ((((congrArg (fun _t : G => (d ((y ◇ ((a ◇ a) ◇ y)) ◇ (a ◇ a)) _t)) ((p56 (((y ◇ ((a ◇ a) ◇ y)) ◇ (a ◇ a)) ◇ y) a)))).symm).trans ((p45 x y a a)))).symm
  have p74 (x y : G) : (d x y) = x := by
    exact (((congrArg (fun _t : G => (d x _t)) ((p63 x y)))).symm).trans ((p4 x x))
  have p75 (x y : G) : x = y := by
    exact (((p74 x (a ◇ a))).symm).trans ((((congrArg (fun _t : G => (d x _t)) (((p63 a (x ◇ y))).symm))).symm).trans ((p4 x y)))
  exact (p75 a a).trans (p75 b a).symm

#print axioms finite_trivial

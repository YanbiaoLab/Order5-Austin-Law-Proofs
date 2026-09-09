import Mathlib.Data.Fintype.Card
import JudgeMagma.Magma

@[reducible] def Equation2 (G : Type _) [Magma G] : Prop := ∀ (x y : G), x = y
@[reducible] def Equation11116 (G : Type _) [Magma G] : Prop := ∀ (x y z : G), x = y ◇ ((x ◇ (z ◇ x)) ◇ (y ◇ y))

theorem finite_trivial (G : Type*) [Magma G] [Finite G] (h : Equation11116 G) : Equation2 G := by
  intro a b
  have ls (y : G) : Function.Surjective (fun t : G => y ◇ t) := by
    intro x
    exact ⟨((x ◇ (a ◇ x)) ◇ (y ◇ y)), (h x y a).symm⟩
  have li (y : G) : Function.Injective (fun t : G => y ◇ t) :=
    Finite.injective_iff_surjective.mpr (ls y)
  let d (x y : G) : G := Classical.choose (ls x y)
  have ld1 (x y : G) : x ◇ d x y = y := Classical.choose_spec (ls x y)
  have ld2 (x y : G) : d x (x ◇ y) = y := li x (ld1 x (x ◇ y))
  have p2 (x y z : G) : (x ◇ ((y ◇ (z ◇ y)) ◇ (x ◇ x))) = y := by
    exact (h y x z).symm
  have p4 (x y : G) : (d x (x ◇ y)) = y := by
    exact (ld2 x y)
  have p8 (x y z : G) : (d x y) = ((y ◇ (z ◇ y)) ◇ (x ◇ x)) := by
    exact (((congrArg (fun _t : G => (d x _t)) ((p2 x y z)))).symm).trans ((p4 x ((y ◇ (z ◇ y)) ◇ (x ◇ x))))
  have p16 (x y z : G) : (((x ◇ y) ◇ (z ◇ (x ◇ y))) ◇ (x ◇ x)) = y := by
    exact (((p8 x (x ◇ y) z)).symm).trans ((p4 x y))
  have p41 (u x y z : G) : ((x ◇ (y ◇ x)) ◇ (((z ◇ x) ◇ (u ◇ (z ◇ x))) ◇ ((z ◇ x) ◇ (u ◇ (z ◇ x))))) = (z ◇ z) := by
    exact (((congrArg (fun _t : G => ((x ◇ (y ◇ _t)) ◇ (((z ◇ x) ◇ (u ◇ (z ◇ x))) ◇ ((z ◇ x) ◇ (u ◇ (z ◇ x)))))) ((p16 z x u)))).symm).trans ((((congrArg (fun _t : G => ((_t ◇ (y ◇ (((z ◇ x) ◇ (u ◇ (z ◇ x))) ◇ (z ◇ z)))) ◇ (((z ◇ x) ◇ (u ◇ (z ◇ x))) ◇ ((z ◇ x) ◇ (u ◇ (z ◇ x)))))) ((p16 z x u)))).symm).trans ((p16 ((z ◇ x) ◇ (u ◇ (z ◇ x))) (z ◇ z) y)))
  have p42 (x y : G) : (((x ◇ x) ◇ y) ◇ (x ◇ x)) = x := by
    exact (((congrArg (fun _t : G => (((x ◇ x) ◇ _t) ◇ (x ◇ x))) ((p16 x y a)))).symm).trans ((p16 x x ((x ◇ y) ◇ (a ◇ (x ◇ y)))))
  have p54 (x y : G) : (x ◇ (y ◇ y)) = y := by
    exact (((congrArg (fun _t : G => (_t ◇ (y ◇ y))) ((p2 (y ◇ y) x a)))).symm).trans ((p42 y ((x ◇ (a ◇ x)) ◇ ((y ◇ y) ◇ (y ◇ y)))))
  have p61 (x y z : G) : ((x ◇ y) ◇ (z ◇ (x ◇ y))) = (x ◇ x) := by
    exact (((p54 (y ◇ (a ◇ y)) ((x ◇ y) ◇ (z ◇ (x ◇ y))))).symm).trans ((p41 z y a x))
  have p63 (x y : G) : x = y := by
    exact (((p54 (x ◇ x) x)).symm).trans ((((congrArg (fun _t : G => (_t ◇ (x ◇ x))) ((p61 x y a)))).symm).trans ((p16 x y a)))
  exact (p63 a a).trans (p63 b a).symm

#print axioms finite_trivial

import Mathlib.Data.Fintype.Card
import JudgeMagma.Magma

@[reducible] def Equation2 (G : Type _) [Magma G] : Prop := ∀ (x y : G), x = y
@[reducible] def Equation12087 (G : Type _) [Magma G] : Prop := ∀ (x y z : G), x = y ◇ (((y ◇ x) ◇ z) ◇ (x ◇ z))

theorem finite_trivial (G : Type*) [Magma G] [Finite G] (h : Equation12087 G) : Equation2 G := by
  intro a b
  have ls (y : G) : Function.Surjective (fun t : G => y ◇ t) := by
    intro x
    exact ⟨(((y ◇ x) ◇ a) ◇ (x ◇ a)), (h x y a).symm⟩
  have li (y : G) : Function.Injective (fun t : G => y ◇ t) :=
    Finite.injective_iff_surjective.mpr (ls y)
  let d (x y : G) : G := Classical.choose (ls x y)
  have ld1 (x y : G) : x ◇ d x y = y := Classical.choose_spec (ls x y)
  have ld2 (x y : G) : d x (x ◇ y) = y := li x (ld1 x (x ◇ y))
  have p2 (x y z : G) : (x ◇ (((x ◇ y) ◇ z) ◇ (y ◇ z))) = y := by
    exact (h y x z).symm
  have p3 (x y : G) : (x ◇ (d x y)) = y := by
    exact (ld1 x y)
  have p4 (x y : G) : (d x (x ◇ y)) = y := by
    exact (ld2 x y)
  have p12 (x y z : G) : (d x y) = (((x ◇ y) ◇ z) ◇ (y ◇ z)) := by
    exact (((congrArg (fun _t : G => (d x _t)) ((p2 x y z)))).symm).trans ((p4 x (((x ◇ y) ◇ z) ◇ (y ◇ z))))
  have p53 (x y z : G) : (((x ◇ (x ◇ y)) ◇ z) ◇ ((x ◇ y) ◇ z)) = y := by
    exact (((p12 x (x ◇ y) z)).symm).trans ((p4 x y))
  have p72 (x y z : G) : (d (x ◇ y) z) = ((d x y) ◇ (z ◇ (y ◇ z))) := by
    exact ((p12 (x ◇ y) z (y ◇ z))).trans ((congrArg (fun _t : G => (_t ◇ (z ◇ (y ◇ z)))) (((p12 x y z)).symm)))
  have p334 (u x y z : G) : (((x ◇ (x ◇ y)) ◇ ((((x ◇ y) ◇ z) ◇ u) ◇ (z ◇ u))) ◇ z) = y := by
    exact (((congrArg (fun _t : G => (((x ◇ (x ◇ y)) ◇ ((((x ◇ y) ◇ z) ◇ u) ◇ (z ◇ u))) ◇ _t)) ((p2 (x ◇ y) z u)))).symm).trans ((p53 x y ((((x ◇ y) ◇ z) ◇ u) ◇ (z ◇ u))))
  have p335 (x y z : G) : (x ◇ ((y ◇ z) ◇ (z ◇ (x ◇ ((y ◇ z) ◇ x))))) = z := by
    exact (((congrArg (fun _t : G => (x ◇ ((y ◇ z) ◇ (_t ◇ (x ◇ ((y ◇ z) ◇ x)))))) ((p4 y z)))).symm).trans ((((congrArg (fun _t : G => (x ◇ ((y ◇ z) ◇ _t))) ((p72 y (y ◇ z) x)))).symm).trans ((((congrArg (fun _t : G => (_t ◇ ((y ◇ z) ◇ (d (y ◇ (y ◇ z)) x)))) ((p3 (y ◇ (y ◇ z)) x)))).symm).trans ((p53 y z (d (y ◇ (y ◇ z)) x)))))
  have p2072 (x y z : G) : (x ◇ (y ◇ (z ◇ (x ◇ (y ◇ x))))) = z := by
    exact (((congrArg (fun _t : G => (x ◇ (y ◇ (z ◇ (x ◇ (_t ◇ x)))))) ((p334 a a y z)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (_t ◇ (z ◇ (x ◇ ((((a ◇ (a ◇ y)) ◇ ((((a ◇ y) ◇ z) ◇ a) ◇ (z ◇ a))) ◇ z) ◇ x)))))) ((p334 a a y z)))).symm).trans ((p335 x ((a ◇ (a ◇ y)) ◇ ((((a ◇ y) ◇ z) ◇ a) ◇ (z ◇ a))) z)))
  have p2173 (x y : G) : ((x ◇ y) ◇ (x ◇ y)) = (y ◇ y) := by
    exact ((((congrArg (fun _t : G => (y ◇ _t)) ((p2 x y (x ◇ y))))).symm).trans ((p2072 y x ((x ◇ y) ◇ (x ◇ y))))).symm
  have p2223 (x y : G) : (x ◇ x) = y := by
    exact (((p2173 y x)).symm).trans ((((congrArg (fun _t : G => ((y ◇ x) ◇ _t)) ((p2072 x y (y ◇ x))))).symm).trans ((p2072 (y ◇ x) x y)))
  have p2233 (x y z : G) : (x ◇ (y ◇ y)) = z := by
    exact (((congrArg (fun _t : G => (x ◇ _t)) (((p2223 y (((x ◇ z) ◇ a) ◇ (z ◇ a)))).symm))).symm).trans ((p2 x z a))
  exact (p2233 a a a).symm.trans (p2233 a a b)

#print axioms finite_trivial

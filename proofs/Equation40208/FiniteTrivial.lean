import Mathlib.Data.Fintype.Card
import JudgeMagma.Magma

@[reducible] def Equation2 (G : Type _) [Magma G] : Prop := ∀ (x y : G), x = y
@[reducible] def Equation5951 (G : Type _) [Magma G] : Prop := ∀ (x y z : G), x = y ◇ (y ◇ (x ◇ ((z ◇ y) ◇ y)))

theorem finite_trivial (G : Type*) [Magma G] [Finite G] (h : Equation5951 G) : Equation2 G := by
  intro a b
  have ls (y : G) : Function.Surjective (fun t : G => y ◇ t) := by
    intro x
    exact ⟨(y ◇ (x ◇ ((a ◇ y) ◇ y))), (h x y a).symm⟩
  have li (y : G) : Function.Injective (fun t : G => y ◇ t) :=
    Finite.injective_iff_surjective.mpr (ls y)
  let d (x y : G) : G := Classical.choose (ls x y)
  have ld1 (x y : G) : x ◇ d x y = y := Classical.choose_spec (ls x y)
  have ld2 (x y : G) : d x (x ◇ y) = y := li x (ld1 x (x ◇ y))
  have p2 (x y z : G) : (x ◇ (x ◇ (y ◇ ((z ◇ x) ◇ x)))) = y := by
    exact (h y x z).symm
  have p4 (x y : G) : (d x (x ◇ y)) = y := by
    exact (ld2 x y)
  have p8 (x y z : G) : (d x y) = (x ◇ (y ◇ ((z ◇ x) ◇ x))) := by
    exact (((congrArg (fun _t : G => (d x _t)) ((p2 x y z)))).symm).trans ((p4 x (x ◇ (y ◇ ((z ◇ x) ◇ x)))))
  have p16 (x y z : G) : (x ◇ ((x ◇ y) ◇ ((z ◇ x) ◇ x))) = y := by
    exact (((p8 x (x ◇ y) z)).symm).trans ((p4 x y))
  have p17 (x y z : G) : (d x (d x y)) = (y ◇ ((z ◇ x) ◇ x)) := by
    exact (((congrArg (fun _t : G => (d x _t)) (((p8 x y z)).symm))).symm).trans ((p4 x (y ◇ ((z ◇ x) ◇ x))))
  have p29 (u x y z : G) : (d (x ◇ ((y ◇ z) ◇ z)) u) = ((x ◇ ((y ◇ z) ◇ z)) ◇ (u ◇ ((d z x) ◇ (x ◇ ((y ◇ z) ◇ z))))) := by
    exact ((p8 (x ◇ ((y ◇ z) ◇ z)) u z)).trans ((congrArg (fun _t : G => ((x ◇ ((y ◇ z) ◇ z)) ◇ (u ◇ (_t ◇ (x ◇ ((y ◇ z) ◇ z)))))) (((p8 z x y)).symm)))
  have p35 (x y z : G) : (d x y) = ((x ◇ y) ◇ ((z ◇ x) ◇ x)) := by
    exact (((congrArg (fun _t : G => (d x _t)) ((p16 x y z)))).symm).trans ((p4 x ((x ◇ y) ◇ ((z ◇ x) ◇ x))))
  have p40 (x y : G) : (d ((x ◇ y) ◇ y) y) = (((x ◇ y) ◇ y) ◇ ((x ◇ y) ◇ y)) := by
    exact ((p8 ((x ◇ y) ◇ y) y y)).trans ((congrArg (fun _t : G => (((x ◇ y) ◇ y) ◇ _t)) ((p16 y ((x ◇ y) ◇ y) x))))
  have p52 (x y z : G) : (d x (d y (d y x))) = ((z ◇ y) ◇ y) := by
    exact (((congrArg (fun _t : G => (d x _t)) (((p17 y x z)).symm))).symm).trans ((p4 x ((z ◇ y) ◇ y)))
  have p65 (x y z : G) : (d x (y ◇ ((z ◇ x) ◇ x))) = ((z ◇ x) ◇ x) := by
    exact ((((p8 x (y ◇ ((z ◇ x) ◇ x)) z)).trans (((p17 ((z ◇ x) ◇ x) x y)).symm)).trans ((congrArg (fun _t : G => (d ((z ◇ x) ◇ x) _t)) ((p40 z x))))).trans ((p4 ((z ◇ x) ◇ x) ((z ◇ x) ◇ x)))
  have p83 (x y z : G) : ((x ◇ (x ◇ y)) ◇ ((z ◇ x) ◇ x)) = y := by
    exact (((p35 x (x ◇ y) z)).symm).trans ((p4 x y))
  have p93 (u x y z : G) : ((x ◇ y) ◇ y) = (z ◇ ((u ◇ y) ◇ y)) := by
    exact (((p65 y (y ◇ z) x)).symm).trans (((p35 y ((y ◇ z) ◇ ((x ◇ y) ◇ y)) u)).trans ((congrArg (fun _t : G => (_t ◇ ((u ◇ y) ◇ y))) ((p16 y z x)))))
  have p130 (x y z : G) : ((x ◇ y) ◇ y) = ((z ◇ y) ◇ y) := by
    exact (((p4 a ((x ◇ y) ◇ y))).symm).trans ((((congrArg (fun _t : G => (d a _t)) ((p4 y (a ◇ ((x ◇ y) ◇ y)))))).symm).trans ((((congrArg (fun _t : G => (d a (d y _t))) ((p8 y a x)))).symm).trans ((p52 a y z))))
  have p155 (x y z : G) : (d (x ◇ y) ((z ◇ y) ◇ y)) = y := by
    exact (((congrArg (fun _t : G => (d (x ◇ y) _t)) ((p130 x y z)))).symm).trans ((p4 (x ◇ y) y))
  have p326 (u x y z : G) : ((x ◇ ((y ◇ z) ◇ z)) ◇ (((u ◇ z) ◇ z) ◇ ((d z x) ◇ (x ◇ ((y ◇ z) ◇ z))))) = z := by
    exact (((p29 ((u ◇ z) ◇ z) x y z)).symm).trans ((((congrArg (fun _t : G => (d _t ((u ◇ z) ◇ z))) ((p93 y a z x)))).symm).trans ((p155 (a ◇ z) z u)))
  have p328 (x y : G) : ((x ◇ y) ◇ y) = y := by
    exact ((((p326 a a x y)).symm).trans ((((p29 ((a ◇ y) ◇ y) a x y)).symm).trans ((((congrArg (fun _t : G => (d (a ◇ ((x ◇ y) ◇ y)) _t)) (((p93 x a y (a ◇ ((x ◇ y) ◇ y)))).symm))).symm).trans ((p155 a ((x ◇ y) ◇ y) a))))).symm
  have p332 (x y : G) : ((x ◇ y) ◇ x) = y := by
    exact ((((congrArg (fun _t : G => ((x ◇ y) ◇ _t)) ((p328 a x)))).symm).trans ((((congrArg (fun _t : G => ((x ◇ _t) ◇ ((a ◇ x) ◇ x))) ((p328 a y)))).symm).trans ((((congrArg (fun _t : G => ((x ◇ _t) ◇ ((a ◇ x) ◇ x))) (((p93 a a y x)).symm))).symm).trans ((p83 x ((a ◇ y) ◇ y) a))))).trans ((p328 a y))
  have p334 (x y : G) : (x ◇ y) = y := by
    exact (((p332 x (x ◇ y))).symm).trans ((((congrArg (fun _t : G => ((x ◇ (x ◇ y)) ◇ _t)) ((p328 a x)))).symm).trans ((((congrArg (fun _t : G => ((x ◇ (_t ◇ y)) ◇ ((a ◇ x) ◇ x))) ((p328 a x)))).symm).trans ((((congrArg (fun _t : G => ((_t ◇ (((a ◇ x) ◇ x) ◇ y)) ◇ ((a ◇ x) ◇ x))) ((p328 a x)))).symm).trans ((((congrArg (fun _t : G => ((((a ◇ x) ◇ x) ◇ (((a ◇ x) ◇ x) ◇ y)) ◇ _t)) (((p93 a a x (a ◇ ((a ◇ x) ◇ x)))).symm))).symm).trans ((p83 ((a ◇ x) ◇ x) y a))))))
  have p335 (x y : G) : x = y := by
    exact (((p334 x x)).symm).trans ((((congrArg (fun _t : G => (_t ◇ x)) ((p334 a x)))).symm).trans (((((p93 a a x (x ◇ (x ◇ y)))).symm).symm).trans ((p83 x y a))))
  exact (p335 a a).trans (p335 b a).symm

@[reducible] def Equation40208 (G : Type _) [Magma G] : Prop := ∀ (x y z : G), x = (((y ◇ (y ◇ z)) ◇ x) ◇ y) ◇ y

theorem finite_trivial_dual (G : Type*) [Magma G] [Finite G] (h : Equation40208 G) : Equation2 G := by
  let opposite : Magma G := ⟨fun x y => y ◇ x⟩
  have hd : @ Equation5951 G opposite := by
    intro x y z
    exact h x y z
  exact @ finite_trivial G opposite inferInstance hd

#print axioms finite_trivial_dual

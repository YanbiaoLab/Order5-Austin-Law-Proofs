import Mathlib.Data.Fintype.Card
import JudgeMagma.Magma

@[reducible] def Equation2 (G : Type _) [Magma G] : Prop := ∀ (x y : G), x = y
@[reducible] def Equation18212 (G : Type _) [Magma G] : Prop := ∀ (x y z : G), x = (y ◇ y) ◇ (x ◇ ((x ◇ z) ◇ z))

theorem finite_trivial (G : Type*) [Magma G] [Finite G] (h : Equation18212 G) : Equation2 G := by
  intro a b
  have ls (y : G) : Function.Surjective (fun t : G => (y ◇ y) ◇ t) := by
    intro x
    exact ⟨(x ◇ ((x ◇ a) ◇ a)), (h x y a).symm⟩
  have li (y : G) : Function.Injective (fun t : G => (y ◇ y) ◇ t) :=
    Finite.injective_iff_surjective.mpr (ls y)
  let d (x y : G) : G := Classical.choose (ls x y)
  have ld1 (x y : G) : (x ◇ x) ◇ d x y = y := Classical.choose_spec (ls x y)
  have ld2 (x y : G) : d x ((x ◇ x) ◇ y) = y := li x (ld1 x ((x ◇ x) ◇ y))
  have p2 (x y z : G) : ((x ◇ x) ◇ (y ◇ ((y ◇ z) ◇ z))) = y := by
    exact (h y x z).symm
  have p4 (x y : G) : (d x ((x ◇ x) ◇ y)) = y := by
    exact (ld2 x y)
  have p9 (x y z : G) : (d x y) = (y ◇ ((y ◇ z) ◇ z)) := by
    exact (((congrArg (fun _t : G => (d x _t)) ((p2 x y z)))).symm).trans ((p4 x (y ◇ ((y ◇ z) ◇ z))))
  have p16 (x y z : G) : ((x ◇ x) ◇ (d y z)) = z := by
    exact (((congrArg (fun _t : G => ((x ◇ x) ◇ _t)) (((p9 y z a)).symm))).symm).trans ((p2 x z a))
  have p27 (x y z : G) : (d x y) = (d z y) := by
    exact ((p9 x y a)).trans (((p9 z y a)).symm)
  have p28 (x y z : G) : (d x ((y ◇ y) ◇ z)) = z := by
    exact (((p27 y ((y ◇ y) ◇ z) x)).symm).trans ((p4 y z))
  have p35 (x y z : G) : (d x (d y z)) = ((d y z) ◇ z) := by
    exact ((p9 x (d y z) (d y z))).trans ((congrArg (fun _t : G => ((d y z) ◇ _t)) ((p16 (d y z) y z))))
  have p37 (x y z : G) : ((x ◇ x) ◇ y) = ((z ◇ z) ◇ y) := by
    exact (((congrArg (fun _t : G => ((x ◇ x) ◇ _t)) ((p28 a z y)))).symm).trans ((p16 x a ((z ◇ z) ◇ y)))
  have p54 (x y z : G) : (d x ((d y z) ◇ z)) = (((d y z) ◇ z) ◇ (d y z)) := by
    exact ((((congrArg (fun _t : G => (d x _t)) ((p35 a y z)))).symm).trans ((p35 x a (d y z)))).trans ((congrArg (fun _t : G => (_t ◇ (d y z))) ((p35 a y z))))
  have p56 (u x y z : G) : ((x ◇ x) ◇ ((y ◇ y) ◇ (((z ◇ z) ◇ u) ◇ u))) = (y ◇ y) := by
    exact (((congrArg (fun _t : G => ((x ◇ x) ◇ ((y ◇ y) ◇ (_t ◇ u)))) ((p37 y u z)))).symm).trans ((p2 x (y ◇ y) u))
  have p58 (x y : G) : (x ◇ x) = (y ◇ y) := by
    exact (((p56 a a x y)).symm).trans ((((congrArg (fun _t : G => ((a ◇ a) ◇ _t)) ((p37 y (((y ◇ y) ◇ a) ◇ a) x)))).symm).trans ((p2 a (y ◇ y) a)))
  have p73 (x y z : G) : (d x (y ◇ y)) = (z ◇ z) := by
    exact (((congrArg (fun _t : G => (d x _t)) ((p58 (z ◇ z) y)))).symm).trans ((p28 x z (z ◇ z)))
  have p82 (u x y z : G) : ((d x (y ◇ y)) ◇ (d z u)) = u := by
    exact (((congrArg (fun _t : G => (_t ◇ (d z u))) (((p73 x y a)).symm))).symm).trans ((p16 a z u))
  have p83 (u x y z : G) : (d x ((d y (z ◇ z)) ◇ u)) = u := by
    exact (((congrArg (fun _t : G => (d x (_t ◇ u))) (((p73 y z a)).symm))).symm).trans ((p28 x a u))
  have p128 (u x y z : G) : (((d x (y ◇ y)) ◇ (y ◇ y)) ◇ (d z u)) = u := by
    exact (((congrArg (fun _t : G => (_t ◇ (d z u))) ((p35 a x (y ◇ y))))).symm).trans ((((congrArg (fun _t : G => ((d a _t) ◇ (d z u))) (((p73 x y a)).symm))).symm).trans ((p82 u a a z)))
  have p160 (x y z : G) : (((d x (y ◇ y)) ◇ z) ◇ z) = (y ◇ y) := by
    exact ((((p128 (y ◇ y) x y x)).symm).trans ((((p54 a x (y ◇ y))).symm).trans ((((congrArg (fun _t : G => (d a _t)) ((p35 a x (y ◇ y))))).symm).trans ((((congrArg (fun _t : G => (d a _t)) (((p9 a (d x (y ◇ y)) z)).symm))).symm).trans ((p83 (((d x (y ◇ y)) ◇ z) ◇ z) a x y)))))).symm
  have p349 (x y z : G) : (x ◇ (d y x)) = (z ◇ z) := by
    exact (((congrArg (fun _t : G => (_t ◇ (d y x))) ((p82 x a z y)))).symm).trans ((p160 a z (d y x)))
  have p354 (x y : G) : ((x ◇ x) ◇ (y ◇ y)) = y := by
    exact (((congrArg (fun _t : G => ((x ◇ x) ◇ (y ◇ _t))) ((p16 a a y)))).symm).trans ((((congrArg (fun _t : G => ((x ◇ x) ◇ (y ◇ (_t ◇ (d a y))))) ((p349 y a a)))).symm).trans ((p2 x y (d a y))))
  have p361 (x y : G) : (d x y) = (y ◇ y) := by
    exact (((p9 x y (d a y))).trans ((congrArg (fun _t : G => (y ◇ (_t ◇ (d a y)))) ((p349 y a a))))).trans ((congrArg (fun _t : G => (y ◇ _t)) ((p16 a a y))))
  have p366 (x y : G) : x = y := by
    exact (((((p354 x x)).symm).trans ((((p361 a (x ◇ x))).symm).trans ((((congrArg (fun _t : G => (d a _t)) ((p349 (y ◇ y) a x)))).symm).trans ((p28 a y (d a (y ◇ y))))))).trans ((p361 a (y ◇ y)))).trans ((p354 y y))
  exact (p366 a a).trans (p366 b a).symm

@[reducible] def Equation27859 (G : Type _) [Magma G] : Prop := ∀ (x y z : G), x = ((y ◇ (y ◇ x)) ◇ x) ◇ (z ◇ z)

theorem finite_trivial_dual (G : Type*) [Magma G] [Finite G] (h : Equation27859 G) : Equation2 G := by
  let opposite : Magma G := ⟨fun x y => y ◇ x⟩
  have hd : @ Equation18212 G opposite := by
    intro x y z
    exact h x z y
  exact @ finite_trivial G opposite inferInstance hd

#print axioms finite_trivial_dual

import Mathlib.Data.Fintype.Card
import JudgeMagma.Magma

@[reducible] def Equation2 (G : Type _) [Magma G] : Prop := ∀ (x y : G), x = y
@[reducible] def Equation10218 (G : Type _) [Magma G] : Prop := ∀ (x y z : G), x = y ◇ ((x ◇ y) ◇ ((z ◇ x) ◇ y))

theorem finite_trivial (G : Type*) [Magma G] [Finite G] (h : Equation10218 G) : Equation2 G := by
  intro a b
  have ls (y : G) : Function.Surjective (fun t : G => y ◇ t) := by
    intro x
    exact ⟨((x ◇ y) ◇ ((a ◇ x) ◇ y)), (h x y a).symm⟩
  have li (y : G) : Function.Injective (fun t : G => y ◇ t) :=
    Finite.injective_iff_surjective.mpr (ls y)
  let d (x y : G) : G := Classical.choose (ls x y)
  have ld1 (x y : G) : x ◇ d x y = y := Classical.choose_spec (ls x y)
  have ld2 (x y : G) : d x (x ◇ y) = y := li x (ld1 x (x ◇ y))
  have p2 (x y z : G) : (x ◇ ((y ◇ x) ◇ ((z ◇ y) ◇ x))) = y := by
    exact (h y x z).symm
  have p3 (x y : G) : (x ◇ (d x y)) = y := by
    exact (ld1 x y)
  have p4 (x y : G) : (d x (x ◇ y)) = y := by
    exact (ld2 x y)
  have p6 (u x y z : G) : (((x ◇ y) ◇ ((z ◇ x) ◇ y)) ◇ (x ◇ ((u ◇ y) ◇ ((x ◇ y) ◇ ((z ◇ x) ◇ y))))) = y := by
    exact (((congrArg (fun _t : G => (((x ◇ y) ◇ ((z ◇ x) ◇ y)) ◇ (_t ◇ ((u ◇ y) ◇ ((x ◇ y) ◇ ((z ◇ x) ◇ y)))))) ((p2 y x z)))).symm).trans ((p2 ((x ◇ y) ◇ ((z ◇ x) ◇ y)) y u))
  have p7 (u x y z : G) : (x ◇ ((((y ◇ z) ◇ ((u ◇ y) ◇ z)) ◇ x) ◇ (y ◇ x))) = ((y ◇ z) ◇ ((u ◇ y) ◇ z)) := by
    exact (((congrArg (fun _t : G => (x ◇ ((((y ◇ z) ◇ ((u ◇ y) ◇ z)) ◇ x) ◇ (_t ◇ x)))) ((p2 z y u)))).symm).trans ((p2 x ((y ◇ z) ◇ ((u ◇ y) ◇ z)) z))
  have p10 (x y z : G) : (x ◇ (((d y z) ◇ x) ◇ (z ◇ x))) = (d y z) := by
    exact (((congrArg (fun _t : G => (x ◇ (((d y z) ◇ x) ◇ (_t ◇ x)))) ((p3 y z)))).symm).trans ((p2 x (d y z) y))
  have p12 (x y z : G) : (d x y) = ((y ◇ x) ◇ ((z ◇ y) ◇ x)) := by
    exact (((congrArg (fun _t : G => (d x _t)) ((p2 x y z)))).symm).trans ((p4 x ((y ◇ x) ◇ ((z ◇ y) ◇ x))))
  have p21 (u x y z : G) : (((x ◇ (d (y ◇ x) z)) ◇ z) ◇ (x ◇ ((u ◇ (d (y ◇ x) z)) ◇ ((x ◇ (d (y ◇ x) z)) ◇ z)))) = (d (y ◇ x) z) := by
    exact (((congrArg (fun _t : G => (((x ◇ (d (y ◇ x) z)) ◇ z) ◇ (x ◇ ((u ◇ (d (y ◇ x) z)) ◇ ((x ◇ (d (y ◇ x) z)) ◇ _t))))) ((p3 (y ◇ x) z)))).symm).trans ((((congrArg (fun _t : G => (((x ◇ (d (y ◇ x) z)) ◇ _t) ◇ (x ◇ ((u ◇ (d (y ◇ x) z)) ◇ ((x ◇ (d (y ◇ x) z)) ◇ ((y ◇ x) ◇ (d (y ◇ x) z))))))) ((p3 (y ◇ x) z)))).symm).trans ((p6 u x (d (y ◇ x) z) y)))
  have p35 (x y z : G) : (((x ◇ y) ◇ x) ◇ ((z ◇ (x ◇ y)) ◇ x)) = y := by
    exact (((p12 x (x ◇ y) z)).symm).trans ((p4 x y))
  have p163 (x y z : G) : (d ((x ◇ y) ◇ x) y) = ((z ◇ (x ◇ y)) ◇ x) := by
    exact (((congrArg (fun _t : G => (d ((x ◇ y) ◇ x) _t)) ((p35 x y z)))).symm).trans ((p4 ((x ◇ y) ◇ x) ((z ◇ (x ◇ y)) ◇ x)))
  have p190 (x y z : G) : (x ◇ ((y ◇ x) ◇ ((d ((y ◇ z) ◇ y) z) ◇ x))) = y := by
    exact (((congrArg (fun _t : G => (x ◇ ((y ◇ x) ◇ (_t ◇ x)))) (((p163 y z a)).symm))).symm).trans ((p2 x y (a ◇ (y ◇ z))))
  have p191 (u x y z : G) : ((x ◇ y) ◇ z) = ((u ◇ y) ◇ z) := by
    exact ((((p4 (y ◇ z) ((x ◇ y) ◇ z))).symm).trans ((((congrArg (fun _t : G => (d (_t ◇ z) ((y ◇ z) ◇ ((x ◇ y) ◇ z)))) ((p2 z y x)))).symm).trans ((p163 z ((y ◇ z) ◇ ((x ◇ y) ◇ z)) u)))).trans ((congrArg (fun _t : G => ((u ◇ _t) ◇ z)) ((p2 z y x))))
  have p209 (u x y z : G) : (x ◇ (((d y (z ◇ (x ◇ u))) ◇ x) ◇ (d ((x ◇ u) ◇ x) u))) = (d y (z ◇ (x ◇ u))) := by
    exact (((congrArg (fun _t : G => (x ◇ (((d y (z ◇ (x ◇ u))) ◇ x) ◇ _t))) (((p163 x u z)).symm))).symm).trans ((p10 x y (z ◇ (x ◇ u))))
  have p210 (u x y z : G) : ((x ◇ (d y z)) ◇ u) = (z ◇ u) := by
    exact (((((p4 ((d y z) ◇ u) (z ◇ u))).symm).trans ((((congrArg (fun _t : G => (d (_t ◇ u) (((d y z) ◇ u) ◇ (z ◇ u)))) ((p10 u y z)))).symm).trans ((p163 u (((d y z) ◇ u) ◇ (z ◇ u)) x)))).trans ((congrArg (fun _t : G => ((x ◇ _t) ◇ u)) ((p10 u y z))))).symm
  have p219 (u w x y z : G) : (x ◇ (((((y ◇ (x ◇ z)) ◇ u) ◇ ((w ◇ (y ◇ (x ◇ z))) ◇ u)) ◇ x) ◇ (d ((x ◇ z) ◇ x) z))) = (((y ◇ (x ◇ z)) ◇ u) ◇ ((w ◇ (y ◇ (x ◇ z))) ◇ u)) := by
    exact (((congrArg (fun _t : G => (x ◇ (((((y ◇ (x ◇ z)) ◇ u) ◇ ((w ◇ (y ◇ (x ◇ z))) ◇ u)) ◇ x) ◇ _t))) (((p163 x z y)).symm))).symm).trans ((p7 w x (y ◇ (x ◇ z)) u))
  have p251 (x y z : G) : (d (x ◇ y) z) = ((z ◇ z) ◇ (y ◇ (z ◇ (z ◇ z)))) := by
    exact ((((congrArg (fun _t : G => ((z ◇ z) ◇ (y ◇ _t))) ((p210 (z ◇ z) a (x ◇ y) z)))).symm).trans ((((congrArg (fun _t : G => ((z ◇ z) ◇ (y ◇ ((a ◇ (d (x ◇ y) z)) ◇ _t)))) ((p210 z y (x ◇ y) z)))).symm).trans ((((congrArg (fun _t : G => (_t ◇ (y ◇ ((a ◇ (d (x ◇ y) z)) ◇ ((y ◇ (d (x ◇ y) z)) ◇ z))))) ((p210 z y (x ◇ y) z)))).symm).trans ((p21 a y x z))))).symm
  have p273 (u w x y z : G) : (x ◇ (((((y ◇ (x ◇ z)) ◇ u) ◇ ((w ◇ (y ◇ (x ◇ z))) ◇ u)) ◇ x) ◇ ((z ◇ z) ◇ (x ◇ (z ◇ (z ◇ z)))))) = (((y ◇ (x ◇ z)) ◇ u) ◇ ((w ◇ (y ◇ (x ◇ z))) ◇ u)) := by
    exact (((congrArg (fun _t : G => (x ◇ (((((y ◇ (x ◇ z)) ◇ u) ◇ ((w ◇ (y ◇ (x ◇ z))) ◇ u)) ◇ x) ◇ _t))) ((p251 (x ◇ z) x z)))).symm).trans ((p219 u w x y z))
  have p281 (u x y z : G) : (x ◇ (((d y (z ◇ (x ◇ u))) ◇ x) ◇ ((u ◇ u) ◇ (x ◇ (u ◇ (u ◇ u)))))) = (d y (z ◇ (x ◇ u))) := by
    exact (((congrArg (fun _t : G => (x ◇ (((d y (z ◇ (x ◇ u))) ◇ x) ◇ _t))) ((p251 (x ◇ u) x u)))).symm).trans ((p209 u x y z))
  have p296 (x y z : G) : (x ◇ ((y ◇ x) ◇ (((z ◇ z) ◇ (y ◇ (z ◇ (z ◇ z)))) ◇ x))) = y := by
    exact (((congrArg (fun _t : G => (x ◇ ((y ◇ x) ◇ (_t ◇ x)))) ((p251 (y ◇ z) y z)))).symm).trans ((p190 x y z))
  have p343 (u x y z : G) : (x ◇ ((y ◇ x) ◇ ((z ◇ u) ◇ x))) = u := by
    exact (((congrArg (fun _t : G => (x ◇ _t)) ((p191 y u x ((z ◇ u) ◇ x))))).symm).trans ((p2 x u z))
  have p361 (x y z : G) : (d x (y ◇ z)) = z := by
    exact ((((p343 z a (d x (y ◇ z)) a)).symm).trans ((((congrArg (fun _t : G => (a ◇ (((d x (y ◇ z)) ◇ a) ◇ _t))) ((p191 a y z a)))).symm).trans ((p10 a x (y ◇ z))))).symm
  have p374 (x y : G) : (x ◇ (y ◇ (y ◇ y))) = x := by
    exact (((p343 (x ◇ (y ◇ (y ◇ y))) a x (y ◇ y))).symm).trans ((p296 a x y))
  have p383 (x y : G) : (x ◇ y) = y := by
    exact (((((p343 y x (x ◇ y) y)).symm).trans ((((congrArg (fun _t : G => (x ◇ (((x ◇ y) ◇ x) ◇ ((y ◇ y) ◇ _t)))) ((p374 x y)))).symm).trans ((((congrArg (fun _t : G => (x ◇ ((_t ◇ x) ◇ ((y ◇ y) ◇ (x ◇ (y ◇ (y ◇ y))))))) ((p361 a a (x ◇ y))))).symm).trans ((p281 y x a a))))).trans ((p361 a a (x ◇ y)))).symm
  have p384 (x y : G) : x = y := by
    exact (((((((((((p383 a x)).symm).trans ((((congrArg (fun _t : G => (a ◇ _t)) ((p383 a x)))).symm).trans ((((congrArg (fun _t : G => (a ◇ (a ◇ _t))) ((p383 x x)))).symm).trans ((((congrArg (fun _t : G => (a ◇ (a ◇ (x ◇ _t)))) ((p383 a x)))).symm).trans ((((congrArg (fun _t : G => (a ◇ (a ◇ (x ◇ (a ◇ _t))))) ((p383 x x)))).symm).trans ((((congrArg (fun _t : G => (a ◇ (a ◇ (x ◇ (a ◇ (x ◇ _t)))))) ((p383 x x)))).symm).trans ((((congrArg (fun _t : G => (a ◇ (a ◇ (_t ◇ (a ◇ (x ◇ (x ◇ x))))))) ((p383 x x)))).symm).trans ((((congrArg (fun _t : G => (a ◇ (_t ◇ ((x ◇ x) ◇ (a ◇ (x ◇ (x ◇ x))))))) ((p383 y a)))).symm).trans ((((congrArg (fun _t : G => (a ◇ ((_t ◇ a) ◇ ((x ◇ x) ◇ (a ◇ (x ◇ (x ◇ x))))))) ((p383 y y)))).symm).trans ((((congrArg (fun _t : G => (a ◇ (((y ◇ _t) ◇ a) ◇ ((x ◇ x) ◇ (a ◇ (x ◇ (x ◇ x))))))) ((p383 x y)))).symm).trans ((((congrArg (fun _t : G => (a ◇ (((y ◇ (_t ◇ y)) ◇ a) ◇ ((x ◇ x) ◇ (a ◇ (x ◇ (x ◇ x))))))) ((p383 a x)))).symm).trans ((((congrArg (fun _t : G => (a ◇ (((y ◇ ((a ◇ _t) ◇ y)) ◇ a) ◇ ((x ◇ x) ◇ (a ◇ (x ◇ (x ◇ x))))))) ((p383 a x)))).symm).trans ((((congrArg (fun _t : G => (a ◇ (((y ◇ ((a ◇ (a ◇ _t)) ◇ y)) ◇ a) ◇ ((x ◇ x) ◇ (a ◇ (x ◇ (x ◇ x))))))) ((p383 a x)))).symm).trans ((((congrArg (fun _t : G => (a ◇ (((_t ◇ ((a ◇ (a ◇ (a ◇ x))) ◇ y)) ◇ a) ◇ ((x ◇ x) ◇ (a ◇ (x ◇ (x ◇ x))))))) ((p383 x y)))).symm).trans ((((congrArg (fun _t : G => (a ◇ ((((_t ◇ y) ◇ ((a ◇ (a ◇ (a ◇ x))) ◇ y)) ◇ a) ◇ ((x ◇ x) ◇ (a ◇ (x ◇ (x ◇ x))))))) ((p383 a x)))).symm).trans ((((congrArg (fun _t : G => (a ◇ (((((a ◇ _t) ◇ y) ◇ ((a ◇ (a ◇ (a ◇ x))) ◇ y)) ◇ a) ◇ ((x ◇ x) ◇ (a ◇ (x ◇ (x ◇ x))))))) ((p383 a x)))).symm).trans ((p273 y a a a x)))))))))))))))))).trans ((congrArg (fun _t : G => (((a ◇ _t) ◇ y) ◇ ((a ◇ (a ◇ (a ◇ x))) ◇ y))) ((p383 a x))))).trans ((congrArg (fun _t : G => ((_t ◇ y) ◇ ((a ◇ (a ◇ (a ◇ x))) ◇ y))) ((p383 a x))))).trans ((congrArg (fun _t : G => (_t ◇ ((a ◇ (a ◇ (a ◇ x))) ◇ y))) ((p383 x y))))).trans ((congrArg (fun _t : G => (y ◇ ((a ◇ (a ◇ _t)) ◇ y))) ((p383 a x))))).trans ((congrArg (fun _t : G => (y ◇ ((a ◇ _t) ◇ y))) ((p383 a x))))).trans ((congrArg (fun _t : G => (y ◇ (_t ◇ y))) ((p383 a x))))).trans ((congrArg (fun _t : G => (y ◇ _t)) ((p383 x y))))).trans ((p383 y y))
  exact (p384 a a).trans (p384 b a).symm

#print axioms finite_trivial

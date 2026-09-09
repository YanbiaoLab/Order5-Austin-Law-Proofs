import Mathlib.Data.Fintype.Card
import JudgeMagma.Magma

@[reducible] def Equation2 (G : Type _) [Magma G] : Prop := ∀ (x y : G), x = y
@[reducible] def Equation5833 (G : Type _) [Magma G] : Prop := ∀ (x y z : G), x = y ◇ (x ◇ (y ◇ ((z ◇ x) ◇ y)))

theorem finite_trivial (G : Type*) [Magma G] [Finite G] (h : Equation5833 G) : Equation2 G := by
  intro a b
  have ls (y : G) : Function.Surjective (fun t : G => y ◇ t) := by
    intro x
    exact ⟨(x ◇ (y ◇ ((a ◇ x) ◇ y))), (h x y a).symm⟩
  have li (y : G) : Function.Injective (fun t : G => y ◇ t) :=
    Finite.injective_iff_surjective.mpr (ls y)
  let d (x y : G) : G := Classical.choose (ls x y)
  have ld1 (x y : G) : x ◇ d x y = y := Classical.choose_spec (ls x y)
  have ld2 (x y : G) : d x (x ◇ y) = y := li x (ld1 x (x ◇ y))
  have p2 (x y z : G) : (x ◇ (y ◇ (x ◇ ((z ◇ y) ◇ x)))) = y := by
    exact (h y x z).symm
  have p3 (x y : G) : (x ◇ (d x y)) = y := by
    exact (ld1 x y)
  have p4 (x y : G) : (d x (x ◇ y)) = y := by
    exact (ld2 x y)
  have p7 (u x y z : G) : ((x ◇ ((y ◇ z) ◇ ((u ◇ x) ◇ (y ◇ z)))) ◇ (z ◇ ((x ◇ ((y ◇ z) ◇ ((u ◇ x) ◇ (y ◇ z)))) ◇ x))) = z := by
    exact (((congrArg (fun _t : G => ((x ◇ ((y ◇ z) ◇ ((u ◇ x) ◇ (y ◇ z)))) ◇ (z ◇ ((x ◇ ((y ◇ z) ◇ ((u ◇ x) ◇ (y ◇ z)))) ◇ _t)))) ((p2 (y ◇ z) x u)))).symm).trans ((p2 (x ◇ ((y ◇ z) ◇ ((u ◇ x) ◇ (y ◇ z)))) z y))
  have p9 (x y z : G) : ((d (x ◇ y) z) ◇ (y ◇ ((d (x ◇ y) z) ◇ z))) = y := by
    exact (((congrArg (fun _t : G => ((d (x ◇ y) z) ◇ (y ◇ ((d (x ◇ y) z) ◇ _t)))) ((p3 (x ◇ y) z)))).symm).trans ((p2 (d (x ◇ y) z) y x))
  have p10 (x y z : G) : (d x y) = (y ◇ (x ◇ ((z ◇ y) ◇ x))) := by
    exact (((congrArg (fun _t : G => (d x _t)) ((p2 x y z)))).symm).trans ((p4 x (y ◇ (x ◇ ((z ◇ y) ◇ x)))))
  have p25 (x y z : G) : (d x (d y z)) = ((d y z) ◇ (x ◇ (z ◇ x))) := by
    exact ((p10 x (d y z) y)).trans ((congrArg (fun _t : G => ((d y z) ◇ (x ◇ (_t ◇ x)))) ((p3 y z))))
  have p27 (x y z : G) : ((x ◇ y) ◇ (x ◇ ((z ◇ (x ◇ y)) ◇ x))) = y := by
    exact (((p10 x (x ◇ y) z)).symm).trans ((p4 x y))
  have p28 (x y z : G) : ((d x y) ◇ (y ◇ (y ◇ y))) = (x ◇ ((z ◇ y) ◇ x)) := by
    exact (((p25 y x y)).symm).trans ((((congrArg (fun _t : G => (d y _t)) (((p10 x y z)).symm))).symm).trans ((p4 y (x ◇ ((z ◇ y) ◇ x)))))
  have p56 (x y z : G) : (d (x ◇ y) y) = (x ◇ ((z ◇ (x ◇ y)) ◇ x)) := by
    exact (((congrArg (fun _t : G => (d (x ◇ y) _t)) ((p27 x y z)))).symm).trans ((p4 (x ◇ y) (x ◇ ((z ◇ (x ◇ y)) ◇ x))))
  have p96 (x y z : G) : ((x ◇ ((y ◇ ((z ◇ (y ◇ x)) ◇ y)) ◇ x)) ◇ (((z ◇ (y ◇ x)) ◇ y) ◇ ((x ◇ ((y ◇ ((z ◇ (y ◇ x)) ◇ y)) ◇ x)) ◇ x))) = ((z ◇ (y ◇ x)) ◇ y) := by
    exact (((congrArg (fun _t : G => ((x ◇ ((y ◇ ((z ◇ (y ◇ x)) ◇ y)) ◇ x)) ◇ (((z ◇ (y ◇ x)) ◇ y) ◇ ((x ◇ ((y ◇ ((z ◇ (y ◇ x)) ◇ y)) ◇ _t)) ◇ x)))) ((p27 y x z)))).symm).trans ((((congrArg (fun _t : G => ((x ◇ ((y ◇ ((z ◇ (y ◇ x)) ◇ y)) ◇ _t)) ◇ (((z ◇ (y ◇ x)) ◇ y) ◇ ((x ◇ ((y ◇ ((z ◇ (y ◇ x)) ◇ y)) ◇ ((y ◇ x) ◇ (y ◇ ((z ◇ (y ◇ x)) ◇ y))))) ◇ x)))) ((p27 y x z)))).symm).trans ((p7 y x y ((z ◇ (y ◇ x)) ◇ y))))
  have p101 (u x y z : G) : (x ◇ ((y ◇ z) ◇ x)) = (x ◇ ((u ◇ z) ◇ x)) := by
    exact ((((p4 z (x ◇ ((y ◇ z) ◇ x)))).symm).trans ((((congrArg (fun _t : G => (d _t (z ◇ (x ◇ ((y ◇ z) ◇ x))))) ((p2 x z y)))).symm).trans ((p56 x (z ◇ (x ◇ ((y ◇ z) ◇ x))) u)))).trans ((congrArg (fun _t : G => (x ◇ ((u ◇ _t) ◇ x))) ((p2 x z y))))
  have p138 (u x y z : G) : (d (d (x ◇ y) y) ((z ◇ (x ◇ y)) ◇ x)) = (x ◇ ((u ◇ (x ◇ ((z ◇ (x ◇ y)) ◇ x))) ◇ x)) := by
    exact (((congrArg (fun _t : G => (d _t ((z ◇ (x ◇ y)) ◇ x))) (((p56 x y z)).symm))).symm).trans ((p56 x ((z ◇ (x ◇ y)) ◇ x) u))
  have p143 (u x y z : G) : ((x ◇ y) ◇ z) = ((u ◇ y) ◇ z) := by
    exact (((p4 z ((x ◇ y) ◇ z))).symm).trans ((((congrArg (fun _t : G => (d z _t)) ((p101 x z u y)))).symm).trans ((p4 z ((u ◇ y) ◇ z))))
  have p165 (u w x y z : G) : (x ◇ ((y ◇ (z ◇ ((u ◇ (z ◇ w)) ◇ z))) ◇ x)) = (x ◇ (w ◇ x)) := by
    exact ((((congrArg (fun _t : G => (x ◇ (_t ◇ x))) ((p27 z w u)))).symm).trans ((p101 y x (z ◇ w) (z ◇ ((u ◇ (z ◇ w)) ◇ z))))).symm
  have p185 (x y z : G) : (d (d (x ◇ y) y) ((z ◇ (x ◇ y)) ◇ x)) = (x ◇ (y ◇ x)) := by
    exact ((p138 a x y z)).trans ((p165 z y x a x))
  have p188 (u w x y z : G) : ((x ◇ y) ◇ (z ◇ ((u ◇ y) ◇ ((w ◇ z) ◇ (u ◇ y))))) = z := by
    exact (((p143 x u y (z ◇ ((u ◇ y) ◇ ((w ◇ z) ◇ (u ◇ y)))))).symm).trans ((p2 (u ◇ y) z w))
  have p190 (u x y z : G) : ((x ◇ y) ◇ (d (z ◇ y) u)) = u := by
    exact (((p143 x z y (d (z ◇ y) u))).symm).trans ((p3 (z ◇ y) u))
  have p192 (u x y z : G) : (d (x ◇ y) ((z ◇ y) ◇ u)) = u := by
    exact (((congrArg (fun _t : G => (d (x ◇ y) _t)) ((p143 z x y u)))).symm).trans ((p4 (x ◇ y) u))
  have p210 (u x y z : G) : ((x ◇ y) ◇ (z ◇ ((u ◇ (z ◇ y)) ◇ z))) = y := by
    exact (((p143 x z y (z ◇ ((u ◇ (z ◇ y)) ◇ z)))).symm).trans ((p27 z y u))
  have p222 (u x y z : G) : (d (x ◇ y) z) = (d (u ◇ y) z) := by
    exact (((congrArg (fun _t : G => (d (x ◇ y) _t)) ((p190 z x y u)))).symm).trans ((p4 (x ◇ y) (d (u ◇ y) z)))
  have p238 (x y z : G) : ((x ◇ ((y ◇ (x ◇ z)) ◇ x)) ◇ (z ◇ ((d (x ◇ z) z) ◇ z))) = z := by
    exact (((congrArg (fun _t : G => (_t ◇ (z ◇ ((d (x ◇ z) z) ◇ z)))) ((p56 x z y)))).symm).trans ((p9 x z z))
  have p282 (u x y z : G) : (d (x ◇ y) y) = (z ◇ ((u ◇ (z ◇ y)) ◇ z)) := by
    exact (((p222 x z y y)).symm).trans ((p56 z y u))
  have p377 (u w x y z : G) : (d x ((y ◇ (z ◇ u)) ◇ z)) = (((y ◇ (z ◇ u)) ◇ z) ◇ (x ◇ ((d (w ◇ u) u) ◇ x))) := by
    exact ((p10 x ((y ◇ (z ◇ u)) ◇ z) z)).trans ((congrArg (fun _t : G => (((y ◇ (z ◇ u)) ◇ z) ◇ (x ◇ (_t ◇ x)))) (((p282 y w u z)).symm)))
  have p407 (u v5 w x y z : G) : (d (d (x ◇ y) y) ((z ◇ (u ◇ y)) ◇ u)) = (w ◇ ((v5 ◇ (w ◇ ((z ◇ (u ◇ y)) ◇ u))) ◇ w)) := by
    exact (((congrArg (fun _t : G => (d _t ((z ◇ (u ◇ y)) ◇ u))) (((p282 z x y u)).symm))).symm).trans ((p282 v5 u ((z ◇ (u ◇ y)) ◇ u) w))
  have p512 (u x y z : G) : (d ((x ◇ y) ◇ (z ◇ u)) u) = (u ◇ (((x ◇ y) ◇ (z ◇ u)) ◇ ((d (z ◇ u) y) ◇ (y ◇ (y ◇ y))))) := by
    exact ((p10 ((x ◇ y) ◇ (z ◇ u)) u z)).trans ((congrArg (fun _t : G => (u ◇ (((x ◇ y) ◇ (z ◇ u)) ◇ _t))) (((p28 (z ◇ u) y x)).symm)))
  have p552 (x y : G) : ((x ◇ (y ◇ x)) ◇ (x ◇ (x ◇ x))) = (y ◇ x) := by
    exact (((congrArg (fun _t : G => ((x ◇ _t) ◇ (x ◇ (x ◇ x)))) ((p188 (y ◇ x) (y ◇ x) (a ◇ ((y ◇ x) ◇ (y ◇ x))) (y ◇ x) (y ◇ x))))).symm).trans ((((congrArg (fun _t : G => ((x ◇ (((a ◇ ((y ◇ x) ◇ (y ◇ x))) ◇ (y ◇ x)) ◇ (_t ◇ (((y ◇ x) ◇ (y ◇ x)) ◇ (((y ◇ x) ◇ (y ◇ x)) ◇ ((y ◇ x) ◇ (y ◇ x))))))) ◇ (x ◇ (x ◇ x)))) ((p4 (y ◇ x) (y ◇ x))))).symm).trans ((((congrArg (fun _t : G => (_t ◇ (x ◇ (x ◇ x)))) ((p512 x a ((y ◇ x) ◇ (y ◇ x)) y)))).symm).trans (((((p28 ((a ◇ ((y ◇ x) ◇ (y ◇ x))) ◇ (y ◇ x)) x y)).symm).symm).trans ((p210 a (a ◇ ((y ◇ x) ◇ (y ◇ x))) (y ◇ x) (y ◇ x))))))
  have p557 (u w x y z : G) : (d ((d x y) ◇ (y ◇ (y ◇ y))) ((z ◇ y) ◇ x)) = (u ◇ ((w ◇ (u ◇ ((z ◇ y) ◇ x))) ◇ u)) := by
    exact (((congrArg (fun _t : G => (d _t ((z ◇ y) ◇ x))) (((p28 x y z)).symm))).symm).trans ((p282 w x ((z ◇ y) ◇ x) u))
  have p597 (u x y z : G) : (d (x ◇ (y ◇ (y ◇ y))) ((z ◇ y) ◇ u)) = u := by
    exact (((congrArg (fun _t : G => (d (x ◇ (y ◇ (y ◇ y))) (_t ◇ u))) ((p552 y z)))).symm).trans ((p192 u x (y ◇ (y ◇ y)) (y ◇ (z ◇ y))))
  have p609 (x y : G) : (d (x ◇ y) y) = ((y ◇ (y ◇ y)) ◇ ((y ◇ (y ◇ y)) ◇ y)) := by
    exact ((p282 y x y (y ◇ (y ◇ y)))).trans ((congrArg (fun _t : G => ((y ◇ (y ◇ y)) ◇ _t)) ((p552 y (y ◇ (y ◇ y))))))
  have p623 (u w x y z : G) : (x ◇ ((y ◇ (x ◇ ((z ◇ u) ◇ w))) ◇ x)) = w := by
    exact ((((p597 w (d w u) u z)).symm).trans ((p557 x y w u z))).symm
  have p650 (x y z : G) : (d ((x ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ x)) ((y ◇ (z ◇ x)) ◇ z)) = z := by
    exact ((((congrArg (fun _t : G => (d _t ((y ◇ (z ◇ x)) ◇ z))) ((p609 a x)))).symm).trans ((p407 z a a a x y))).trans ((p623 (z ◇ x) z a a y))
  have p668 (u x y z : G) : (d x ((y ◇ (z ◇ u)) ◇ z)) = (((y ◇ (z ◇ u)) ◇ z) ◇ (x ◇ (((u ◇ (u ◇ u)) ◇ ((u ◇ (u ◇ u)) ◇ u)) ◇ x))) := by
    exact ((p377 u a x y z)).trans ((congrArg (fun _t : G => (((y ◇ (z ◇ u)) ◇ z) ◇ (x ◇ (_t ◇ x)))) ((p609 a u))))
  have p675 (x y z : G) : ((x ◇ ((y ◇ (x ◇ z)) ◇ x)) ◇ (z ◇ (((z ◇ (z ◇ z)) ◇ ((z ◇ (z ◇ z)) ◇ z)) ◇ z))) = z := by
    exact (((congrArg (fun _t : G => ((x ◇ ((y ◇ (x ◇ z)) ◇ x)) ◇ (z ◇ (_t ◇ z)))) ((p609 x z)))).symm).trans ((p238 x y z))
  have p676 (x y z : G) : (((x ◇ (y ◇ z)) ◇ y) ◇ (((z ◇ (z ◇ z)) ◇ ((z ◇ (z ◇ z)) ◇ z)) ◇ (((z ◇ (z ◇ z)) ◇ ((z ◇ (z ◇ z)) ◇ z)) ◇ ((z ◇ (z ◇ z)) ◇ ((z ◇ (z ◇ z)) ◇ z))))) = (y ◇ (z ◇ y)) := by
    exact (((p668 z ((z ◇ (z ◇ z)) ◇ ((z ◇ (z ◇ z)) ◇ z)) x y)).symm).trans ((((congrArg (fun _t : G => (d _t ((x ◇ (y ◇ z)) ◇ y))) ((p609 y z)))).symm).trans ((p185 y z x)))
  have p693 (x y : G) : (x ◇ (y ◇ x)) = x := by
    exact (((p676 a x y)).symm).trans ((((p668 y ((y ◇ (y ◇ y)) ◇ ((y ◇ (y ◇ y)) ◇ y)) a x)).symm).trans ((p650 y a x)))
  have p696 (x y : G) : (x ◇ y) = y := by
    exact (((congrArg (fun _t : G => (x ◇ _t)) ((p693 y y)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (y ◇ (_t ◇ y)))) ((p693 y y)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (y ◇ ((y ◇ (_t ◇ y)) ◇ y)))) ((p693 y y)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (y ◇ ((_t ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ y)))) ((p693 y y)))).symm).trans ((((congrArg (fun _t : G => (_t ◇ (y ◇ (((y ◇ (y ◇ y)) ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ y)))) ((p693 x (a ◇ (x ◇ y)))))).symm).trans ((p675 x a y))))))
  have p697 (x y : G) : x = y := by
    exact ((((((p696 x x)).symm).trans ((((congrArg (fun _t : G => (x ◇ _t)) ((p696 y x)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (y ◇ _t))) ((p696 x x)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (y ◇ (_t ◇ x)))) ((p696 x x)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (y ◇ ((x ◇ _t) ◇ x)))) ((p696 y x)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (y ◇ ((x ◇ (_t ◇ x)) ◇ x)))) ((p696 y y)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (y ◇ ((x ◇ ((y ◇ _t) ◇ x)) ◇ x)))) ((p696 x y)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (y ◇ ((x ◇ ((y ◇ (_t ◇ y)) ◇ x)) ◇ x)))) ((p696 a x)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (y ◇ ((x ◇ ((y ◇ ((a ◇ _t) ◇ y)) ◇ x)) ◇ x)))) ((p696 y x)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (_t ◇ ((x ◇ ((y ◇ ((a ◇ (y ◇ x)) ◇ y)) ◇ x)) ◇ x)))) ((p696 x y)))).symm).trans ((((congrArg (fun _t : G => (x ◇ ((_t ◇ y) ◇ ((x ◇ ((y ◇ ((a ◇ (y ◇ x)) ◇ y)) ◇ x)) ◇ x)))) ((p696 a x)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (((a ◇ _t) ◇ y) ◇ ((x ◇ ((y ◇ ((a ◇ (y ◇ x)) ◇ y)) ◇ x)) ◇ x)))) ((p696 y x)))).symm).trans ((((congrArg (fun _t : G => (_t ◇ (((a ◇ (y ◇ x)) ◇ y) ◇ ((x ◇ ((y ◇ ((a ◇ (y ◇ x)) ◇ y)) ◇ x)) ◇ x)))) ((p696 x x)))).symm).trans ((((congrArg (fun _t : G => ((x ◇ _t) ◇ (((a ◇ (y ◇ x)) ◇ y) ◇ ((x ◇ ((y ◇ ((a ◇ (y ◇ x)) ◇ y)) ◇ x)) ◇ x)))) ((p696 y x)))).symm).trans ((((congrArg (fun _t : G => ((x ◇ (_t ◇ x)) ◇ (((a ◇ (y ◇ x)) ◇ y) ◇ ((x ◇ ((y ◇ ((a ◇ (y ◇ x)) ◇ y)) ◇ x)) ◇ x)))) ((p696 y y)))).symm).trans ((((congrArg (fun _t : G => ((x ◇ ((y ◇ _t) ◇ x)) ◇ (((a ◇ (y ◇ x)) ◇ y) ◇ ((x ◇ ((y ◇ ((a ◇ (y ◇ x)) ◇ y)) ◇ x)) ◇ x)))) ((p696 x y)))).symm).trans ((((congrArg (fun _t : G => ((x ◇ ((y ◇ (_t ◇ y)) ◇ x)) ◇ (((a ◇ (y ◇ x)) ◇ y) ◇ ((x ◇ ((y ◇ ((a ◇ (y ◇ x)) ◇ y)) ◇ x)) ◇ x)))) ((p696 a x)))).symm).trans ((((congrArg (fun _t : G => ((x ◇ ((y ◇ ((a ◇ _t) ◇ y)) ◇ x)) ◇ (((a ◇ (y ◇ x)) ◇ y) ◇ ((x ◇ ((y ◇ ((a ◇ (y ◇ x)) ◇ y)) ◇ x)) ◇ x)))) ((p696 y x)))).symm).trans ((p96 x y a)))))))))))))))))))).trans ((congrArg (fun _t : G => ((a ◇ _t) ◇ y)) ((p696 y x))))).trans ((congrArg (fun _t : G => (_t ◇ y)) ((p696 a x))))).trans ((p696 x y))
  exact (p697 a a).trans (p697 b a).symm

@[reducible] def Equation40070 (G : Type _) [Magma G] : Prop := ∀ (x y z : G), x = (((y ◇ (x ◇ z)) ◇ y) ◇ x) ◇ y

theorem finite_trivial_dual (G : Type*) [Magma G] [Finite G] (h : Equation40070 G) : Equation2 G := by
  let opposite : Magma G := ⟨fun x y => y ◇ x⟩
  have hd : @ Equation5833 G opposite := by
    intro x y z
    exact h x y z
  exact @ finite_trivial G opposite inferInstance hd

#print axioms finite_trivial_dual

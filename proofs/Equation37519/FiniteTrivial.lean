import Mathlib.Data.Fintype.Card
import JudgeMagma.Magma

@[reducible] def Equation2 (G : Type _) [Magma G] : Prop := ∀ (x y : G), x = y
@[reducible] def Equation8485 (G : Type _) [Magma G] : Prop := ∀ (x y z : G), x = y ◇ (x ◇ (((z ◇ x) ◇ y) ◇ y))

theorem finite_trivial (G : Type*) [Magma G] [Finite G] (h : Equation8485 G) : Equation2 G := by
  intro a b
  have ls (y : G) : Function.Surjective (fun t : G => y ◇ t) := by
    intro x
    exact ⟨(x ◇ (((a ◇ x) ◇ y) ◇ y)), (h x y a).symm⟩
  have li (y : G) : Function.Injective (fun t : G => y ◇ t) :=
    Finite.injective_iff_surjective.mpr (ls y)
  let d (x y : G) : G := Classical.choose (ls x y)
  have ld1 (x y : G) : x ◇ d x y = y := Classical.choose_spec (ls x y)
  have ld2 (x y : G) : d x (x ◇ y) = y := li x (ld1 x (x ◇ y))
  have p2 (x y z : G) : (x ◇ (y ◇ (((z ◇ y) ◇ x) ◇ x))) = y := by
    exact (h y x z).symm
  have p3 (x y : G) : (x ◇ (d x y)) = y := by
    exact (ld1 x y)
  have p4 (x y : G) : (d x (x ◇ y)) = y := by
    exact (ld2 x y)
  have p6 (u x y z : G) : (x ◇ ((y ◇ (((z ◇ y) ◇ u) ◇ u)) ◇ ((y ◇ x) ◇ x))) = (y ◇ (((z ◇ y) ◇ u) ◇ u)) := by
    exact (((congrArg (fun _t : G => (x ◇ ((y ◇ (((z ◇ y) ◇ u) ◇ u)) ◇ ((_t ◇ x) ◇ x)))) ((p2 u y z)))).symm).trans ((p2 x (y ◇ (((z ◇ y) ◇ u) ◇ u)) u))
  have p7 (u x y z : G) : ((x ◇ (((y ◇ x) ◇ (z ◇ u)) ◇ (z ◇ u))) ◇ (u ◇ (x ◇ (x ◇ (((y ◇ x) ◇ (z ◇ u)) ◇ (z ◇ u)))))) = u := by
    exact (((congrArg (fun _t : G => ((x ◇ (((y ◇ x) ◇ (z ◇ u)) ◇ (z ◇ u))) ◇ (u ◇ (_t ◇ (x ◇ (((y ◇ x) ◇ (z ◇ u)) ◇ (z ◇ u))))))) ((p2 (z ◇ u) x y)))).symm).trans ((p2 (x ◇ (((y ◇ x) ◇ (z ◇ u)) ◇ (z ◇ u))) u z))
  have p8 (x y z : G) : (x ◇ ((d y z) ◇ ((z ◇ x) ◇ x))) = (d y z) := by
    exact (((congrArg (fun _t : G => (x ◇ ((d y z) ◇ ((_t ◇ x) ◇ x)))) ((p3 y z)))).symm).trans ((p2 x (d y z) y))
  have p10 (x y z : G) : (d x y) = (y ◇ (((z ◇ y) ◇ x) ◇ x)) := by
    exact (((congrArg (fun _t : G => (d x _t)) ((p2 x y z)))).symm).trans ((p4 x (y ◇ (((z ◇ y) ◇ x) ◇ x))))
  have p25 (x y z : G) : (d x (d y z)) = ((d y z) ◇ ((z ◇ x) ◇ x)) := by
    exact ((p10 x (d y z) y)).trans ((congrArg (fun _t : G => ((d y z) ◇ ((_t ◇ x) ◇ x))) ((p3 y z))))
  have p27 (x y z : G) : ((x ◇ y) ◇ (((z ◇ (x ◇ y)) ◇ x) ◇ x)) = y := by
    exact (((p10 x (x ◇ y) z)).symm).trans ((p4 x y))
  have p46 (u x y z : G) : (d x ((d y z) ◇ ((z ◇ u) ◇ u))) = (((d y z) ◇ ((z ◇ u) ◇ u)) ◇ (((d y z) ◇ x) ◇ x)) := by
    exact ((p10 x ((d y z) ◇ ((z ◇ u) ◇ u)) u)).trans ((congrArg (fun _t : G => (((d y z) ◇ ((z ◇ u) ◇ u)) ◇ ((_t ◇ x) ◇ x))) ((p8 u y z))))
  have p55 (x y z : G) : ((x ◇ (((y ◇ x) ◇ z) ◇ z)) ◇ ((x ◇ x) ◇ x)) = (((y ◇ x) ◇ z) ◇ z) := by
    exact (((congrArg (fun _t : G => ((x ◇ (((y ◇ x) ◇ z) ◇ z)) ◇ ((_t ◇ x) ◇ x))) ((p2 z x y)))).symm).trans ((p27 x (((y ◇ x) ◇ z) ◇ z) z))
  have p56 (x y z : G) : (d (x ◇ y) y) = (((z ◇ (x ◇ y)) ◇ x) ◇ x) := by
    exact (((congrArg (fun _t : G => (d (x ◇ y) _t)) ((p27 x y z)))).symm).trans ((p4 (x ◇ y) (((z ◇ (x ◇ y)) ◇ x) ◇ x)))
  have p62 (u x y z : G) : (d x (((y ◇ (z ◇ u)) ◇ z) ◇ z)) = ((((y ◇ (z ◇ u)) ◇ z) ◇ z) ◇ ((u ◇ x) ◇ x)) := by
    exact ((p10 x (((y ◇ (z ◇ u)) ◇ z) ◇ z) (z ◇ u))).trans ((congrArg (fun _t : G => ((((y ◇ (z ◇ u)) ◇ z) ◇ z) ◇ ((_t ◇ x) ◇ x))) ((p27 z u y))))
  have p68 (u x y z : G) : (((x ◇ (y ◇ z)) ◇ y) ◇ y) = (z ◇ (((u ◇ z) ◇ (y ◇ z)) ◇ (y ◇ z))) := by
    exact ((((congrArg (fun _t : G => (z ◇ (((u ◇ _t) ◇ (y ◇ z)) ◇ (y ◇ z)))) ((p27 y z x)))).symm).trans ((((congrArg (fun _t : G => (_t ◇ (((u ◇ ((y ◇ z) ◇ (((x ◇ (y ◇ z)) ◇ y) ◇ y))) ◇ (y ◇ z)) ◇ (y ◇ z)))) ((p27 y z x)))).symm).trans ((p27 (y ◇ z) (((x ◇ (y ◇ z)) ◇ y) ◇ y) u)))).symm
  have p102 (u x y z : G) : (((x ◇ y) ◇ z) ◇ z) = (((u ◇ y) ◇ z) ◇ z) := by
    exact ((((p4 y (((x ◇ y) ◇ z) ◇ z))).symm).trans ((((congrArg (fun _t : G => (d _t (y ◇ (((x ◇ y) ◇ z) ◇ z)))) ((p2 z y x)))).symm).trans ((p56 z (y ◇ (((x ◇ y) ◇ z) ◇ z)) u)))).trans ((congrArg (fun _t : G => (((u ◇ _t) ◇ z) ◇ z)) ((p2 z y x))))
  have p113 (x y z : G) : (d x y) = (y ◇ (((d (y ◇ z) z) ◇ x) ◇ x)) := by
    exact ((p10 x y ((a ◇ (y ◇ z)) ◇ y))).trans ((congrArg (fun _t : G => (y ◇ ((_t ◇ x) ◇ x))) (((p56 y z a)).symm)))
  have p114 (x y : G) : (x ◇ ((d (x ◇ y) y) ◇ x)) = (d x x) := by
    exact (((p10 x x (a ◇ (x ◇ y)))).trans ((congrArg (fun _t : G => (x ◇ (_t ◇ x))) (((p56 x y a)).symm)))).symm
  have p120 (u x y z : G) : (((x ◇ (d y z)) ◇ u) ◇ u) = ((z ◇ u) ◇ u) := by
    exact (((((p4 (d y z) ((z ◇ u) ◇ u))).symm).trans ((((congrArg (fun _t : G => (d _t ((d y z) ◇ ((z ◇ u) ◇ u)))) ((p8 u y z)))).symm).trans ((p56 u ((d y z) ◇ ((z ◇ u) ◇ u)) x)))).trans ((congrArg (fun _t : G => (((x ◇ _t) ◇ u) ◇ u)) ((p8 u y z))))).symm
  have p131 (x y : G) : ((d (x ◇ y) (x ◇ y)) ◇ (y ◇ (x ◇ y))) = y := by
    exact (((congrArg (fun _t : G => ((d (x ◇ y) (x ◇ y)) ◇ (y ◇ _t))) ((p2 (x ◇ y) (x ◇ y) (a ◇ ((x ◇ y) ◇ a)))))).symm).trans ((((congrArg (fun _t : G => (_t ◇ (y ◇ ((x ◇ y) ◇ ((x ◇ y) ◇ ((((a ◇ ((x ◇ y) ◇ a)) ◇ (x ◇ y)) ◇ (x ◇ y)) ◇ (x ◇ y))))))) ((p114 (x ◇ y) a)))).symm).trans ((((congrArg (fun _t : G => (((x ◇ y) ◇ (_t ◇ (x ◇ y))) ◇ (y ◇ ((x ◇ y) ◇ ((x ◇ y) ◇ ((((a ◇ ((x ◇ y) ◇ a)) ◇ (x ◇ y)) ◇ (x ◇ y)) ◇ (x ◇ y))))))) (((p56 (x ◇ y) a a)).symm))).symm).trans ((p7 y (x ◇ y) (a ◇ ((x ◇ y) ◇ a)) x))))
  have p138 (u x y z : G) : (d (d (x ◇ y) y) x) = (((z ◇ (((u ◇ (x ◇ y)) ◇ x) ◇ x)) ◇ ((u ◇ (x ◇ y)) ◇ x)) ◇ ((u ◇ (x ◇ y)) ◇ x)) := by
    exact (((congrArg (fun _t : G => (d _t x)) (((p56 x y u)).symm))).symm).trans ((p56 ((u ◇ (x ◇ y)) ◇ x) x z))
  have p143 (x y : G) : ((d (x ◇ y) y) ◇ x) = ((d x x) ◇ ((x ◇ x) ◇ x)) := by
    exact ((((p25 x x x)).symm).trans ((((congrArg (fun _t : G => (d x _t)) ((p114 x y)))).symm).trans ((p4 x ((d (x ◇ y) y) ◇ x))))).symm
  have p150 (x y z : G) : (d ((x ◇ (y ◇ z)) ◇ y) ((x ◇ (y ◇ z)) ◇ y)) = (((x ◇ (y ◇ z)) ◇ y) ◇ ((d (d (y ◇ z) z) y) ◇ ((x ◇ (y ◇ z)) ◇ y))) := by
    exact ((((congrArg (fun _t : G => (((x ◇ (y ◇ z)) ◇ y) ◇ ((d _t y) ◇ ((x ◇ (y ◇ z)) ◇ y)))) (((p56 y z x)).symm))).symm).trans ((p114 ((x ◇ (y ◇ z)) ◇ y) y))).symm
  have p180 (u x y z : G) : (d ((x ◇ y) ◇ z) (((u ◇ y) ◇ z) ◇ z)) = z := by
    exact (((congrArg (fun _t : G => (d ((x ◇ y) ◇ z) _t)) ((p102 u x y z)))).symm).trans ((p4 ((x ◇ y) ◇ z) z))
  have p195 (u w x y z : G) : (((x ◇ (((y ◇ (z ◇ u)) ◇ z) ◇ z)) ◇ w) ◇ w) = ((u ◇ w) ◇ w) := by
    exact ((((congrArg (fun _t : G => ((_t ◇ w) ◇ w)) ((p27 z u y)))).symm).trans ((p102 x (z ◇ u) (((y ◇ (z ◇ u)) ◇ z) ◇ z) w))).symm
  have p209 (x y z : G) : (d (d (x ◇ y) y) x) = ((y ◇ ((z ◇ (x ◇ y)) ◇ x)) ◇ ((z ◇ (x ◇ y)) ◇ x)) := by
    exact ((p138 z x y a)).trans ((p195 y ((z ◇ (x ◇ y)) ◇ x) a z x))
  have p251 (u x y z : G) : (d x (y ◇ z)) = ((y ◇ z) ◇ ((((((u ◇ (y ◇ z)) ◇ y) ◇ y) ◇ ((z ◇ z) ◇ z)) ◇ x) ◇ x)) := by
    exact (((p113 x (y ◇ z) (((u ◇ (y ◇ z)) ◇ y) ◇ y))).trans ((congrArg (fun _t : G => ((y ◇ z) ◇ (((d _t (((u ◇ (y ◇ z)) ◇ y) ◇ y)) ◇ x) ◇ x))) ((p27 y z u))))).trans ((congrArg (fun _t : G => ((y ◇ z) ◇ ((_t ◇ x) ◇ x))) ((p62 z z u y))))
  have p272 (u x y z : G) : (d ((x ◇ (d y z)) ◇ u) ((z ◇ u) ◇ u)) = u := by
    exact (((congrArg (fun _t : G => (d ((x ◇ (d y z)) ◇ u) _t)) ((p120 u x y z)))).symm).trans ((p4 ((x ◇ (d y z)) ◇ u) u))
  have p279 (u w x y z : G) : (((x ◇ y) ◇ y) ◇ (((z ◇ ((x ◇ y) ◇ y)) ◇ ((u ◇ (d w x)) ◇ y)) ◇ ((u ◇ (d w x)) ◇ y))) = y := by
    exact (((congrArg (fun _t : G => (((x ◇ y) ◇ y) ◇ (((z ◇ _t) ◇ ((u ◇ (d w x)) ◇ y)) ◇ ((u ◇ (d w x)) ◇ y)))) ((p120 y u w x)))).symm).trans ((((congrArg (fun _t : G => (_t ◇ (((z ◇ (((u ◇ (d w x)) ◇ y) ◇ y)) ◇ ((u ◇ (d w x)) ◇ y)) ◇ ((u ◇ (d w x)) ◇ y)))) ((p120 y u w x)))).symm).trans ((p27 ((u ◇ (d w x)) ◇ y) y z)))
  have p280 (u w x y z : G) : (d ((x ◇ y) ◇ y) y) = (((z ◇ ((x ◇ y) ◇ y)) ◇ ((u ◇ (d w x)) ◇ y)) ◇ ((u ◇ (d w x)) ◇ y)) := by
    exact ((((congrArg (fun _t : G => (d _t y)) ((p120 y u w x)))).symm).trans ((p56 ((u ◇ (d w x)) ◇ y) y z))).trans ((congrArg (fun _t : G => (((z ◇ _t) ◇ ((u ◇ (d w x)) ◇ y)) ◇ ((u ◇ (d w x)) ◇ y))) ((p120 y u w x))))
  have p293 (x y z : G) : (d x (y ◇ (z ◇ y))) = ((y ◇ (z ◇ y)) ◇ ((y ◇ x) ◇ x)) := by
    exact ((p10 x (y ◇ (z ◇ y)) (d (z ◇ y) (z ◇ y)))).trans ((congrArg (fun _t : G => ((y ◇ (z ◇ y)) ◇ ((_t ◇ x) ◇ x))) ((p131 z y))))
  have p298 (x y : G) : ((x ◇ (y ◇ x)) ◇ ((x ◇ x) ◇ x)) = (y ◇ x) := by
    exact (((congrArg (fun _t : G => ((x ◇ (y ◇ x)) ◇ ((_t ◇ x) ◇ x))) ((p131 y x)))).symm).trans ((p27 x (y ◇ x) (d (y ◇ x) (y ◇ x))))
  have p412 (u w x y z : G) : (d ((x ◇ (((y ◇ (z ◇ u)) ◇ z) ◇ z)) ◇ w) ((u ◇ w) ◇ w)) = w := by
    exact (((congrArg (fun _t : G => (d ((x ◇ (((y ◇ (z ◇ u)) ◇ z) ◇ z)) ◇ w) ((_t ◇ w) ◇ w))) ((p27 z u y)))).symm).trans ((p180 (z ◇ u) x (((y ◇ (z ◇ u)) ◇ z) ◇ z) w))
  have p415 (x y z : G) : (d (d (x ◇ y) y) (((z ◇ x) ◇ x) ◇ x)) = x := by
    exact (((congrArg (fun _t : G => (d _t (((z ◇ x) ◇ x) ◇ x))) (((p56 x y a)).symm))).symm).trans ((p180 z (a ◇ (x ◇ y)) x x))
  have p417 (x y : G) : (((d x x) ◇ ((x ◇ x) ◇ x)) ◇ (((d x x) ◇ ((y ◇ x) ◇ x)) ◇ ((y ◇ x) ◇ x))) = x := by
    exact (((p46 x ((y ◇ x) ◇ x) x x)).symm).trans ((((congrArg (fun _t : G => (d ((y ◇ x) ◇ x) _t)) ((p143 x a)))).symm).trans ((((congrArg (fun _t : G => (d ((y ◇ x) ◇ x) (_t ◇ x))) (((p56 x a a)).symm))).symm).trans ((p180 (a ◇ (x ◇ a)) y x x))))
  have p426 (u x y z : G) : (d ((x ◇ (y ◇ (z ◇ y))) ◇ u) ((y ◇ u) ◇ u)) = u := by
    exact (((congrArg (fun _t : G => (d ((x ◇ (y ◇ (z ◇ y))) ◇ u) ((_t ◇ u) ◇ u))) ((p131 z y)))).symm).trans ((p180 (d (z ◇ y) (z ◇ y)) x (y ◇ (z ◇ y)) u))
  have p449 (x y z : G) : (x ◇ (((y ◇ y) ◇ y) ◇ (((z ◇ y) ◇ x) ◇ x))) = ((y ◇ y) ◇ y) := by
    exact (((congrArg (fun _t : G => (x ◇ (((y ◇ y) ◇ y) ◇ ((_t ◇ x) ◇ x)))) ((p298 y z)))).symm).trans ((p2 x ((y ◇ y) ◇ y) (y ◇ (z ◇ y))))
  have p456 (x y z : G) : (((x ◇ x) ◇ x) ◇ (((y ◇ x) ◇ z) ◇ z)) = (x ◇ (((y ◇ x) ◇ z) ◇ z)) := by
    exact (((congrArg (fun _t : G => (((x ◇ x) ◇ x) ◇ _t)) ((p55 x y z)))).symm).trans ((((congrArg (fun _t : G => (((x ◇ x) ◇ x) ◇ ((x ◇ (((y ◇ x) ◇ z) ◇ z)) ◇ _t))) ((p298 x (x ◇ x))))).symm).trans ((p6 z ((x ◇ x) ◇ x) x y)))
  have p470 (x y z : G) : (d (x ◇ y) ((y ◇ y) ◇ y)) = (((z ◇ (x ◇ y)) ◇ (y ◇ (x ◇ y))) ◇ (y ◇ (x ◇ y))) := by
    exact ((((congrArg (fun _t : G => (d _t ((y ◇ y) ◇ y))) ((p298 y x)))).symm).trans ((p56 (y ◇ (x ◇ y)) ((y ◇ y) ◇ y) z))).trans ((congrArg (fun _t : G => (((z ◇ _t) ◇ (y ◇ (x ◇ y))) ◇ (y ◇ (x ◇ y)))) ((p298 y x))))
  have p471 (x y : G) : (d ((x ◇ x) ◇ x) x) = (((y ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) := by
    exact ((p56 (x ◇ x) x (x ◇ (y ◇ x)))).trans ((congrArg (fun _t : G => ((_t ◇ (x ◇ x)) ◇ (x ◇ x))) ((p298 x y))))
  have p473 (x y z : G) : (((x ◇ (y ◇ z)) ◇ y) ◇ y) = ((y ◇ (d (y ◇ z) z)) ◇ ((y ◇ y) ◇ y)) := by
    exact ((((congrArg (fun _t : G => ((y ◇ _t) ◇ ((y ◇ y) ◇ y))) (((p56 y z x)).symm))).symm).trans ((p298 y ((x ◇ (y ◇ z)) ◇ y)))).symm
  have p479 (x y z : G) : (((x ◇ y) ◇ (((z ◇ y) ◇ (z ◇ y)) ◇ (z ◇ y))) ◇ (((z ◇ y) ◇ (z ◇ y)) ◇ (z ◇ y))) = (((z ◇ y) ◇ (z ◇ y)) ◇ (z ◇ y)) := by
    exact ((((p298 (z ◇ y) ((z ◇ y) ◇ (z ◇ y)))).symm).trans ((p102 x z y (((z ◇ y) ◇ (z ◇ y)) ◇ (z ◇ y))))).symm
  have p484 (x y : G) : (d (((d (x ◇ y) y) ◇ (d (x ◇ y) y)) ◇ (d (x ◇ y) y)) x) = (x ◇ (((d (x ◇ y) y) ◇ (d (x ◇ y) y)) ◇ (d (x ◇ y) y))) := by
    exact ((p113 (((d (x ◇ y) y) ◇ (d (x ◇ y) y)) ◇ (d (x ◇ y) y)) x y)).trans ((congrArg (fun _t : G => (x ◇ _t)) ((p298 (d (x ◇ y) y) ((d (x ◇ y) y) ◇ (d (x ◇ y) y))))))
  have p486 (x : G) : (((d x x) ◇ ((x ◇ x) ◇ x)) ◇ x) = ((d x x) ◇ ((x ◇ x) ◇ x)) := by
    exact (((((congrArg (fun _t : G => (_t ◇ ((x ◇ x) ◇ x))) (((p113 x x a)).symm))).symm).trans ((p298 x ((d (x ◇ a) a) ◇ x)))).trans ((congrArg (fun _t : G => (_t ◇ x)) ((p143 x a))))).symm
  have p491 (x y : G) : (((x ◇ (y ◇ x)) ◇ x) ◇ (((x ◇ (y ◇ x)) ◇ (x ◇ (y ◇ x))) ◇ (x ◇ (y ◇ x)))) = x := by
    exact ((((congrArg (fun _t : G => (((x ◇ (y ◇ x)) ◇ _t) ◇ (((x ◇ (y ◇ x)) ◇ (x ◇ (y ◇ x))) ◇ (x ◇ (y ◇ x))))) ((p131 y x)))).symm).trans ((p298 (x ◇ (y ◇ x)) (d (y ◇ x) (y ◇ x))))).trans ((p131 y x))
  have p497 (u x y z : G) : (d ((x ◇ ((y ◇ (z ◇ y)) ◇ ((y ◇ u) ◇ u))) ◇ ((y ◇ y) ◇ y)) ((z ◇ y) ◇ ((y ◇ y) ◇ y))) = ((y ◇ y) ◇ y) := by
    exact (((congrArg (fun _t : G => (d ((x ◇ _t) ◇ ((y ◇ y) ◇ y)) ((z ◇ y) ◇ ((y ◇ y) ◇ y)))) ((p293 u y z)))).symm).trans ((((congrArg (fun _t : G => (d ((x ◇ (d u (y ◇ (z ◇ y)))) ◇ ((y ◇ y) ◇ y)) (_t ◇ ((y ◇ y) ◇ y)))) ((p298 y z)))).symm).trans ((p272 ((y ◇ y) ◇ y) x u (y ◇ (z ◇ y)))))
  have p499 (x y : G) : ((((x ◇ x) ◇ x) ◇ (y ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ ((x ◇ x) ◇ x))) = (y ◇ x) := by
    exact ((((congrArg (fun _t : G => ((((x ◇ x) ◇ x) ◇ _t) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ ((x ◇ x) ◇ x)))) ((p298 x y)))).symm).trans ((p298 ((x ◇ x) ◇ x) (x ◇ (y ◇ x))))).trans ((p298 x y))
  have p500 (x : G) : ((x ◇ x) ◇ x) = x := by
    exact ((((p2 a x a)).symm).trans ((((congrArg (fun _t : G => (a ◇ _t)) ((p456 x a a)))).symm).trans ((p449 a x a)))).symm
  have p505 (x y : G) : ((x ◇ (y ◇ x)) ◇ x) = (y ◇ x) := by
    exact (((congrArg (fun _t : G => ((x ◇ (y ◇ x)) ◇ _t)) ((p500 x)))).symm).trans ((((congrArg (fun _t : G => ((x ◇ (y ◇ x)) ◇ ((x ◇ x) ◇ _t))) ((p500 x)))).symm).trans ((((congrArg (fun _t : G => ((x ◇ (y ◇ x)) ◇ ((x ◇ _t) ◇ ((x ◇ x) ◇ x)))) ((p500 x)))).symm).trans ((((congrArg (fun _t : G => ((x ◇ (y ◇ x)) ◇ ((_t ◇ ((x ◇ x) ◇ x)) ◇ ((x ◇ x) ◇ x)))) ((p500 x)))).symm).trans ((((congrArg (fun _t : G => ((_t ◇ (y ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ ((x ◇ x) ◇ x)))) ((p500 x)))).symm).trans ((p499 x y))))))
  have p507 (u x y z : G) : (d ((x ◇ ((y ◇ (z ◇ y)) ◇ ((y ◇ u) ◇ u))) ◇ y) ((z ◇ y) ◇ y)) = y := by
    exact ((((congrArg (fun _t : G => (d ((x ◇ ((y ◇ (z ◇ y)) ◇ ((y ◇ u) ◇ u))) ◇ y) ((z ◇ y) ◇ _t))) ((p500 y)))).symm).trans ((((congrArg (fun _t : G => (d ((x ◇ ((y ◇ (z ◇ y)) ◇ ((y ◇ u) ◇ u))) ◇ _t) ((z ◇ y) ◇ ((y ◇ y) ◇ y)))) ((p500 y)))).symm).trans ((p497 u x y z)))).trans ((p500 y))
  have p511 (x y : G) : ((x ◇ y) ◇ (y ◇ (x ◇ y))) = y := by
    exact (((congrArg (fun _t : G => ((x ◇ y) ◇ _t)) ((p500 (y ◇ (x ◇ y)))))).symm).trans ((((congrArg (fun _t : G => (_t ◇ (((y ◇ (x ◇ y)) ◇ (y ◇ (x ◇ y))) ◇ (y ◇ (x ◇ y))))) ((p505 y x)))).symm).trans ((p491 y x)))
  have p513 (x : G) : (((d x x) ◇ x) ◇ x) = ((d x x) ◇ x) := by
    exact ((((congrArg (fun _t : G => (((d x x) ◇ _t) ◇ x)) ((p500 x)))).symm).trans ((p486 x))).trans ((congrArg (fun _t : G => ((d x x) ◇ _t)) ((p500 x))))
  have p515 (x y : G) : (d (d (x ◇ y) y) x) = (x ◇ (d (x ◇ y) y)) := by
    exact ((((congrArg (fun _t : G => (d _t x)) ((p500 (d (x ◇ y) y))))).symm).trans ((p484 x y))).trans ((congrArg (fun _t : G => (x ◇ _t)) ((p500 (d (x ◇ y) y)))))
  have p518 (x y z : G) : (((x ◇ y) ◇ (z ◇ y)) ◇ (z ◇ y)) = (z ◇ y) := by
    exact ((((congrArg (fun _t : G => (((x ◇ y) ◇ (z ◇ y)) ◇ _t)) ((p500 (z ◇ y))))).symm).trans ((((congrArg (fun _t : G => (((x ◇ y) ◇ _t) ◇ (((z ◇ y) ◇ (z ◇ y)) ◇ (z ◇ y)))) ((p500 (z ◇ y))))).symm).trans ((p479 x y z)))).trans ((p500 (z ◇ y)))
  have p522 (x y z : G) : (((x ◇ (y ◇ z)) ◇ y) ◇ y) = ((y ◇ (d (y ◇ z) z)) ◇ y) := by
    exact ((p473 x y z)).trans ((congrArg (fun _t : G => ((y ◇ (d (y ◇ z) z)) ◇ _t)) ((p500 y))))
  have p524 (x : G) : (d x x) = (x ◇ x) := by
    exact ((((congrArg (fun _t : G => (d _t x)) ((p500 x)))).symm).trans ((p471 x a))).trans ((p518 a x x))
  have p525 (x y : G) : (d (x ◇ y) y) = (y ◇ (x ◇ y)) := by
    exact ((((congrArg (fun _t : G => (d (x ◇ y) _t)) ((p500 y)))).symm).trans ((p470 x y a))).trans ((p518 a (x ◇ y) y))
  have p538 (x y : G) : (x ◇ ((y ◇ x) ◇ x)) = x := by
    exact (((congrArg (fun _t : G => (x ◇ _t)) ((p518 x x (y ◇ x))))).symm).trans ((((congrArg (fun _t : G => (x ◇ ((_t ◇ ((y ◇ x) ◇ x)) ◇ ((y ◇ x) ◇ x)))) ((p524 x)))).symm).trans ((((congrArg (fun _t : G => (_t ◇ (((d x x) ◇ ((y ◇ x) ◇ x)) ◇ ((y ◇ x) ◇ x)))) ((p500 x)))).symm).trans ((((congrArg (fun _t : G => (((x ◇ x) ◇ _t) ◇ (((d x x) ◇ ((y ◇ x) ◇ x)) ◇ ((y ◇ x) ◇ x)))) ((p500 x)))).symm).trans ((((congrArg (fun _t : G => ((_t ◇ ((x ◇ x) ◇ x)) ◇ (((d x x) ◇ ((y ◇ x) ◇ x)) ◇ ((y ◇ x) ◇ x)))) ((p524 x)))).symm).trans ((p417 x y))))))
  have p546 (u x y z : G) : (d x (y ◇ z)) = ((y ◇ z) ◇ ((((((u ◇ (y ◇ z)) ◇ y) ◇ y) ◇ z) ◇ x) ◇ x)) := by
    exact ((p251 u x y z)).trans ((congrArg (fun _t : G => ((y ◇ z) ◇ ((((((u ◇ (y ◇ z)) ◇ y) ◇ y) ◇ _t) ◇ x) ◇ x))) ((p500 z))))
  have p577 (x y z : G) : (d (x ◇ (y ◇ x)) y) = ((x ◇ ((z ◇ (y ◇ x)) ◇ y)) ◇ ((z ◇ (y ◇ x)) ◇ y)) := by
    exact (((congrArg (fun _t : G => (d _t y)) ((p525 y x)))).symm).trans ((p209 y x z))
  have p579 (x y z : G) : (((x ◇ (y ◇ z)) ◇ y) ◇ ((d (z ◇ (y ◇ z)) y) ◇ ((x ◇ (y ◇ z)) ◇ y))) = (((x ◇ (y ◇ z)) ◇ y) ◇ ((x ◇ (y ◇ z)) ◇ y)) := by
    exact (((((p524 ((x ◇ (y ◇ z)) ◇ y))).symm).trans ((p150 x y z))).trans ((congrArg (fun _t : G => (((x ◇ (y ◇ z)) ◇ y) ◇ ((d _t y) ◇ ((x ◇ (y ◇ z)) ◇ y)))) ((p525 y z))))).symm
  have p583 (x y z : G) : (((x ◇ (y ◇ z)) ◇ y) ◇ y) = (z ◇ (y ◇ z)) := by
    exact ((p68 a x y z)).trans ((congrArg (fun _t : G => (z ◇ _t)) ((p518 a z y))))
  have p584 (x : G) : (x ◇ x) = x := by
    exact (((((congrArg (fun _t : G => (_t ◇ x)) ((p500 x)))).symm).trans ((((congrArg (fun _t : G => ((_t ◇ x) ◇ x)) ((p524 x)))).symm).trans ((p513 x)))).trans ((congrArg (fun _t : G => (_t ◇ x)) ((p524 x))))).trans ((p500 x))
  have p593 (x y : G) : ((x ◇ (y ◇ (x ◇ y))) ◇ x) = (y ◇ (x ◇ y)) := by
    exact (((((p583 a x y)).symm).trans ((p522 a x y))).trans ((congrArg (fun _t : G => ((x ◇ _t) ◇ x)) ((p525 x y))))).symm
  have p596 (x y : G) : (d (x ◇ (y ◇ x)) y) = (y ◇ (x ◇ (y ◇ x))) := by
    exact ((((congrArg (fun _t : G => (d _t y)) ((p525 y x)))).symm).trans ((p515 y x))).trans ((congrArg (fun _t : G => (y ◇ _t)) ((p525 y x))))
  have p615 (x y z : G) : (d (x ◇ (y ◇ x)) (((z ◇ y) ◇ y) ◇ y)) = y := by
    exact (((congrArg (fun _t : G => (d _t (((z ◇ y) ◇ y) ◇ y))) ((p525 y x)))).symm).trans ((p415 y x z))
  have p641 (u w x y z : G) : (((x ◇ ((y ◇ z) ◇ z)) ◇ ((u ◇ (d w y)) ◇ z)) ◇ ((u ◇ (d w y)) ◇ z)) = z := by
    exact ((((p538 z y)).symm).trans ((((p525 (y ◇ z) z)).symm).trans ((p280 u w y z x)))).symm
  have p701 (x y z : G) : (d x (y ◇ z)) = ((y ◇ z) ◇ (((y ◇ z) ◇ x) ◇ x)) := by
    exact (((p546 a x y z)).trans ((congrArg (fun _t : G => ((y ◇ z) ◇ (((_t ◇ z) ◇ x) ◇ x))) ((p583 a y z))))).trans ((congrArg (fun _t : G => ((y ◇ z) ◇ ((_t ◇ x) ◇ x))) ((p505 z y))))
  have p706 (u x y z : G) : (((x ◇ y) ◇ y) ◇ ((z ◇ (x ◇ (u ◇ x))) ◇ y)) = y := by
    exact (((congrArg (fun _t : G => (((x ◇ y) ◇ y) ◇ _t)) ((p518 (x ◇ y) y (z ◇ (x ◇ (u ◇ x))))))).symm).trans ((((p701 ((z ◇ (x ◇ (u ◇ x))) ◇ y) (x ◇ y) y)).symm).trans ((((congrArg (fun _t : G => (d ((z ◇ _t) ◇ y) ((x ◇ y) ◇ y))) ((p583 a u x)))).symm).trans ((p412 x y z a u))))
  have p715 (x y z : G) : (((x ◇ (y ◇ z)) ◇ y) ◇ ((y ◇ (z ◇ (y ◇ z))) ◇ ((x ◇ (y ◇ z)) ◇ y))) = ((x ◇ (y ◇ z)) ◇ y) := by
    exact ((((congrArg (fun _t : G => (((x ◇ (y ◇ z)) ◇ y) ◇ (_t ◇ ((x ◇ (y ◇ z)) ◇ y)))) ((p596 z y)))).symm).trans ((p579 x y z))).trans ((p584 ((x ◇ (y ◇ z)) ◇ y)))
  have p720 (x y z : G) : ((x ◇ ((y ◇ (z ◇ x)) ◇ z)) ◇ ((y ◇ (z ◇ x)) ◇ z)) = (z ◇ (x ◇ (z ◇ x))) := by
    exact ((((p596 x z)).symm).trans ((p577 x z y))).symm
  have p723 (x y : G) : (((x ◇ y) ◇ y) ◇ y) = y := by
    exact (((congrArg (fun _t : G => (((x ◇ y) ◇ y) ◇ _t)) ((p641 a a a x y)))).symm).trans ((p279 a a x y a))
  have p738 (x y : G) : (x ◇ (y ◇ (x ◇ y))) = x := by
    exact (((p596 y x)).symm).trans ((((congrArg (fun _t : G => (d (y ◇ (x ◇ y)) _t)) ((p723 a x)))).symm).trans ((p615 y x a)))
  have p758 (u x y z : G) : (((x ◇ y) ◇ y) ◇ ((z ◇ ((y ◇ (x ◇ y)) ◇ ((y ◇ u) ◇ u))) ◇ y)) = y := by
    exact (((congrArg (fun _t : G => (((x ◇ y) ◇ y) ◇ _t)) ((p518 (x ◇ y) y (z ◇ ((y ◇ (x ◇ y)) ◇ ((y ◇ u) ◇ u))))))).symm).trans ((((p701 ((z ◇ ((y ◇ (x ◇ y)) ◇ ((y ◇ u) ◇ u))) ◇ y) (x ◇ y) y)).symm).trans ((p507 u z y x)))
  have p769 (u x y z : G) : (((x ◇ y) ◇ y) ◇ (y ◇ ((z ◇ (x ◇ (u ◇ x))) ◇ y))) = y := by
    exact (((congrArg (fun _t : G => (((x ◇ y) ◇ y) ◇ (_t ◇ ((z ◇ (x ◇ (u ◇ x))) ◇ y)))) ((p706 u x y z)))).symm).trans ((((p701 ((z ◇ (x ◇ (u ◇ x))) ◇ y) (x ◇ y) y)).symm).trans ((p426 y z x u)))
  have p811 (x y z : G) : ((x ◇ ((y ◇ (z ◇ x)) ◇ z)) ◇ ((y ◇ (z ◇ x)) ◇ z)) = z := by
    exact ((p720 x y z)).trans ((p738 z x))
  have p812 (x y z : G) : ((x ◇ (y ◇ z)) ◇ y) = y := by
    exact ((((p511 (x ◇ (y ◇ z)) y)).symm).trans ((((congrArg (fun _t : G => (((x ◇ (y ◇ z)) ◇ y) ◇ (_t ◇ ((x ◇ (y ◇ z)) ◇ y)))) ((p738 y z)))).symm).trans ((p715 x y z)))).symm
  have p814 (x y : G) : (x ◇ (y ◇ x)) = y := by
    exact ((((p584 y)).symm).trans ((((congrArg (fun _t : G => (_t ◇ y)) ((p738 y x)))).symm).trans ((p593 y x)))).symm
  have p826 (x y : G) : ((x ◇ y) ◇ y) = y := by
    exact (((congrArg (fun _t : G => ((x ◇ y) ◇ _t)) ((p812 a y x)))).symm).trans ((((congrArg (fun _t : G => ((x ◇ _t) ◇ ((a ◇ (y ◇ x)) ◇ y))) ((p812 a y x)))).symm).trans ((p811 x a y)))
  have p827 (x y z : G) : (x ◇ (y ◇ z)) = x := by
    exact (((congrArg (fun _t : G => (x ◇ _t)) ((p814 x (y ◇ z))))).symm).trans ((((congrArg (fun _t : G => (x ◇ (x ◇ ((y ◇ _t) ◇ x)))) ((p814 a z)))).symm).trans ((((congrArg (fun _t : G => (_t ◇ (x ◇ ((y ◇ (a ◇ (z ◇ a))) ◇ x)))) ((p826 a x)))).symm).trans ((p769 z a x y))))
  have p828 (x y : G) : x = y := by
    exact (((p814 y x)).symm).trans ((((congrArg (fun _t : G => (y ◇ (_t ◇ y))) ((p827 x a a)))).symm).trans ((((congrArg (fun _t : G => (y ◇ ((x ◇ (a ◇ _t)) ◇ y))) ((p826 y a)))).symm).trans ((((congrArg (fun _t : G => (y ◇ ((x ◇ (_t ◇ ((y ◇ a) ◇ a))) ◇ y))) ((p814 y a)))).symm).trans ((((congrArg (fun _t : G => (_t ◇ ((x ◇ ((y ◇ (a ◇ y)) ◇ ((y ◇ a) ◇ a))) ◇ y))) ((p826 a y)))).symm).trans ((p758 a a y x))))))
  exact (p828 a a).trans (p828 b a).symm

@[reducible] def Equation37519 (G : Type _) [Magma G] : Prop := ∀ (x y z : G), x = ((y ◇ (y ◇ (x ◇ z))) ◇ x) ◇ y

theorem finite_trivial_dual (G : Type*) [Magma G] [Finite G] (h : Equation37519 G) : Equation2 G := by
  let opposite : Magma G := ⟨fun x y => y ◇ x⟩
  have hd : @ Equation8485 G opposite := by
    intro x y z
    exact h x y z
  exact @ finite_trivial G opposite inferInstance hd

#print axioms finite_trivial_dual

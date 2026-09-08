import Mathlib.Data.Fintype.Card
import JudgeMagma.Magma

@[reducible] def Equation2 (G : Type _) [Magma G] : Prop := ∀ (x y : G), x = y
@[reducible] def Equation7587 (G : Type _) [Magma G] : Prop := ∀ (x y z : G), x = y ◇ (x ◇ ((y ◇ (z ◇ x)) ◇ y))

theorem finite_trivial (G : Type*) [Magma G] [Finite G] (h : Equation7587 G) : Equation2 G := by
  intro a b
  have ls (y : G) : Function.Surjective (fun t : G => y ◇ t) := by
    intro x
    exact ⟨(x ◇ ((y ◇ (a ◇ x)) ◇ y)), (h x y a).symm⟩
  have li (y : G) : Function.Injective (fun t : G => y ◇ t) :=
    Finite.injective_iff_surjective.mpr (ls y)
  let d (x y : G) : G := Classical.choose (ls x y)
  have ld1 (x y : G) : x ◇ d x y = y := Classical.choose_spec (ls x y)
  have ld2 (x y : G) : d x (x ◇ y) = y := li x (ld1 x (x ◇ y))
  have p2 (x y z : G) : (x ◇ (y ◇ ((x ◇ (z ◇ y)) ◇ x))) = y := by
    exact (h y x z).symm
  have p3 (x y : G) : (x ◇ (d x y)) = y := by
    exact (ld1 x y)
  have p4 (x y : G) : (d x (x ◇ y)) = y := by
    exact (ld2 x y)
  have p6 (u x y z : G) : (x ◇ ((y ◇ ((z ◇ (u ◇ y)) ◇ z)) ◇ ((x ◇ y) ◇ x))) = (y ◇ ((z ◇ (u ◇ y)) ◇ z)) := by
    exact (((congrArg (fun _t : G => (x ◇ ((y ◇ ((z ◇ (u ◇ y)) ◇ z)) ◇ ((x ◇ _t) ◇ x)))) ((p2 z y u)))).symm).trans ((p2 x (y ◇ ((z ◇ (u ◇ y)) ◇ z)) z))
  have p7 (x y z : G) : (x ◇ (((x ◇ (y ◇ z)) ◇ x) ◇ (z ◇ x))) = ((x ◇ (y ◇ z)) ◇ x) := by
    exact (((congrArg (fun _t : G => (x ◇ (((x ◇ (y ◇ z)) ◇ x) ◇ (_t ◇ x)))) ((p2 x z y)))).symm).trans ((p2 x ((x ◇ (y ◇ z)) ◇ x) z))
  have p8 (x y z : G) : (x ◇ ((d y z) ◇ ((x ◇ z) ◇ x))) = (d y z) := by
    exact (((congrArg (fun _t : G => (x ◇ ((d y z) ◇ ((x ◇ _t) ◇ x)))) ((p3 y z)))).symm).trans ((p2 x (d y z) y))
  have p9 (x y z : G) : (d x y) = (y ◇ ((x ◇ (z ◇ y)) ◇ x)) := by
    exact (((congrArg (fun _t : G => (d x _t)) ((p2 x y z)))).symm).trans ((p4 x (y ◇ ((x ◇ (z ◇ y)) ◇ x))))
  have p10 (u w x y z : G) : (x ◇ (((y ◇ ((z ◇ (u ◇ y)) ◇ z)) ◇ ((w ◇ y) ◇ w)) ◇ ((x ◇ (y ◇ ((z ◇ (u ◇ y)) ◇ z))) ◇ x))) = ((y ◇ ((z ◇ (u ◇ y)) ◇ z)) ◇ ((w ◇ y) ◇ w)) := by
    exact (((congrArg (fun _t : G => (x ◇ (((y ◇ ((z ◇ (u ◇ y)) ◇ z)) ◇ ((w ◇ y) ◇ w)) ◇ ((x ◇ _t) ◇ x)))) ((p6 u w y z)))).symm).trans ((p2 x ((y ◇ ((z ◇ (u ◇ y)) ◇ z)) ◇ ((w ◇ y) ◇ w)) w))
  have p20 (u x y z : G) : (x ◇ (((y ◇ (z ◇ u)) ◇ y) ◇ ((x ◇ (d y u)) ◇ x))) = ((y ◇ (z ◇ u)) ◇ y) := by
    exact (((congrArg (fun _t : G => (x ◇ (((y ◇ (z ◇ u)) ◇ y) ◇ ((x ◇ _t) ◇ x)))) (((p9 y u z)).symm))).symm).trans ((p2 x ((y ◇ (z ◇ u)) ◇ y) u))
  have p21 (x y : G) : (x ◇ (y ◇ ((d y x) ◇ x))) = y := by
    exact (((congrArg (fun _t : G => (x ◇ (y ◇ (_t ◇ x)))) (((p9 y x a)).symm))).symm).trans ((p2 x y (y ◇ (a ◇ x))))
  have p23 (x y z : G) : (d x (d y z)) = ((d y z) ◇ ((x ◇ z) ◇ x)) := by
    exact ((p9 x (d y z) y)).trans ((congrArg (fun _t : G => ((d y z) ◇ ((x ◇ _t) ◇ x))) ((p3 y z))))
  have p24 (x y z : G) : ((x ◇ y) ◇ ((x ◇ (z ◇ (x ◇ y))) ◇ x)) = y := by
    exact (((p9 x (x ◇ y) z)).symm).trans ((p4 x y))
  have p35 (x y : G) : (d x y) = (y ◇ ((d y x) ◇ x)) := by
    exact ((p9 x y (y ◇ (a ◇ x)))).trans ((congrArg (fun _t : G => (y ◇ (_t ◇ x))) (((p9 y x a)).symm)))
  have p38 (x y : G) : ((x ◇ y) ◇ (x ◇ (y ◇ (x ◇ y)))) = x := by
    exact (((congrArg (fun _t : G => ((x ◇ y) ◇ (x ◇ (_t ◇ (x ◇ y))))) ((p4 x y)))).symm).trans ((p21 (x ◇ y) x))
  have p46 (x y : G) : ((d x y) ◇ ((y ◇ y) ◇ y)) = ((d y x) ◇ x) := by
    exact (((p23 y x y)).symm).trans ((((congrArg (fun _t : G => (d y _t)) (((p35 x y)).symm))).symm).trans ((p4 y ((d y x) ◇ x))))
  have p47 (x y : G) : (d (x ◇ y) x) = (x ◇ (y ◇ (x ◇ y))) := by
    exact ((p35 (x ◇ y) x)).trans ((congrArg (fun _t : G => (x ◇ (_t ◇ (x ◇ y)))) ((p4 x y))))
  have p61 (x y : G) : (d (x ◇ y) (y ◇ (x ◇ y))) = ((y ◇ (x ◇ y)) ◇ (x ◇ (x ◇ y))) := by
    exact ((p9 (x ◇ y) (y ◇ (x ◇ y)) x)).trans ((congrArg (fun _t : G => ((y ◇ (x ◇ y)) ◇ (_t ◇ (x ◇ y)))) ((p38 x y))))
  have p111 (u x y z : G) : (d x ((d y z) ◇ ((u ◇ z) ◇ u))) = (((d y z) ◇ ((u ◇ z) ◇ u)) ◇ ((x ◇ (d y z)) ◇ x)) := by
    exact ((p9 x ((d y z) ◇ ((u ◇ z) ◇ u)) u)).trans ((congrArg (fun _t : G => (((d y z) ◇ ((u ◇ z) ◇ u)) ◇ ((x ◇ _t) ◇ x))) ((p8 u y z))))
  have p133 (u x y z : G) : (d x (((d y z) ◇ ((x ◇ z) ◇ x)) ◇ ((u ◇ (d y z)) ◇ u))) = ((((d y z) ◇ ((x ◇ z) ◇ x)) ◇ ((u ◇ (d y z)) ◇ u)) ◇ ((d y z) ◇ x)) := by
    exact ((((congrArg (fun _t : G => (d x _t)) ((p111 x u y z)))).symm).trans (((p23 x u ((d y z) ◇ ((x ◇ z) ◇ x)))).trans ((congrArg (fun _t : G => ((d u ((d y z) ◇ ((x ◇ z) ◇ x))) ◇ (_t ◇ x))) ((p8 x y z)))))).trans ((congrArg (fun _t : G => (_t ◇ ((d y z) ◇ x))) ((p111 x u y z))))
  have p136 (x y z : G) : ((x ◇ ((y ◇ (z ◇ x)) ◇ y)) ◇ ((x ◇ x) ◇ x)) = ((y ◇ (z ◇ x)) ◇ y) := by
    exact (((congrArg (fun _t : G => ((x ◇ ((y ◇ (z ◇ x)) ◇ y)) ◇ ((x ◇ _t) ◇ x))) ((p2 y x z)))).symm).trans ((p24 x ((y ◇ (z ◇ x)) ◇ y) y))
  have p137 (x y z : G) : (d (x ◇ y) y) = ((x ◇ (z ◇ (x ◇ y))) ◇ x) := by
    exact (((congrArg (fun _t : G => (d (x ◇ y) _t)) ((p24 x y z)))).symm).trans ((p4 (x ◇ y) ((x ◇ (z ◇ (x ◇ y))) ◇ x)))
  have p147 (x y z : G) : ((d x y) ◇ ((y ◇ (z ◇ (y ◇ ((d y x) ◇ x)))) ◇ y)) = ((d y x) ◇ x) := by
    exact (((congrArg (fun _t : G => (_t ◇ ((y ◇ (z ◇ (y ◇ ((d y x) ◇ x)))) ◇ y))) (((p35 x y)).symm))).symm).trans ((p24 y ((d y x) ◇ x) z))
  have p155 (x y z : G) : ((((x ◇ (y ◇ z)) ◇ x) ◇ (z ◇ x)) ◇ ((((x ◇ (y ◇ z)) ◇ x) ◇ ((x ◇ (y ◇ z)) ◇ x)) ◇ ((x ◇ (y ◇ z)) ◇ x))) = (z ◇ x) := by
    exact (((congrArg (fun _t : G => ((((x ◇ (y ◇ z)) ◇ x) ◇ (z ◇ x)) ◇ ((((x ◇ (y ◇ z)) ◇ x) ◇ _t) ◇ ((x ◇ (y ◇ z)) ◇ x)))) ((p7 x y z)))).symm).trans ((p24 ((x ◇ (y ◇ z)) ◇ x) (z ◇ x) x))
  have p159 (x y z : G) : (((d x y) ◇ ((z ◇ y) ◇ z)) ◇ (((d x y) ◇ (d x y)) ◇ (d x y))) = ((z ◇ y) ◇ z) := by
    exact (((congrArg (fun _t : G => (((d x y) ◇ ((z ◇ y) ◇ z)) ◇ (((d x y) ◇ _t) ◇ (d x y)))) ((p8 z x y)))).symm).trans ((p24 (d x y) ((z ◇ y) ◇ z) z))
  have p175 (u w x y z : G) : (x ◇ (((y ◇ ((z ◇ (u ◇ y)) ◇ z)) ◇ ((w ◇ y) ◇ w)) ◇ ((x ◇ (d z y)) ◇ x))) = ((y ◇ ((z ◇ (u ◇ y)) ◇ z)) ◇ ((w ◇ y) ◇ w)) := by
    exact (((congrArg (fun _t : G => (x ◇ (((y ◇ ((z ◇ (u ◇ y)) ◇ z)) ◇ ((w ◇ y) ◇ w)) ◇ ((x ◇ _t) ◇ x)))) (((p9 z y u)).symm))).symm).trans ((p10 u w x y z))
  have p203 (x y : G) : ((d x y) ◇ (y ◇ (((d y x) ◇ x) ◇ (d x y)))) = y := by
    exact (((congrArg (fun _t : G => ((d x y) ◇ (y ◇ (_t ◇ (d x y))))) ((p46 x y)))).symm).trans ((p2 (d x y) y (y ◇ y)))
  have p206 (x y : G) : (d (d x y) ((d y x) ◇ x)) = ((y ◇ y) ◇ y) := by
    exact (((congrArg (fun _t : G => (d (d x y) _t)) ((p46 x y)))).symm).trans ((p4 (d x y) ((y ◇ y) ◇ y)))
  have p210 (x y z : G) : (x ◇ (((d y x) ◇ ((x ◇ x) ◇ x)) ◇ (d y x))) = (z ◇ ((x ◇ (((d x y) ◇ y) ◇ (d y x))) ◇ ((z ◇ x) ◇ z))) := by
    exact ((((congrArg (fun _t : G => (z ◇ ((x ◇ (_t ◇ (d y x))) ◇ ((z ◇ x) ◇ z)))) ((p46 y x)))).symm).trans ((p6 (x ◇ x) z x (d y x)))).symm
  have p222 (x y z : G) : ((d x y) ◇ y) = ((y ◇ (z ◇ x)) ◇ y) := by
    exact ((((p136 x y z)).symm).trans ((((congrArg (fun _t : G => (_t ◇ ((x ◇ x) ◇ x))) ((p9 y x z)))).symm).trans ((p46 y x)))).symm
  have p232 (x y : G) : (((d x y) ◇ ((y ◇ y) ◇ y)) ◇ (d x y)) = (((d y x) ◇ x) ◇ (d x y)) := by
    exact (((p7 (d x y) (y ◇ y) y)).symm).trans (((p7 (d x y) (y ◇ y) y)).trans ((congrArg (fun _t : G => (_t ◇ (d x y))) ((p46 x y)))))
  have p239 (x y : G) : ((d x y) ◇ ((((d y x) ◇ ((x ◇ x) ◇ x)) ◇ y) ◇ ((d y x) ◇ ((x ◇ x) ◇ x)))) = ((d x y) ◇ (y ◇ ((d x y) ◇ y))) := by
    exact (((p23 ((d y x) ◇ ((x ◇ x) ◇ x)) x y)).symm).trans ((((congrArg (fun _t : G => (d _t (d x y))) (((p46 y x)).symm))).symm).trans ((p47 (d x y) y)))
  have p245 (x y z : G) : ((d (d x y) z) ◇ z) = ((z ◇ y) ◇ z) := by
    exact ((((p159 x y z)).symm).trans ((((congrArg (fun _t : G => (_t ◇ (((d x y) ◇ (d x y)) ◇ (d x y)))) ((p23 z x y)))).symm).trans ((p46 z (d x y))))).symm
  have p247 (x y z : G) : (((d x y) ◇ ((y ◇ y) ◇ y)) ◇ (((d x y) ◇ (z ◇ ((d y x) ◇ x))) ◇ (d x y))) = ((y ◇ y) ◇ y) := by
    exact (((congrArg (fun _t : G => (((d x y) ◇ ((y ◇ y) ◇ y)) ◇ (((d x y) ◇ (z ◇ _t)) ◇ (d x y)))) ((p46 x y)))).symm).trans ((p24 (d x y) ((y ◇ y) ◇ y) z))
  have p258 (x y z : G) : ((x ◇ (((d y x) ◇ ((x ◇ x) ◇ x)) ◇ (d y x))) ◇ ((z ◇ x) ◇ z)) = ((x ◇ (((d x y) ◇ y) ◇ (d y x))) ◇ ((z ◇ x) ◇ z)) := by
    exact (((p10 (x ◇ x) z a x (d y x))).symm).trans (((p10 (x ◇ x) z a x (d y x))).trans ((congrArg (fun _t : G => ((x ◇ (_t ◇ (d y x))) ◇ ((z ◇ x) ◇ z))) ((p46 y x)))))
  have p267 (u x y z : G) : ((x ◇ (((d (y ◇ x) z) ◇ ((z ◇ z) ◇ z)) ◇ (d z (y ◇ x)))) ◇ ((u ◇ x) ◇ u)) = ((x ◇ (((d z (y ◇ x)) ◇ (y ◇ x)) ◇ (d z (y ◇ x)))) ◇ ((u ◇ x) ◇ u)) := by
    exact ((((p10 y u a x (d z (y ◇ x)))).symm).trans (((p10 y u a x (d z (y ◇ x)))).trans ((congrArg (fun _t : G => ((x ◇ (_t ◇ (d z (y ◇ x)))) ◇ ((u ◇ x) ◇ u))) (((p46 (y ◇ x) z)).symm))))).symm
  have p275 (x y z : G) : ((d ((x ◇ (y ◇ z)) ◇ x) x) ◇ x) = (z ◇ x) := by
    exact ((p222 ((x ◇ (y ◇ z)) ◇ x) x z)).trans ((congrArg (fun _t : G => (_t ◇ x)) ((p2 x z y))))
  have p276 (x y z : G) : (d (d x y) ((y ◇ (z ◇ x)) ◇ y)) = y := by
    exact (((congrArg (fun _t : G => (d (d x y) _t)) ((p222 x y z)))).symm).trans ((p4 (d x y) y))
  have p277 (x y z : G) : (d (x ◇ (y ◇ z)) ((d z x) ◇ x)) = x := by
    exact (((congrArg (fun _t : G => (d (x ◇ (y ◇ z)) _t)) (((p222 z x y)).symm))).symm).trans ((p4 (x ◇ (y ◇ z)) x))
  have p279 (u w x y z : G) : (x ◇ (((d y (z ◇ x)) ◇ (z ◇ x)) ◇ (d y (z ◇ x)))) = (u ◇ ((x ◇ ((((z ◇ x) ◇ (w ◇ y)) ◇ (z ◇ x)) ◇ (d y (z ◇ x)))) ◇ ((u ◇ x) ◇ u))) := by
    exact ((((congrArg (fun _t : G => (u ◇ ((x ◇ (_t ◇ (d y (z ◇ x)))) ◇ ((u ◇ x) ◇ u)))) ((p222 y (z ◇ x) w)))).symm).trans ((p6 z u x (d y (z ◇ x))))).symm
  have p300 (x y : G) : ((d (x ◇ (y ◇ x)) (y ◇ x)) ◇ (y ◇ x)) = (y ◇ (y ◇ x)) := by
    exact ((p222 (x ◇ (y ◇ x)) (y ◇ x) y)).trans ((congrArg (fun _t : G => (_t ◇ (y ◇ x))) ((p38 y x))))
  have p309 (x y z : G) : ((d (x ◇ y) y) ◇ y) = (((y ◇ (z ◇ x)) ◇ y) ◇ y) := by
    exact ((p222 (x ◇ y) y ((y ◇ (z ◇ x)) ◇ y))).trans ((congrArg (fun _t : G => (_t ◇ y)) ((p7 y z x))))
  have p319 (x y z : G) : ((d ((x ◇ y) ◇ x) x) ◇ x) = ((d z y) ◇ x) := by
    exact ((p222 ((x ◇ y) ◇ x) x (d z y))).trans ((congrArg (fun _t : G => (_t ◇ x)) ((p8 x z y))))
  have p350 (u w x y z : G) : (((x ◇ ((y ◇ (z ◇ x)) ◇ y)) ◇ ((u ◇ x) ◇ u)) ◇ w) = (((y ◇ (z ◇ x)) ◇ y) ◇ w) := by
    exact ((((p275 w x ((y ◇ (z ◇ x)) ◇ y))).symm).trans (((p222 ((w ◇ (x ◇ ((y ◇ (z ◇ x)) ◇ y))) ◇ w) w ((x ◇ ((y ◇ (z ◇ x)) ◇ y)) ◇ ((u ◇ x) ◇ u)))).trans ((congrArg (fun _t : G => (_t ◇ w)) ((p10 z u w x y)))))).symm
  have p375 (u x y z : G) : ((x ◇ ((y ◇ (z ◇ x)) ◇ y)) ◇ ((u ◇ x) ◇ u)) = ((y ◇ (z ◇ x)) ◇ y) := by
    exact ((((p20 x a y z)).symm).trans ((((congrArg (fun _t : G => (a ◇ _t)) ((p350 u ((a ◇ (d y x)) ◇ a) x y z)))).symm).trans ((p175 z u a x y)))).symm
  have p404 (u x y z : G) : (((d x (y ◇ z)) ◇ (y ◇ z)) ◇ (d x (y ◇ z))) = ((z ◇ (((d (y ◇ z) x) ◇ ((x ◇ x) ◇ x)) ◇ (d x (y ◇ z)))) ◇ ((u ◇ z) ◇ u)) := by
    exact (((p267 u z y x)).trans ((p375 u z (d x (y ◇ z)) y))).symm
  have p409 (x y z : G) : (((d x y) ◇ ((y ◇ y) ◇ y)) ◇ (d x y)) = ((y ◇ (((d y x) ◇ x) ◇ (d x y))) ◇ ((z ◇ y) ◇ z)) := by
    exact (((p375 z y (d x y) (y ◇ y))).symm).trans ((p258 y x z))
  have p436 (u x y z : G) : ((d (((d x y) ◇ ((z ◇ y) ◇ z)) ◇ ((u ◇ (d x y)) ◇ u)) z) ◇ z) = ((d x y) ◇ z) := by
    exact (((congrArg (fun _t : G => ((d _t z) ◇ z)) ((p111 z u x y)))).symm).trans (((p245 u ((d x y) ◇ ((z ◇ y) ◇ z)) z)).trans ((congrArg (fun _t : G => (_t ◇ z)) ((p8 z x y)))))
  have p441 (u x y z : G) : ((x ◇ (y ◇ (d z u))) ◇ x) = ((x ◇ u) ◇ x) := by
    exact ((((p245 z u x)).symm).trans ((p222 (d z u) x y))).symm
  have p443 (x y z : G) : (((d x y) ◇ y) ◇ (d x y)) = (((y ◇ (z ◇ x)) ◇ y) ◇ (d x y)) := by
    exact (((p441 y (d x y) ((d a y) ◇ y) a)).symm).trans ((((congrArg (fun _t : G => (_t ◇ (d x y))) ((p23 (d a y) x y)))).symm).trans (((p245 a y (d x y))).trans ((congrArg (fun _t : G => (_t ◇ (d x y))) ((p222 x y z))))))
  have p455 (x y : G) : (d (d ((d x y) ◇ y) y) (x ◇ y)) = y := by
    exact (((congrArg (fun _t : G => (d (d ((d x y) ◇ y) y) (_t ◇ y))) ((p21 y x)))).symm).trans ((p276 ((d x y) ◇ y) y x))
  have p537 (x y z : G) : (d ((x ◇ (y ◇ z)) ◇ x) ((d (z ◇ x) x) ◇ x)) = x := by
    exact (((congrArg (fun _t : G => (d _t ((d (z ◇ x) x) ◇ x))) ((p7 x y z)))).symm).trans ((p277 x ((x ◇ (y ◇ z)) ◇ x) (z ◇ x)))
  have p545 (x y z : G) : (d (x ◇ ((d y z) ◇ ((z ◇ z) ◇ z))) ((d y x) ◇ x)) = x := by
    exact (((congrArg (fun _t : G => (d (x ◇ _t) ((d y x) ◇ x))) (((p46 y z)).symm))).symm).trans ((p277 x (d z y) y))
  have p578 (x y : G) : ((x ◇ y) ◇ ((d ((d x y) ◇ y) y) ◇ (y ◇ (x ◇ y)))) = (d ((d x y) ◇ y) y) := by
    exact (((congrArg (fun _t : G => ((x ◇ y) ◇ ((d ((d x y) ◇ y) y) ◇ (_t ◇ (x ◇ y))))) ((p455 x y)))).symm).trans ((p21 (x ◇ y) (d ((d x y) ◇ y) y)))
  have p595 (x y z : G) : (d (d (x ◇ ((d y x) ◇ x)) ((d y x) ◇ x)) ((x ◇ (z ◇ y)) ◇ ((d y x) ◇ x))) = ((d y x) ◇ x) := by
    exact (((congrArg (fun _t : G => (d (d (_t ◇ ((d y x) ◇ x)) ((d y x) ◇ x)) ((x ◇ (z ◇ y)) ◇ ((d y x) ◇ x)))) ((p277 x z y)))).symm).trans ((p455 (x ◇ (z ◇ y)) ((d y x) ◇ x)))
  have p609 (x y z : G) : ((x ◇ (y ◇ (x ◇ ((d x z) ◇ z)))) ◇ x) = ((x ◇ x) ◇ x) := by
    exact ((((p206 z x)).symm).trans ((((congrArg (fun _t : G => (d _t ((d x z) ◇ z))) (((p35 z x)).symm))).symm).trans ((p137 x ((d x z) ◇ z) y)))).symm
  have p610 (x y : G) : (d ((d x y) ◇ y) y) = (((d x y) ◇ (d y x)) ◇ (d x y)) := by
    exact ((p137 (d x y) y x)).trans ((congrArg (fun _t : G => (((d x y) ◇ _t) ◇ (d x y))) (((p35 y x)).symm)))
  have p627 (x y z : G) : (d ((d x y) ◇ ((z ◇ y) ◇ z)) ((z ◇ y) ◇ z)) = (((d x y) ◇ (d x y)) ◇ (d x y)) := by
    exact ((p137 (d x y) ((z ◇ y) ◇ z) z)).trans ((congrArg (fun _t : G => (((d x y) ◇ _t) ◇ (d x y))) ((p8 z x y))))
  have p638 (x y z : G) : (((d x y) ◇ (d x y)) ◇ (d x y)) = (((d x y) ◇ (z ◇ ((d y x) ◇ x))) ◇ (d x y)) := by
    exact (((p627 x y y)).symm).trans (((p137 (d x y) ((y ◇ y) ◇ y) z)).trans ((congrArg (fun _t : G => (((d x y) ◇ (z ◇ _t)) ◇ (d x y))) ((p46 x y)))))
  have p641 (x y z : G) : (((d x y) ◇ (z ◇ ((d y x) ◇ ((x ◇ x) ◇ x)))) ◇ (d x y)) = (((d x y) ◇ (d y x)) ◇ (d x y)) := by
    exact ((((p610 x y)).symm).trans (((p137 (d x y) y z)).trans ((congrArg (fun _t : G => (((d x y) ◇ (z ◇ _t)) ◇ (d x y))) (((p46 y x)).symm))))).symm
  have p664 (x : G) : ((x ◇ x) ◇ x) = x := by
    exact (((p609 x a x)).symm).trans ((((p137 x ((d x x) ◇ x) a)).symm).trans ((p277 x (d x x) x)))
  have p680 (x y : G) : ((d x y) ◇ y) = ((d y x) ◇ x) := by
    exact (((congrArg (fun _t : G => ((d x y) ◇ _t)) ((p664 y)))).symm).trans ((((congrArg (fun _t : G => ((d x y) ◇ _t)) ((p609 y a x)))).symm).trans ((p147 x y a)))
  have p686 (x y : G) : ((x ◇ y) ◇ ((((d x y) ◇ (d y x)) ◇ (d x y)) ◇ (y ◇ (x ◇ y)))) = (((d x y) ◇ (d y x)) ◇ (d x y)) := by
    exact ((((congrArg (fun _t : G => ((x ◇ y) ◇ (_t ◇ (y ◇ (x ◇ y))))) ((p610 x y)))).symm).trans ((p578 x y))).trans ((p610 x y))
  have p693 (x y z : G) : (((d x y) ◇ (z ◇ ((d y x) ◇ x))) ◇ (d x y)) = (((d x y) ◇ (d y x)) ◇ (d x y)) := by
    exact (((congrArg (fun _t : G => (((d x y) ◇ (z ◇ ((d y x) ◇ _t))) ◇ (d x y))) ((p664 x)))).symm).trans ((p641 x y z))
  have p696 (x y : G) : (((d x y) ◇ (d y x)) ◇ (d x y)) = (d x y) := by
    exact (((((p664 (d x y))).symm).trans ((p638 x y a))).trans ((p693 x y a))).symm
  have p709 (x y z : G) : (d (x ◇ ((d y z) ◇ z)) ((d y x) ◇ x)) = x := by
    exact (((congrArg (fun _t : G => (d (x ◇ ((d y z) ◇ _t)) ((d y x) ◇ x))) ((p664 z)))).symm).trans ((p545 x y z))
  have p729 (x y z : G) : (((d x y) ◇ y) ◇ (d x y)) = ((y ◇ (((d y x) ◇ x) ◇ (d x y))) ◇ ((z ◇ y) ◇ z)) := by
    exact (((congrArg (fun _t : G => (((d x y) ◇ _t) ◇ (d x y))) ((p664 y)))).symm).trans ((p409 x y z))
  have p732 (u x y z : G) : (((d x (y ◇ z)) ◇ (y ◇ z)) ◇ (d x (y ◇ z))) = ((z ◇ (((d (y ◇ z) x) ◇ x) ◇ (d x (y ◇ z)))) ◇ ((u ◇ z) ◇ u)) := by
    exact ((p404 u x y z)).trans ((congrArg (fun _t : G => ((z ◇ (((d (y ◇ z) x) ◇ _t) ◇ (d x (y ◇ z)))) ◇ ((u ◇ z) ◇ u))) ((p664 x))))
  have p744 (x y : G) : (((d x y) ◇ y) ◇ (d x y)) = y := by
    exact ((((congrArg (fun _t : G => (((d x y) ◇ y) ◇ _t)) ((p696 x y)))).symm).trans ((((congrArg (fun _t : G => (((d x y) ◇ y) ◇ _t)) ((p693 x y a)))).symm).trans ((((congrArg (fun _t : G => (((d x y) ◇ _t) ◇ (((d x y) ◇ (a ◇ ((d y x) ◇ x))) ◇ (d x y)))) ((p664 y)))).symm).trans ((p247 x y a))))).trans ((p664 y))
  have p748 (x y : G) : ((d x y) ◇ ((((d y x) ◇ x) ◇ y) ◇ ((d y x) ◇ x))) = ((d x y) ◇ (y ◇ ((d x y) ◇ y))) := by
    exact (((congrArg (fun _t : G => ((d x y) ◇ ((((d y x) ◇ x) ◇ y) ◇ ((d y x) ◇ _t)))) ((p664 x)))).symm).trans ((((congrArg (fun _t : G => ((d x y) ◇ ((((d y x) ◇ _t) ◇ y) ◇ ((d y x) ◇ ((x ◇ x) ◇ x))))) ((p664 x)))).symm).trans ((p239 x y)))
  have p751 (x y : G) : (((d x y) ◇ y) ◇ (d y x)) = x := by
    exact ((((p744 y x)).symm).trans ((((congrArg (fun _t : G => (((d y x) ◇ _t) ◇ (d y x))) ((p664 x)))).symm).trans ((p232 y x)))).symm
  have p762 (x y : G) : (x ◇ ((y ◇ y) ◇ ((x ◇ y) ◇ x))) = (y ◇ y) := by
    exact (((((congrArg (fun _t : G => (y ◇ _t)) ((p744 a y)))).symm).trans ((((congrArg (fun _t : G => (y ◇ (((d a y) ◇ _t) ◇ (d a y)))) ((p664 y)))).symm).trans ((p210 y a x)))).trans ((congrArg (fun _t : G => (x ◇ ((y ◇ _t) ◇ ((x ◇ y) ◇ x)))) ((p751 y a))))).symm
  have p767 (x y z : G) : ((((x ◇ (y ◇ z)) ◇ x) ◇ (z ◇ x)) ◇ ((x ◇ (y ◇ z)) ◇ x)) = (z ◇ x) := by
    exact (((congrArg (fun _t : G => ((((x ◇ (y ◇ z)) ◇ x) ◇ (z ◇ x)) ◇ _t)) ((p664 ((x ◇ (y ◇ z)) ◇ x))))).symm).trans ((p155 x y z))
  have p769 (x y z : G) : (d ((x ◇ (y ◇ z)) ◇ x) ((d x (z ◇ x)) ◇ (z ◇ x))) = x := by
    exact (((congrArg (fun _t : G => (d ((x ◇ (y ◇ z)) ◇ x) _t)) ((p680 (z ◇ x) x)))).symm).trans ((p537 x y z))
  have p773 (u x y z : G) : (((((d x y) ◇ ((z ◇ y) ◇ z)) ◇ ((u ◇ (d x y)) ◇ u)) ◇ ((d x y) ◇ z)) ◇ (((d x y) ◇ ((z ◇ y) ◇ z)) ◇ ((u ◇ (d x y)) ◇ u))) = ((d x y) ◇ z) := by
    exact (((congrArg (fun _t : G => (_t ◇ (((d x y) ◇ ((z ◇ y) ◇ z)) ◇ ((u ◇ (d x y)) ◇ u)))) ((p133 u z x y)))).symm).trans ((((p680 (((d x y) ◇ ((z ◇ y) ◇ z)) ◇ ((u ◇ (d x y)) ◇ u)) z)).symm).trans ((p436 u x y z)))
  have p777 (x y z : G) : ((d x ((x ◇ y) ◇ x)) ◇ ((x ◇ y) ◇ x)) = ((d z y) ◇ x) := by
    exact (((p680 ((x ◇ y) ◇ x) x)).symm).trans ((p319 x y z))
  have p778 (x y z : G) : ((d x (y ◇ x)) ◇ (y ◇ x)) = (((x ◇ (z ◇ y)) ◇ x) ◇ x) := by
    exact (((p680 (y ◇ x) x)).symm).trans ((p309 y x z))
  have p779 (x y : G) : (((x ◇ (y ◇ x)) ◇ (y ◇ (y ◇ x))) ◇ (x ◇ (y ◇ x))) = (y ◇ (y ◇ x)) := by
    exact (((congrArg (fun _t : G => (_t ◇ (x ◇ (y ◇ x)))) ((p61 y x)))).symm).trans ((((p680 (x ◇ (y ◇ x)) (y ◇ x))).symm).trans ((p300 x y)))
  have p790 (x y : G) : ((x ◇ y) ◇ ((d x y) ◇ (y ◇ (x ◇ y)))) = (d x y) := by
    exact ((((congrArg (fun _t : G => ((x ◇ y) ◇ (_t ◇ (y ◇ (x ◇ y))))) ((p696 x y)))).symm).trans ((p686 x y))).trans ((p696 x y))
  have p798 (x y z : G) : (d x ((x ◇ (y ◇ z)) ◇ ((d z x) ◇ x))) = ((d z x) ◇ x) := by
    exact (((congrArg (fun _t : G => (d _t ((x ◇ (y ◇ z)) ◇ ((d z x) ◇ x)))) ((p709 x z x)))).symm).trans ((p595 x z y))
  have p799 (x y z : G) : ((x ◇ (y ◇ x)) ◇ ((z ◇ x) ◇ z)) = (y ◇ x) := by
    exact (((((p744 a (y ◇ x))).symm).trans ((p732 z a y x))).trans ((congrArg (fun _t : G => ((x ◇ _t) ◇ ((z ◇ x) ◇ z))) ((p751 (y ◇ x) a))))).symm
  have p800 (x y : G) : ((x ◇ x) ◇ ((y ◇ x) ◇ y)) = x := by
    exact (((((p744 a x)).symm).trans ((p729 a x y))).trans ((congrArg (fun _t : G => ((x ◇ _t) ◇ ((y ◇ x) ◇ y))) ((p751 x a))))).symm
  have p805 (x y z : G) : (((x ◇ (y ◇ z)) ◇ x) ◇ (d z x)) = x := by
    exact ((((p744 z x)).symm).trans ((p443 z x y))).symm
  have p807 (x y z : G) : (x ◇ (y ◇ z)) = (z ◇ (y ◇ z)) := by
    exact ((((((congrArg (fun _t : G => (z ◇ _t)) ((p744 a (y ◇ z))))).symm).trans ((p279 x a z a y))).trans ((congrArg (fun _t : G => (x ◇ ((z ◇ _t) ◇ ((x ◇ z) ◇ x)))) ((p805 (y ◇ z) a a))))).trans ((congrArg (fun _t : G => (x ◇ _t)) ((p799 z y x))))).symm
  have p816 (x : G) : (x ◇ (x ◇ x)) = x := by
    exact (((p807 (d a x) x x)).symm).trans ((((congrArg (fun _t : G => ((d a x) ◇ (x ◇ _t))) ((p751 x a)))).symm).trans ((p203 a x)))
  have p826 (x y : G) : (x ◇ y) = (y ◇ y) := by
    exact (((congrArg (fun _t : G => (x ◇ _t)) ((p800 y x)))).symm).trans ((p762 x y))
  have p834 (x : G) : (d x x) = (x ◇ x) := by
    exact ((((congrArg (fun _t : G => (d x _t)) ((p816 x)))).symm).trans ((((congrArg (fun _t : G => (d x _t)) ((p807 (x ◇ (a ◇ a)) x x)))).symm).trans ((((congrArg (fun _t : G => (d x ((x ◇ (a ◇ a)) ◇ _t))) ((p826 (d a x) x)))).symm).trans ((p798 x a a))))).trans ((p826 (d a x) x))
  have p838 (x y : G) : (d x y) = ((x ◇ y) ◇ ((x ◇ y) ◇ (y ◇ (x ◇ y)))) := by
    exact ((((congrArg (fun _t : G => ((x ◇ y) ◇ _t)) ((p807 (y ◇ (x ◇ y)) y (x ◇ y))))).symm).trans ((((congrArg (fun _t : G => ((x ◇ y) ◇ _t)) ((p826 (d x y) (y ◇ (x ◇ y)))))).symm).trans ((p790 x y)))).symm
  have p843 (x y : G) : ((x ◇ y) ◇ (y ◇ (x ◇ y))) = (x ◇ (x ◇ y)) := by
    exact (((p807 (y ◇ (x ◇ y)) y (x ◇ y))).symm).trans ((((p826 ((x ◇ y) ◇ (x ◇ (x ◇ y))) (y ◇ (x ◇ y)))).symm).trans ((((congrArg (fun _t : G => (_t ◇ (y ◇ (x ◇ y)))) ((p807 (y ◇ (x ◇ y)) x (x ◇ y))))).symm).trans ((p779 y x))))
  have p844 (x y : G) : (x ◇ (y ◇ x)) = (x ◇ x) := by
    exact (((((p807 (y ◇ x) y x)).symm).trans ((((p826 ((x ◇ (y ◇ x)) ◇ ((y ◇ x) ◇ (y ◇ (y ◇ x)))) (y ◇ x))).symm).trans ((((congrArg (fun _t : G => (((x ◇ (y ◇ x)) ◇ _t) ◇ (y ◇ x))) ((p807 (x ◇ (y ◇ x)) y (y ◇ x))))).symm).trans ((((congrArg (fun _t : G => (((x ◇ (y ◇ x)) ◇ ((x ◇ (y ◇ x)) ◇ _t)) ◇ (y ◇ x))) ((p843 y x)))).symm).trans ((((congrArg (fun _t : G => (_t ◇ (y ◇ x))) ((p838 x (y ◇ x))))).symm).trans ((p778 x y a))))))).trans ((congrArg (fun _t : G => (_t ◇ x)) ((p826 (x ◇ (a ◇ y)) x))))).trans ((p826 (x ◇ x) x))
  have p845 (x y : G) : ((x ◇ x) ◇ y) = y := by
    exact (((((((((p816 y)).symm).trans ((((p807 (y ◇ y) y y)).symm).trans ((((congrArg (fun _t : G => ((y ◇ y) ◇ _t)) ((p826 (y ◇ x) y)))).symm).trans ((((congrArg (fun _t : G => ((y ◇ _t) ◇ ((y ◇ x) ◇ y))) ((p816 y)))).symm).trans ((((congrArg (fun _t : G => ((y ◇ (y ◇ _t)) ◇ ((y ◇ x) ◇ y))) ((p826 (y ◇ y) y)))).symm).trans ((((congrArg (fun _t : G => ((y ◇ (y ◇ ((y ◇ y) ◇ _t))) ◇ ((y ◇ x) ◇ y))) ((p816 y)))).symm).trans ((((congrArg (fun _t : G => ((y ◇ (_t ◇ ((y ◇ y) ◇ (y ◇ (y ◇ y))))) ◇ ((y ◇ x) ◇ y))) ((p816 y)))).symm).trans ((((congrArg (fun _t : G => ((_t ◇ ((y ◇ (y ◇ y)) ◇ ((y ◇ y) ◇ (y ◇ (y ◇ y))))) ◇ ((y ◇ x) ◇ y))) ((p816 y)))).symm).trans ((((congrArg (fun _t : G => (_t ◇ ((y ◇ x) ◇ y))) ((p838 y (y ◇ y))))).symm).trans ((((congrArg (fun _t : G => ((d y _t) ◇ ((y ◇ x) ◇ y))) ((p826 (y ◇ x) y)))).symm).trans ((p777 y x a)))))))))))).trans ((congrArg (fun _t : G => (_t ◇ y)) ((p838 a x))))).trans ((congrArg (fun _t : G => (((a ◇ x) ◇ ((a ◇ x) ◇ _t)) ◇ y)) ((p844 x a))))).trans ((congrArg (fun _t : G => (((a ◇ x) ◇ _t) ◇ y)) ((p807 (a ◇ x) x x))))).trans ((congrArg (fun _t : G => (((a ◇ x) ◇ _t) ◇ y)) ((p816 x))))).trans ((congrArg (fun _t : G => (_t ◇ y)) ((p826 (a ◇ x) x))))).symm
  have p849 (x y : G) : (x ◇ (y ◇ y)) = x := by
    exact (((((((((congrArg (fun _t : G => (x ◇ _t)) ((p845 x (y ◇ y))))).symm).trans ((((congrArg (fun _t : G => (x ◇ ((x ◇ x) ◇ _t))) ((p826 (y ◇ (a ◇ a)) y)))).symm).trans ((((congrArg (fun _t : G => (x ◇ ((x ◇ x) ◇ ((y ◇ _t) ◇ y)))) ((p826 (a ◇ a) a)))).symm).trans ((((congrArg (fun _t : G => (x ◇ ((x ◇ x) ◇ ((y ◇ ((a ◇ a) ◇ _t)) ◇ y)))) ((p816 a)))).symm).trans ((((congrArg (fun _t : G => (x ◇ ((x ◇ x) ◇ ((y ◇ ((a ◇ a) ◇ _t)) ◇ y)))) ((p807 (a ◇ a) a a)))).symm).trans ((((congrArg (fun _t : G => (x ◇ ((x ◇ x) ◇ ((y ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ _t))) ◇ y)))) ((p844 a a)))).symm).trans ((((congrArg (fun _t : G => (x ◇ ((x ◇ x) ◇ ((y ◇ _t) ◇ y)))) ((p838 a a)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (_t ◇ ((y ◇ (d a a)) ◇ y)))) ((p845 a (x ◇ x))))).symm).trans ((((congrArg (fun _t : G => (x ◇ (((a ◇ a) ◇ _t) ◇ ((y ◇ (d a a)) ◇ y)))) ((p826 (x ◇ a) x)))).symm).trans ((((congrArg (fun _t : G => (x ◇ ((_t ◇ ((x ◇ a) ◇ x)) ◇ ((y ◇ (d a a)) ◇ y)))) ((p826 (a ◇ a) a)))).symm).trans ((((congrArg (fun _t : G => (x ◇ ((((a ◇ a) ◇ _t) ◇ ((x ◇ a) ◇ x)) ◇ ((y ◇ (d a a)) ◇ y)))) ((p816 a)))).symm).trans ((((congrArg (fun _t : G => (x ◇ ((((a ◇ a) ◇ _t) ◇ ((x ◇ a) ◇ x)) ◇ ((y ◇ (d a a)) ◇ y)))) ((p807 (a ◇ a) a a)))).symm).trans ((((congrArg (fun _t : G => (x ◇ ((((a ◇ a) ◇ ((a ◇ a) ◇ _t)) ◇ ((x ◇ a) ◇ x)) ◇ ((y ◇ (d a a)) ◇ y)))) ((p844 a a)))).symm).trans ((((congrArg (fun _t : G => (x ◇ ((_t ◇ ((x ◇ a) ◇ x)) ◇ ((y ◇ (d a a)) ◇ y)))) ((p838 a a)))).symm).trans ((((congrArg (fun _t : G => (_t ◇ (((d a a) ◇ ((x ◇ a) ◇ x)) ◇ ((y ◇ (d a a)) ◇ y)))) ((p845 y x)))).symm).trans ((((congrArg (fun _t : G => (((y ◇ y) ◇ _t) ◇ (((d a a) ◇ ((x ◇ a) ◇ x)) ◇ ((y ◇ (d a a)) ◇ y)))) ((p845 a x)))).symm).trans ((((congrArg (fun _t : G => (((y ◇ y) ◇ (_t ◇ x)) ◇ (((d a a) ◇ ((x ◇ a) ◇ x)) ◇ ((y ◇ (d a a)) ◇ y)))) ((p826 (a ◇ a) a)))).symm).trans ((((congrArg (fun _t : G => (((y ◇ y) ◇ (((a ◇ a) ◇ _t) ◇ x)) ◇ (((d a a) ◇ ((x ◇ a) ◇ x)) ◇ ((y ◇ (d a a)) ◇ y)))) ((p816 a)))).symm).trans ((((congrArg (fun _t : G => (((y ◇ y) ◇ (((a ◇ a) ◇ _t) ◇ x)) ◇ (((d a a) ◇ ((x ◇ a) ◇ x)) ◇ ((y ◇ (d a a)) ◇ y)))) ((p807 (a ◇ a) a a)))).symm).trans ((((congrArg (fun _t : G => (((y ◇ y) ◇ (((a ◇ a) ◇ ((a ◇ a) ◇ _t)) ◇ x)) ◇ (((d a a) ◇ ((x ◇ a) ◇ x)) ◇ ((y ◇ (d a a)) ◇ y)))) ((p844 a a)))).symm).trans ((((congrArg (fun _t : G => (((y ◇ y) ◇ (_t ◇ x)) ◇ (((d a a) ◇ ((x ◇ a) ◇ x)) ◇ ((y ◇ (d a a)) ◇ y)))) ((p838 a a)))).symm).trans ((((congrArg (fun _t : G => ((_t ◇ ((d a a) ◇ x)) ◇ (((d a a) ◇ ((x ◇ a) ◇ x)) ◇ ((y ◇ (d a a)) ◇ y)))) ((p845 x (y ◇ y))))).symm).trans ((((congrArg (fun _t : G => ((((x ◇ x) ◇ _t) ◇ ((d a a) ◇ x)) ◇ (((d a a) ◇ ((x ◇ a) ◇ x)) ◇ ((y ◇ (d a a)) ◇ y)))) ((p826 (y ◇ (a ◇ a)) y)))).symm).trans ((((congrArg (fun _t : G => ((((x ◇ x) ◇ ((y ◇ _t) ◇ y)) ◇ ((d a a) ◇ x)) ◇ (((d a a) ◇ ((x ◇ a) ◇ x)) ◇ ((y ◇ (d a a)) ◇ y)))) ((p826 (a ◇ a) a)))).symm).trans ((((congrArg (fun _t : G => ((((x ◇ x) ◇ ((y ◇ ((a ◇ a) ◇ _t)) ◇ y)) ◇ ((d a a) ◇ x)) ◇ (((d a a) ◇ ((x ◇ a) ◇ x)) ◇ ((y ◇ (d a a)) ◇ y)))) ((p816 a)))).symm).trans ((((congrArg (fun _t : G => ((((x ◇ x) ◇ ((y ◇ ((a ◇ a) ◇ _t)) ◇ y)) ◇ ((d a a) ◇ x)) ◇ (((d a a) ◇ ((x ◇ a) ◇ x)) ◇ ((y ◇ (d a a)) ◇ y)))) ((p807 (a ◇ a) a a)))).symm).trans ((((congrArg (fun _t : G => ((((x ◇ x) ◇ ((y ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ _t))) ◇ y)) ◇ ((d a a) ◇ x)) ◇ (((d a a) ◇ ((x ◇ a) ◇ x)) ◇ ((y ◇ (d a a)) ◇ y)))) ((p844 a a)))).symm).trans ((((congrArg (fun _t : G => ((((x ◇ x) ◇ ((y ◇ _t) ◇ y)) ◇ ((d a a) ◇ x)) ◇ (((d a a) ◇ ((x ◇ a) ◇ x)) ◇ ((y ◇ (d a a)) ◇ y)))) ((p838 a a)))).symm).trans ((((congrArg (fun _t : G => (((_t ◇ ((y ◇ (d a a)) ◇ y)) ◇ ((d a a) ◇ x)) ◇ (((d a a) ◇ ((x ◇ a) ◇ x)) ◇ ((y ◇ (d a a)) ◇ y)))) ((p845 a (x ◇ x))))).symm).trans ((((congrArg (fun _t : G => (((((a ◇ a) ◇ _t) ◇ ((y ◇ (d a a)) ◇ y)) ◇ ((d a a) ◇ x)) ◇ (((d a a) ◇ ((x ◇ a) ◇ x)) ◇ ((y ◇ (d a a)) ◇ y)))) ((p826 (x ◇ a) x)))).symm).trans ((((congrArg (fun _t : G => ((((_t ◇ ((x ◇ a) ◇ x)) ◇ ((y ◇ (d a a)) ◇ y)) ◇ ((d a a) ◇ x)) ◇ (((d a a) ◇ ((x ◇ a) ◇ x)) ◇ ((y ◇ (d a a)) ◇ y)))) ((p826 (a ◇ a) a)))).symm).trans ((((congrArg (fun _t : G => ((((((a ◇ a) ◇ _t) ◇ ((x ◇ a) ◇ x)) ◇ ((y ◇ (d a a)) ◇ y)) ◇ ((d a a) ◇ x)) ◇ (((d a a) ◇ ((x ◇ a) ◇ x)) ◇ ((y ◇ (d a a)) ◇ y)))) ((p816 a)))).symm).trans ((((congrArg (fun _t : G => ((((((a ◇ a) ◇ _t) ◇ ((x ◇ a) ◇ x)) ◇ ((y ◇ (d a a)) ◇ y)) ◇ ((d a a) ◇ x)) ◇ (((d a a) ◇ ((x ◇ a) ◇ x)) ◇ ((y ◇ (d a a)) ◇ y)))) ((p807 (a ◇ a) a a)))).symm).trans ((((congrArg (fun _t : G => ((((((a ◇ a) ◇ ((a ◇ a) ◇ _t)) ◇ ((x ◇ a) ◇ x)) ◇ ((y ◇ (d a a)) ◇ y)) ◇ ((d a a) ◇ x)) ◇ (((d a a) ◇ ((x ◇ a) ◇ x)) ◇ ((y ◇ (d a a)) ◇ y)))) ((p844 a a)))).symm).trans ((((congrArg (fun _t : G => ((((_t ◇ ((x ◇ a) ◇ x)) ◇ ((y ◇ (d a a)) ◇ y)) ◇ ((d a a) ◇ x)) ◇ (((d a a) ◇ ((x ◇ a) ◇ x)) ◇ ((y ◇ (d a a)) ◇ y)))) ((p838 a a)))).symm).trans ((p773 y a a x))))))))))))))))))))))))))))))))))))).trans ((congrArg (fun _t : G => (_t ◇ x)) ((p838 a a))))).trans ((congrArg (fun _t : G => (((a ◇ a) ◇ ((a ◇ a) ◇ _t)) ◇ x)) ((p844 a a))))).trans ((congrArg (fun _t : G => (((a ◇ a) ◇ _t) ◇ x)) ((p807 (a ◇ a) a a))))).trans ((congrArg (fun _t : G => (((a ◇ a) ◇ _t) ◇ x)) ((p816 a))))).trans ((congrArg (fun _t : G => (_t ◇ x)) ((p826 (a ◇ a) a))))).trans ((p845 a x))
  have p850 (x : G) : (x ◇ x) = x := by
    exact (((p849 (x ◇ x) x)).symm).trans ((((p834 (x ◇ x))).symm).trans ((((congrArg (fun _t : G => (d (x ◇ x) _t)) ((p844 x a)))).symm).trans ((((congrArg (fun _t : G => (d (x ◇ x) _t)) ((p807 (x ◇ x) a x)))).symm).trans ((((congrArg (fun _t : G => (d (x ◇ x) (_t ◇ (a ◇ x)))) ((p849 (x ◇ x) x)))).symm).trans ((((congrArg (fun _t : G => (d (x ◇ x) (((x ◇ x) ◇ _t) ◇ (a ◇ x)))) ((p844 x a)))).symm).trans ((((congrArg (fun _t : G => (d (x ◇ x) (((x ◇ x) ◇ _t) ◇ (a ◇ x)))) ((p807 (x ◇ x) a x)))).symm).trans ((((congrArg (fun _t : G => (d (x ◇ x) (((x ◇ x) ◇ ((x ◇ x) ◇ _t)) ◇ (a ◇ x)))) ((p849 (a ◇ x) x)))).symm).trans ((((congrArg (fun _t : G => (d (x ◇ x) (((x ◇ x) ◇ ((x ◇ x) ◇ ((a ◇ x) ◇ _t))) ◇ (a ◇ x)))) ((p844 x a)))).symm).trans ((((congrArg (fun _t : G => (d (x ◇ x) (((x ◇ x) ◇ (_t ◇ ((a ◇ x) ◇ (x ◇ (a ◇ x))))) ◇ (a ◇ x)))) ((p844 x a)))).symm).trans ((((congrArg (fun _t : G => (d (x ◇ x) ((_t ◇ ((x ◇ (a ◇ x)) ◇ ((a ◇ x) ◇ (x ◇ (a ◇ x))))) ◇ (a ◇ x)))) ((p844 x a)))).symm).trans ((((congrArg (fun _t : G => (d (x ◇ x) (_t ◇ (a ◇ x)))) ((p838 x (a ◇ x))))).symm).trans ((((congrArg (fun _t : G => (d _t ((d x (a ◇ x)) ◇ (a ◇ x)))) ((p826 (x ◇ (a ◇ a)) x)))).symm).trans ((p769 x a a))))))))))))))
  have p851 (x y : G) : (x ◇ y) = y := by
    exact ((((p850 y)).symm).trans ((((congrArg (fun _t : G => (y ◇ _t)) ((p850 y)))).symm).trans ((((congrArg (fun _t : G => (y ◇ _t)) ((p826 (y ◇ (a ◇ x)) y)))).symm).trans ((((congrArg (fun _t : G => (_t ◇ ((y ◇ (a ◇ x)) ◇ y))) ((p850 y)))).symm).trans ((((congrArg (fun _t : G => (_t ◇ ((y ◇ (a ◇ x)) ◇ y))) ((p844 y x)))).symm).trans ((((congrArg (fun _t : G => ((_t ◇ (x ◇ y)) ◇ ((y ◇ (a ◇ x)) ◇ y))) ((p850 y)))).symm).trans ((((congrArg (fun _t : G => ((_t ◇ (x ◇ y)) ◇ ((y ◇ (a ◇ x)) ◇ y))) ((p826 (y ◇ (a ◇ x)) y)))).symm).trans ((p767 y a x))))))))).symm
  have p852 (x y : G) : x = y := by
    exact ((((((((((((((((((((p851 y x)).symm).trans ((((congrArg (fun _t : G => (y ◇ _t)) ((p851 y x)))).symm).trans ((((congrArg (fun _t : G => (y ◇ (y ◇ _t))) ((p850 x)))).symm).trans ((((congrArg (fun _t : G => (y ◇ (y ◇ (_t ◇ x)))) ((p850 x)))).symm).trans ((((congrArg (fun _t : G => (y ◇ (y ◇ ((x ◇ _t) ◇ x)))) ((p850 x)))).symm).trans ((((congrArg (fun _t : G => (y ◇ (y ◇ ((x ◇ (x ◇ _t)) ◇ x)))) ((p850 x)))).symm).trans ((((congrArg (fun _t : G => (y ◇ (y ◇ ((x ◇ (x ◇ (x ◇ _t))) ◇ x)))) ((p851 y x)))).symm).trans ((((congrArg (fun _t : G => (y ◇ (y ◇ ((x ◇ (_t ◇ (x ◇ (y ◇ x)))) ◇ x)))) ((p851 y x)))).symm).trans ((((congrArg (fun _t : G => (y ◇ (y ◇ ((_t ◇ ((y ◇ x) ◇ (x ◇ (y ◇ x)))) ◇ x)))) ((p851 y x)))).symm).trans ((((congrArg (fun _t : G => (y ◇ (y ◇ (_t ◇ x)))) ((p838 y x)))).symm).trans ((((congrArg (fun _t : G => (y ◇ (_t ◇ ((d y x) ◇ x)))) ((p851 x y)))).symm).trans ((((congrArg (fun _t : G => (y ◇ ((_t ◇ y) ◇ ((d y x) ◇ x)))) ((p850 x)))).symm).trans ((((congrArg (fun _t : G => (y ◇ (((_t ◇ x) ◇ y) ◇ ((d y x) ◇ x)))) ((p850 x)))).symm).trans ((((congrArg (fun _t : G => (y ◇ ((((x ◇ _t) ◇ x) ◇ y) ◇ ((d y x) ◇ x)))) ((p850 x)))).symm).trans ((((congrArg (fun _t : G => (y ◇ ((((x ◇ (x ◇ _t)) ◇ x) ◇ y) ◇ ((d y x) ◇ x)))) ((p850 x)))).symm).trans ((((congrArg (fun _t : G => (y ◇ ((((x ◇ (x ◇ (x ◇ _t))) ◇ x) ◇ y) ◇ ((d y x) ◇ x)))) ((p851 y x)))).symm).trans ((((congrArg (fun _t : G => (y ◇ ((((x ◇ (_t ◇ (x ◇ (y ◇ x)))) ◇ x) ◇ y) ◇ ((d y x) ◇ x)))) ((p851 y x)))).symm).trans ((((congrArg (fun _t : G => (y ◇ ((((_t ◇ ((y ◇ x) ◇ (x ◇ (y ◇ x)))) ◇ x) ◇ y) ◇ ((d y x) ◇ x)))) ((p851 y x)))).symm).trans ((((congrArg (fun _t : G => (y ◇ (((_t ◇ x) ◇ y) ◇ ((d y x) ◇ x)))) ((p838 y x)))).symm).trans ((((congrArg (fun _t : G => (_t ◇ ((((d y x) ◇ x) ◇ y) ◇ ((d y x) ◇ x)))) ((p850 y)))).symm).trans ((((congrArg (fun _t : G => ((y ◇ _t) ◇ ((((d y x) ◇ x) ◇ y) ◇ ((d y x) ◇ x)))) ((p850 y)))).symm).trans ((((congrArg (fun _t : G => ((y ◇ (y ◇ _t)) ◇ ((((d y x) ◇ x) ◇ y) ◇ ((d y x) ◇ x)))) ((p850 y)))).symm).trans ((((congrArg (fun _t : G => ((y ◇ (y ◇ (y ◇ _t))) ◇ ((((d y x) ◇ x) ◇ y) ◇ ((d y x) ◇ x)))) ((p851 x y)))).symm).trans ((((congrArg (fun _t : G => ((y ◇ (_t ◇ (y ◇ (x ◇ y)))) ◇ ((((d y x) ◇ x) ◇ y) ◇ ((d y x) ◇ x)))) ((p851 x y)))).symm).trans ((((congrArg (fun _t : G => ((_t ◇ ((x ◇ y) ◇ (y ◇ (x ◇ y)))) ◇ ((((d y x) ◇ x) ◇ y) ◇ ((d y x) ◇ x)))) ((p851 x y)))).symm).trans ((((congrArg (fun _t : G => (_t ◇ ((((d y x) ◇ x) ◇ y) ◇ ((d y x) ◇ x)))) ((p838 x y)))).symm).trans ((p748 x y)))))))))))))))))))))))))))).trans ((congrArg (fun _t : G => (_t ◇ (y ◇ ((d x y) ◇ y)))) ((p838 x y))))).trans ((congrArg (fun _t : G => ((_t ◇ ((x ◇ y) ◇ (y ◇ (x ◇ y)))) ◇ (y ◇ ((d x y) ◇ y)))) ((p851 x y))))).trans ((congrArg (fun _t : G => ((y ◇ (_t ◇ (y ◇ (x ◇ y)))) ◇ (y ◇ ((d x y) ◇ y)))) ((p851 x y))))).trans ((congrArg (fun _t : G => ((y ◇ (y ◇ (y ◇ _t))) ◇ (y ◇ ((d x y) ◇ y)))) ((p851 x y))))).trans ((congrArg (fun _t : G => ((y ◇ (y ◇ _t)) ◇ (y ◇ ((d x y) ◇ y)))) ((p850 y))))).trans ((congrArg (fun _t : G => ((y ◇ _t) ◇ (y ◇ ((d x y) ◇ y)))) ((p850 y))))).trans ((congrArg (fun _t : G => (_t ◇ (y ◇ ((d x y) ◇ y)))) ((p850 y))))).trans ((congrArg (fun _t : G => (y ◇ (y ◇ (_t ◇ y)))) ((p838 x y))))).trans ((congrArg (fun _t : G => (y ◇ (y ◇ ((_t ◇ ((x ◇ y) ◇ (y ◇ (x ◇ y)))) ◇ y)))) ((p851 x y))))).trans ((congrArg (fun _t : G => (y ◇ (y ◇ ((y ◇ (_t ◇ (y ◇ (x ◇ y)))) ◇ y)))) ((p851 x y))))).trans ((congrArg (fun _t : G => (y ◇ (y ◇ ((y ◇ (y ◇ (y ◇ _t))) ◇ y)))) ((p851 x y))))).trans ((congrArg (fun _t : G => (y ◇ (y ◇ ((y ◇ (y ◇ _t)) ◇ y)))) ((p850 y))))).trans ((congrArg (fun _t : G => (y ◇ (y ◇ ((y ◇ _t) ◇ y)))) ((p850 y))))).trans ((congrArg (fun _t : G => (y ◇ (y ◇ (_t ◇ y)))) ((p850 y))))).trans ((congrArg (fun _t : G => (y ◇ (y ◇ _t))) ((p850 y))))).trans ((congrArg (fun _t : G => (y ◇ _t)) ((p850 y))))).trans ((p850 y))
  exact (p852 a a).trans (p852 b a).symm

#print axioms finite_trivial

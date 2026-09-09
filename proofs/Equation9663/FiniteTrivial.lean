import Mathlib.Data.Fintype.Card
import JudgeMagma.Magma

@[reducible] def Equation2 (G : Type _) [Magma G] : Prop := ∀ (x y : G), x = y
@[reducible] def Equation9663 (G : Type _) [Magma G] : Prop := ∀ (x y z : G), x = y ◇ ((z ◇ y) ◇ (x ◇ (x ◇ y)))

theorem finite_trivial (G : Type*) [Magma G] [Finite G] (h : Equation9663 G) : Equation2 G := by
  intro a b
  have ls (y : G) : Function.Surjective (fun t : G => y ◇ t) := by
    intro x
    exact ⟨((a ◇ y) ◇ (x ◇ (x ◇ y))), (h x y a).symm⟩
  have li (y : G) : Function.Injective (fun t : G => y ◇ t) :=
    Finite.injective_iff_surjective.mpr (ls y)
  let d (x y : G) : G := Classical.choose (ls x y)
  have ld1 (x y : G) : x ◇ d x y = y := Classical.choose_spec (ls x y)
  have ld2 (x y : G) : d x (x ◇ y) = y := li x (ld1 x (x ◇ y))
  have p2 (x y z : G) : (x ◇ ((y ◇ x) ◇ (z ◇ (z ◇ x)))) = z := by
    exact (h z x y).symm
  have p3 (x y : G) : (x ◇ (d x y)) = y := by
    exact (ld1 x y)
  have p4 (x y : G) : (d x (x ◇ y)) = y := by
    exact (ld2 x y)
  have p6 (u x y z : G) : (((x ◇ y) ◇ (z ◇ (z ◇ y))) ◇ (z ◇ (u ◇ (u ◇ ((x ◇ y) ◇ (z ◇ (z ◇ y))))))) = u := by
    exact (((congrArg (fun _t : G => (((x ◇ y) ◇ (z ◇ (z ◇ y))) ◇ (_t ◇ (u ◇ (u ◇ ((x ◇ y) ◇ (z ◇ (z ◇ y)))))))) ((p2 y x z)))).symm).trans ((p2 ((x ◇ y) ◇ (z ◇ (z ◇ y))) y u))
  have p9 (x y z : G) : ((d x y) ◇ ((z ◇ (d x y)) ◇ (x ◇ y))) = x := by
    exact (((congrArg (fun _t : G => ((d x y) ◇ ((z ◇ (d x y)) ◇ (x ◇ _t)))) ((p3 x y)))).symm).trans ((p2 (d x y) z x))
  have p10 (x y z : G) : (d x y) = ((z ◇ x) ◇ (y ◇ (y ◇ x))) := by
    exact (((congrArg (fun _t : G => (d x _t)) ((p2 x z y)))).symm).trans ((p4 x ((z ◇ x) ◇ (y ◇ (y ◇ x)))))
  have p13 (u w x y z : G) : (((x ◇ ((y ◇ z) ◇ (u ◇ (u ◇ z)))) ◇ (z ◇ u)) ◇ (z ◇ (w ◇ (w ◇ ((x ◇ ((y ◇ z) ◇ (u ◇ (u ◇ z)))) ◇ (z ◇ u)))))) = w := by
    exact (((congrArg (fun _t : G => (((x ◇ ((y ◇ z) ◇ (u ◇ (u ◇ z)))) ◇ (z ◇ u)) ◇ (z ◇ (w ◇ (w ◇ ((x ◇ ((y ◇ z) ◇ (u ◇ (u ◇ z)))) ◇ (z ◇ _t))))))) ((p2 z y u)))).symm).trans ((((congrArg (fun _t : G => (((x ◇ ((y ◇ z) ◇ (u ◇ (u ◇ z)))) ◇ (z ◇ _t)) ◇ (z ◇ (w ◇ (w ◇ ((x ◇ ((y ◇ z) ◇ (u ◇ (u ◇ z)))) ◇ (z ◇ (z ◇ ((y ◇ z) ◇ (u ◇ (u ◇ z))))))))))) ((p2 z y u)))).symm).trans ((p6 w x ((y ◇ z) ◇ (u ◇ (u ◇ z))) z)))
  have p14 (x y z : G) : (((x ◇ y) ◇ (z ◇ (z ◇ y))) ◇ (z ◇ (y ◇ z))) = y := by
    exact (((congrArg (fun _t : G => (((x ◇ y) ◇ (z ◇ (z ◇ y))) ◇ (z ◇ (y ◇ _t)))) ((p2 y x z)))).symm).trans ((p6 y x y z))
  have p17 (u x y z : G) : (d ((x ◇ y) ◇ (z ◇ (z ◇ y))) u) = (z ◇ (u ◇ (u ◇ ((x ◇ y) ◇ (z ◇ (z ◇ y)))))) := by
    exact (((congrArg (fun _t : G => (d ((x ◇ y) ◇ (z ◇ (z ◇ y))) _t)) ((p6 u x y z)))).symm).trans ((p4 ((x ◇ y) ◇ (z ◇ (z ◇ y))) (z ◇ (u ◇ (u ◇ ((x ◇ y) ◇ (z ◇ (z ◇ y))))))))
  have p18 (u v5 w x y z : G) : ((x ◇ (y ◇ (y ◇ (z ◇ (x ◇ (x ◇ ((u ◇ w) ◇ (z ◇ (z ◇ w))))))))) ◇ (y ◇ (v5 ◇ (v5 ◇ (x ◇ (y ◇ (y ◇ (z ◇ (x ◇ (x ◇ ((u ◇ w) ◇ (z ◇ (z ◇ w))))))))))))) = v5 := by
    exact (((congrArg (fun _t : G => ((x ◇ (y ◇ (y ◇ (z ◇ (x ◇ (x ◇ ((u ◇ w) ◇ (z ◇ (z ◇ w))))))))) ◇ (y ◇ (v5 ◇ (v5 ◇ (_t ◇ (y ◇ (y ◇ (z ◇ (x ◇ (x ◇ ((u ◇ w) ◇ (z ◇ (z ◇ w)))))))))))))) ((p6 x u w z)))).symm).trans ((((congrArg (fun _t : G => ((_t ◇ (y ◇ (y ◇ (z ◇ (x ◇ (x ◇ ((u ◇ w) ◇ (z ◇ (z ◇ w))))))))) ◇ (y ◇ (v5 ◇ (v5 ◇ ((((u ◇ w) ◇ (z ◇ (z ◇ w))) ◇ (z ◇ (x ◇ (x ◇ ((u ◇ w) ◇ (z ◇ (z ◇ w))))))) ◇ (y ◇ (y ◇ (z ◇ (x ◇ (x ◇ ((u ◇ w) ◇ (z ◇ (z ◇ w)))))))))))))) ((p6 x u w z)))).symm).trans ((p6 v5 ((u ◇ w) ◇ (z ◇ (z ◇ w))) (z ◇ (x ◇ (x ◇ ((u ◇ w) ◇ (z ◇ (z ◇ w)))))) y)))
  have p23 (u x y z : G) : ((x ◇ ((y ◇ z) ◇ (u ◇ (u ◇ z)))) ◇ (z ◇ u)) = (u ◇ (z ◇ u)) := by
    exact ((((congrArg (fun _t : G => (u ◇ (z ◇ _t))) ((p2 z y u)))).symm).trans ((((p17 z y z u)).symm).trans (((p10 ((y ◇ z) ◇ (u ◇ (u ◇ z))) z x)).trans ((congrArg (fun _t : G => ((x ◇ ((y ◇ z) ◇ (u ◇ (u ◇ z)))) ◇ (z ◇ _t))) ((p2 z y u))))))).symm
  have p24 (x y z : G) : (d (d x y) z) = (y ◇ (z ◇ (z ◇ (d x y)))) := by
    exact ((p10 (d x y) z x)).trans ((congrArg (fun _t : G => (_t ◇ (z ◇ (z ◇ (d x y))))) ((p3 x y))))
  have p25 (x y z : G) : ((x ◇ (d y z)) ◇ (y ◇ z)) = (z ◇ (y ◇ z)) := by
    exact ((((congrArg (fun _t : G => (z ◇ (y ◇ _t))) ((p3 y z)))).symm).trans ((((p24 y z y)).symm).trans (((p10 (d y z) y x)).trans ((congrArg (fun _t : G => ((x ◇ (d y z)) ◇ (y ◇ _t))) ((p3 y z))))))).symm
  have p26 (x y z : G) : ((x ◇ y) ◇ ((y ◇ z) ◇ ((y ◇ z) ◇ y))) = z := by
    exact (((p10 y (y ◇ z) x)).symm).trans ((p4 y z))
  have p27 (x y z : G) : (d (x ◇ y) (d y z)) = (z ◇ (z ◇ y)) := by
    exact (((congrArg (fun _t : G => (d (x ◇ y) _t)) (((p10 y z x)).symm))).symm).trans ((p4 (x ◇ y) (z ◇ (z ◇ y))))
  have p39 (u x y z : G) : ((x ◇ y) ◇ (z ◇ (z ◇ y))) = ((u ◇ y) ◇ (z ◇ (z ◇ y))) := by
    exact (((p10 y z x)).symm).trans ((p10 y z u))
  have p43 (x y z : G) : ((x ◇ (y ◇ x)) ◇ (y ◇ (z ◇ (z ◇ (x ◇ (y ◇ x)))))) = z := by
    exact (((congrArg (fun _t : G => ((x ◇ (y ◇ x)) ◇ (y ◇ (z ◇ (z ◇ _t))))) ((p23 x a a y)))).symm).trans ((((congrArg (fun _t : G => (_t ◇ (y ◇ (z ◇ (z ◇ ((a ◇ ((a ◇ y) ◇ (x ◇ (x ◇ y)))) ◇ (y ◇ x))))))) ((p23 x a a y)))).symm).trans ((p13 x z a a y)))
  have p44 (x y : G) : ((d x y) ◇ (y ◇ (x ◇ y))) = x := by
    exact (((congrArg (fun _t : G => ((d x y) ◇ _t)) ((p25 a x y)))).symm).trans ((p9 x y a))
  have p52 (x y z : G) : (d (x ◇ (y ◇ x)) z) = (y ◇ (z ◇ (z ◇ (x ◇ (y ◇ x))))) := by
    exact ((p10 (x ◇ (y ◇ x)) z (d y x))).trans ((congrArg (fun _t : G => (_t ◇ (z ◇ (z ◇ (x ◇ (y ◇ x)))))) ((p44 y x))))
  have p55 (x y : G) : ((x ◇ ((x ◇ (y ◇ x)) ◇ ((x ◇ (y ◇ x)) ◇ (d y x)))) ◇ ((x ◇ (y ◇ x)) ◇ y)) = (d y x) := by
    exact (((congrArg (fun _t : G => (_t ◇ ((x ◇ (y ◇ x)) ◇ y))) ((p24 y x (x ◇ (y ◇ x)))))).symm).trans ((((congrArg (fun _t : G => ((d (d y x) (x ◇ (y ◇ x))) ◇ ((x ◇ (y ◇ x)) ◇ _t))) ((p44 y x)))).symm).trans ((p44 (d y x) (x ◇ (y ◇ x)))))
  have p59 (x y z : G) : (d (x ◇ y) z) = ((y ◇ z) ◇ ((y ◇ z) ◇ y)) := by
    exact (((congrArg (fun _t : G => (d (x ◇ y) _t)) ((p4 y z)))).symm).trans ((p27 x y (y ◇ z)))
  have p69 (x y z : G) : (((x ◇ y) ◇ z) ◇ (((x ◇ y) ◇ z) ◇ (x ◇ y))) = (x ◇ (z ◇ (z ◇ (y ◇ (x ◇ y))))) := by
    exact (((p59 y (x ◇ y) z)).symm).trans ((p52 y x z))
  have p99 (x y z : G) : (x ◇ (y ◇ (y ◇ (d z x)))) = (x ◇ (y ◇ (y ◇ ((x ◇ z) ◇ (x ◇ (x ◇ z)))))) := by
    exact ((((p69 x (x ◇ z) y)).symm).trans ((((p59 (a ◇ z) (x ◇ (x ◇ z)) y)).symm).trans ((((congrArg (fun _t : G => (d _t y)) ((p10 z x a)))).symm).trans ((p24 z x y))))).symm
  have p106 (x y : G) : (d x y) = ((y ◇ ((y ◇ (x ◇ y)) ◇ ((y ◇ (x ◇ y)) ◇ ((y ◇ x) ◇ (y ◇ (y ◇ x)))))) ◇ ((y ◇ (x ◇ y)) ◇ x)) := by
    exact ((((congrArg (fun _t : G => (_t ◇ ((y ◇ (x ◇ y)) ◇ x))) ((p99 y (y ◇ (x ◇ y)) x)))).symm).trans ((p55 y x))).symm
  have p145 (x y : G) : (((x ◇ x) ◇ x) ◇ ((y ◇ ((x ◇ x) ◇ x)) ◇ x)) = (x ◇ x) := by
    exact (((congrArg (fun _t : G => (((x ◇ x) ◇ x) ◇ ((y ◇ ((x ◇ x) ◇ x)) ◇ _t))) ((p26 x x x)))).symm).trans ((p2 ((x ◇ x) ◇ x) y (x ◇ x)))
  have p151 (u w x y z : G) : ((x ◇ ((y ◇ z) ◇ (u ◇ (u ◇ z)))) ◇ (w ◇ (w ◇ ((y ◇ z) ◇ (u ◇ (u ◇ z)))))) = (u ◇ (w ◇ (w ◇ ((y ◇ z) ◇ (u ◇ (u ◇ z)))))) := by
    exact (((congrArg (fun _t : G => ((x ◇ ((y ◇ z) ◇ (u ◇ (u ◇ z)))) ◇ (w ◇ (_t ◇ ((y ◇ z) ◇ (u ◇ (u ◇ z))))))) ((p6 w y z u)))).symm).trans ((((congrArg (fun _t : G => ((x ◇ ((y ◇ z) ◇ (u ◇ (u ◇ z)))) ◇ (_t ◇ ((((y ◇ z) ◇ (u ◇ (u ◇ z))) ◇ (u ◇ (w ◇ (w ◇ ((y ◇ z) ◇ (u ◇ (u ◇ z))))))) ◇ ((y ◇ z) ◇ (u ◇ (u ◇ z))))))) ((p6 w y z u)))).symm).trans ((p26 x ((y ◇ z) ◇ (u ◇ (u ◇ z))) (u ◇ (w ◇ (w ◇ ((y ◇ z) ◇ (u ◇ (u ◇ z)))))))))
  have p160 (x y z : G) : (x ◇ (y ◇ (z ◇ (z ◇ ((x ◇ y) ◇ (y ◇ (x ◇ y))))))) = z := by
    exact (((congrArg (fun _t : G => (x ◇ _t)) ((p69 y (x ◇ y) z)))).symm).trans ((((congrArg (fun _t : G => (_t ◇ (((y ◇ (x ◇ y)) ◇ z) ◇ (((y ◇ (x ◇ y)) ◇ z) ◇ (y ◇ (x ◇ y)))))) ((p14 a x y)))).symm).trans ((p26 ((a ◇ x) ◇ (y ◇ (y ◇ x))) (y ◇ (x ◇ y)) z)))
  have p168 (x y z : G) : ((x ◇ ((x ◇ (y ◇ x)) ◇ ((x ◇ (y ◇ x)) ◇ ((z ◇ y) ◇ (x ◇ (x ◇ y)))))) ◇ ((x ◇ (y ◇ x)) ◇ y)) = ((z ◇ y) ◇ (x ◇ (x ◇ y))) := by
    exact (((congrArg (fun _t : G => (_t ◇ ((x ◇ (y ◇ x)) ◇ y))) ((p151 x (x ◇ (y ◇ x)) a z y)))).symm).trans ((((congrArg (fun _t : G => (((a ◇ ((z ◇ y) ◇ (x ◇ (x ◇ y)))) ◇ ((x ◇ (y ◇ x)) ◇ ((x ◇ (y ◇ x)) ◇ ((z ◇ y) ◇ (x ◇ (x ◇ y)))))) ◇ ((x ◇ (y ◇ x)) ◇ _t))) ((p14 z y x)))).symm).trans ((p14 a ((z ◇ y) ◇ (x ◇ (x ◇ y))) (x ◇ (y ◇ x)))))
  have p186 (x y : G) : (d x y) = ((y ◇ x) ◇ (y ◇ (y ◇ x))) := by
    exact ((p106 x y)).trans ((p168 y x y))
  have p245 (x y z : G) : ((x ◇ (x ◇ x)) ◇ (x ◇ ((y ◇ x) ◇ ((z ◇ x) ◇ (x ◇ (x ◇ x)))))) = (y ◇ x) := by
    exact (((congrArg (fun _t : G => ((x ◇ (x ◇ x)) ◇ (x ◇ ((y ◇ x) ◇ _t)))) ((p39 z y x x)))).symm).trans ((p43 x x (y ◇ x)))
  have p258 (x : G) : (x ◇ (x ◇ (x ◇ x))) = x := by
    exact (((congrArg (fun _t : G => (x ◇ (x ◇ (x ◇ _t)))) ((p2 x x x)))).symm).trans ((p160 x x x))
  have p274 (x : G) : ((((x ◇ x) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ x) ◇ (x ◇ (x ◇ x))))) ◇ (((x ◇ x) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ x) ◇ (x ◇ (x ◇ x))))) = x := by
    exact (((congrArg (fun _t : G => ((((x ◇ x) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ x) ◇ (x ◇ (x ◇ x))))) ◇ (((x ◇ x) ◇ (x ◇ (x ◇ x))) ◇ _t))) ((p160 x x ((x ◇ x) ◇ (x ◇ (x ◇ x))))))).symm).trans ((p43 ((x ◇ x) ◇ (x ◇ (x ◇ x))) ((x ◇ x) ◇ (x ◇ (x ◇ x))) x))
  have p297 (u v5 w x y z : G) : ((x ◇ (y ◇ (y ◇ (z ◇ (x ◇ (x ◇ ((u ◇ u) ◇ (z ◇ (z ◇ ((w ◇ ((u ◇ u) ◇ u)) ◇ u)))))))))) ◇ (y ◇ (v5 ◇ (v5 ◇ (x ◇ (y ◇ (y ◇ (z ◇ (x ◇ (x ◇ ((u ◇ u) ◇ (z ◇ (z ◇ ((w ◇ ((u ◇ u) ◇ u)) ◇ u)))))))))))))) = v5 := by
    exact (((congrArg (fun _t : G => ((x ◇ (y ◇ (y ◇ (z ◇ (x ◇ (x ◇ ((u ◇ u) ◇ (z ◇ (z ◇ ((w ◇ ((u ◇ u) ◇ u)) ◇ u)))))))))) ◇ (y ◇ (v5 ◇ (v5 ◇ (x ◇ (y ◇ (y ◇ (z ◇ (x ◇ (x ◇ (_t ◇ (z ◇ (z ◇ ((w ◇ ((u ◇ u) ◇ u)) ◇ u))))))))))))))) ((p145 u w)))).symm).trans ((((congrArg (fun _t : G => ((x ◇ (y ◇ (y ◇ (z ◇ (x ◇ (x ◇ (_t ◇ (z ◇ (z ◇ ((w ◇ ((u ◇ u) ◇ u)) ◇ u)))))))))) ◇ (y ◇ (v5 ◇ (v5 ◇ (x ◇ (y ◇ (y ◇ (z ◇ (x ◇ (x ◇ ((((u ◇ u) ◇ u) ◇ ((w ◇ ((u ◇ u) ◇ u)) ◇ u)) ◇ (z ◇ (z ◇ ((w ◇ ((u ◇ u) ◇ u)) ◇ u))))))))))))))) ((p145 u w)))).symm).trans ((p18 ((u ◇ u) ◇ u) v5 ((w ◇ ((u ◇ u) ◇ u)) ◇ u) x y z)))
  have p305 (x y : G) : ((x ◇ y) ◇ (y ◇ (y ◇ y))) = (y ◇ (y ◇ y)) := by
    exact (((congrArg (fun _t : G => ((x ◇ y) ◇ (y ◇ (_t ◇ y)))) ((p258 y)))).symm).trans ((((congrArg (fun _t : G => ((x ◇ y) ◇ (_t ◇ ((y ◇ (y ◇ (y ◇ y))) ◇ y)))) ((p258 y)))).symm).trans ((p26 x y (y ◇ (y ◇ y)))))
  have p311 (x : G) : ((x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) = x := by
    exact (((congrArg (fun _t : G => ((x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ _t)))) ((p258 x)))).symm).trans ((p43 x x x))
  have p314 (x : G) : (((x ◇ (x ◇ x)) ◇ x) ◇ x) = x := by
    exact (((congrArg (fun _t : G => (((x ◇ (x ◇ x)) ◇ x) ◇ _t)) ((p311 x)))).symm).trans ((((congrArg (fun _t : G => (((x ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ (x ◇ x)) ◇ _t))) ((p305 x x)))).symm).trans ((((congrArg (fun _t : G => (((x ◇ (x ◇ x)) ◇ x) ◇ (_t ◇ ((x ◇ x) ◇ (x ◇ (x ◇ x)))))) ((p305 x x)))).symm).trans ((((congrArg (fun _t : G => (((x ◇ (x ◇ x)) ◇ _t) ◇ (((x ◇ x) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ x) ◇ (x ◇ (x ◇ x)))))) ((p311 x)))).symm).trans ((((congrArg (fun _t : G => (((x ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ _t)) ◇ (((x ◇ x) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ x) ◇ (x ◇ (x ◇ x)))))) ((p305 x x)))).symm).trans ((((congrArg (fun _t : G => (((x ◇ (x ◇ x)) ◇ (_t ◇ ((x ◇ x) ◇ (x ◇ (x ◇ x))))) ◇ (((x ◇ x) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ x) ◇ (x ◇ (x ◇ x)))))) ((p305 x x)))).symm).trans ((((congrArg (fun _t : G => ((_t ◇ (((x ◇ x) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ x) ◇ (x ◇ (x ◇ x))))) ◇ (((x ◇ x) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ x) ◇ (x ◇ (x ◇ x)))))) ((p305 x x)))).symm).trans ((p274 x))))))))
  have p319 (x y : G) : ((x ◇ (x ◇ x)) ◇ x) = (y ◇ x) := by
    exact (((congrArg (fun _t : G => ((x ◇ (x ◇ x)) ◇ _t)) ((p258 x)))).symm).trans ((((congrArg (fun _t : G => ((x ◇ (x ◇ x)) ◇ (x ◇ _t))) ((p305 y x)))).symm).trans ((((congrArg (fun _t : G => ((x ◇ (x ◇ x)) ◇ (x ◇ ((y ◇ x) ◇ _t)))) ((p305 a x)))).symm).trans ((p245 x y a))))
  have p323 (x y : G) : ((x ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ (y ◇ (y ◇ ((y ◇ (y ◇ y)) ◇ y)))) = y := by
    exact (((congrArg (fun _t : G => ((x ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ (y ◇ (_t ◇ ((y ◇ (y ◇ y)) ◇ y))))) ((p314 y)))).symm).trans ((((congrArg (fun _t : G => ((x ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ (_t ◇ ((((y ◇ (y ◇ y)) ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ y))))) ((p314 y)))).symm).trans ((p26 x ((y ◇ (y ◇ y)) ◇ y) y)))
  have p326 (x : G) : ((x ◇ (x ◇ x)) ◇ x) = (x ◇ (x ◇ x)) := by
    exact ((((congrArg (fun _t : G => (_t ◇ (x ◇ x))) ((p323 a x)))).symm).trans ((((congrArg (fun _t : G => (((a ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (x ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x)))) ◇ (x ◇ _t))) ((p314 x)))).symm).trans ((p14 a ((x ◇ (x ◇ x)) ◇ x) x)))).symm
  have p327 (x : G) : (x ◇ (x ◇ x)) = (x ◇ x) := by
    exact (((((((p326 x)).symm).trans ((((congrArg (fun _t : G => ((x ◇ (x ◇ x)) ◇ _t)) ((p311 x)))).symm).trans ((((congrArg (fun _t : G => ((x ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ _t))) ((p326 x)))).symm).trans ((((congrArg (fun _t : G => (_t ◇ ((x ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ x)))) ((p326 x)))).symm).trans ((((p186 x (x ◇ (x ◇ x)))).symm).trans ((((congrArg (fun _t : G => (d x _t)) ((p326 x)))).symm).trans (((p186 x ((x ◇ (x ◇ x)) ◇ x))).trans ((congrArg (fun _t : G => (_t ◇ (((x ◇ (x ◇ x)) ◇ x) ◇ (((x ◇ (x ◇ x)) ◇ x) ◇ x)))) ((p314 x))))))))))).trans ((congrArg (fun _t : G => (x ◇ (_t ◇ (((x ◇ (x ◇ x)) ◇ x) ◇ x)))) ((p326 x))))).trans ((congrArg (fun _t : G => (x ◇ ((x ◇ (x ◇ x)) ◇ (_t ◇ x)))) ((p326 x))))).trans ((congrArg (fun _t : G => (x ◇ ((x ◇ (x ◇ x)) ◇ _t))) ((p326 x))))).trans ((congrArg (fun _t : G => (x ◇ _t)) ((p311 x))))
  have p341 (x y : G) : ((x ◇ x) ◇ x) = (y ◇ x) := by
    exact (((congrArg (fun _t : G => (_t ◇ x)) ((p327 x)))).symm).trans ((p319 x y))
  have p355 (x : G) : (x ◇ x) = x := by
    exact (((p327 x)).symm).trans ((((congrArg (fun _t : G => (x ◇ _t)) ((p327 x)))).symm).trans ((p258 x)))
  have p445 (x y : G) : (x ◇ y) = y := by
    exact ((((p355 y)).symm).trans ((((congrArg (fun _t : G => (_t ◇ y)) ((p355 y)))).symm).trans ((p341 y x)))).symm
  have p446 (x y : G) : x = y := by
    exact (((p355 x)).symm).trans ((((congrArg (fun _t : G => (x ◇ _t)) ((p445 a x)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (a ◇ _t))) ((p445 y x)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (a ◇ (y ◇ _t)))) ((p445 y x)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (a ◇ (y ◇ (y ◇ _t))))) ((p445 a x)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (a ◇ (y ◇ (y ◇ (a ◇ _t)))))) ((p445 a x)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (a ◇ (y ◇ (y ◇ (a ◇ (a ◇ _t))))))) ((p445 a x)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (a ◇ (y ◇ (y ◇ (a ◇ (a ◇ (a ◇ _t)))))))) ((p445 a x)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (a ◇ (y ◇ (y ◇ (a ◇ (a ◇ (a ◇ (a ◇ _t))))))))) ((p445 a x)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (a ◇ (y ◇ (y ◇ (a ◇ (a ◇ (a ◇ (a ◇ (a ◇ _t)))))))))) ((p445 a x)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (a ◇ (y ◇ (y ◇ (a ◇ (a ◇ (a ◇ (a ◇ (a ◇ (a ◇ _t))))))))))) ((p355 x)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (a ◇ (y ◇ (y ◇ (a ◇ (a ◇ (a ◇ (a ◇ (a ◇ (a ◇ (x ◇ _t)))))))))))) ((p445 a x)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (a ◇ (y ◇ (y ◇ (a ◇ (a ◇ (a ◇ (a ◇ (a ◇ (a ◇ (x ◇ (a ◇ _t))))))))))))) ((p445 a x)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (a ◇ (y ◇ (y ◇ (a ◇ (a ◇ (a ◇ (a ◇ (a ◇ (a ◇ (x ◇ (a ◇ (a ◇ _t)))))))))))))) ((p355 x)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (a ◇ (y ◇ (y ◇ (a ◇ (a ◇ (a ◇ (a ◇ (a ◇ (a ◇ (x ◇ (a ◇ (a ◇ (_t ◇ x))))))))))))))) ((p445 a x)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (a ◇ (y ◇ (y ◇ (a ◇ (a ◇ (a ◇ (a ◇ (a ◇ (a ◇ (x ◇ (a ◇ (a ◇ ((a ◇ _t) ◇ x))))))))))))))) ((p355 x)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (a ◇ (y ◇ (y ◇ (a ◇ (a ◇ (a ◇ (a ◇ (a ◇ (a ◇ (x ◇ (a ◇ (a ◇ ((a ◇ (_t ◇ x)) ◇ x))))))))))))))) ((p355 x)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (a ◇ (y ◇ (y ◇ (a ◇ (a ◇ (a ◇ (a ◇ (a ◇ (a ◇ (_t ◇ (a ◇ (a ◇ ((a ◇ ((x ◇ x) ◇ x)) ◇ x))))))))))))))) ((p355 x)))).symm).trans ((((congrArg (fun _t : G => (_t ◇ (a ◇ (y ◇ (y ◇ (a ◇ (a ◇ (a ◇ (a ◇ (a ◇ (a ◇ ((x ◇ x) ◇ (a ◇ (a ◇ ((a ◇ ((x ◇ x) ◇ x)) ◇ x))))))))))))))) ((p445 a x)))).symm).trans ((((congrArg (fun _t : G => ((a ◇ _t) ◇ (a ◇ (y ◇ (y ◇ (a ◇ (a ◇ (a ◇ (a ◇ (a ◇ (a ◇ ((x ◇ x) ◇ (a ◇ (a ◇ ((a ◇ ((x ◇ x) ◇ x)) ◇ x))))))))))))))) ((p445 a x)))).symm).trans ((((congrArg (fun _t : G => ((a ◇ (a ◇ _t)) ◇ (a ◇ (y ◇ (y ◇ (a ◇ (a ◇ (a ◇ (a ◇ (a ◇ (a ◇ ((x ◇ x) ◇ (a ◇ (a ◇ ((a ◇ ((x ◇ x) ◇ x)) ◇ x))))))))))))))) ((p445 a x)))).symm).trans ((((congrArg (fun _t : G => ((a ◇ (a ◇ (a ◇ _t))) ◇ (a ◇ (y ◇ (y ◇ (a ◇ (a ◇ (a ◇ (a ◇ (a ◇ (a ◇ ((x ◇ x) ◇ (a ◇ (a ◇ ((a ◇ ((x ◇ x) ◇ x)) ◇ x))))))))))))))) ((p445 a x)))).symm).trans ((((congrArg (fun _t : G => ((a ◇ (a ◇ (a ◇ (a ◇ _t)))) ◇ (a ◇ (y ◇ (y ◇ (a ◇ (a ◇ (a ◇ (a ◇ (a ◇ (a ◇ ((x ◇ x) ◇ (a ◇ (a ◇ ((a ◇ ((x ◇ x) ◇ x)) ◇ x))))))))))))))) ((p445 a x)))).symm).trans ((((congrArg (fun _t : G => ((a ◇ (a ◇ (a ◇ (a ◇ (a ◇ _t))))) ◇ (a ◇ (y ◇ (y ◇ (a ◇ (a ◇ (a ◇ (a ◇ (a ◇ (a ◇ ((x ◇ x) ◇ (a ◇ (a ◇ ((a ◇ ((x ◇ x) ◇ x)) ◇ x))))))))))))))) ((p445 a x)))).symm).trans ((((congrArg (fun _t : G => ((a ◇ (a ◇ (a ◇ (a ◇ (a ◇ (a ◇ _t)))))) ◇ (a ◇ (y ◇ (y ◇ (a ◇ (a ◇ (a ◇ (a ◇ (a ◇ (a ◇ ((x ◇ x) ◇ (a ◇ (a ◇ ((a ◇ ((x ◇ x) ◇ x)) ◇ x))))))))))))))) ((p355 x)))).symm).trans ((((congrArg (fun _t : G => ((a ◇ (a ◇ (a ◇ (a ◇ (a ◇ (a ◇ (x ◇ _t))))))) ◇ (a ◇ (y ◇ (y ◇ (a ◇ (a ◇ (a ◇ (a ◇ (a ◇ (a ◇ ((x ◇ x) ◇ (a ◇ (a ◇ ((a ◇ ((x ◇ x) ◇ x)) ◇ x))))))))))))))) ((p445 a x)))).symm).trans ((((congrArg (fun _t : G => ((a ◇ (a ◇ (a ◇ (a ◇ (a ◇ (a ◇ (x ◇ (a ◇ _t)))))))) ◇ (a ◇ (y ◇ (y ◇ (a ◇ (a ◇ (a ◇ (a ◇ (a ◇ (a ◇ ((x ◇ x) ◇ (a ◇ (a ◇ ((a ◇ ((x ◇ x) ◇ x)) ◇ x))))))))))))))) ((p445 a x)))).symm).trans ((((congrArg (fun _t : G => ((a ◇ (a ◇ (a ◇ (a ◇ (a ◇ (a ◇ (x ◇ (a ◇ (a ◇ _t))))))))) ◇ (a ◇ (y ◇ (y ◇ (a ◇ (a ◇ (a ◇ (a ◇ (a ◇ (a ◇ ((x ◇ x) ◇ (a ◇ (a ◇ ((a ◇ ((x ◇ x) ◇ x)) ◇ x))))))))))))))) ((p355 x)))).symm).trans ((((congrArg (fun _t : G => ((a ◇ (a ◇ (a ◇ (a ◇ (a ◇ (a ◇ (x ◇ (a ◇ (a ◇ (_t ◇ x)))))))))) ◇ (a ◇ (y ◇ (y ◇ (a ◇ (a ◇ (a ◇ (a ◇ (a ◇ (a ◇ ((x ◇ x) ◇ (a ◇ (a ◇ ((a ◇ ((x ◇ x) ◇ x)) ◇ x))))))))))))))) ((p445 a x)))).symm).trans ((((congrArg (fun _t : G => ((a ◇ (a ◇ (a ◇ (a ◇ (a ◇ (a ◇ (x ◇ (a ◇ (a ◇ ((a ◇ _t) ◇ x)))))))))) ◇ (a ◇ (y ◇ (y ◇ (a ◇ (a ◇ (a ◇ (a ◇ (a ◇ (a ◇ ((x ◇ x) ◇ (a ◇ (a ◇ ((a ◇ ((x ◇ x) ◇ x)) ◇ x))))))))))))))) ((p355 x)))).symm).trans ((((congrArg (fun _t : G => ((a ◇ (a ◇ (a ◇ (a ◇ (a ◇ (a ◇ (x ◇ (a ◇ (a ◇ ((a ◇ (_t ◇ x)) ◇ x)))))))))) ◇ (a ◇ (y ◇ (y ◇ (a ◇ (a ◇ (a ◇ (a ◇ (a ◇ (a ◇ ((x ◇ x) ◇ (a ◇ (a ◇ ((a ◇ ((x ◇ x) ◇ x)) ◇ x))))))))))))))) ((p355 x)))).symm).trans ((((congrArg (fun _t : G => ((a ◇ (a ◇ (a ◇ (a ◇ (a ◇ (a ◇ (_t ◇ (a ◇ (a ◇ ((a ◇ ((x ◇ x) ◇ x)) ◇ x)))))))))) ◇ (a ◇ (y ◇ (y ◇ (a ◇ (a ◇ (a ◇ (a ◇ (a ◇ (a ◇ ((x ◇ x) ◇ (a ◇ (a ◇ ((a ◇ ((x ◇ x) ◇ x)) ◇ x))))))))))))))) ((p355 x)))).symm).trans ((p297 x y a a a a)))))))))))))))))))))))))))))))))
  exact (p446 a a).trans (p446 b a).symm

#print axioms finite_trivial

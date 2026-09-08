import Mathlib.Data.Fintype.Card
import JudgeMagma.Magma

@[reducible] def Equation2 (G : Type _) [Magma G] : Prop := ∀ (x y : G), x = y
@[reducible] def Equation6878 (G : Type _) [Magma G] : Prop := ∀ (x y z : G), x = y ◇ (y ◇ ((z ◇ x) ◇ (x ◇ y)))

theorem finite_trivial (G : Type*) [Magma G] [Finite G] (h : Equation6878 G) : Equation2 G := by
  intro a b
  have ls (y : G) : Function.Surjective (fun t : G => y ◇ t) := by
    intro x
    exact ⟨(y ◇ ((a ◇ x) ◇ (x ◇ y))), (h x y a).symm⟩
  have li (y : G) : Function.Injective (fun t : G => y ◇ t) :=
    Finite.injective_iff_surjective.mpr (ls y)
  let d (x y : G) : G := Classical.choose (ls x y)
  have ld1 (x y : G) : x ◇ d x y = y := Classical.choose_spec (ls x y)
  have ld2 (x y : G) : d x (x ◇ y) = y := li x (ld1 x (x ◇ y))
  have p2 (x y z : G) : (x ◇ (x ◇ ((y ◇ z) ◇ (z ◇ x)))) = z := by
    exact (h z x y).symm
  have p3 (x y : G) : (x ◇ (d x y)) = y := by
    exact (ld1 x y)
  have p4 (x y : G) : (d x (x ◇ y)) = y := by
    exact (ld2 x y)
  have p6 (u x y z : G) : (x ◇ (x ◇ (y ◇ ((z ◇ ((u ◇ y) ◇ (y ◇ z))) ◇ x)))) = (z ◇ ((u ◇ y) ◇ (y ◇ z))) := by
    exact (((congrArg (fun _t : G => (x ◇ (x ◇ (_t ◇ ((z ◇ ((u ◇ y) ◇ (y ◇ z))) ◇ x))))) ((p2 z u y)))).symm).trans ((p2 x z (z ◇ ((u ◇ y) ◇ (y ◇ z)))))
  have p7 (u x y z : G) : ((x ◇ ((y ◇ z) ◇ (z ◇ x))) ◇ ((x ◇ ((y ◇ z) ◇ (z ◇ x))) ◇ ((u ◇ x) ◇ z))) = x := by
    exact (((congrArg (fun _t : G => ((x ◇ ((y ◇ z) ◇ (z ◇ x))) ◇ ((x ◇ ((y ◇ z) ◇ (z ◇ x))) ◇ ((u ◇ x) ◇ _t)))) ((p2 x y z)))).symm).trans ((p2 (x ◇ ((y ◇ z) ◇ (z ◇ x))) u x))
  have p9 (x y z : G) : ((d x y) ◇ ((d x y) ◇ ((z ◇ x) ◇ y))) = x := by
    exact (((congrArg (fun _t : G => ((d x y) ◇ ((d x y) ◇ ((z ◇ x) ◇ _t)))) ((p3 x y)))).symm).trans ((p2 (d x y) z x))
  have p10 (x y z : G) : (d x y) = (x ◇ ((z ◇ y) ◇ (y ◇ x))) := by
    exact (((congrArg (fun _t : G => (d x _t)) ((p2 x z y)))).symm).trans ((p4 x (x ◇ ((z ◇ y) ◇ (y ◇ x)))))
  have p11 (u w x y z : G) : (x ◇ (x ◇ ((y ◇ ((z ◇ u) ◇ (u ◇ y))) ◇ ((w ◇ (u ◇ ((y ◇ ((z ◇ u) ◇ (u ◇ y))) ◇ w))) ◇ x)))) = (w ◇ (u ◇ ((y ◇ ((z ◇ u) ◇ (u ◇ y))) ◇ w))) := by
    exact (((congrArg (fun _t : G => (x ◇ (x ◇ (_t ◇ ((w ◇ (u ◇ ((y ◇ ((z ◇ u) ◇ (u ◇ y))) ◇ w))) ◇ x))))) ((p6 z w u y)))).symm).trans ((p2 x w (w ◇ (u ◇ ((y ◇ ((z ◇ u) ◇ (u ◇ y))) ◇ w)))))
  have p12 (u w x y z : G) : ((x ◇ (y ◇ ((z ◇ ((u ◇ y) ◇ (y ◇ z))) ◇ x))) ◇ ((x ◇ (y ◇ ((z ◇ ((u ◇ y) ◇ (y ◇ z))) ◇ x))) ◇ ((w ◇ x) ◇ (z ◇ ((u ◇ y) ◇ (y ◇ z)))))) = x := by
    exact (((congrArg (fun _t : G => ((x ◇ (y ◇ ((z ◇ ((u ◇ y) ◇ (y ◇ z))) ◇ x))) ◇ ((x ◇ (y ◇ ((z ◇ ((u ◇ y) ◇ (y ◇ z))) ◇ x))) ◇ ((w ◇ x) ◇ _t)))) ((p6 u x y z)))).symm).trans ((p2 (x ◇ (y ◇ ((z ◇ ((u ◇ y) ◇ (y ◇ z))) ◇ x))) w x))
  have p14 (u w x y z : G) : (((x ◇ ((y ◇ z) ◇ (z ◇ x))) ◇ ((u ◇ w) ◇ (w ◇ (x ◇ ((y ◇ z) ◇ (z ◇ x)))))) ◇ (((x ◇ ((y ◇ z) ◇ (z ◇ x))) ◇ ((u ◇ w) ◇ (w ◇ (x ◇ ((y ◇ z) ◇ (z ◇ x)))))) ◇ (z ◇ w))) = (x ◇ ((y ◇ z) ◇ (z ◇ x))) := by
    exact (((congrArg (fun _t : G => (((x ◇ ((y ◇ z) ◇ (z ◇ x))) ◇ ((u ◇ w) ◇ (w ◇ (x ◇ ((y ◇ z) ◇ (z ◇ x)))))) ◇ (((x ◇ ((y ◇ z) ◇ (z ◇ x))) ◇ ((u ◇ w) ◇ (w ◇ (x ◇ ((y ◇ z) ◇ (z ◇ x)))))) ◇ (z ◇ _t)))) ((p2 (x ◇ ((y ◇ z) ◇ (z ◇ x))) u w)))).symm).trans ((p6 y ((x ◇ ((y ◇ z) ◇ (z ◇ x))) ◇ ((u ◇ w) ◇ (w ◇ (x ◇ ((y ◇ z) ◇ (z ◇ x)))))) z x))
  have p18 (u x y z : G) : (d x (y ◇ ((z ◇ u) ◇ (u ◇ y)))) = (x ◇ (u ◇ ((y ◇ ((z ◇ u) ◇ (u ◇ y))) ◇ x))) := by
    exact (((congrArg (fun _t : G => (d x _t)) ((p6 z x u y)))).symm).trans ((p4 x (x ◇ (u ◇ ((y ◇ ((z ◇ u) ◇ (u ◇ y))) ◇ x)))))
  have p25 (u x y z : G) : (d (x ◇ ((y ◇ z) ◇ (z ◇ x))) x) = ((x ◇ ((y ◇ z) ◇ (z ◇ x))) ◇ ((u ◇ x) ◇ z)) := by
    exact ((p10 (x ◇ ((y ◇ z) ◇ (z ◇ x))) x u)).trans ((congrArg (fun _t : G => ((x ◇ ((y ◇ z) ◇ (z ◇ x))) ◇ ((u ◇ x) ◇ _t))) ((p2 x y z))))
  have p28 (x y z : G) : (x ◇ ((y ◇ (x ◇ z)) ◇ ((x ◇ z) ◇ x))) = z := by
    exact (((p10 x (x ◇ z) y)).symm).trans ((p4 x z))
  have p78 (u v5 w x y z : G) : (x ◇ (x ◇ ((y ◇ ((z ◇ u) ◇ (u ◇ y))) ◇ ((((y ◇ ((z ◇ u) ◇ (u ◇ y))) ◇ ((w ◇ y) ◇ u)) ◇ ((v5 ◇ (y ◇ ((z ◇ u) ◇ (u ◇ y)))) ◇ y)) ◇ x)))) = (((y ◇ ((z ◇ u) ◇ (u ◇ y))) ◇ ((w ◇ y) ◇ u)) ◇ ((v5 ◇ (y ◇ ((z ◇ u) ◇ (u ◇ y)))) ◇ y)) := by
    exact ((((congrArg (fun _t : G => (x ◇ (x ◇ ((y ◇ ((z ◇ u) ◇ (u ◇ y))) ◇ ((((y ◇ ((z ◇ u) ◇ (u ◇ y))) ◇ ((w ◇ y) ◇ u)) ◇ ((v5 ◇ (y ◇ ((z ◇ u) ◇ (u ◇ y)))) ◇ _t)) ◇ x))))) ((p7 w y z u)))).symm).trans ((p6 v5 x (y ◇ ((z ◇ u) ◇ (u ◇ y))) ((y ◇ ((z ◇ u) ◇ (u ◇ y))) ◇ ((w ◇ y) ◇ u))))).trans ((congrArg (fun _t : G => (((y ◇ ((z ◇ u) ◇ (u ◇ y))) ◇ ((w ◇ y) ◇ u)) ◇ ((v5 ◇ (y ◇ ((z ◇ u) ◇ (u ◇ y)))) ◇ _t))) ((p7 w y z u))))
  have p83 (u w x y z : G) : (((x ◇ ((y ◇ z) ◇ (z ◇ x))) ◇ ((u ◇ x) ◇ z)) ◇ ((w ◇ (x ◇ ((y ◇ z) ◇ (z ◇ x)))) ◇ x)) = (((x ◇ ((y ◇ z) ◇ (z ◇ x))) ◇ ((u ◇ x) ◇ z)) ◇ (z ◇ x)) := by
    exact ((((congrArg (fun _t : G => (((x ◇ ((y ◇ z) ◇ (z ◇ x))) ◇ ((u ◇ x) ◇ z)) ◇ (z ◇ _t))) ((p7 u x y z)))).symm).trans ((((p18 z ((x ◇ ((y ◇ z) ◇ (z ◇ x))) ◇ ((u ◇ x) ◇ z)) x y)).symm).trans (((p10 ((x ◇ ((y ◇ z) ◇ (z ◇ x))) ◇ ((u ◇ x) ◇ z)) (x ◇ ((y ◇ z) ◇ (z ◇ x))) w)).trans ((congrArg (fun _t : G => (((x ◇ ((y ◇ z) ◇ (z ◇ x))) ◇ ((u ◇ x) ◇ z)) ◇ ((w ◇ (x ◇ ((y ◇ z) ◇ (z ◇ x)))) ◇ _t))) ((p7 u x y z))))))).symm
  have p100 (u w x y z : G) : ((((x ◇ ((y ◇ z) ◇ (z ◇ x))) ◇ ((u ◇ x) ◇ z)) ◇ (z ◇ x)) ◇ ((((x ◇ ((y ◇ z) ◇ (z ◇ x))) ◇ ((u ◇ x) ◇ z)) ◇ (z ◇ x)) ◇ ((w ◇ ((x ◇ ((y ◇ z) ◇ (z ◇ x))) ◇ ((u ◇ x) ◇ z))) ◇ (x ◇ ((y ◇ z) ◇ (z ◇ x)))))) = ((x ◇ ((y ◇ z) ◇ (z ◇ x))) ◇ ((u ◇ x) ◇ z)) := by
    exact (((congrArg (fun _t : G => ((((x ◇ ((y ◇ z) ◇ (z ◇ x))) ◇ ((u ◇ x) ◇ z)) ◇ (z ◇ x)) ◇ (_t ◇ ((w ◇ ((x ◇ ((y ◇ z) ◇ (z ◇ x))) ◇ ((u ◇ x) ◇ z))) ◇ (x ◇ ((y ◇ z) ◇ (z ◇ x))))))) ((p83 u a x y z)))).symm).trans ((((congrArg (fun _t : G => ((((x ◇ ((y ◇ z) ◇ (z ◇ x))) ◇ ((u ◇ x) ◇ z)) ◇ (z ◇ x)) ◇ ((((x ◇ ((y ◇ z) ◇ (z ◇ x))) ◇ ((u ◇ x) ◇ z)) ◇ ((a ◇ (x ◇ ((y ◇ z) ◇ (z ◇ x)))) ◇ _t)) ◇ ((w ◇ ((x ◇ ((y ◇ z) ◇ (z ◇ x))) ◇ ((u ◇ x) ◇ z))) ◇ (x ◇ ((y ◇ z) ◇ (z ◇ x))))))) ((p7 u x y z)))).symm).trans ((((congrArg (fun _t : G => (_t ◇ ((((x ◇ ((y ◇ z) ◇ (z ◇ x))) ◇ ((u ◇ x) ◇ z)) ◇ ((a ◇ (x ◇ ((y ◇ z) ◇ (z ◇ x)))) ◇ ((x ◇ ((y ◇ z) ◇ (z ◇ x))) ◇ ((x ◇ ((y ◇ z) ◇ (z ◇ x))) ◇ ((u ◇ x) ◇ z))))) ◇ ((w ◇ ((x ◇ ((y ◇ z) ◇ (z ◇ x))) ◇ ((u ◇ x) ◇ z))) ◇ (x ◇ ((y ◇ z) ◇ (z ◇ x))))))) ((p83 u a x y z)))).symm).trans ((((congrArg (fun _t : G => ((((x ◇ ((y ◇ z) ◇ (z ◇ x))) ◇ ((u ◇ x) ◇ z)) ◇ ((a ◇ (x ◇ ((y ◇ z) ◇ (z ◇ x)))) ◇ _t)) ◇ ((((x ◇ ((y ◇ z) ◇ (z ◇ x))) ◇ ((u ◇ x) ◇ z)) ◇ ((a ◇ (x ◇ ((y ◇ z) ◇ (z ◇ x)))) ◇ ((x ◇ ((y ◇ z) ◇ (z ◇ x))) ◇ ((x ◇ ((y ◇ z) ◇ (z ◇ x))) ◇ ((u ◇ x) ◇ z))))) ◇ ((w ◇ ((x ◇ ((y ◇ z) ◇ (z ◇ x))) ◇ ((u ◇ x) ◇ z))) ◇ (x ◇ ((y ◇ z) ◇ (z ◇ x))))))) ((p7 u x y z)))).symm).trans ((p7 w ((x ◇ ((y ◇ z) ◇ (z ◇ x))) ◇ ((u ◇ x) ◇ z)) a (x ◇ ((y ◇ z) ◇ (z ◇ x))))))))
  have p102 (u w x y z : G) : (x ◇ (x ◇ ((y ◇ ((z ◇ u) ◇ (u ◇ y))) ◇ ((((y ◇ ((z ◇ u) ◇ (u ◇ y))) ◇ ((w ◇ y) ◇ u)) ◇ (u ◇ y)) ◇ x)))) = (((y ◇ ((z ◇ u) ◇ (u ◇ y))) ◇ ((w ◇ y) ◇ u)) ◇ (u ◇ y)) := by
    exact ((((congrArg (fun _t : G => (x ◇ (x ◇ ((y ◇ ((z ◇ u) ◇ (u ◇ y))) ◇ (_t ◇ x))))) ((p83 w a y z u)))).symm).trans ((p78 u a w x y z))).trans ((p83 w a y z u))
  have p139 (x y z : G) : (d x y) = ((z ◇ (x ◇ y)) ◇ ((x ◇ y) ◇ x)) := by
    exact (((congrArg (fun _t : G => (d x _t)) ((p28 x z y)))).symm).trans ((p4 x ((z ◇ (x ◇ y)) ◇ ((x ◇ y) ◇ x))))
  have p170 (x y z : G) : (d x ((y ◇ z) ◇ (z ◇ x))) = (z ◇ ((x ◇ ((y ◇ z) ◇ (z ◇ x))) ◇ x)) := by
    exact ((p139 x ((y ◇ z) ◇ (z ◇ x)) x)).trans ((congrArg (fun _t : G => (_t ◇ ((x ◇ ((y ◇ z) ◇ (z ◇ x))) ◇ x))) ((p2 x y z))))
  have p190 (u x y z : G) : ((x ◇ y) ◇ z) = ((u ◇ y) ◇ z) := by
    exact (((((p4 (d y z) ((x ◇ y) ◇ z))).symm).trans (((p139 (d y z) ((d y z) ◇ ((x ◇ y) ◇ z)) u)).trans ((congrArg (fun _t : G => ((u ◇ _t) ◇ (((d y z) ◇ ((d y z) ◇ ((x ◇ y) ◇ z))) ◇ (d y z)))) ((p9 y z x)))))).trans ((congrArg (fun _t : G => ((u ◇ y) ◇ (_t ◇ (d y z)))) ((p9 y z x))))).trans ((congrArg (fun _t : G => ((u ◇ y) ◇ _t)) ((p3 y z))))
  have p213 (x y : G) : (d (x ◇ y) x) = ((d x y) ◇ (((x ◇ y) ◇ x) ◇ (x ◇ y))) := by
    exact ((p139 (x ◇ y) x (a ◇ (x ◇ y)))).trans ((congrArg (fun _t : G => (_t ◇ (((x ◇ y) ◇ x) ◇ (x ◇ y)))) (((p139 x y a)).symm)))
  have p223 (u x y z : G) : ((x ◇ ((y ◇ ((z ◇ x) ◇ (x ◇ y))) ◇ y)) ◇ (((y ◇ ((z ◇ x) ◇ (x ◇ y))) ◇ y) ◇ (y ◇ ((z ◇ x) ◇ (x ◇ y))))) = ((y ◇ ((z ◇ x) ◇ (x ◇ y))) ◇ ((u ◇ y) ◇ x)) := by
    exact (((congrArg (fun _t : G => (_t ◇ (((y ◇ ((z ◇ x) ◇ (x ◇ y))) ◇ y) ◇ (y ◇ ((z ◇ x) ◇ (x ◇ y)))))) ((p170 y z x)))).symm).trans ((((p213 y ((z ◇ x) ◇ (x ◇ y)))).symm).trans ((p25 u y z x)))
  have p224 (u w x y z : G) : (x ◇ (x ◇ ((y ◇ (z ◇ u)) ◇ ((w ◇ u) ◇ x)))) = (z ◇ u) := by
    exact (((congrArg (fun _t : G => (x ◇ (x ◇ ((y ◇ (z ◇ u)) ◇ _t)))) ((p190 w z u x)))).symm).trans ((p2 x y (z ◇ u)))
  have p225 (u w x y z : G) : ((x ◇ y) ◇ ((z ◇ y) ◇ ((u ◇ w) ◇ (w ◇ (x ◇ y))))) = w := by
    exact (((congrArg (fun _t : G => ((x ◇ y) ◇ _t)) ((p190 z x y ((u ◇ w) ◇ (w ◇ (x ◇ y))))))).symm).trans ((p2 (x ◇ y) u w))
  have p227 (u w x y z : G) : ((x ◇ (y ◇ ((z ◇ u) ◇ (u ◇ y)))) ◇ w) = (u ◇ w) := by
    exact ((((congrArg (fun _t : G => (_t ◇ w)) ((p2 y z u)))).symm).trans ((p190 x y (y ◇ ((z ◇ u) ◇ (u ◇ y))) w))).symm
  have p229 (u x y z : G) : ((x ◇ (d y z)) ◇ u) = (z ◇ u) := by
    exact ((((congrArg (fun _t : G => (_t ◇ u)) ((p3 y z)))).symm).trans ((p190 x y (d y z) u))).symm
  have p230 (u x y z : G) : (d (x ◇ y) ((z ◇ y) ◇ u)) = u := by
    exact (((congrArg (fun _t : G => (d (x ◇ y) _t)) ((p190 z x y u)))).symm).trans ((p4 (x ◇ y) u))
  have p250 (u w x y z : G) : ((x ◇ ((y ◇ z) ◇ (z ◇ x))) ◇ ((x ◇ ((u ◇ z) ◇ (z ◇ x))) ◇ ((w ◇ x) ◇ z))) = x := by
    exact (((congrArg (fun _t : G => ((x ◇ _t) ◇ ((x ◇ ((u ◇ z) ◇ (z ◇ x))) ◇ ((w ◇ x) ◇ z)))) ((p190 y u z (z ◇ x))))).symm).trans ((p7 w x u z))
  have p255 (u w x y z : G) : ((x ◇ ((y ◇ z) ◇ (z ◇ u))) ◇ ((u ◇ ((y ◇ z) ◇ (z ◇ u))) ◇ ((w ◇ u) ◇ z))) = u := by
    exact (((p190 x u ((y ◇ z) ◇ (z ◇ u)) ((u ◇ ((y ◇ z) ◇ (z ◇ u))) ◇ ((w ◇ u) ◇ z)))).symm).trans ((p7 w u y z))
  have p256 (u v5 w x y z : G) : ((x ◇ ((y ◇ ((z ◇ u) ◇ (u ◇ y))) ◇ ((w ◇ y) ◇ u))) ◇ v5) = (y ◇ v5) := by
    exact ((((congrArg (fun _t : G => (_t ◇ v5)) ((p7 w y z u)))).symm).trans ((p190 x (y ◇ ((z ◇ u) ◇ (u ◇ y))) ((y ◇ ((z ◇ u) ◇ (u ◇ y))) ◇ ((w ◇ y) ◇ u)) v5))).symm
  have p265 (u x y z : G) : (d x y) = ((z ◇ (x ◇ y)) ◇ ((u ◇ y) ◇ x)) := by
    exact ((p139 x y z)).trans ((congrArg (fun _t : G => ((z ◇ (x ◇ y)) ◇ _t)) ((p190 u x y x))))
  have p267 (u x y z : G) : (((x ◇ ((y ◇ z) ◇ (z ◇ x))) ◇ ((u ◇ x) ◇ z)) ◇ (z ◇ x)) = ((y ◇ z) ◇ (z ◇ x)) := by
    exact ((((p224 (z ◇ x) ((x ◇ ((y ◇ z) ◇ (z ◇ x))) ◇ ((u ◇ x) ◇ z)) a x (y ◇ z))).symm).trans ((p102 z u a x y))).symm
  have p277 (u x y z : G) : ((x ◇ ((y ◇ z) ◇ (z ◇ x))) ◇ ((u ◇ x) ◇ z)) = (((y ◇ z) ◇ (z ◇ x)) ◇ (((y ◇ z) ◇ (z ◇ x)) ◇ z)) := by
    exact ((((congrArg (fun _t : G => (((y ◇ z) ◇ (z ◇ x)) ◇ (((y ◇ z) ◇ (z ◇ x)) ◇ _t))) ((p2 x y z)))).symm).trans ((((congrArg (fun _t : G => (((y ◇ z) ◇ (z ◇ x)) ◇ (((y ◇ z) ◇ (z ◇ x)) ◇ _t))) ((p256 z (x ◇ ((y ◇ z) ◇ (z ◇ x))) u a x y)))).symm).trans ((((congrArg (fun _t : G => (((y ◇ z) ◇ (z ◇ x)) ◇ (_t ◇ ((a ◇ ((x ◇ ((y ◇ z) ◇ (z ◇ x))) ◇ ((u ◇ x) ◇ z))) ◇ (x ◇ ((y ◇ z) ◇ (z ◇ x))))))) ((p267 u x y z)))).symm).trans ((((congrArg (fun _t : G => (_t ◇ ((((x ◇ ((y ◇ z) ◇ (z ◇ x))) ◇ ((u ◇ x) ◇ z)) ◇ (z ◇ x)) ◇ ((a ◇ ((x ◇ ((y ◇ z) ◇ (z ◇ x))) ◇ ((u ◇ x) ◇ z))) ◇ (x ◇ ((y ◇ z) ◇ (z ◇ x))))))) ((p267 u x y z)))).symm).trans ((p100 u a x y z)))))).symm
  have p283 (u x y z : G) : ((x ◇ ((y ◇ z) ◇ (z ◇ u))) ◇ (((y ◇ z) ◇ (z ◇ u)) ◇ (((y ◇ z) ◇ (z ◇ u)) ◇ z))) = u := by
    exact (((congrArg (fun _t : G => ((x ◇ ((y ◇ z) ◇ (z ◇ u))) ◇ _t)) ((p277 a u y z)))).symm).trans ((p255 u a x y z))
  have p284 (u x y z : G) : ((x ◇ ((y ◇ z) ◇ (z ◇ x))) ◇ (((u ◇ z) ◇ (z ◇ x)) ◇ (((u ◇ z) ◇ (z ◇ x)) ◇ z))) = x := by
    exact (((congrArg (fun _t : G => ((x ◇ ((y ◇ z) ◇ (z ◇ x))) ◇ _t)) ((p277 a x u z)))).symm).trans ((p250 u a x y z))
  have p286 (x y z : G) : ((x ◇ ((y ◇ ((z ◇ x) ◇ (x ◇ y))) ◇ y)) ◇ (((y ◇ ((z ◇ x) ◇ (x ◇ y))) ◇ y) ◇ (y ◇ ((z ◇ x) ◇ (x ◇ y))))) = (((z ◇ x) ◇ (x ◇ y)) ◇ (((z ◇ x) ◇ (x ◇ y)) ◇ x)) := by
    exact ((p223 a x y z)).trans ((p277 a y z x))
  have p315 (x y z : G) : ((((x ◇ y) ◇ (y ◇ z)) ◇ y) ◇ (y ◇ ((z ◇ ((x ◇ y) ◇ (y ◇ z))) ◇ (((x ◇ y) ◇ (y ◇ z)) ◇ y)))) = ((x ◇ y) ◇ (y ◇ z)) := by
    exact ((((p2 a z ((x ◇ y) ◇ (y ◇ z)))).symm).trans ((((congrArg (fun _t : G => (a ◇ (a ◇ ((z ◇ ((x ◇ y) ◇ (y ◇ z))) ◇ _t)))) ((p229 a (((x ◇ y) ◇ (y ◇ z)) ◇ y) y ((x ◇ y) ◇ (y ◇ z)))))).symm).trans ((((congrArg (fun _t : G => (a ◇ (a ◇ ((z ◇ ((x ◇ y) ◇ (y ◇ z))) ◇ (((((x ◇ y) ◇ (y ◇ z)) ◇ y) ◇ _t) ◇ a))))) (((p10 y ((x ◇ y) ◇ (y ◇ z)) z)).symm))).symm).trans ((p11 y (((x ◇ y) ◇ (y ◇ z)) ◇ y) a z x))))).symm
  have p321 (x y z : G) : ((((x ◇ y) ◇ (y ◇ z)) ◇ y) ◇ (d y ((x ◇ y) ◇ (y ◇ z)))) = ((x ◇ y) ◇ (y ◇ z)) := by
    exact ((((p2 a z ((x ◇ y) ◇ (y ◇ z)))).symm).trans ((((congrArg (fun _t : G => (a ◇ (a ◇ ((z ◇ ((x ◇ y) ◇ (y ◇ z))) ◇ (_t ◇ a))))) ((p315 x y z)))).symm).trans (((p11 y (((x ◇ y) ◇ (y ◇ z)) ◇ y) a z x)).trans ((congrArg (fun _t : G => ((((x ◇ y) ◇ (y ◇ z)) ◇ y) ◇ _t)) (((p10 y ((x ◇ y) ◇ (y ◇ z)) z)).symm)))))).symm
  have p395 (u x y z : G) : (((x ◇ y) ◇ (y ◇ z)) ◇ (((x ◇ y) ◇ (y ◇ z)) ◇ ((u ◇ (((x ◇ y) ◇ (y ◇ z)) ◇ y)) ◇ (z ◇ ((x ◇ y) ◇ (y ◇ z)))))) = (((x ◇ y) ◇ (y ◇ z)) ◇ y) := by
    exact (((congrArg (fun _t : G => (((x ◇ y) ◇ (y ◇ z)) ◇ (_t ◇ ((u ◇ (((x ◇ y) ◇ (y ◇ z)) ◇ y)) ◇ (z ◇ ((x ◇ y) ◇ (y ◇ z))))))) ((p315 x y z)))).symm).trans ((((congrArg (fun _t : G => (_t ◇ (((((x ◇ y) ◇ (y ◇ z)) ◇ y) ◇ (y ◇ ((z ◇ ((x ◇ y) ◇ (y ◇ z))) ◇ (((x ◇ y) ◇ (y ◇ z)) ◇ y)))) ◇ ((u ◇ (((x ◇ y) ◇ (y ◇ z)) ◇ y)) ◇ (z ◇ ((x ◇ y) ◇ (y ◇ z))))))) ((p321 x y z)))).symm).trans ((((congrArg (fun _t : G => (((((x ◇ y) ◇ (y ◇ z)) ◇ y) ◇ _t) ◇ (((((x ◇ y) ◇ (y ◇ z)) ◇ y) ◇ (y ◇ ((z ◇ ((x ◇ y) ◇ (y ◇ z))) ◇ (((x ◇ y) ◇ (y ◇ z)) ◇ y)))) ◇ ((u ◇ (((x ◇ y) ◇ (y ◇ z)) ◇ y)) ◇ (z ◇ ((x ◇ y) ◇ (y ◇ z))))))) (((p10 y ((x ◇ y) ◇ (y ◇ z)) z)).symm))).symm).trans ((p12 x u (((x ◇ y) ◇ (y ◇ z)) ◇ y) y z))))
  have p519 (u w x y z : G) : ((d x y) ◇ z) = ((u ◇ ((w ◇ y) ◇ x)) ◇ z) := by
    exact (((congrArg (fun _t : G => (_t ◇ z)) (((p265 w x y a)).symm))).symm).trans ((p190 u (a ◇ (x ◇ y)) ((w ◇ y) ◇ x) z))
  have p563 (u v5 v6 w x y z : G) : ((x ◇ (((y ◇ ((z ◇ u) ◇ (u ◇ y))) ◇ ((w ◇ v5) ◇ (v5 ◇ (y ◇ ((z ◇ u) ◇ (u ◇ y)))))) ◇ (u ◇ v5))) ◇ v6) = ((y ◇ ((z ◇ u) ◇ (u ◇ y))) ◇ v6) := by
    exact ((((congrArg (fun _t : G => (_t ◇ v6)) ((p14 w v5 y z u)))).symm).trans ((p190 x ((y ◇ ((z ◇ u) ◇ (u ◇ y))) ◇ ((w ◇ v5) ◇ (v5 ◇ (y ◇ ((z ◇ u) ◇ (u ◇ y)))))) (((y ◇ ((z ◇ u) ◇ (u ◇ y))) ◇ ((w ◇ v5) ◇ (v5 ◇ (y ◇ ((z ◇ u) ◇ (u ◇ y)))))) ◇ (u ◇ v5)) v6))).symm
  have p614 (u w x y z : G) : ((x ◇ ((y ◇ (z ◇ u)) ◇ z)) ◇ w) = (u ◇ w) := by
    exact ((((congrArg (fun _t : G => (_t ◇ w)) ((p4 z u)))).symm).trans ((p519 x y z (z ◇ u) w))).symm
  have p640 (u v5 v6 w x y z : G) : ((x ◇ ((y ◇ ((z ◇ u) ◇ w)) ◇ (v5 ◇ u))) ◇ v6) = (w ◇ v6) := by
    exact ((((congrArg (fun _t : G => (_t ◇ v6)) ((p230 w v5 u z)))).symm).trans ((p519 x y (v5 ◇ u) ((z ◇ u) ◇ w) v6))).symm
  have p655 (x y z : G) : (((x ◇ y) ◇ (y ◇ z)) ◇ (((x ◇ y) ◇ (y ◇ z)) ◇ y)) = (((x ◇ y) ◇ (y ◇ z)) ◇ y) := by
    exact (((congrArg (fun _t : G => (((x ◇ y) ◇ (y ◇ z)) ◇ (((x ◇ y) ◇ (y ◇ z)) ◇ _t))) ((p2 z x y)))).symm).trans ((((congrArg (fun _t : G => (((x ◇ y) ◇ (y ◇ z)) ◇ (((x ◇ y) ◇ (y ◇ z)) ◇ _t))) ((p614 z (z ◇ ((x ◇ y) ◇ (y ◇ z))) a (x ◇ y) y)))).symm).trans ((p395 a x y z)))
  have p680 (u x y z : G) : ((x ◇ ((y ◇ z) ◇ (z ◇ x))) ◇ u) = (z ◇ u) := by
    exact ((((p227 z u a x y)).symm).trans ((((p640 a z u (a ◇ (x ◇ ((y ◇ z) ◇ (z ◇ x)))) a (x ◇ ((y ◇ z) ◇ (z ◇ x))) a)).symm).trans ((p563 z a u a a x y)))).symm
  have p687 (x y z : G) : (((x ◇ y) ◇ (y ◇ z)) ◇ y) = ((y ◇ (y ◇ z)) ◇ ((y ◇ z) ◇ (z ◇ ((x ◇ y) ◇ (y ◇ z))))) := by
    exact (((((congrArg (fun _t : G => ((y ◇ (y ◇ z)) ◇ (_t ◇ (z ◇ ((x ◇ y) ◇ (y ◇ z)))))) ((p680 z z x y)))).symm).trans ((((congrArg (fun _t : G => ((y ◇ _t) ◇ (((z ◇ ((x ◇ y) ◇ (y ◇ z))) ◇ z) ◇ (z ◇ ((x ◇ y) ◇ (y ◇ z)))))) ((p680 z z x y)))).symm).trans ((p286 y z x)))).trans ((p655 x y z))).symm
  have p689 (x y : G) : (x ◇ y) = y := by
    exact (((p680 y y a x)).symm).trans ((((congrArg (fun _t : G => ((y ◇ ((a ◇ x) ◇ (x ◇ y))) ◇ _t)) ((p225 x y (a ◇ x) (x ◇ y) x)))).symm).trans ((((congrArg (fun _t : G => ((y ◇ ((a ◇ x) ◇ (x ◇ y))) ◇ (((a ◇ x) ◇ (x ◇ y)) ◇ _t))) ((p687 a x y)))).symm).trans ((p284 a y a x))))
  have p690 (x y : G) : x = y := by
    exact (((p689 y x)).symm).trans ((((congrArg (fun _t : G => (y ◇ _t)) ((p689 y x)))).symm).trans ((((congrArg (fun _t : G => (y ◇ (y ◇ _t))) ((p689 y x)))).symm).trans ((((congrArg (fun _t : G => (y ◇ (y ◇ (_t ◇ x)))) ((p689 x y)))).symm).trans ((((congrArg (fun _t : G => (y ◇ (y ◇ ((x ◇ _t) ◇ x)))) ((p689 x y)))).symm).trans ((((congrArg (fun _t : G => (y ◇ (y ◇ ((_t ◇ (x ◇ y)) ◇ x)))) ((p689 a x)))).symm).trans ((((congrArg (fun _t : G => (y ◇ (_t ◇ (((a ◇ x) ◇ (x ◇ y)) ◇ x)))) ((p689 x y)))).symm).trans ((((congrArg (fun _t : G => (y ◇ ((x ◇ _t) ◇ (((a ◇ x) ◇ (x ◇ y)) ◇ x)))) ((p689 x y)))).symm).trans ((((congrArg (fun _t : G => (y ◇ ((_t ◇ (x ◇ y)) ◇ (((a ◇ x) ◇ (x ◇ y)) ◇ x)))) ((p689 a x)))).symm).trans ((((congrArg (fun _t : G => (_t ◇ (((a ◇ x) ◇ (x ◇ y)) ◇ (((a ◇ x) ◇ (x ◇ y)) ◇ x)))) ((p689 a y)))).symm).trans ((((congrArg (fun _t : G => ((a ◇ _t) ◇ (((a ◇ x) ◇ (x ◇ y)) ◇ (((a ◇ x) ◇ (x ◇ y)) ◇ x)))) ((p689 x y)))).symm).trans ((((congrArg (fun _t : G => ((a ◇ (x ◇ _t)) ◇ (((a ◇ x) ◇ (x ◇ y)) ◇ (((a ◇ x) ◇ (x ◇ y)) ◇ x)))) ((p689 x y)))).symm).trans ((((congrArg (fun _t : G => ((a ◇ (_t ◇ (x ◇ y))) ◇ (((a ◇ x) ◇ (x ◇ y)) ◇ (((a ◇ x) ◇ (x ◇ y)) ◇ x)))) ((p689 a x)))).symm).trans ((p283 y a a x))))))))))))))
  exact (p690 a a).trans (p690 b a).symm

#print axioms finite_trivial

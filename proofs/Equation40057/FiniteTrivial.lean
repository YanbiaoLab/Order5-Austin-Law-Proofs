import Mathlib.Data.Fintype.Card
import JudgeMagma.Magma

@[reducible] def Equation2 (G : Type _) [Magma G] : Prop := ∀ (x y : G), x = y
@[reducible] def Equation5947 (G : Type _) [Magma G] : Prop := ∀ (x y z : G), x = y ◇ (y ◇ (x ◇ ((z ◇ x) ◇ y)))

theorem finite_trivial (G : Type*) [Magma G] [Finite G] (h : Equation5947 G) : Equation2 G := by
  intro a b
  have ls (y : G) : Function.Surjective (fun t : G => y ◇ t) := by
    intro x
    exact ⟨(y ◇ (x ◇ ((a ◇ x) ◇ y))), (h x y a).symm⟩
  have li (y : G) : Function.Injective (fun t : G => y ◇ t) :=
    Finite.injective_iff_surjective.mpr (ls y)
  let d (x y : G) : G := Classical.choose (ls x y)
  have ld1 (x y : G) : x ◇ d x y = y := Classical.choose_spec (ls x y)
  have ld2 (x y : G) : d x (x ◇ y) = y := li x (ld1 x (x ◇ y))
  have p2 (x y z : G) : (x ◇ (x ◇ (y ◇ ((z ◇ y) ◇ x)))) = y := by
    exact (h y x z).symm
  have p3 (x y : G) : (x ◇ (d x y)) = y := by
    exact (ld1 x y)
  have p4 (x y : G) : (d x (x ◇ y)) = y := by
    exact (ld2 x y)
  have p6 (u x y z : G) : (x ◇ (x ◇ ((y ◇ (z ◇ ((u ◇ z) ◇ y))) ◇ (z ◇ x)))) = (y ◇ (z ◇ ((u ◇ z) ◇ y))) := by
    exact (((congrArg (fun _t : G => (x ◇ (x ◇ ((y ◇ (z ◇ ((u ◇ z) ◇ y))) ◇ (_t ◇ x))))) ((p2 y z u)))).symm).trans ((p2 x (y ◇ (z ◇ ((u ◇ z) ◇ y))) y))
  have p7 (u x y z : G) : (((x ◇ y) ◇ (z ◇ ((u ◇ z) ◇ (x ◇ y)))) ◇ (((x ◇ y) ◇ (z ◇ ((u ◇ z) ◇ (x ◇ y)))) ◇ (y ◇ z))) = y := by
    exact (((congrArg (fun _t : G => (((x ◇ y) ◇ (z ◇ ((u ◇ z) ◇ (x ◇ y)))) ◇ (((x ◇ y) ◇ (z ◇ ((u ◇ z) ◇ (x ◇ y)))) ◇ (y ◇ _t)))) ((p2 (x ◇ y) z u)))).symm).trans ((p2 ((x ◇ y) ◇ (z ◇ ((u ◇ z) ◇ (x ◇ y)))) y x))
  have p8 (x y z : G) : (x ◇ (x ◇ ((d y z) ◇ (z ◇ x)))) = (d y z) := by
    exact (((congrArg (fun _t : G => (x ◇ (x ◇ ((d y z) ◇ (_t ◇ x))))) ((p3 y z)))).symm).trans ((p2 x (d y z) y))
  have p10 (x y z : G) : (d x y) = (x ◇ (y ◇ ((z ◇ y) ◇ x))) := by
    exact (((congrArg (fun _t : G => (d x _t)) ((p2 x y z)))).symm).trans ((p4 x (x ◇ (y ◇ ((z ◇ y) ◇ x)))))
  have p11 (u w x y z : G) : (x ◇ (x ◇ ((y ◇ ((z ◇ (u ◇ ((w ◇ u) ◇ z))) ◇ (u ◇ y))) ◇ ((z ◇ (u ◇ ((w ◇ u) ◇ z))) ◇ x)))) = (y ◇ ((z ◇ (u ◇ ((w ◇ u) ◇ z))) ◇ (u ◇ y))) := by
    exact (((congrArg (fun _t : G => (x ◇ (x ◇ ((y ◇ ((z ◇ (u ◇ ((w ◇ u) ◇ z))) ◇ (u ◇ y))) ◇ (_t ◇ x))))) ((p6 w y z u)))).symm).trans ((p2 x (y ◇ ((z ◇ (u ◇ ((w ◇ u) ◇ z))) ◇ (u ◇ y))) y))
  have p12 (u w x y z : G) : (((x ◇ y) ◇ ((z ◇ (u ◇ ((w ◇ u) ◇ z))) ◇ (u ◇ (x ◇ y)))) ◇ (((x ◇ y) ◇ ((z ◇ (u ◇ ((w ◇ u) ◇ z))) ◇ (u ◇ (x ◇ y)))) ◇ (y ◇ (z ◇ (u ◇ ((w ◇ u) ◇ z)))))) = y := by
    exact (((congrArg (fun _t : G => (((x ◇ y) ◇ ((z ◇ (u ◇ ((w ◇ u) ◇ z))) ◇ (u ◇ (x ◇ y)))) ◇ (((x ◇ y) ◇ ((z ◇ (u ◇ ((w ◇ u) ◇ z))) ◇ (u ◇ (x ◇ y)))) ◇ (y ◇ _t)))) ((p6 w (x ◇ y) z u)))).symm).trans ((p2 ((x ◇ y) ◇ ((z ◇ (u ◇ ((w ◇ u) ◇ z))) ◇ (u ◇ (x ◇ y)))) y x))
  have p18 (u x y z : G) : (d x (y ◇ (z ◇ ((u ◇ z) ◇ y)))) = (x ◇ ((y ◇ (z ◇ ((u ◇ z) ◇ y))) ◇ (z ◇ x))) := by
    exact (((congrArg (fun _t : G => (d x _t)) ((p6 u x y z)))).symm).trans ((p4 x (x ◇ ((y ◇ (z ◇ ((u ◇ z) ◇ y))) ◇ (z ◇ x)))))
  have p26 (x y z : G) : (d x (d y z)) = (x ◇ ((d y z) ◇ (z ◇ x))) := by
    exact ((p10 x (d y z) y)).trans ((congrArg (fun _t : G => (x ◇ ((d y z) ◇ (_t ◇ x)))) ((p3 y z))))
  have p28 (x y z : G) : (x ◇ ((x ◇ y) ◇ ((z ◇ (x ◇ y)) ◇ x))) = y := by
    exact (((p10 x (x ◇ y) z)).symm).trans ((p4 x y))
  have p41 (u x y z : G) : (d x (y ◇ ((z ◇ y) ◇ u))) = (x ◇ ((y ◇ ((z ◇ y) ◇ u)) ◇ ((d u y) ◇ x))) := by
    exact ((p10 x (y ◇ ((z ◇ y) ◇ u)) u)).trans ((congrArg (fun _t : G => (x ◇ ((y ◇ ((z ◇ y) ◇ u)) ◇ (_t ◇ x)))) (((p10 u y z)).symm)))
  have p44 (u x y z : G) : (((x ◇ y) ◇ ((d z u) ◇ (u ◇ (x ◇ y)))) ◇ (((x ◇ y) ◇ ((d z u) ◇ (u ◇ (x ◇ y)))) ◇ (y ◇ (d z u)))) = y := by
    exact (((congrArg (fun _t : G => (((x ◇ y) ◇ ((d z u) ◇ (u ◇ (x ◇ y)))) ◇ (((x ◇ y) ◇ ((d z u) ◇ (u ◇ (x ◇ y)))) ◇ (y ◇ _t)))) ((p8 (x ◇ y) z u)))).symm).trans ((p2 ((x ◇ y) ◇ ((d z u) ◇ (u ◇ (x ◇ y)))) y x))
  have p48 (u w x y z : G) : (x ◇ (x ◇ ((((y ◇ z) ◇ ((d u w) ◇ (w ◇ (y ◇ z)))) ◇ (z ◇ (d u w))) ◇ (z ◇ x)))) = (((y ◇ z) ◇ ((d u w) ◇ (w ◇ (y ◇ z)))) ◇ (z ◇ (d u w))) := by
    exact ((((congrArg (fun _t : G => (x ◇ (x ◇ ((((y ◇ z) ◇ ((d u w) ◇ (w ◇ (y ◇ z)))) ◇ (z ◇ _t)) ◇ (z ◇ x))))) ((p8 (y ◇ z) u w)))).symm).trans ((p6 y x ((y ◇ z) ◇ ((d u w) ◇ (w ◇ (y ◇ z)))) z))).trans ((congrArg (fun _t : G => (((y ◇ z) ◇ ((d u w) ◇ (w ◇ (y ◇ z)))) ◇ (z ◇ _t))) ((p8 (y ◇ z) u w))))
  have p52 (u x y z : G) : (d ((x ◇ y) ◇ ((d z u) ◇ (u ◇ (x ◇ y)))) y) = (((x ◇ y) ◇ ((d z u) ◇ (u ◇ (x ◇ y)))) ◇ (y ◇ (d z u))) := by
    exact ((p10 ((x ◇ y) ◇ ((d z u) ◇ (u ◇ (x ◇ y)))) y x)).trans ((congrArg (fun _t : G => (((x ◇ y) ◇ ((d z u) ◇ (u ◇ (x ◇ y)))) ◇ (y ◇ _t))) ((p8 (x ◇ y) z u))))
  have p57 (u x y z : G) : (x ◇ ((d y z) ◇ (z ◇ x))) = (x ◇ ((y ◇ (z ◇ ((u ◇ z) ◇ y))) ◇ (z ◇ x))) := by
    exact ((((p18 u x y z)).symm).trans ((((congrArg (fun _t : G => (d x _t)) ((p10 y z u)))).symm).trans ((p26 x y z)))).symm
  have p64 (x y z : G) : (d x y) = ((x ◇ y) ◇ ((z ◇ (x ◇ y)) ◇ x)) := by
    exact (((congrArg (fun _t : G => (d x _t)) ((p28 x y z)))).symm).trans ((p4 x ((x ◇ y) ◇ ((z ◇ (x ◇ y)) ◇ x))))
  have p78 (x y z : G) : ((x ◇ y) ◇ (((x ◇ y) ◇ ((z ◇ (x ◇ y)) ◇ x)) ◇ (y ◇ (x ◇ y)))) = ((z ◇ (x ◇ y)) ◇ x) := by
    exact (((congrArg (fun _t : G => ((x ◇ y) ◇ (((x ◇ y) ◇ ((z ◇ (x ◇ y)) ◇ x)) ◇ (_t ◇ (x ◇ y))))) ((p28 x y z)))).symm).trans ((p28 (x ◇ y) ((z ◇ (x ◇ y)) ◇ x) x))
  have p101 (x y z : G) : ((((x ◇ (y ◇ z)) ◇ z) ◇ (z ◇ ((y ◇ z) ◇ ((x ◇ (y ◇ z)) ◇ z)))) ◇ ((((x ◇ (y ◇ z)) ◇ z) ◇ (d z (y ◇ z))) ◇ (z ◇ z))) = z := by
    exact (((congrArg (fun _t : G => ((((x ◇ (y ◇ z)) ◇ z) ◇ (z ◇ ((y ◇ z) ◇ ((x ◇ (y ◇ z)) ◇ z)))) ◇ ((((x ◇ (y ◇ z)) ◇ z) ◇ _t) ◇ (z ◇ z)))) (((p10 z (y ◇ z) x)).symm))).symm).trans ((p7 y (x ◇ (y ◇ z)) z z))
  have p120 (u x y z : G) : (x ◇ ((y ◇ x) ◇ z)) = (x ◇ ((u ◇ x) ◇ z)) := by
    exact ((((p4 z (x ◇ ((y ◇ x) ◇ z)))).symm).trans (((p64 z (z ◇ (x ◇ ((y ◇ x) ◇ z))) u)).trans ((congrArg (fun _t : G => (_t ◇ ((u ◇ (z ◇ (z ◇ (x ◇ ((y ◇ x) ◇ z))))) ◇ z))) ((p2 z x y)))))).trans ((congrArg (fun _t : G => (x ◇ ((u ◇ _t) ◇ z))) ((p2 z x y))))
  have p126 (u w x y z : G) : (((x ◇ (y ◇ z)) ◇ y) ◇ (((x ◇ (y ◇ z)) ◇ y) ◇ ((u ◇ ((y ◇ z) ◇ ((w ◇ (y ◇ z)) ◇ u))) ◇ (d y z)))) = (u ◇ ((y ◇ z) ◇ ((w ◇ (y ◇ z)) ◇ u))) := by
    exact (((congrArg (fun _t : G => (((x ◇ (y ◇ z)) ◇ y) ◇ (((x ◇ (y ◇ z)) ◇ y) ◇ ((u ◇ ((y ◇ z) ◇ ((w ◇ (y ◇ z)) ◇ u))) ◇ _t)))) (((p64 y z x)).symm))).symm).trans ((p6 w ((x ◇ (y ◇ z)) ◇ y) u (y ◇ z)))
  have p145 (x y z : G) : (d (x ◇ y) ((z ◇ (x ◇ y)) ◇ x)) = (((x ◇ y) ◇ ((z ◇ (x ◇ y)) ◇ x)) ◇ (y ◇ (x ◇ y))) := by
    exact ((p64 (x ◇ y) ((z ◇ (x ◇ y)) ◇ x) x)).trans ((congrArg (fun _t : G => (((x ◇ y) ◇ ((z ◇ (x ◇ y)) ◇ x)) ◇ (_t ◇ (x ◇ y)))) ((p28 x y z))))
  have p165 (u x y z : G) : ((x ◇ y) ◇ z) = ((u ◇ y) ◇ z) := by
    exact (((p4 y ((x ◇ y) ◇ z))).symm).trans ((((congrArg (fun _t : G => (d y _t)) ((p120 x y u z)))).symm).trans ((p4 y ((u ◇ y) ◇ z))))
  have p216 (u w x y z : G) : ((x ◇ (y ◇ (z ◇ ((u ◇ z) ◇ y)))) ◇ w) = (z ◇ w) := by
    exact ((((congrArg (fun _t : G => (_t ◇ w)) ((p2 y z u)))).symm).trans ((p165 x y (y ◇ (z ◇ ((u ◇ z) ◇ y))) w))).symm
  have p218 (u x y z : G) : ((x ◇ (d y z)) ◇ u) = (z ◇ u) := by
    exact ((((congrArg (fun _t : G => (_t ◇ u)) ((p3 y z)))).symm).trans ((p165 x y (d y z) u))).symm
  have p219 (u x y z : G) : (d (x ◇ y) ((z ◇ y) ◇ u)) = u := by
    exact (((congrArg (fun _t : G => (d (x ◇ y) _t)) ((p165 z x y u)))).symm).trans ((p4 (x ◇ y) u))
  have p228 (u w x y z : G) : (d x (y ◇ z)) = (x ◇ ((u ◇ z) ◇ ((w ◇ (y ◇ z)) ◇ x))) := by
    exact ((p10 x (y ◇ z) w)).trans ((congrArg (fun _t : G => (x ◇ _t)) ((p165 u y z ((w ◇ (y ◇ z)) ◇ x)))))
  have p238 (u x y z : G) : (x ◇ ((y ◇ z) ◇ ((u ◇ (x ◇ z)) ◇ x))) = z := by
    exact (((congrArg (fun _t : G => (x ◇ _t)) ((p165 y x z ((u ◇ (x ◇ z)) ◇ x))))).symm).trans ((p28 x z u))
  have p243 (u x y z : G) : (d x y) = ((z ◇ y) ◇ ((u ◇ (x ◇ y)) ◇ x)) := by
    exact ((p64 x y u)).trans ((p165 z x y ((u ◇ (x ◇ y)) ◇ x)))
  have p248 (x y : G) : ((x ◇ y) ◇ ((x ◇ y) ◇ (y ◇ y))) = y := by
    exact (((p216 a ((x ◇ y) ◇ (y ◇ y)) ((a ◇ (x ◇ y)) ◇ y) y (x ◇ y))).symm).trans ((((congrArg (fun _t : G => ((((a ◇ (x ◇ y)) ◇ y) ◇ (y ◇ ((x ◇ y) ◇ ((a ◇ (x ◇ y)) ◇ y)))) ◇ _t)) ((p218 (y ◇ y) ((a ◇ (x ◇ y)) ◇ y) y (x ◇ y))))).symm).trans ((p101 a x y)))
  have p318 (u w x y z : G) : (x ◇ ((y ◇ (z ◇ ((u ◇ z) ◇ y))) ◇ (z ◇ x))) = (w ◇ (w ◇ ((x ◇ ((d y z) ◇ (z ◇ x))) ◇ ((y ◇ (z ◇ ((u ◇ z) ◇ y))) ◇ w)))) := by
    exact ((((congrArg (fun _t : G => (w ◇ (w ◇ ((x ◇ (_t ◇ (z ◇ x))) ◇ ((y ◇ (z ◇ ((u ◇ z) ◇ y))) ◇ w))))) (((p10 y z u)).symm))).symm).trans ((p11 z u w x y))).symm
  have p384 (x y : G) : (d (x ◇ y) y) = ((x ◇ y) ◇ (y ◇ y)) := by
    exact (((congrArg (fun _t : G => (d (x ◇ y) _t)) ((p248 x y)))).symm).trans ((p4 (x ◇ y) ((x ◇ y) ◇ (y ◇ y))))
  have p396 (x y z : G) : ((x ◇ y) ◇ ((z ◇ y) ◇ (y ◇ y))) = y := by
    exact ((((p248 z y)).symm).trans ((p165 x z y ((z ◇ y) ◇ (y ◇ y))))).symm
  have p411 (u x y z : G) : (d (x ◇ ((y ◇ x) ◇ z)) ((u ◇ x) ◇ z)) = ((x ◇ ((u ◇ x) ◇ z)) ◇ (((u ◇ x) ◇ z) ◇ ((u ◇ x) ◇ z))) := by
    exact (((congrArg (fun _t : G => (d _t ((u ◇ x) ◇ z))) ((p120 y x u z)))).symm).trans ((p384 x ((u ◇ x) ◇ z)))
  have p415 (u x y z : G) : (((x ◇ y) ◇ (y ◇ y)) ◇ (((x ◇ y) ◇ (y ◇ y)) ◇ ((d z (u ◇ y)) ◇ y))) = (d z (u ◇ y)) := by
    exact (((congrArg (fun _t : G => (((x ◇ y) ◇ (y ◇ y)) ◇ (((x ◇ y) ◇ (y ◇ y)) ◇ ((d z (u ◇ y)) ◇ _t)))) ((p396 u y x)))).symm).trans ((p8 ((x ◇ y) ◇ (y ◇ y)) z (u ◇ y)))
  have p434 (u v5 w x y z : G) : (((x ◇ y) ◇ ((z ◇ ((u ◇ ((w ◇ u) ◇ v5)) ◇ ((v5 ◇ (u ◇ ((w ◇ u) ◇ v5))) ◇ z))) ◇ ((u ◇ ((w ◇ u) ◇ v5)) ◇ (x ◇ y)))) ◇ (((x ◇ y) ◇ ((z ◇ ((u ◇ ((w ◇ u) ◇ v5)) ◇ ((d v5 u) ◇ z))) ◇ ((u ◇ ((w ◇ u) ◇ v5)) ◇ (x ◇ y)))) ◇ (y ◇ (z ◇ ((u ◇ ((w ◇ u) ◇ v5)) ◇ ((v5 ◇ (u ◇ ((w ◇ u) ◇ v5))) ◇ z)))))) = y := by
    exact (((congrArg (fun _t : G => (((x ◇ y) ◇ ((z ◇ ((u ◇ ((w ◇ u) ◇ v5)) ◇ ((v5 ◇ (u ◇ ((w ◇ u) ◇ v5))) ◇ z))) ◇ ((u ◇ ((w ◇ u) ◇ v5)) ◇ (x ◇ y)))) ◇ (((x ◇ y) ◇ ((z ◇ ((u ◇ ((w ◇ u) ◇ v5)) ◇ (_t ◇ z))) ◇ ((u ◇ ((w ◇ u) ◇ v5)) ◇ (x ◇ y)))) ◇ (y ◇ (z ◇ ((u ◇ ((w ◇ u) ◇ v5)) ◇ ((v5 ◇ (u ◇ ((w ◇ u) ◇ v5))) ◇ z))))))) (((p10 v5 u w)).symm))).symm).trans ((p12 (u ◇ ((w ◇ u) ◇ v5)) v5 x y z))
  have p505 (u w x y z : G) : (d x ((y ◇ z) ◇ ((u ◇ (w ◇ z)) ◇ w))) = (x ◇ (((y ◇ z) ◇ ((u ◇ (w ◇ z)) ◇ w)) ◇ (z ◇ x))) := by
    exact ((p10 x ((y ◇ z) ◇ ((u ◇ (w ◇ z)) ◇ w)) w)).trans ((congrArg (fun _t : G => (x ◇ (((y ◇ z) ◇ ((u ◇ (w ◇ z)) ◇ w)) ◇ (_t ◇ x)))) ((p238 u w y z))))
  have p511 (x y z : G) : (d x (y ◇ z)) = ((y ◇ z) ◇ ((y ◇ z) ◇ z)) := by
    exact ((((p218 ((y ◇ z) ◇ z) (a ◇ ((d x (y ◇ z)) ◇ z)) x (y ◇ z))).symm).trans ((((congrArg (fun _t : G => (((a ◇ ((d x (y ◇ z)) ◇ z)) ◇ (d x (y ◇ z))) ◇ _t)) ((p218 z (a ◇ ((d x (y ◇ z)) ◇ z)) x (y ◇ z))))).symm).trans ((((congrArg (fun _t : G => (((a ◇ ((d x (y ◇ z)) ◇ z)) ◇ (d x (y ◇ z))) ◇ (((a ◇ ((d x (y ◇ z)) ◇ z)) ◇ (d x (y ◇ z))) ◇ _t))) ((p238 a (d x (y ◇ z)) y z)))).symm).trans ((p8 ((a ◇ ((d x (y ◇ z)) ◇ z)) ◇ (d x (y ◇ z))) x (y ◇ z)))))).symm
  have p520 (u v5 w x y z : G) : ((x ◇ ((y ◇ z) ◇ ((u ◇ (w ◇ z)) ◇ w))) ◇ v5) = (z ◇ v5) := by
    exact ((((congrArg (fun _t : G => (_t ◇ v5)) ((p238 u w y z)))).symm).trans ((p165 x w ((y ◇ z) ◇ ((u ◇ (w ◇ z)) ◇ w)) v5))).symm
  have p525 (x y : G) : ((x ◇ y) ◇ ((x ◇ y) ◇ y)) = y := by
    exact (((p511 (a ◇ ((a ◇ x) ◇ ((a ◇ (a ◇ x)) ◇ a))) x y)).symm).trans ((((congrArg (fun _t : G => (d (a ◇ ((a ◇ x) ◇ ((a ◇ (a ◇ x)) ◇ a))) (_t ◇ y))) ((p238 a a a x)))).symm).trans ((p219 y a ((a ◇ x) ◇ ((a ◇ (a ◇ x)) ◇ a)) a)))
  have p528 (u x y z : G) : (x ◇ (((y ◇ x) ◇ ((z ◇ (u ◇ x)) ◇ u)) ◇ ((y ◇ x) ◇ ((z ◇ (u ◇ x)) ◇ u)))) = ((z ◇ (u ◇ x)) ◇ u) := by
    exact (((((p525 (y ◇ x) ((z ◇ (u ◇ x)) ◇ u))).symm).trans ((((p511 x (y ◇ x) ((z ◇ (u ◇ x)) ◇ u))).symm).trans ((((congrArg (fun _t : G => (d _t ((y ◇ x) ◇ ((z ◇ (u ◇ x)) ◇ u)))) ((p238 z u y x)))).symm).trans ((p384 u ((y ◇ x) ◇ ((z ◇ (u ◇ x)) ◇ u))))))).trans ((congrArg (fun _t : G => (_t ◇ (((y ◇ x) ◇ ((z ◇ (u ◇ x)) ◇ u)) ◇ ((y ◇ x) ◇ ((z ◇ (u ◇ x)) ◇ u))))) ((p238 z u y x))))).symm
  have p529 (u x y z : G) : ((x ◇ y) ◇ ((z ◇ (u ◇ y)) ◇ u)) = (y ◇ ((z ◇ (u ◇ y)) ◇ u)) := by
    exact ((((congrArg (fun _t : G => (y ◇ _t)) ((p528 u y x z)))).symm).trans ((((congrArg (fun _t : G => (y ◇ _t)) ((p520 z (((x ◇ y) ◇ ((z ◇ (u ◇ y)) ◇ u)) ◇ ((x ◇ y) ◇ ((z ◇ (u ◇ y)) ◇ u))) u a x y)))).symm).trans ((((congrArg (fun _t : G => (_t ◇ ((a ◇ ((x ◇ y) ◇ ((z ◇ (u ◇ y)) ◇ u))) ◇ (((x ◇ y) ◇ ((z ◇ (u ◇ y)) ◇ u)) ◇ ((x ◇ y) ◇ ((z ◇ (u ◇ y)) ◇ u)))))) ((p238 z u x y)))).symm).trans ((p396 u ((x ◇ y) ◇ ((z ◇ (u ◇ y)) ◇ u)) a))))).symm
  have p536 (u x y z : G) : (x ◇ ((y ◇ ((z ◇ (u ◇ y)) ◇ u)) ◇ (y ◇ x))) = ((z ◇ (u ◇ y)) ◇ u) := by
    exact (((((p525 y ((z ◇ (u ◇ y)) ◇ u))).symm).trans ((((p511 x y ((z ◇ (u ◇ y)) ◇ u))).symm).trans ((((congrArg (fun _t : G => (d x _t)) ((p529 u a y z)))).symm).trans ((p505 z u x a y))))).trans ((congrArg (fun _t : G => (x ◇ (_t ◇ (y ◇ x)))) ((p529 u a y z))))).symm
  have p541 (x : G) : (x ◇ x) = x := by
    exact (((((p525 (a ◇ x) (x ◇ x))).symm).trans ((((congrArg (fun _t : G => (((a ◇ x) ◇ (x ◇ x)) ◇ (((a ◇ x) ◇ (x ◇ x)) ◇ (_t ◇ x)))) ((p525 a x)))).symm).trans ((((congrArg (fun _t : G => (((a ◇ x) ◇ (x ◇ x)) ◇ (((a ◇ x) ◇ (x ◇ x)) ◇ (_t ◇ x)))) ((p511 a a x)))).symm).trans ((p415 a a x a))))).trans ((p511 a a x))).trans ((p525 a x))
  have p542 (x y z : G) : ((x ◇ ((y ◇ x) ◇ z)) ◇ ((y ◇ x) ◇ z)) = z := by
    exact (((((p525 (y ◇ x) z)).symm).trans ((((p511 (x ◇ ((a ◇ x) ◇ z)) (y ◇ x) z)).symm).trans ((p411 y x a z)))).trans ((congrArg (fun _t : G => ((x ◇ ((y ◇ x) ◇ z)) ◇ _t)) ((p541 ((y ◇ x) ◇ z)))))).symm
  have p553 (u w x y z : G) : (x ◇ ((y ◇ z) ◇ ((u ◇ (w ◇ z)) ◇ x))) = z := by
    exact ((((p525 w z)).symm).trans ((((p511 x w z)).symm).trans ((p228 y u x w z)))).symm
  have p556 (x y z : G) : ((x ◇ ((y ◇ (z ◇ x)) ◇ z)) ◇ (x ◇ (z ◇ x))) = z := by
    exact (((((p525 (y ◇ (z ◇ x)) z)).symm).trans ((((p511 (z ◇ x) (y ◇ (z ◇ x)) z)).symm).trans ((p145 z x y)))).trans ((congrArg (fun _t : G => (_t ◇ (x ◇ (z ◇ x)))) ((p529 z z x y))))).symm
  have p566 (u x y z : G) : (x ◇ ((y ◇ ((z ◇ y) ◇ u)) ◇ ((d u y) ◇ x))) = ((y ◇ ((z ◇ y) ◇ u)) ◇ u) := by
    exact ((((congrArg (fun _t : G => ((y ◇ ((z ◇ y) ◇ u)) ◇ _t)) ((p542 y z u)))).symm).trans ((((p511 x y ((z ◇ y) ◇ u))).symm).trans ((p41 u x y z)))).symm
  have p574 (x y z : G) : (x ◇ (x ◇ ((y ◇ (z ◇ x)) ◇ z))) = ((y ◇ (z ◇ x)) ◇ z) := by
    exact (((congrArg (fun _t : G => (x ◇ _t)) ((p541 (x ◇ ((y ◇ (z ◇ x)) ◇ z)))))).symm).trans ((((congrArg (fun _t : G => (x ◇ ((x ◇ ((y ◇ (z ◇ x)) ◇ z)) ◇ _t))) ((p529 z a x y)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (_t ◇ ((a ◇ x) ◇ ((y ◇ (z ◇ x)) ◇ z))))) ((p529 z a x y)))).symm).trans ((p528 z x a y))))
  have p583 (x y z : G) : (d x y) = (y ◇ ((z ◇ (x ◇ y)) ◇ x)) := by
    exact ((p243 z x y a)).trans ((p529 x a y z))
  have p601 (x y z : G) : ((x ◇ (y ◇ z)) ◇ y) = ((y ◇ z) ◇ y) := by
    exact ((((congrArg (fun _t : G => ((y ◇ z) ◇ _t)) ((p556 z x y)))).symm).trans ((((congrArg (fun _t : G => ((y ◇ z) ◇ (_t ◇ (z ◇ (y ◇ z))))) ((p529 y y z x)))).symm).trans ((p78 y z x)))).symm
  have p642 (u x y z : G) : (x ◇ (x ◇ (y ◇ ((z ◇ u) ◇ x)))) = y := by
    exact (((congrArg (fun _t : G => (x ◇ (x ◇ (y ◇ _t)))) ((p553 x u a u ((z ◇ u) ◇ x))))).symm).trans ((((congrArg (fun _t : G => (x ◇ (_t ◇ (y ◇ (a ◇ ((u ◇ ((z ◇ u) ◇ x)) ◇ ((x ◇ (u ◇ ((z ◇ u) ◇ x))) ◇ a))))))) ((p553 u (z ◇ u) (a ◇ y) (u ◇ ((z ◇ u) ◇ x)) x)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (((a ◇ y) ◇ (_t ◇ ((u ◇ ((z ◇ u) ◇ x)) ◇ (a ◇ y)))) ◇ (y ◇ (a ◇ ((u ◇ ((z ◇ u) ◇ x)) ◇ ((x ◇ (u ◇ ((z ◇ u) ◇ x))) ◇ a))))))) ((p566 x a u z)))).symm).trans ((((congrArg (fun _t : G => (_t ◇ (((a ◇ y) ◇ ((a ◇ ((u ◇ ((z ◇ u) ◇ x)) ◇ ((d x u) ◇ a))) ◇ ((u ◇ ((z ◇ u) ◇ x)) ◇ (a ◇ y)))) ◇ (y ◇ (a ◇ ((u ◇ ((z ◇ u) ◇ x)) ◇ ((x ◇ (u ◇ ((z ◇ u) ◇ x))) ◇ a))))))) ((p553 u (z ◇ u) (a ◇ y) (z ◇ u) x)))).symm).trans ((((congrArg (fun _t : G => (((a ◇ y) ◇ (_t ◇ ((u ◇ ((z ◇ u) ◇ x)) ◇ (a ◇ y)))) ◇ (((a ◇ y) ◇ ((a ◇ ((u ◇ ((z ◇ u) ◇ x)) ◇ ((d x u) ◇ a))) ◇ ((u ◇ ((z ◇ u) ◇ x)) ◇ (a ◇ y)))) ◇ (y ◇ (a ◇ ((u ◇ ((z ◇ u) ◇ x)) ◇ ((x ◇ (u ◇ ((z ◇ u) ◇ x))) ◇ a))))))) ((p553 x u a u ((z ◇ u) ◇ x))))).symm).trans ((p434 u x z a y a))))))
  have p644 (x y : G) : (((x ◇ y) ◇ x) ◇ (((x ◇ y) ◇ x) ◇ (y ◇ (d x y)))) = y := by
    exact ((((congrArg (fun _t : G => (((x ◇ y) ◇ x) ◇ (((x ◇ y) ◇ x) ◇ (_t ◇ (d x y))))) ((p553 a x a x y)))).symm).trans ((((congrArg (fun _t : G => (((x ◇ y) ◇ x) ◇ (_t ◇ ((a ◇ ((x ◇ y) ◇ ((a ◇ (x ◇ y)) ◇ a))) ◇ (d x y))))) ((p601 a x y)))).symm).trans ((((congrArg (fun _t : G => (_t ◇ (((a ◇ (x ◇ y)) ◇ x) ◇ ((a ◇ ((x ◇ y) ◇ ((a ◇ (x ◇ y)) ◇ a))) ◇ (d x y))))) ((p601 a x y)))).symm).trans ((p126 a a a x y))))).trans ((p553 a x a x y))
  have p685 (x y : G) : (d x y) = (y ◇ ((x ◇ y) ◇ x)) := by
    exact ((p583 x y a)).trans ((congrArg (fun _t : G => (y ◇ _t)) ((p601 a x y))))
  have p692 (x y : G) : (x ◇ (x ◇ ((y ◇ x) ◇ y))) = ((y ◇ x) ◇ y) := by
    exact ((((congrArg (fun _t : G => (x ◇ (x ◇ _t))) ((p601 a y x)))).symm).trans ((p574 x a y))).trans ((p601 a y x))
  have p698 (x y z : G) : (x ◇ ((y ◇ ((z ◇ y) ◇ z)) ◇ (y ◇ x))) = ((z ◇ y) ◇ z) := by
    exact ((((congrArg (fun _t : G => (x ◇ ((y ◇ _t) ◇ (y ◇ x)))) ((p601 a z y)))).symm).trans ((p536 z x y a))).trans ((p601 a z y))
  have p710 (u x y z : G) : (x ◇ ((y ◇ (z ◇ ((u ◇ z) ◇ y))) ◇ (z ◇ x))) = ((y ◇ z) ◇ y) := by
    exact ((((p318 u a x y z)).trans ((congrArg (fun _t : G => (a ◇ (a ◇ ((x ◇ (_t ◇ (z ◇ x))) ◇ ((y ◇ (z ◇ ((u ◇ z) ◇ y))) ◇ a))))) ((p685 y z))))).trans ((congrArg (fun _t : G => (a ◇ (a ◇ (_t ◇ ((y ◇ (z ◇ ((u ◇ z) ◇ y))) ◇ a))))) ((p698 x z y))))).trans ((p642 (z ◇ ((u ◇ z) ◇ y)) a ((y ◇ z) ◇ y) y))
  have p717 (x y : G) : ((x ◇ y) ◇ x) = y := by
    exact (((p541 ((x ◇ y) ◇ x))).symm).trans ((((congrArg (fun _t : G => (((x ◇ y) ◇ x) ◇ _t)) ((p541 ((x ◇ y) ◇ x))))).symm).trans ((((congrArg (fun _t : G => (((x ◇ y) ◇ x) ◇ (((x ◇ y) ◇ x) ◇ _t))) ((p692 y x)))).symm).trans ((((congrArg (fun _t : G => (((x ◇ y) ◇ x) ◇ (((x ◇ y) ◇ x) ◇ (y ◇ _t)))) ((p685 x y)))).symm).trans ((p644 x y)))))
  have p745 (x y : G) : (x ◇ (y ◇ (y ◇ x))) = y := by
    exact (((((congrArg (fun _t : G => (x ◇ (_t ◇ (y ◇ x)))) ((p541 y)))).symm).trans ((((congrArg (fun _t : G => (x ◇ ((y ◇ _t) ◇ (y ◇ x)))) ((p717 a y)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (_t ◇ (y ◇ x)))) ((p685 a y)))).symm).trans ((p57 a x a y))))).trans ((p710 a x a y))).trans ((p717 a y))
  have p746 (x y : G) : (x ◇ (y ◇ x)) = y := by
    exact (((((((((((p541 y)).symm).trans ((((congrArg (fun _t : G => (y ◇ _t)) ((p717 x y)))).symm).trans ((((p685 x y)).symm).trans ((((congrArg (fun _t : G => (d _t y)) ((p745 (a ◇ y) x)))).symm).trans ((((congrArg (fun _t : G => (d ((a ◇ y) ◇ (_t ◇ (x ◇ (a ◇ y)))) y)) ((p541 x)))).symm).trans ((((congrArg (fun _t : G => (d ((a ◇ y) ◇ ((x ◇ _t) ◇ (x ◇ (a ◇ y)))) y)) ((p717 a x)))).symm).trans ((((congrArg (fun _t : G => (d ((a ◇ y) ◇ (_t ◇ (x ◇ (a ◇ y)))) y)) ((p685 a x)))).symm).trans ((p52 x a y a))))))))).trans ((congrArg (fun _t : G => (((a ◇ y) ◇ (_t ◇ (x ◇ (a ◇ y)))) ◇ (y ◇ (d a x)))) ((p685 a x))))).trans ((congrArg (fun _t : G => (((a ◇ y) ◇ ((x ◇ _t) ◇ (x ◇ (a ◇ y)))) ◇ (y ◇ (d a x)))) ((p717 a x))))).trans ((congrArg (fun _t : G => (((a ◇ y) ◇ (_t ◇ (x ◇ (a ◇ y)))) ◇ (y ◇ (d a x)))) ((p541 x))))).trans ((congrArg (fun _t : G => (_t ◇ (y ◇ (d a x)))) ((p745 (a ◇ y) x))))).trans ((congrArg (fun _t : G => (x ◇ (y ◇ _t))) ((p685 a x))))).trans ((congrArg (fun _t : G => (x ◇ (y ◇ (x ◇ _t)))) ((p717 a x))))).trans ((congrArg (fun _t : G => (x ◇ (y ◇ _t))) ((p541 x))))).symm
  have p748 (x y : G) : (x ◇ y) = y := by
    exact (((((((((((congrArg (fun _t : G => (x ◇ _t)) ((p745 x y)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (x ◇ (_t ◇ (y ◇ x))))) ((p746 a y)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (x ◇ ((a ◇ (y ◇ _t)) ◇ (y ◇ x))))) ((p541 a)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (x ◇ ((a ◇ (y ◇ (a ◇ _t))) ◇ (y ◇ x))))) ((p717 a a)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (x ◇ ((a ◇ (y ◇ _t)) ◇ (y ◇ x))))) ((p685 a a)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (x ◇ ((_t ◇ (y ◇ (d a a))) ◇ (y ◇ x))))) ((p745 (a ◇ y) a)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (x ◇ ((((a ◇ y) ◇ (_t ◇ (a ◇ (a ◇ y)))) ◇ (y ◇ (d a a))) ◇ (y ◇ x))))) ((p541 a)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (x ◇ ((((a ◇ y) ◇ ((a ◇ _t) ◇ (a ◇ (a ◇ y)))) ◇ (y ◇ (d a a))) ◇ (y ◇ x))))) ((p717 a a)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (x ◇ ((((a ◇ y) ◇ (_t ◇ (a ◇ (a ◇ y)))) ◇ (y ◇ (d a a))) ◇ (y ◇ x))))) ((p685 a a)))).symm).trans ((p48 a a x a y))))))))))).trans ((congrArg (fun _t : G => (((a ◇ y) ◇ (_t ◇ (a ◇ (a ◇ y)))) ◇ (y ◇ (d a a)))) ((p685 a a))))).trans ((congrArg (fun _t : G => (((a ◇ y) ◇ ((a ◇ _t) ◇ (a ◇ (a ◇ y)))) ◇ (y ◇ (d a a)))) ((p717 a a))))).trans ((congrArg (fun _t : G => (((a ◇ y) ◇ (_t ◇ (a ◇ (a ◇ y)))) ◇ (y ◇ (d a a)))) ((p541 a))))).trans ((congrArg (fun _t : G => (_t ◇ (y ◇ (d a a)))) ((p745 (a ◇ y) a))))).trans ((congrArg (fun _t : G => (a ◇ (y ◇ _t))) ((p685 a a))))).trans ((congrArg (fun _t : G => (a ◇ (y ◇ (a ◇ _t)))) ((p717 a a))))).trans ((congrArg (fun _t : G => (a ◇ (y ◇ _t))) ((p541 a))))).trans ((p746 a y))
  have p749 (x y : G) : x = y := by
    exact (((p748 y x)).symm).trans ((((congrArg (fun _t : G => (y ◇ _t)) ((p748 y x)))).symm).trans ((((congrArg (fun _t : G => (y ◇ (y ◇ _t))) ((p748 y x)))).symm).trans ((((congrArg (fun _t : G => (y ◇ (y ◇ (y ◇ _t)))) ((p748 a x)))).symm).trans ((((congrArg (fun _t : G => (y ◇ (y ◇ (y ◇ (a ◇ _t))))) ((p748 a x)))).symm).trans ((((congrArg (fun _t : G => (y ◇ (y ◇ (y ◇ (a ◇ (_t ◇ x)))))) ((p748 x a)))).symm).trans ((((congrArg (fun _t : G => (y ◇ (y ◇ (y ◇ _t)))) ((p685 x a)))).symm).trans ((((congrArg (fun _t : G => (y ◇ (_t ◇ (y ◇ (d x a))))) ((p541 y)))).symm).trans ((((congrArg (fun _t : G => (y ◇ ((y ◇ _t) ◇ (y ◇ (d x a))))) ((p748 x y)))).symm).trans ((((congrArg (fun _t : G => (y ◇ ((y ◇ (x ◇ _t)) ◇ (y ◇ (d x a))))) ((p748 a y)))).symm).trans ((((congrArg (fun _t : G => (y ◇ ((y ◇ (x ◇ (a ◇ _t))) ◇ (y ◇ (d x a))))) ((p748 a y)))).symm).trans ((((congrArg (fun _t : G => (y ◇ ((y ◇ (_t ◇ (a ◇ (a ◇ y)))) ◇ (y ◇ (d x a))))) ((p748 a x)))).symm).trans ((((congrArg (fun _t : G => (y ◇ ((y ◇ ((a ◇ _t) ◇ (a ◇ (a ◇ y)))) ◇ (y ◇ (d x a))))) ((p748 a x)))).symm).trans ((((congrArg (fun _t : G => (y ◇ ((y ◇ ((a ◇ (_t ◇ x)) ◇ (a ◇ (a ◇ y)))) ◇ (y ◇ (d x a))))) ((p748 x a)))).symm).trans ((((congrArg (fun _t : G => (y ◇ ((y ◇ (_t ◇ (a ◇ (a ◇ y)))) ◇ (y ◇ (d x a))))) ((p685 x a)))).symm).trans ((((congrArg (fun _t : G => (y ◇ ((_t ◇ ((d x a) ◇ (a ◇ (a ◇ y)))) ◇ (y ◇ (d x a))))) ((p748 a y)))).symm).trans ((((congrArg (fun _t : G => (_t ◇ (((a ◇ y) ◇ ((d x a) ◇ (a ◇ (a ◇ y)))) ◇ (y ◇ (d x a))))) ((p541 y)))).symm).trans ((((congrArg (fun _t : G => ((y ◇ _t) ◇ (((a ◇ y) ◇ ((d x a) ◇ (a ◇ (a ◇ y)))) ◇ (y ◇ (d x a))))) ((p748 x y)))).symm).trans ((((congrArg (fun _t : G => ((y ◇ (x ◇ _t)) ◇ (((a ◇ y) ◇ ((d x a) ◇ (a ◇ (a ◇ y)))) ◇ (y ◇ (d x a))))) ((p748 a y)))).symm).trans ((((congrArg (fun _t : G => ((y ◇ (x ◇ (a ◇ _t))) ◇ (((a ◇ y) ◇ ((d x a) ◇ (a ◇ (a ◇ y)))) ◇ (y ◇ (d x a))))) ((p748 a y)))).symm).trans ((((congrArg (fun _t : G => ((y ◇ (_t ◇ (a ◇ (a ◇ y)))) ◇ (((a ◇ y) ◇ ((d x a) ◇ (a ◇ (a ◇ y)))) ◇ (y ◇ (d x a))))) ((p748 a x)))).symm).trans ((((congrArg (fun _t : G => ((y ◇ ((a ◇ _t) ◇ (a ◇ (a ◇ y)))) ◇ (((a ◇ y) ◇ ((d x a) ◇ (a ◇ (a ◇ y)))) ◇ (y ◇ (d x a))))) ((p748 a x)))).symm).trans ((((congrArg (fun _t : G => ((y ◇ ((a ◇ (_t ◇ x)) ◇ (a ◇ (a ◇ y)))) ◇ (((a ◇ y) ◇ ((d x a) ◇ (a ◇ (a ◇ y)))) ◇ (y ◇ (d x a))))) ((p748 x a)))).symm).trans ((((congrArg (fun _t : G => ((y ◇ (_t ◇ (a ◇ (a ◇ y)))) ◇ (((a ◇ y) ◇ ((d x a) ◇ (a ◇ (a ◇ y)))) ◇ (y ◇ (d x a))))) ((p685 x a)))).symm).trans ((((congrArg (fun _t : G => ((_t ◇ ((d x a) ◇ (a ◇ (a ◇ y)))) ◇ (((a ◇ y) ◇ ((d x a) ◇ (a ◇ (a ◇ y)))) ◇ (y ◇ (d x a))))) ((p748 a y)))).symm).trans ((p44 a a y x))))))))))))))))))))))))))
  exact (p749 a a).trans (p749 b a).symm

@[reducible] def Equation40057 (G : Type _) [Magma G] : Prop := ∀ (x y z : G), x = (((y ◇ (x ◇ z)) ◇ x) ◇ y) ◇ y

theorem finite_trivial_dual (G : Type*) [Magma G] [Finite G] (h : Equation40057 G) : Equation2 G := by
  let opposite : Magma G := ⟨fun x y => y ◇ x⟩
  have hd : @ Equation5947 G opposite := by
    intro x y z
    exact h x y z
  exact @ finite_trivial G opposite inferInstance hd

#print axioms finite_trivial_dual

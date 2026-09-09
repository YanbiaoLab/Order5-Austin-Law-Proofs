import Mathlib.Data.Fintype.Card
import JudgeMagma.Magma

@[reducible] def Equation2 (G : Type _) [Magma G] : Prop := ∀ (x y : G), x = y
@[reducible] def Equation5012 (G : Type _) [Magma G] : Prop := ∀ (x y z : G), x = y ◇ (x ◇ (z ◇ (z ◇ (y ◇ z))))

theorem finite_trivial (G : Type*) [Magma G] [Finite G] (h : Equation5012 G) : Equation2 G := by
  intro a b
  have ls (y : G) : Function.Surjective (fun t : G => y ◇ t) := by
    intro x
    exact ⟨(x ◇ (a ◇ (a ◇ (y ◇ a)))), (h x y a).symm⟩
  have li (y : G) : Function.Injective (fun t : G => y ◇ t) :=
    Finite.injective_iff_surjective.mpr (ls y)
  let d (x y : G) : G := Classical.choose (ls x y)
  have ld1 (x y : G) : x ◇ d x y = y := Classical.choose_spec (ls x y)
  have ld2 (x y : G) : d x (x ◇ y) = y := li x (ld1 x (x ◇ y))
  have p2 (x y z : G) : (x ◇ (y ◇ (z ◇ (z ◇ (x ◇ z))))) = y := by
    exact (h y x z).symm
  have p4 (x y : G) : (d x (x ◇ y)) = y := by
    exact (ld2 x y)
  have p6 (u x y z : G) : (x ◇ (y ◇ ((z ◇ (u ◇ (u ◇ (x ◇ u)))) ◇ ((z ◇ (u ◇ (u ◇ (x ◇ u)))) ◇ z)))) = y := by
    exact (((congrArg (fun _t : G => (x ◇ (y ◇ ((z ◇ (u ◇ (u ◇ (x ◇ u)))) ◇ ((z ◇ (u ◇ (u ◇ (x ◇ u)))) ◇ _t))))) ((p2 x z u)))).symm).trans ((p2 x y (z ◇ (u ◇ (u ◇ (x ◇ u))))))
  have p8 (x y z : G) : (d x y) = (y ◇ (z ◇ (z ◇ (x ◇ z)))) := by
    exact (((congrArg (fun _t : G => (d x _t)) ((p2 x y z)))).symm).trans ((p4 x (y ◇ (z ◇ (z ◇ (x ◇ z))))))
  have p15 (x y z : G) : ((x ◇ y) ◇ (z ◇ (z ◇ (x ◇ z)))) = y := by
    exact (((p8 x (x ◇ y) z)).symm).trans ((p4 x y))
  have p25 (u x y z : G) : (x ◇ (y ◇ (y ◇ (z ◇ y)))) = (x ◇ (u ◇ (u ◇ (z ◇ u)))) := by
    exact (((p8 z x y)).symm).trans ((p8 z x u))
  have p28 (u x y z : G) : ((x ◇ y) ◇ (z ◇ ((u ◇ (u ◇ (x ◇ u))) ◇ ((u ◇ (u ◇ (x ◇ u))) ◇ y)))) = z := by
    exact (((congrArg (fun _t : G => ((x ◇ y) ◇ (z ◇ ((u ◇ (u ◇ (x ◇ u))) ◇ ((u ◇ (u ◇ (x ◇ u))) ◇ _t))))) ((p15 x y u)))).symm).trans ((p2 (x ◇ y) z (u ◇ (u ◇ (x ◇ u)))))
  have p38 (x y : G) : (d x y) = (y ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ x))) := by
    exact ((p8 x y (x ◇ (x ◇ x)))).trans ((congrArg (fun _t : G => (y ◇ ((x ◇ (x ◇ x)) ◇ _t))) ((p15 x (x ◇ x) x))))
  have p39 (x y : G) : ((x ◇ y) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ x))) = y := by
    exact (((p38 x (x ◇ y))).symm).trans (((p8 x (x ◇ y) a)).trans ((p15 x y a)))
  have p69 (u v5 w x y z : G) : (x ◇ (y ◇ ((z ◇ ((u ◇ (u ◇ (w ◇ u))) ◇ ((u ◇ (u ◇ (w ◇ u))) ◇ (x ◇ (u ◇ (u ◇ (w ◇ u))))))) ◇ ((z ◇ ((u ◇ (u ◇ (w ◇ u))) ◇ ((u ◇ (u ◇ (w ◇ u))) ◇ (x ◇ (v5 ◇ (v5 ◇ (w ◇ v5))))))) ◇ z)))) = y := by
    exact (((congrArg (fun _t : G => (x ◇ (y ◇ ((z ◇ ((u ◇ (u ◇ (w ◇ u))) ◇ ((u ◇ (u ◇ (w ◇ u))) ◇ (x ◇ (u ◇ (u ◇ (w ◇ u))))))) ◇ ((z ◇ ((u ◇ (u ◇ (w ◇ u))) ◇ ((u ◇ (u ◇ (w ◇ u))) ◇ _t))) ◇ z))))) ((p25 v5 x u w)))).symm).trans ((p6 (u ◇ (u ◇ (w ◇ u))) x y z))
  have p72 (x y z : G) : (x ◇ (x ◇ (y ◇ x))) = (z ◇ (z ◇ (y ◇ z))) := by
    exact (((p15 a (x ◇ (x ◇ (y ◇ x))) a)).symm).trans ((((congrArg (fun _t : G => (_t ◇ (a ◇ (a ◇ (a ◇ a))))) ((p25 x a z y)))).symm).trans ((p15 a (z ◇ (z ◇ (y ◇ z))) a)))
  have p79 (u x y z : G) : (x ◇ (((y ◇ (y ◇ (z ◇ y))) ◇ ((y ◇ (y ◇ (z ◇ y))) ◇ (y ◇ (y ◇ (z ◇ y))))) ◇ ((y ◇ (y ◇ (z ◇ y))) ◇ (u ◇ (u ◇ (z ◇ u)))))) = (x ◇ (((y ◇ (y ◇ (z ◇ y))) ◇ ((y ◇ (y ◇ (z ◇ y))) ◇ (y ◇ (y ◇ (z ◇ y))))) ◇ ((y ◇ (y ◇ (z ◇ y))) ◇ (y ◇ (y ◇ (z ◇ y)))))) := by
    exact ((((p38 (y ◇ (y ◇ (z ◇ y))) x)).symm).trans (((p38 (y ◇ (y ◇ (z ◇ y))) x)).trans ((congrArg (fun _t : G => (x ◇ (((y ◇ (y ◇ (z ◇ y))) ◇ ((y ◇ (y ◇ (z ◇ y))) ◇ (y ◇ (y ◇ (z ◇ y))))) ◇ _t))) ((p25 u (y ◇ (y ◇ (z ◇ y))) y z)))))).symm
  have p83 (x y : G) : ((x ◇ (x ◇ x)) ◇ (y ◇ ((x ◇ x) ◇ x))) = y := by
    exact (((congrArg (fun _t : G => ((x ◇ (x ◇ x)) ◇ (y ◇ ((x ◇ x) ◇ _t)))) ((p39 x x)))).symm).trans ((p2 (x ◇ (x ◇ x)) y (x ◇ x)))
  have p91 (u x y z : G) : (((x ◇ (x ◇ (y ◇ x))) ◇ z) ◇ (((x ◇ (x ◇ (y ◇ x))) ◇ ((x ◇ (x ◇ (y ◇ x))) ◇ (x ◇ (x ◇ (y ◇ x))))) ◇ ((x ◇ (x ◇ (y ◇ x))) ◇ (u ◇ (u ◇ (y ◇ u)))))) = z := by
    exact (((congrArg (fun _t : G => (((x ◇ (x ◇ (y ◇ x))) ◇ z) ◇ (((x ◇ (x ◇ (y ◇ x))) ◇ ((x ◇ (x ◇ (y ◇ x))) ◇ (x ◇ (x ◇ (y ◇ x))))) ◇ _t))) ((p25 u (x ◇ (x ◇ (y ◇ x))) x y)))).symm).trans ((p39 (x ◇ (x ◇ (y ◇ x))) z))
  have p103 (x y : G) : (((x ◇ (x ◇ (y ◇ x))) ◇ ((x ◇ (x ◇ (y ◇ x))) ◇ (x ◇ (x ◇ (y ◇ x))))) ◇ ((x ◇ (x ◇ (y ◇ x))) ◇ (x ◇ (x ◇ (y ◇ x))))) = y := by
    exact (((congrArg (fun _t : G => (((x ◇ (x ◇ (y ◇ x))) ◇ ((x ◇ (x ◇ (y ◇ x))) ◇ (x ◇ (x ◇ (y ◇ x))))) ◇ _t)) ((p2 y ((x ◇ (x ◇ (y ◇ x))) ◇ (x ◇ (x ◇ (y ◇ x)))) x)))).symm).trans ((p83 (x ◇ (x ◇ (y ◇ x))) y))
  have p114 (u x y z : G) : (x ◇ (((y ◇ (y ◇ (z ◇ y))) ◇ ((y ◇ (y ◇ (z ◇ y))) ◇ (y ◇ (y ◇ (z ◇ y))))) ◇ ((y ◇ (y ◇ (z ◇ y))) ◇ (u ◇ (u ◇ (z ◇ u)))))) = (x ◇ z) := by
    exact ((p79 u x y z)).trans ((congrArg (fun _t : G => (x ◇ _t)) ((p103 y z))))
  have p118 (x y z : G) : (((x ◇ (x ◇ (y ◇ x))) ◇ z) ◇ y) = z := by
    exact (((p114 a ((x ◇ (x ◇ (y ◇ x))) ◇ z) x y)).symm).trans ((p91 a x y z))
  have p138 (u x y z : G) : ((x ◇ (x ◇ (y ◇ x))) ◇ (z ◇ (x ◇ (x ◇ (y ◇ x))))) = ((u ◇ (u ◇ (z ◇ u))) ◇ y) := by
    exact ((((congrArg (fun _t : G => (_t ◇ y)) ((p72 (x ◇ (x ◇ (y ◇ x))) z u)))).symm).trans ((p118 x y ((x ◇ (x ◇ (y ◇ x))) ◇ (z ◇ (x ◇ (x ◇ (y ◇ x)))))))).symm
  have p181 (x y z : G) : ((x ◇ (x ◇ (y ◇ x))) ◇ z) = (y ◇ z) := by
    exact (((p15 y ((x ◇ (x ◇ (y ◇ x))) ◇ z) x)).symm).trans ((((congrArg (fun _t : G => ((y ◇ ((x ◇ (x ◇ (y ◇ x))) ◇ z)) ◇ _t)) ((p28 x y z (x ◇ (x ◇ (y ◇ x))))))).symm).trans ((p28 x y ((x ◇ (x ◇ (y ◇ x))) ◇ z) (y ◇ z))))
  have p188 (x y : G) : (x ◇ y) = x := by
    exact (((((p2 y x a)).symm).trans ((((p181 a y (x ◇ (a ◇ (a ◇ (y ◇ a)))))).symm).trans ((p138 a a y x)))).trans ((p181 a x y))).symm
  have p189 (x y : G) : x = y := by
    exact (((p188 x y)).symm).trans ((((congrArg (fun _t : G => (x ◇ _t)) ((p188 y a)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (y ◇ _t))) ((p188 a a)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (y ◇ (a ◇ _t)))) ((p188 a a)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (y ◇ (a ◇ (_t ◇ a))))) ((p188 a a)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (y ◇ (a ◇ ((a ◇ _t) ◇ a))))) ((p188 a a)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (y ◇ (a ◇ ((a ◇ (a ◇ _t)) ◇ a))))) ((p188 a x)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (y ◇ (a ◇ ((a ◇ (a ◇ (a ◇ _t))) ◇ a))))) ((p188 x a)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (y ◇ (a ◇ ((a ◇ (a ◇ (a ◇ (x ◇ _t)))) ◇ a))))) ((p188 a a)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (y ◇ (a ◇ ((a ◇ (a ◇ (a ◇ (x ◇ (a ◇ _t))))) ◇ a))))) ((p188 a a)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (y ◇ (a ◇ ((a ◇ (a ◇ (a ◇ (x ◇ (a ◇ (a ◇ _t)))))) ◇ a))))) ((p188 a a)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (y ◇ (a ◇ ((a ◇ (a ◇ (_t ◇ (x ◇ (a ◇ (a ◇ (a ◇ a))))))) ◇ a))))) ((p188 a a)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (y ◇ (a ◇ ((a ◇ (a ◇ ((a ◇ _t) ◇ (x ◇ (a ◇ (a ◇ (a ◇ a))))))) ◇ a))))) ((p188 a a)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (y ◇ (a ◇ ((a ◇ (a ◇ ((a ◇ (a ◇ _t)) ◇ (x ◇ (a ◇ (a ◇ (a ◇ a))))))) ◇ a))))) ((p188 a a)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (y ◇ (a ◇ ((a ◇ (_t ◇ ((a ◇ (a ◇ (a ◇ a))) ◇ (x ◇ (a ◇ (a ◇ (a ◇ a))))))) ◇ a))))) ((p188 a a)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (y ◇ (a ◇ ((a ◇ ((a ◇ _t) ◇ ((a ◇ (a ◇ (a ◇ a))) ◇ (x ◇ (a ◇ (a ◇ (a ◇ a))))))) ◇ a))))) ((p188 a a)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (y ◇ (a ◇ ((a ◇ ((a ◇ (a ◇ _t)) ◇ ((a ◇ (a ◇ (a ◇ a))) ◇ (x ◇ (a ◇ (a ◇ (a ◇ a))))))) ◇ a))))) ((p188 a a)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (y ◇ (_t ◇ ((a ◇ ((a ◇ (a ◇ (a ◇ a))) ◇ ((a ◇ (a ◇ (a ◇ a))) ◇ (x ◇ (a ◇ (a ◇ (a ◇ a))))))) ◇ a))))) ((p188 a a)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (y ◇ ((a ◇ _t) ◇ ((a ◇ ((a ◇ (a ◇ (a ◇ a))) ◇ ((a ◇ (a ◇ (a ◇ a))) ◇ (x ◇ (a ◇ (a ◇ (a ◇ a))))))) ◇ a))))) ((p188 a a)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (y ◇ ((a ◇ (a ◇ _t)) ◇ ((a ◇ ((a ◇ (a ◇ (a ◇ a))) ◇ ((a ◇ (a ◇ (a ◇ a))) ◇ (x ◇ (a ◇ (a ◇ (a ◇ a))))))) ◇ a))))) ((p188 a x)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (y ◇ ((a ◇ (a ◇ (a ◇ _t))) ◇ ((a ◇ ((a ◇ (a ◇ (a ◇ a))) ◇ ((a ◇ (a ◇ (a ◇ a))) ◇ (x ◇ (a ◇ (a ◇ (a ◇ a))))))) ◇ a))))) ((p188 x a)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (y ◇ ((a ◇ (a ◇ (a ◇ (x ◇ _t)))) ◇ ((a ◇ ((a ◇ (a ◇ (a ◇ a))) ◇ ((a ◇ (a ◇ (a ◇ a))) ◇ (x ◇ (a ◇ (a ◇ (a ◇ a))))))) ◇ a))))) ((p188 a a)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (y ◇ ((a ◇ (a ◇ (a ◇ (x ◇ (a ◇ _t))))) ◇ ((a ◇ ((a ◇ (a ◇ (a ◇ a))) ◇ ((a ◇ (a ◇ (a ◇ a))) ◇ (x ◇ (a ◇ (a ◇ (a ◇ a))))))) ◇ a))))) ((p188 a a)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (y ◇ ((a ◇ (a ◇ (a ◇ (x ◇ (a ◇ (a ◇ _t)))))) ◇ ((a ◇ ((a ◇ (a ◇ (a ◇ a))) ◇ ((a ◇ (a ◇ (a ◇ a))) ◇ (x ◇ (a ◇ (a ◇ (a ◇ a))))))) ◇ a))))) ((p188 a a)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (y ◇ ((a ◇ (a ◇ (_t ◇ (x ◇ (a ◇ (a ◇ (a ◇ a))))))) ◇ ((a ◇ ((a ◇ (a ◇ (a ◇ a))) ◇ ((a ◇ (a ◇ (a ◇ a))) ◇ (x ◇ (a ◇ (a ◇ (a ◇ a))))))) ◇ a))))) ((p188 a a)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (y ◇ ((a ◇ (a ◇ ((a ◇ _t) ◇ (x ◇ (a ◇ (a ◇ (a ◇ a))))))) ◇ ((a ◇ ((a ◇ (a ◇ (a ◇ a))) ◇ ((a ◇ (a ◇ (a ◇ a))) ◇ (x ◇ (a ◇ (a ◇ (a ◇ a))))))) ◇ a))))) ((p188 a a)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (y ◇ ((a ◇ (a ◇ ((a ◇ (a ◇ _t)) ◇ (x ◇ (a ◇ (a ◇ (a ◇ a))))))) ◇ ((a ◇ ((a ◇ (a ◇ (a ◇ a))) ◇ ((a ◇ (a ◇ (a ◇ a))) ◇ (x ◇ (a ◇ (a ◇ (a ◇ a))))))) ◇ a))))) ((p188 a a)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (y ◇ ((a ◇ (_t ◇ ((a ◇ (a ◇ (a ◇ a))) ◇ (x ◇ (a ◇ (a ◇ (a ◇ a))))))) ◇ ((a ◇ ((a ◇ (a ◇ (a ◇ a))) ◇ ((a ◇ (a ◇ (a ◇ a))) ◇ (x ◇ (a ◇ (a ◇ (a ◇ a))))))) ◇ a))))) ((p188 a a)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (y ◇ ((a ◇ ((a ◇ _t) ◇ ((a ◇ (a ◇ (a ◇ a))) ◇ (x ◇ (a ◇ (a ◇ (a ◇ a))))))) ◇ ((a ◇ ((a ◇ (a ◇ (a ◇ a))) ◇ ((a ◇ (a ◇ (a ◇ a))) ◇ (x ◇ (a ◇ (a ◇ (a ◇ a))))))) ◇ a))))) ((p188 a a)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (y ◇ ((a ◇ ((a ◇ (a ◇ _t)) ◇ ((a ◇ (a ◇ (a ◇ a))) ◇ (x ◇ (a ◇ (a ◇ (a ◇ a))))))) ◇ ((a ◇ ((a ◇ (a ◇ (a ◇ a))) ◇ ((a ◇ (a ◇ (a ◇ a))) ◇ (x ◇ (a ◇ (a ◇ (a ◇ a))))))) ◇ a))))) ((p188 a a)))).symm).trans ((p69 a a a x y a)))))))))))))))))))))))))))))))
  exact (p189 a a).trans (p189 b a).symm

#print axioms finite_trivial

import Mathlib.Data.Fintype.Card
import JudgeMagma.Magma

@[reducible] def Equation2 (G : Type _) [Magma G] : Prop := ∀ (x y : G), x = y
@[reducible] def Equation5837 (G : Type _) [Magma G] : Prop := ∀ (x y z : G), x = y ◇ (x ◇ (y ◇ ((z ◇ y) ◇ y)))

theorem finite_trivial (G : Type*) [Magma G] [Finite G] (h : Equation5837 G) : Equation2 G := by
  intro a b
  have ls (y : G) : Function.Surjective (fun t : G => y ◇ t) := by
    intro x
    exact ⟨(x ◇ (y ◇ ((a ◇ y) ◇ y))), (h x y a).symm⟩
  have li (y : G) : Function.Injective (fun t : G => y ◇ t) :=
    Finite.injective_iff_surjective.mpr (ls y)
  let d (x y : G) : G := Classical.choose (ls x y)
  have ld1 (x y : G) : x ◇ d x y = y := Classical.choose_spec (ls x y)
  have ld2 (x y : G) : d x (x ◇ y) = y := li x (ld1 x (x ◇ y))
  have p2 (x y z : G) : (x ◇ (y ◇ (x ◇ ((z ◇ x) ◇ x)))) = y := by
    exact (h y x z).symm
  have p3 (x y : G) : (x ◇ (d x y)) = y := by
    exact (ld1 x y)
  have p4 (x y : G) : (d x (x ◇ y)) = y := by
    exact (ld2 x y)
  have p6 (u x y z : G) : ((x ◇ (y ◇ ((z ◇ y) ◇ y))) ◇ (u ◇ ((x ◇ (y ◇ ((z ◇ y) ◇ y))) ◇ (x ◇ (x ◇ (y ◇ ((z ◇ y) ◇ y))))))) = u := by
    exact (((congrArg (fun _t : G => ((x ◇ (y ◇ ((z ◇ y) ◇ y))) ◇ (u ◇ ((x ◇ (y ◇ ((z ◇ y) ◇ y))) ◇ (_t ◇ (x ◇ (y ◇ ((z ◇ y) ◇ y)))))))) ((p2 y x z)))).symm).trans ((p2 (x ◇ (y ◇ ((z ◇ y) ◇ y))) u y))
  have p8 (x y z : G) : (d x y) = (y ◇ (x ◇ ((z ◇ x) ◇ x))) := by
    exact (((congrArg (fun _t : G => (d x _t)) ((p2 x y z)))).symm).trans ((p4 x (y ◇ (x ◇ ((z ◇ x) ◇ x)))))
  have p10 (x y z : G) : ((x ◇ (x ◇ ((y ◇ x) ◇ x))) ◇ (z ◇ ((x ◇ (x ◇ ((y ◇ x) ◇ x))) ◇ x))) = z := by
    exact (((congrArg (fun _t : G => ((x ◇ (x ◇ ((y ◇ x) ◇ x))) ◇ (z ◇ ((x ◇ (x ◇ ((y ◇ x) ◇ x))) ◇ _t)))) ((p2 x x y)))).symm).trans ((p6 z x x y))
  have p15 (x y z : G) : (d (d x y) z) = (z ◇ ((d x y) ◇ (y ◇ (d x y)))) := by
    exact ((p8 (d x y) z x)).trans ((congrArg (fun _t : G => (z ◇ ((d x y) ◇ (_t ◇ (d x y))))) ((p3 x y))))
  have p16 (x y z : G) : ((x ◇ y) ◇ (x ◇ ((z ◇ x) ◇ x))) = y := by
    exact (((p8 x (x ◇ y) z)).symm).trans ((p4 x y))
  have p17 (x y z : G) : (d x (d y x)) = (y ◇ ((z ◇ y) ◇ y)) := by
    exact (((congrArg (fun _t : G => (d x _t)) (((p8 y x z)).symm))).symm).trans ((p4 x (y ◇ ((z ◇ y) ◇ y))))
  have p51 (x y z : G) : (x ◇ (y ◇ (d z (d x z)))) = y := by
    exact (((congrArg (fun _t : G => (x ◇ (y ◇ _t))) (((p17 z x a)).symm))).symm).trans ((p2 x y a))
  have p60 (x y z : G) : (d x y) = (y ◇ (d z (d x z))) := by
    exact ((p8 x y a)).trans ((congrArg (fun _t : G => (y ◇ _t)) (((p17 z x a)).symm)))
  have p66 (x y z : G) : ((x ◇ y) ◇ (d z (d x z))) = y := by
    exact (((congrArg (fun _t : G => ((x ◇ y) ◇ _t)) (((p17 z x a)).symm))).symm).trans ((p16 x y a))
  have p70 (x y z : G) : (d x (d y x)) = (d z (d y z)) := by
    exact ((p17 x y a)).trans (((p17 z y a)).symm)
  have p72 (x y z : G) : (x ◇ (y ◇ (d (x ◇ z) z))) = y := by
    exact (((congrArg (fun _t : G => (x ◇ (y ◇ (d (x ◇ z) _t)))) ((p4 x z)))).symm).trans ((p51 x y (x ◇ z)))
  have p92 (x y z : G) : (d x y) = (y ◇ (d (x ◇ z) z)) := by
    exact ((p60 x y (x ◇ z))).trans ((congrArg (fun _t : G => (y ◇ (d (x ◇ z) _t))) ((p4 x z))))
  have p117 (x y z : G) : (d (x ◇ y) y) = (d z (d x z)) := by
    exact (((congrArg (fun _t : G => (d (x ◇ y) _t)) ((p66 x y z)))).symm).trans ((p4 (x ◇ y) (d z (d x z))))
  have p118 (x y z : G) : ((x ◇ y) ◇ (d (x ◇ z) z)) = y := by
    exact (((congrArg (fun _t : G => ((x ◇ y) ◇ (d (x ◇ z) _t))) ((p4 x z)))).symm).trans ((p66 x y (x ◇ z)))
  have p122 (x y z : G) : (x ◇ ((d y (d z y)) ◇ ((d z y) ◇ (d y (d z y))))) = (x ◇ ((d y (d z y)) ◇ (d y (d z y)))) := by
    exact (((p15 y (d z y) x)).symm).trans (((p8 (d y (d z y)) x z)).trans ((congrArg (fun _t : G => (x ◇ ((d y (d z y)) ◇ _t))) ((p66 z (d y (d z y)) y)))))
  have p126 (x y z : G) : (((d x (d y x)) ◇ z) ◇ ((d x (d y x)) ◇ (d x (d y x)))) = z := by
    exact (((congrArg (fun _t : G => (((d x (d y x)) ◇ z) ◇ ((d x (d y x)) ◇ _t))) ((p66 y (d x (d y x)) x)))).symm).trans ((p16 (d x (d y x)) z y))
  have p128 (x y z : G) : ((d x (d y x)) ◇ (z ◇ (d x (d y x)))) = ((d x (d y x)) ◇ (d x (d y x))) := by
    exact ((((p4 a ((d x (d y x)) ◇ (d x (d y x))))).symm).trans ((((congrArg (fun _t : G => (d a _t)) ((p122 a x y)))).symm).trans ((((congrArg (fun _t : G => (d a _t)) ((p15 x (d y x) a)))).symm).trans (((p17 a (d x (d y x)) (y ◇ z))).trans ((congrArg (fun _t : G => ((d x (d y x)) ◇ (_t ◇ (d x (d y x))))) ((p66 y z x)))))))).symm
  have p138 (u x y z : G) : (x ◇ (y ◇ ((d z (d u z)) ◇ ((d u x) ◇ (x ◇ (d u x)))))) = y := by
    exact (((congrArg (fun _t : G => (x ◇ (y ◇ _t))) ((p15 u x (d z (d u z)))))).symm).trans ((((congrArg (fun _t : G => (x ◇ (y ◇ (d (d u x) _t)))) ((p70 x u z)))).symm).trans ((p51 x y (d u x))))
  have p142 (u x y z : G) : (d x y) = (y ◇ ((d z (d u z)) ◇ ((d u x) ◇ (x ◇ (d u x))))) := by
    exact (((p60 x y (d u x))).trans ((congrArg (fun _t : G => (y ◇ (d (d u x) _t))) ((p70 x u z))))).trans ((congrArg (fun _t : G => (y ◇ _t)) ((p15 u x (d z (d u z))))))
  have p153 (u x y z : G) : (x ◇ (y ◇ (z ◇ (d u (d (x ◇ z) u))))) = y := by
    exact (((congrArg (fun _t : G => (x ◇ (y ◇ _t))) ((p60 (x ◇ z) z u)))).symm).trans ((p72 x y z))
  have p195 (u x y z : G) : (d x y) = (y ◇ (z ◇ (d u (d (x ◇ z) u)))) := by
    exact ((p92 x y z)).trans ((congrArg (fun _t : G => (y ◇ _t)) ((p60 (x ◇ z) z u))))
  have p198 (u x y z : G) : (d (x ◇ y) z) = (z ◇ (d y (d u (d x u)))) := by
    exact ((p92 (x ◇ y) z (d u (d x u)))).trans ((congrArg (fun _t : G => (z ◇ (d _t (d u (d x u))))) ((p66 x y u))))
  have p232 (x y z : G) : (x ◇ ((d (y ◇ z) z) ◇ (z ◇ (d (y ◇ z) z)))) = (x ◇ ((d (y ◇ z) z) ◇ (d (y ◇ z) z))) := by
    exact (((p15 (y ◇ z) z x)).symm).trans (((p8 (d (y ◇ z) z) x y)).trans ((congrArg (fun _t : G => (x ◇ ((d (y ◇ z) z) ◇ _t))) ((p118 y (d (y ◇ z) z) z)))))
  have p236 (x y z : G) : (((d (x ◇ y) y) ◇ z) ◇ ((d (x ◇ y) y) ◇ (d (x ◇ y) y))) = z := by
    exact (((congrArg (fun _t : G => (((d (x ◇ y) y) ◇ z) ◇ ((d (x ◇ y) y) ◇ _t))) ((p118 x (d (x ◇ y) y) y)))).symm).trans ((p16 (d (x ◇ y) y) z x))
  have p239 (x y z : G) : ((d (x ◇ y) y) ◇ (z ◇ (d (x ◇ y) y))) = ((d (x ◇ y) y) ◇ (d (x ◇ y) y)) := by
    exact ((((p4 a ((d (x ◇ y) y) ◇ (d (x ◇ y) y)))).symm).trans ((((congrArg (fun _t : G => (d a _t)) ((p232 a x y)))).symm).trans ((((congrArg (fun _t : G => (d a _t)) ((p15 (x ◇ y) y a)))).symm).trans (((p17 a (d (x ◇ y) y) (x ◇ z))).trans ((congrArg (fun _t : G => ((d (x ◇ y) y) ◇ (_t ◇ (d (x ◇ y) y)))) ((p118 x z y)))))))).symm
  have p250 (u x y z : G) : (d x (d (y ◇ z) z)) = (d u (d (y ◇ x) u)) := by
    exact (((congrArg (fun _t : G => (d _t (d (y ◇ z) z))) ((p118 y x z)))).symm).trans ((p117 (y ◇ x) (d (y ◇ z) z) u))
  have p278 (x y : G) : (d x (d y x)) = y := by
    exact (((p126 x y (d x (d y x)))).symm).trans ((((congrArg (fun _t : G => (((d x (d y x)) ◇ (d x (d y x))) ◇ _t)) ((p128 x y (d x (d y x)))))).symm).trans ((((congrArg (fun _t : G => (((d x (d y x)) ◇ (d x (d y x))) ◇ ((d x (d y x)) ◇ _t))) ((p128 x y (a ◇ (d x (d y x))))))).symm).trans ((((congrArg (fun _t : G => (_t ◇ ((d x (d y x)) ◇ ((d x (d y x)) ◇ ((a ◇ (d x (d y x))) ◇ (d x (d y x))))))) ((p128 x y (d x (d y x)))))).symm).trans ((((congrArg (fun _t : G => (((d x (d y x)) ◇ _t) ◇ ((d x (d y x)) ◇ ((d x (d y x)) ◇ ((a ◇ (d x (d y x))) ◇ (d x (d y x))))))) ((p128 x y (a ◇ (d x (d y x))))))).symm).trans ((((congrArg (fun _t : G => (((d x (d y x)) ◇ ((d x (d y x)) ◇ ((a ◇ (d x (d y x))) ◇ (d x (d y x))))) ◇ _t)) ((p51 y ((d x (d y x)) ◇ ((d x (d y x)) ◇ ((a ◇ (d x (d y x))) ◇ (d x (d y x))))) x)))).symm).trans ((p10 (d x (d y x)) a y)))))))
  have p289 (x y : G) : (d (x ◇ y) y) = x := by
    exact (((p236 x y (d (x ◇ y) y))).symm).trans ((((congrArg (fun _t : G => (((d (x ◇ y) y) ◇ (d (x ◇ y) y)) ◇ _t)) ((p239 x y (d (x ◇ y) y))))).symm).trans ((((congrArg (fun _t : G => (((d (x ◇ y) y) ◇ (d (x ◇ y) y)) ◇ ((d (x ◇ y) y) ◇ _t))) ((p239 x y (a ◇ (d (x ◇ y) y)))))).symm).trans ((((congrArg (fun _t : G => (_t ◇ ((d (x ◇ y) y) ◇ ((d (x ◇ y) y) ◇ ((a ◇ (d (x ◇ y) y)) ◇ (d (x ◇ y) y)))))) ((p239 x y (d (x ◇ y) y))))).symm).trans ((((congrArg (fun _t : G => (((d (x ◇ y) y) ◇ _t) ◇ ((d (x ◇ y) y) ◇ ((d (x ◇ y) y) ◇ ((a ◇ (d (x ◇ y) y)) ◇ (d (x ◇ y) y)))))) ((p239 x y (a ◇ (d (x ◇ y) y)))))).symm).trans ((((congrArg (fun _t : G => (((d (x ◇ y) y) ◇ ((d (x ◇ y) y) ◇ ((a ◇ (d (x ◇ y) y)) ◇ (d (x ◇ y) y)))) ◇ _t)) ((p72 x ((d (x ◇ y) y) ◇ ((d (x ◇ y) y) ◇ ((a ◇ (d (x ◇ y) y)) ◇ (d (x ◇ y) y)))) y)))).symm).trans ((p10 (d (x ◇ y) y) a x)))))))
  have p303 (x y : G) : (d x y) = (y ◇ x) := by
    exact ((((congrArg (fun _t : G => (d x _t)) ((p289 y a)))).symm).trans ((p250 a x y a))).trans ((p278 a (y ◇ x)))
  have p323 (u x y z : G) : (x ◇ (((y ◇ z) ◇ y) ◇ u)) = (x ◇ (z ◇ u)) := by
    exact (((((((p303 (z ◇ u) x)).symm).trans ((p198 y z u x))).trans ((congrArg (fun _t : G => (x ◇ (d u (d y _t)))) ((p303 z y))))).trans ((congrArg (fun _t : G => (x ◇ (d u _t))) ((p303 y (y ◇ z)))))).trans ((congrArg (fun _t : G => (x ◇ _t)) ((p303 u ((y ◇ z) ◇ y)))))).symm
  have p325 (u x y z : G) : (x ◇ (y ◇ ((z ◇ (u ◇ y)) ◇ z))) = (x ◇ u) := by
    exact ((((((p303 u x)).symm).trans ((p195 z u x y))).trans ((congrArg (fun _t : G => (x ◇ (y ◇ (d z _t)))) ((p303 (u ◇ y) z))))).trans ((congrArg (fun _t : G => (x ◇ (y ◇ _t))) ((p303 z (z ◇ (u ◇ y))))))).symm
  have p335 (x y : G) : (x ◇ (y ◇ x)) = y := by
    exact (((congrArg (fun _t : G => (x ◇ _t)) ((p325 x y a a)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (y ◇ (a ◇ _t)))) ((p303 a (a ◇ (x ◇ a)))))).symm).trans ((((congrArg (fun _t : G => (x ◇ (y ◇ (a ◇ (d a _t))))) ((p303 (x ◇ a) a)))).symm).trans ((p153 a x y a))))
  have p338 (x y z : G) : (x ◇ (y ◇ z)) = (x ◇ z) := by
    exact ((((((((((p303 z x)).symm).trans ((p142 y z x a))).trans ((congrArg (fun _t : G => (x ◇ ((d a _t) ◇ ((d y z) ◇ (z ◇ (d y z)))))) ((p303 y a))))).trans ((congrArg (fun _t : G => (x ◇ (_t ◇ ((d y z) ◇ (z ◇ (d y z)))))) ((p303 a (a ◇ y)))))).trans ((congrArg (fun _t : G => (x ◇ (((a ◇ y) ◇ a) ◇ (_t ◇ (z ◇ (d y z)))))) ((p303 y z))))).trans ((congrArg (fun _t : G => (x ◇ (((a ◇ y) ◇ a) ◇ ((z ◇ y) ◇ (z ◇ _t))))) ((p303 y z))))).trans ((congrArg (fun _t : G => (x ◇ (((a ◇ y) ◇ a) ◇ _t))) ((p335 (z ◇ y) z))))).trans ((p323 z x a y))).symm
  have p340 (x y z : G) : (x ◇ y) = z := by
    exact (((p338 x z y)).symm).trans ((((congrArg (fun _t : G => (x ◇ _t)) ((p338 z ((a ◇ y) ◇ a) y)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (z ◇ _t))) ((p338 ((a ◇ y) ◇ a) (x ◇ y) y)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (z ◇ (((a ◇ y) ◇ a) ◇ _t)))) ((p338 (x ◇ y) x y)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (z ◇ (((a ◇ y) ◇ a) ◇ ((x ◇ y) ◇ _t))))) ((p338 x x y)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (z ◇ (((a ◇ y) ◇ a) ◇ ((x ◇ y) ◇ (x ◇ _t)))))) ((p303 y x)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (z ◇ (((a ◇ y) ◇ a) ◇ (_t ◇ (x ◇ (d y x))))))) ((p303 y x)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (z ◇ (_t ◇ ((d y x) ◇ (x ◇ (d y x))))))) ((p303 a (a ◇ y))))).symm).trans ((((congrArg (fun _t : G => (x ◇ (z ◇ ((d a _t) ◇ ((d y x) ◇ (x ◇ (d y x))))))) ((p303 y a)))).symm).trans ((p138 y x z a))))))))))
  exact (p340 a a a).symm.trans (p340 a a b)

@[reducible] def Equation40221 (G : Type _) [Magma G] : Prop := ∀ (x y z : G), x = (((y ◇ (y ◇ z)) ◇ y) ◇ x) ◇ y

theorem finite_trivial_dual (G : Type*) [Magma G] [Finite G] (h : Equation40221 G) : Equation2 G := by
  let opposite : Magma G := ⟨fun x y => y ◇ x⟩
  have hd : @ Equation5837 G opposite := by
    intro x y z
    exact h x y z
  exact @ finite_trivial G opposite inferInstance hd

#print axioms finite_trivial_dual

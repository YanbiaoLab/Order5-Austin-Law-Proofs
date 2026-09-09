import Mathlib.Data.Fintype.Card
import JudgeMagma.Magma

@[reducible] def Equation2 (G : Type _) [Magma G] : Prop := ∀ (x y : G), x = y
@[reducible] def Equation4957 (G : Type _) [Magma G] : Prop := ∀ (x y z : G), x = y ◇ (x ◇ (y ◇ (z ◇ (x ◇ z))))

theorem finite_trivial (G : Type*) [Magma G] [Finite G] (h : Equation4957 G) : Equation2 G := by
  intro a b
  have ls (y : G) : Function.Surjective (fun t : G => y ◇ t) := by
    intro x
    exact ⟨(x ◇ (y ◇ (a ◇ (x ◇ a)))), (h x y a).symm⟩
  have li (y : G) : Function.Injective (fun t : G => y ◇ t) :=
    Finite.injective_iff_surjective.mpr (ls y)
  let d (x y : G) : G := Classical.choose (ls x y)
  have ld1 (x y : G) : x ◇ d x y = y := Classical.choose_spec (ls x y)
  have ld2 (x y : G) : d x (x ◇ y) = y := li x (ld1 x (x ◇ y))
  have p2 (x y z : G) : (x ◇ (y ◇ (x ◇ (z ◇ (y ◇ z))))) = y := by
    exact (h y x z).symm
  have p3 (x y : G) : (x ◇ (d x y)) = y := by
    exact (ld1 x y)
  have p4 (x y : G) : (d x (x ◇ y)) = y := by
    exact (ld2 x y)
  have p7 (x y z : G) : (x ◇ (y ◇ (x ◇ ((d y z) ◇ z)))) = y := by
    exact (((congrArg (fun _t : G => (x ◇ (y ◇ (x ◇ ((d y z) ◇ _t))))) ((p3 y z)))).symm).trans ((p2 x y (d y z)))
  have p8 (x y z : G) : (d x y) = (y ◇ (x ◇ (z ◇ (y ◇ z)))) := by
    exact (((congrArg (fun _t : G => (d x _t)) ((p2 x y z)))).symm).trans ((p4 x (y ◇ (x ◇ (z ◇ (y ◇ z))))))
  have p13 (x y z : G) : (d x y) = (y ◇ (x ◇ ((d y z) ◇ z))) := by
    exact (((congrArg (fun _t : G => (d x _t)) ((p7 x y z)))).symm).trans ((p4 x (y ◇ (x ◇ ((d y z) ◇ z)))))
  have p18 (x y z : G) : (d x (d y x)) = (y ◇ (z ◇ (x ◇ z))) := by
    exact (((congrArg (fun _t : G => (d x _t)) (((p8 y x z)).symm))).symm).trans ((p4 x (y ◇ (z ◇ (x ◇ z)))))
  have p27 (x y : G) : (x ◇ (d (y ◇ x) y)) = (d y x) := by
    exact (((p8 y x (y ◇ x))).trans ((congrArg (fun _t : G => (x ◇ _t)) (((p8 (y ◇ x) y x)).symm)))).symm
  have p31 (x y : G) : (d (x ◇ y) x) = (d y (d x y)) := by
    exact ((((congrArg (fun _t : G => (d y _t)) ((p27 y x)))).symm).trans ((p4 y (d (x ◇ y) x)))).symm
  have p38 (x y : G) : ((x ◇ y) ◇ (d y (d x y))) = x := by
    exact (((congrArg (fun _t : G => ((x ◇ y) ◇ _t)) ((p31 x y)))).symm).trans ((p3 (x ◇ y) x))
  have p56 (x y z : G) : ((x ◇ y) ◇ (x ◇ (z ◇ (y ◇ z)))) = x := by
    exact (((congrArg (fun _t : G => ((x ◇ y) ◇ _t)) ((p4 y (x ◇ (z ◇ (y ◇ z))))))).symm).trans ((((congrArg (fun _t : G => ((x ◇ y) ◇ (d y _t))) ((p8 x y z)))).symm).trans ((p38 x y)))
  have p63 (x y : G) : (x ◇ ((d x y) ◇ (d y x))) = (d x y) := by
    exact (((congrArg (fun _t : G => (x ◇ ((d x y) ◇ _t))) (((p13 y x y)).symm))).symm).trans ((p2 x (d x y) y))
  have p65 (x y z : G) : (d x (d y x)) = (y ◇ ((d x z) ◇ z)) := by
    exact (((congrArg (fun _t : G => (d x _t)) (((p13 y x z)).symm))).symm).trans ((p4 x (y ◇ ((d x z) ◇ z))))
  have p80 (x y z : G) : ((x ◇ y) ◇ (x ◇ ((d y z) ◇ z))) = x := by
    exact (((congrArg (fun _t : G => ((x ◇ y) ◇ _t)) ((p4 y (x ◇ ((d y z) ◇ z)))))).symm).trans ((((congrArg (fun _t : G => ((x ◇ y) ◇ (d y _t))) ((p13 x y z)))).symm).trans ((p38 x y)))
  have p87 (x y z : G) : (d x (d y (d x y))) = (z ◇ (y ◇ z)) := by
    exact (((congrArg (fun _t : G => (d x _t)) (((p18 y x z)).symm))).symm).trans ((p4 x (z ◇ (y ◇ z))))
  have p433 (x y z : G) : (x ◇ (y ◇ x)) = (z ◇ (y ◇ z)) := by
    exact (((p4 a (x ◇ (y ◇ x)))).symm).trans ((((congrArg (fun _t : G => (d a _t)) ((p4 y (a ◇ (x ◇ (y ◇ x))))))).symm).trans ((((congrArg (fun _t : G => (d a (d y _t))) ((p8 a y x)))).symm).trans ((p87 a y z))))
  have p517 (x y : G) : (x ◇ ((d y y) ◇ x)) = (d y y) := by
    exact (((p433 ((d y y) ◇ y) (d y y) x)).symm).trans ((p80 (d y y) y y))
  have p749 (x : G) : (x ◇ x) = x := by
    exact (((congrArg (fun _t : G => (x ◇ _t)) ((p3 x x)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (x ◇ _t))) ((p517 x x)))).symm).trans ((p7 x x x)))
  have p757 (x : G) : (d x x) = x := by
    exact (((p13 x x x)).trans ((congrArg (fun _t : G => (x ◇ _t)) ((p517 x x))))).trans ((p3 x x))
  have p768 (x y : G) : (x ◇ y) = x := by
    exact (((p749 (x ◇ y))).symm).trans ((((congrArg (fun _t : G => ((x ◇ y) ◇ (x ◇ _t))) ((p757 y)))).symm).trans ((((congrArg (fun _t : G => ((x ◇ _t) ◇ (x ◇ (d y y)))) ((p757 y)))).symm).trans ((((congrArg (fun _t : G => ((x ◇ (d y y)) ◇ (x ◇ _t))) ((p517 a y)))).symm).trans ((p56 x (d y y) a)))))
  have p769 (x y : G) : (d x y) = x := by
    exact ((((p749 (d x y))).symm).trans ((((congrArg (fun _t : G => ((d x y) ◇ (d _t y))) ((p757 x)))).symm).trans ((((congrArg (fun _t : G => (_t ◇ (d (d x x) y))) ((p768 (d x y) (d y x))))).symm).trans ((((congrArg (fun _t : G => (((d x y) ◇ (d y _t)) ◇ (d (d x x) y))) ((p757 x)))).symm).trans ((((congrArg (fun _t : G => (((d _t y) ◇ (d y (d x x))) ◇ (d (d x x) y))) ((p757 x)))).symm).trans ((((congrArg (fun _t : G => (((d (d x x) y) ◇ (d y (d x x))) ◇ _t)) ((p63 (d x x) y)))).symm).trans ((p517 ((d (d x x) y) ◇ (d y (d x x))) x)))))))).trans ((p757 x))
  have p770 (x y : G) : x = y := by
    exact ((((p749 x)).symm).trans ((((congrArg (fun _t : G => (x ◇ _t)) ((p769 x y)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (d x _t))) ((p769 y x)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (d x (d _t x)))) ((p757 y)))).symm).trans ((((congrArg (fun _t : G => (_t ◇ (d x (d (d y y) x)))) ((p768 x a)))).symm).trans ((((congrArg (fun _t : G => ((_t ◇ a) ◇ (d x (d (d y y) x)))) ((p769 x a)))).symm).trans ((((congrArg (fun _t : G => (((d x a) ◇ a) ◇ _t)) (((p65 x (d y y) a)).symm))).symm).trans ((p517 ((d x a) ◇ a) y))))))))).trans ((p757 y))
  exact (p770 a a).trans (p770 b a).symm

@[reducible] def Equation40914 (G : Type _) [Magma G] : Prop := ∀ (x y z : G), x = ((((y ◇ x) ◇ y) ◇ z) ◇ x) ◇ z

theorem finite_trivial_dual (G : Type*) [Magma G] [Finite G] (h : Equation40914 G) : Equation2 G := by
  let opposite : Magma G := ⟨fun x y => y ◇ x⟩
  have hd : @ Equation4957 G opposite := by
    intro x y z
    exact h x z y
  exact @ finite_trivial G opposite inferInstance hd

#print axioms finite_trivial_dual

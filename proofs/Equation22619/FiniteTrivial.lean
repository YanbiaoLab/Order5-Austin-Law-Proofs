import Mathlib.Data.Fintype.Card
import JudgeMagma.Magma

@[reducible] def Equation2 (G : Type _) [Magma G] : Prop := ∀ (x y : G), x = y
@[reducible] def Equation22619 (G : Type _) [Magma G] : Prop := ∀ (x y z : G), x = (y ◇ (y ◇ x)) ◇ ((z ◇ z) ◇ z)

theorem finite_trivial (G : Type*) [Magma G] [Finite G] (h : Equation22619 G) : Equation2 G := by
  intro a b
  have li (y : G) : Function.Injective (fun t : G => y ◇ t) := by
    intro u v huv
    change y ◇ u = y ◇ v at huv
    calc u = (y ◇ (y ◇ u)) ◇ ((a ◇ a) ◇ a) := h u y a
         _ = (y ◇ (y ◇ v)) ◇ ((a ◇ a) ◇ a) := by rw [huv]
         _ = v := (h v y a).symm
  have ls (y : G) : Function.Surjective (fun t : G => y ◇ t) :=
    Finite.injective_iff_surjective.mp (li y)
  let d (x y : G) : G := Classical.choose (ls x y)
  have ld1 (x y : G) : x ◇ d x y = y := Classical.choose_spec (ls x y)
  have ld2 (x y : G) : d x (x ◇ y) = y := li x (ld1 x (x ◇ y))
  have p2 (x y z : G) : ((x ◇ (x ◇ y)) ◇ ((z ◇ z) ◇ z)) = y := by
    exact (h y x z).symm
  have p3 (x y : G) : (x ◇ (d x y)) = y := by
    exact (ld1 x y)
  have p4 (x y : G) : (d x (x ◇ y)) = y := by
    exact (ld2 x y)
  have p6 (u x y z : G) : (((x ◇ (x ◇ y)) ◇ y) ◇ ((z ◇ z) ◇ z)) = ((u ◇ u) ◇ u) := by
    exact (((congrArg (fun _t : G => (((x ◇ (x ◇ y)) ◇ _t) ◇ ((z ◇ z) ◇ z))) ((p2 x y u)))).symm).trans ((p2 (x ◇ (x ◇ y)) ((u ◇ u) ◇ u) z))
  have p7 (x y z : G) : (d x y) = ((x ◇ y) ◇ ((z ◇ z) ◇ z)) := by
    exact ((((congrArg (fun _t : G => ((x ◇ _t) ◇ ((z ◇ z) ◇ z))) ((p3 x y)))).symm).trans ((p2 x (d x y) z))).symm
  have p9 (u w x y z : G) : ((((x ◇ (x ◇ y)) ◇ y) ◇ ((z ◇ z) ◇ z)) ◇ ((u ◇ u) ◇ u)) = ((w ◇ w) ◇ w) := by
    exact (((congrArg (fun _t : G => ((((x ◇ (x ◇ y)) ◇ y) ◇ _t) ◇ ((u ◇ u) ◇ u))) ((p6 z x y w)))).symm).trans ((p2 ((x ◇ (x ◇ y)) ◇ y) ((w ◇ w) ◇ w) u))
  have p17 (x y : G) : ((x ◇ x) ◇ x) = ((y ◇ y) ◇ y) := by
    exact (((p6 x a a a)).symm).trans ((p6 y a a a))
  have p22 (x y : G) : (d (x ◇ x) ((y ◇ y) ◇ y)) = x := by
    exact (((congrArg (fun _t : G => (d (x ◇ x) _t)) ((p17 x y)))).symm).trans ((p4 (x ◇ x) x))
  have p24 (x y : G) : ((d x x) ◇ ((y ◇ y) ◇ y)) = x := by
    exact (((congrArg (fun _t : G => (_t ◇ ((y ◇ y) ◇ y))) (((p7 x x x)).symm))).symm).trans ((p2 (x ◇ x) x y))
  have p28 (x y z : G) : (x ◇ ((x ◇ y) ◇ ((z ◇ z) ◇ z))) = y := by
    exact (((congrArg (fun _t : G => (x ◇ _t)) ((p7 x y z)))).symm).trans ((p3 x y))
  have p42 (x y z : G) : (d (x ◇ x) x) = (((y ◇ y) ◇ y) ◇ ((z ◇ z) ◇ z)) := by
    exact ((p7 (x ◇ x) x z)).trans ((congrArg (fun _t : G => (_t ◇ ((z ◇ z) ◇ z))) ((p17 x y))))
  have p43 (x y : G) : (d (d (x ◇ x) x) ((y ◇ y) ◇ y)) = ((x ◇ x) ◇ x) := by
    exact (((congrArg (fun _t : G => (d _t ((y ◇ y) ◇ y))) (((p7 (x ◇ x) x x)).symm))).symm).trans ((p22 ((x ◇ x) ◇ x) y))
  have p44 (x y : G) : (d (x ◇ x) ((d (y ◇ y) y) ◇ ((y ◇ y) ◇ y))) = x := by
    exact (((congrArg (fun _t : G => (d (x ◇ x) (_t ◇ ((y ◇ y) ◇ y)))) (((p7 (y ◇ y) y y)).symm))).symm).trans ((p22 x ((y ◇ y) ◇ y)))
  have p48 (x y z : G) : (d x y) = ((x ◇ y) ◇ ((d (z ◇ z) z) ◇ ((z ◇ z) ◇ z))) := by
    exact ((p7 x y ((z ◇ z) ◇ z))).trans ((congrArg (fun _t : G => ((x ◇ y) ◇ (_t ◇ ((z ◇ z) ◇ z)))) (((p7 (z ◇ z) z z)).symm)))
  have p54 (x y : G) : ((d x x) ◇ ((d (y ◇ y) y) ◇ ((y ◇ y) ◇ y))) = x := by
    exact (((congrArg (fun _t : G => ((d x x) ◇ (_t ◇ ((y ◇ y) ◇ y)))) (((p7 (y ◇ y) y y)).symm))).symm).trans ((p24 x ((y ◇ y) ◇ y)))
  have p99 (u v5 w x y z : G) : (((x ◇ x) ◇ ((((y ◇ (y ◇ z)) ◇ z) ◇ ((u ◇ u) ◇ u)) ◇ ((w ◇ w) ◇ w))) ◇ ((v5 ◇ v5) ◇ v5)) = x := by
    exact (((congrArg (fun _t : G => (((x ◇ x) ◇ _t) ◇ ((v5 ◇ v5) ◇ v5))) (((p9 w x y z u)).symm))).symm).trans ((p2 (x ◇ x) x v5))
  have p143 (u w x y z : G) : ((x ◇ x) ◇ ((((y ◇ (y ◇ z)) ◇ z) ◇ ((u ◇ u) ◇ u)) ◇ ((w ◇ w) ◇ w))) = x := by
    exact (((congrArg (fun _t : G => ((x ◇ x) ◇ (_t ◇ ((w ◇ w) ◇ w)))) (((p6 x y z u)).symm))).symm).trans ((p28 (x ◇ x) x w))
  have p148 (x : G) : (d (x ◇ x) x) = ((x ◇ x) ◇ x) := by
    exact ((p7 (x ◇ x) x ((x ◇ x) ◇ x))).trans ((p28 ((x ◇ x) ◇ x) ((x ◇ x) ◇ x) x))
  have p169 (x y : G) : (x ◇ ((y ◇ y) ◇ y)) = x := by
    exact (((congrArg (fun _t : G => (_t ◇ ((y ◇ y) ◇ y))) ((p143 a a x a a)))).symm).trans ((p99 a y a x a a))
  have p172 (x : G) : (d x x) = x := by
    exact (((p169 (d x x) a)).symm).trans ((((congrArg (fun _t : G => ((d x x) ◇ _t)) ((p169 ((a ◇ a) ◇ a) a)))).symm).trans ((((congrArg (fun _t : G => ((d x x) ◇ (_t ◇ ((a ◇ a) ◇ a)))) ((p148 a)))).symm).trans ((p54 x a))))
  have p173 (x y : G) : (d x y) = (x ◇ y) := by
    exact ((((p48 x y a)).trans ((congrArg (fun _t : G => ((x ◇ y) ◇ (_t ◇ ((a ◇ a) ◇ a)))) ((p148 a))))).trans ((congrArg (fun _t : G => ((x ◇ y) ◇ _t)) ((p169 ((a ◇ a) ◇ a) a))))).trans ((p169 (x ◇ y) a))
  have p174 (x : G) : (x ◇ x) = x := by
    exact (((p169 (x ◇ x) a)).symm).trans ((((p173 (x ◇ x) ((a ◇ a) ◇ a))).symm).trans ((((congrArg (fun _t : G => (d (x ◇ x) _t)) ((p169 ((a ◇ a) ◇ a) a)))).symm).trans ((((congrArg (fun _t : G => (d (x ◇ x) (_t ◇ ((a ◇ a) ◇ a)))) ((p173 (a ◇ a) a)))).symm).trans ((p44 x a)))))
  have p175 (x y : G) : (x ◇ y) = x := by
    exact (((((p173 x y)).symm).trans ((((congrArg (fun _t : G => (d x _t)) ((p174 y)))).symm).trans ((((congrArg (fun _t : G => (d x (_t ◇ y))) ((p174 y)))).symm).trans ((((congrArg (fun _t : G => (d _t ((y ◇ y) ◇ y))) ((p172 x)))).symm).trans ((((congrArg (fun _t : G => (d (d _t x) ((y ◇ y) ◇ y))) ((p174 x)))).symm).trans ((p43 x y))))))).trans ((congrArg (fun _t : G => (_t ◇ x)) ((p174 x))))).trans ((p174 x))
  have p176 (x y : G) : x = y := by
    exact ((((((((p172 x)).symm).trans ((((congrArg (fun _t : G => (d _t x)) ((p174 x)))).symm).trans ((p42 x y a)))).trans ((congrArg (fun _t : G => ((_t ◇ y) ◇ ((a ◇ a) ◇ a))) ((p174 y))))).trans ((congrArg (fun _t : G => (_t ◇ ((a ◇ a) ◇ a))) ((p174 y))))).trans ((congrArg (fun _t : G => (y ◇ (_t ◇ a))) ((p174 a))))).trans ((congrArg (fun _t : G => (y ◇ _t)) ((p174 a))))).trans ((p175 y a))
  exact (p176 a a).trans (p176 b a).symm

#print axioms finite_trivial

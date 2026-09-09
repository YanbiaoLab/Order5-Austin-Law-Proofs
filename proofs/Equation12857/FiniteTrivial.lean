import Mathlib.Data.Fintype.Card
import JudgeMagma.Magma

@[reducible] def Equation2 (G : Type _) [Magma G] : Prop := ∀ (x y : G), x = y
@[reducible] def Equation12857 (G : Type _) [Magma G] : Prop := ∀ (x y z : G), x = y ◇ ((x ◇ (y ◇ (z ◇ z))) ◇ y)

theorem finite_trivial (G : Type*) [Magma G] [Finite G] (h : Equation12857 G) : Equation2 G := by
  intro a b
  have ls (y : G) : Function.Surjective (fun t : G => y ◇ t) := by
    intro x
    exact ⟨((x ◇ (y ◇ (a ◇ a))) ◇ y), (h x y a).symm⟩
  have li (y : G) : Function.Injective (fun t : G => y ◇ t) :=
    Finite.injective_iff_surjective.mpr (ls y)
  let d (x y : G) : G := Classical.choose (ls x y)
  have ld1 (x y : G) : x ◇ d x y = y := Classical.choose_spec (ls x y)
  have ld2 (x y : G) : d x (x ◇ y) = y := li x (ld1 x (x ◇ y))
  have rs (t : G) : Function.Surjective (fun w : G => w ◇ t) := by
    have ti : Function.Injective (fun x : G => ((x ◇ (t ◇ (a ◇ a))) ◇ t)) := by
      intro u v huv
      change ((u ◇ (t ◇ (a ◇ a))) ◇ t) = ((v ◇ (t ◇ (a ◇ a))) ◇ t) at huv
      calc u = (t ◇ ((u ◇ (t ◇ (a ◇ a))) ◇ t)) := h u t a
           _ = (t ◇ ((v ◇ (t ◇ (a ◇ a))) ◇ t)) := by rw [huv]
           _ = v := (h v t a).symm
    intro u
    obtain ⟨x, hx⟩ := (Finite.injective_iff_surjective.mp ti) u
    exact ⟨(x ◇ (t ◇ (a ◇ a))), hx⟩
  have ri (y : G) : Function.Injective (fun t : G => t ◇ y) :=
    Finite.injective_iff_surjective.mpr (rs y)
  let r (x y : G) : G := Classical.choose (rs y x)
  have rd1 (x y : G) : r x y ◇ y = x := Classical.choose_spec (rs y x)
  have rd2 (x y : G) : r (x ◇ y) y = x := ri y (rd1 (x ◇ y) y)
  have p2 (x y z : G) : (x ◇ ((y ◇ (x ◇ (z ◇ z))) ◇ x)) = y := by
    exact (h y x z).symm
  have p4 (x y : G) : (d x (x ◇ y)) = y := by
    exact (ld2 x y)
  have p8 (x y z : G) : ((x ◇ ((y ◇ y) ◇ (z ◇ z))) ◇ (x ◇ (x ◇ ((y ◇ y) ◇ (z ◇ z))))) = (y ◇ y) := by
    exact (((congrArg (fun _t : G => ((x ◇ ((y ◇ y) ◇ (z ◇ z))) ◇ (_t ◇ (x ◇ ((y ◇ y) ◇ (z ◇ z)))))) ((p2 (y ◇ y) x z)))).symm).trans ((p2 (x ◇ ((y ◇ y) ◇ (z ◇ z))) (y ◇ y) y))
  have p9 (x y z : G) : (d x y) = ((y ◇ (x ◇ (z ◇ z))) ◇ x) := by
    exact (((congrArg (fun _t : G => (d x _t)) ((p2 x y z)))).symm).trans ((p4 x ((y ◇ (x ◇ (z ◇ z))) ◇ x)))
  have p22 (x y z : G) : (((x ◇ y) ◇ (x ◇ (z ◇ z))) ◇ x) = y := by
    exact (((p9 x (x ◇ y) z)).symm).trans ((p4 x y))
  have p23 (x y z : G) : (d (x ◇ (y ◇ (z ◇ z))) (d y x)) = y := by
    exact (((congrArg (fun _t : G => (d (x ◇ (y ◇ (z ◇ z))) _t)) (((p9 y x z)).symm))).symm).trans ((p4 (x ◇ (y ◇ (z ◇ z))) y))
  have p26 (x y z : G) : (((x ◇ x) ◇ (y ◇ y)) ◇ ((x ◇ x) ◇ (y ◇ y))) = ((z ◇ (y ◇ y)) ◇ (z ◇ (z ◇ (y ◇ y)))) := by
    exact ((((congrArg (fun _t : G => ((z ◇ (y ◇ y)) ◇ (z ◇ (z ◇ _t)))) ((p22 (x ◇ x) (y ◇ y) y)))).symm).trans ((((congrArg (fun _t : G => ((z ◇ _t) ◇ (z ◇ (z ◇ ((((x ◇ x) ◇ (y ◇ y)) ◇ ((x ◇ x) ◇ (y ◇ y))) ◇ (x ◇ x)))))) ((p4 (x ◇ x) (y ◇ y))))).symm).trans ((((congrArg (fun _t : G => ((z ◇ _t) ◇ (z ◇ (z ◇ ((((x ◇ x) ◇ (y ◇ y)) ◇ ((x ◇ x) ◇ (y ◇ y))) ◇ (x ◇ x)))))) (((p9 (x ◇ x) ((x ◇ x) ◇ (y ◇ y)) y)).symm))).symm).trans ((p8 z ((x ◇ x) ◇ (y ◇ y)) x))))).symm
  have p62 (x y : G) : ((x ◇ x) ◇ (y ◇ y)) = (y ◇ y) := by
    exact ((((p4 (x ◇ x) (y ◇ y))).symm).trans ((((congrArg (fun _t : G => (d (x ◇ x) _t)) ((p4 ((x ◇ x) ◇ (y ◇ y)) ((x ◇ x) ◇ (y ◇ y)))))).symm).trans ((((congrArg (fun _t : G => (d _t (d ((x ◇ x) ◇ (y ◇ y)) (((x ◇ x) ◇ (y ◇ y)) ◇ ((x ◇ x) ◇ (y ◇ y)))))) ((p8 ((x ◇ x) ◇ (y ◇ y)) x y)))).symm).trans ((p23 (((x ◇ x) ◇ (y ◇ y)) ◇ ((x ◇ x) ◇ (y ◇ y))) ((x ◇ x) ◇ (y ◇ y)) ((x ◇ x) ◇ (y ◇ y))))))).symm
  have p81 (x y : G) : ((x ◇ (y ◇ y)) ◇ (x ◇ (x ◇ (y ◇ y)))) = (y ◇ y) := by
    exact ((((p62 y y)).symm).trans ((((congrArg (fun _t : G => ((y ◇ y) ◇ _t)) ((p62 a y)))).symm).trans ((((congrArg (fun _t : G => (_t ◇ ((a ◇ a) ◇ (y ◇ y)))) ((p62 a y)))).symm).trans ((p26 a y x))))).symm
  have p84 (x y : G) : (x ◇ x) = (y ◇ y) := by
    exact (((p81 a x)).symm).trans ((((congrArg (fun _t : G => ((a ◇ (x ◇ x)) ◇ (a ◇ (a ◇ _t)))) ((p62 y x)))).symm).trans ((((congrArg (fun _t : G => ((a ◇ _t) ◇ (a ◇ (a ◇ ((y ◇ y) ◇ (x ◇ x)))))) ((p62 y x)))).symm).trans ((p8 a y x))))
  have p87 (x y : G) : (d x (y ◇ y)) = x := by
    exact (((congrArg (fun _t : G => (d x _t)) ((p84 x y)))).symm).trans ((p4 x x))
  have p99 (x y : G) : (x ◇ x) = y := by
    exact (((p87 (x ◇ x) a)).symm).trans ((((congrArg (fun _t : G => (d (x ◇ x) _t)) ((p4 y (a ◇ a))))).symm).trans ((((congrArg (fun _t : G => (d _t (d y (y ◇ (a ◇ a))))) ((p84 (y ◇ (a ◇ a)) x)))).symm).trans ((p23 (y ◇ (a ◇ a)) y a))))
  have p150 (x y : G) : (d x y) = x := by
    exact (((congrArg (fun _t : G => (d x _t)) ((p99 x y)))).symm).trans ((p4 x x))
  have p151 (x y : G) : x = y := by
    exact (((p150 x (a ◇ a))).symm).trans ((((congrArg (fun _t : G => (d x _t)) (((p99 a (x ◇ y))).symm))).symm).trans ((p4 x y)))
  exact (p151 a a).trans (p151 b a).symm

#print axioms finite_trivial

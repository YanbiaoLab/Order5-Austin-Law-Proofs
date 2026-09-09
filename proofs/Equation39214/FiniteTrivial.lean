import Mathlib.Data.Fintype.Card
import JudgeMagma.Magma

@[reducible] def Equation2 (G : Type _) [Magma G] : Prop := ∀ (x y : G), x = y
@[reducible] def Equation6912 (G : Type _) [Magma G] : Prop := ∀ (x y z : G), x = y ◇ (y ◇ ((z ◇ z) ◇ (x ◇ y)))

theorem finite_trivial (G : Type*) [Magma G] [Finite G] (h : Equation6912 G) : Equation2 G := by
  intro a b
  have ls (y : G) : Function.Surjective (fun t : G => y ◇ t) := by
    intro x
    exact ⟨(y ◇ ((a ◇ a) ◇ (x ◇ y))), (h x y a).symm⟩
  have li (y : G) : Function.Injective (fun t : G => y ◇ t) :=
    Finite.injective_iff_surjective.mpr (ls y)
  let d (x y : G) : G := Classical.choose (ls x y)
  have ld1 (x y : G) : x ◇ d x y = y := Classical.choose_spec (ls x y)
  have ld2 (x y : G) : d x (x ◇ y) = y := li x (ld1 x (x ◇ y))
  have rs (t : G) : Function.Surjective (fun w : G => w ◇ t) := by
    have ti : Function.Injective (fun x : G => (x ◇ t)) := by
      intro u v huv
      change (u ◇ t) = (v ◇ t) at huv
      calc u = (t ◇ (t ◇ ((a ◇ a) ◇ (u ◇ t)))) := h u t a
           _ = (t ◇ (t ◇ ((a ◇ a) ◇ (v ◇ t)))) := by rw [huv]
           _ = v := (h v t a).symm
    intro u
    obtain ⟨x, hx⟩ := (Finite.injective_iff_surjective.mp ti) u
    exact ⟨x, hx⟩
  have ri (y : G) : Function.Injective (fun t : G => t ◇ y) :=
    Finite.injective_iff_surjective.mpr (rs y)
  let r (x y : G) : G := Classical.choose (rs y x)
  have rd1 (x y : G) : r x y ◇ y = x := Classical.choose_spec (rs y x)
  have rd2 (x y : G) : r (x ◇ y) y = x := ri y (rd1 (x ◇ y) y)
  have p2 (x y z : G) : (x ◇ (x ◇ ((y ◇ y) ◇ (z ◇ x)))) = z := by
    exact (h z x y).symm
  have p4 (x y : G) : (d x (x ◇ y)) = y := by
    exact (ld2 x y)
  have p5 (x y : G) : ((r x y) ◇ y) = x := by
    exact (rd1 x y)
  have p8 (u x y z : G) : ((x ◇ ((y ◇ y) ◇ (z ◇ x))) ◇ ((x ◇ ((y ◇ y) ◇ (z ◇ x))) ◇ ((u ◇ u) ◇ z))) = x := by
    exact (((congrArg (fun _t : G => ((x ◇ ((y ◇ y) ◇ (z ◇ x))) ◇ ((x ◇ ((y ◇ y) ◇ (z ◇ x))) ◇ ((u ◇ u) ◇ _t)))) ((p2 x y z)))).symm).trans ((p2 (x ◇ ((y ◇ y) ◇ (z ◇ x))) u x))
  have p9 (x y z : G) : (((x ◇ x) ◇ (y ◇ (z ◇ z))) ◇ (((x ◇ x) ◇ (y ◇ (z ◇ z))) ◇ y)) = (z ◇ z) := by
    exact (((congrArg (fun _t : G => (((x ◇ x) ◇ (y ◇ (z ◇ z))) ◇ (((x ◇ x) ◇ (y ◇ (z ◇ z))) ◇ _t))) ((p2 (z ◇ z) x y)))).symm).trans ((p2 ((x ◇ x) ◇ (y ◇ (z ◇ z))) z (z ◇ z)))
  have p11 (x y z : G) : (d x y) = (x ◇ ((z ◇ z) ◇ (y ◇ x))) := by
    exact (((congrArg (fun _t : G => (d x _t)) ((p2 x z y)))).symm).trans ((p4 x (x ◇ ((z ◇ z) ◇ (y ◇ x)))))
  have p12 (x y z : G) : (r x y) = (y ◇ (y ◇ ((z ◇ z) ◇ x))) := by
    exact ((((congrArg (fun _t : G => (y ◇ (y ◇ ((z ◇ z) ◇ _t)))) ((p5 x y)))).symm).trans ((p2 y z (r x y)))).symm
  have p13 (x y : G) : (d (r x y) x) = y := by
    exact (((congrArg (fun _t : G => (d (r x y) _t)) ((p5 x y)))).symm).trans ((p4 (r x y) y))
  have p30 (x y z : G) : (d x (d x y)) = ((z ◇ z) ◇ (y ◇ x)) := by
    exact (((congrArg (fun _t : G => (d x _t)) (((p11 x y z)).symm))).symm).trans ((p4 x ((z ◇ z) ◇ (y ◇ x))))
  have p46 (x y : G) : ((x ◇ x) ◇ (r (x ◇ x) (x ◇ x))) = (y ◇ y) := by
    exact (((congrArg (fun _t : G => ((x ◇ x) ◇ _t)) (((p12 (x ◇ x) (x ◇ x) y)).symm))).symm).trans ((p2 (x ◇ x) x (y ◇ y)))
  have p60 (x y z : G) : (d (x ◇ (x ◇ ((y ◇ y) ◇ z))) z) = x := by
    exact (((congrArg (fun _t : G => (d _t z)) ((p12 z x y)))).symm).trans ((p13 z x))
  have p72 (x : G) : ((x ◇ x) ◇ (x ◇ x)) = (x ◇ x) := by
    exact (((p9 x ((x ◇ x) ◇ (x ◇ x)) (x ◇ x))).symm).trans ((p8 x (x ◇ x) (x ◇ x) (x ◇ x)))
  have p79 (x y : G) : (r (x ◇ x) y) = (y ◇ (y ◇ (x ◇ x))) := by
    exact (((congrArg (fun _t : G => (r _t y)) ((p72 x)))).symm).trans ((((congrArg (fun _t : G => (r (_t ◇ (x ◇ x)) y)) ((p72 x)))).symm).trans ((((congrArg (fun _t : G => (r (((x ◇ x) ◇ _t) ◇ (x ◇ x)) y)) ((p72 x)))).symm).trans ((((congrArg (fun _t : G => (r ((_t ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (x ◇ x)) y)) ((p72 x)))).symm).trans (((p12 ((((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (x ◇ x)) y ((x ◇ x) ◇ (x ◇ x)))).trans ((congrArg (fun _t : G => (y ◇ (y ◇ _t))) ((p9 (x ◇ x) (x ◇ x) x))))))))
  have p88 (x y : G) : (x ◇ x) = (y ◇ y) := by
    exact (((p72 x)).symm).trans ((((congrArg (fun _t : G => ((x ◇ x) ◇ _t)) ((p72 x)))).symm).trans ((((congrArg (fun _t : G => ((x ◇ x) ◇ ((x ◇ x) ◇ _t))) ((p72 x)))).symm).trans ((((congrArg (fun _t : G => ((x ◇ x) ◇ _t)) ((p79 x (x ◇ x))))).symm).trans ((p46 x y)))))
  have p90 (x y : G) : (x ◇ (x ◇ (y ◇ y))) = x := by
    exact (((congrArg (fun _t : G => (x ◇ (x ◇ _t))) ((p88 (x ◇ x) y)))).symm).trans ((p2 x x x))
  have p91 (x y : G) : (d x (y ◇ y)) = x := by
    exact (((congrArg (fun _t : G => (d x _t)) ((p88 x y)))).symm).trans ((p4 x x))
  have p99 (x y : G) : (d x x) = (x ◇ (y ◇ y)) := by
    exact ((p11 x x x)).trans ((congrArg (fun _t : G => (x ◇ _t)) ((p88 (x ◇ x) y))))
  have p133 (x y : G) : (d x (d x x)) = (y ◇ y) := by
    exact (((congrArg (fun _t : G => (d x _t)) (((p99 x y)).symm))).symm).trans ((p4 x (y ◇ y)))
  have p367 (x y : G) : ((x ◇ x) ◇ ((d y y) ◇ y)) = y := by
    exact ((((p91 y a)).symm).trans ((((congrArg (fun _t : G => (d y _t)) ((p133 y a)))).symm).trans ((p30 y (d y y) x)))).symm
  have p408 (x y : G) : (d (x ◇ x) y) = ((d y y) ◇ y) := by
    exact (((congrArg (fun _t : G => (d (x ◇ x) _t)) ((p367 x y)))).symm).trans ((p4 (x ◇ x) ((d y y) ◇ y)))
  have p464 (x y : G) : (d (d x x) (d (y ◇ y) x)) = x := by
    exact (((congrArg (fun _t : G => (d (d x x) _t)) (((p408 y x)).symm))).symm).trans ((p4 (d x x) x))
  have p498 (x y : G) : (d (d ((x ◇ x) ◇ y) ((x ◇ x) ◇ y)) y) = ((x ◇ x) ◇ y) := by
    exact (((congrArg (fun _t : G => (d (d ((x ◇ x) ◇ y) ((x ◇ x) ◇ y)) _t)) ((p4 (x ◇ x) y)))).symm).trans ((p464 ((x ◇ x) ◇ y) x))
  have p762 (x y z : G) : ((x ◇ x) ◇ y) = (z ◇ z) := by
    exact (((p498 x y)).symm).trans ((((congrArg (fun _t : G => (d (d ((x ◇ x) ◇ y) _t) y)) ((p91 ((x ◇ x) ◇ y) z)))).symm).trans ((((congrArg (fun _t : G => (d _t y)) (((p30 ((x ◇ x) ◇ y) (z ◇ z) z)).symm))).symm).trans ((p60 (z ◇ z) x y))))
  have p772 (x y : G) : x = y := by
    exact (((p90 x a)).symm).trans ((((congrArg (fun _t : G => (x ◇ (x ◇ _t))) ((p762 a (y ◇ x) a)))).symm).trans ((p2 x a y)))
  exact (p772 a a).trans (p772 b a).symm

@[reducible] def Equation39214 (G : Type _) [Magma G] : Prop := ∀ (x y z : G), x = (((y ◇ x) ◇ (z ◇ z)) ◇ y) ◇ y

theorem finite_trivial_dual (G : Type*) [Magma G] [Finite G] (h : Equation39214 G) : Equation2 G := by
  let opposite : Magma G := ⟨fun x y => y ◇ x⟩
  have hd : @ Equation6912 G opposite := by
    intro x y z
    exact h x y z
  exact @ finite_trivial G opposite inferInstance hd

#print axioms finite_trivial_dual

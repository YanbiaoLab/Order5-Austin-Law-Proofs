import Mathlib.Data.Fintype.Card
import JudgeMagma.Magma

@[reducible] def Equation2 (G : Type _) [Magma G] : Prop := ∀ (x y : G), x = y
@[reducible] def Equation7763 (G : Type _) [Magma G] : Prop := ∀ (x y z : G), x = y ◇ (y ◇ ((z ◇ (x ◇ z)) ◇ y))

theorem finite_trivial (G : Type*) [Magma G] [Finite G] (h : Equation7763 G) : Equation2 G := by
  intro a b
  have ls (y : G) : Function.Surjective (fun t : G => y ◇ t) := by
    intro x
    exact ⟨(y ◇ ((a ◇ (x ◇ a)) ◇ y)), (h x y a).symm⟩
  have li (y : G) : Function.Injective (fun t : G => y ◇ t) :=
    Finite.injective_iff_surjective.mpr (ls y)
  let d (x y : G) : G := Classical.choose (ls x y)
  have ld1 (x y : G) : x ◇ d x y = y := Classical.choose_spec (ls x y)
  have ld2 (x y : G) : d x (x ◇ y) = y := li x (ld1 x (x ◇ y))
  have rs (t : G) : Function.Surjective (fun w : G => w ◇ t) := by
    have ti : Function.Injective (fun x : G => ((a ◇ (x ◇ a)) ◇ t)) := by
      intro u v huv
      change ((a ◇ (u ◇ a)) ◇ t) = ((a ◇ (v ◇ a)) ◇ t) at huv
      calc u = (t ◇ (t ◇ ((a ◇ (u ◇ a)) ◇ t))) := h u t a
           _ = (t ◇ (t ◇ ((a ◇ (v ◇ a)) ◇ t))) := by rw [huv]
           _ = v := (h v t a).symm
    intro u
    obtain ⟨x, hx⟩ := (Finite.injective_iff_surjective.mp ti) u
    exact ⟨(a ◇ (x ◇ a)), hx⟩
  have ri (y : G) : Function.Injective (fun t : G => t ◇ y) :=
    Finite.injective_iff_surjective.mpr (rs y)
  let r (x y : G) : G := Classical.choose (rs y x)
  have rd1 (x y : G) : r x y ◇ y = x := Classical.choose_spec (rs y x)
  have rd2 (x y : G) : r (x ◇ y) y = x := ri y (rd1 (x ◇ y) y)
  have p2 (x y z : G) : (x ◇ (x ◇ ((y ◇ (z ◇ y)) ◇ x))) = z := by
    exact (h z x y).symm
  have p3 (x y : G) : (x ◇ (d x y)) = y := by
    exact (ld1 x y)
  have p4 (x y : G) : (d x (x ◇ y)) = y := by
    exact (ld2 x y)
  have p9 (u x y z : G) : (((x ◇ (y ◇ x)) ◇ ((z ◇ (u ◇ z)) ◇ (x ◇ (y ◇ x)))) ◇ (((x ◇ (y ◇ x)) ◇ ((z ◇ (u ◇ z)) ◇ (x ◇ (y ◇ x)))) ◇ u)) = y := by
    exact (((congrArg (fun _t : G => (((x ◇ (y ◇ x)) ◇ ((z ◇ (u ◇ z)) ◇ (x ◇ (y ◇ x)))) ◇ (((x ◇ (y ◇ x)) ◇ ((z ◇ (u ◇ z)) ◇ (x ◇ (y ◇ x)))) ◇ _t))) ((p2 (x ◇ (y ◇ x)) z u)))).symm).trans ((p2 ((x ◇ (y ◇ x)) ◇ ((z ◇ (u ◇ z)) ◇ (x ◇ (y ◇ x)))) x y))
  have p10 (x y z : G) : (x ◇ (x ◇ (((d y z) ◇ z) ◇ x))) = y := by
    exact (((congrArg (fun _t : G => (x ◇ (x ◇ (((d y z) ◇ _t) ◇ x)))) ((p3 y z)))).symm).trans ((p2 x (d y z) y))
  have p12 (x y z : G) : (d x y) = (x ◇ ((z ◇ (y ◇ z)) ◇ x)) := by
    exact (((congrArg (fun _t : G => (d x _t)) ((p2 x z y)))).symm).trans ((p4 x (x ◇ ((z ◇ (y ◇ z)) ◇ x))))
  have p33 (x y z : G) : (d x y) = (x ◇ (((d y z) ◇ z) ◇ x)) := by
    exact (((congrArg (fun _t : G => (d x _t)) ((p10 x y z)))).symm).trans ((p4 x (x ◇ (((d y z) ◇ z) ◇ x))))
  have p45 (x y z : G) : (x ◇ ((y ◇ ((x ◇ z) ◇ y)) ◇ x)) = z := by
    exact (((p12 x (x ◇ z) y)).symm).trans ((p4 x z))
  have p160 (u w x y z : G) : (((x ◇ (y ◇ x)) ◇ ((d z u) ◇ (x ◇ (y ◇ x)))) ◇ (((x ◇ (y ◇ x)) ◇ ((z ◇ (((d u w) ◇ w) ◇ z)) ◇ (x ◇ (y ◇ x)))) ◇ ((d u w) ◇ w))) = y := by
    exact (((congrArg (fun _t : G => (((x ◇ (y ◇ x)) ◇ (_t ◇ (x ◇ (y ◇ x)))) ◇ (((x ◇ (y ◇ x)) ◇ ((z ◇ (((d u w) ◇ w) ◇ z)) ◇ (x ◇ (y ◇ x)))) ◇ ((d u w) ◇ w)))) (((p33 z u w)).symm))).symm).trans ((p9 ((d u w) ◇ w) x y z))
  have p220 (u x y z : G) : (x ◇ ((((x ◇ y) ◇ (((d z u) ◇ u) ◇ (x ◇ y))) ◇ z) ◇ x)) = y := by
    exact (((congrArg (fun _t : G => (x ◇ ((((x ◇ y) ◇ (((d z u) ◇ u) ◇ (x ◇ y))) ◇ _t) ◇ x))) ((p10 (x ◇ y) z u)))).symm).trans ((p45 x ((x ◇ y) ◇ (((d z u) ◇ u) ◇ (x ◇ y))) y))
  have p225 (x y z : G) : (x ◇ ((d y z) ◇ x)) = (z ◇ x) := by
    exact (((congrArg (fun _t : G => (x ◇ (_t ◇ x))) (((p12 y z x)).symm))).symm).trans ((p45 x y (z ◇ x)))
  have p228 (u w x y z : G) : (((x ◇ (y ◇ x)) ◇ ((((z ◇ ((u ◇ w) ◇ z)) ◇ u) ◇ w) ◇ (x ◇ (y ◇ x)))) ◇ (((x ◇ (y ◇ x)) ◇ ((((z ◇ ((u ◇ w) ◇ z)) ◇ u) ◇ w) ◇ (x ◇ (y ◇ x)))) ◇ u)) = y := by
    exact (((congrArg (fun _t : G => (((x ◇ (y ◇ x)) ◇ ((((z ◇ ((u ◇ w) ◇ z)) ◇ u) ◇ w) ◇ (x ◇ (y ◇ x)))) ◇ (((x ◇ (y ◇ x)) ◇ ((((z ◇ ((u ◇ w) ◇ z)) ◇ u) ◇ _t) ◇ (x ◇ (y ◇ x)))) ◇ u))) ((p45 u z w)))).symm).trans ((((congrArg (fun _t : G => (((x ◇ (y ◇ x)) ◇ ((((z ◇ ((u ◇ w) ◇ z)) ◇ u) ◇ _t) ◇ (x ◇ (y ◇ x)))) ◇ (((x ◇ (y ◇ x)) ◇ ((((z ◇ ((u ◇ w) ◇ z)) ◇ u) ◇ (u ◇ ((z ◇ ((u ◇ w) ◇ z)) ◇ u))) ◇ (x ◇ (y ◇ x)))) ◇ u))) ((p45 u z w)))).symm).trans ((p9 u x y ((z ◇ ((u ◇ w) ◇ z)) ◇ u))))
  have p246 (x y z : G) : ((x ◇ y) ◇ z) = (z ◇ (y ◇ z)) := by
    exact ((((congrArg (fun _t : G => (z ◇ (_t ◇ z))) ((p45 x z y)))).symm).trans ((p45 z x ((x ◇ y) ◇ z)))).symm
  have p255 (x y : G) : (x ◇ (x ◇ (x ◇ (y ◇ x)))) = x := by
    exact (((congrArg (fun _t : G => (x ◇ (x ◇ _t))) ((p246 x y x)))).symm).trans ((((congrArg (fun _t : G => (x ◇ _t)) ((p246 y (x ◇ y) x)))).symm).trans ((((p246 a (y ◇ (x ◇ y)) x)).symm).trans ((((congrArg (fun _t : G => ((a ◇ (y ◇ (x ◇ y))) ◇ _t)) ((p2 ((d a a) ◇ a) y x)))).symm).trans ((((congrArg (fun _t : G => ((a ◇ (y ◇ (x ◇ y))) ◇ (((d a a) ◇ a) ◇ _t))) ((p246 (a ◇ (((d a a) ◇ a) ◇ a)) (y ◇ (x ◇ y)) ((d a a) ◇ a))))).symm).trans ((((congrArg (fun _t : G => ((a ◇ (y ◇ (x ◇ y))) ◇ _t)) ((p246 (y ◇ (x ◇ y)) ((a ◇ (((d a a) ◇ a) ◇ a)) ◇ (y ◇ (x ◇ y))) ((d a a) ◇ a))))).symm).trans ((((congrArg (fun _t : G => (_t ◇ (((y ◇ (x ◇ y)) ◇ ((a ◇ (((d a a) ◇ a) ◇ a)) ◇ (y ◇ (x ◇ y)))) ◇ ((d a a) ◇ a)))) ((p225 (y ◇ (x ◇ y)) a a)))).symm).trans ((p160 a a y x a))))))))
  have p268 (x : G) : (x ◇ x) = x := by
    exact (((congrArg (fun _t : G => (x ◇ _t)) ((p255 x a)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (x ◇ (x ◇ _t)))) ((p246 x a x)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (x ◇ _t))) ((p246 a (x ◇ a) x)))).symm).trans ((((congrArg (fun _t : G => (x ◇ _t)) ((p246 ((a ◇ (a ◇ (a ◇ a))) ◇ a) (a ◇ (x ◇ a)) x)))).symm).trans ((((p246 (a ◇ (x ◇ a)) (((a ◇ (a ◇ (a ◇ a))) ◇ a) ◇ (a ◇ (x ◇ a))) x)).symm).trans ((((congrArg (fun _t : G => (((a ◇ (x ◇ a)) ◇ (((a ◇ (a ◇ (a ◇ a))) ◇ a) ◇ (a ◇ (x ◇ a)))) ◇ _t)) ((p2 a a x)))).symm).trans ((((congrArg (fun _t : G => (((a ◇ (x ◇ a)) ◇ (((a ◇ (a ◇ (a ◇ a))) ◇ a) ◇ (a ◇ (x ◇ a)))) ◇ (a ◇ _t))) ((p246 ((a ◇ (a ◇ (a ◇ a))) ◇ a) (a ◇ (x ◇ a)) a)))).symm).trans ((((congrArg (fun _t : G => (((a ◇ (x ◇ a)) ◇ (((a ◇ (a ◇ (a ◇ a))) ◇ a) ◇ (a ◇ (x ◇ a)))) ◇ _t)) ((p246 (a ◇ (x ◇ a)) (((a ◇ (a ◇ (a ◇ a))) ◇ a) ◇ (a ◇ (x ◇ a))) a)))).symm).trans ((((congrArg (fun _t : G => (((a ◇ (x ◇ a)) ◇ (((a ◇ (a ◇ (a ◇ a))) ◇ a) ◇ (a ◇ (x ◇ a)))) ◇ (((a ◇ (x ◇ a)) ◇ (((a ◇ _t) ◇ a) ◇ (a ◇ (x ◇ a)))) ◇ a))) ((p246 (a ◇ a) a a)))).symm).trans ((((congrArg (fun _t : G => (((a ◇ (x ◇ a)) ◇ (((a ◇ (a ◇ (a ◇ a))) ◇ a) ◇ (a ◇ (x ◇ a)))) ◇ (((a ◇ (x ◇ a)) ◇ ((_t ◇ a) ◇ (a ◇ (x ◇ a)))) ◇ a))) ((p246 a ((a ◇ a) ◇ a) a)))).symm).trans ((((congrArg (fun _t : G => (((a ◇ (x ◇ a)) ◇ (((a ◇ _t) ◇ a) ◇ (a ◇ (x ◇ a)))) ◇ (((a ◇ (x ◇ a)) ◇ ((((a ◇ ((a ◇ a) ◇ a)) ◇ a) ◇ a) ◇ (a ◇ (x ◇ a)))) ◇ a))) ((p246 (a ◇ a) a a)))).symm).trans ((((congrArg (fun _t : G => (((a ◇ (x ◇ a)) ◇ ((_t ◇ a) ◇ (a ◇ (x ◇ a)))) ◇ (((a ◇ (x ◇ a)) ◇ ((((a ◇ ((a ◇ a) ◇ a)) ◇ a) ◇ a) ◇ (a ◇ (x ◇ a)))) ◇ a))) ((p246 a ((a ◇ a) ◇ a) a)))).symm).trans ((p228 a a a x a)))))))))))))
  have p272 (x y : G) : x = y := by
    exact (((p268 x)).symm).trans ((((congrArg (fun _t : G => (x ◇ _t)) ((p255 x a)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (x ◇ (x ◇ _t)))) ((p246 (x ◇ y) a x)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (x ◇ _t))) ((p246 a ((x ◇ y) ◇ a) x)))).symm).trans ((((congrArg (fun _t : G => (x ◇ _t)) ((p246 a (a ◇ ((x ◇ y) ◇ a)) x)))).symm).trans ((((congrArg (fun _t : G => (x ◇ ((a ◇ _t) ◇ x))) ((p246 ((d a a) ◇ a) (x ◇ y) a)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (_t ◇ x))) ((p246 (x ◇ y) (((d a a) ◇ a) ◇ (x ◇ y)) a)))).symm).trans ((p220 a x y a))))))))
  exact (p272 a a).trans (p272 b a).symm

@[reducible] def Equation38565 (G : Type _) [Magma G] : Prop := ∀ (x y z : G), x = ((y ◇ ((z ◇ x) ◇ z)) ◇ y) ◇ y

theorem finite_trivial_dual (G : Type*) [Magma G] [Finite G] (h : Equation38565 G) : Equation2 G := by
  let opposite : Magma G := ⟨fun x y => y ◇ x⟩
  have hd : @ Equation7763 G opposite := by
    intro x y z
    exact h x y z
  exact @ finite_trivial G opposite inferInstance hd

#print axioms finite_trivial_dual

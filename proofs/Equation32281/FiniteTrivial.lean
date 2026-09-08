import Mathlib.Data.Fintype.Card
import JudgeMagma.Magma

@[reducible] def Equation2 (G : Type _) [Magma G] : Prop := ∀ (x y : G), x = y
@[reducible] def Equation13849 (G : Type _) [Magma G] : Prop := ∀ (x y z : G), x = y ◇ ((y ◇ ((x ◇ z) ◇ z)) ◇ z)

theorem finite_trivial (G : Type*) [Magma G] [Finite G] (h : Equation13849 G) : Equation2 G := by
  intro a b
  have ls (y : G) : Function.Surjective (fun t : G => y ◇ t) := by
    intro x
    exact ⟨((y ◇ ((x ◇ a) ◇ a)) ◇ a), (h x y a).symm⟩
  have li (y : G) : Function.Injective (fun t : G => y ◇ t) :=
    Finite.injective_iff_surjective.mpr (ls y)
  let d (x y : G) : G := Classical.choose (ls x y)
  have ld1 (x y : G) : x ◇ d x y = y := Classical.choose_spec (ls x y)
  have ld2 (x y : G) : d x (x ◇ y) = y := li x (ld1 x (x ◇ y))
  have rs (t : G) : Function.Surjective (fun w : G => w ◇ t) := by
    have ti : Function.Injective (fun x : G => ((a ◇ ((x ◇ t) ◇ t)) ◇ t)) := by
      intro u v huv
      change ((a ◇ ((u ◇ t) ◇ t)) ◇ t) = ((a ◇ ((v ◇ t) ◇ t)) ◇ t) at huv
      calc u = (a ◇ ((a ◇ ((u ◇ t) ◇ t)) ◇ t)) := h u a t
           _ = (a ◇ ((a ◇ ((v ◇ t) ◇ t)) ◇ t)) := by rw [huv]
           _ = v := (h v a t).symm
    intro u
    obtain ⟨x, hx⟩ := (Finite.injective_iff_surjective.mp ti) u
    exact ⟨(a ◇ ((x ◇ t) ◇ t)), hx⟩
  have ri (y : G) : Function.Injective (fun t : G => t ◇ y) :=
    Finite.injective_iff_surjective.mpr (rs y)
  let r (x y : G) : G := Classical.choose (rs y x)
  have rd1 (x y : G) : r x y ◇ y = x := Classical.choose_spec (rs y x)
  have rd2 (x y : G) : r (x ◇ y) y = x := ri y (rd1 (x ◇ y) y)
  have p2 (x y z : G) : (x ◇ ((x ◇ ((y ◇ z) ◇ z)) ◇ z)) = y := by
    exact (h y x z).symm
  have p3 (x y : G) : (x ◇ (d x y)) = y := by
    exact (ld1 x y)
  have p4 (x y : G) : (d x (x ◇ y)) = y := by
    exact (ld2 x y)
  have p5 (x y : G) : ((r x y) ◇ y) = x := by
    exact (rd1 x y)
  have p8 (u x y z : G) : (x ◇ ((x ◇ (y ◇ ((z ◇ ((y ◇ u) ◇ u)) ◇ u))) ◇ ((z ◇ ((y ◇ u) ◇ u)) ◇ u))) = z := by
    exact (((congrArg (fun _t : G => (x ◇ ((x ◇ (_t ◇ ((z ◇ ((y ◇ u) ◇ u)) ◇ u))) ◇ ((z ◇ ((y ◇ u) ◇ u)) ◇ u)))) ((p2 z y u)))).symm).trans ((p2 x z ((z ◇ ((y ◇ u) ◇ u)) ◇ u)))
  have p9 (x y z : G) : (x ◇ ((x ◇ (y ◇ (d z y))) ◇ (d z y))) = z := by
    exact (((congrArg (fun _t : G => (x ◇ ((x ◇ (_t ◇ (d z y))) ◇ (d z y)))) ((p3 z y)))).symm).trans ((p2 x z (d z y)))
  have p10 (x y z : G) : (d x y) = ((x ◇ ((y ◇ z) ◇ z)) ◇ z) := by
    exact (((congrArg (fun _t : G => (d x _t)) ((p2 x y z)))).symm).trans ((p4 x ((x ◇ ((y ◇ z) ◇ z)) ◇ z)))
  have p11 (x y z : G) : (r x y) = (z ◇ ((z ◇ (x ◇ y)) ◇ y)) := by
    exact ((((congrArg (fun _t : G => (z ◇ ((z ◇ (_t ◇ y)) ◇ y))) ((p5 x y)))).symm).trans ((p2 z (r x y) y))).symm
  have p38 (u x y z : G) : (x ◇ ((x ◇ (y ◇ ((z ◇ ((y ◇ u) ◇ u)) ◇ u))) ◇ (d z y))) = z := by
    exact (((congrArg (fun _t : G => (x ◇ ((x ◇ (y ◇ ((z ◇ ((y ◇ u) ◇ u)) ◇ u))) ◇ _t))) (((p10 z y u)).symm))).symm).trans ((p8 u x y z))
  have p42 (u x y z : G) : (d x (y ◇ ((z ◇ u) ◇ u))) = ((x ◇ ((d y z) ◇ u)) ◇ u) := by
    exact ((p10 x (y ◇ ((z ◇ u) ◇ u)) u)).trans ((congrArg (fun _t : G => ((x ◇ (_t ◇ u)) ◇ u)) (((p10 y z u)).symm)))
  have p47 (x y z : G) : ((x ◇ ((x ◇ (y ◇ z)) ◇ z)) ◇ z) = y := by
    exact (((congrArg (fun _t : G => (_t ◇ z)) ((p11 y z x)))).symm).trans ((p5 y z))
  have p61 (x y z : G) : (r (x ◇ (y ◇ z)) z) = (x ◇ y) := by
    exact (((p11 (x ◇ (y ◇ z)) z x)).trans ((congrArg (fun _t : G => (x ◇ (_t ◇ z))) (((p11 y z x)).symm)))).trans ((congrArg (fun _t : G => (x ◇ _t)) ((p5 y z))))
  have p62 (x y : G) : (x ◇ ((x ◇ y) ◇ (d y y))) = y := by
    exact (((congrArg (fun _t : G => (x ◇ ((x ◇ _t) ◇ (d y y)))) ((p3 y y)))).symm).trans ((p9 x y y))
  have p72 (x y z : G) : ((x ◇ y) ◇ z) = (x ◇ (y ◇ z)) := by
    exact (((congrArg (fun _t : G => (_t ◇ z)) ((p61 x y z)))).symm).trans ((p5 (x ◇ (y ◇ z)) z))
  have p94 (x y : G) : (x ◇ (x ◇ y)) = y := by
    exact (((congrArg (fun _t : G => (x ◇ (x ◇ _t))) ((p3 y y)))).symm).trans ((((congrArg (fun _t : G => (x ◇ _t)) ((p72 x y (d y y))))).symm).trans ((p62 x y)))
  have p105 (x y : G) : (x ◇ y) = x := by
    exact (((congrArg (fun _t : G => (x ◇ _t)) ((p94 y y)))).symm).trans ((((congrArg (fun _t : G => (x ◇ _t)) ((p72 y y y)))).symm).trans ((((p72 x (y ◇ y) y)).symm).trans ((((congrArg (fun _t : G => (_t ◇ y)) ((p94 a (x ◇ (y ◇ y)))))).symm).trans ((((congrArg (fun _t : G => ((a ◇ (a ◇ _t)) ◇ y)) ((p72 x y y)))).symm).trans ((((congrArg (fun _t : G => ((a ◇ _t) ◇ y)) ((p72 a (x ◇ y) y)))).symm).trans ((p47 a x y)))))))
  have p109 (x y : G) : (d x y) = x := by
    exact ((((((congrArg (fun _t : G => (d x _t)) ((p105 y a)))).symm).trans ((((congrArg (fun _t : G => (d x (y ◇ _t))) ((p105 a a)))).symm).trans ((((congrArg (fun _t : G => (d x (y ◇ (_t ◇ a)))) ((p105 a a)))).symm).trans ((p42 a x y a))))).trans ((congrArg (fun _t : G => ((x ◇ _t) ◇ a)) ((p105 (d y a) a))))).trans ((congrArg (fun _t : G => (_t ◇ a)) ((p105 x (d y a)))))).trans ((p105 x a))
  have p111 (x y : G) : x = y := by
    exact (((p105 x x)).symm).trans ((((congrArg (fun _t : G => (x ◇ _t)) ((p105 x y)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (x ◇ _t))) ((p109 y a)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (_t ◇ (d y a)))) ((p105 x a)))).symm).trans ((((congrArg (fun _t : G => (x ◇ ((x ◇ _t) ◇ (d y a)))) ((p105 a y)))).symm).trans ((((congrArg (fun _t : G => (x ◇ ((x ◇ (a ◇ _t)) ◇ (d y a)))) ((p105 y a)))).symm).trans ((((congrArg (fun _t : G => (x ◇ ((x ◇ (a ◇ (_t ◇ a))) ◇ (d y a)))) ((p105 y a)))).symm).trans ((((congrArg (fun _t : G => (x ◇ ((x ◇ (a ◇ ((y ◇ _t) ◇ a))) ◇ (d y a)))) ((p105 a a)))).symm).trans ((((congrArg (fun _t : G => (x ◇ ((x ◇ (a ◇ ((y ◇ (_t ◇ a)) ◇ a))) ◇ (d y a)))) ((p105 a a)))).symm).trans ((p38 a x a y))))))))))
  exact (p111 a a).trans (p111 b a).symm

@[reducible] def Equation32281 (G : Type _) [Magma G] : Prop := ∀ (x y z : G), x = (y ◇ ((y ◇ (y ◇ x)) ◇ z)) ◇ z

theorem finite_trivial_dual (G : Type*) [Magma G] [Finite G] (h : Equation32281 G) : Equation2 G := by
  let opposite : Magma G := ⟨fun x y => y ◇ x⟩
  have hd : @ Equation13849 G opposite := by
    intro x y z
    exact h x z y
  exact @ finite_trivial G opposite inferInstance hd

#print axioms finite_trivial_dual

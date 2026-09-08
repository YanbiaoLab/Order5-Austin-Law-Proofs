import Mathlib.Data.Fintype.Card
import JudgeMagma.Magma

@[reducible] def Equation2 (G : Type _) [Magma G] : Prop := ∀ (x y : G), x = y
@[reducible] def Equation19966 (G : Type _) [Magma G] : Prop := ∀ (x y z : G), x = (y ◇ y) ◇ ((x ◇ (x ◇ z)) ◇ z)

theorem finite_trivial (G : Type*) [Magma G] [Finite G] (h : Equation19966 G) : Equation2 G := by
  intro a b
  have ls (y : G) : Function.Surjective (fun t : G => (y ◇ y) ◇ t) := by
    intro x
    exact ⟨((x ◇ (x ◇ a)) ◇ a), (h x y a).symm⟩
  have li (y : G) : Function.Injective (fun t : G => (y ◇ y) ◇ t) :=
    Finite.injective_iff_surjective.mpr (ls y)
  let d (x y : G) : G := Classical.choose (ls x y)
  have ld1 (x y : G) : (x ◇ x) ◇ d x y = y := Classical.choose_spec (ls x y)
  have ld2 (x y : G) : d x ((x ◇ x) ◇ y) = y := li x (ld1 x ((x ◇ x) ◇ y))
  have rs (t : G) : Function.Surjective (fun w : G => w ◇ t) := by
    have ti : Function.Injective (fun x : G => ((x ◇ (x ◇ t)) ◇ t)) := by
      intro u v huv
      change ((u ◇ (u ◇ t)) ◇ t) = ((v ◇ (v ◇ t)) ◇ t) at huv
      calc u = ((a ◇ a) ◇ ((u ◇ (u ◇ t)) ◇ t)) := h u a t
           _ = ((a ◇ a) ◇ ((v ◇ (v ◇ t)) ◇ t)) := by rw [huv]
           _ = v := (h v a t).symm
    intro u
    obtain ⟨x, hx⟩ := (Finite.injective_iff_surjective.mp ti) u
    exact ⟨(x ◇ (x ◇ t)), hx⟩
  have ri (y : G) : Function.Injective (fun t : G => t ◇ y) :=
    Finite.injective_iff_surjective.mpr (rs y)
  let r (x y : G) : G := Classical.choose (rs y x)
  have rd1 (x y : G) : r x y ◇ y = x := Classical.choose_spec (rs y x)
  have rd2 (x y : G) : r (x ◇ y) y = x := ri y (rd1 (x ◇ y) y)
  have p2 (x y z : G) : ((x ◇ x) ◇ ((y ◇ (y ◇ z)) ◇ z)) = y := by
    exact (h y x z).symm
  have p3 (x y : G) : ((x ◇ x) ◇ (d x y)) = y := by
    exact (ld1 x y)
  have p5 (x y : G) : ((r x y) ◇ y) = x := by
    exact (rd1 x y)
  have p8 (u x y z : G) : ((x ◇ x) ◇ (((y ◇ y) ◇ z) ◇ ((z ◇ (z ◇ u)) ◇ u))) = (y ◇ y) := by
    exact (((congrArg (fun _t : G => ((x ◇ x) ◇ (((y ◇ y) ◇ _t) ◇ ((z ◇ (z ◇ u)) ◇ u)))) ((p2 y z u)))).symm).trans ((p2 x (y ◇ y) ((z ◇ (z ◇ u)) ◇ u)))
  have p9 (x y z : G) : ((x ◇ x) ◇ (((y ◇ y) ◇ z) ◇ (d y z))) = (y ◇ y) := by
    exact (((congrArg (fun _t : G => ((x ◇ x) ◇ (((y ◇ y) ◇ _t) ◇ (d y z)))) ((p3 y z)))).symm).trans ((p2 x (y ◇ y) (d y z)))
  have p11 (x y z : G) : ((x ◇ x) ◇ (((r y z) ◇ y) ◇ z)) = (r y z) := by
    exact (((congrArg (fun _t : G => ((x ◇ x) ◇ (((r y z) ◇ _t) ◇ z))) ((p5 y z)))).symm).trans ((p2 x (r y z) z))
  have p17 (x y : G) : ((x ◇ x) ◇ (y ◇ y)) = (y ◇ y) := by
    exact (((congrArg (fun _t : G => ((x ◇ x) ◇ _t)) ((p2 (y ◇ y) (y ◇ y) a)))).symm).trans ((p8 a x y (y ◇ y)))
  have p19 (x y : G) : (x ◇ x) = (y ◇ y) := by
    exact (((p17 a x)).symm).trans ((((congrArg (fun _t : G => ((a ◇ a) ◇ _t)) ((p9 x x a)))).symm).trans ((((congrArg (fun _t : G => ((a ◇ a) ◇ (_t ◇ (((x ◇ x) ◇ a) ◇ (d x a))))) ((p17 y x)))).symm).trans ((((congrArg (fun _t : G => ((a ◇ a) ◇ (((y ◇ y) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ _t) ◇ (d x a))))) ((p3 x a)))).symm).trans ((p8 (d x a) a y (x ◇ x))))))
  have p23 (x y z : G) : ((x ◇ x) ◇ ((y ◇ (z ◇ z)) ◇ y)) = y := by
    exact (((congrArg (fun _t : G => ((x ◇ x) ◇ ((y ◇ _t) ◇ y))) ((p19 y z)))).symm).trans ((p2 x y y))
  have p43 (x : G) : (r x x) = (x ◇ x) := by
    exact ((((p17 a x)).symm).trans ((((congrArg (fun _t : G => ((a ◇ a) ◇ (_t ◇ x))) ((p5 x x)))).symm).trans ((p11 a x x)))).symm
  have p47 (x : G) : ((x ◇ x) ◇ x) = x := by
    exact (((congrArg (fun _t : G => (_t ◇ x)) ((p43 x)))).symm).trans ((p5 x x))
  have p48 (x y : G) : ((x ◇ (x ◇ y)) ◇ y) = x := by
    exact (((p47 ((x ◇ (x ◇ y)) ◇ y))).symm).trans ((p2 ((x ◇ (x ◇ y)) ◇ y) x y))
  have p50 (x y : G) : ((x ◇ x) ◇ y) = y := by
    exact (((congrArg (fun _t : G => (_t ◇ y)) ((p19 y x)))).symm).trans ((p47 y))
  have p56 (x y : G) : ((x ◇ (y ◇ y)) ◇ x) = x := by
    exact (((p50 a ((x ◇ (y ◇ y)) ◇ x))).symm).trans ((p23 a x y))
  have p60 (x y : G) : (x ◇ (y ◇ y)) = (x ◇ x) := by
    exact ((((congrArg (fun _t : G => (_t ◇ x)) ((p56 x y)))).symm).trans ((((congrArg (fun _t : G => (((x ◇ (y ◇ y)) ◇ _t) ◇ x)) ((p56 x y)))).symm).trans ((p48 (x ◇ (y ◇ y)) x)))).symm
  have p64 (x y z : G) : ((x ◇ (y ◇ y)) ◇ z) = z := by
    exact (((congrArg (fun _t : G => (_t ◇ z)) (((p60 x y)).symm))).symm).trans ((p50 x z))
  have p65 (x y : G) : (x ◇ x) = y := by
    exact (((p64 y y (x ◇ x))).symm).trans ((((congrArg (fun _t : G => ((y ◇ _t) ◇ (x ◇ x))) ((p60 y x)))).symm).trans ((p48 y (x ◇ x))))
  exact (p65 a a).symm.trans (p65 a b)

@[reducible] def Equation26105 (G : Type _) [Magma G] : Prop := ∀ (x y z : G), x = (y ◇ ((y ◇ x) ◇ x)) ◇ (z ◇ z)

theorem finite_trivial_dual (G : Type*) [Magma G] [Finite G] (h : Equation26105 G) : Equation2 G := by
  let opposite : Magma G := ⟨fun x y => y ◇ x⟩
  have hd : @ Equation19966 G opposite := by
    intro x y z
    exact h x z y
  exact @ finite_trivial G opposite inferInstance hd

#print axioms finite_trivial_dual

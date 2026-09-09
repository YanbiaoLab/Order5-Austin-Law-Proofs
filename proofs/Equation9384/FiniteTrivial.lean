import Mathlib.Data.Fintype.Card
import JudgeMagma.Magma

@[reducible] def Equation2 (G : Type _) [Magma G] : Prop := ∀ (x y : G), x = y
@[reducible] def Equation9384 (G : Type _) [Magma G] : Prop := ∀ (x y z : G), x = y ◇ ((x ◇ z) ◇ (y ◇ (z ◇ z)))

theorem finite_trivial (G : Type*) [Magma G] [Finite G] (h : Equation9384 G) : Equation2 G := by
  intro a b
  have ls (y : G) : Function.Surjective (fun t : G => y ◇ t) := by
    intro x
    exact ⟨((x ◇ a) ◇ (y ◇ (a ◇ a))), (h x y a).symm⟩
  have li (y : G) : Function.Injective (fun t : G => y ◇ t) :=
    Finite.injective_iff_surjective.mpr (ls y)
  let d (x y : G) : G := Classical.choose (ls x y)
  have ld1 (x y : G) : x ◇ d x y = y := Classical.choose_spec (ls x y)
  have ld2 (x y : G) : d x (x ◇ y) = y := li x (ld1 x (x ◇ y))
  have rs (t : G) : Function.Surjective (fun w : G => w ◇ t) := by
    have ti : Function.Injective (fun x : G => (x ◇ t)) := by
      intro u v huv
      change (u ◇ t) = (v ◇ t) at huv
      calc u = (a ◇ ((u ◇ t) ◇ (a ◇ (t ◇ t)))) := h u a t
           _ = (a ◇ ((v ◇ t) ◇ (a ◇ (t ◇ t)))) := by rw [huv]
           _ = v := (h v a t).symm
    intro u
    obtain ⟨x, hx⟩ := (Finite.injective_iff_surjective.mp ti) u
    exact ⟨x, hx⟩
  have ri (y : G) : Function.Injective (fun t : G => t ◇ y) :=
    Finite.injective_iff_surjective.mpr (rs y)
  let r (x y : G) : G := Classical.choose (rs y x)
  have rd1 (x y : G) : r x y ◇ y = x := Classical.choose_spec (rs y x)
  have rd2 (x y : G) : r (x ◇ y) y = x := ri y (rd1 (x ◇ y) y)
  have p2 (x y z : G) : (x ◇ ((y ◇ z) ◇ (x ◇ (z ◇ z)))) = y := by
    exact (h y x z).symm
  have p4 (x y : G) : (d x (x ◇ y)) = y := by
    exact (ld2 x y)
  have p5 (x y : G) : ((r x y) ◇ y) = x := by
    exact (rd1 x y)
  have p6 (x y : G) : (r (x ◇ y) y) = x := by
    exact (rd2 x y)
  have p10 (x y z : G) : (d x y) = ((y ◇ z) ◇ (x ◇ (z ◇ z))) := by
    exact (((congrArg (fun _t : G => (d x _t)) ((p2 x y z)))).symm).trans ((p4 x ((y ◇ z) ◇ (x ◇ (z ◇ z)))))
  have p11 (x y z : G) : (r x y) = (z ◇ (x ◇ (z ◇ (y ◇ y)))) := by
    exact ((((congrArg (fun _t : G => (z ◇ (_t ◇ (z ◇ (y ◇ y))))) ((p5 x y)))).symm).trans ((p2 z (r x y) y))).symm
  have p13 (x y : G) : (d (r x y) x) = y := by
    exact (((congrArg (fun _t : G => (d (r x y) _t)) ((p5 x y)))).symm).trans ((p4 (r x y) y))
  have p26 (x y z : G) : (((x ◇ y) ◇ z) ◇ (x ◇ (z ◇ z))) = y := by
    exact (((p10 x (x ◇ y) z)).symm).trans ((p4 x y))
  have p29 (x y z : G) : (d (r x (y ◇ y)) z) = ((z ◇ y) ◇ x) := by
    exact ((p10 (r x (y ◇ y)) z y)).trans ((congrArg (fun _t : G => ((z ◇ y) ◇ _t)) ((p5 x (y ◇ y)))))
  have p43 (x y : G) : (r (x ◇ x) (x ◇ x)) = ((y ◇ x) ◇ y) := by
    exact ((p11 (x ◇ x) (x ◇ x) (y ◇ x))).trans ((congrArg (fun _t : G => ((y ◇ x) ◇ _t)) ((p2 (x ◇ x) y x))))
  have p60 (x y : G) : (r (x ◇ x) (x ◇ x)) = (y ◇ (r y x)) := by
    exact ((p11 (x ◇ x) (x ◇ x) y)).trans ((congrArg (fun _t : G => (y ◇ _t)) (((p11 y x (x ◇ x))).symm)))
  have p165 (x y : G) : ((x ◇ y) ◇ x) = (y ◇ y) := by
    exact (((p29 x y x)).symm).trans ((p13 x (y ◇ y)))
  have p173 (x : G) : (r (x ◇ x) (x ◇ x)) = (x ◇ x) := by
    exact ((p43 x a)).trans ((p165 a x))
  have p176 (x y : G) : (x ◇ (r x y)) = (y ◇ y) := by
    exact ((((p173 y)).symm).trans ((p60 y x))).symm
  have p206 (x y : G) : (r (x ◇ x) y) = (y ◇ x) := by
    exact (((congrArg (fun _t : G => (r _t y)) ((p165 y x)))).symm).trans ((p6 (y ◇ x) y))
  have p207 (x y z : G) : (d x (y ◇ z)) = ((z ◇ z) ◇ (x ◇ (y ◇ y))) := by
    exact ((p10 x (y ◇ z) y)).trans ((congrArg (fun _t : G => (_t ◇ (x ◇ (y ◇ y)))) ((p165 y z))))
  have p252 (x : G) : (x ◇ x) = x := by
    exact (((p206 x x)).symm).trans ((p6 x x))
  have p255 (x y z : G) : (r (x ◇ y) (z ◇ y)) = (d x z) := by
    exact (((congrArg (fun _t : G => (r _t (z ◇ y))) ((p252 (x ◇ y))))).symm).trans ((((congrArg (fun _t : G => (r ((x ◇ y) ◇ (x ◇ _t)) (z ◇ y))) ((p252 y)))).symm).trans ((((congrArg (fun _t : G => (r ((x ◇ _t) ◇ (x ◇ (y ◇ y))) (z ◇ y))) ((p252 y)))).symm).trans (((p206 (x ◇ (y ◇ y)) (z ◇ y))).trans (((p10 x z y)).symm))))
  have p261 (x y : G) : (x ◇ y) = x := by
    exact (((congrArg (fun _t : G => (x ◇ _t)) ((p252 y)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (y ◇ _t))) ((p252 y)))).symm).trans ((((congrArg (fun _t : G => (_t ◇ (y ◇ (y ◇ y)))) ((p252 x)))).symm).trans ((((p207 y y x)).symm).trans ((((p255 y a (y ◇ x))).symm).trans ((((congrArg (fun _t : G => (r _t ((y ◇ x) ◇ a))) ((p252 (y ◇ a))))).symm).trans ((((congrArg (fun _t : G => (r ((y ◇ a) ◇ (y ◇ _t)) ((y ◇ x) ◇ a))) ((p252 a)))).symm).trans ((((congrArg (fun _t : G => (r ((y ◇ _t) ◇ (y ◇ (a ◇ a))) ((y ◇ x) ◇ a))) ((p252 a)))).symm).trans (((p206 (y ◇ (a ◇ a)) ((y ◇ x) ◇ a))).trans ((p26 y x a))))))))))
  have p264 (x y : G) : x = y := by
    exact ((((p261 x y)).symm).trans ((((congrArg (fun _t : G => (x ◇ _t)) ((p261 y x)))).symm).trans ((((congrArg (fun _t : G => (_t ◇ (y ◇ x))) ((p252 x)))).symm).trans ((((congrArg (fun _t : G => ((x ◇ x) ◇ _t)) ((p206 x y)))).symm).trans ((p176 (x ◇ x) y)))))).trans ((p252 y))
  exact (p264 a a).trans (p264 b a).symm

#print axioms finite_trivial

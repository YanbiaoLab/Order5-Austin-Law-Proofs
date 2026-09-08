import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finite.Prod
import JudgeMagma.Magma

/- Consequences only: this file does not prove Equation2. -/
namespace FinitePairInverse

theorem pair_inverse (G : Type*) [Magma G] [Finite G]
    (h : ∀ x y : G, x = (y ◇ (y ◇ x)) ◇ (x ◇ (x ◇ y))) :
    ∀ x y : G, (x ◇ y) ◇ ((x ◇ y) ◇ (y ◇ x)) = y := by
  let f : G × G → G × G := fun p =>
    (p.1 ◇ (p.1 ◇ p.2), p.2 ◇ (p.2 ◇ p.1))
  let g : G × G → G × G := fun p => (p.2 ◇ p.1, p.1 ◇ p.2)
  have hgf (p : G × G) : g (f p) = p :=
    Prod.ext (h p.1 p.2).symm (h p.2 p.1).symm
  have fi : Function.Injective f := by
    intro p q hpq
    exact (hgf p).symm.trans ((congrArg g hpq).trans (hgf q))
  have fs : Function.Surjective f := Finite.injective_iff_surjective.mp fi
  intro x y
  obtain ⟨p, hp⟩ := fs (y, x)
  have hi : g (y, x) = p := by
    rw [← hp]
    exact hgf p
  have hr : f (g (y, x)) = (y, x) := by
    rw [hi]
    exact hp
  exact congrArg Prod.fst hr

theorem square_bijective (G : Type*) [Magma G] [Finite G]
    (h : ∀ x y : G, x = (y ◇ (y ◇ x)) ◇ (x ◇ (x ◇ y))) :
    Function.Bijective (fun x : G => x ◇ x) := by
  have hs : Function.Surjective (fun x : G => x ◇ x) := by
    intro x
    exact ⟨x ◇ (x ◇ x), (h x x).symm⟩
  exact ⟨Finite.injective_iff_surjective.mpr hs, hs⟩

theorem commutes_only_when_equal (G : Type*) [Magma G] [Finite G]
    (h : ∀ x y : G, x = (y ◇ (y ◇ x)) ◇ (x ◇ (x ◇ y)))
    {a b : G} (hab : a ◇ b = b ◇ a) : a = b := by
  have hp := pair_inverse G h
  exact (hp b a).symm.trans ((by rw [hab] :
    (b ◇ a) ◇ ((b ◇ a) ◇ (a ◇ b)) = (a ◇ b) ◇ ((a ◇ b) ◇ (b ◇ a))).trans (hp a b))

end FinitePairInverse



@[reducible] def Equation2 (G : Type _) [Magma G] : Prop := ∀ (x y : G), x = y
@[reducible] def Equation21714 (G : Type _) [Magma G] : Prop := ∀ (x y z : G), x = (y ◇ (y ◇ x)) ◇ (x ◇ (x ◇ z))

theorem finite_trivial (G : Type*) [Magma G] [Finite G] (h : Equation21714 G) : Equation2 G := by
  intro a b
  have hh : ∀ x y : G, x = (y ◇ (y ◇ x)) ◇ (x ◇ (x ◇ y)) := by
    intro x y
    exact h x y y
  have hp := FinitePairInverse.pair_inverse G hh
  have p2 (x y z : G) : ((x ◇ (x ◇ y)) ◇ (y ◇ (y ◇ z))) = y := by
    exact (h y x z).symm
  have p3 (x y : G) : ((x ◇ y) ◇ ((x ◇ y) ◇ (y ◇ x))) = y := by
    exact hp x y
  have p5 (u x y z : G) : (((x ◇ (x ◇ y)) ◇ y) ◇ ((y ◇ (y ◇ z)) ◇ ((y ◇ (y ◇ z)) ◇ u))) = (y ◇ (y ◇ z)) := by
    exact (((congrArg (fun _t : G => (((x ◇ (x ◇ y)) ◇ _t) ◇ ((y ◇ (y ◇ z)) ◇ ((y ◇ (y ◇ z)) ◇ u)))) ((p2 x y z)))).symm).trans ((p2 (x ◇ (x ◇ y)) (y ◇ (y ◇ z)) u))
  have p8 (x y z : G) : (x ◇ ((x ◇ y) ◇ ((x ◇ y) ◇ z))) = (x ◇ y) := by
    exact (((congrArg (fun _t : G => (_t ◇ ((x ◇ y) ◇ ((x ◇ y) ◇ z)))) ((p3 y x)))).symm).trans ((p2 (y ◇ x) (x ◇ y) z))
  have p9 (x y z : G) : ((x ◇ (x ◇ (y ◇ z))) ◇ ((y ◇ z) ◇ z)) = (y ◇ z) := by
    exact (((congrArg (fun _t : G => ((x ◇ (x ◇ (y ◇ z))) ◇ ((y ◇ z) ◇ _t))) ((p3 y z)))).symm).trans ((p2 x (y ◇ z) ((y ◇ z) ◇ (z ◇ y))))
  have p26 (x y z : G) : (((x ◇ (x ◇ y)) ◇ y) ◇ (y ◇ z)) = (y ◇ (y ◇ z)) := by
    exact (((congrArg (fun _t : G => (((x ◇ (x ◇ y)) ◇ y) ◇ _t)) ((p3 y (y ◇ z))))).symm).trans ((p5 ((y ◇ z) ◇ y) x y z))
  have p39 (x y z : G) : ((x ◇ y) ◇ (y ◇ (y ◇ z))) = y := by
    exact ((((congrArg (fun _t : G => ((x ◇ y) ◇ (y ◇ (_t ◇ z)))) ((p3 x y)))).symm).trans ((((congrArg (fun _t : G => ((x ◇ y) ◇ (_t ◇ (((x ◇ y) ◇ ((x ◇ y) ◇ (y ◇ x))) ◇ z)))) ((p3 x y)))).symm).trans ((p8 (x ◇ y) ((x ◇ y) ◇ (y ◇ x)) z)))).trans ((p3 x y))
  have p47 (x y : G) : (((x ◇ y) ◇ x) ◇ x) = x := by
    exact (((congrArg (fun _t : G => (((x ◇ y) ◇ x) ◇ _t)) ((p39 (x ◇ y) x y)))).symm).trans ((p3 (x ◇ y) x))
  have p50 (x y z : G) : ((x ◇ (y ◇ z)) ◇ z) = (y ◇ z) := by
    exact (((congrArg (fun _t : G => ((x ◇ (y ◇ z)) ◇ _t)) ((p3 y z)))).symm).trans ((p39 x (y ◇ z) (z ◇ y)))
  have p60 (x y z : G) : ((x ◇ y) ◇ (y ◇ z)) = (y ◇ (y ◇ z)) := by
    exact (((congrArg (fun _t : G => (_t ◇ (y ◇ z))) ((p50 x x y)))).symm).trans ((p26 x y z))
  have p64 (x y : G) : (x ◇ (x ◇ (x ◇ y))) = x := by
    exact (((p60 a x (x ◇ y))).symm).trans ((p39 a x y))
  have p66 (x y z : G) : (x ◇ (y ◇ z)) = (y ◇ z) := by
    exact ((((p50 x x (y ◇ z))).symm).trans ((((congrArg (fun _t : G => ((x ◇ (x ◇ (y ◇ z))) ◇ _t)) ((p64 (y ◇ z) a)))).symm).trans ((((congrArg (fun _t : G => ((x ◇ (x ◇ (y ◇ z))) ◇ (_t ◇ ((y ◇ z) ◇ ((y ◇ z) ◇ a))))) ((p8 y z a)))).symm).trans ((((congrArg (fun _t : G => ((x ◇ (x ◇ _t)) ◇ ((y ◇ ((y ◇ z) ◇ ((y ◇ z) ◇ a))) ◇ ((y ◇ z) ◇ ((y ◇ z) ◇ a))))) ((p8 y z a)))).symm).trans ((p9 x y ((y ◇ z) ◇ ((y ◇ z) ◇ a)))))))).trans ((p8 y z a))
  have p67 (x y z : G) : ((x ◇ y) ◇ z) = (x ◇ y) := by
    exact (((p66 ((x ◇ y) ◇ z) (x ◇ y) z)).symm).trans ((((congrArg (fun _t : G => (((x ◇ y) ◇ z) ◇ _t)) ((p66 ((x ◇ y) ◇ z) (x ◇ y) z)))).symm).trans ((((congrArg (fun _t : G => (((x ◇ y) ◇ z) ◇ (((x ◇ y) ◇ z) ◇ _t))) ((p66 (x ◇ y) (x ◇ y) z)))).symm).trans ((((congrArg (fun _t : G => (((x ◇ y) ◇ z) ◇ (_t ◇ ((x ◇ y) ◇ ((x ◇ y) ◇ z))))) ((p66 x (x ◇ y) z)))).symm).trans ((((congrArg (fun _t : G => (((x ◇ y) ◇ z) ◇ ((x ◇ _t) ◇ ((x ◇ y) ◇ ((x ◇ y) ◇ z))))) ((p66 (x ◇ y) (x ◇ y) z)))).symm).trans ((((congrArg (fun _t : G => (_t ◇ ((x ◇ ((x ◇ y) ◇ ((x ◇ y) ◇ z))) ◇ ((x ◇ y) ◇ ((x ◇ y) ◇ z))))) ((p66 a (x ◇ y) z)))).symm).trans ((((congrArg (fun _t : G => ((a ◇ _t) ◇ ((x ◇ ((x ◇ y) ◇ ((x ◇ y) ◇ z))) ◇ ((x ◇ y) ◇ ((x ◇ y) ◇ z))))) ((p66 a (x ◇ y) z)))).symm).trans ((((congrArg (fun _t : G => ((a ◇ (a ◇ _t)) ◇ ((x ◇ ((x ◇ y) ◇ ((x ◇ y) ◇ z))) ◇ ((x ◇ y) ◇ ((x ◇ y) ◇ z))))) ((p66 x (x ◇ y) z)))).symm).trans ((((congrArg (fun _t : G => ((a ◇ (a ◇ (x ◇ _t))) ◇ ((x ◇ ((x ◇ y) ◇ ((x ◇ y) ◇ z))) ◇ ((x ◇ y) ◇ ((x ◇ y) ◇ z))))) ((p66 (x ◇ y) (x ◇ y) z)))).symm).trans (((p9 a x ((x ◇ y) ◇ ((x ◇ y) ◇ z)))).trans ((p8 x y z)))))))))))
  have p69 (x y : G) : (x ◇ y) = x := by
    exact (((p66 (x ◇ y) x y)).symm).trans ((((congrArg (fun _t : G => ((x ◇ y) ◇ _t)) ((p67 x y x)))).symm).trans ((((congrArg (fun _t : G => ((x ◇ y) ◇ (_t ◇ x))) ((p67 x y x)))).symm).trans ((((congrArg (fun _t : G => ((x ◇ y) ◇ ((_t ◇ x) ◇ x))) ((p67 x y x)))).symm).trans ((((congrArg (fun _t : G => (_t ◇ ((((x ◇ y) ◇ x) ◇ x) ◇ x))) ((p66 a x y)))).symm).trans ((((congrArg (fun _t : G => ((a ◇ _t) ◇ ((((x ◇ y) ◇ x) ◇ x) ◇ x))) ((p66 a x y)))).symm).trans ((((congrArg (fun _t : G => ((a ◇ (a ◇ _t)) ◇ ((((x ◇ y) ◇ x) ◇ x) ◇ x))) ((p67 x y x)))).symm).trans ((((congrArg (fun _t : G => ((a ◇ (a ◇ (_t ◇ x))) ◇ ((((x ◇ y) ◇ x) ◇ x) ◇ x))) ((p67 x y x)))).symm).trans (((p9 a ((x ◇ y) ◇ x) x)).trans ((p47 x y))))))))))
  have p70 (x y : G) : x = y := by
    exact (((((((((p69 x y)).symm).trans ((((congrArg (fun _t : G => (x ◇ _t)) ((p69 y a)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (y ◇ _t))) ((p69 a a)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (y ◇ (_t ◇ a)))) ((p69 a a)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (_t ◇ ((a ◇ a) ◇ a)))) ((p69 y a)))).symm).trans ((((congrArg (fun _t : G => (x ◇ ((y ◇ _t) ◇ ((a ◇ a) ◇ a)))) ((p69 a a)))).symm).trans ((((congrArg (fun _t : G => (x ◇ ((y ◇ (_t ◇ a)) ◇ ((a ◇ a) ◇ a)))) ((p69 a a)))).symm).trans ((((congrArg (fun _t : G => (x ◇ ((_t ◇ ((a ◇ a) ◇ a)) ◇ ((a ◇ a) ◇ a)))) ((p69 y y)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (((y ◇ _t) ◇ ((a ◇ a) ◇ a)) ◇ ((a ◇ a) ◇ a)))) ((p69 y a)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (((y ◇ (y ◇ _t)) ◇ ((a ◇ a) ◇ a)) ◇ ((a ◇ a) ◇ a)))) ((p69 a a)))).symm).trans ((((congrArg (fun _t : G => (_t ◇ (((y ◇ (y ◇ (a ◇ a))) ◇ ((a ◇ a) ◇ a)) ◇ ((a ◇ a) ◇ a)))) ((p69 x x)))).symm).trans ((((congrArg (fun _t : G => ((x ◇ _t) ◇ (((y ◇ (y ◇ (a ◇ a))) ◇ ((a ◇ a) ◇ a)) ◇ ((a ◇ a) ◇ a)))) ((p69 x a)))).symm).trans ((((congrArg (fun _t : G => ((x ◇ (x ◇ _t)) ◇ (((y ◇ (y ◇ (a ◇ a))) ◇ ((a ◇ a) ◇ a)) ◇ ((a ◇ a) ◇ a)))) ((p69 a a)))).symm).trans ((((congrArg (fun _t : G => ((x ◇ (x ◇ _t)) ◇ (((y ◇ (y ◇ (a ◇ a))) ◇ ((a ◇ a) ◇ a)) ◇ ((a ◇ a) ◇ a)))) ((p9 y a a)))).symm).trans ((p9 x (y ◇ (y ◇ (a ◇ a))) ((a ◇ a) ◇ a))))))))))))))))).trans ((congrArg (fun _t : G => ((y ◇ (y ◇ _t)) ◇ ((a ◇ a) ◇ a))) ((p69 a a))))).trans ((congrArg (fun _t : G => ((y ◇ _t) ◇ ((a ◇ a) ◇ a))) ((p69 y a))))).trans ((congrArg (fun _t : G => (_t ◇ ((a ◇ a) ◇ a))) ((p69 y y))))).trans ((congrArg (fun _t : G => (y ◇ (_t ◇ a))) ((p69 a a))))).trans ((congrArg (fun _t : G => (y ◇ _t)) ((p69 a a))))).trans ((p69 y a))
  exact (p70 a a).trans (p70 b a).symm

#print axioms finite_trivial

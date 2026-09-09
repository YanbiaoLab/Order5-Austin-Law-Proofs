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
@[reducible] def Equation21866 (G : Type _) [Magma G] : Prop := ∀ (x y z w : G), x = (y ◇ (z ◇ x)) ◇ (x ◇ (x ◇ w))

theorem finite_trivial (G : Type*) [Magma G] [Finite G] (h : Equation21866 G) : Equation2 G := by
  intro a b
  have hh : ∀ x y : G, x = (y ◇ (y ◇ x)) ◇ (x ◇ (x ◇ y)) := by
    intro x y
    exact h x y y y
  have hp := FinitePairInverse.pair_inverse G hh
  have p2 (u x y z : G) : ((x ◇ (y ◇ z)) ◇ (z ◇ (z ◇ u))) = z := by
    exact (h z x y u).symm
  have p3 (x y : G) : ((x ◇ y) ◇ ((x ◇ y) ◇ (y ◇ x))) = y := by
    exact hp x y
  have p5 (u x y z : G) : ((x ◇ y) ◇ ((y ◇ (y ◇ z)) ◇ ((y ◇ (y ◇ z)) ◇ u))) = (y ◇ (y ◇ z)) := by
    exact (((congrArg (fun _t : G => ((x ◇ _t) ◇ ((y ◇ (y ◇ z)) ◇ ((y ◇ (y ◇ z)) ◇ u)))) ((p2 z a a y)))).symm).trans ((p2 u x (a ◇ (a ◇ y)) (y ◇ (y ◇ z))))
  have p13 (x y : G) : (x ◇ (x ◇ (((y ◇ x) ◇ (x ◇ y)) ◇ (y ◇ x)))) = ((y ◇ x) ◇ (x ◇ y)) := by
    exact (((congrArg (fun _t : G => (x ◇ (_t ◇ (((y ◇ x) ◇ (x ◇ y)) ◇ (y ◇ x))))) ((p3 y x)))).symm).trans ((((congrArg (fun _t : G => (_t ◇ (((y ◇ x) ◇ ((y ◇ x) ◇ (x ◇ y))) ◇ (((y ◇ x) ◇ (x ◇ y)) ◇ (y ◇ x))))) ((p3 y x)))).symm).trans ((p3 (y ◇ x) ((y ◇ x) ◇ (x ◇ y)))))
  have p24 (x y z : G) : ((x ◇ y) ◇ (y ◇ z)) = (y ◇ (y ◇ z)) := by
    exact (((congrArg (fun _t : G => ((x ◇ y) ◇ _t)) ((p3 y (y ◇ z))))).symm).trans ((p5 ((y ◇ z) ◇ y) x y z))
  have p31 (x y : G) : (x ◇ (x ◇ ((x ◇ (x ◇ y)) ◇ (y ◇ x)))) = (x ◇ (x ◇ y)) := by
    exact ((((congrArg (fun _t : G => (x ◇ (x ◇ (_t ◇ (y ◇ x))))) ((p24 y x y)))).symm).trans ((p13 x y))).trans ((p24 y x y))
  have p32 (x y : G) : (x ◇ (x ◇ (x ◇ y))) = x := by
    exact (((p24 y x (x ◇ y))).symm).trans ((((congrArg (fun _t : G => ((y ◇ x) ◇ _t)) ((p24 y x y)))).symm).trans ((p3 y x)))
  have p35 (x y z : G) : ((x ◇ (y ◇ z)) ◇ z) = z := by
    exact (((congrArg (fun _t : G => ((x ◇ (y ◇ z)) ◇ _t)) ((p32 z a)))).symm).trans ((p2 (z ◇ a) x y z))
  have p36 (x y z : G) : (x ◇ (y ◇ z)) = z := by
    exact ((((p35 x y z)).symm).trans ((((congrArg (fun _t : G => ((x ◇ (y ◇ z)) ◇ _t)) ((p35 x y z)))).symm).trans ((((congrArg (fun _t : G => ((x ◇ (y ◇ z)) ◇ ((x ◇ (y ◇ z)) ◇ _t))) ((p2 a x y z)))).symm).trans ((p32 (x ◇ (y ◇ z)) (z ◇ (z ◇ a))))))).symm
  have p38 (x y : G) : x = y := by
    exact ((((p36 x x x)).symm).trans ((((congrArg (fun _t : G => (x ◇ (x ◇ _t))) ((p36 y y x)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (x ◇ (_t ◇ (y ◇ x))))) ((p36 x x y)))).symm).trans ((p31 x y))))).trans ((p36 x x y))
  exact (p38 a a).trans (p38 b a).symm

#print axioms finite_trivial

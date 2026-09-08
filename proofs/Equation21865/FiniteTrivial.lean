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
@[reducible] def Equation21865 (G : Type _) [Magma G] : Prop := ∀ (x y z : G), x = (y ◇ (z ◇ x)) ◇ (x ◇ (x ◇ z))

theorem finite_trivial (G : Type*) [Magma G] [Finite G] (h : Equation21865 G) : Equation2 G := by
  intro a b
  have hh : ∀ x y : G, x = (y ◇ (y ◇ x)) ◇ (x ◇ (x ◇ y)) := by
    intro x y
    exact h x y y
  have hp := FinitePairInverse.pair_inverse G hh
  have p2 (x y z : G) : ((x ◇ (y ◇ z)) ◇ (z ◇ (z ◇ y))) = z := by
    exact (h z x y).symm
  have p3 (x y : G) : ((x ◇ y) ◇ ((x ◇ y) ◇ (y ◇ x))) = y := by
    exact hp x y
  have p5 (u x y z : G) : ((x ◇ y) ◇ ((y ◇ (y ◇ z)) ◇ ((y ◇ (y ◇ z)) ◇ (u ◇ (z ◇ y))))) = (y ◇ (y ◇ z)) := by
    exact (((congrArg (fun _t : G => ((x ◇ _t) ◇ ((y ◇ (y ◇ z)) ◇ ((y ◇ (y ◇ z)) ◇ (u ◇ (z ◇ y)))))) ((p2 u z y)))).symm).trans ((p2 x (u ◇ (z ◇ y)) (y ◇ (y ◇ z))))
  have p6 (x y : G) : (x ◇ ((x ◇ y) ◇ ((x ◇ y) ◇ x))) = (x ◇ y) := by
    exact (((congrArg (fun _t : G => (_t ◇ ((x ◇ y) ◇ ((x ◇ y) ◇ x)))) ((p2 a y x)))).symm).trans ((p2 (a ◇ (y ◇ x)) x (x ◇ y)))
  have p7 (u x y z : G) : ((x ◇ ((y ◇ (y ◇ z)) ◇ (u ◇ (z ◇ y)))) ◇ ((u ◇ (z ◇ y)) ◇ y)) = (u ◇ (z ◇ y)) := by
    exact (((congrArg (fun _t : G => ((x ◇ ((y ◇ (y ◇ z)) ◇ (u ◇ (z ◇ y)))) ◇ ((u ◇ (z ◇ y)) ◇ _t))) ((p2 u z y)))).symm).trans ((p2 x (y ◇ (y ◇ z)) (u ◇ (z ◇ y))))
  have p10 (x y z : G) : ((x ◇ ((y ◇ z) ◇ (z ◇ y))) ◇ y) = (z ◇ y) := by
    exact (((congrArg (fun _t : G => ((x ◇ ((y ◇ z) ◇ (z ◇ y))) ◇ _t)) ((p3 z y)))).symm).trans ((p2 x (y ◇ z) (z ◇ y)))
  have p20 (x y z : G) : ((x ◇ y) ◇ ((y ◇ (y ◇ z)) ◇ z)) = (y ◇ (y ◇ z)) := by
    exact (((congrArg (fun _t : G => ((x ◇ y) ◇ ((y ◇ (y ◇ z)) ◇ _t))) ((p2 y y z)))).symm).trans ((p5 z x y z))
  have p33 (x y : G) : ((x ◇ y) ◇ (y ◇ (y ◇ (x ◇ y)))) = y := by
    exact ((((congrArg (fun _t : G => ((x ◇ y) ◇ (y ◇ (_t ◇ (x ◇ y))))) ((p3 x y)))).symm).trans ((((congrArg (fun _t : G => ((x ◇ y) ◇ (_t ◇ (((x ◇ y) ◇ ((x ◇ y) ◇ (y ◇ x))) ◇ (x ◇ y))))) ((p3 x y)))).symm).trans ((p6 (x ◇ y) ((x ◇ y) ◇ (y ◇ x)))))).trans ((p3 x y))
  have p44 (u x y z : G) : ((x ◇ (y ◇ z)) ◇ (((y ◇ z) ◇ z) ◇ (((y ◇ z) ◇ z) ◇ (u ◇ ((z ◇ (z ◇ (y ◇ z))) ◇ (y ◇ z)))))) = ((y ◇ z) ◇ z) := by
    exact ((((congrArg (fun _t : G => ((x ◇ (y ◇ z)) ◇ (((y ◇ z) ◇ z) ◇ (((y ◇ z) ◇ _t) ◇ (u ◇ ((z ◇ (z ◇ (y ◇ z))) ◇ (y ◇ z))))))) ((p33 y z)))).symm).trans ((((congrArg (fun _t : G => ((x ◇ (y ◇ z)) ◇ (((y ◇ z) ◇ _t) ◇ (((y ◇ z) ◇ ((y ◇ z) ◇ (z ◇ (z ◇ (y ◇ z))))) ◇ (u ◇ ((z ◇ (z ◇ (y ◇ z))) ◇ (y ◇ z))))))) ((p33 y z)))).symm).trans ((p5 u x (y ◇ z) (z ◇ (z ◇ (y ◇ z))))))).trans ((congrArg (fun _t : G => ((y ◇ z) ◇ _t)) ((p33 y z))))
  have p61 (x y z : G) : ((x ◇ (((y ◇ (y ◇ (z ◇ y))) ◇ (z ◇ y)) ◇ y)) ◇ (y ◇ (y ◇ (z ◇ y)))) = y := by
    exact ((((congrArg (fun _t : G => ((x ◇ (((y ◇ (y ◇ (z ◇ y))) ◇ (z ◇ y)) ◇ _t)) ◇ (y ◇ (y ◇ (z ◇ y))))) ((p33 z y)))).symm).trans ((p10 x (y ◇ (y ◇ (z ◇ y))) (z ◇ y)))).trans ((p33 z y))
  have p71 (x y z : G) : ((x ◇ (y ◇ z)) ◇ (((y ◇ z) ◇ z) ◇ ((y ◇ z) ◇ (z ◇ y)))) = ((y ◇ z) ◇ z) := by
    exact ((((congrArg (fun _t : G => ((x ◇ (y ◇ z)) ◇ (((y ◇ z) ◇ _t) ◇ ((y ◇ z) ◇ (z ◇ y))))) ((p3 y z)))).symm).trans ((p20 x (y ◇ z) ((y ◇ z) ◇ (z ◇ y))))).trans ((congrArg (fun _t : G => ((y ◇ z) ◇ _t)) ((p3 y z))))
  have p79 (x y : G) : (((x ◇ (x ◇ (y ◇ x))) ◇ (y ◇ x)) ◇ x) = (y ◇ x) := by
    exact (((congrArg (fun _t : G => (((x ◇ (x ◇ (y ◇ x))) ◇ (y ◇ x)) ◇ _t)) ((p33 y x)))).symm).trans ((((congrArg (fun _t : G => (((x ◇ (x ◇ (y ◇ x))) ◇ (y ◇ x)) ◇ ((y ◇ x) ◇ _t))) ((p20 y x (y ◇ x))))).symm).trans ((p33 (x ◇ (x ◇ (y ◇ x))) (y ◇ x))))
  have p86 (x y z : G) : ((x ◇ (y ◇ z)) ◇ (z ◇ (z ◇ (y ◇ z)))) = z := by
    exact (((congrArg (fun _t : G => ((x ◇ _t) ◇ (z ◇ (z ◇ (y ◇ z))))) ((p79 z y)))).symm).trans ((p61 x z y))
  have p101 (u x y z : G) : ((x ◇ (((y ◇ z) ◇ z) ◇ (u ◇ ((z ◇ (z ◇ (y ◇ z))) ◇ (y ◇ z))))) ◇ ((u ◇ ((z ◇ (z ◇ (y ◇ z))) ◇ (y ◇ z))) ◇ (y ◇ z))) = (u ◇ ((z ◇ (z ◇ (y ◇ z))) ◇ (y ◇ z))) := by
    exact (((congrArg (fun _t : G => ((x ◇ (((y ◇ z) ◇ _t) ◇ (u ◇ ((z ◇ (z ◇ (y ◇ z))) ◇ (y ◇ z))))) ◇ ((u ◇ ((z ◇ (z ◇ (y ◇ z))) ◇ (y ◇ z))) ◇ (y ◇ z)))) ((p33 y z)))).symm).trans ((p7 u x (y ◇ z) (z ◇ (z ◇ (y ◇ z)))))
  have p125 (x y : G) : ((x ◇ (x ◇ (y ◇ x))) ◇ ((x ◇ (y ◇ x)) ◇ x)) = (x ◇ (y ◇ x)) := by
    exact (((congrArg (fun _t : G => ((x ◇ (x ◇ (y ◇ x))) ◇ ((x ◇ (y ◇ x)) ◇ _t))) ((p86 x y x)))).symm).trans ((p33 x (x ◇ (y ◇ x))))
  have p126 (x y : G) : (x ◇ ((x ◇ (y ◇ x)) ◇ x)) = (x ◇ (y ◇ x)) := by
    exact (((congrArg (fun _t : G => (x ◇ ((x ◇ (y ◇ x)) ◇ _t))) ((p86 x y x)))).symm).trans ((((congrArg (fun _t : G => (_t ◇ ((x ◇ (y ◇ x)) ◇ ((x ◇ (y ◇ x)) ◇ (x ◇ (x ◇ (y ◇ x))))))) ((p33 y x)))).symm).trans ((p86 (y ◇ x) x (x ◇ (y ◇ x)))))
  have p129 (u x y z : G) : ((x ◇ (y ◇ (z ◇ u))) ◇ (((y ◇ (z ◇ u)) ◇ u) ◇ (u ◇ (u ◇ (z ◇ u))))) = ((y ◇ (z ◇ u)) ◇ u) := by
    exact ((((congrArg (fun _t : G => ((x ◇ (y ◇ (z ◇ u))) ◇ (((y ◇ (z ◇ u)) ◇ _t) ◇ (u ◇ (u ◇ (z ◇ u)))))) ((p86 y z u)))).symm).trans ((p20 x (y ◇ (z ◇ u)) (u ◇ (u ◇ (z ◇ u)))))).trans ((congrArg (fun _t : G => ((y ◇ (z ◇ u)) ◇ _t)) ((p86 y z u))))
  have p144 (x : G) : ((x ◇ x) ◇ (x ◇ (x ◇ x))) = x := by
    exact ((((congrArg (fun _t : G => ((x ◇ x) ◇ (_t ◇ (x ◇ x)))) ((p3 x x)))).symm).trans ((p126 (x ◇ x) (x ◇ x)))).trans ((p3 x x))
  have p147 (x y : G) : (((x ◇ (y ◇ x)) ◇ x) ◇ (x ◇ (x ◇ (y ◇ x)))) = x := by
    exact (((congrArg (fun _t : G => (((x ◇ (y ◇ x)) ◇ x) ◇ (x ◇ _t))) ((p126 x y)))).symm).trans ((p33 (x ◇ (y ◇ x)) x))
  have p148 (x y z : G) : ((x ◇ ((y ◇ (z ◇ y)) ◇ (((y ◇ (z ◇ y)) ◇ y) ◇ y))) ◇ y) = (((y ◇ (z ◇ y)) ◇ y) ◇ y) := by
    exact (((congrArg (fun _t : G => ((x ◇ (_t ◇ (((y ◇ (z ◇ y)) ◇ y) ◇ y))) ◇ y)) ((p126 y z)))).symm).trans ((p10 x y ((y ◇ (z ◇ y)) ◇ y)))
  have p150 (x y z : G) : ((x ◇ y) ◇ (y ◇ (z ◇ y))) = (y ◇ (y ◇ (z ◇ y))) := by
    exact ((((congrArg (fun _t : G => ((x ◇ y) ◇ _t)) ((p125 y z)))).symm).trans ((((congrArg (fun _t : G => ((x ◇ y) ◇ ((y ◇ _t) ◇ ((y ◇ (z ◇ y)) ◇ y)))) ((p126 y z)))).symm).trans ((p20 x y ((y ◇ (z ◇ y)) ◇ y))))).trans ((congrArg (fun _t : G => (y ◇ _t)) ((p126 y z))))
  have p155 (x y z : G) : ((x ◇ (y ◇ (z ◇ y))) ◇ y) = ((y ◇ (z ◇ y)) ◇ y) := by
    exact (((congrArg (fun _t : G => ((x ◇ (y ◇ (z ◇ y))) ◇ _t)) ((p147 y z)))).symm).trans ((((congrArg (fun _t : G => ((x ◇ (y ◇ (z ◇ y))) ◇ (((y ◇ (z ◇ y)) ◇ y) ◇ _t))) ((p150 (y ◇ (z ◇ y)) y z)))).symm).trans ((((congrArg (fun _t : G => ((x ◇ (y ◇ (z ◇ y))) ◇ (((y ◇ (z ◇ y)) ◇ y) ◇ (((y ◇ (z ◇ y)) ◇ y) ◇ _t)))) ((p126 y z)))).symm).trans ((((congrArg (fun _t : G => ((x ◇ _t) ◇ (((y ◇ (z ◇ y)) ◇ y) ◇ (((y ◇ (z ◇ y)) ◇ y) ◇ (y ◇ ((y ◇ (z ◇ y)) ◇ y)))))) ((p126 y z)))).symm).trans ((p86 x y ((y ◇ (z ◇ y)) ◇ y))))))
  have p157 (x : G) : (x ◇ (x ◇ (x ◇ x))) = x := by
    exact (((p150 x x x)).symm).trans ((p144 x))
  have p162 (x : G) : (x ◇ (x ◇ x)) = x := by
    exact ((((p157 x)).symm).trans ((((congrArg (fun _t : G => (x ◇ _t)) ((p126 x x)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (_t ◇ ((x ◇ (x ◇ x)) ◇ x)))) ((p157 x)))).symm).trans ((((congrArg (fun _t : G => (_t ◇ ((x ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (x ◇ x)) ◇ x)))) ((p157 x)))).symm).trans ((p3 x (x ◇ (x ◇ x)))))))).symm
  have p163 (x : G) : ((x ◇ x) ◇ x) = x := by
    exact ((((congrArg (fun _t : G => ((x ◇ x) ◇ _t)) ((p162 x)))).symm).trans ((((congrArg (fun _t : G => ((x ◇ x) ◇ (x ◇ (_t ◇ x)))) ((p162 x)))).symm).trans ((((congrArg (fun _t : G => ((x ◇ _t) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x)))) ((p162 x)))).symm).trans ((((congrArg (fun _t : G => ((x ◇ (x ◇ (x ◇ x))) ◇ (_t ◇ ((x ◇ (x ◇ x)) ◇ x)))) ((p157 x)))).symm).trans ((p3 x (x ◇ (x ◇ x)))))))).trans ((p162 x))
  have p164 (x : G) : (x ◇ x) = x := by
    exact ((((p163 x)).symm).trans ((((congrArg (fun _t : G => ((x ◇ x) ◇ _t)) ((p3 x x)))).symm).trans ((p157 (x ◇ x))))).symm
  have p166 (x y z : G) : ((x ◇ y) ◇ (y ◇ (y ◇ (z ◇ y)))) = y := by
    exact (((((((congrArg (fun _t : G => ((x ◇ y) ◇ (y ◇ (y ◇ (z ◇ _t))))) ((p164 y)))).symm).trans ((((congrArg (fun _t : G => ((x ◇ y) ◇ (y ◇ (y ◇ (z ◇ (_t ◇ y)))))) ((p164 y)))).symm).trans ((((congrArg (fun _t : G => ((x ◇ y) ◇ (y ◇ (y ◇ (z ◇ ((y ◇ _t) ◇ y)))))) ((p164 y)))).symm).trans ((((congrArg (fun _t : G => ((x ◇ y) ◇ (y ◇ (_t ◇ (z ◇ ((y ◇ (y ◇ y)) ◇ y)))))) ((p164 y)))).symm).trans ((((congrArg (fun _t : G => ((x ◇ y) ◇ (y ◇ ((y ◇ _t) ◇ (z ◇ ((y ◇ (y ◇ y)) ◇ y)))))) ((p164 y)))).symm).trans ((((congrArg (fun _t : G => ((x ◇ y) ◇ (y ◇ ((y ◇ (y ◇ _t)) ◇ (z ◇ ((y ◇ (y ◇ y)) ◇ y)))))) ((p164 y)))).symm).trans ((((congrArg (fun _t : G => ((x ◇ y) ◇ (y ◇ ((y ◇ (y ◇ (y ◇ _t))) ◇ (z ◇ ((y ◇ (y ◇ y)) ◇ y)))))) ((p164 y)))).symm).trans ((((congrArg (fun _t : G => ((x ◇ y) ◇ (_t ◇ ((y ◇ (y ◇ (y ◇ (y ◇ y)))) ◇ (z ◇ ((y ◇ (y ◇ y)) ◇ y)))))) ((p164 y)))).symm).trans ((((congrArg (fun _t : G => ((x ◇ y) ◇ ((y ◇ _t) ◇ ((y ◇ (y ◇ (y ◇ (y ◇ y)))) ◇ (z ◇ ((y ◇ (y ◇ y)) ◇ y)))))) ((p157 y)))).symm).trans ((p5 z x y (y ◇ (y ◇ y))))))))))))).trans ((congrArg (fun _t : G => (y ◇ (y ◇ (y ◇ _t)))) ((p164 y))))).trans ((congrArg (fun _t : G => (y ◇ (y ◇ _t))) ((p164 y))))).trans ((congrArg (fun _t : G => (y ◇ _t)) ((p164 y))))).trans ((p164 y))
  have p167 (x y : G) : ((x ◇ y) ◇ y) = y := by
    exact (((((((congrArg (fun _t : G => ((x ◇ y) ◇ _t)) ((p164 y)))).symm).trans ((((congrArg (fun _t : G => ((x ◇ y) ◇ (y ◇ _t))) ((p164 y)))).symm).trans ((((congrArg (fun _t : G => ((x ◇ y) ◇ (y ◇ (_t ◇ y)))) ((p164 y)))).symm).trans ((((congrArg (fun _t : G => ((x ◇ y) ◇ (y ◇ ((y ◇ _t) ◇ y)))) ((p164 y)))).symm).trans ((((congrArg (fun _t : G => ((x ◇ y) ◇ (y ◇ ((y ◇ (_t ◇ y)) ◇ y)))) ((p164 y)))).symm).trans ((((congrArg (fun _t : G => ((x ◇ y) ◇ (y ◇ ((_t ◇ ((y ◇ y) ◇ y)) ◇ y)))) ((p164 y)))).symm).trans ((((congrArg (fun _t : G => ((x ◇ y) ◇ (_t ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y)))) ((p164 y)))).symm).trans ((((congrArg (fun _t : G => ((x ◇ y) ◇ ((y ◇ _t) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y)))) ((p164 y)))).symm).trans ((((congrArg (fun _t : G => ((x ◇ y) ◇ ((y ◇ (_t ◇ y)) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y)))) ((p164 y)))).symm).trans ((((congrArg (fun _t : G => ((x ◇ y) ◇ ((_t ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y)))) ((p164 y)))).symm).trans ((((congrArg (fun _t : G => ((x ◇ _t) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y)))) ((p164 y)))).symm).trans ((((congrArg (fun _t : G => ((x ◇ (y ◇ y)) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ _t)))) ((p157 y)))).symm).trans ((p5 y x (y ◇ y) y)))))))))))))).trans ((congrArg (fun _t : G => (_t ◇ ((y ◇ y) ◇ y))) ((p164 y))))).trans ((congrArg (fun _t : G => (y ◇ (_t ◇ y))) ((p164 y))))).trans ((congrArg (fun _t : G => (y ◇ _t)) ((p164 y))))).trans ((p164 y))
  have p169 (x y : G) : ((x ◇ (y ◇ x)) ◇ x) = (y ◇ x) := by
    exact ((((((p155 a x y)).symm).trans ((((congrArg (fun _t : G => ((a ◇ (x ◇ (y ◇ x))) ◇ _t)) ((p167 y x)))).symm).trans ((((congrArg (fun _t : G => ((a ◇ (x ◇ (y ◇ x))) ◇ ((y ◇ _t) ◇ x))) ((p164 x)))).symm).trans ((((congrArg (fun _t : G => ((a ◇ (x ◇ (y ◇ x))) ◇ ((y ◇ (_t ◇ x)) ◇ x))) ((p164 x)))).symm).trans ((((congrArg (fun _t : G => ((a ◇ (x ◇ (y ◇ x))) ◇ ((y ◇ ((x ◇ _t) ◇ x)) ◇ x))) ((p164 x)))).symm).trans ((((congrArg (fun _t : G => ((a ◇ (x ◇ (y ◇ _t))) ◇ ((y ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x))) ((p164 x)))).symm).trans ((((congrArg (fun _t : G => ((a ◇ (x ◇ (y ◇ (_t ◇ x)))) ◇ ((y ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x))) ((p164 x)))).symm).trans ((((congrArg (fun _t : G => ((a ◇ (x ◇ (y ◇ ((x ◇ _t) ◇ x)))) ◇ ((y ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x))) ((p164 x)))).symm).trans ((((congrArg (fun _t : G => ((a ◇ (_t ◇ (y ◇ ((x ◇ (x ◇ x)) ◇ x)))) ◇ ((y ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x))) ((p164 x)))).symm).trans ((((congrArg (fun _t : G => ((a ◇ ((x ◇ _t) ◇ (y ◇ ((x ◇ (x ◇ x)) ◇ x)))) ◇ ((y ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x))) ((p157 x)))).symm).trans ((p7 y a x (x ◇ (x ◇ x)))))))))))))).trans ((congrArg (fun _t : G => (y ◇ ((x ◇ _t) ◇ x))) ((p164 x))))).trans ((congrArg (fun _t : G => (y ◇ (_t ◇ x))) ((p164 x))))).trans ((congrArg (fun _t : G => (y ◇ _t)) ((p164 x))))
  have p171 (u x y z : G) : ((x ◇ (y ◇ (z ◇ u))) ◇ u) = ((y ◇ (z ◇ u)) ◇ u) := by
    exact (((congrArg (fun _t : G => ((x ◇ (y ◇ (z ◇ u))) ◇ _t)) ((p166 (y ◇ (z ◇ u)) u z)))).symm).trans ((p129 u x y z))
  have p176 (x y z : G) : ((x ◇ (y ◇ z)) ◇ z) = z := by
    exact (((((congrArg (fun _t : G => ((x ◇ _t) ◇ z)) ((p169 z y)))).symm).trans ((((congrArg (fun _t : G => ((x ◇ ((z ◇ (y ◇ z)) ◇ _t)) ◇ z)) ((p167 y z)))).symm).trans ((((congrArg (fun _t : G => ((x ◇ ((z ◇ (y ◇ z)) ◇ (_t ◇ z))) ◇ z)) ((p169 z y)))).symm).trans ((p148 x z y))))).trans ((congrArg (fun _t : G => (_t ◇ z)) ((p169 z y))))).trans ((p167 y z))
  have p179 (x y z : G) : (x ◇ (y ◇ z)) = (y ◇ z) := by
    exact (((((p176 z x (y ◇ z))).symm).trans ((((p171 (y ◇ z) a z x)).symm).trans ((((congrArg (fun _t : G => ((a ◇ (z ◇ (x ◇ (y ◇ z)))) ◇ _t)) ((p167 x (y ◇ z))))).symm).trans ((((congrArg (fun _t : G => ((a ◇ (z ◇ (x ◇ (y ◇ z)))) ◇ ((x ◇ _t) ◇ (y ◇ z)))) ((p176 z z (y ◇ z))))).symm).trans ((((congrArg (fun _t : G => ((a ◇ (z ◇ (x ◇ _t))) ◇ ((x ◇ ((z ◇ (z ◇ (y ◇ z))) ◇ (y ◇ z))) ◇ (y ◇ z)))) ((p176 z z (y ◇ z))))).symm).trans ((((congrArg (fun _t : G => ((a ◇ (_t ◇ (x ◇ ((z ◇ (z ◇ (y ◇ z))) ◇ (y ◇ z))))) ◇ ((x ◇ ((z ◇ (z ◇ (y ◇ z))) ◇ (y ◇ z))) ◇ (y ◇ z)))) ((p167 y z)))).symm).trans ((p101 x a y z)))))))).trans ((congrArg (fun _t : G => (x ◇ _t)) ((p176 z z (y ◇ z)))))).symm
  have p180 (x y : G) : (x ◇ y) = x := by
    exact ((((p179 (y ◇ x) x y)).symm).trans ((((congrArg (fun _t : G => ((y ◇ x) ◇ _t)) ((p179 x x y)))).symm).trans ((((congrArg (fun _t : G => ((y ◇ x) ◇ (x ◇ _t))) ((p179 (y ◇ x) x y)))).symm).trans ((((congrArg (fun _t : G => ((y ◇ x) ◇ (_t ◇ ((y ◇ x) ◇ (x ◇ y))))) ((p167 y x)))).symm).trans ((((congrArg (fun _t : G => (_t ◇ (((y ◇ x) ◇ x) ◇ ((y ◇ x) ◇ (x ◇ y))))) ((p179 a y x)))).symm).trans ((p71 a y x))))))).trans ((p167 y x))
  have p181 (x y : G) : x = y := by
    exact (((((p180 x y)).symm).trans ((((congrArg (fun _t : G => (x ◇ _t)) ((p164 y)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (y ◇ _t))) ((p180 y a)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (y ◇ (y ◇ _t)))) ((p180 a a)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (y ◇ (y ◇ (a ◇ _t))))) ((p180 a y)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (y ◇ (y ◇ (a ◇ (a ◇ _t)))))) ((p180 y a)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (y ◇ (y ◇ (a ◇ (_t ◇ (y ◇ a))))))) ((p164 a)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (y ◇ (y ◇ (a ◇ ((a ◇ _t) ◇ (y ◇ a))))))) ((p180 a y)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (y ◇ (y ◇ (a ◇ ((a ◇ (a ◇ _t)) ◇ (y ◇ a))))))) ((p180 y a)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (y ◇ (_t ◇ (a ◇ ((a ◇ (a ◇ (y ◇ a))) ◇ (y ◇ a))))))) ((p180 y a)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (y ◇ ((_t ◇ a) ◇ (a ◇ ((a ◇ (a ◇ (y ◇ a))) ◇ (y ◇ a))))))) ((p180 y a)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (_t ◇ (((y ◇ a) ◇ a) ◇ (a ◇ ((a ◇ (a ◇ (y ◇ a))) ◇ (y ◇ a))))))) ((p180 y a)))).symm).trans ((((congrArg (fun _t : G => (x ◇ ((_t ◇ a) ◇ (((y ◇ a) ◇ a) ◇ (a ◇ ((a ◇ (a ◇ (y ◇ a))) ◇ (y ◇ a))))))) ((p180 y a)))).symm).trans ((((congrArg (fun _t : G => (_t ◇ (((y ◇ a) ◇ a) ◇ (((y ◇ a) ◇ a) ◇ (a ◇ ((a ◇ (a ◇ (y ◇ a))) ◇ (y ◇ a))))))) ((p180 x y)))).symm).trans ((((congrArg (fun _t : G => ((x ◇ _t) ◇ (((y ◇ a) ◇ a) ◇ (((y ◇ a) ◇ a) ◇ (a ◇ ((a ◇ (a ◇ (y ◇ a))) ◇ (y ◇ a))))))) ((p180 y a)))).symm).trans ((p44 a x y a))))))))))))))))).trans ((congrArg (fun _t : G => (_t ◇ a)) ((p180 y a))))).trans ((p180 y a))
  exact (p181 a a).trans (p181 b a).symm

#print axioms finite_trivial

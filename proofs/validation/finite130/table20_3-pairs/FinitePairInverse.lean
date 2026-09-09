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

#print axioms FinitePairInverse.pair_inverse
#print axioms FinitePairInverse.square_bijective
#print axioms FinitePairInverse.commutes_only_when_equal

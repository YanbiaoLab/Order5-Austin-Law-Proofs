import Mathlib.Data.Fintype.Card
import JudgeMagma.Magma

@[reducible] def Equation2 (G : Type _) [Magma G] : Prop := ∀ (x y : G), x = y
@[reducible] def Equation22446 (G : Type _) [Magma G] : Prop := ∀ (x y z : G), x = (y ◇ (x ◇ x)) ◇ ((x ◇ z) ◇ z)

theorem square_injective (G : Type*) [Magma G] (h : Equation22446 G) :
    Function.Injective (fun x : G => x ◇ x) := by
  intro b c ht
  let a : G := b
  have p2 (x y z : G) : ((x ◇ (y ◇ y)) ◇ ((y ◇ z) ◇ z)) = y := by
    exact (h y x z).symm
  have p3 : (b ◇ b) = (c ◇ c) := by
    exact ht
  have p4 : (c ◇ c) = (b ◇ b) := by
    exact ((p3)).symm
  have p6 (x y z : G) : ((x ◇ y) ◇ ((((y ◇ (y ◇ y)) ◇ (y ◇ y)) ◇ z) ◇ z)) = ((y ◇ (y ◇ y)) ◇ (y ◇ y)) := by
    exact (((congrArg (fun _t : G => ((x ◇ _t) ◇ ((((y ◇ (y ◇ y)) ◇ (y ◇ y)) ◇ z) ◇ z))) ((p2 (y ◇ (y ◇ y)) y (y ◇ y))))).symm).trans ((p2 x ((y ◇ (y ◇ y)) ◇ (y ◇ y)) z))
  have p8 (x y : G) : ((x ◇ (b ◇ b)) ◇ ((c ◇ y) ◇ y)) = c := by
    exact (((congrArg (fun _t : G => ((x ◇ _t) ◇ ((c ◇ y) ◇ y))) ((p4)))).symm).trans ((p2 x c y))
  have p13 (x y z : G) : ((x ◇ (x ◇ x)) ◇ (x ◇ x)) = ((y ◇ x) ◇ (x ◇ ((x ◇ z) ◇ z))) := by
    exact ((((congrArg (fun _t : G => ((y ◇ x) ◇ (_t ◇ ((x ◇ z) ◇ z)))) ((p2 (x ◇ (x ◇ x)) x z)))).symm).trans ((p6 y x ((x ◇ z) ◇ z)))).symm
  have p20 (x y : G) : ((x ◇ b) ◇ (c ◇ ((c ◇ y) ◇ y))) = ((b ◇ (b ◇ b)) ◇ (b ◇ b)) := by
    exact (((congrArg (fun _t : G => ((x ◇ b) ◇ (_t ◇ ((c ◇ y) ◇ y)))) ((p8 (b ◇ (b ◇ b)) y)))).symm).trans ((p6 x b ((c ◇ y) ◇ y)))
  have p31 (x y : G) : ((c ◇ (b ◇ b)) ◇ (b ◇ b)) = ((x ◇ c) ◇ (c ◇ ((c ◇ y) ◇ y))) := by
    exact (((congrArg (fun _t : G => ((c ◇ (b ◇ b)) ◇ _t)) ((p4)))).symm).trans ((((congrArg (fun _t : G => ((c ◇ _t) ◇ (c ◇ c))) ((p4)))).symm).trans ((p13 c x y)))
  have p32 : ((c ◇ (b ◇ b)) ◇ (b ◇ b)) = ((b ◇ (b ◇ b)) ◇ (b ◇ b)) := by
    exact ((((congrArg (fun _t : G => ((c ◇ (b ◇ b)) ◇ _t)) ((p4)))).symm).trans ((((congrArg (fun _t : G => ((c ◇ _t) ◇ (c ◇ c))) ((p4)))).symm).trans (((p13 c c a)).trans ((congrArg (fun _t : G => (_t ◇ (c ◇ ((c ◇ a) ◇ a)))) ((p4))))))).trans ((p20 b a))
  have p42 (x y z : G) : ((x ◇ (b ◇ b)) ◇ ((y ◇ c) ◇ (c ◇ ((c ◇ z) ◇ z)))) = c := by
    exact (((congrArg (fun _t : G => ((x ◇ (b ◇ b)) ◇ _t)) ((p13 c y z)))).symm).trans ((p8 x (c ◇ c)))
  have p55 (x y : G) : ((x ◇ c) ◇ (c ◇ ((c ◇ y) ◇ y))) = ((b ◇ (b ◇ b)) ◇ (b ◇ b)) := by
    exact ((((p32)).symm).trans ((p31 x y))).symm
  have p58 : c = b := by
    exact ((((p2 a b (b ◇ b))).symm).trans ((((congrArg (fun _t : G => ((a ◇ (b ◇ b)) ◇ _t)) ((p55 a a)))).symm).trans ((p42 a a a)))).symm
  exact p58.symm

theorem square_bijective (G : Type*) [Magma G] [Finite G] (h : Equation22446 G) :
    Function.Bijective (fun x : G => x ◇ x) :=
  ⟨square_injective G h, Finite.injective_iff_surjective.mp (square_injective G h)⟩

#print axioms square_injective
#print axioms square_bijective

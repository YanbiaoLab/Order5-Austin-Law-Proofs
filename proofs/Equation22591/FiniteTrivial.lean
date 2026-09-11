/- Every finite model of Equation22446 is trivial. The proof uses a finite
incidence-triple rotation and its explicitly proved injectivity. -/
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finite.Prod
import JudgeMagma.Magma

@[reducible] def Equation2 (G : Type _) [Magma G] : Prop := ∀ x y : G, x = y
@[reducible] def Equation22446 (G : Type _) [Magma G] : Prop :=
  ∀ x y z : G, x = (y ◇ (x ◇ x)) ◇ ((x ◇ z) ◇ z)

namespace Equation22446Finite

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

theorem square_inverse_structure (G : Type*) [Magma G] (h : Equation22446 G) :
    let S : G → G := fun x => x ◇ x
    let Q : G → G := fun x => (x ◇ S x) ◇ S x
    (∀ x, S (Q x) = x) ∧ (∀ x, Q (S x) = x) ∧
    (∀ x y, (y ◇ S x) ◇ Q x = x) ∧
    (∀ x, S (S (S x)) ◇ x = S x) := by
  intro S Q
  have sq (x : G) : S (Q x) = x := (h x (x ◇ S x) (S x)).symm
  have qs (x : G) : Q (S x) = x := square_injective G h (sq (S x))
  have col (x y : G) : (y ◇ S x) ◇ Q x = x := (h x y (S x)).symm
  refine ⟨sq, qs, col, ?_⟩
  intro x
  have hh := col (S x) (S (S x))
  change S (S (S x)) ◇ Q (S x) = S x at hh
  rwa [qs x] at hh

theorem square_period_three (G : Type*) [Magma G] (h : Equation22446 G) :
    ∀ x : G, ((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x)) = x := by
  let S : G → G := fun x => x ◇ x
  let Q : G → G := fun x => (x ◇ S x) ◇ S x
  obtain ⟨sq, qs, col, orbit⟩ := square_inverse_structure G h
  change (∀ x, S (Q x) = x) at sq
  change (∀ x, Q (S x) = x) at qs
  change (∀ x y, (y ◇ S x) ◇ Q x = x) at col
  change (∀ x, S (S (S x)) ◇ x = S x) at orbit
  intro x
  change S (S (S x)) = x
  have step (y : G) : (y ◇ S (S (S (S x)))) ◇ (S x ◇ x) = S (S (S x)) := by
    have hh := (h (S (S (S x))) y x).symm
    change (y ◇ S (S (S (S x)))) ◇ ((S (S (S x)) ◇ x) ◇ x) = S (S (S x)) at hh
    rwa [orbit x] at hh
  have hh := step (S (S (S x)) ◇ S (S (S (S x))))
  change Q (S (S (S x))) ◇ (S x ◇ x) = S (S (S x)) at hh
  rw [qs (S (S x))] at hh
  exact hh.symm.trans (h x (S x) x).symm

theorem equation2_of_idempotent (G : Type*) [Magma G] (h : Equation22446 G)
    (c : G) (hc : c ◇ c = c) : Equation2 G := by
  intro a b
  have p2 (x y z : G) : ((x ◇ (y ◇ y)) ◇ ((y ◇ z) ◇ z)) = y := by
    exact (h y x z).symm
  have p5 : (c ◇ c) = c := by
    exact hc
  have p17 (x : G) : ((x ◇ c) ◇ c) = c := by
    exact (((congrArg (fun _t : G => ((x ◇ _t) ◇ c)) ((p5)))).symm).trans ((((congrArg (fun _t : G => ((x ◇ (c ◇ c)) ◇ _t)) ((p5)))).symm).trans ((((congrArg (fun _t : G => ((x ◇ (c ◇ c)) ◇ (_t ◇ c))) ((p5)))).symm).trans ((p2 x c c))))
  have p25 (x y : G) : ((x ◇ (y ◇ y)) ◇ c) = y := by
    exact (((congrArg (fun _t : G => ((x ◇ (y ◇ y)) ◇ _t)) ((p17 y)))).symm).trans ((p2 x y c))
  have p27 (x y z : G) : ((x ◇ ((y ◇ (z ◇ z)) ◇ (y ◇ (z ◇ z)))) ◇ (z ◇ c)) = (y ◇ (z ◇ z)) := by
    exact (((congrArg (fun _t : G => ((x ◇ ((y ◇ (z ◇ z)) ◇ (y ◇ (z ◇ z)))) ◇ (_t ◇ c))) ((p25 y z)))).symm).trans ((p2 x (y ◇ (z ◇ z)) c))
  have p31 (x : G) : (x ◇ c) = c := by
    exact (((congrArg (fun _t : G => (_t ◇ c)) ((p25 a x)))).symm).trans ((p17 (a ◇ (x ◇ x))))
  have p34 (x y : G) : (x ◇ (y ◇ y)) = c := by
    exact ((((p31 (a ◇ ((x ◇ (y ◇ y)) ◇ (x ◇ (y ◇ y)))))).symm).trans ((((congrArg (fun _t : G => ((a ◇ ((x ◇ (y ◇ y)) ◇ (x ◇ (y ◇ y)))) ◇ _t)) ((p31 y)))).symm).trans ((p27 a x y)))).symm
  have p35 (x : G) : c = x := by
    exact (((p31 c)).symm).trans ((((congrArg (fun _t : G => (_t ◇ c)) ((p34 a x)))).symm).trans ((p25 a x)))
  exact (p35 a).symm.trans (p35 b)

theorem column_cycle (G : Type*) [Magma G] (h : Equation22446 G) :
    ∀ x y : G, (y ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x)) = x := by
  obtain ⟨sq, qs, col, orbit⟩ := square_inverse_structure G h
  intro x y
  have hq := qs ((x ◇ x) ◇ (x ◇ x))
  dsimp only at hq
  rw [square_period_three G h x] at hq
  have hh := col x y
  dsimp only at hh
  rwa [hq] at hh

theorem shifted_column (G : Type*) [Magma G] (h : Equation22446 G)
    (x y : G) : (x ◇ y) ◇ (y ◇ y) = (y ◇ y) ◇ (y ◇ y) := by
  let S : G → G := fun x => x ◇ x
  have hs (a : G) : S (S (S a)) = a := square_period_three G h a
  have hh := column_cycle G h (S (S y)) x
  change (x ◇ S (S (S y))) ◇ S (S (S (S y))) = S (S y) at hh
  rw [hs y] at hh
  exact hh

theorem equation2_of_adjacent_product (G : Type*) [Magma G] (h : Equation22446 G)
    (a : G) (ha : a ◇ (a ◇ a) = (a ◇ a) ◇ (a ◇ a)) : Equation2 G := by
  let S : G → G := fun x => x ◇ x
  have hs (x : G) : S (S (S x)) = x := square_period_three G h x
  have hq (x : G) : (x ◇ S x) ◇ S x = S (S x) :=
    square_injective G h ((h x (x ◇ S x) (S x)).symm.trans (hs x).symm)
  change a ◇ S a = S (S a) at ha
  have hcb : S (S a) ◇ S a = S (S a) := by
    have hh := hq a
    rwa [ha] at hh
  have hac : a ◇ S (S a) = S a := by
    have hh := (h (S a) (S (S a)) (S a)).symm
    change S (S (S a)) ◇ (S (S a) ◇ S a) = S a at hh
    rwa [hs a, hcb] at hh
  have hbc1 : S a ◇ S (S a) = S a := by
    have hh := (h (S a) a (S a)).symm
    change (a ◇ S (S a)) ◇ (S (S a) ◇ S a) = S a at hh
    rwa [hac, hcb] at hh
  have hbc2 : S a ◇ S (S a) = S (S a) := by
    have hh := (h (S (S a)) a (S a)).symm
    change (a ◇ S (S (S a))) ◇ ((S (S a) ◇ S a) ◇ S a) = S (S a) at hh
    rw [hs a, hcb, hcb] at hh
    exact hh
  exact equation2_of_idempotent G h (S a) (hbc2.symm.trans hbc1)

theorem equation2_of_left_fixed_point (G : Type*) [Magma G] (h : Equation22446 G)
    (a b : G) (hab : a ◇ b = b) : Equation2 G := by
  have hh := shifted_column G h a b
  rw [hab] at hh
  exact equation2_of_adjacent_product G h b hh

theorem finite_column_preimage (G : Type*) [Magma G] [Finite G]
    (h : Equation22446 G) (u v : G) : ∃ w : G, w ◇ ((u ◇ v) ◇ (u ◇ v)) = u := by
  let S : G → G := fun x => x ◇ x
  have hs (x : G) : S (S (S x)) = x := square_period_three G h x
  let D := {t : G × G × G // ∃ w : G, w ◇ t.2.1 = t.1}
  let F : D → D := fun t =>
    ⟨((S (S t.val.2.1) ◇ t.val.2.2) ◇ t.val.2.2, t.val.2.2, t.val.1),
      ⟨S (S t.val.2.1) ◇ t.val.2.2, rfl⟩⟩
  have recover (t : D) : S (t.val.1 ◇ (F t).val.1) = t.val.2.1 := by
    obtain ⟨w, hw⟩ := t.property
    have hh := h (S (S t.val.2.1)) w t.val.2.2
    change S (S t.val.2.1) =
      (w ◇ S (S (S t.val.2.1))) ◇ (F t).val.1 at hh
    rw [hs t.val.2.1, hw] at hh
    exact (congrArg S hh).symm.trans (hs t.val.2.1)
  have hi : Function.Injective F := by
    intro a b hab
    have hu : a.val.1 = b.val.1 := congrArg (fun t : D => t.val.2.2) hab
    have hz : a.val.2.2 = b.val.2.2 := congrArg (fun t : D => t.val.2.1) hab
    have hv : (F a).val.1 = (F b).val.1 := congrArg (fun t : D => t.val.1) hab
    have hy : a.val.2.1 = b.val.2.1 := by
      calc
        _ = S (a.val.1 ◇ (F a).val.1) := (recover a).symm
        _ = S (b.val.1 ◇ (F b).val.1) := by rw [hu, hv]
        _ = _ := recover b
    exact Subtype.ext (Prod.ext hu (Prod.ext hy hz))
  let target : D := ⟨(v, S (S v), u), ⟨S (S v), hs v⟩⟩
  obtain ⟨t, ht⟩ := Finite.surjective_of_injective hi target
  have hu : t.val.1 = u := congrArg (fun t : D => t.val.2.2) ht
  have hv : (F t).val.1 = v := congrArg (fun t : D => t.val.1) ht
  have hy : t.val.2.1 = S (u ◇ v) := by
    have hh := (recover t).symm
    rwa [hu, hv] at hh
  obtain ⟨w, hw⟩ := t.property
  rw [hy, hu] at hw
  exact ⟨w, hw⟩

theorem finite_row_image_identity (G : Type*) [Magma G] [Finite G]
    (h : Equation22446 G) (u v z : G) :
    u ◇ (((u ◇ v) ◇ z) ◇ z) = u ◇ v := by
  obtain ⟨w, hw⟩ := finite_column_preimage G h u v
  have hh := (h (u ◇ v) w z).symm
  rwa [hw] at hh

theorem finite_adjacent_absorption (G : Type*) [Magma G] [Finite G]
    (h : Equation22446 G) (x : G) : x ◇ (x ◇ x) = x ◇ x := by
  let S : G → G := fun a => a ◇ a
  have hs (a : G) : S (S (S a)) = a := square_period_three G h a
  have hq (a : G) : (a ◇ S a) ◇ S a = S (S a) :=
    square_injective G h ((h a (a ◇ S a) (S a)).symm.trans (hs a).symm)
  have hshift (a b : G) : (a ◇ S (S b)) ◇ b = S b := by
    have hh := column_cycle G h (S b) a
    change (a ◇ S (S b)) ◇ S (S (S b)) = S b at hh
    rwa [hs b] at hh
  have he (a b : G) : a ◇ (S b ◇ b) = a ◇ S (S b) := by
    have hh := finite_row_image_identity G h a (S (S b)) b
    rw [hshift a b] at hh
    exact hh
  have hh := finite_row_image_identity G h x (S x) (S x)
  rw [hq x, he x (S x), hs x] at hh
  exact hh.symm

theorem finite_trivial (G : Type*) [Magma G] [Finite G]
    (h : Equation22446 G) : Equation2 G := by
  intro a b
  exact equation2_of_left_fixed_point G h a (a ◇ a)
    (finite_adjacent_absorption G h a) a b

#print axioms square_injective
#print axioms square_inverse_structure
#print axioms square_period_three
#print axioms equation2_of_idempotent
#print axioms column_cycle
#print axioms shifted_column
#print axioms equation2_of_adjacent_product
#print axioms equation2_of_left_fixed_point
#print axioms finite_column_preimage
#print axioms finite_row_image_identity
#print axioms finite_adjacent_absorption
#print axioms finite_trivial

end Equation22446Finite

example (G : Type*) [Magma G] [Finite G] :
    (∀ x y z : G, x = (y ◇ (x ◇ x)) ◇ ((x ◇ z) ◇ z)) → ∀ a b : G, a = b :=
  Equation22446Finite.finite_trivial G

@[reducible] def Equation22591 (G : Type _) [Magma G] : Prop :=
  ∀ x y z : G, x = (y ◇ (y ◇ x)) ◇ ((x ◇ x) ◇ z)

/-- Transfer the finite theorem through the opposite magma. -/
theorem finite_trivial_dual (G : Type*) [Magma G] [Finite G]
    (h : Equation22591 G) : Equation2 G := by
  let opposite : Magma G := ⟨fun x y => y ◇ x⟩
  have hd : @Equation22446 G opposite := by
    intro x y z
    exact h x z y
  exact @Equation22446Finite.finite_trivial G opposite inferInstance hd

#print axioms finite_trivial_dual

example (G : Type*) [Magma G] [Finite G] :
    (∀ x y z : G, x = (y ◇ (y ◇ x)) ◇ ((x ◇ x) ◇ z)) → ∀ a b : G, a = b :=
  finite_trivial_dual G

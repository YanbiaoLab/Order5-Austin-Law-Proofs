/- Finite left-division image argument for Equation12294. -/
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finite.Set
import JudgeMagma.Magma

@[reducible] def Equation2 (G : Type _) [Magma G] : Prop := ∀ x y : G, x = y
@[reducible] def Equation12294 (G : Type _) [Magma G] : Prop :=
  ∀ x y z : G, x = y ◇ (((z ◇ y) ◇ x) ◇ (x ◇ y))

namespace Equation12294Finite

theorem left_bijective (G : Type*) [Magma G] [Finite G]
    (h : Equation12294 G) (y : G) : Function.Bijective (fun x : G => y ◇ x) := by
  have hs : Function.Surjective (fun x : G => y ◇ x) := by
    intro x
    exact ⟨((y ◇ y) ◇ x) ◇ (x ◇ y), (h x y y).symm⟩
  exact ⟨Finite.injective_iff_surjective.mpr hs, hs⟩

theorem left_division_presentation (G : Type*) [Magma G] [Finite G]
    (h : Equation12294 G) : ∃ d : G → G → G,
      (∀ x y : G, x ◇ d x y = y) ∧
      (∀ x y : G, d x (x ◇ y) = y) ∧
      (∀ x y z : G, ((x ◇ y) ◇ z) ◇ (z ◇ y) = d y z) := by
  let d (x y : G) := Classical.choose ((left_bijective G h x).2 y)
  have hd1 (x y : G) : x ◇ d x y = y := Classical.choose_spec ((left_bijective G h x).2 y)
  have hd2 (x y : G) : d x (x ◇ y) = y := (left_bijective G h x).1 (hd1 x (x ◇ y))
  refine ⟨d, hd1, hd2, ?_⟩
  intro x y z
  apply (left_bijective G h y).1
  exact (h z y x).symm.trans (hd1 y z).symm

theorem division_identity (G : Type*) [Magma G] (d : G → G → G)
    (hd1 : ∀ x y : G, x ◇ d x y = y)
    (hd2 : ∀ x y : G, d x (x ◇ y) = y)
    (hlaw : ∀ x y z : G, ((x ◇ y) ◇ z) ◇ (z ◇ y) = d y z) :
    ∀ x y z : G, d (d x y) (d y (d (d z x) (d x y))) = d z x := by
  have p2 (x y : G) : (x ◇ (d x y)) = y := by
    exact hd1 x y
  have p3 (x y : G) : (d x (x ◇ y)) = y := by
    exact hd2 x y
  have p4 (x y z : G) : (((x ◇ y) ◇ z) ◇ (z ◇ y)) = (d y z) := by
    exact hlaw x y z
  have p6 (x y z : G) : ((x ◇ y) ◇ (y ◇ (d z x))) = (d (d z x) y) := by
    exact (((congrArg (fun _t : G => ((_t ◇ y) ◇ (y ◇ (d z x)))) ((p2 z x)))).symm).trans ((p4 z (d z x) y))
  have p14 (x y : G) : ((x ◇ y) ◇ x) = (d (d y x) y) := by
    exact (((congrArg (fun _t : G => ((x ◇ y) ◇ _t)) ((p2 y x)))).symm).trans ((p6 x y y))
  have p15 (x y z : G) : (x ◇ (d y z)) = (d (z ◇ x) (d (d y z) x)) := by
    exact ((((congrArg (fun _t : G => (d (z ◇ x) _t)) ((p6 z x y)))).symm).trans ((p3 (z ◇ x) (x ◇ (d y z))))).symm
  have p20 (x y : G) : (x ◇ y) = (d (d (d y x) y) (d y x)) := by
    exact (((congrArg (fun _t : G => (_t ◇ y)) ((p2 y x)))).symm).trans ((p14 y (d y x)))
  have p21 (x y : G) : (d (d (d (d x y) x) (d x y)) (d (d x y) x)) = y := by
    exact (((congrArg (fun _t : G => (d _t (d (d x y) x))) ((p20 y x)))).symm).trans ((((congrArg (fun _t : G => (d (y ◇ x) _t)) ((p14 y x)))).symm).trans ((p3 (y ◇ x) y)))
  have p23 (x y z : G) : (d (d (d (d x y) z) (d x y)) (d (d x y) z)) = (d (d (d (d z y) z) (d z y)) (d (d x y) z)) := by
    exact ((((p20 z (d x y))).symm).trans ((p15 z x y))).trans ((congrArg (fun _t : G => (d _t (d (d x y) z))) ((p20 y z))))
  have p26 (x y : G) : (d x (d (d (d y x) y) (d y x))) = y := by
    exact (((congrArg (fun _t : G => (d x _t)) ((p20 x y)))).symm).trans ((p3 x y))
  have p29 (x y z : G) : (d x (d (d (d (d x y) x) (d x y)) (d (d z y) x))) = (d z y) := by
    exact (((((p26 x (d z y))).symm).trans ((((congrArg (fun _t : G => (d _t (d (d (d (d z y) x) (d z y)) (d (d z y) x)))) ((p21 (d z y) x)))).symm).trans ((((p20 (d (d z y) x) (d (d (d z y) x) (d z y)))).symm).trans (((p20 (d (d z y) x) (d (d (d z y) x) (d z y)))).trans ((congrArg (fun _t : G => (d (d (d (d (d (d z y) x) (d z y)) (d (d z y) x)) (d (d (d z y) x) (d z y))) _t)) ((p23 z y x)))))))).trans ((congrArg (fun _t : G => (d _t (d (d (d (d x y) x) (d x y)) (d (d z y) x)))) ((p21 (d z y) x))))).symm
  have p41 (x y z : G) : (d (d x y) (d y (d (d z x) (d x y)))) = (d z x) := by
    exact (((congrArg (fun _t : G => (d (d x y) (d _t (d (d z x) (d x y))))) ((p21 x y)))).symm).trans ((p29 (d x y) x z))
  exact p41

#print axioms division_identity


theorem image_decoder (G : Type*) [Magma G] (d : G → G → G)
    (hd1 : ∀ x y : G, x ◇ d x y = y)
    (hd2 : ∀ x y : G, d x (x ◇ y) = y)
    (hlaw : ∀ x y z : G, ((x ◇ y) ◇ z) ◇ (z ◇ y) = d y z)
    (x t u : G) (hu : ∃ w : G, d w x = u) :
    d t (d (x ◇ t) (d u t)) = u := by
  obtain ⟨w, rfl⟩ := hu
  have hh := division_identity G d hd1 hd2 hlaw x (x ◇ t) w
  simpa only [hd2 x t] using hh

theorem right_injective_on_images (G : Type*) [Magma G] (d : G → G → G)
    (hd1 : ∀ x y : G, x ◇ d x y = y)
    (hd2 : ∀ x y : G, d x (x ◇ y) = y)
    (hlaw : ∀ x y z : G, ((x ◇ y) ◇ z) ◇ (z ◇ y) = d y z)
    (x t u v : G) (hu : ∃ w : G, d w x = u) (hv : ∃ w : G, d w x = v)
    (he : d u t = d v t) : u = v := by
  calc
    u = d t (d (x ◇ t) (d u t)) := (image_decoder G d hd1 hd2 hlaw x t u hu).symm
    _ = d t (d (x ◇ t) (d v t)) := by rw [he]
    _ = v := image_decoder G d hd1 hd2 hlaw x t v hv

/-- Finiteness turns the injections between column images into surjections. -/
theorem image_completion (G : Type*) [Magma G] [Finite G] (d : G → G → G)
    (hd1 : ∀ x y : G, x ◇ d x y = y)
    (hd2 : ∀ x y : G, d x (x ◇ y) = y)
    (hlaw : ∀ x y z : G, ((x ◇ y) ◇ z) ◇ (z ◇ y) = d y z)
    (x t z : G) :
    let u := d t (d (x ◇ t) (d z t))
    d u t = d z t ∧ ∃ w : G, d w x = u := by
  let C := {u : G // ∃ w : G, d w x = u}
  let : Finite C := Finite.of_injective (fun u : C => u.val) Subtype.val_injective
  let F : C → C := fun u => ⟨d (d u.val t) x, ⟨d u.val t, rfl⟩⟩
  have hi : Function.Injective F := by
    intro u v huv
    have h0 : d (d u.val t) x = d (d v.val t) x := congrArg Subtype.val huv
    have h1 : d u.val t = d v.val t := right_injective_on_images G d hd1 hd2 hlaw
      t x (d u.val t) (d v.val t) ⟨u.val, rfl⟩ ⟨v.val, rfl⟩ h0
    exact Subtype.ext (right_injective_on_images G d hd1 hd2 hlaw
      x t u.val v.val u.property v.property h1)
  let target : C := ⟨d (d z t) x, ⟨d z t, rfl⟩⟩
  obtain ⟨v, hv⟩ := Finite.surjective_of_injective hi target
  have h0 : d (d v.val t) x = d (d z t) x := congrArg Subtype.val hv
  have he : d v.val t = d z t := right_injective_on_images G d hd1 hd2 hlaw
    t x (d v.val t) (d z t) ⟨v.val, rfl⟩ ⟨z, rfl⟩ h0
  have hr := image_decoder G d hd1 hd2 hlaw x t v.val v.property
  rw [he] at hr
  have hvalue : v.val = d t (d (x ◇ t) (d z t)) := hr.symm
  constructor
  · rwa [hvalue] at he
  · obtain ⟨w, hw⟩ := v.property
    exact ⟨w, hw.trans hvalue⟩

theorem finite_inverse (G : Type*) [Magma G] [Finite G] (d : G → G → G)
    (hd1 : ∀ x y : G, x ◇ d x y = y)
    (hd2 : ∀ x y : G, d x (x ◇ y) = y)
    (hlaw : ∀ x y z : G, ((x ◇ y) ◇ z) ◇ (z ◇ y) = d y z)
    (x y z : G) :
    d (d (d x y) (d y (d z (d x y)))) (d x y) = d z (d x y) := by
  have hh := (image_completion G d hd1 hd2 hlaw x (d x y) z).1
  simpa only [hd1 x y] using hh

theorem finite_completion_identity (G : Type*) [Magma G] [Finite G] (d : G → G → G)
    (hd1 : ∀ x y : G, x ◇ d x y = y)
    (hd2 : ∀ x y : G, d x (x ◇ y) = y)
    (hlaw : ∀ x y z : G, ((x ◇ y) ◇ z) ◇ (z ◇ y) = d y z)
    (x y z w : G) :
    d (d x y) (d y (d (d z (d (x ◇ z) (d w z))) (d x y))) =
      d z (d (x ◇ z) (d w z)) := by
  have hm := (image_completion G d hd1 hd2 hlaw x z w).2
  have hh := image_decoder G d hd1 hd2 hlaw x (d x y)
    (d z (d (x ◇ z) (d w z))) hm
  simpa only [hd1 x y] using hh

#print axioms left_bijective
#print axioms left_division_presentation
#print axioms image_decoder
#print axioms right_injective_on_images
#print axioms image_completion
#print axioms finite_inverse
#print axioms finite_completion_identity

theorem finite_trivial (G : Type*) [Magma G] [Finite G]
    (h : Equation12294 G) : Equation2 G := by
  intro a b
  obtain ⟨d, hd1, hd2, hlaw⟩ := left_division_presentation G h
  have p2 (x y : G) : (x ◇ (d x y)) = y := by
    exact hd1 x y
  have p3 (x y : G) : (d x (x ◇ y)) = y := by
    exact hd2 x y
  have p4 (x y z : G) : (((x ◇ y) ◇ z) ◇ (z ◇ y)) = (d y z) := by
    exact hlaw x y z
  have p5 (x y z : G) : (d (d x y) (d y (d (d z x) (d x y)))) = (d z x) := by
    exact division_identity G d hd1 hd2 hlaw x y z
  have p6 (x y z : G) : (d (d (d x y) (d y (d z (d x y)))) (d x y)) = (d z (d x y)) := by
    exact finite_inverse G d hd1 hd2 hlaw x y z
  have p7 (u x y z : G) : (d (d x y) (d y (d (d z (d (x ◇ z) (d u z))) (d x y)))) = (d z (d (x ◇ z) (d u z))) := by
    exact finite_completion_identity G d hd1 hd2 hlaw x y z u
  have p9 (x y z : G) : ((x ◇ y) ◇ (y ◇ (d z x))) = (d (d z x) y) := by
    exact (((congrArg (fun _t : G => ((_t ◇ y) ◇ (y ◇ (d z x)))) ((p2 z x)))).symm).trans ((p4 z (d z x) y))
  have p17 (x y z : G) : (d x (d (y ◇ x) (d (d z y) x))) = (d z y) := by
    exact (((congrArg (fun _t : G => (d x (d (y ◇ x) (d (d z y) _t)))) ((p3 y x)))).symm).trans ((((congrArg (fun _t : G => (d _t (d (y ◇ x) (d (d z y) (d y (y ◇ x)))))) ((p3 y x)))).symm).trans ((p5 y (y ◇ x) z)))
  have p20 (u x y z : G) : (d (d x y) (d (d z (d (d x y) (d y z))) (d (d u (d y z)) (d x y)))) = (d u (d y z)) := by
    exact (((congrArg (fun _t : G => (d (d x y) (d (d z (d (d x y) (d y z))) (d (d u (d y z)) _t)))) ((p5 y z x)))).symm).trans ((((congrArg (fun _t : G => (d _t (d (d z (d (d x y) (d y z))) (d (d u (d y z)) (d (d y z) (d z (d (d x y) (d y z)))))))) ((p5 y z x)))).symm).trans ((p5 (d y z) (d z (d (d x y) (d y z))) u)))
  have p21 (u x y z : G) : (d (d (d x (d (d y z) (d z x))) u) (d u (d (d y z) (d (d x (d (d y z) (d z x))) u)))) = (d y z) := by
    exact ((((congrArg (fun _t : G => (d (d (d x (d (d y z) (d z x))) u) (d u (d _t (d (d x (d (d y z) (d z x))) u))))) ((p5 z x y)))).symm).trans ((p5 (d x (d (d y z) (d z x))) u (d z x)))).trans ((p5 z x y))
  have p24 (u x y z : G) : (d (d x (d y z)) (d (d y z) (d (d u (d (d y z) (d z (d x (d y z))))) (d x (d y z))))) = (d u (d (d y z) (d z (d x (d y z))))) := by
    exact (((congrArg (fun _t : G => (d (d x (d y z)) (d (d y z) (d (d u (d (d y z) (d z (d x (d y z))))) _t)))) ((p6 y z x)))).symm).trans ((((congrArg (fun _t : G => (d _t (d (d y z) (d (d u (d (d y z) (d z (d x (d y z))))) (d (d (d y z) (d z (d x (d y z)))) (d y z)))))) ((p6 y z x)))).symm).trans ((p5 (d (d y z) (d z (d x (d y z)))) (d y z) u)))
  have p26 (x y z : G) : (d (d (d (d x y) (d y z)) (d x y)) (d (d x y) (d y z))) = (d z (d (d x y) (d y z))) := by
    exact (((congrArg (fun _t : G => (d (d (d (d x y) (d y z)) _t) (d (d x y) (d y z)))) ((p5 y z x)))).symm).trans ((p6 (d x y) (d y z) z))
  have p28 (u x y z : G) : (d (d x y) (d y (d (d (d x z) (d z (d u (d x z)))) (d x y)))) = (d (d x z) (d z (d u (d x z)))) := by
    exact ((((congrArg (fun _t : G => (d (d x y) (d y (d (d (d x z) (d _t (d u (d x z)))) (d x y))))) ((p2 x z)))).symm).trans ((p7 u x y (d x z)))).trans ((congrArg (fun _t : G => (d (d x z) (d _t (d u (d x z))))) ((p2 x z))))
  have p45 (x y : G) : ((x ◇ y) ◇ x) = (d (d y x) y) := by
    exact (((congrArg (fun _t : G => ((x ◇ y) ◇ _t)) ((p2 y x)))).symm).trans ((p9 x y y))
  have p46 (x y z : G) : (x ◇ (d y z)) = (d (z ◇ x) (d (d y z) x)) := by
    exact ((((congrArg (fun _t : G => (d (z ◇ x) _t)) ((p9 z x y)))).symm).trans ((p3 (z ◇ x) (x ◇ (d y z))))).symm
  have p54 (x y : G) : (x ◇ y) = (d (d (d y x) y) (d y x)) := by
    exact (((congrArg (fun _t : G => (_t ◇ y)) ((p2 y x)))).symm).trans ((p45 y (d y x)))
  have p55 (x y : G) : (d (d (d (d x y) x) (d x y)) (d (d x y) x)) = y := by
    exact (((congrArg (fun _t : G => (d _t (d (d x y) x))) ((p54 y x)))).symm).trans ((((congrArg (fun _t : G => (d (y ◇ x) _t)) ((p45 y x)))).symm).trans ((p3 (y ◇ x) y)))
  have p58 (x y z : G) : (d (d (d (d x y) z) (d x y)) (d (d x y) z)) = (d (d (d (d z y) z) (d z y)) (d (d x y) z)) := by
    exact ((((p54 z (d x y))).symm).trans ((p46 z x y))).trans ((congrArg (fun _t : G => (d _t (d (d x y) z))) ((p54 y z))))
  have p65 (x y z : G) : (d x (d (d (d (d x y) x) (d x y)) (d (d z y) x))) = (d z y) := by
    exact (((congrArg (fun _t : G => (d x (d _t (d (d z y) x)))) ((p54 y x)))).symm).trans ((p17 x y z))
  have p68 (x y : G) : (d x (d (d (d y x) y) (d y x))) = y := by
    exact (((congrArg (fun _t : G => (d x _t)) ((p54 x y)))).symm).trans ((p3 x y))
  have p69 (x y z : G) : (d x (d (d (d y x) y) (d (d z (d (d (d y x) y) (d y x))) x))) = (d z (d (d (d y x) y) (d y x))) := by
    exact (((congrArg (fun _t : G => (d x (d (d (d y x) y) (d (d z (d (d (d y x) y) (d y x))) _t)))) ((p55 y x)))).symm).trans ((((congrArg (fun _t : G => (d _t (d (d (d y x) y) (d (d z (d (d (d y x) y) (d y x))) (d (d (d (d y x) y) (d y x)) (d (d y x) y)))))) ((p55 y x)))).symm).trans ((p5 (d (d (d y x) y) (d y x)) (d (d y x) y) z)))
  have p70 (x y z : G) : (d (d (d (d x y) x) z) (d z (d y (d (d (d x y) x) z)))) = y := by
    exact ((((congrArg (fun _t : G => (d (d (d (d x y) x) z) (d z (d _t (d (d (d x y) x) z))))) ((p55 x y)))).symm).trans ((p5 (d (d x y) x) z (d (d (d x y) x) (d x y))))).trans ((p55 x y))
  have p71 (x y z : G) : (d (d x (d (d (d y x) y) (d z x))) x) = (d z x) := by
    exact ((((congrArg (fun _t : G => (d (d x (d (d (d y x) y) (d z x))) _t)) ((p55 y x)))).symm).trans ((((congrArg (fun _t : G => (d (d x (d (d (d y x) y) (d z _t))) (d (d (d (d y x) y) (d y x)) (d (d y x) y)))) ((p55 y x)))).symm).trans ((((congrArg (fun _t : G => (d (d _t (d (d (d y x) y) (d z (d (d (d (d y x) y) (d y x)) (d (d y x) y))))) (d (d (d (d y x) y) (d y x)) (d (d y x) y)))) ((p55 y x)))).symm).trans ((p6 (d (d (d y x) y) (d y x)) (d (d y x) y) z))))).trans ((congrArg (fun _t : G => (d z _t)) ((p55 y x))))
  have p82 (u x y z : G) : (d (d x y) (d (d (d (d (d z y) z) (d z y)) (d (d x y) z)) (d (d u z) (d x y)))) = (d u z) := by
    exact ((((congrArg (fun _t : G => (d (d x y) (d (d (d (d (d z y) z) (d z y)) (d (d x y) z)) (d (d u _t) (d x y))))) ((p68 y z)))).symm).trans ((((congrArg (fun _t : G => (d (d x y) (d (d (d (d (d z y) z) (d z y)) (d (d x y) _t)) (d (d u (d y (d (d (d z y) z) (d z y)))) (d x y))))) ((p68 y z)))).symm).trans ((p20 u x y (d (d (d z y) z) (d z y)))))).trans ((congrArg (fun _t : G => (d u _t)) ((p68 y z))))
  have p89 (u x y z : G) : (d (d x y) (d y (d (d z (d y (d (d (d u y) u) (d x y)))) (d x y)))) = (d z (d y (d (d (d u y) u) (d x y)))) := by
    exact (((congrArg (fun _t : G => (d (d x y) (d y (d (d z (d y (d (d (d u y) u) (d x y)))) _t)))) ((p71 y u x)))).symm).trans ((((congrArg (fun _t : G => (d _t (d y (d (d z (d y (d (d (d u y) u) (d x y)))) (d (d y (d (d (d u y) u) (d x y))) y))))) ((p71 y u x)))).symm).trans ((p5 (d y (d (d (d u y) u) (d x y))) y z)))
  have p92 (x y z : G) : (d (d (d (d x y) x) (d (d (d z (d (d x y) x)) z) y)) (d (d x y) x)) = y := by
    exact ((((congrArg (fun _t : G => (d (d (d (d x y) x) (d (d (d z (d (d x y) x)) z) _t)) (d (d x y) x))) ((p55 x y)))).symm).trans ((p71 (d (d x y) x) z (d (d (d x y) x) (d x y))))).trans ((p55 x y))
  have p101 (u w x y z : G) : (d (d x y) (d (d (d (d (d (d y z) y) (d y z)) (d (d u z) y)) (d (d x y) (d u z))) (d (d w (d u z)) (d x y)))) = (d w (d u z)) := by
    exact ((((congrArg (fun _t : G => (d (d x y) (d (d (d (d (d (d y z) y) (d y z)) (d (d u z) y)) (d (d x y) (d u z))) (d (d w _t) (d x y))))) ((p65 y z u)))).symm).trans ((((congrArg (fun _t : G => (d (d x y) (d (d (d (d (d (d y z) y) (d y z)) (d (d u z) y)) (d (d x y) _t)) (d (d w (d y (d (d (d (d y z) y) (d y z)) (d (d u z) y)))) (d x y))))) ((p65 y z u)))).symm).trans ((p20 w x y (d (d (d (d y z) y) (d y z)) (d (d u z) y)))))).trans ((congrArg (fun _t : G => (d w _t)) ((p65 y z u))))
  have p106 (u x y z : G) : (d (d (d x (d y (d (d (d z y) z) x))) u) (d u (d y (d (d x (d y (d (d (d z y) z) x))) u)))) = y := by
    exact ((((congrArg (fun _t : G => (d (d (d x (d y (d (d (d z y) z) x))) u) (d u (d _t (d (d x (d y (d (d (d z y) z) x))) u))))) ((p70 z y x)))).symm).trans ((p5 (d x (d y (d (d (d z y) z) x))) u (d (d (d z y) z) x)))).trans ((p70 z y x))
  have p107 (x y z : G) : (d (d x (d y (d (d (d z y) z) x))) (d (d y (d (d (d z y) z) x)) y)) = (d (d (d z y) z) x) := by
    exact (((congrArg (fun _t : G => (d (d x (d y (d (d (d z y) z) x))) (d (d y (d (d (d z y) z) x)) _t))) ((p70 z y x)))).symm).trans ((p5 x (d y (d (d (d z y) z) x)) (d (d z y) z)))
  have p109 (x y z : G) : (d (d (d x (d (d (d y x) y) z)) x) (d x (d (d (d y x) y) z))) = (d z (d x (d (d (d y x) y) z))) := by
    exact (((congrArg (fun _t : G => (d (d (d x (d (d (d y x) y) z)) _t) (d x (d (d (d y x) y) z)))) ((p70 y x z)))).symm).trans ((p6 x (d (d (d y x) y) z) z))
  have p113 (u x y z : G) : (d (d x y) (d (d (d z (d (d (d u z) u) y)) (d (d x y) (d y (d z (d (d (d u z) u) y))))) (d z (d x y)))) = z := by
    exact ((((congrArg (fun _t : G => (d (d x y) (d (d (d z (d (d (d u z) u) y)) (d (d x y) (d y (d z (d (d (d u z) u) y))))) (d _t (d x y))))) ((p70 u z y)))).symm).trans ((p20 (d (d (d u z) u) y) x y (d z (d (d (d u z) u) y))))).trans ((p70 u z y))
  have p114 (u x y z : G) : (d (d x (d y z)) (d (d (d z (d (d (d y u) y) (d y z))) (d (d x (d y z)) (d (d y u) y))) (d u (d x (d y z))))) = u := by
    exact (((congrArg (fun _t : G => (d (d x (d y z)) (d (d (d z (d (d (d y u) y) (d y z))) (d (d x (d y z)) (d (d y u) y))) (d u _t)))) ((p20 x (d y u) y z)))).symm).trans ((((congrArg (fun _t : G => (d _t (d (d (d z (d (d (d y u) y) (d y z))) (d (d x (d y z)) (d (d y u) y))) (d u (d (d (d y u) y) (d (d z (d (d (d y u) y) (d y z))) (d (d x (d y z)) (d (d y u) y)))))))) ((p20 x (d y u) y z)))).symm).trans ((p70 y u (d (d z (d (d (d y u) y) (d y z))) (d (d x (d y z)) (d (d y u) y))))))
  have p143 (x y z : G) : (d (d (d (d x y) x) (d (d z (d (d (d x y) x) (d x z))) y)) (d (d x y) x)) = y := by
    exact (((congrArg (fun _t : G => (d (d (d (d x y) x) (d (d z (d (d (d x y) x) (d x z))) y)) _t)) ((p21 y z (d x y) x)))).symm).trans ((p70 x y (d (d z (d (d (d x y) x) (d x z))) y)))
  have p178 (x y z : G) : (d (d (d (d x y) x) (d (d (d (d (d z x) z) (d z x)) (d (d (d x y) x) z)) y)) (d (d x y) x)) = y := by
    exact (((congrArg (fun _t : G => (d (d (d (d x y) x) (d (d (d (d (d z x) z) (d z x)) (d (d (d x y) x) _t)) y)) (d (d x y) x))) ((p68 x z)))).symm).trans ((p143 x y (d (d (d z x) z) (d z x))))
  have p180 (u x y z : G) : (d (d (d (d x y) x) (d (d (d (d (d (d x z) x) (d x z)) (d (d u z) x)) (d (d (d x y) x) (d u z))) y)) (d (d x y) x)) = y := by
    exact (((congrArg (fun _t : G => (d (d (d (d x y) x) (d (d (d (d (d (d x z) x) (d x z)) (d (d u z) x)) (d (d (d x y) x) _t)) y)) (d (d x y) x))) ((p65 x z u)))).symm).trans ((p143 x y (d (d (d (d x z) x) (d x z)) (d (d u z) x))))
  have p194 (u x y z : G) : (d (d (d (d (d x y) x) (d x y)) (d (d z y) x)) (d (d u x) (d z y))) = (d (d (d (d u x) (d z y)) (d u x)) (d (d u x) (d z y))) := by
    exact (((((congrArg (fun _t : G => (d (d (d (d u x) (d z y)) (d u x)) (d (d u x) _t))) ((p65 x y z)))).symm).trans ((((congrArg (fun _t : G => (d (d (d (d u x) _t) (d u x)) (d (d u x) (d x (d (d (d (d x y) x) (d x y)) (d (d z y) x)))))) ((p65 x y z)))).symm).trans ((p26 u x (d (d (d (d x y) x) (d x y)) (d (d z y) x)))))).trans ((congrArg (fun _t : G => (d (d (d (d (d x y) x) (d x y)) (d (d z y) x)) (d (d u x) _t))) ((p65 x y z))))).symm
  have p228 (u x y z : G) : (d (d x (d (d (d y x) y) (d (d x z) (d z (d u (d x z)))))) x) = (d (d x z) (d z (d u (d x z)))) := by
    exact (((congrArg (fun _t : G => (d (d x (d (d (d y x) y) (d (d x z) (d z (d u (d x z)))))) _t)) ((p70 y x (d (d x z) (d z (d u (d x z)))))))).symm).trans ((p28 u x (d (d (d y x) y) (d (d x z) (d z (d u (d x z))))) z))
  have p232 (u w x y z : G) : (d (d x y) (d y (d (d z (d (d u w) (d w (d x (d u w))))) (d x y)))) = (d z (d (d u w) (d w (d x (d u w))))) := by
    exact ((((congrArg (fun _t : G => (d (d x y) (d y (d _t (d x y))))) ((p24 z x u w)))).symm).trans ((p28 (d z (d (d u w) (d w (d x (d u w))))) x y (d u w)))).trans ((p24 z x u w))
  have p256 (u x y z : G) : (d x (d (d (d (d y z) u) (d y z)) (d (d y z) u))) = (d x (d (d (d (d u z) u) (d u z)) (d (d y z) u))) := by
    exact (((p6 (d (d (d y z) u) (d y z)) (d (d y z) u) x)).symm).trans (((p6 (d (d (d y z) u) (d y z)) (d (d y z) u) x)).trans ((congrArg (fun _t : G => (d x _t)) ((p58 y z u)))))
  have p261 (x y z : G) : (d (d (d x y) z) (d (d y (d (d (d x y) z) (d z y))) (d (d (d (d x y) z) (d x y)) (d (d x y) z)))) = (d (d (d z y) z) (d z y)) := by
    exact (((congrArg (fun _t : G => (d (d (d x y) z) (d (d y (d (d (d x y) z) (d z y))) _t))) (((p58 x y z)).symm))).symm).trans ((p20 (d (d z y) z) (d x y) z y))
  have p294 (u x y z : G) : (d (d (d (d (d x y) z) (d x y)) (d (d x y) z)) u) = (d (d (d (d (d z y) z) (d z y)) (d (d x y) z)) u) := by
    exact (((p107 u (d x y) (d (d x y) z))).symm).trans (((p107 u (d x y) (d (d x y) z))).trans ((congrArg (fun _t : G => (d _t u)) ((p58 x y z)))))
  have p338 (u w x y z : G) : (d (d x (d (d y (d x (d (d (d z x) z) y))) (d (d x u) (d u (d w (d x u)))))) x) = (d (d x u) (d u (d w (d x u)))) := by
    exact (((congrArg (fun _t : G => (d (d x (d (d y (d x (d (d (d z x) z) y))) (d (d x u) (d u (d w (d x u)))))) _t)) ((p106 (d (d x u) (d u (d w (d x u)))) y x z)))).symm).trans ((p28 w x (d (d y (d x (d (d (d z x) z) y))) (d (d x u) (d u (d w (d x u))))) u))
  have p350 (u x y z : G) : (d (d (d (d (d (d x y) x) (d x y)) (d (d (d y z) y) x)) (d (d u x) (d (d y z) y))) (d z (d u x))) = (d (d (d z (d u x)) z) (d z (d u x))) := by
    exact (((((congrArg (fun _t : G => (d (d (d z (d u x)) z) (d z _t))) ((p82 u (d y z) y x)))).symm).trans ((((congrArg (fun _t : G => (d (d (d z _t) z) (d z (d (d (d y z) y) (d (d (d (d (d x y) x) (d x y)) (d (d (d y z) y) x)) (d (d u x) (d (d y z) y))))))) ((p82 u (d y z) y x)))).symm).trans ((p109 z y (d (d (d (d (d x y) x) (d x y)) (d (d (d y z) y) x)) (d (d u x) (d (d y z) y))))))).trans ((congrArg (fun _t : G => (d (d (d (d (d (d x y) x) (d x y)) (d (d (d y z) y) x)) (d (d u x) (d (d y z) y))) (d z _t))) ((p82 u (d y z) y x))))).symm
  have p445 (u w x y z : G) : (d (d (d x (d (d (d (d y z) u) (d y z)) (d (d y z) u))) x) w) = (d (d (d x (d (d (d (d u z) u) (d u z)) (d (d y z) u))) x) w) := by
    exact (((p107 w (d (d (d (d y z) u) (d y z)) (d (d y z) u)) x)).symm).trans (((p107 w (d (d (d (d y z) u) (d y z)) (d (d y z) u)) x)).trans ((congrArg (fun _t : G => (d (d _t x) w)) ((p256 u x y z)))))
  have p462 (u w x y z : G) : (d (d (d (d (d (d x y) x) (d x y)) (d (d z y) x)) (d (d u x) (d z y))) w) = (d (d (d (d (d u x) (d z y)) (d u x)) (d (d u x) (d z y))) w) := by
    exact (((p294 w u x (d z y))).trans ((congrArg (fun _t : G => (d (d _t (d (d u x) (d z y))) w)) ((p58 z y x))))).symm
  have p519 (u w x y z : G) : (d (d x (d (d (d y x) y) (d z (d u (d (d (d w u) w) (d x u)))))) x) = (d z (d u (d (d (d w u) w) (d x u)))) := by
    exact ((((congrArg (fun _t : G => (d (d x (d (d (d y x) y) _t)) x)) ((p89 w x u z)))).symm).trans ((p228 (d z (d u (d (d (d w u) w) (d x u)))) x y u))).trans ((p89 w x u z))
  have p525 (u x y z : G) : (d (d (d x (d (d (d y x) y) z)) (d (d u z) (d z (d x (d (d (d y x) y) z))))) (d x (d u z))) = (d (d (d x (d u z)) x) (d x (d u z))) := by
    exact ((((congrArg (fun _t : G => (d (d (d x (d u z)) _t) (d x (d u z)))) ((p113 y u z x)))).symm).trans ((p6 x (d u z) (d (d x (d (d (d y x) y) z)) (d (d u z) (d z (d x (d (d (d y x) y) z)))))))).symm
  have p556 (u w x y z : G) : (d (d x y) (d y (d (d z (d (d (d u w) (d w x)) (d u w))) (d x y)))) = (d z (d (d (d u w) (d w x)) (d u w))) := by
    exact ((((congrArg (fun _t : G => (d (d x y) (d y (d (d z (d (d (d u w) (d w x)) _t)) (d x y))))) ((p5 w x u)))).symm).trans ((p232 (d u w) (d w x) x y z))).trans ((congrArg (fun _t : G => (d z (d (d (d u w) (d w x)) _t))) ((p5 w x u))))
  have p557 (u w x y z : G) : (d (d (d x y) (d y (d z (d (d u w) (d w (d (d x y) (d u w))))))) (d x y)) = (d z (d (d u w) (d w (d (d x y) (d u w))))) := by
    exact (((congrArg (fun _t : G => (d (d (d x y) (d y (d z (d (d u w) (d w (d (d x y) (d u w))))))) _t)) ((p5 y (d z (d (d u w) (d w (d (d x y) (d u w))))) x)))).symm).trans ((p232 u w (d x y) (d y (d z (d (d u w) (d w (d (d x y) (d u w)))))) z))
  have p639 (x y z : G) : (d (d (d x (d (d (d y x) y) (d z x))) (d (d (d (d z x) z) (d z x)) (d (d z x) (d x (d (d (d y x) y) (d z x)))))) z) = (d (d z x) z) := by
    exact (((((congrArg (fun _t : G => (d (d z _t) z)) ((p113 y (d (d z x) z) (d z x) x)))).symm).trans ((p519 x z z (d z x) (d (d x (d (d (d y x) y) (d z x))) (d (d (d (d z x) z) (d z x)) (d (d z x) (d x (d (d (d y x) y) (d z x))))))))).trans ((congrArg (fun _t : G => (d (d (d x (d (d (d y x) y) (d z x))) (d (d (d (d z x) z) (d z x)) (d (d z x) (d x (d (d (d y x) y) (d z x)))))) _t)) ((p68 x z))))).symm
  have p660 (u w x y z : G) : (d (d x (d (d (d y x) y) (d z (d (d (d u w) (d w x)) (d u w))))) x) = (d z (d (d (d u w) (d w x)) (d u w))) := by
    exact (((congrArg (fun _t : G => (d (d x (d (d (d y x) y) (d z (d (d (d u w) (d w x)) (d u w))))) _t)) ((p70 y x (d z (d (d (d u w) (d w x)) (d u w))))))).symm).trans ((p556 u w x (d (d (d y x) y) (d z (d (d (d u w) (d w x)) (d u w)))) z))
  have p781 (u x y z : G) : (d x (d (d (d (d (d (d (d y z) y) u) (d (d (d z x) z) (d z (d (d (d y z) y) u)))) (d (d u (d z (d (d (d y z) y) u))) (d (d z x) z))) (d x (d u (d z (d (d (d y z) y) u))))) (d z x))) = z := by
    exact (((congrArg (fun _t : G => (d x (d (d (d (d (d (d (d y z) y) u) (d (d (d z x) z) (d z (d (d (d y z) y) u)))) (d (d u (d z (d (d (d y z) y) u))) (d (d z x) z))) (d x (d u (d z (d (d (d y z) y) u))))) (d z _t)))) ((p114 x u z (d (d (d y z) y) u))))).symm).trans ((((congrArg (fun _t : G => (d _t (d (d (d (d (d (d (d y z) y) u) (d (d (d z x) z) (d z (d (d (d y z) y) u)))) (d (d u (d z (d (d (d y z) y) u))) (d (d z x) z))) (d x (d u (d z (d (d (d y z) y) u))))) (d z (d (d u (d z (d (d (d y z) y) u))) (d (d (d (d (d (d y z) y) u) (d (d (d z x) z) (d z (d (d (d y z) y) u)))) (d (d u (d z (d (d (d y z) y) u))) (d (d z x) z))) (d x (d u (d z (d (d (d y z) y) u)))))))))) ((p114 x u z (d (d (d y z) y) u))))).symm).trans ((p106 (d (d (d (d (d (d y z) y) u) (d (d (d z x) z) (d z (d (d (d y z) y) u)))) (d (d u (d z (d (d (d y z) y) u))) (d (d z x) z))) (d x (d u (d z (d (d (d y z) y) u))))) u z y)))
  have p946 (u x y z : G) : (d (d (d (d (d x y) x) (d x y)) (d (d x y) (d z (d (d (d u y) x) (d u y))))) (d (d (d x y) x) (d x y))) = (d z (d (d (d u y) x) (d u y))) := by
    exact ((((congrArg (fun _t : G => (d (d (d (d (d x y) x) (d x y)) (d (d x y) (d z (d (d (d u y) x) _t)))) (d (d (d x y) x) (d x y)))) ((p65 x y u)))).symm).trans ((p557 (d u y) x (d (d x y) x) (d x y) z))).trans ((congrArg (fun _t : G => (d z (d (d (d u y) x) _t))) ((p65 x y u))))
  have p1057 (u x y z : G) : (d (d (d (d (d x y) x) (d x y)) (d (d (d (d z (d u x)) z) y) x)) (d (d u x) (d (d (d z (d u x)) z) y))) = (d y (d (d u x) (d (d (d z (d u x)) z) y))) := by
    exact ((((p194 u x y (d (d z (d u x)) z))).symm).symm).trans ((p109 (d u x) z y))
  have p1071 (x y z : G) : (d (d (d (d x y) z) (d (d y (d (d (d x y) z) (d z y))) (d (d (d (d x y) z) (d x y)) (d (d x y) z)))) (d (d z y) z)) = y := by
    exact ((((p55 z y)).symm).trans ((((p54 z (d z y))).symm).trans (((p54 z (d z y))).trans ((congrArg (fun _t : G => (d _t (d (d z y) z))) (((p261 x y z)).symm)))))).symm
  have p1072 (x y z : G) : (d x (d (d (d y x) z) (d (d x (d (d (d y x) z) (d z x))) (d (d (d (d y x) z) (d y x)) (d (d y x) z))))) = z := by
    exact (((((p68 x z)).symm).trans ((((congrArg (fun _t : G => (d _t (d (d (d z x) z) (d z x)))) ((p55 z x)))).symm).trans ((((p54 (d z x) (d (d z x) z))).symm).trans (((p54 (d z x) (d (d z x) z))).trans ((congrArg (fun _t : G => (d (d (d (d (d z x) z) (d z x)) (d (d z x) z)) _t)) (((p261 y x z)).symm))))))).trans ((congrArg (fun _t : G => (d _t (d (d (d y x) z) (d (d x (d (d (d y x) z) (d z x))) (d (d (d (d y x) z) (d y x)) (d (d y x) z)))))) ((p55 z x))))).symm
  have p1117 (x y z : G) : (d x (d y (d (d x (d y (d (d (d (d y (d z x)) y) (d y (d z x))) x))) (d (d y (d z x)) y)))) = (d (d (d y (d z x)) y) (d y (d z x))) := by
    exact (((congrArg (fun _t : G => (d x (d y (d (d x (d y (d (d (d (d y (d z x)) y) (d y (d z x))) x))) (d (d y (d z x)) _t))))) ((p68 (d z x) y)))).symm).trans ((((congrArg (fun _t : G => (d x (d y (d (d x (d y (d (d (d (d y (d z x)) y) (d y (d z x))) x))) (d (d _t (d z x)) (d (d z x) (d (d (d y (d z x)) y) (d y (d z x))))))))) ((p68 (d z x) y)))).symm).trans ((((congrArg (fun _t : G => (d x (d y (d (d x (d _t (d (d (d (d y (d z x)) y) (d y (d z x))) x))) (d (d (d (d z x) (d (d (d y (d z x)) y) (d y (d z x)))) (d z x)) (d (d z x) (d (d (d y (d z x)) y) (d y (d z x))))))))) ((p68 (d z x) y)))).symm).trans ((((congrArg (fun _t : G => (d x (d _t (d (d x (d (d (d z x) (d (d (d y (d z x)) y) (d y (d z x)))) (d (d (d (d y (d z x)) y) (d y (d z x))) x))) (d (d (d (d z x) (d (d (d y (d z x)) y) (d y (d z x)))) (d z x)) (d (d z x) (d (d (d y (d z x)) y) (d y (d z x))))))))) ((p68 (d z x) y)))).symm).trans ((p1072 x z (d (d (d y (d z x)) y) (d y (d z x))))))))
  have p1118 (x y z : G) : (d (d (d x y) x) (d (d y z) (d (d (d (d x y) x) (d (d y z) (d z (d (d x y) x)))) (d (d (d y z) y) (d y z))))) = z := by
    exact (((congrArg (fun _t : G => (d (d (d x y) x) (d (d y z) (d (d (d (d x y) x) (d (d y z) (d z (d (d x y) x)))) (d (d (d y z) y) (d _t z)))))) ((p55 x y)))).symm).trans ((((congrArg (fun _t : G => (d (d (d x y) x) (d (d y z) (d (d (d (d x y) x) (d (d y z) (d z (d (d x y) x)))) (d (d (d y z) _t) (d (d (d (d (d x y) x) (d x y)) (d (d x y) x)) z)))))) ((p55 x y)))).symm).trans ((((congrArg (fun _t : G => (d (d (d x y) x) (d (d y z) (d (d (d (d x y) x) (d (d y z) (d z (d (d x y) x)))) (d (d (d _t z) (d (d (d (d x y) x) (d x y)) (d (d x y) x))) (d (d (d (d (d x y) x) (d x y)) (d (d x y) x)) z)))))) ((p55 x y)))).symm).trans ((((congrArg (fun _t : G => (d (d (d x y) x) (d (d y z) (d (d (d (d x y) x) (d (d _t z) (d z (d (d x y) x)))) (d (d (d (d (d (d (d x y) x) (d x y)) (d (d x y) x)) z) (d (d (d (d x y) x) (d x y)) (d (d x y) x))) (d (d (d (d (d x y) x) (d x y)) (d (d x y) x)) z)))))) ((p55 x y)))).symm).trans ((((congrArg (fun _t : G => (d (d (d x y) x) (d (d _t z) (d (d (d (d x y) x) (d (d (d (d (d (d x y) x) (d x y)) (d (d x y) x)) z) (d z (d (d x y) x)))) (d (d (d (d (d (d (d x y) x) (d x y)) (d (d x y) x)) z) (d (d (d (d x y) x) (d x y)) (d (d x y) x))) (d (d (d (d (d x y) x) (d x y)) (d (d x y) x)) z)))))) ((p55 x y)))).symm).trans ((p1072 (d (d x y) x) (d (d (d x y) x) (d x y)) z))))))
  have p1119 (u x y z : G) : (d (d x (d y (d (d (d z y) z) x))) (d (d y u) (d (d (d x (d y (d (d (d z y) z) x))) (d (d y u) (d u (d x (d y (d (d (d z y) z) x)))))) (d (d (d y u) y) (d y u))))) = u := by
    exact (((congrArg (fun _t : G => (d (d x (d y (d (d (d z y) z) x))) (d (d y u) (d (d (d x (d y (d (d (d z y) z) x))) (d (d y u) (d u (d x (d y (d (d (d z y) z) x)))))) (d (d (d y u) y) (d _t u)))))) ((p70 z y x)))).symm).trans ((((congrArg (fun _t : G => (d (d x (d y (d (d (d z y) z) x))) (d (d y u) (d (d (d x (d y (d (d (d z y) z) x))) (d (d y u) (d u (d x (d y (d (d (d z y) z) x)))))) (d (d (d y u) _t) (d (d (d (d (d z y) z) x) (d x (d y (d (d (d z y) z) x)))) u)))))) ((p70 z y x)))).symm).trans ((((congrArg (fun _t : G => (d (d x (d y (d (d (d z y) z) x))) (d (d y u) (d (d (d x (d y (d (d (d z y) z) x))) (d (d y u) (d u (d x (d y (d (d (d z y) z) x)))))) (d (d (d _t u) (d (d (d (d z y) z) x) (d x (d y (d (d (d z y) z) x))))) (d (d (d (d (d z y) z) x) (d x (d y (d (d (d z y) z) x)))) u)))))) ((p70 z y x)))).symm).trans ((((congrArg (fun _t : G => (d (d x (d y (d (d (d z y) z) x))) (d (d y u) (d (d (d x (d y (d (d (d z y) z) x))) (d (d _t u) (d u (d x (d y (d (d (d z y) z) x)))))) (d (d (d (d (d (d (d z y) z) x) (d x (d y (d (d (d z y) z) x)))) u) (d (d (d (d z y) z) x) (d x (d y (d (d (d z y) z) x))))) (d (d (d (d (d z y) z) x) (d x (d y (d (d (d z y) z) x)))) u)))))) ((p70 z y x)))).symm).trans ((((congrArg (fun _t : G => (d (d x (d y (d (d (d z y) z) x))) (d (d _t u) (d (d (d x (d y (d (d (d z y) z) x))) (d (d (d (d (d (d z y) z) x) (d x (d y (d (d (d z y) z) x)))) u) (d u (d x (d y (d (d (d z y) z) x)))))) (d (d (d (d (d (d (d z y) z) x) (d x (d y (d (d (d z y) z) x)))) u) (d (d (d (d z y) z) x) (d x (d y (d (d (d z y) z) x))))) (d (d (d (d (d z y) z) x) (d x (d y (d (d (d z y) z) x)))) u)))))) ((p70 z y x)))).symm).trans ((p1072 (d x (d y (d (d (d z y) z) x))) (d (d (d z y) z) x) u))))))
  have p1128 (x y z : G) : (d (d (d x (d y z)) x) (d (d (d y z) y) (d (d (d (d x (d y z)) x) (d (d (d y z) y) (d y (d (d x (d y z)) x)))) z))) = y := by
    exact (((congrArg (fun _t : G => (d (d (d x (d y z)) x) (d (d (d y z) y) (d (d (d (d x (d y z)) x) (d (d (d y z) y) (d y (d (d x (d y z)) x)))) _t)))) ((p55 y z)))).symm).trans ((p1118 x (d y z) y))
  have p1147 (x y z : G) : (d (d x (d (d y z) (d z x))) (d (d (d y z) y) (d (d (d x (d (d y z) (d z x))) (d (d (d y z) y) (d y (d x (d (d y z) (d z x)))))) z))) = y := by
    exact (((congrArg (fun _t : G => (d (d x (d (d y z) (d z x))) (d (d (d y z) y) (d (d (d x (d (d y z) (d z x))) (d (d (d y z) y) (d y _t))) z)))) ((p26 y z x)))).symm).trans ((((congrArg (fun _t : G => (d (d x (d (d y z) (d z x))) (d (d (d y z) y) (d (d _t (d (d (d y z) y) (d y (d (d (d (d y z) (d z x)) (d y z)) (d (d y z) (d z x)))))) z)))) ((p26 y z x)))).symm).trans ((((congrArg (fun _t : G => (d _t (d (d (d y z) y) (d (d (d (d (d (d y z) (d z x)) (d y z)) (d (d y z) (d z x))) (d (d (d y z) y) (d y (d (d (d (d y z) (d z x)) (d y z)) (d (d y z) (d z x)))))) z)))) ((p26 y z x)))).symm).trans ((p1128 (d (d y z) (d z x)) y z))))
  have p1162 (u x y z : G) : (d (d x (d (d (d (d y z) u) (d y z)) (d (d y z) u))) x) = (d (d x (d (d (d (d u z) u) (d u z)) (d (d y z) u))) x) := by
    exact ((((p5 x a (d x (d (d (d (d u z) u) (d u z)) (d (d y z) u))))).symm).trans ((((congrArg (fun _t : G => (d (d x a) (d a _t))) ((p445 u (d x a) x y z)))).symm).trans ((p5 x a (d x (d (d (d (d y z) u) (d y z)) (d (d y z) u))))))).symm
  have p1186 (u w x y z : G) : (d x (d (d y (d (d (d (d z u) w) (d z u)) (d (d z u) w))) y)) = (d x (d (d y (d (d (d (d w u) w) (d w u)) (d (d z u) w))) y)) := by
    exact (((p6 (d y (d (d (d (d z u) w) (d z u)) (d (d z u) w))) y x)).symm).trans (((p6 (d y (d (d (d (d z u) w) (d z u)) (d (d z u) w))) y x)).trans ((congrArg (fun _t : G => (d x _t)) ((p1162 w y z u)))))
  have p1329 (u w x y z : G) : (d (d x (d (d y (d (d (d (d z u) w) (d z u)) (d (d z u) w))) y)) x) = (d (d x (d (d y (d (d (d (d w u) w) (d w u)) (d (d z u) w))) y)) x) := by
    exact (((p639 (d (d y (d (d (d (d z u) w) (d z u)) (d (d z u) w))) y) a x)).symm).trans (((p639 (d (d y (d (d (d (d z u) w) (d z u)) (d (d z u) w))) y) a x)).trans ((congrArg (fun _t : G => (d _t x)) ((p1186 u w x y z)))))
  have p1539 (u x y z : G) : (d x (d (d (d y x) y) (d (d z (d (d (d u x) y) (d u x))) x))) = (d z (d (d (d u x) y) (d u x))) := by
    exact ((((congrArg (fun _t : G => (d x (d (d (d y x) y) (d _t x)))) ((p946 u y x z)))).symm).trans ((p69 x y (d (d (d (d y x) y) (d y x)) (d (d y x) (d z (d (d (d u x) y) (d u x)))))))).trans ((p946 u y x z))
  have p1557 (u x y z : G) : (d (d (d x y) x) (d (d (d z (d (d x y) x)) z) (d (d u (d (d y z) y)) (d (d x y) x)))) = (d u (d (d y z) y)) := by
    exact (((((congrArg (fun _t : G => (d (d (d x y) x) (d (d (d z (d (d x y) x)) z) (d (d u (d (d y z) _t)) (d (d x y) x))))) ((p55 x y)))).symm).trans ((((congrArg (fun _t : G => (d (d (d x y) x) (d (d (d z (d (d x y) x)) z) (d (d u (d (d _t z) (d (d (d (d x y) x) (d x y)) (d (d x y) x)))) (d (d x y) x))))) ((p55 x y)))).symm).trans ((p1539 (d (d (d x y) x) (d x y)) (d (d x y) x) z u)))).trans ((congrArg (fun _t : G => (d u (d (d _t z) (d (d (d (d x y) x) (d x y)) (d (d x y) x))))) ((p55 x y))))).trans ((congrArg (fun _t : G => (d u (d (d y z) _t))) ((p55 x y))))
  have p1561 (u x y z : G) : (d x (d (d (d (d (d (d y (d (d x z) x)) y) z) x) (d (d (d y (d (d x z) x)) y) z)) (d (d u z) x))) = (d u z) := by
    exact ((((congrArg (fun _t : G => (d x (d (d (d (d (d (d y (d (d x z) x)) y) z) x) (d (d (d y (d (d x z) x)) y) z)) (d (d u _t) x)))) ((p92 x z y)))).symm).trans ((p1539 (d x z) x (d (d (d y (d (d x z) x)) y) z) u))).trans ((congrArg (fun _t : G => (d u _t)) ((p92 x z y))))
  have p1578 (u x y z : G) : (d (d (d (d x (d (d y z) y)) (d (d u y) u)) (d x (d (d y z) y))) (d (d x (d (d y z) y)) (d (d u y) u))) = (d (d (d z (d (d u y) u)) z) (d (d x (d (d y z) y)) (d (d u y) u))) := by
    exact (((congrArg (fun _t : G => (d (d (d (d x (d (d y z) y)) (d (d u y) u)) _t) (d (d x (d (d y z) y)) (d (d u y) u)))) ((p1557 x u y z)))).symm).trans ((p6 (d x (d (d y z) y)) (d (d u y) u) (d (d z (d (d u y) u)) z)))
  have p1600 (u v5 w x y z : G) : (d (d x (d (d (d (d (d y (d (d z x) z)) y) (d (d u (d (d x y) x)) (d (d z x) z))) (d x (d u (d (d x y) x)))) (d (d x w) (d w (d v5 (d x w)))))) x) = (d (d x w) (d w (d v5 (d x w)))) := by
    exact (((congrArg (fun _t : G => (d (d x (d (d (d (d (d y (d (d z x) z)) y) (d (d u (d (d x y) x)) (d (d z x) z))) (d x _t)) (d (d x w) (d w (d v5 (d x w)))))) x)) ((p1557 u z x y)))).symm).trans ((p338 w v5 x (d (d (d y (d (d z x) z)) y) (d (d u (d (d x y) x)) (d (d z x) z))) z))
  have p1631 (x y z : G) : (d (d (d (d (d (d x y) x) (d z y)) (d (d z y) z)) (d (d (d x y) x) (d z y))) y) = (d z y) := by
    exact (((((((congrArg (fun _t : G => (d _t y)) ((p68 y z)))).symm).trans ((((congrArg (fun _t : G => (d (d y _t) y)) ((p1561 (d (d z y) z) (d (d z y) z) x (d z y))))).symm).trans ((p660 (d z y) z y z (d (d (d (d (d x (d (d (d (d z y) z) (d z y)) (d (d z y) z))) x) (d z y)) (d (d z y) z)) (d (d (d x (d (d (d (d z y) z) (d z y)) (d (d z y) z))) x) (d z y))))))).trans ((congrArg (fun _t : G => (d (d (d (d (d (d x _t) x) (d z y)) (d (d z y) z)) (d (d (d x (d (d (d (d z y) z) (d z y)) (d (d z y) z))) x) (d z y))) (d (d (d (d z y) z) (d z y)) (d (d z y) z)))) ((p55 z y))))).trans ((congrArg (fun _t : G => (d (d (d (d (d (d x y) x) (d z y)) (d (d z y) z)) (d (d (d x _t) x) (d z y))) (d (d (d (d z y) z) (d z y)) (d (d z y) z)))) ((p55 z y))))).trans ((congrArg (fun _t : G => (d (d (d (d (d (d x y) x) (d z y)) (d (d z y) z)) (d (d (d x y) x) (d z y))) _t)) ((p55 z y))))).symm
  have p1646 (x y z : G) : (d (d (d (d (d (d x (d (d y z) y)) x) z) y) (d (d (d x (d (d y z) y)) x) z)) (d (d y z) y)) = z := by
    exact ((((congrArg (fun _t : G => (d (d (d (d (d (d x (d (d y z) y)) x) z) y) (d (d (d x (d (d y z) y)) x) _t)) (d (d y z) y))) ((p55 y z)))).symm).trans ((((congrArg (fun _t : G => (d (d (d (d (d (d x (d (d y z) y)) x) z) _t) (d (d (d x (d (d y z) y)) x) (d (d (d (d y z) y) (d y z)) (d (d y z) y)))) (d (d y z) y))) ((p68 z y)))).symm).trans ((((congrArg (fun _t : G => (d (d (d (d (d (d x (d (d y z) y)) x) z) (d _t (d (d (d y z) y) (d y z)))) (d (d (d x (d (d y z) y)) x) (d (d (d (d y z) y) (d y z)) (d (d y z) y)))) (d (d y z) y))) ((p55 y z)))).symm).trans ((((congrArg (fun _t : G => (d (d (d (d (d (d x (d (d y z) y)) x) _t) (d (d (d (d (d y z) y) (d y z)) (d (d y z) y)) (d (d (d y z) y) (d y z)))) (d (d (d x (d (d y z) y)) x) (d (d (d (d y z) y) (d y z)) (d (d y z) y)))) (d (d y z) y))) ((p55 y z)))).symm).trans ((p1631 x (d (d y z) y) (d (d (d y z) y) (d y z)))))))).trans ((p55 y z))
  have p1715 (x y z : G) : (d (d (d (d (d x (d (d y z) y)) x) z) y) (d (d (d x (d (d y z) y)) x) z)) = (d (d (d y z) y) (d (d (d x (d (d y z) y)) x) z)) := by
    exact ((((congrArg (fun _t : G => (d (d (d y z) y) _t)) ((p71 z y (d (d x (d (d y z) y)) x))))).symm).trans ((((congrArg (fun _t : G => (d (d (d y z) y) (d (d _t (d (d (d y z) y) (d (d (d x (d (d y z) y)) x) z))) z))) ((p92 y z x)))).symm).trans ((((congrArg (fun _t : G => (d (d (d y z) y) (d (d (d (d (d (d y z) y) (d (d (d x (d (d y z) y)) x) z)) (d (d y z) y)) (d (d (d y z) y) (d (d (d x (d (d y z) y)) x) z))) _t))) ((p1646 x y z)))).symm).trans ((p65 (d (d y z) y) (d (d (d x (d (d y z) y)) x) z) (d (d (d (d x (d (d y z) y)) x) z) y)))))).symm
  have p1716 (u x y z : G) : (d (d (d (d (d (d x y) x) (d (d z (d (d (d u y) u) (d u z))) y)) (d (d u y) u)) (d (d (d x y) x) (d (d z (d (d (d u y) u) (d u z))) y))) y) = (d (d z (d (d (d u y) u) (d u z))) y) := by
    exact (((congrArg (fun _t : G => (d (d (d (d (d (d x y) x) (d (d z (d (d (d u y) u) (d u z))) y)) (d (d u y) u)) (d (d (d x y) x) (d (d z (d (d (d u y) u) (d u z))) y))) _t)) ((p143 u y z)))).symm).trans ((((congrArg (fun _t : G => (d (d (d (d (d (d x y) x) (d (d z (d (d (d u y) u) (d u z))) y)) (d (d u y) u)) (d (d (d x _t) x) (d (d z (d (d (d u y) u) (d u z))) y))) (d (d (d (d u y) u) (d (d z (d (d (d u y) u) (d u z))) y)) (d (d u y) u)))) ((p143 u y z)))).symm).trans ((((congrArg (fun _t : G => (d (d (d (d (d (d x _t) x) (d (d z (d (d (d u y) u) (d u z))) y)) (d (d u y) u)) (d (d (d x (d (d (d (d u y) u) (d (d z (d (d (d u y) u) (d u z))) y)) (d (d u y) u))) x) (d (d z (d (d (d u y) u) (d u z))) y))) (d (d (d (d u y) u) (d (d z (d (d (d u y) u) (d u z))) y)) (d (d u y) u)))) ((p143 u y z)))).symm).trans ((p1646 x (d (d u y) u) (d (d z (d (d (d u y) u) (d u z))) y)))))
  have p1721 (x y z : G) : (d (d (d (d (d x y) x) (d (d (d z (d (d x y) x)) z) y)) (d (d (d (d z (d (d x y) x)) z) y) x)) (d (d (d x y) x) (d (d (d z (d (d x y) x)) z) y))) = x := by
    exact (((congrArg (fun _t : G => (d (d (d (d (d x y) x) (d (d (d z (d (d x y) x)) z) y)) (d (d (d (d z (d (d x y) x)) z) y) x)) _t)) ((p1715 z x y)))).symm).trans ((((congrArg (fun _t : G => (d (d (d (d (d x y) x) (d (d (d z (d (d x y) x)) z) y)) (d _t x)) (d (d (d (d (d z (d (d x y) x)) z) y) x) (d (d (d z (d (d x y) x)) z) y)))) ((p71 y x (d (d z (d (d x y) x)) z))))).symm).trans ((((congrArg (fun _t : G => (d (d (d (d (d x y) x) (d (d (d z (d (d x y) x)) z) y)) (d (d (d _t (d (d (d x y) x) (d (d (d z (d (d x y) x)) z) y))) y) x)) (d (d (d (d (d z (d (d x y) x)) z) y) x) (d (d (d z (d (d x y) x)) z) y)))) ((p92 x y z)))).symm).trans ((((congrArg (fun _t : G => (d (d _t (d (d (d (d (d (d (d x y) x) (d (d (d z (d (d x y) x)) z) y)) (d (d x y) x)) (d (d (d x y) x) (d (d (d z (d (d x y) x)) z) y))) y) x)) (d (d (d (d (d z (d (d x y) x)) z) y) x) (d (d (d z (d (d x y) x)) z) y)))) ((p1715 z x y)))).symm).trans ((((congrArg (fun _t : G => (d (d (d (d (d (d (d z (d (d x y) x)) z) y) x) (d (d (d z (d (d x y) x)) z) y)) (d (d (d (d (d (d (d x y) x) (d (d (d z (d (d x y) x)) z) y)) (d (d x y) x)) (d (d (d x y) x) (d (d (d z (d (d x y) x)) z) y))) _t) x)) (d (d (d (d (d z (d (d x y) x)) z) y) x) (d (d (d z (d (d x y) x)) z) y)))) ((p1646 z x y)))).symm).trans ((p178 (d (d (d z (d (d x y) x)) z) y) x (d (d x y) x)))))))
  have p1726 (x y z : G) : (d x (d (d (d y x) y) (d (d (d z (d (d y x) y)) z) x))) = y := by
    exact (((congrArg (fun _t : G => (d x _t)) ((p1715 z y x)))).symm).trans ((((congrArg (fun _t : G => (d _t (d (d (d (d (d z (d (d y x) y)) z) x) y) (d (d (d z (d (d y x) y)) z) x)))) ((p92 y x z)))).symm).trans ((((congrArg (fun _t : G => (d (d (d (d (d y x) y) (d (d (d z (d (d y x) y)) z) x)) (d (d _t x) y)) (d (d (d (d (d z (d (d y x) y)) z) x) y) (d (d (d z (d (d y x) y)) z) x)))) ((p1721 y x z)))).symm).trans ((((congrArg (fun _t : G => (d (d (d (d (d y x) y) (d (d (d z (d (d y x) y)) z) x)) (d (d (d (d _t (d (d (d (d z (d (d y x) y)) z) x) y)) (d (d (d y x) y) (d (d (d z (d (d y x) y)) z) x))) x) y)) (d (d (d (d (d z (d (d y x) y)) z) x) y) (d (d (d z (d (d y x) y)) z) x)))) ((p1715 z y x)))).symm).trans ((((congrArg (fun _t : G => (d (d _t (d (d (d (d (d (d (d (d (d z (d (d y x) y)) z) x) y) (d (d (d z (d (d y x) y)) z) x)) (d (d (d (d z (d (d y x) y)) z) x) y)) (d (d (d y x) y) (d (d (d z (d (d y x) y)) z) x))) x) y)) (d (d (d (d (d z (d (d y x) y)) z) x) y) (d (d (d z (d (d y x) y)) z) x)))) ((p1715 z y x)))).symm).trans ((((congrArg (fun _t : G => (d (d (d (d (d (d (d z (d (d y x) y)) z) x) y) (d (d (d z (d (d y x) y)) z) x)) (d (d (d (d (d (d (d (d (d z (d (d y x) y)) z) x) y) (d (d (d z (d (d y x) y)) z) x)) (d (d (d (d z (d (d y x) y)) z) x) y)) (d (d (d y x) y) (d (d (d z (d (d y x) y)) z) x))) _t) y)) (d (d (d (d (d z (d (d y x) y)) z) x) y) (d (d (d z (d (d y x) y)) z) x)))) ((p1646 z y x)))).symm).trans ((p180 (d y x) (d (d (d z (d (d y x) y)) z) x) y y)))))))
  have p1729 (x y z : G) : (d (d (d x y) x) (d (d (d z (d (d x y) x)) z) y)) = (d (d (d x y) x) (d x y)) := by
    exact (((((congrArg (fun _t : G => (d (d (d x y) x) (d _t y))) ((p1726 y x z)))).symm).trans ((((congrArg (fun _t : G => (d (d (d x y) x) (d _t y))) ((p1057 (d x y) x y z)))).symm).trans ((((congrArg (fun _t : G => (d (d (d x y) x) (d (d (d (d (d (d x y) x) (d x y)) (d (d (d (d z (d (d x y) x)) z) y) x)) (d (d (d x y) x) (d (d (d z (d (d x y) x)) z) y))) _t))) ((p1646 z x y)))).symm).trans ((p101 (d (d z (d (d x y) x)) z) (d (d (d (d z (d (d x y) x)) z) y) x) (d x y) x y))))).trans ((p1715 z x y))).symm
  have p1731 (x y z : G) : (d x (d (d (d (d (d y (d (d z x) z)) y) x) z) (d z x))) = z := by
    exact (((((((congrArg (fun _t : G => (d x (d (d (d (d (d y (d (d z x) z)) y) x) z) (d z _t)))) ((p55 z x)))).symm).trans ((((congrArg (fun _t : G => (d x (d (d (d (d (d y (d (d z x) z)) y) x) z) (d z (d _t (d (d z x) z)))))) ((p1729 z x y)))).symm).trans ((((congrArg (fun _t : G => (d x (d (d (d (d (d y (d (d z x) z)) y) x) z) (d z (d _t (d (d z x) z)))))) ((p1715 y z x)))).symm).trans ((((congrArg (fun _t : G => (d x (d (d (d (d (d y (d (d z x) z)) y) x) z) (d _t (d (d (d (d (d (d y (d (d z x) z)) y) x) z) (d (d (d y (d (d z x) z)) y) x)) (d (d z x) z)))))) ((p68 x z)))).symm).trans ((((congrArg (fun _t : G => (d x (d (d (d (d (d y (d (d z x) z)) y) x) z) (d (d x _t) (d (d (d (d (d (d y (d (d z x) z)) y) x) z) (d (d (d y (d (d z x) z)) y) x)) (d (d z x) z)))))) ((p1729 z x y)))).symm).trans ((((congrArg (fun _t : G => (d x (d (d (d (d (d y (d (d z x) z)) y) x) z) (d (d x _t) (d (d (d (d (d (d y (d (d z x) z)) y) x) z) (d (d (d y (d (d z x) z)) y) x)) (d (d z x) z)))))) ((p1715 y z x)))).symm).trans ((((congrArg (fun _t : G => (d x (d (d (d (d (d y (d (d z x) z)) y) x) z) (d (d _t (d (d (d (d (d y (d (d z x) z)) y) x) z) (d (d (d y (d (d z x) z)) y) x))) (d (d (d (d (d (d y (d (d z x) z)) y) x) z) (d (d (d y (d (d z x) z)) y) x)) (d (d z x) z)))))) ((p55 z x)))).symm).trans ((((congrArg (fun _t : G => (d x (d (d (d (d (d y (d (d z x) z)) y) x) z) (d (d (d _t (d (d z x) z)) (d (d (d (d (d y (d (d z x) z)) y) x) z) (d (d (d y (d (d z x) z)) y) x))) (d (d (d (d (d (d y (d (d z x) z)) y) x) z) (d (d (d y (d (d z x) z)) y) x)) (d (d z x) z)))))) ((p1729 z x y)))).symm).trans ((((congrArg (fun _t : G => (d x (d (d (d (d (d y (d (d z x) z)) y) x) z) (d (d (d _t (d (d z x) z)) (d (d (d (d (d y (d (d z x) z)) y) x) z) (d (d (d y (d (d z x) z)) y) x))) (d (d (d (d (d (d y (d (d z x) z)) y) x) z) (d (d (d y (d (d z x) z)) y) x)) (d (d z x) z)))))) ((p1715 y z x)))).symm).trans ((((congrArg (fun _t : G => (d x (d (d (d (d (d y (d (d z x) z)) y) x) _t) (d (d (d (d (d (d (d (d y (d (d z x) z)) y) x) z) (d (d (d y (d (d z x) z)) y) x)) (d (d z x) z)) (d (d (d (d (d y (d (d z x) z)) y) x) z) (d (d (d y (d (d z x) z)) y) x))) (d (d (d (d (d (d y (d (d z x) z)) y) x) z) (d (d (d y (d (d z x) z)) y) x)) (d (d z x) z)))))) ((p68 x z)))).symm).trans ((((congrArg (fun _t : G => (d x (d (d (d (d (d y (d (d z x) z)) y) x) (d x _t)) (d (d (d (d (d (d (d (d y (d (d z x) z)) y) x) z) (d (d (d y (d (d z x) z)) y) x)) (d (d z x) z)) (d (d (d (d (d y (d (d z x) z)) y) x) z) (d (d (d y (d (d z x) z)) y) x))) (d (d (d (d (d (d y (d (d z x) z)) y) x) z) (d (d (d y (d (d z x) z)) y) x)) (d (d z x) z)))))) ((p1729 z x y)))).symm).trans ((((congrArg (fun _t : G => (d x (d (d (d (d (d y (d (d z x) z)) y) x) (d _t (d (d (d z x) z) (d (d (d y (d (d z x) z)) y) x)))) (d (d (d (d (d (d (d (d y (d (d z x) z)) y) x) z) (d (d (d y (d (d z x) z)) y) x)) (d (d z x) z)) (d (d (d (d (d y (d (d z x) z)) y) x) z) (d (d (d y (d (d z x) z)) y) x))) (d (d (d (d (d (d y (d (d z x) z)) y) x) z) (d (d (d y (d (d z x) z)) y) x)) (d (d z x) z)))))) ((p55 z x)))).symm).trans ((((congrArg (fun _t : G => (d x (d (d (d (d (d y (d (d z x) z)) y) x) (d (d _t (d (d z x) z)) (d (d (d z x) z) (d (d (d y (d (d z x) z)) y) x)))) (d (d (d (d (d (d (d (d y (d (d z x) z)) y) x) z) (d (d (d y (d (d z x) z)) y) x)) (d (d z x) z)) (d (d (d (d (d y (d (d z x) z)) y) x) z) (d (d (d y (d (d z x) z)) y) x))) (d (d (d (d (d (d y (d (d z x) z)) y) x) z) (d (d (d y (d (d z x) z)) y) x)) (d (d z x) z)))))) ((p1729 z x y)))).symm).trans ((((congrArg (fun _t : G => (d x (d (d (d (d (d y (d (d z x) z)) y) x) (d (d _t (d (d z x) z)) (d (d (d z x) z) (d (d (d y (d (d z x) z)) y) x)))) (d (d (d (d (d (d (d (d y (d (d z x) z)) y) x) z) (d (d (d y (d (d z x) z)) y) x)) (d (d z x) z)) (d (d (d (d (d y (d (d z x) z)) y) x) z) (d (d (d y (d (d z x) z)) y) x))) (d (d (d (d (d (d y (d (d z x) z)) y) x) z) (d (d (d y (d (d z x) z)) y) x)) (d (d z x) z)))))) ((p1715 y z x)))).symm).trans ((((congrArg (fun _t : G => (d _t (d (d (d (d (d y (d (d z x) z)) y) x) (d (d (d (d (d (d (d y (d (d z x) z)) y) x) z) (d (d (d y (d (d z x) z)) y) x)) (d (d z x) z)) (d (d (d z x) z) (d (d (d y (d (d z x) z)) y) x)))) (d (d (d (d (d (d (d (d y (d (d z x) z)) y) x) z) (d (d (d y (d (d z x) z)) y) x)) (d (d z x) z)) (d (d (d (d (d y (d (d z x) z)) y) x) z) (d (d (d y (d (d z x) z)) y) x))) (d (d (d (d (d (d y (d (d z x) z)) y) x) z) (d (d (d y (d (d z x) z)) y) x)) (d (d z x) z)))))) ((p1646 y z x)))).symm).trans ((p261 (d (d (d (d y (d (d z x) z)) y) x) z) (d (d (d y (d (d z x) z)) y) x) (d (d z x) z)))))))))))))))))).trans ((congrArg (fun _t : G => (d (d _t (d (d z x) z)) (d (d (d z x) z) (d (d (d y (d (d z x) z)) y) x)))) ((p1729 z x y))))).trans ((congrArg (fun _t : G => (d _t (d (d (d z x) z) (d (d (d y (d (d z x) z)) y) x)))) ((p55 z x))))).trans ((congrArg (fun _t : G => (d x _t)) ((p1729 z x y))))).trans ((p68 x z))
  have p1732 (x y z : G) : (d (d (d (d x (d (d y z) y)) x) z) y) = (d (d y z) y) := by
    exact (((congrArg (fun _t : G => (d (d (d (d x (d (d y z) y)) x) z) _t)) ((p1731 z x y)))).symm).trans ((((congrArg (fun _t : G => (d (d (d (d x (d (d y z) y)) x) z) (d z (d (d (d (d (d x (d (d y z) y)) x) z) y) (d y _t))))) ((p55 y z)))).symm).trans ((((congrArg (fun _t : G => (d (d (d (d x (d (d y z) y)) x) z) (d z (d (d (d (d (d x (d (d y z) y)) x) z) y) (d y (d _t (d (d y z) y))))))) ((p1729 y z x)))).symm).trans ((((congrArg (fun _t : G => (d (d (d (d x (d (d y z) y)) x) z) (d z (d (d (d (d (d x (d (d y z) y)) x) z) y) (d y (d _t (d (d y z) y))))))) ((p1715 x y z)))).symm).trans ((((congrArg (fun _t : G => (d (d (d (d x (d (d y z) y)) x) z) (d z (d (d (d (d (d x (d (d y z) y)) x) z) y) (d _t (d (d (d (d (d (d x (d (d y z) y)) x) z) y) (d (d (d x (d (d y z) y)) x) z)) (d (d y z) y))))))) ((p68 z y)))).symm).trans ((((congrArg (fun _t : G => (d (d (d (d x (d (d y z) y)) x) z) (d z (d (d (d (d (d x (d (d y z) y)) x) z) y) (d (d z _t) (d (d (d (d (d (d x (d (d y z) y)) x) z) y) (d (d (d x (d (d y z) y)) x) z)) (d (d y z) y))))))) ((p1729 y z x)))).symm).trans ((((congrArg (fun _t : G => (d (d (d (d x (d (d y z) y)) x) z) (d z (d (d (d (d (d x (d (d y z) y)) x) z) y) (d (d z _t) (d (d (d (d (d (d x (d (d y z) y)) x) z) y) (d (d (d x (d (d y z) y)) x) z)) (d (d y z) y))))))) ((p1715 x y z)))).symm).trans ((((congrArg (fun _t : G => (d (d (d (d x (d (d y z) y)) x) z) (d z (d (d (d (d (d x (d (d y z) y)) x) z) y) (d (d _t (d (d (d (d (d x (d (d y z) y)) x) z) y) (d (d (d x (d (d y z) y)) x) z))) (d (d (d (d (d (d x (d (d y z) y)) x) z) y) (d (d (d x (d (d y z) y)) x) z)) (d (d y z) y))))))) ((p55 y z)))).symm).trans ((((congrArg (fun _t : G => (d (d (d (d x (d (d y z) y)) x) z) (d z (d (d (d (d (d x (d (d y z) y)) x) z) y) (d (d (d _t (d (d y z) y)) (d (d (d (d (d x (d (d y z) y)) x) z) y) (d (d (d x (d (d y z) y)) x) z))) (d (d (d (d (d (d x (d (d y z) y)) x) z) y) (d (d (d x (d (d y z) y)) x) z)) (d (d y z) y))))))) ((p1729 y z x)))).symm).trans ((((congrArg (fun _t : G => (d (d (d (d x (d (d y z) y)) x) z) (d z (d (d (d (d (d x (d (d y z) y)) x) z) y) (d (d (d _t (d (d y z) y)) (d (d (d (d (d x (d (d y z) y)) x) z) y) (d (d (d x (d (d y z) y)) x) z))) (d (d (d (d (d (d x (d (d y z) y)) x) z) y) (d (d (d x (d (d y z) y)) x) z)) (d (d y z) y))))))) ((p1715 x y z)))).symm).trans ((((congrArg (fun _t : G => (d (d (d (d x (d (d y z) y)) x) z) (d z (d (d (d (d (d x (d (d y z) y)) x) z) _t) (d (d (d (d (d (d (d (d x (d (d y z) y)) x) z) y) (d (d (d x (d (d y z) y)) x) z)) (d (d y z) y)) (d (d (d (d (d x (d (d y z) y)) x) z) y) (d (d (d x (d (d y z) y)) x) z))) (d (d (d (d (d (d x (d (d y z) y)) x) z) y) (d (d (d x (d (d y z) y)) x) z)) (d (d y z) y))))))) ((p68 z y)))).symm).trans ((((congrArg (fun _t : G => (d (d (d (d x (d (d y z) y)) x) z) (d z (d (d (d (d (d x (d (d y z) y)) x) z) (d z _t)) (d (d (d (d (d (d (d (d x (d (d y z) y)) x) z) y) (d (d (d x (d (d y z) y)) x) z)) (d (d y z) y)) (d (d (d (d (d x (d (d y z) y)) x) z) y) (d (d (d x (d (d y z) y)) x) z))) (d (d (d (d (d (d x (d (d y z) y)) x) z) y) (d (d (d x (d (d y z) y)) x) z)) (d (d y z) y))))))) ((p1729 y z x)))).symm).trans ((((congrArg (fun _t : G => (d (d (d (d x (d (d y z) y)) x) z) (d z (d (d (d (d (d x (d (d y z) y)) x) z) (d _t (d (d (d y z) y) (d (d (d x (d (d y z) y)) x) z)))) (d (d (d (d (d (d (d (d x (d (d y z) y)) x) z) y) (d (d (d x (d (d y z) y)) x) z)) (d (d y z) y)) (d (d (d (d (d x (d (d y z) y)) x) z) y) (d (d (d x (d (d y z) y)) x) z))) (d (d (d (d (d (d x (d (d y z) y)) x) z) y) (d (d (d x (d (d y z) y)) x) z)) (d (d y z) y))))))) ((p55 y z)))).symm).trans ((((congrArg (fun _t : G => (d (d (d (d x (d (d y z) y)) x) z) (d z (d (d (d (d (d x (d (d y z) y)) x) z) (d (d _t (d (d y z) y)) (d (d (d y z) y) (d (d (d x (d (d y z) y)) x) z)))) (d (d (d (d (d (d (d (d x (d (d y z) y)) x) z) y) (d (d (d x (d (d y z) y)) x) z)) (d (d y z) y)) (d (d (d (d (d x (d (d y z) y)) x) z) y) (d (d (d x (d (d y z) y)) x) z))) (d (d (d (d (d (d x (d (d y z) y)) x) z) y) (d (d (d x (d (d y z) y)) x) z)) (d (d y z) y))))))) ((p1729 y z x)))).symm).trans ((((congrArg (fun _t : G => (d (d (d (d x (d (d y z) y)) x) z) (d z (d (d (d (d (d x (d (d y z) y)) x) z) (d (d _t (d (d y z) y)) (d (d (d y z) y) (d (d (d x (d (d y z) y)) x) z)))) (d (d (d (d (d (d (d (d x (d (d y z) y)) x) z) y) (d (d (d x (d (d y z) y)) x) z)) (d (d y z) y)) (d (d (d (d (d x (d (d y z) y)) x) z) y) (d (d (d x (d (d y z) y)) x) z))) (d (d (d (d (d (d x (d (d y z) y)) x) z) y) (d (d (d x (d (d y z) y)) x) z)) (d (d y z) y))))))) ((p1715 x y z)))).symm).trans ((((congrArg (fun _t : G => (d (d (d (d x (d (d y z) y)) x) z) (d _t (d (d (d (d (d x (d (d y z) y)) x) z) (d (d (d (d (d (d (d x (d (d y z) y)) x) z) y) (d (d (d x (d (d y z) y)) x) z)) (d (d y z) y)) (d (d (d y z) y) (d (d (d x (d (d y z) y)) x) z)))) (d (d (d (d (d (d (d (d x (d (d y z) y)) x) z) y) (d (d (d x (d (d y z) y)) x) z)) (d (d y z) y)) (d (d (d (d (d x (d (d y z) y)) x) z) y) (d (d (d x (d (d y z) y)) x) z))) (d (d (d (d (d (d x (d (d y z) y)) x) z) y) (d (d (d x (d (d y z) y)) x) z)) (d (d y z) y))))))) ((p1646 x y z)))).symm).trans ((p1072 (d (d (d x (d (d y z) y)) x) z) (d (d (d (d x (d (d y z) y)) x) z) y) (d (d y z) y))))))))))))))))))
  have p1733 (x y z : G) : (d (d (d x (d (d y z) y)) x) z) = (d y z) := by
    exact ((((congrArg (fun _t : G => (d y _t)) ((p55 y z)))).symm).trans ((((congrArg (fun _t : G => (d y (d _t (d (d y z) y)))) ((p1729 y z x)))).symm).trans ((((congrArg (fun _t : G => (d _t (d (d (d (d y z) y) (d (d (d x (d (d y z) y)) x) z)) (d (d y z) y)))) ((p68 z y)))).symm).trans ((((congrArg (fun _t : G => (d (d z (d (d (d y z) y) (d y _t))) (d (d (d (d y z) y) (d (d (d x (d (d y z) y)) x) z)) (d (d y z) y)))) ((p55 y z)))).symm).trans ((((congrArg (fun _t : G => (d (d z (d (d (d y z) y) (d y (d _t (d (d y z) y))))) (d (d (d (d y z) y) (d (d (d x (d (d y z) y)) x) z)) (d (d y z) y)))) ((p1729 y z x)))).symm).trans ((((congrArg (fun _t : G => (d (d z (d (d (d y z) y) (d y (d (d _t (d (d (d x (d (d y z) y)) x) z)) (d (d y z) y))))) (d (d (d (d y z) y) (d (d (d x (d (d y z) y)) x) z)) (d (d y z) y)))) ((p1732 x y z)))).symm).trans ((((congrArg (fun _t : G => (d (d z (d (d (d y z) y) (d _t (d (d (d (d (d (d x (d (d y z) y)) x) z) y) (d (d (d x (d (d y z) y)) x) z)) (d (d y z) y))))) (d (d (d (d y z) y) (d (d (d x (d (d y z) y)) x) z)) (d (d y z) y)))) ((p68 z y)))).symm).trans ((((congrArg (fun _t : G => (d (d z (d (d (d y z) y) (d (d z _t) (d (d (d (d (d (d x (d (d y z) y)) x) z) y) (d (d (d x (d (d y z) y)) x) z)) (d (d y z) y))))) (d (d (d (d y z) y) (d (d (d x (d (d y z) y)) x) z)) (d (d y z) y)))) ((p1729 y z x)))).symm).trans ((((congrArg (fun _t : G => (d (d z (d (d (d y z) y) (d (d z (d _t (d (d (d x (d (d y z) y)) x) z))) (d (d (d (d (d (d x (d (d y z) y)) x) z) y) (d (d (d x (d (d y z) y)) x) z)) (d (d y z) y))))) (d (d (d (d y z) y) (d (d (d x (d (d y z) y)) x) z)) (d (d y z) y)))) ((p1732 x y z)))).symm).trans ((((congrArg (fun _t : G => (d (d z (d (d (d y z) y) (d (d _t (d (d (d (d (d x (d (d y z) y)) x) z) y) (d (d (d x (d (d y z) y)) x) z))) (d (d (d (d (d (d x (d (d y z) y)) x) z) y) (d (d (d x (d (d y z) y)) x) z)) (d (d y z) y))))) (d (d (d (d y z) y) (d (d (d x (d (d y z) y)) x) z)) (d (d y z) y)))) ((p55 y z)))).symm).trans ((((congrArg (fun _t : G => (d (d z (d (d (d y z) y) (d (d (d _t (d (d y z) y)) (d (d (d (d (d x (d (d y z) y)) x) z) y) (d (d (d x (d (d y z) y)) x) z))) (d (d (d (d (d (d x (d (d y z) y)) x) z) y) (d (d (d x (d (d y z) y)) x) z)) (d (d y z) y))))) (d (d (d (d y z) y) (d (d (d x (d (d y z) y)) x) z)) (d (d y z) y)))) ((p1729 y z x)))).symm).trans ((((congrArg (fun _t : G => (d (d z (d (d (d y z) y) (d (d (d (d _t (d (d (d x (d (d y z) y)) x) z)) (d (d y z) y)) (d (d (d (d (d x (d (d y z) y)) x) z) y) (d (d (d x (d (d y z) y)) x) z))) (d (d (d (d (d (d x (d (d y z) y)) x) z) y) (d (d (d x (d (d y z) y)) x) z)) (d (d y z) y))))) (d (d (d (d y z) y) (d (d (d x (d (d y z) y)) x) z)) (d (d y z) y)))) ((p1732 x y z)))).symm).trans ((((congrArg (fun _t : G => (d (d z (d _t (d (d (d (d (d (d (d (d x (d (d y z) y)) x) z) y) (d (d (d x (d (d y z) y)) x) z)) (d (d y z) y)) (d (d (d (d (d x (d (d y z) y)) x) z) y) (d (d (d x (d (d y z) y)) x) z))) (d (d (d (d (d (d x (d (d y z) y)) x) z) y) (d (d (d x (d (d y z) y)) x) z)) (d (d y z) y))))) (d (d (d (d y z) y) (d (d (d x (d (d y z) y)) x) z)) (d (d y z) y)))) ((p1732 x y z)))).symm).trans ((((congrArg (fun _t : G => (d (d z (d (d (d (d (d x (d (d y z) y)) x) z) _t) (d (d (d (d (d (d (d (d x (d (d y z) y)) x) z) y) (d (d (d x (d (d y z) y)) x) z)) (d (d y z) y)) (d (d (d (d (d x (d (d y z) y)) x) z) y) (d (d (d x (d (d y z) y)) x) z))) (d (d (d (d (d (d x (d (d y z) y)) x) z) y) (d (d (d x (d (d y z) y)) x) z)) (d (d y z) y))))) (d (d (d (d y z) y) (d (d (d x (d (d y z) y)) x) z)) (d (d y z) y)))) ((p68 z y)))).symm).trans ((((congrArg (fun _t : G => (d (d z (d (d (d (d (d x (d (d y z) y)) x) z) (d z _t)) (d (d (d (d (d (d (d (d x (d (d y z) y)) x) z) y) (d (d (d x (d (d y z) y)) x) z)) (d (d y z) y)) (d (d (d (d (d x (d (d y z) y)) x) z) y) (d (d (d x (d (d y z) y)) x) z))) (d (d (d (d (d (d x (d (d y z) y)) x) z) y) (d (d (d x (d (d y z) y)) x) z)) (d (d y z) y))))) (d (d (d (d y z) y) (d (d (d x (d (d y z) y)) x) z)) (d (d y z) y)))) ((p1729 y z x)))).symm).trans ((((congrArg (fun _t : G => (d (d z (d (d (d (d (d x (d (d y z) y)) x) z) (d _t (d (d (d y z) y) (d (d (d x (d (d y z) y)) x) z)))) (d (d (d (d (d (d (d (d x (d (d y z) y)) x) z) y) (d (d (d x (d (d y z) y)) x) z)) (d (d y z) y)) (d (d (d (d (d x (d (d y z) y)) x) z) y) (d (d (d x (d (d y z) y)) x) z))) (d (d (d (d (d (d x (d (d y z) y)) x) z) y) (d (d (d x (d (d y z) y)) x) z)) (d (d y z) y))))) (d (d (d (d y z) y) (d (d (d x (d (d y z) y)) x) z)) (d (d y z) y)))) ((p55 y z)))).symm).trans ((((congrArg (fun _t : G => (d (d z (d (d (d (d (d x (d (d y z) y)) x) z) (d (d _t (d (d y z) y)) (d (d (d y z) y) (d (d (d x (d (d y z) y)) x) z)))) (d (d (d (d (d (d (d (d x (d (d y z) y)) x) z) y) (d (d (d x (d (d y z) y)) x) z)) (d (d y z) y)) (d (d (d (d (d x (d (d y z) y)) x) z) y) (d (d (d x (d (d y z) y)) x) z))) (d (d (d (d (d (d x (d (d y z) y)) x) z) y) (d (d (d x (d (d y z) y)) x) z)) (d (d y z) y))))) (d (d (d (d y z) y) (d (d (d x (d (d y z) y)) x) z)) (d (d y z) y)))) ((p1729 y z x)))).symm).trans ((((congrArg (fun _t : G => (d (d z (d (d (d (d (d x (d (d y z) y)) x) z) (d (d (d _t (d (d (d x (d (d y z) y)) x) z)) (d (d y z) y)) (d (d (d y z) y) (d (d (d x (d (d y z) y)) x) z)))) (d (d (d (d (d (d (d (d x (d (d y z) y)) x) z) y) (d (d (d x (d (d y z) y)) x) z)) (d (d y z) y)) (d (d (d (d (d x (d (d y z) y)) x) z) y) (d (d (d x (d (d y z) y)) x) z))) (d (d (d (d (d (d x (d (d y z) y)) x) z) y) (d (d (d x (d (d y z) y)) x) z)) (d (d y z) y))))) (d (d (d (d y z) y) (d (d (d x (d (d y z) y)) x) z)) (d (d y z) y)))) ((p1732 x y z)))).symm).trans ((((congrArg (fun _t : G => (d (d _t (d (d (d (d (d x (d (d y z) y)) x) z) (d (d (d (d (d (d (d x (d (d y z) y)) x) z) y) (d (d (d x (d (d y z) y)) x) z)) (d (d y z) y)) (d (d (d y z) y) (d (d (d x (d (d y z) y)) x) z)))) (d (d (d (d (d (d (d (d x (d (d y z) y)) x) z) y) (d (d (d x (d (d y z) y)) x) z)) (d (d y z) y)) (d (d (d (d (d x (d (d y z) y)) x) z) y) (d (d (d x (d (d y z) y)) x) z))) (d (d (d (d (d (d x (d (d y z) y)) x) z) y) (d (d (d x (d (d y z) y)) x) z)) (d (d y z) y))))) (d (d (d (d y z) y) (d (d (d x (d (d y z) y)) x) z)) (d (d y z) y)))) ((p1646 x y z)))).symm).trans ((p1071 (d (d (d (d x (d (d y z) y)) x) z) y) (d (d (d x (d (d y z) y)) x) z) (d (d y z) y)))))))))))))))))))))).symm
  have p1763 (x y z : G) : (d (d x (d (d (d y z) y) (d y x))) z) = (d y z) := by
    exact ((((p1733 (d (d (d a z) a) (d (d x (d (d (d y z) y) (d y x))) z)) y z)).symm).trans ((p1716 y a z x))).symm
  have p1769 (x y z : G) : (d (d x (d (d y z) (d z x))) (d (d (d y z) y) (d y z))) = y := by
    exact (((congrArg (fun _t : G => (d (d x (d (d y z) (d z x))) (d (d (d y z) y) _t))) ((p1763 (d x (d (d y z) (d z x))) y z)))).symm).trans ((p1147 x y z))
  have p1788 (u x y z : G) : (d (d x (d y (d (d (d z y) z) x))) (d (d y u) y)) = u := by
    exact (((congrArg (fun _t : G => (d (d x (d y (d (d (d z y) z) x))) (d (d y u) _t))) ((p1769 (d x (d y (d (d (d z y) z) x))) y u)))).symm).trans ((p1119 u x y z))
  have p1821 (x y z : G) : (d x (d (d (d y x) z) (d y x))) = z := by
    exact (((congrArg (fun _t : G => (d x (d (d (d y x) z) _t))) ((p1769 x (d y x) z)))).symm).trans ((p1072 x y z))
  have p1836 (x y z : G) : (d (d (d x (d y z)) x) (d x (d y z))) = (d z (d x (d y z))) := by
    exact ((((congrArg (fun _t : G => (d z (d x _t))) ((p1788 (d y z) z x (d x (d y z)))))).symm).trans ((p1117 z x y))).symm
  have p1837 (u x y z : G) : (d x (d y (d z (d (d (d u z) u) y)))) = z := by
    exact (((p1821 x z (d x (d y (d z (d (d (d u z) u) y)))))).symm).trans ((((congrArg (fun _t : G => (d x (d (d _t (d x (d y (d z (d (d (d u z) u) y))))) (d z x)))) ((p1763 (d (d (d u z) u) y) z x)))).symm).trans ((((congrArg (fun _t : G => (d x (d (d (d (d (d (d (d u z) u) y) (d (d (d z x) z) (d z (d (d (d u z) u) y)))) _t) (d x (d y (d z (d (d (d u z) u) y))))) (d z x)))) ((p1788 x y z u)))).symm).trans ((p781 y x u z))))
  have p1848 (u x y z : G) : (d (d (d x (d (d y z) y)) x) (d (d u (d (d z x) z)) (d (d y z) y))) = (d y (d (d u (d (d z x) z)) (d (d y z) y))) := by
    exact ((((p1836 (d u (d (d z x) z)) (d y z) y)).symm).trans ((p1578 y u z x))).symm
  have p1932 (u x y z : G) : (d (d (d x (d (d (d y x) y) z)) x) (d x (d u z))) = (d z (d x (d u z))) := by
    exact ((((congrArg (fun _t : G => (d (d (d x (d (d (d y x) y) z)) _t) (d x (d u z)))) ((p1837 y (d u z) z x)))).symm).trans ((p525 u x y z))).trans ((p1836 x u z))
  have p1937 (u w x y z : G) : (d (d (d (d (d (d x y) x) (d x y)) (d (d z y) x)) (d (d u x) (d z y))) w) = (d (d y (d (d u x) (d z y))) w) := by
    exact ((p462 u w x y z)).trans ((congrArg (fun _t : G => (d _t w)) ((p1836 (d u x) z y))))
  have p1945 (u x y z : G) : (d (d x (d (d y z) (d (d x u) x))) (d u (d y z))) = (d z (d u (d y z))) := by
    exact ((((p1937 y (d u (d y z)) z x (d x u))).symm).trans ((p350 y z x u))).trans ((p1836 u y z))
  have p1974 (x y z : G) : (d (d x y) (d y (d z (d x y)))) = z := by
    exact (((congrArg (fun _t : G => (d (d x y) _t)) ((p1932 x z a y)))).symm).trans ((((congrArg (fun _t : G => (d (d x y) (d (d (d z (d (d (d a z) a) y)) _t) (d z (d x y))))) ((p1837 a (d x y) y z)))).symm).trans ((p113 a x y z)))
  have p1976 (x y z : G) : (d (d x (d y z)) x) = z := by
    exact ((((congrArg (fun _t : G => (d (d x (d y _t)) x)) ((p1974 x a z)))).symm).trans ((((congrArg (fun _t : G => (d (d x (d _t (d (d x a) (d a (d z (d x a)))))) x)) ((p1974 (d x a) x y)))).symm).trans ((((congrArg (fun _t : G => (d (d x (d _t (d (d x a) (d a (d z (d x a)))))) x)) ((p1945 x a y (d (d x a) x))))).symm).trans ((((congrArg (fun _t : G => (d (d x (d (d _t (d x (d y (d (d x a) x)))) (d (d x a) (d a (d z (d x a)))))) x)) ((p1848 y a a x)))).symm).trans ((p1600 y z a x a a)))))).trans ((p1974 x a z))
  have p1981 (x y : G) : x = y := by
    exact (((((p1976 a (d x a) x)).symm).trans ((((congrArg (fun _t : G => (d (d a (d (d x _t) x)) a)) ((p1976 (d (d a a) y) a a)))).symm).trans ((p1329 a y a x a)))).trans ((congrArg (fun _t : G => (d (d a _t) a)) ((p1976 x (d (d (d y a) y) (d y a)) (d (d a a) y)))))).trans ((p1976 a (d a a) y))
  exact (p1981 a a).trans (p1981 b a).symm

#print axioms finite_trivial

example (G : Type*) [Magma G] [Finite G]
    (h : ∀ x y z : G, x = y ◇ (((z ◇ y) ◇ x) ◇ (x ◇ y))) :
    ∀ x y : G, x = y := finite_trivial G h

end Equation12294Finite

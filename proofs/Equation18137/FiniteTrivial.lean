import Mathlib.Data.Fintype.Card
import JudgeMagma.Magma

@[reducible] def Equation2 (G : Type _) [Magma G] : Prop := ∀ (x y : G), x = y
@[reducible] def Equation18137 (G : Type _) [Magma G] : Prop := ∀ (x y z : G), x = (y ◇ x) ◇ (z ◇ ((x ◇ z) ◇ z))

theorem finite_trivial (G : Type*) [Magma G] [Finite G] (h : Equation18137 G) : Equation2 G := by
  intro a b
  have ti (a : G) : Function.Injective (fun x : G => (a ◇ x) ◇ x) := by
    intro b c ht
    change (a ◇ b) ◇ b = (a ◇ c) ◇ c at ht
    have p2 (x y z : G) : ((x ◇ y) ◇ (z ◇ ((y ◇ z) ◇ z))) = y := by
      exact (h y x z).symm
    have p3 : ((a ◇ b) ◇ b) = ((a ◇ c) ◇ c) := by
      exact ht
    have p4 : ((a ◇ c) ◇ c) = ((a ◇ b) ◇ b) := by
      exact ((p3)).symm
    have p6 (x y z : G) : (x ◇ (y ◇ (((z ◇ ((x ◇ z) ◇ z)) ◇ y) ◇ y))) = (z ◇ ((x ◇ z) ◇ z)) := by
      exact (((congrArg (fun _t : G => (_t ◇ (y ◇ (((z ◇ ((x ◇ z) ◇ z)) ◇ y) ◇ y)))) ((p2 a x z)))).symm).trans ((p2 (a ◇ x) (z ◇ ((x ◇ z) ◇ z)) y))
    have p8 (x : G) : (((a ◇ b) ◇ b) ◇ (x ◇ ((c ◇ x) ◇ x))) = c := by
      exact (((congrArg (fun _t : G => (_t ◇ (x ◇ ((c ◇ x) ◇ x)))) ((p4)))).symm).trans ((p2 (a ◇ c) c x))
    have p13 (x y z : G) : (x ◇ ((y ◇ ((((x ◇ z) ◇ z) ◇ y) ◇ y)) ◇ (((x ◇ z) ◇ z) ◇ (y ◇ ((((x ◇ z) ◇ z) ◇ y) ◇ y))))) = (z ◇ ((x ◇ z) ◇ z)) := by
      exact (((congrArg (fun _t : G => (x ◇ ((y ◇ ((((x ◇ z) ◇ z) ◇ y) ◇ y)) ◇ (_t ◇ (y ◇ ((((x ◇ z) ◇ z) ◇ y) ◇ y)))))) ((p2 z ((x ◇ z) ◇ z) y)))).symm).trans ((p6 x (y ◇ ((((x ◇ z) ◇ z) ◇ y) ◇ y)) z))
    have p15 (x : G) : (a ◇ (x ◇ (((c ◇ ((a ◇ b) ◇ b)) ◇ x) ◇ x))) = (c ◇ ((a ◇ b) ◇ b)) := by
      exact ((((congrArg (fun _t : G => (a ◇ (x ◇ (((c ◇ _t) ◇ x) ◇ x)))) ((p4)))).symm).trans ((p6 a x c))).trans ((congrArg (fun _t : G => (c ◇ _t)) ((p4))))
    have p26 : (c ◇ ((a ◇ b) ◇ b)) = (b ◇ ((a ◇ b) ◇ b)) := by
      exact ((((p13 a a b)).symm).trans ((((congrArg (fun _t : G => (a ◇ ((a ◇ ((((a ◇ b) ◇ b) ◇ a) ◇ a)) ◇ (_t ◇ (a ◇ ((((a ◇ b) ◇ b) ◇ a) ◇ a)))))) ((p2 c ((a ◇ b) ◇ b) a)))).symm).trans ((p15 (a ◇ ((((a ◇ b) ◇ b) ◇ a) ◇ a)))))).symm
    have p39 : c = b := by
      exact ((((p2 (a ◇ b) b ((a ◇ b) ◇ b))).symm).trans ((((congrArg (fun _t : G => (((a ◇ b) ◇ b) ◇ (((a ◇ b) ◇ b) ◇ (_t ◇ ((a ◇ b) ◇ b))))) ((p26)))).symm).trans ((p8 ((a ◇ b) ◇ b))))).symm
    exact p39.symm
  have ts (a : G) : Function.Surjective (fun x : G => (a ◇ x) ◇ x) :=
    Finite.injective_iff_surjective.mp (ti a)
  let d (x y : G) : G := Classical.choose (ts x y)
  have ld1 (x y : G) : (x ◇ d x y) ◇ d x y = y := Classical.choose_spec (ts x y)
  have p2 (x y z : G) : ((x ◇ y) ◇ (z ◇ ((y ◇ z) ◇ z))) = y := by
    exact (h y x z).symm
  have p3 (x y : G) : ((x ◇ (d x y)) ◇ (d x y)) = y := by
    exact (ld1 x y)
  have p5 (x y z : G) : (x ◇ (y ◇ (((z ◇ ((x ◇ z) ◇ z)) ◇ y) ◇ y))) = (z ◇ ((x ◇ z) ◇ z)) := by
    exact (((congrArg (fun _t : G => (_t ◇ (y ◇ (((z ◇ ((x ◇ z) ◇ z)) ◇ y) ◇ y)))) ((p2 a x z)))).symm).trans ((p2 (a ◇ x) (z ◇ ((x ◇ z) ◇ z)) y))
  have p6 (u x y z : G) : ((x ◇ (y ◇ z)) ◇ ((u ◇ ((z ◇ u) ◇ u)) ◇ (z ◇ (u ◇ ((z ◇ u) ◇ u))))) = (y ◇ z) := by
    exact (((congrArg (fun _t : G => ((x ◇ (y ◇ z)) ◇ ((u ◇ ((z ◇ u) ◇ u)) ◇ (_t ◇ (u ◇ ((z ◇ u) ◇ u)))))) ((p2 y z u)))).symm).trans ((p2 x (y ◇ z) (u ◇ ((z ◇ u) ◇ u))))
  have p7 (x y z : G) : (x ◇ (y ◇ (((d z x) ◇ y) ◇ y))) = (d z x) := by
    exact (((congrArg (fun _t : G => (_t ◇ (y ◇ (((d z x) ◇ y) ◇ y)))) ((p3 z x)))).symm).trans ((p2 (z ◇ (d z x)) (d z x) y))
  have p8 (x y z : G) : ((x ◇ (y ◇ (d y z))) ◇ ((d y z) ◇ (z ◇ (d y z)))) = (y ◇ (d y z)) := by
    exact (((congrArg (fun _t : G => ((x ◇ (y ◇ (d y z))) ◇ ((d y z) ◇ (_t ◇ (d y z))))) ((p3 y z)))).symm).trans ((p2 x (y ◇ (d y z)) (d y z)))
  have p9 (x y z : G) : ((x ◇ y) ◇ ((d y z) ◇ z)) = y := by
    exact (((congrArg (fun _t : G => ((x ◇ y) ◇ ((d y z) ◇ _t))) ((p3 y z)))).symm).trans ((p2 x y (d y z)))
  have p14 (x y z : G) : (x ◇ (y ◇ ((((d x z) ◇ z) ◇ y) ◇ y))) = ((d x z) ◇ z) := by
    exact ((((congrArg (fun _t : G => (x ◇ (y ◇ ((((d x z) ◇ _t) ◇ y) ◇ y)))) ((p3 x z)))).symm).trans ((p5 x y (d x z)))).trans ((congrArg (fun _t : G => ((d x z) ◇ _t)) ((p3 x z))))
  have p18 (u x y z : G) : ((x ◇ (y ◇ z)) ◇ (((d z u) ◇ u) ◇ (z ◇ ((d z u) ◇ u)))) = (y ◇ z) := by
    exact (((congrArg (fun _t : G => ((x ◇ (y ◇ z)) ◇ (((d z u) ◇ u) ◇ (_t ◇ ((d z u) ◇ u))))) ((p9 y z u)))).symm).trans ((p2 x (y ◇ z) ((d z u) ◇ u)))
  have p22 (x y z : G) : (x ◇ ((d ((d x y) ◇ y) z) ◇ z)) = ((d x y) ◇ y) := by
    exact (((congrArg (fun _t : G => (_t ◇ ((d ((d x y) ◇ y) z) ◇ z))) ((p9 a x y)))).symm).trans ((p9 (a ◇ x) ((d x y) ◇ y) z))
  have p43 (x y z : G) : ((d x y) ◇ y) = (x ◇ ((z ◇ ((y ◇ z) ◇ z)) ◇ (y ◇ (z ◇ ((y ◇ z) ◇ z))))) := by
    exact ((((congrArg (fun _t : G => (_t ◇ ((z ◇ ((y ◇ z) ◇ z)) ◇ (y ◇ (z ◇ ((y ◇ z) ◇ z)))))) ((p9 a x y)))).symm).trans ((p6 z (a ◇ x) (d x y) y))).symm
  have p50 (u x y z : G) : (x ◇ (y ◇ ((((z ◇ ((((d x u) ◇ u) ◇ z) ◇ z)) ◇ (((d x u) ◇ u) ◇ (z ◇ ((((d x u) ◇ u) ◇ z) ◇ z)))) ◇ y) ◇ y))) = ((z ◇ ((((d x u) ◇ u) ◇ z) ◇ z)) ◇ (((d x u) ◇ u) ◇ (z ◇ ((((d x u) ◇ u) ◇ z) ◇ z)))) := by
    exact ((((congrArg (fun _t : G => (x ◇ (y ◇ ((((z ◇ ((((d x u) ◇ u) ◇ z) ◇ z)) ◇ (_t ◇ (z ◇ ((((d x u) ◇ u) ◇ z) ◇ z)))) ◇ y) ◇ y)))) ((p14 x z u)))).symm).trans ((p5 x y (z ◇ ((((d x u) ◇ u) ◇ z) ◇ z))))).trans ((congrArg (fun _t : G => ((z ◇ ((((d x u) ◇ u) ◇ z) ◇ z)) ◇ (_t ◇ (z ◇ ((((d x u) ◇ u) ◇ z) ◇ z))))) ((p14 x z u))))
  have p53 (x y z : G) : ((d x y) ◇ y) = (x ◇ (((d y z) ◇ z) ◇ (y ◇ ((d y z) ◇ z)))) := by
    exact ((((congrArg (fun _t : G => (x ◇ (((d y z) ◇ z) ◇ (_t ◇ ((d y z) ◇ z))))) ((p9 (d x y) y z)))).symm).trans ((p14 x ((d y z) ◇ z) y))).symm
  have p59 (u x y z : G) : ((d x (y ◇ z)) ◇ (y ◇ z)) = (x ◇ (((u ◇ ((z ◇ u) ◇ u)) ◇ (z ◇ (u ◇ ((z ◇ u) ◇ u)))) ◇ ((y ◇ z) ◇ ((u ◇ ((z ◇ u) ◇ u)) ◇ (z ◇ (u ◇ ((z ◇ u) ◇ u))))))) := by
    exact ((((congrArg (fun _t : G => (x ◇ (((u ◇ ((z ◇ u) ◇ u)) ◇ (z ◇ (u ◇ ((z ◇ u) ◇ u)))) ◇ (_t ◇ ((u ◇ ((z ◇ u) ◇ u)) ◇ (z ◇ (u ◇ ((z ◇ u) ◇ u)))))))) ((p6 u (d x (y ◇ z)) y z)))).symm).trans ((p14 x ((u ◇ ((z ◇ u) ◇ u)) ◇ (z ◇ (u ◇ ((z ◇ u) ◇ u)))) (y ◇ z)))).symm
  have p89 (u x y z : G) : ((x ◇ y) ◇ (y ◇ (((d z u) ◇ u) ◇ (z ◇ ((d z u) ◇ u))))) = y := by
    exact (((congrArg (fun _t : G => ((x ◇ y) ◇ _t)) ((p53 y z u)))).symm).trans ((p9 x y z))
  have p93 (x y z : G) : (d x y) = (y ◇ (y ◇ ((x ◇ (((d y z) ◇ z) ◇ (y ◇ ((d y z) ◇ z)))) ◇ y))) := by
    exact ((((congrArg (fun _t : G => (y ◇ (y ◇ (_t ◇ y)))) ((p53 x y z)))).symm).trans ((p7 y y x))).symm
  have p123 (u x y z : G) : (x ◇ ((((x ◇ y) ◇ y) ◇ (((d z u) ◇ u) ◇ (z ◇ ((d z u) ◇ u)))) ◇ (((x ◇ y) ◇ y) ◇ (((x ◇ y) ◇ y) ◇ (((d z u) ◇ u) ◇ (z ◇ ((d z u) ◇ u))))))) = (y ◇ ((x ◇ y) ◇ y)) := by
    exact (((congrArg (fun _t : G => (x ◇ ((((x ◇ y) ◇ y) ◇ (((d z u) ◇ u) ◇ (z ◇ ((d z u) ◇ u)))) ◇ (_t ◇ (((x ◇ y) ◇ y) ◇ (((d z u) ◇ u) ◇ (z ◇ ((d z u) ◇ u)))))))) ((p89 u y ((x ◇ y) ◇ y) z)))).symm).trans ((p5 x (((x ◇ y) ◇ y) ◇ (((d z u) ◇ u) ◇ (z ◇ ((d z u) ◇ u)))) y))
  have p141 (u w x y z : G) : ((x ◇ (y ◇ (z ◇ (u ◇ (d u w))))) ◇ ((((d u w) ◇ (w ◇ (d u w))) ◇ ((u ◇ (d u w)) ◇ ((d u w) ◇ (w ◇ (d u w))))) ◇ ((z ◇ (u ◇ (d u w))) ◇ (((d u w) ◇ (w ◇ (d u w))) ◇ ((u ◇ (d u w)) ◇ ((d u w) ◇ (w ◇ (d u w)))))))) = (y ◇ (z ◇ (u ◇ (d u w)))) := by
    exact (((congrArg (fun _t : G => ((x ◇ (y ◇ (z ◇ (u ◇ (d u w))))) ◇ ((((d u w) ◇ (w ◇ (d u w))) ◇ ((u ◇ (d u w)) ◇ ((d u w) ◇ (w ◇ (d u w))))) ◇ ((z ◇ (u ◇ (d u w))) ◇ (((d u w) ◇ (w ◇ (d u w))) ◇ (_t ◇ ((d u w) ◇ (w ◇ (d u w))))))))) ((p8 z u w)))).symm).trans ((((congrArg (fun _t : G => ((x ◇ (y ◇ (z ◇ (u ◇ (d u w))))) ◇ ((((d u w) ◇ (w ◇ (d u w))) ◇ (_t ◇ ((d u w) ◇ (w ◇ (d u w))))) ◇ ((z ◇ (u ◇ (d u w))) ◇ (((d u w) ◇ (w ◇ (d u w))) ◇ (((z ◇ (u ◇ (d u w))) ◇ ((d u w) ◇ (w ◇ (d u w)))) ◇ ((d u w) ◇ (w ◇ (d u w))))))))) ((p8 z u w)))).symm).trans ((p6 ((d u w) ◇ (w ◇ (d u w))) x y (z ◇ (u ◇ (d u w))))))
  have p142 (x y z : G) : ((d x (y ◇ (d y z))) ◇ (y ◇ (d y z))) = (x ◇ (((d y z) ◇ (z ◇ (d y z))) ◇ ((y ◇ (d y z)) ◇ ((d y z) ◇ (z ◇ (d y z)))))) := by
    exact ((((congrArg (fun _t : G => (x ◇ (((d y z) ◇ (z ◇ (d y z))) ◇ (_t ◇ ((d y z) ◇ (z ◇ (d y z))))))) ((p8 (d x (y ◇ (d y z))) y z)))).symm).trans ((p14 x ((d y z) ◇ (z ◇ (d y z))) (y ◇ (d y z))))).symm
  have p148 (u x y z : G) : ((x ◇ y) ◇ ((z ◇ (((y ◇ ((d y u) ◇ u)) ◇ z) ◇ z)) ◇ ((y ◇ ((d y u) ◇ u)) ◇ (z ◇ (((y ◇ ((d y u) ◇ u)) ◇ z) ◇ z))))) = (((d y u) ◇ u) ◇ (y ◇ ((d y u) ◇ u))) := by
    exact (((congrArg (fun _t : G => (_t ◇ ((z ◇ (((y ◇ ((d y u) ◇ u)) ◇ z) ◇ z)) ◇ ((y ◇ ((d y u) ◇ u)) ◇ (z ◇ (((y ◇ ((d y u) ◇ u)) ◇ z) ◇ z)))))) ((p18 u a x y)))).symm).trans ((p6 z (a ◇ (x ◇ y)) ((d y u) ◇ u) (y ◇ ((d y u) ◇ u))))
  have p154 (x y z : G) : ((d (x ◇ (y ◇ z)) z) ◇ z) = (y ◇ z) := by
    exact ((p53 (x ◇ (y ◇ z)) z a)).trans ((p18 a x y z))
  have p186 (x y z : G) : (d (x ◇ (y ◇ z)) z) = (z ◇ (z ◇ ((y ◇ z) ◇ z))) := by
    exact ((((congrArg (fun _t : G => (z ◇ (z ◇ (_t ◇ z)))) ((p154 x y z)))).symm).trans ((p7 z z (x ◇ (y ◇ z))))).symm
  have p187 (x y : G) : ((x ◇ (x ◇ ((y ◇ x) ◇ x))) ◇ x) = (y ◇ x) := by
    exact (((((p9 a (y ◇ x) a)).symm).trans ((((congrArg (fun _t : G => ((a ◇ (y ◇ x)) ◇ ((d _t a) ◇ a))) ((p154 a y x)))).symm).trans ((p22 (a ◇ (y ◇ x)) x a)))).trans ((congrArg (fun _t : G => (_t ◇ x)) ((p186 a y x))))).symm
  have p188 (x y z : G) : ((d x (y ◇ z)) ◇ (y ◇ z)) = (x ◇ (y ◇ z)) := by
    exact ((((congrArg (fun _t : G => (x ◇ _t)) ((p154 (d x (y ◇ z)) y z)))).symm).trans ((p22 x (y ◇ z) z))).symm
  have p190 (x y z : G) : ((x ◇ ((y ◇ x) ◇ x)) ◇ (y ◇ (x ◇ ((y ◇ x) ◇ x)))) = ((z ◇ y) ◇ (y ◇ (x ◇ ((y ◇ x) ◇ x)))) := by
    exact ((((p188 (z ◇ y) y (x ◇ ((y ◇ x) ◇ x)))).symm).trans ((((congrArg (fun _t : G => ((d _t (y ◇ (x ◇ ((y ◇ x) ◇ x)))) ◇ (y ◇ (x ◇ ((y ◇ x) ◇ x))))) ((p6 x a z y)))).symm).trans ((p154 (a ◇ (z ◇ y)) (x ◇ ((y ◇ x) ◇ x)) (y ◇ (x ◇ ((y ◇ x) ◇ x))))))).symm
  have p193 (u x y z : G) : (x ◇ ((y ◇ z) ◇ ((u ◇ (y ◇ z)) ◇ (y ◇ z)))) = (x ◇ (u ◇ (y ◇ z))) := by
    exact ((((((p188 x u (y ◇ z))).symm).trans (((p53 x (u ◇ (y ◇ z)) z)).trans ((congrArg (fun _t : G => (x ◇ (_t ◇ ((u ◇ (y ◇ z)) ◇ ((d (u ◇ (y ◇ z)) z) ◇ z))))) ((p154 u y z)))))).trans ((congrArg (fun _t : G => (x ◇ ((y ◇ z) ◇ ((u ◇ (y ◇ z)) ◇ (_t ◇ z))))) ((p186 u y z))))).trans ((congrArg (fun _t : G => (x ◇ ((y ◇ z) ◇ ((u ◇ (y ◇ z)) ◇ _t)))) ((p187 z y))))).symm
  have p198 (u w x y z : G) : ((x ◇ y) ◇ (y ◇ (z ◇ (u ◇ w)))) = y := by
    exact (((congrArg (fun _t : G => ((x ◇ y) ◇ _t)) ((p193 z y u w)))).symm).trans ((((congrArg (fun _t : G => ((x ◇ y) ◇ (y ◇ ((u ◇ w) ◇ ((z ◇ (u ◇ w)) ◇ _t))))) ((p187 w u)))).symm).trans ((((congrArg (fun _t : G => ((x ◇ y) ◇ (y ◇ ((u ◇ w) ◇ ((z ◇ (u ◇ w)) ◇ (_t ◇ w)))))) ((p186 z u w)))).symm).trans ((((congrArg (fun _t : G => ((x ◇ y) ◇ (y ◇ (_t ◇ ((z ◇ (u ◇ w)) ◇ ((d (z ◇ (u ◇ w)) w) ◇ w)))))) ((p154 z u w)))).symm).trans ((p89 w x y (z ◇ (u ◇ w)))))))
  have p202 (x y z : G) : (x ◇ (((d y z) ◇ (z ◇ (d y z))) ◇ ((y ◇ (d y z)) ◇ ((d y z) ◇ (z ◇ (d y z)))))) = (x ◇ (y ◇ (d y z))) := by
    exact ((((p188 x y (d y z))).symm).trans ((p142 x y z))).symm
  have p203 (u x y z : G) : (x ◇ (((y ◇ ((z ◇ y) ◇ y)) ◇ (z ◇ (y ◇ ((z ◇ y) ◇ y)))) ◇ ((u ◇ z) ◇ ((y ◇ ((z ◇ y) ◇ y)) ◇ (z ◇ (y ◇ ((z ◇ y) ◇ y))))))) = (x ◇ (u ◇ z)) := by
    exact ((((p188 x u z)).symm).trans ((p59 y x u z))).symm
  have p205 (x y : G) : ((x ◇ ((y ◇ x) ◇ x)) ◇ (y ◇ (x ◇ ((y ◇ x) ◇ x)))) = y := by
    exact ((p190 x y a)).trans ((p198 (y ◇ x) x a y x))
  have p208 (u w x y z : G) : ((x ◇ (y ◇ (z ◇ (u ◇ (d u w))))) ◇ ((((d u w) ◇ (w ◇ (d u w))) ◇ ((u ◇ (d u w)) ◇ ((d u w) ◇ (w ◇ (d u w))))) ◇ ((z ◇ (u ◇ (d u w))) ◇ (u ◇ (d u w))))) = (y ◇ (z ◇ (u ◇ (d u w)))) := by
    exact (((congrArg (fun _t : G => ((x ◇ (y ◇ (z ◇ (u ◇ (d u w))))) ◇ ((((d u w) ◇ (w ◇ (d u w))) ◇ ((u ◇ (d u w)) ◇ ((d u w) ◇ (w ◇ (d u w))))) ◇ _t))) ((p202 (z ◇ (u ◇ (d u w))) u w)))).symm).trans ((p141 u w x y z))
  have p211 (x y z : G) : (x ◇ (y ◇ ((z ◇ y) ◇ y))) = (x ◇ (z ◇ y)) := by
    exact (((congrArg (fun _t : G => (x ◇ (y ◇ ((z ◇ y) ◇ _t)))) ((p205 a y)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (_t ◇ ((z ◇ y) ◇ ((a ◇ ((y ◇ a) ◇ a)) ◇ (y ◇ (a ◇ ((y ◇ a) ◇ a)))))))) ((p205 a y)))).symm).trans ((p203 z x a y)))
  have p214 (u x y z : G) : ((x ◇ y) ◇ ((z ◇ (((y ◇ ((d y u) ◇ u)) ◇ z) ◇ z)) ◇ ((y ◇ ((d y u) ◇ u)) ◇ ((y ◇ ((d y u) ◇ u)) ◇ z)))) = (((d y u) ◇ u) ◇ (y ◇ ((d y u) ◇ u))) := by
    exact (((congrArg (fun _t : G => ((x ◇ y) ◇ ((z ◇ (((y ◇ ((d y u) ◇ u)) ◇ z) ◇ z)) ◇ _t))) ((p211 (y ◇ ((d y u) ◇ u)) z (y ◇ ((d y u) ◇ u)))))).symm).trans ((p148 u x y z))
  have p232 (u x y z : G) : (x ◇ (((y ◇ ((((d x z) ◇ z) ◇ y) ◇ y)) ◇ (((d x z) ◇ z) ◇ (((d x z) ◇ z) ◇ y))) ◇ u)) = ((y ◇ ((((d x z) ◇ z) ◇ y) ◇ y)) ◇ (((d x z) ◇ z) ◇ (((d x z) ◇ z) ◇ y))) := by
    exact ((((p211 x u ((y ◇ ((((d x z) ◇ z) ◇ y) ◇ y)) ◇ (((d x z) ◇ z) ◇ (((d x z) ◇ z) ◇ y))))).symm).trans ((((congrArg (fun _t : G => (x ◇ (u ◇ ((((y ◇ ((((d x z) ◇ z) ◇ y) ◇ y)) ◇ _t) ◇ u) ◇ u)))) ((p211 ((d x z) ◇ z) y ((d x z) ◇ z))))).symm).trans ((p50 z x u y)))).trans ((congrArg (fun _t : G => ((y ◇ ((((d x z) ◇ z) ◇ y) ◇ y)) ◇ _t)) ((p211 ((d x z) ◇ z) y ((d x z) ◇ z)))))
  have p236 (x y z : G) : ((d x y) ◇ y) = (x ◇ ((z ◇ ((y ◇ z) ◇ z)) ◇ (y ◇ (y ◇ z)))) := by
    exact ((p43 x y z)).trans ((congrArg (fun _t : G => (x ◇ ((z ◇ ((y ◇ z) ◇ z)) ◇ _t))) ((p211 y z y))))
  have p252 (x y : G) : ((x ◇ ((y ◇ x) ◇ x)) ◇ (y ◇ (y ◇ x))) = y := by
    exact (((congrArg (fun _t : G => ((x ◇ ((y ◇ x) ◇ x)) ◇ _t)) ((p211 y x y)))).symm).trans ((p205 x y))
  have p253 (x y : G) : ((x ◇ (y ◇ x)) ◇ x) = (y ◇ x) := by
    exact (((congrArg (fun _t : G => (_t ◇ x)) ((p211 x x y)))).symm).trans ((p187 x y))
  have p271 (x y z : G) : ((x ◇ y) ◇ (y ◇ z)) = y := by
    exact (((p211 (x ◇ y) z y)).symm).trans ((p2 x y z))
  have p277 (x y : G) : ((d x y) ◇ y) = (x ◇ y) := by
    exact ((p236 x y a)).trans ((congrArg (fun _t : G => (x ◇ _t)) ((p252 a y))))
  have p279 (x y z : G) : (x ◇ ((x ◇ y) ◇ z)) = (x ◇ y) := by
    exact (((((((congrArg (fun _t : G => (x ◇ (_t ◇ z))) ((p252 a (x ◇ y))))).symm).trans ((((congrArg (fun _t : G => (x ◇ (((a ◇ (((x ◇ y) ◇ a) ◇ a)) ◇ ((x ◇ y) ◇ (_t ◇ a))) ◇ z))) ((p277 x y)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (((a ◇ (((x ◇ y) ◇ a) ◇ a)) ◇ (_t ◇ (((d x y) ◇ y) ◇ a))) ◇ z))) ((p277 x y)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (((a ◇ ((_t ◇ a) ◇ a)) ◇ (((d x y) ◇ y) ◇ (((d x y) ◇ y) ◇ a))) ◇ z))) ((p277 x y)))).symm).trans ((p232 z x a y)))))).trans ((congrArg (fun _t : G => ((a ◇ ((_t ◇ a) ◇ a)) ◇ (((d x y) ◇ y) ◇ (((d x y) ◇ y) ◇ a)))) ((p277 x y))))).trans ((congrArg (fun _t : G => ((a ◇ (((x ◇ y) ◇ a) ◇ a)) ◇ (_t ◇ (((d x y) ◇ y) ◇ a)))) ((p277 x y))))).trans ((congrArg (fun _t : G => ((a ◇ (((x ◇ y) ◇ a) ◇ a)) ◇ ((x ◇ y) ◇ (_t ◇ a)))) ((p277 x y))))).trans ((p252 a (x ◇ y)))
  have p284 (x y : G) : ((x ◇ y) ◇ (x ◇ (x ◇ y))) = x := by
    exact ((((((p271 a x (x ◇ y))).symm).trans ((((congrArg (fun _t : G => ((a ◇ x) ◇ _t)) ((p252 a (x ◇ (x ◇ y)))))).symm).trans ((((congrArg (fun _t : G => ((a ◇ x) ◇ ((a ◇ (((x ◇ (x ◇ y)) ◇ a) ◇ a)) ◇ ((x ◇ (x ◇ y)) ◇ ((x ◇ _t) ◇ a))))) ((p277 x y)))).symm).trans ((((congrArg (fun _t : G => ((a ◇ x) ◇ ((a ◇ (((x ◇ (x ◇ y)) ◇ a) ◇ a)) ◇ ((x ◇ _t) ◇ ((x ◇ ((d x y) ◇ y)) ◇ a))))) ((p277 x y)))).symm).trans ((((congrArg (fun _t : G => ((a ◇ x) ◇ ((a ◇ (((x ◇ _t) ◇ a) ◇ a)) ◇ ((x ◇ ((d x y) ◇ y)) ◇ ((x ◇ ((d x y) ◇ y)) ◇ a))))) ((p277 x y)))).symm).trans ((p214 y a x a))))))).trans ((congrArg (fun _t : G => (_t ◇ (x ◇ ((d x y) ◇ y)))) ((p277 x y))))).trans ((congrArg (fun _t : G => ((x ◇ y) ◇ (x ◇ _t))) ((p277 x y))))).symm
  have p286 (u w x y z : G) : ((x ◇ (y ◇ (z ◇ (u ◇ (d u w))))) ◇ ((w ◇ (d u w)) ◇ ((z ◇ (u ◇ (d u w))) ◇ (u ◇ (d u w))))) = (y ◇ (z ◇ (u ◇ (d u w)))) := by
    exact (((congrArg (fun _t : G => ((x ◇ (y ◇ (z ◇ (u ◇ (d u w))))) ◇ (_t ◇ ((z ◇ (u ◇ (d u w))) ◇ (u ◇ (d u w)))))) ((p253 (d u w) w)))).symm).trans ((((congrArg (fun _t : G => ((x ◇ (y ◇ (z ◇ (u ◇ (d u w))))) ◇ ((((d u w) ◇ (w ◇ (d u w))) ◇ _t) ◇ ((z ◇ (u ◇ (d u w))) ◇ (u ◇ (d u w)))))) ((p271 u (d u w) (w ◇ (d u w)))))).symm).trans ((p208 u w x y z)))
  have p287 (x y z : G) : (x ◇ (y ◇ (d z y))) = (x ◇ (z ◇ (d z y))) := by
    exact (((congrArg (fun _t : G => (x ◇ _t)) ((p253 (d z y) y)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (((d z y) ◇ (y ◇ (d z y))) ◇ _t))) ((p271 z (d z y) (y ◇ (d z y)))))).symm).trans ((p202 x z y)))
  have p293 (x y : G) : (x ◇ ((y ◇ x) ◇ x)) = (y ◇ x) := by
    exact ((((p279 y x x)).symm).trans ((((congrArg (fun _t : G => (y ◇ _t)) ((p284 ((y ◇ x) ◇ x) a)))).symm).trans ((((congrArg (fun _t : G => (y ◇ ((((y ◇ x) ◇ x) ◇ a) ◇ (((y ◇ x) ◇ x) ◇ (((y ◇ x) ◇ x) ◇ _t))))) ((p284 a a)))).symm).trans ((((congrArg (fun _t : G => (y ◇ ((((y ◇ x) ◇ x) ◇ a) ◇ (((y ◇ x) ◇ x) ◇ (((y ◇ x) ◇ x) ◇ ((a ◇ a) ◇ (a ◇ _t))))))) ((p277 a a)))).symm).trans ((((congrArg (fun _t : G => (y ◇ ((((y ◇ x) ◇ x) ◇ a) ◇ (((y ◇ x) ◇ x) ◇ (((y ◇ x) ◇ x) ◇ (_t ◇ (a ◇ ((d a a) ◇ a)))))))) ((p277 a a)))).symm).trans ((((congrArg (fun _t : G => (y ◇ ((((y ◇ x) ◇ x) ◇ _t) ◇ (((y ◇ x) ◇ x) ◇ (((y ◇ x) ◇ x) ◇ (((d a a) ◇ a) ◇ (a ◇ ((d a a) ◇ a)))))))) ((p284 a a)))).symm).trans ((((congrArg (fun _t : G => (y ◇ ((((y ◇ x) ◇ x) ◇ ((a ◇ a) ◇ (a ◇ _t))) ◇ (((y ◇ x) ◇ x) ◇ (((y ◇ x) ◇ x) ◇ (((d a a) ◇ a) ◇ (a ◇ ((d a a) ◇ a)))))))) ((p277 a a)))).symm).trans ((((congrArg (fun _t : G => (y ◇ ((((y ◇ x) ◇ x) ◇ (_t ◇ (a ◇ ((d a a) ◇ a)))) ◇ (((y ◇ x) ◇ x) ◇ (((y ◇ x) ◇ x) ◇ (((d a a) ◇ a) ◇ (a ◇ ((d a a) ◇ a)))))))) ((p277 a a)))).symm).trans ((p123 a y x a)))))))))).symm
  have p296 (x y : G) : (d x y) = (y ◇ (x ◇ y)) := by
    exact (((((p93 x y a)).trans ((congrArg (fun _t : G => (y ◇ (y ◇ ((x ◇ (_t ◇ (y ◇ ((d y a) ◇ a)))) ◇ y)))) ((p277 y a))))).trans ((congrArg (fun _t : G => (y ◇ (y ◇ ((x ◇ ((y ◇ a) ◇ (y ◇ _t))) ◇ y)))) ((p277 y a))))).trans ((congrArg (fun _t : G => (y ◇ (y ◇ ((x ◇ _t) ◇ y)))) ((p284 y a))))).trans ((congrArg (fun _t : G => (y ◇ _t)) ((p293 y x))))
  have p298 (x y z : G) : (x ◇ (y ◇ (z ◇ (y ◇ z)))) = (x ◇ (z ◇ (z ◇ (y ◇ z)))) := by
    exact (((((congrArg (fun _t : G => (x ◇ (z ◇ _t))) ((p296 y z)))).symm).trans ((p287 x z y))).trans ((congrArg (fun _t : G => (x ◇ (y ◇ _t))) ((p296 y z))))).symm
  have p299 (u w x y z : G) : ((x ◇ (y ◇ (z ◇ (u ◇ (w ◇ (u ◇ w)))))) ◇ ((w ◇ (w ◇ (u ◇ w))) ◇ ((z ◇ (u ◇ (w ◇ (u ◇ w)))) ◇ (u ◇ (w ◇ (u ◇ w)))))) = (y ◇ (z ◇ (u ◇ (w ◇ (u ◇ w))))) := by
    exact ((((congrArg (fun _t : G => ((x ◇ (y ◇ (z ◇ (u ◇ (w ◇ (u ◇ w)))))) ◇ ((w ◇ (w ◇ (u ◇ w))) ◇ ((z ◇ (u ◇ (w ◇ (u ◇ w)))) ◇ (u ◇ _t))))) ((p296 u w)))).symm).trans ((((congrArg (fun _t : G => ((x ◇ (y ◇ (z ◇ (u ◇ (w ◇ (u ◇ w)))))) ◇ ((w ◇ (w ◇ (u ◇ w))) ◇ ((z ◇ (u ◇ _t)) ◇ (u ◇ (d u w)))))) ((p296 u w)))).symm).trans ((((congrArg (fun _t : G => ((x ◇ (y ◇ (z ◇ (u ◇ (w ◇ (u ◇ w)))))) ◇ ((w ◇ _t) ◇ ((z ◇ (u ◇ (d u w))) ◇ (u ◇ (d u w)))))) ((p296 u w)))).symm).trans ((((congrArg (fun _t : G => ((x ◇ (y ◇ (z ◇ (u ◇ _t)))) ◇ ((w ◇ (d u w)) ◇ ((z ◇ (u ◇ (d u w))) ◇ (u ◇ (d u w)))))) ((p296 u w)))).symm).trans ((p286 u w x y z)))))).trans ((congrArg (fun _t : G => (y ◇ (z ◇ (u ◇ _t)))) ((p296 u w))))
  have p303 (x y z : G) : ((x ◇ y) ◇ (x ◇ z)) = x := by
    exact ((((congrArg (fun _t : G => ((x ◇ y) ◇ (_t ◇ z))) ((p284 x y)))).symm).trans ((p279 (x ◇ y) (x ◇ (x ◇ y)) z))).trans ((p284 x y))
  have p304 (x y : G) : (x ◇ y) = (x ◇ x) := by
    exact ((((congrArg (fun _t : G => (x ◇ _t)) ((p284 x y)))).symm).trans ((p279 x y (x ◇ (x ◇ y))))).symm
  have p307 (u w x y z : G) : ((x ◇ (y ◇ (z ◇ (u ◇ (w ◇ w))))) ◇ w) = (y ◇ (z ◇ (u ◇ (w ◇ w)))) := by
    exact ((((congrArg (fun _t : G => ((x ◇ (y ◇ (z ◇ (u ◇ (w ◇ w))))) ◇ _t)) ((p303 w w w)))).symm).trans ((((congrArg (fun _t : G => ((x ◇ (y ◇ (z ◇ (u ◇ (w ◇ w))))) ◇ _t)) ((p304 (w ◇ w) ((z ◇ (u ◇ (w ◇ w))) ◇ (u ◇ (w ◇ w))))))).symm).trans ((((congrArg (fun _t : G => ((x ◇ (y ◇ (z ◇ (u ◇ (w ◇ w))))) ◇ ((w ◇ w) ◇ ((z ◇ (u ◇ (w ◇ w))) ◇ (u ◇ _t))))) ((p304 w (u ◇ w))))).symm).trans ((((congrArg (fun _t : G => ((x ◇ (y ◇ (z ◇ (u ◇ (w ◇ w))))) ◇ ((w ◇ w) ◇ ((z ◇ (u ◇ _t)) ◇ (u ◇ (w ◇ (u ◇ w))))))) ((p304 w (u ◇ w))))).symm).trans ((((congrArg (fun _t : G => ((x ◇ (y ◇ (z ◇ (u ◇ (w ◇ w))))) ◇ (_t ◇ ((z ◇ (u ◇ (w ◇ (u ◇ w)))) ◇ (u ◇ (w ◇ (u ◇ w))))))) ((p304 w (w ◇ w))))).symm).trans ((((congrArg (fun _t : G => ((x ◇ (y ◇ (z ◇ (u ◇ (w ◇ w))))) ◇ ((w ◇ _t) ◇ ((z ◇ (u ◇ (w ◇ (u ◇ w)))) ◇ (u ◇ (w ◇ (u ◇ w))))))) ((p304 w (u ◇ w))))).symm).trans ((((congrArg (fun _t : G => ((x ◇ (y ◇ (z ◇ (u ◇ _t)))) ◇ ((w ◇ (w ◇ (u ◇ w))) ◇ ((z ◇ (u ◇ (w ◇ (u ◇ w)))) ◇ (u ◇ (w ◇ (u ◇ w))))))) ((p304 w (u ◇ w))))).symm).trans ((p299 u w x y z))))))))).trans ((congrArg (fun _t : G => (y ◇ (z ◇ (u ◇ _t)))) ((p304 w (u ◇ w)))))
  have p308 (x y z : G) : (x ◇ (y ◇ (z ◇ z))) = (x ◇ (z ◇ z)) := by
    exact (((((congrArg (fun _t : G => (x ◇ (y ◇ _t))) ((p304 z (y ◇ z))))).symm).trans ((p298 x y z))).trans ((congrArg (fun _t : G => (x ◇ (z ◇ _t))) ((p304 z (y ◇ z)))))).trans ((congrArg (fun _t : G => (x ◇ _t)) ((p304 z (z ◇ z)))))
  have p311 (x y : G) : (x ◇ y) = (y ◇ y) := by
    exact ((((p304 y ((x ◇ y) ◇ y))).symm).trans ((p293 y x))).symm
  have p312 (x y : G) : (x ◇ (y ◇ y)) = (y ◇ y) := by
    exact ((((((p311 (a ◇ (y ◇ y)) y)).symm).trans ((((congrArg (fun _t : G => (_t ◇ y)) ((p308 a x y)))).symm).trans ((((congrArg (fun _t : G => ((a ◇ _t) ◇ y)) ((p308 x a y)))).symm).trans ((((congrArg (fun _t : G => ((a ◇ (x ◇ _t)) ◇ y)) ((p308 a a y)))).symm).trans ((p307 a y a x a)))))).trans ((congrArg (fun _t : G => (x ◇ _t)) ((p308 a a y))))).trans ((p308 x a y))).symm
  have p314 (x : G) : (x ◇ x) = x := by
    exact (((p312 (a ◇ x) x)).symm).trans ((((congrArg (fun _t : G => ((a ◇ x) ◇ _t)) ((p304 x a)))).symm).trans ((p271 a x a)))
  have p315 (x y : G) : (x ◇ y) = y := by
    exact (((p314 (x ◇ y))).symm).trans ((((p304 (x ◇ y) (y ◇ a))).symm).trans ((p271 x y a)))
  have p316 (x y : G) : x = y := by
    exact (((p315 a x)).symm).trans ((((congrArg (fun _t : G => (a ◇ _t)) ((p315 y x)))).symm).trans ((((congrArg (fun _t : G => (_t ◇ (y ◇ x))) ((p315 y a)))).symm).trans ((((congrArg (fun _t : G => (_t ◇ (y ◇ x))) (((p304 y a)).symm))).symm).trans ((p271 y y x)))))
  exact (p316 a a).trans (p316 b a).symm

#print axioms finite_trivial

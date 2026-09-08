import Mathlib.Data.Fintype.Card
import JudgeMagma.Magma

@[reducible] def Equation2 (G : Type _) [Magma G] : Prop := ∀ (x y : G), x = y
@[reducible] def Equation20911 (G : Type _) [Magma G] : Prop := ∀ (x y z : G), x = (y ◇ y) ◇ (((z ◇ x) ◇ x) ◇ z)

theorem left_injective (G : Type*) [Magma G] [Finite G] (h : Equation20911 G) (a : G) :
    Function.Injective (fun x : G => a ◇ x) := by
  intro b c ht
  have ls (y : G) : Function.Surjective (fun t : G => (y ◇ y) ◇ t) := by
    intro x
    exact ⟨(((a ◇ x) ◇ x) ◇ a), (h x y a).symm⟩
  have li (y : G) : Function.Injective (fun t : G => (y ◇ y) ◇ t) :=
    Finite.injective_iff_surjective.mpr (ls y)
  let d (x y : G) : G := Classical.choose (ls x y)
  have ld1 (x y : G) : (x ◇ x) ◇ d x y = y := Classical.choose_spec (ls x y)
  have ld2 (x y : G) : d x ((x ◇ x) ◇ y) = y := li x (ld1 x ((x ◇ x) ◇ y))
  have rs (t : G) : Function.Surjective (fun w : G => w ◇ t) := by
    have ti : Function.Injective (fun x : G => (((t ◇ x) ◇ x) ◇ t)) := by
      intro u v huv
      change (((t ◇ u) ◇ u) ◇ t) = (((t ◇ v) ◇ v) ◇ t) at huv
      calc u = ((a ◇ a) ◇ (((t ◇ u) ◇ u) ◇ t)) := h u a t
           _ = ((a ◇ a) ◇ (((t ◇ v) ◇ v) ◇ t)) := by rw [huv]
           _ = v := (h v a t).symm
    intro u
    obtain ⟨x, hx⟩ := (Finite.injective_iff_surjective.mp ti) u
    exact ⟨((t ◇ x) ◇ x), hx⟩
  have ri (y : G) : Function.Injective (fun t : G => t ◇ y) :=
    Finite.injective_iff_surjective.mpr (rs y)
  let r (x y : G) : G := Classical.choose (rs y x)
  have rd1 (x y : G) : r x y ◇ y = x := Classical.choose_spec (rs y x)
  have rd2 (x y : G) : r (x ◇ y) y = x := ri y (rd1 (x ◇ y) y)
  have p2 (x y z : G) : ((x ◇ x) ◇ (((y ◇ z) ◇ z) ◇ y)) = z := by
    exact (h z x y).symm
  have p4 (x y : G) : (d x ((x ◇ x) ◇ y)) = y := by
    exact (ld2 x y)
  have p6 (x y : G) : (r (x ◇ y) y) = x := by
    exact (rd2 x y)
  have p7 : (a ◇ b) = (a ◇ c) := by
    exact ht
  have p8 : (a ◇ c) = (a ◇ b) := by
    exact ((p7)).symm
  have p13 (x y z : G) : (d x y) = (((z ◇ y) ◇ y) ◇ z) := by
    exact (((congrArg (fun _t : G => (d x _t)) ((p2 x z y)))).symm).trans ((p4 x (((z ◇ y) ◇ y) ◇ z)))
  have p18 : (r (a ◇ b) c) = a := by
    exact (((congrArg (fun _t : G => (r _t c)) ((p8)))).symm).trans ((p6 a c))
  have p37 (x y z : G) : (r (d x y) z) = ((z ◇ y) ◇ y) := by
    exact (((congrArg (fun _t : G => (r _t z)) (((p13 x y z)).symm))).symm).trans ((p6 ((z ◇ y) ◇ y) z))
  have p48 (x y z : G) : (d x y) = (d z y) := by
    exact ((p13 x y a)).trans (((p13 z y a)).symm)
  have p57 (x y z : G) : (d x ((y ◇ y) ◇ z)) = z := by
    exact (((p48 y ((y ◇ y) ◇ z) x)).symm).trans ((p4 y z))
  have p154 (x y z : G) : (r x y) = ((y ◇ ((z ◇ z) ◇ x)) ◇ ((z ◇ z) ◇ x)) := by
    exact (((congrArg (fun _t : G => (r _t y)) ((p57 a z x)))).symm).trans ((p37 a ((z ◇ z) ◇ x) y))
  have p1148 (x y z : G) : (r (r x y) ((z ◇ z) ◇ x)) = (y ◇ ((z ◇ z) ◇ x)) := by
    exact (((congrArg (fun _t : G => (r _t ((z ◇ z) ◇ x))) (((p154 x y z)).symm))).symm).trans ((p6 (y ◇ ((z ◇ z) ◇ x)) ((z ◇ z) ◇ x)))
  have p1586 (x y z : G) : (r x ((y ◇ y) ◇ (x ◇ z))) = (z ◇ ((y ◇ y) ◇ (x ◇ z))) := by
    exact (((congrArg (fun _t : G => (r _t ((y ◇ y) ◇ (x ◇ z)))) ((p6 x z)))).symm).trans ((p1148 (x ◇ z) z y))
  have p1587 (x : G) : (c ◇ ((x ◇ x) ◇ (a ◇ b))) = (b ◇ ((x ◇ x) ◇ (a ◇ b))) := by
    exact ((((p1586 a x b)).symm).trans ((((congrArg (fun _t : G => (r _t ((x ◇ x) ◇ (a ◇ b)))) ((p18)))).symm).trans ((p1148 (a ◇ b) c x)))).symm
  have p3757 : c = b := by
    exact ((((p6 b ((a ◇ a) ◇ (a ◇ b)))).symm).trans ((((congrArg (fun _t : G => (r _t ((a ◇ a) ◇ (a ◇ b)))) ((p1587 a)))).symm).trans ((p6 c ((a ◇ a) ◇ (a ◇ b)))))).symm
  exact p3757.symm

theorem right_injective (G : Type*) [Magma G] [Finite G] (h : Equation20911 G) (a : G) :
    Function.Injective (fun x : G => x ◇ a) := by
  have ls (y : G) : Function.Surjective (fun t : G => (y ◇ y) ◇ t) := by
    intro x
    exact ⟨(((a ◇ x) ◇ x) ◇ a), (h x y a).symm⟩
  have li (y : G) : Function.Injective (fun t : G => (y ◇ y) ◇ t) :=
    Finite.injective_iff_surjective.mpr (ls y)
  let d (x y : G) : G := Classical.choose (ls x y)
  have ld1 (x y : G) : (x ◇ x) ◇ d x y = y := Classical.choose_spec (ls x y)
  have ld2 (x y : G) : d x ((x ◇ x) ◇ y) = y := li x (ld1 x ((x ◇ x) ◇ y))
  have rs (t : G) : Function.Surjective (fun w : G => w ◇ t) := by
    have ti : Function.Injective (fun x : G => (((t ◇ x) ◇ x) ◇ t)) := by
      intro u v huv
      change (((t ◇ u) ◇ u) ◇ t) = (((t ◇ v) ◇ v) ◇ t) at huv
      calc u = ((a ◇ a) ◇ (((t ◇ u) ◇ u) ◇ t)) := h u a t
           _ = ((a ◇ a) ◇ (((t ◇ v) ◇ v) ◇ t)) := by rw [huv]
           _ = v := (h v a t).symm
    intro u
    obtain ⟨x, hx⟩ := (Finite.injective_iff_surjective.mp ti) u
    exact ⟨((t ◇ x) ◇ x), hx⟩
  have ri (y : G) : Function.Injective (fun t : G => t ◇ y) :=
    Finite.injective_iff_surjective.mpr (rs y)
  let r (x y : G) : G := Classical.choose (rs y x)
  have rd1 (x y : G) : r x y ◇ y = x := Classical.choose_spec (rs y x)
  have rd2 (x y : G) : r (x ◇ y) y = x := ri y (rd1 (x ◇ y) y)
  exact ri a

theorem common_square (G : Type*) [Magma G] [Finite G] (h : Equation20911 G) :
    ∀ a b : G, a ◇ a = b ◇ b := by
  intro a b
  let p : G → G := fun x => ((a ◇ x) ◇ x) ◇ a
  have pi : Function.Injective p := by
    intro u v huv
    exact (h u a a).trans ((congrArg (fun t => (a ◇ a) ◇ t) huv).trans (h v a a).symm)
  obtain ⟨x, hx⟩ := (Finite.injective_iff_surjective.mp pi) a
  have ha : x = (a ◇ a) ◇ a := by
    have hh := h x a a
    change x = (a ◇ a) ◇ p x at hh
    rwa [hx] at hh
  have hb : x = (b ◇ b) ◇ a := by
    have hh := h x b a
    change x = (b ◇ b) ◇ p x at hh
    rwa [hx] at hh
  exact right_injective G h a (ha.symm.trans hb)

theorem common_square_right_identity (G : Type*) [Magma G] [Finite G]
    (h : Equation20911 G) (a : G) : ∀ x : G, x ◇ (a ◇ a) = x := by
  let c : G := a ◇ a
  have hs (x : G) : x ◇ x = c := common_square G h x a
  let t : G → G := fun x => (c ◇ x) ◇ x
  have ht (x : G) : c ◇ t x = x := by
    have hh := (h x a x).symm
    change c ◇ (((x ◇ x) ◇ x) ◇ x) = x at hh
    rwa [hs x] at hh
  have ti : Function.Injective t := by
    intro u v huv
    exact (ht u).symm.trans ((congrArg (fun s => c ◇ s) huv).trans (ht v))
  intro x
  obtain ⟨u, hu⟩ := (Finite.injective_iff_surjective.mp ti) x
  have hc : t u ◇ c = t u := left_injective G h c ((h u a c).symm.trans (ht u).symm)
  change x ◇ c = x
  rwa [hu] at hc

theorem orbit_identities (G : Type*) [Magma G] [Finite G]
    (h : Equation20911 G) (a : G) :
    ∀ x : G, (((a ◇ a) ◇ ((a ◇ a) ◇ x)) ◇ ((a ◇ a) ◇ x) = x) ∧
      (x ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ x)) = (a ◇ a) ◇ ((a ◇ a) ◇ x)) := by
  let c : G := a ◇ a
  have sq (x : G) : x ◇ x = c := common_square G h x a
  have h0 (x y : G) : c ◇ (((x ◇ y) ◇ y) ◇ x) = y := (h y a x).symm
  have ls (x : G) : Function.Surjective (fun y : G => x ◇ y) :=
    Finite.injective_iff_surjective.mp (left_injective G h x)
  have rs (y : G) : Function.Surjective (fun x : G => x ◇ y) :=
    Finite.injective_iff_surjective.mp (right_injective G h y)
  let d (x y : G) : G := Classical.choose (ls x y)
  have ld1 (x y : G) : x ◇ d x y = y := Classical.choose_spec (ls x y)
  have ld2 (x y : G) : d x (x ◇ y) = y := left_injective G h x (ld1 x (x ◇ y))
  let r (x y : G) : G := Classical.choose (rs y x)
  have rd1 (x y : G) : r x y ◇ y = x := Classical.choose_spec (rs y x)
  have rd2 (x y : G) : r (x ◇ y) y = x := right_injective G h y (rd1 (x ◇ y) y)
  intro x
  have p2 (x y : G) : (c ◇ (((x ◇ y) ◇ y) ◇ x)) = y := by
    exact h0 x y
  have p3 (x : G) : (x ◇ x) = c := by
    exact sq x
  have p5 (x y : G) : (d x (x ◇ y)) = y := by
    exact ld2 x y
  have p6 (x y : G) : ((r x y) ◇ y) = x := by
    exact rd1 x y
  have p7 (x y : G) : (r (x ◇ y) y) = x := by
    exact rd2 x y
  have p10 (x : G) : (c ◇ ((c ◇ x) ◇ x)) = x := by
    exact (((congrArg (fun _t : G => (c ◇ ((_t ◇ x) ◇ x))) ((p3 x)))).symm).trans ((p2 x x))
  have p14 (x y : G) : (c ◇ ((x ◇ y) ◇ (r x y))) = y := by
    exact (((congrArg (fun _t : G => (c ◇ ((_t ◇ y) ◇ (r x y)))) ((p6 x y)))).symm).trans ((p2 (r x y) y))
  have p17 (x : G) : (r c x) = x := by
    exact (((congrArg (fun _t : G => (r _t x)) ((p3 x)))).symm).trans ((p7 x x))
  have p29 (x : G) : (d c x) = ((c ◇ x) ◇ x) := by
    exact (((congrArg (fun _t : G => (d c _t)) ((p10 x)))).symm).trans ((p5 c ((c ◇ x) ◇ x)))
  have p44 (x : G) : ((c ◇ (c ◇ x)) ◇ (c ◇ x)) = x := by
    exact (((p29 (c ◇ x))).symm).trans ((p5 c x))
  have p45 (x : G) : (c ◇ (c ◇ (r x x))) = x := by
    exact (((congrArg (fun _t : G => (c ◇ (_t ◇ (r x x)))) ((p3 x)))).symm).trans ((p14 x x))
  have p48 (x y : G) : (c ◇ (x ◇ (r (r x y) y))) = y := by
    exact (((congrArg (fun _t : G => (c ◇ (_t ◇ (r (r x y) y)))) ((p6 x y)))).symm).trans ((p14 (r x y) y))
  have p49 (x : G) : (c ◇ (r x x)) = ((c ◇ x) ◇ x) := by
    exact ((((p29 x)).symm).trans ((((congrArg (fun _t : G => (d c _t)) ((p45 x)))).symm).trans ((p5 c (c ◇ (r x x)))))).symm
  have p63 (x : G) : (r x x) = (x ◇ ((c ◇ x) ◇ x)) := by
    exact (((((congrArg (fun _t : G => (x ◇ _t)) ((p49 x)))).symm).trans ((((congrArg (fun _t : G => (x ◇ (c ◇ (r _t x)))) ((p17 x)))).symm).trans ((((congrArg (fun _t : G => (_t ◇ (c ◇ (r (r c x) x)))) ((p48 c x)))).symm).trans ((p44 (r (r c x) x)))))).trans ((congrArg (fun _t : G => (r _t x)) ((p17 x))))).symm
  have p67 (x : G) : ((x ◇ ((c ◇ x) ◇ x)) ◇ x) = x := by
    exact (((congrArg (fun _t : G => (_t ◇ x)) ((p63 x)))).symm).trans ((p6 x x))
  have p75 (x : G) : (((c ◇ x) ◇ x) ◇ (c ◇ x)) = (c ◇ x) := by
    exact (((congrArg (fun _t : G => (((c ◇ x) ◇ _t) ◇ (c ◇ x))) ((p44 x)))).symm).trans ((p67 (c ◇ x)))
  have p107 (x : G) : (x ◇ (c ◇ (c ◇ x))) = (c ◇ (c ◇ x)) := by
    exact (((congrArg (fun _t : G => (_t ◇ (c ◇ (c ◇ x)))) ((p44 x)))).symm).trans ((p75 (c ◇ x)))
  exact ⟨p44 x, p107 x⟩

#print axioms left_injective
#print axioms right_injective
#print axioms common_square
#print axioms common_square_right_identity
#print axioms orbit_identities

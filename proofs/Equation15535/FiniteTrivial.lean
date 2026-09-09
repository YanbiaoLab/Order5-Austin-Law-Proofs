import Mathlib.Data.Fintype.Card
import JudgeMagma.Magma

@[reducible] def Equation2 (G : Type _) [Magma G] : Prop := ∀ (x y : G), x = y
@[reducible] def Equation15535 (G : Type _) [Magma G] : Prop := ∀ (x y z : G), x = y ◇ (((x ◇ (z ◇ z)) ◇ y) ◇ y)

theorem finite_trivial (G : Type*) [Magma G] [Finite G] (h : Equation15535 G) : Equation2 G := by
  intro a b
  let k := a ◇ a
  have li (y : G) : Function.Injective (fun t : G => y ◇ t) := by
    apply Finite.injective_iff_surjective.mpr
    intro x
    exact ⟨((x ◇ k) ◇ y) ◇ y, (h x y a).symm⟩
  have ri (y : G) : Function.Injective (fun t : G => t ◇ y) := by
    let f : G → G := fun x => ((x ◇ k) ◇ y) ◇ y
    have fi : Function.Injective f := by
      intro u v huv
      calc
        u = y ◇ f u := h u y a
        _ = y ◇ f v := by rw [huv]
        _ = v := (h v y a).symm
    apply Finite.injective_iff_surjective.mpr
    intro t
    obtain ⟨x, hx⟩ := Finite.surjective_of_injective fi t
    exact ⟨(x ◇ k) ◇ y, hx⟩
  have sq (x : G) : x ◇ x = k := by
    exact li a (ri a (ri a (li a ((h a a x).symm.trans (h a a a)))))
  have hn (x y : G) : x = y ◇ (((x ◇ k) ◇ y) ◇ y) := h x y a
  have helper (u v : G) : (((u ◇ v) ◇ k) ◇ u) ◇ u = v := by
    apply li u
    exact (hn (u ◇ v) u).symm
  have h32 (u : G) : ((u ◇ k) ◇ k) ◇ u = u := by
    apply ri u
    exact (helper u k).trans (sq u).symm
  have h23 (u : G) : (k ◇ u) ◇ k = k ◇ (u ◇ k) := by
    calc
      (k ◇ u) ◇ k = k ◇ (((((k ◇ u) ◇ k) ◇ k) ◇ k) ◇ k) := hn ((k ◇ u) ◇ k) k
      _ = k ◇ (u ◇ k) := by rw [helper k u]
  have h37 (u : G) : u ◇ (k ◇ (u ◇ k)) = k ◇ (u ◇ k) := by
    have hh := h32 ((k ◇ u) ◇ k)
    rw [helper k u, h23 u] at hh
    exact hh
  have allk (u : G) : u = k := by
    have hshort : (u ◇ k) ◇ (k ◇ (u ◇ k)) = u := by
      have hh := (hn u (u ◇ k)).symm
      rw [sq (u ◇ k)] at hh
      exact hh
    have hh := hn u (k ◇ (u ◇ k))
    rw [hshort, h37 u, sq] at hh
    exact hh
  exact (allk a).trans (allk b).symm

#print axioms finite_trivial

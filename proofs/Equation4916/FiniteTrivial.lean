import Mathlib.Data.Fintype.Card
import JudgeMagma.Magma

@[reducible] def Equation2 (G : Type _) [Magma G] : Prop := ∀ (x y : G), x = y
@[reducible] def Equation4916 (G : Type _) [Magma G] : Prop := ∀ (x y z : G), x = y ◇ (x ◇ (x ◇ (y ◇ (z ◇ z))))

theorem finite_trivial (G : Type*) [Magma G] [Finite G] (h : Equation4916 G) : Equation2 G := by
  intro a b
  have li (y : G) : Function.Injective (fun t : G => y ◇ t) := by
    apply Finite.injective_iff_surjective.mpr
    intro x
    exact ⟨x ◇ (x ◇ (y ◇ (a ◇ a))), (h x y a).symm⟩
  let k := a ◇ a
  have sq (x : G) : x ◇ x = k := by
    exact li a (li a (li a (li a ((h a a x).symm.trans (h a a a)))))
  have hn (x y : G) : x = y ◇ (x ◇ (x ◇ (y ◇ k))) := h x y a
  have helper (u v : G) : (u ◇ v) ◇ ((u ◇ v) ◇ (u ◇ k)) = v := by
    apply li u
    exact (hn (u ◇ v) u).symm
  have hk (u : G) : (u ◇ k) ◇ k = k := by
    have hh := helper u k
    rw [sq (u ◇ k)] at hh
    exact hh
  have h10 (u : G) : k ◇ (u ◇ (u ◇ k)) = u := by
    have hh := (hn u k).symm
    rw [sq k] at hh
    exact hh
  have rk (u : G) : u ◇ k = k := by
    have hh := h10 (u ◇ k)
    rw [hk u, hk u, sq k] at hh
    exact hh.symm
  have allk (u : G) : u = k := by
    have hh := hn u a
    rw [rk a, rk u, rk u, rk a] at hh
    exact hh
  exact (allk a).trans (allk b).symm

#print axioms finite_trivial

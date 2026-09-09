import Mathlib.Data.Fintype.Card
import JudgeMagma.Magma

@[reducible] def Equation2 (G : Type _) [Magma G] : Prop := ∀ (x y : G), x = y
@[reducible] def Equation20034 (G : Type _) [Magma G] : Prop := ∀ (x y z : G), x = (y ◇ y) ◇ ((z ◇ (x ◇ x)) ◇ z)

theorem finite_trivial (G : Type*) [Magma G] [Finite G] (h : Equation20034 G) : Equation2 G := by
  intro a b
  have si : Function.Injective (fun x : G => x ◇ x) := by
    intro u v huv
    change u ◇ u = v ◇ v at huv
    calc
      u = (a ◇ a) ◇ ((a ◇ (u ◇ u)) ◇ a) := h u a a
      _ = (a ◇ a) ◇ ((a ◇ (v ◇ v)) ◇ a) := by rw [huv]
      _ = v := (h v a a).symm
  have ss := Finite.surjective_of_injective si
  let f : G → G := fun x => (a ◇ (x ◇ x)) ◇ a
  have fi : Function.Injective f := by
    intro u v huv
    calc
      u = (a ◇ a) ◇ f u := h u a a
      _ = (a ◇ a) ◇ f v := by rw [huv]
      _ = v := (h v a a).symm
  have fs := Finite.surjective_of_injective fi
  have independent (u v t : G) : u ◇ t = v ◇ t := by
    obtain ⟨y, hy⟩ := ss u
    obtain ⟨z, hz⟩ := ss v
    obtain ⟨x, hx⟩ := fs t
    rw [← hy, ← hz, ← hx]
    exact (h x y a).symm.trans (h x z a)
  calc
    a = (a ◇ a) ◇ ((a ◇ (a ◇ a)) ◇ a) := h a a a
    _ = (a ◇ a) ◇ ((a ◇ (b ◇ b)) ◇ a) := by rw [independent (a ◇ (a ◇ a)) (a ◇ (b ◇ b)) a]
    _ = b := (h b a a).symm

#print axioms finite_trivial

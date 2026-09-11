prelude
import Austin10222.UnitDouble
set_option autoImplicit false
namespace Austin10222Unit
open T

theorem inverse_self_none (a : T) : inverse a a = none := by
  cases hi : inverse a a with
  | none => rfl
  | some x => exact False.elim (mul_ne_right x a (inverse_sound hi))

theorem inverse_double_key_none {w c : T} (hi : (inverse c w).isSome = true) :
    inverse (p w c) c = none := by
  have hs : sz c < sz (p w c) := by simp only [sz]; omega
  have h1 : c ≠ u c := Ne.symm (u_ne_self c)
  have h2 : inverse (u c) w ≠ some c := by
    intro h
    have hw : w = c := (inverse_sound h).symm.trans (mul_unit c)
    rw [hw,inverse_self_none] at hi
    cases hi
  rw [inverse_small hs]
  simp only [inverseTail,h1,h2,false_and,↓reduceIte]
  cases c with
  | atom n => rfl
  | s a => rfl
  | u a => rfl
  | p t d =>
      have hn : ¬((inverse d t).isSome = true ∧ mul t d = p t d ∧
          inverse d w = some (p t d)) := by
        rintro ⟨_,_,hx⟩
        have hw : w = p (p t d) d := (inverse_sound hx).symm.trans (pair_column_raw t d)
        have hz : inverse (p t d) w = none := by
          rw [hw]
          apply inverse_large_pair_none
          · simp only [sz]; omega
          · intro h; have hh := congrArg sz h; simp only [sz] at hh; omega
        rw [hz] at hi
        cases hi
      simp [hn]

theorem image_not_large_pair_key {x y v : T} :
    mul x y ≠ s (u (p v y)) := by
  intro he
  have hs : sz y ≤ sz (mul x y) := by rw [he]; simp only [sz]; omega
  rcases large_output_cases hs with hp | hq | hu
  · have hh := hp.symm.trans he; cases hh
  · have hh := congrArg sz (hq.symm.trans he)
    simp only [sz] at hh
    omega
  · have hh := hu.symm.trans he; cases hh

theorem source_middle_raw {u0 v y x : T}
    (hi : inverse y u0 = some x) (hv : (inverse y v).isSome = true)
    (hm : mul v y = p v y) (h1 : u0 ≠ p v y) (h2 : u0 ≠ s y) :
    mul u0 (p v y) = p u0 (p v y) := by
  have h3 : u0 ≠ s (u (p v y)) := by
    intro h
    exact image_not_large_pair_key ((inverse_sound hi).trans h)
  have h4 : u0 ≠ u y := by
    intro h; rw [h,inverse_unit_none] at hi; cases hi
  rw [mul.eq_def]
  dsimp only
  simp only [h1,h2,h3,h4,false_and,↓reduceIte]
  cases y with
  | atom n => rfl
  | s a => rfl
  | u a => rfl
  | p w c =>
      have hn : ¬(u0 = c ∧ (inverse c w).isSome = true ∧ mul w c = p w c) := by
        rintro ⟨he,hj,_⟩
        have hx : inverse (p w c) c = some x :=
          (congrArg (inverse (p w c)) he).symm.trans hi
        rw [inverse_double_key_none hj] at hx
        cases hx
      simp [hn]

theorem source_raw_double (x y v : T) (hv : (inverse y v).isSome = true)
    (hm : mul v y = p v y) :
    x = mul y (mul (mul x y) (p v y)) := by
  have hi := inverse_complete x y
  by_cases h1 : mul x y = p v y
  · have hx : x = v := right_injective (h1.trans hm.symm)
    rw [h1,mul_square,mul_square_decode hv hm]
    exact hx
  by_cases h2 : mul x y = s y
  · have hx : x = y := right_injective (h2.trans (mul_square y).symm)
    rw [h2,mul_unit_fiber hv hm,mul_unit]
    exact hx
  rw [source_middle_raw hi hv hm h1 h2,mul_pair_tail_decode hv hm hi]

theorem fixed_middle_raw {x z : T} (h1 : x ≠ z) (h2 : x ≠ u z) :
    mul (mul x (u z)) z = p (mul x (u z)) z := by
  rcases unit_column_cases x z with hu | hu | hu | hu
  · exact False.elim (h1 (right_injective (hu.trans (mul_unit z).symm)))
  · exact False.elim (h2 (right_injective (hu.trans (mul_square (u z)).symm)))
  · rw [hu]
    apply bigger_key_raw
    · simp only [sz]; omega
    · intro h; cases h
  · rw [hu]
    apply bigger_key_raw
    · simp only [sz]; omega
    · intro h; cases h

theorem source_unit_middle (x z : T) :
    x = mul (u z) (mul (mul x (u z)) z) := by
  by_cases h1 : x = z
  · subst x; rw [mul_unit,mul_square,mul_unit_decoder]
  by_cases h2 : x = u z
  · subst x; rw [mul_square,mul_large_code,mul_unit]
  rw [fixed_middle_raw h1 h2,mul_pair_unit_decode (inverse_complete x (u z))]

theorem source_of_normal_middle (x y z : T) (hy : NF y) :
    x = mul y (mul (mul x y) (mul (mul z y) y)) := by
  rcases column_double_cases z y hy with ⟨he,_⟩ | hd
  · subst y
    rw [mul_unit,mul_unit]
    exact source_unit_middle x z
  · rw [hd]
    apply source_raw_double
    · rw [inverse_complete]; rfl
    · exact hd

theorem source_holds : Law := by
  intro x y z _ hy _
  exact source_of_normal_middle x y z hy

theorem carrier_source (x y z : Carrier) :
    x = carrierMul y (carrierMul (carrierMul x y) (carrierMul (carrierMul z y) y)) := by
  apply Subtype.ext
  exact source_of_normal_middle x.val y.val z.val y.property

theorem carrier_dual (x y z : Carrier) :
    x = (fun a b => carrierMul b a)
      ((fun a b => carrierMul b a)
        ((fun a b => carrierMul b a) y ((fun a b => carrierMul b a) y z))
        ((fun a b => carrierMul b a) y x)) y := carrier_source x y z

theorem carrier_nontrivial : embed 0 ≠ embed 1 := by
  intro h
  have hh := embed_injective 0 1 h
  cases hh

end Austin10222Unit
#print axioms Austin10222Unit.inverse_self_none
#print axioms Austin10222Unit.inverse_double_key_none
#print axioms Austin10222Unit.image_not_large_pair_key
#print axioms Austin10222Unit.source_middle_raw
#print axioms Austin10222Unit.source_raw_double
#print axioms Austin10222Unit.fixed_middle_raw
#print axioms Austin10222Unit.source_unit_middle
#print axioms Austin10222Unit.source_of_normal_middle
#print axioms Austin10222Unit.source_holds
#print axioms Austin10222Unit.carrier_source
#print axioms Austin10222Unit.carrier_dual
#print axioms Austin10222Unit.carrier_nontrivial

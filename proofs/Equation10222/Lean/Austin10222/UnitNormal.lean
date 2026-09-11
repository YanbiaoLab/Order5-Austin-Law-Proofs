prelude
import Austin10222.UnitComplete
set_option autoImplicit false
namespace Austin10222Unit
open T

theorem inverse_tail_normal {b out a : T} (h : inverseTail b out = some a)
    (hb : NF b) : NF a := by
  unfold inverseTail at h
  repeat' first | split at h | contradiction
  all_goals simp_all only [Option.some.injEq]
  all_goals subst a
  all_goals simp_all [NF]

theorem inverse_eq_tail (b out : T) : inverse b out =
    if out = s b then some b
    else if out = u (u b) then some (s (u b))
    else match out with
    | p a c => if c = b ∧ mul a b = out then some a else inverseTail b out
    | _ => inverseTail b out := by
  rw [inverse.eq_def]
  rfl

theorem inverse_normal {b out a : T} (h : inverse b out = some a)
    (hb : NF b) (ho : NF out) : NF a := by
  rw [inverse_eq_tail] at h
  split at h
  · have he := Option.some.inj h; subst a; exact hb
  · split at h
    · have he := Option.some.inj h; subst a; exact hb
    · cases out with
      | atom n => exact inverse_tail_normal h hb
      | s v => exact inverse_tail_normal h hb
      | u v => exact inverse_tail_normal h hb
      | p v c =>
          dsimp only at h
          split at h
          · have he := Option.some.inj h; subst a; exact ho.1
          · exact inverse_tail_normal h hb

theorem mul_normal {a b : T} (ha : NF a) (hb : NF b) : NF (mul a b) := by
  generalize he : mul a b = out
  have original := he
  rw [mul.eq_def] at he
  simp only [Option.getD] at he
  repeat' first | split at he | contradiction
  all_goals cases he
  all_goals try simp only [NF] at ha hb ⊢
  all_goals first
    | exact ⟨ha,hb,original⟩
    | assumption
    | exact hb.1
    | exact hb.2.1
    | exact hb.1.1
    | exact hb.2.1.2.1
    | (apply inverse_normal (show inverse _ _ = some _ from by assumption) <;>
        first | assumption | exact hb.1 | exact hb.2.1 | exact hb.2.1.2.1)

abbrev Carrier := {a : T // NF a}
def embed (n : Nat) : Carrier := ⟨atom n,nf_atom n⟩
theorem embed_injective (m n : Nat) (h : embed m = embed n) : m = n := by
  exact atom_injective m n (congrArg Subtype.val h)

def carrierMul (a b : Carrier) : Carrier := ⟨mul a.val b.val,mul_normal a.property b.property⟩

end Austin10222Unit
#print axioms Austin10222Unit.inverse_normal
#print axioms Austin10222Unit.inverse_tail_normal
#print axioms Austin10222Unit.inverse_eq_tail
#print axioms Austin10222Unit.mul_normal
#print axioms Austin10222Unit.embed_injective
#print axioms Austin10222Unit.carrierMul

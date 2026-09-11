prelude
import JudgeProblem
import Austin10222.UnitLaw

namespace submission
abbrev CM := Austin10222Unit.Carrier
namespace CM
theorem tower_injective (m n : Nat)
    (h : Austin10222Unit.embed m = Austin10222Unit.embed n) : m = n :=
  Austin10222Unit.embed_injective m n h
end CM
instance modelMagma : Magma CM := ⟨Austin10222Unit.carrierMul⟩
end submission

theorem submission : Goal := by
  refine ⟨submission.CM,submission.modelMagma,?_,?_⟩
  · intro x y z
    exact Austin10222Unit.carrier_source x y z
  · intro h
    exact Austin10222Unit.carrier_nontrivial
      (h (Austin10222Unit.embed 0) (Austin10222Unit.embed 1))

example : Goal := submission
#print axioms submission
#print axioms submission.CM.tower_injective

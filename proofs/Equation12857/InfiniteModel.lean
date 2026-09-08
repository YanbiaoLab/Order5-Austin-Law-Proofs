import JudgeProblem
import Model

namespace submission
abbrev CM := Austin12857.Carrier
namespace CM
/-- An explicit injection of the natural numbers into the model carrier. -/
theorem tower_injective (n k : Nat)
    (h : Austin12857.embed n = Austin12857.embed k) : n = k :=
  Austin12857.embed_injective n k h
end CM
noncomputable instance : Magma CM := ⟨Austin12857.mul⟩
end submission

/-- The exact archived source equation has a nontrivial, explicitly infinite model. -/
theorem submission : Goal := by
  refine ⟨submission.CM, inferInstance, ?_, ?_⟩
  · intro x y z
    exact (Austin12857.equation12857 x y z).symm
  · intro h
    have bad : 0 = 1 := Austin12857.embed_injective 0 1
      (h (Austin12857.embed 0) (Austin12857.embed 1))
    cases bad

example : Goal := submission
#print axioms submission
#print axioms submission.CM.tower_injective

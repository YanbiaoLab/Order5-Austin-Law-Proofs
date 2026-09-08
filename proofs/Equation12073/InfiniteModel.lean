import JudgeProblem
import Model

namespace submission
abbrev CM := Austin12073.Carrier
namespace CM
/-- The model contains an injective image of every natural number. -/
theorem tower_injective (n j : Nat)
    (h : Austin12073.embed n = Austin12073.embed j) : n = j :=
  Austin12073.embed_injective n j h
end CM
noncomputable instance modelMagma : Magma CM := ⟨Austin12073.mul⟩
end submission

theorem submission : Goal := by
  refine ⟨submission.CM, submission.modelMagma, ?_, ?_⟩
  · intro x y z
    exact (submission.Austin12073.equation12073 x y z).symm
  · intro h
    have bad : 0 = 1 := submission.Austin12073.embed_injective 0 1
      (h (submission.Austin12073.embed 0) (submission.Austin12073.embed 1))
    exact Nat.noConfusion bad
example : Goal := submission
#print axioms submission
#print axioms submission.CM.tower_injective

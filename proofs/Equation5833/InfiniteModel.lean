import JudgeProblem
import Model

namespace submission
abbrev CM := Austin5833.Carrier
namespace CM
theorem tower_injective (n j : Nat)
    (h : Austin5833.embed n = Austin5833.embed j) : n = j :=
  Austin5833.embed_injective n j h
end CM
noncomputable instance modelMagma : Magma CM := ⟨Austin5833.mul⟩
end submission
theorem submission : Goal := by
  refine ⟨submission.CM, submission.modelMagma, ?_, ?_⟩
  · intro x y z
    exact (submission.Austin5833.equation5833 x y z).symm
  · intro h
    have bad : 0 = 1 := submission.Austin5833.embed_injective 0 1
      (h (submission.Austin5833.embed 0) (submission.Austin5833.embed 1))
    exact Nat.noConfusion bad
example : Goal := submission
#print axioms submission
#print axioms submission.CM.tower_injective

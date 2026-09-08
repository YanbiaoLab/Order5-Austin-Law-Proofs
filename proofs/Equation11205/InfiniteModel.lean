import JudgeProblem
import Model

namespace submission
abbrev CM := Austin11205.Carrier
namespace CM
theorem tower_injective (n j : Nat)
    (h : Austin11205.embed n = Austin11205.embed j) : n = j :=
  Austin11205.embed_injective n j h
end CM
noncomputable instance modelMagma : Magma CM := ⟨Austin11205.mul⟩
end submission
theorem submission : Goal := by
  refine ⟨submission.CM, submission.modelMagma, ?_, ?_⟩
  · intro x y z
    exact (submission.Austin11205.equation11205 x y z).symm
  · intro h
    have bad : 0 = 1 := submission.Austin11205.embed_injective 0 1
      (h (submission.Austin11205.embed 0) (submission.Austin11205.embed 1))
    exact Nat.noConfusion bad
example : Goal := submission
#print axioms submission
#print axioms submission.CM.tower_injective

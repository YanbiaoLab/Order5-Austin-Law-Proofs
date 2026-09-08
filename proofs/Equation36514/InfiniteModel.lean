import JudgeProblem
import Model

namespace submission
abbrev CM := Austin9603.Carrier
namespace CM
theorem tower_injective (n j : Nat)
    (h : Austin9603.embed n = Austin9603.embed j) : n = j :=
  Austin9603.embed_injective n j h
end CM
noncomputable instance modelMagma : Magma CM := ⟨Austin9603.opposite⟩
end submission
theorem submission : Goal := by
  refine ⟨submission.CM, submission.modelMagma, ?_, ?_⟩
  · intro x y z
    exact (submission.Austin9603.equation36514 x y z).symm
  · intro h
    have bad : 0 = 1 := submission.Austin9603.embed_injective 0 1
      (h (submission.Austin9603.embed 0) (submission.Austin9603.embed 1))
    exact Nat.noConfusion bad
example : Goal := submission
#print axioms submission
#print axioms submission.CM.tower_injective

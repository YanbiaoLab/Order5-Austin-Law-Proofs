import JudgeProblem
import Model

namespace submission
abbrev CM := Austin13849.Carrier
namespace CM
/-- The model contains an injective image of every natural number. -/
theorem tower_injective (n j : Nat)
    (h : Austin13849.embed n = Austin13849.embed j) : n = j :=
  Austin13849.embed_injective n j h
end CM
noncomputable instance modelMagma : Magma CM := ⟨Austin13849.opposite⟩
end submission

theorem submission : Goal := by
  refine ⟨submission.CM, submission.modelMagma, ?_, ?_⟩
  · intro x y z
    exact (submission.Austin13849.equation32281 x y z).symm
  · intro h
    have bad : 0 = 1 := submission.Austin13849.embed_injective 0 1
      (h (submission.Austin13849.embed 0) (submission.Austin13849.embed 1))
    exact Nat.noConfusion bad
example : Goal := submission
#print axioms submission
#print axioms submission.CM.tower_injective

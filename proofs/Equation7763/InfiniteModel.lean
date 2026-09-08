import JudgeProblem
import Model

namespace submission
abbrev CM := Austin7763.Carrier
namespace CM
theorem tower_injective (n j : Nat)
    (h : Austin7763.embed n = Austin7763.embed j) : n = j :=
  Austin7763.embed_injective n j h
end CM
noncomputable instance modelMagma : Magma CM := ⟨Austin7763.mul⟩
end submission
theorem submission : Goal := by
  refine ⟨submission.CM, submission.modelMagma, ?_, ?_⟩
  · intro x y z
    exact (submission.Austin7763.equation7763 x y z).symm
  · intro h
    have bad : 0 = 1 := submission.Austin7763.embed_injective 0 1
      (h (submission.Austin7763.embed 0) (submission.Austin7763.embed 1))
    exact Nat.noConfusion bad
example : Goal := submission
#print axioms submission
#print axioms submission.CM.tower_injective

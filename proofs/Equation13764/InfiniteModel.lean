import JudgeProblem
import Model

namespace submission
abbrev CM := Austin13764.Carrier
namespace CM
/-- The model contains an injective image of every natural number. -/
theorem tower_injective (n j : Nat)
    (h : Austin13764.embed n = Austin13764.embed j) : n = j :=
  Austin13764.embed_injective n j h
end CM
noncomputable instance modelMagma : Magma CM := ⟨Austin13764.mul⟩
end submission

theorem submission : Goal := by
  refine ⟨submission.CM, submission.modelMagma, ?_, ?_⟩
  · intro x y z
    exact (submission.Austin13764.equation13764 x y z).symm
  · intro h
    have bad : 0 = 1 := submission.Austin13764.embed_injective 0 1
      (h (submission.Austin13764.embed 0) (submission.Austin13764.embed 1))
    exact Nat.noConfusion bad
example : Goal := submission
#print axioms submission
#print axioms submission.CM.tower_injective

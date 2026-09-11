import JudgeProblem
import Austin21866.Duals

namespace submission
abbrev CM := Austin21866.T
namespace CM
theorem tower_injective (n m : Nat)
    (h : Austin21866.tower n = Austin21866.tower m) : n = m :=
  Austin21866.tower_injective n m h
end CM
noncomputable instance modelMagma : Magma CM := ⟨Austin21866.op⟩
end submission

theorem submission : Goal := by
  refine ⟨submission.CM, submission.modelMagma, ?_, ?_⟩
  · intro x y z
    exact submission.Austin21866.equation21865 x y z
  · intro h
    have bad : 0 = 1 := submission.Austin21866.tower_injective 0 1
      (h (submission.Austin21866.tower 0) (submission.Austin21866.tower 1))
    exact Nat.noConfusion bad
example : Goal := submission
#print axioms submission
#print axioms submission.CM.tower_injective

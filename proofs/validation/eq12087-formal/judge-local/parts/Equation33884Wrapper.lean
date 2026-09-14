prelude
import JudgeProblem
import JudgeTraceFullSource
set_option Elab.async false
set_option autoImplicit false

namespace submission
abbrev CM := submission.Austin12087Trace.NormalTree
instance modelMagma : Magma CM := ⟨fun a b => submission.Austin12087Trace.normalMul b a⟩
namespace CM
theorem tower_injective (m n : Nat)
    (h : submission.Austin12087Trace.normalAtom m = submission.Austin12087Trace.normalAtom n) : m = n :=
  submission.Austin12087Trace.normalAtom_injective h
end CM
theorem source_law : EquationLHS CM := by
  intro x y z
  exact submission.Austin12087Trace.full_source_law x z y
end submission

theorem submission : Goal := by
  refine ⟨submission.CM,submission.modelMagma,submission.source_law,?_⟩
  intro h
  exact submission.Austin12087Trace.normalAtom_nontrivial
    (h (submission.Austin12087Trace.normalAtom 0) (submission.Austin12087Trace.normalAtom 1))

#print axioms submission
#print axioms submission.source_law
#print axioms submission.CM.tower_injective

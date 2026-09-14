prelude
import JudgeProblem
import TraceFullSource
set_option autoImplicit false

namespace submission
abbrev CM := Austin12087Trace.NormalTree
instance : Magma CM := ⟨fun a b => Austin12087Trace.normalMul b a⟩
namespace CM
theorem tower_injective (m n : Nat)
    (h : Austin12087Trace.normalAtom m = Austin12087Trace.normalAtom n) : m = n :=
  Austin12087Trace.normalAtom_injective h
end CM
theorem source_law : EquationLHS CM := by
  intro x y z
  exact Austin12087Trace.full_source_law x z y
end submission

theorem submission : Goal := by
  refine ⟨submission.CM,inferInstance,submission.source_law,?_⟩
  intro h
  exact Austin12087Trace.normalAtom_nontrivial
    (h (Austin12087Trace.normalAtom 0) (Austin12087Trace.normalAtom 1))

#print axioms submission
#print axioms submission.source_law
#print axioms submission.CM.tower_injective

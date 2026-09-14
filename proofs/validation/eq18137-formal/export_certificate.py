"""Flatten the four checked tree modules into the local Judge certificate."""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
MODULES = ["TreeSchema", "TreeBounds", "TreeUnique", "TreeModel"]


def certificate_text():
    header = """prelude
import JudgeProblem
import Init.Data.Nat.Basic
import Init.Classical
set_option autoImplicit false

/- Equation18137: finite binary trees with Nat-labelled atoms.
   Generated from TreeSchema, TreeBounds, TreeUnique and TreeModel.
   All decoding obligations are proved below; no finite-model assumption.
   Reproduce: python3 proofs/validation/eq18137-formal/verify.py
   This is a local Lean certificate, not a remote Judge acceptance receipt. -/
"""
    sections = [header]
    for name in MODULES:
        source = ROOT / "proofs/Equation18137" / (name + ".lean")
        lines = [line for line in source.read_text().splitlines()
                 if line != "prelude" and not line.startswith(("import ", "#print axioms "))]
        sections.append("\n/- Module: " + name + " -/\n" + "\n".join(lines).strip() + "\n")
    sections.append("""
namespace submission
abbrev CM := Equation18137TreeSchema.Tree
noncomputable instance modelMagma : Magma CM := ⟨Equation18137TreeSchema.op⟩
namespace CM
theorem tower_injective (m n : Nat)
    (h : Equation18137TreeSchema.Tree.atom m = Equation18137TreeSchema.Tree.atom n) :
    m = n := Equation18137TreeSchema.atom_injective m n h
end CM
end submission

theorem submission : Goal := by
  refine ⟨submission.CM, submission.modelMagma, ?_, ?_⟩
  · exact Equation18137TreeSchema.source_law_explicit
  · intro h
    exact Nat.noConfusion (Equation18137TreeSchema.Tree.atom.inj
      (h (Equation18137TreeSchema.Tree.atom 0) (Equation18137TreeSchema.Tree.atom 1)))

example : Goal := submission
example (x y z : submission.CM) :
    x = (y ◇ x) ◇ (z ◇ ((x ◇ z) ◇ z)) :=
  Equation18137TreeSchema.source_law_explicit x y z

#print axioms submission
#print axioms submission.CM.tower_injective
#print axioms Equation18137TreeSchema.infinite_model
""")
    # The remote proof policy admits participant declarations under submission.
    # Keep development modules unchanged; rename their namespace in this export.
    return "\n".join(sections).replace("Equation18137TreeSchema", "submission.Equation18137TreeSchema")


if __name__ == "__main__":
    output = ROOT / "proofs/Equation18137/InfiniteModel.lean"
    output.write_text(certificate_text())
    print(output)

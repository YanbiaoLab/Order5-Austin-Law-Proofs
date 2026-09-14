"""Standalone Equation27863 certificate with the complete source model included."""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
MODULES = [(name, "proofs/Equation18137/" + name + ".lean")
           for name in ["TreeSchema", "TreeBounds", "TreeUnique", "TreeModel"]]
MODULES.append(("DualModel", "proofs/Equation27863/DualModel.lean"))


def certificate_text():
    sections = ["""prelude
import JudgeProblem
import Init.Data.Nat.Basic
import Init.Classical
set_option autoImplicit false

/- Equation27863: the opposite operation on the Equation18137 infinite tree model.
   All construction proofs are included below. No external model assumption.
   Reproduce: python3 proofs/validation/eq27863-formal/verify.py -/
"""]
    for name, path in MODULES:
        lines = [line for line in (ROOT / path).read_text().splitlines()
                 if line != "prelude" and not line.startswith(("import ", "#print axioms "))]
        sections.append("\n/- Module: " + name + " -/\n" + "\n".join(lines).strip() + "\n")
    sections.append("""
namespace submission
abbrev CM := Equation27863TreeModel.Carrier
noncomputable instance modelMagma : Magma CM := ⟨Equation27863TreeModel.op⟩
namespace CM
theorem tower_injective (m n : Nat)
    (he : Equation27863TreeModel.embed m = Equation27863TreeModel.embed n) : m = n :=
  Equation27863TreeModel.embed_injective m n he
end CM
end submission

theorem submission : Goal := by
  refine ⟨submission.CM, submission.modelMagma, ?_, ?_⟩
  · exact Equation27863TreeModel.source_law_explicit
  · intro h
    exact Nat.noConfusion (Equation27863TreeModel.embed_injective 0 1
      (h (Equation27863TreeModel.embed 0) (Equation27863TreeModel.embed 1)))

example : Goal := submission
example (x y z : submission.CM) :
    x = ((y ◇ (y ◇ x)) ◇ y) ◇ (x ◇ z) :=
  Equation27863TreeModel.source_law_explicit x y z

#print axioms submission
#print axioms submission.CM.tower_injective
#print axioms Equation27863TreeModel.infinite_model
""")
    return ("\n".join(sections)
            .replace("Equation18137TreeSchema", "submission.Equation18137TreeSchema")
            .replace("Equation27863TreeModel", "submission.Equation27863TreeModel"))


if __name__ == "__main__":
    output = ROOT / "proofs/Equation27863/InfiniteModel.lean"
    output.write_text(certificate_text())
    print(output)

"""Generate the incidence-check optimization from original projection batches."""
import argparse
from pathlib import Path
import re

VERTICES = re.compile(
    r"^noncomputable def vertices_(\d+) : Finset \(Fin 10\) := literalFinset \[([^\]]+)\]",
    re.M,
)
PRIORITY = re.compile(
    r"(?<=^noncomputable def planePriority \(p : PlaneNode boundary\) : ℕ :=\n)"
    r"((?:  if p\.val = \((?:true|false), vertices_\d+\) then \d+ else\n)+)  0(?=\n)",
    re.M,
)
ORIGINAL_CHECK = (
    "  incidenceCertificateOfChecks boundary priority priority_injective "
    "(by decide +kernel) (by decide +kernel)"
)

KEY = """-- The upper bit distinguishes extra polygon planes from ordinary facet planes.
private def projectionPlaneKey (p : Bool × Finset (Fin 10)) : Nat :=
  (if p.1 then 1024 else 0) + p.2.sum (fun i => 2 ^ i.val)

"""

HELPERS = """private def projectionRetainedPoints {n : Nat} {B : Boundary n}
    (priority : Node B → Nat) (p : PlaneNode B) : Finset (Fin n) :=
  Finset.univ.filter fun i => incidence i p ∧ priority (Sum.inr p) < priority (Sum.inl i)

private def projectionRetainedPlanes {n : Nat} {B : Boundary n}
    (priority : Node B → Nat) (i : Fin n) : Finset (PlaneNode B) :=
  Finset.univ.filter fun p => incidence i p ∧ priority (Sum.inl i) < priority (Sum.inr p)

private theorem projectionRetainedPoints_eq {n : Nat} {B : Boundary n}
    (priority : Node B → Nat) (p : PlaneNode B) :
    projectionRetainedPoints priority p = retainedPoints priority p := by
  apply Finset.ext
  intro i
  simp only [projectionRetainedPoints, retainedPoints, Finset.mem_filter, Finset.mem_univ, true_and]
  exact and_comm

private theorem projectionRetainedPlanes_eq {n : Nat} {B : Boundary n}
    (priority : Node B → Nat) (i : Fin n) :
    projectionRetainedPlanes priority i = retainedPlanes priority i := by
  apply Finset.ext
  intro p
  simp only [projectionRetainedPlanes, retainedPlanes, Finset.mem_filter, Finset.mem_univ, true_and]
  exact and_comm

-- Transport the checked rules back to the existing reconstruction interface.
private def projectionIncidenceOfChecks {n : Nat} (B : Boundary n) (priority : Node B → Nat)
    (hinj : Function.Injective priority)
    (hplane : ∀ p, PointRuleValid B (projectionRetainedPoints priority p))
    (hpoint : ∀ i, PlaneRuleValid B (projectionRetainedPlanes priority i)) : IncidenceCertificate B :=
  incidenceCertificateOfChecks B priority hinj
    (fun p => projectionRetainedPoints_eq priority p ▸ hplane p)
    (fun i => projectionRetainedPlanes_eq priority i ▸ hpoint i)

"""

ENTRY = re.compile(r"  if p\.val = \((true|false), vertices_(\d+)\) then (\d+) else")


def optimize(source, *, numeric_priority=True):
    parts = source.split("section BundlePart")
    if len(parts) < 2:
        raise ValueError("No original certificate bundles found")
    entries = 0
    incident_pairs = 0
    for index in range(1, len(parts)):
        part = parts[index]
        vertex_sets = dict(VERTICES.findall(part))
        for suffix, literal in vertex_sets.items():
            vertices = [int(value) for value in literal.split(", ")]
            if vertices != sorted(set(vertices)) or any(not 0 <= v < 10 for v in vertices):
                raise ValueError(f"Invalid vertices in bundle {index - 1}")
            if int(suffix) != sum(1 << v for v in vertices):
                raise ValueError(f"Mask mismatch in bundle {index - 1}")

        matches = list(PRIORITY.finditer(part))
        if len(matches) != 1:
            raise ValueError(f"Expected one priority definition in bundle {index - 1}")
        match = matches[0]
        rows = ENTRY.findall(match[1])
        if any(mask not in vertex_sets for _, mask, _ in rows):
            raise ValueError(f"Undefined plane in bundle {index - 1}")
        if len({(tag, mask) for tag, mask, _ in rows}) != len(rows):
            raise ValueError(f"Duplicate plane in bundle {index - 1}")
        entries += len(rows)
        incident_pairs += sum((int(mask) >> 1).bit_count() for _, mask, _ in rows)
        if numeric_priority:
            ordered = [(int(mask) + (1024 if tag == "true" else 0), int(rank))
                       for tag, mask, rank in rows]
            table = ", ".join(f"({key}, {rank})" for key, rank in ordered)
            body = f"  (([{table}] : List (Nat × Nat)).lookup (projectionPlaneKey p.val)).getD 0"
            part = part[:match.start()] + body + part[match.end():]
        if part.count(ORIGINAL_CHECK) != 1:
            raise ValueError(f"Expected one incidence check in bundle {index - 1}")
        parts[index] = part.replace(
            ORIGINAL_CHECK, ORIGINAL_CHECK.replace("incidenceCertificateOfChecks", "projectionIncidenceOfChecks")
        )
    header = parts[0]
    needle = "import Papers.FiniteProjectionChecks\n"
    if header.count(needle) != 1:
        raise ValueError("Unexpected batch imports")
    if numeric_priority:
        header = header.replace(needle, needle + "import Mathlib.Algebra.BigOperators.Group.Finset.Defs\n")
    header += (
        "section ProjectionSpeedHelpers\n"
        "open Papers.RationalityTen.ChirotopeDensity.FiniteProjection\n\n"
        + (KEY if numeric_priority else "") + HELPERS + "end ProjectionSpeedHelpers\n\n"
    )
    parts[0] = header
    return "section BundlePart".join(parts), len(parts) - 1, entries, incident_pairs


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    optimized, bundles, entries, incident_pairs = optimize(args.source.read_text())
    args.output.write_text(optimized)
    print(f"{bundles} certificates, {entries} plane entries, "
          f"{incident_pairs} incidences among {9 * entries} point–plane pairs")

if __name__ == "__main__":
    main()

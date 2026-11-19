"""Candidate for matched remote testing on actual small- and six-facet graph cases."""
from pathlib import Path

OLD = "$cells ($allowedProof $record $quota (by decide +kernel))"
NEW = """$cells ($allowedProof $record $quota (by
        intro j
        rw [($parameters).quota j] <;> (revert j; decide +kernel)))"""


def apply(source: Path) -> str:
    original = source.read_text()
    if original.count(OLD) != 1:
        raise ValueError("unexpected GraphCases quota proof")
    # Recover the support equivalence from the existing checked quota equality.
    # The remaining computation is on the fixed row and its five-bit pattern.
    return original.replace(OLD, NEW)

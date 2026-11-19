module
prelude
public import RawLeafCertificate
public import CachedCellRelabel

@[expose] public section

/-!
# Reusing checked complete-boundary matches

The terminal catalogue already verifies its coordinate witnesses. This
module links a literal list of cells to one such checked boundary using
two exact bitset equalities, one for facets and one for polygons. Set
equality is justified for all natural-number masks, without a width bound.
-/

namespace Papers.RationalityTen.FastRawLeafCertificate

open ConcreteGrowth RawLeafCertificate CachedCellRelabel
open Nonrational.InducedTerminalMatches

def boundaryTest (raw : List Cell) (entry : Entry) : Bool :=
  sameSetBits (boundary raw).facets entry.boundary.facets &&
    sameSetBits (boundary raw).polygons entry.boundary.polygons

theorem boundaryTest_eq (raw : List Cell) (entry : Entry) :
    boundaryTest raw entry = boundaryCheck raw entry.boundary := by
  simp only [boundaryTest, boundaryCheck, sameSetBits_eq]

theorem matching_checked (quota : Nat → Nat) (raw : List Cell) (entry : Entry)
    (hentry : Nonrational.InducedTerminalMatches.check entry = true)
    (hboundary : boundaryTest raw entry = true) :
    RawLeafCertificate.check quota raw (.matching entry) = true := by
  change boundaryCheck raw entry.boundary &&
    Nonrational.InducedTerminalMatches.check entry = true
  rw [← boundaryTest_eq, hboundary, hentry]
  rfl

/-- Empty dummy leaves are impossible whenever one actual quota is positive. -/
theorem empty_checked (quota : Nat → Nat) (kind : Nat) (hquota : 0 < quota kind) :
    RawLeafCertificate.check quota [] (.quota kind) = true := by
  change decide (0 ≠ quota kind) = true
  exact decide_eq_true (Nat.ne_of_lt hquota)

#print axioms matching_checked
#print axioms empty_checked

end Papers.RationalityTen.FastRawLeafCertificate

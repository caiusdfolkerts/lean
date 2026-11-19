module
prelude

public import RawClosedLeafData
public import InducedTerminalMatches.Basic

@[expose] public section

/-!
# Checkable dispositions of complete growth leaves

The checker records why a complete ordered facet list is resolved. Negative
cases are numerical contradictions with an actual four-polytope. A positive
case compares both complete face families with an independently checked
terminal-match entry. Its existing match proof can therefore be reused.
The geometric soundness theorem is in `ActualLeafCertificates`.
-/

namespace Papers.RationalityTen.RawLeafCertificate

open ConcreteGrowth RawBoundaryMatch
open Nonrational.TerminalData Nonrational.InducedTerminalMatches

def boundary (raw : List Cell) : RawBoundary where
  facets := raw.map Cell.vertices
  polygons := raw.flatMap Cell.ridgeMasks

inductive Certificate where
  | quota (kind : Nat)
  | incidence (vertex : Nat)
  | euler
  | vertexLink (vertex : Nat)
  | matching (entry : Entry)

/-- Equality of finite sets, including every facet and every polygon.
Repeated polygon records arising from their two incident facets are harmless. -/
def boundaryCheck (raw : List Cell) (B : RawBoundary) : Bool :=
  sameSetCheck (boundary raw).facets B.facets &&
    sameSetCheck (boundary raw).polygons B.polygons

noncomputable def check (quota : Nat → Nat) (raw : List Cell) : Certificate → Bool
  | .quota kind => RawClosedLeafData.quotaFailure raw kind (quota kind)
  | .incidence vertex => decide (vertex < 10) &&
      RawClosedLeafData.incidenceFailure raw vertex 5
  | .euler => RawClosedLeafData.eulerFailure raw
  | .vertexLink vertex => decide (vertex < 10) && VertexLinkObstructionData.check raw vertex
  | .matching entry => boundaryCheck raw entry.boundary &&
      Nonrational.InducedTerminalMatches.check entry

end Papers.RationalityTen.RawLeafCertificate

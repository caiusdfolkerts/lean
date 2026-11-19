module
prelude

public import VertexLinkObstructionData

@[expose] public section

/-!
# Finite reasons that a closed selected family is impossible

These checks use the complete ordered raw facet list. Edge and ridge counts
remove duplicates; the number of facets is the list length. Their application
to actual polytopes separately requires a duplicate-free list of facet indices.
-/

namespace Papers.RationalityTen.RawClosedLeafData

open ConcreteGrowth VertexLinkObstructionData

def kindCount (raw : List Cell) (kind : Nat) : Nat :=
  (raw.filter fun cell => decide (cell.kind = kind)).length

def incidenceCount (raw : List Cell) (vertex : Nat) : Nat :=
  (raw.filter fun cell => cell.vertices.testBit vertex).length

noncomputable def edgeCount (raw : List Cell) : Nat :=
  (distinct (raw.flatMap Cell.edges)).length

noncomputable def ridgeCount (raw : List Cell) : Nat :=
  (distinct (raw.flatMap Cell.ridgeMasks)).length

def quotaFailure (raw : List Cell) (kind quota : Nat) : Bool :=
  decide (kindCount raw kind ≠ quota)

def incidenceFailure (raw : List Cell) (vertex minimum : Nat) : Bool :=
  decide (incidenceCount raw vertex < minimum)

noncomputable def eulerFailure (raw : List Cell) : Bool :=
  decide (10 + ridgeCount raw ≠ edgeCount raw + raw.length)

end Papers.RationalityTen.RawClosedLeafData

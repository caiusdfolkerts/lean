module
prelude
public import RawFacetEmbedding
public import FiniteMaskSets

@[expose] public section

/-! Pure metadata checks for the complete small-facet universe. -/
namespace Papers.RationalityTen.RawSmallCellMetadata

open ConcreteGrowth

def vertexCount (cell : Cell) : Nat := FiniteMaskSets.card 10 cell.vertices

def excess (cell : Cell) : Int :=
  3 * (vertexCount cell : Int) - (cell.edges.length : Int) - 6

def kind (cell : Cell) : Nat :=
  if 4 < vertexCount cell then if excess cell = 1 then 3 else 2 else 1

def check (cell : Cell) : Bool :=
  RawFacetEmbedding.wellFormedCheck cell && decide (cell.kind = kind cell) &&
    decide (vertexCount cell ≤ 5)

end Papers.RationalityTen.RawSmallCellMetadata

module
prelude
public meta import IntegerTables
public import PackedGrowthData

@[expose] public section

/-! Literal common facet universe. Geometric coverage and finite exhaustion are
proved separately. Vertex labels range from zero through nine. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.FacetUniverses.FullSmall
open Papers.RationalityTen.ConcreteGrowth
abbrev cellCount : Nat := 6510
noncomputable def cellTable : Table Nat :=
  integerTable% 0 13019
noncomputable def cells (i : Fin cellCount) : Cell := unpackCell (cellTable.get i.val)
noncomputable def kind (i : Fin cellCount) := (cells i).kind
noncomputable def ridgeList := Papers.RationalityTen.ConcreteGrowth.ridgeList cells
noncomputable def literalCompatible (a b : Fin cellCount) :=
  Papers.RationalityTen.ConcreteGrowth.compatible (cells a) (cells b)
def root : Fin cellCount := 219
end Papers.RationalityTen.FacetUniverses.FullSmall

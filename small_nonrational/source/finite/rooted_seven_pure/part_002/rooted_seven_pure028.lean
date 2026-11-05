module
prelude
public import RootedSevenPure028Data000

@[expose] public section
namespace Papers.RationalityTen.FacetUniverses.RootedSevenPure028
open Papers.RationalityTen.ConcreteGrowth
abbrev cellCount : Nat := 406
def dispatch : Table (Nat → Nat) :=
(.leaf Data.Part000.lookup)
def rawCells (i : Nat) : Cell :=
  Papers.RationalityTen.PackedFacetCells.unpack ((dispatch.get i) i)
def cells (i : Fin cellCount) : Cell := rawCells i.val
def kind (i : Fin cellCount) := (cells i).kind
def ridgeList := Papers.RationalityTen.ConcreteGrowth.ridgeList cells
def literalCompatible (a b : Fin cellCount) :=
  Papers.RationalityTen.ConcreteGrowth.compatible (cells a) (cells b)
end Papers.RationalityTen.FacetUniverses.RootedSevenPure028

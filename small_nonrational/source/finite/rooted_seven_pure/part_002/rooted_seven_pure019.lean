module
prelude
public import RootedSevenPure019Data000
public import RootedSevenPure019Data001

@[expose] public section
namespace Papers.RationalityTen.FacetUniverses.RootedSevenPure019
open Papers.RationalityTen.ConcreteGrowth
abbrev cellCount : Nat := 586
def dispatch : Table (Nat → Nat) :=
(.branch 512
 (.leaf Data.Part000.lookup)
 (.leaf Data.Part001.lookup))
def rawCells (i : Nat) : Cell :=
  Papers.RationalityTen.PackedFacetCells.unpack ((dispatch.get i) i)
def cells (i : Fin cellCount) : Cell := rawCells i.val
def kind (i : Fin cellCount) := (cells i).kind
def ridgeList := Papers.RationalityTen.ConcreteGrowth.ridgeList cells
def literalCompatible (a b : Fin cellCount) :=
  Papers.RationalityTen.ConcreteGrowth.compatible (cells a) (cells b)
end Papers.RationalityTen.FacetUniverses.RootedSevenPure019

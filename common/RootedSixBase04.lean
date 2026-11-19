module
prelude
public import RootedSixBase04Data000
public import RootedSixBase04Data001
public import RootedSixBase04Data002
public import RootedSixBase04Data003
public import RootedSixBase04Data004
public import RootedSixBase04Data005

@[expose] public section
/-! The exact original cell order is retained. This table alone asserts no
template coverage or realizability; the independent coverage certificates
refer to these complete decoded records. -/
namespace Papers.RationalityTen.FacetUniverses.RootedSixBase04
open Papers.RationalityTen.ConcreteGrowth
abbrev cellCount : Nat := 2824
def dispatch : Table (Nat → Nat) :=
(.branch 1536
 (.branch 512
 (.leaf Data.Part000.lookup)
 (.branch 1024
 (.leaf Data.Part001.lookup)
 (.leaf Data.Part002.lookup)))
 (.branch 2048
 (.leaf Data.Part003.lookup)
 (.branch 2560
 (.leaf Data.Part004.lookup)
 (.leaf Data.Part005.lookup))))
def rawCells (i : Nat) : Cell :=
  Papers.RationalityTen.PackedFacetCells.unpack ((dispatch.get i) i)
def cells (i : Fin cellCount) : Cell := rawCells i.val
def kind (i : Fin cellCount) : Nat := (cells i).kind
def ridgeList := Papers.RationalityTen.ConcreteGrowth.ridgeList cells
def literalCompatible (a b : Fin cellCount) : Bool :=
  Papers.RationalityTen.ConcreteGrowth.compatible (cells a) (cells b)
end Papers.RationalityTen.FacetUniverses.RootedSixBase04

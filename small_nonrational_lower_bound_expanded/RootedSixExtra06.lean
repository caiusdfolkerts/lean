module
prelude
public import RootedSixExtra06Data000
public import RootedSixExtra06Data001
public import RootedSixExtra06Data002
public import RootedSixExtra06Data003
public import RootedSixExtra06Data004

@[expose] public section
/-! The exact original cell order is retained. This table alone asserts no
template coverage or realizability; the independent coverage certificates
refer to these complete decoded records. -/
namespace Papers.RationalityTen.FacetUniverses.RootedSixExtra06
open Papers.RationalityTen.ConcreteGrowth
abbrev cellCount : Nat := 2300
def dispatch : Table (Nat → Nat) :=
(.branch 1024
 (.branch 512
 (.leaf Data.Part000.lookup)
 (.leaf Data.Part001.lookup))
 (.branch 1536
 (.leaf Data.Part002.lookup)
 (.branch 2048
 (.leaf Data.Part003.lookup)
 (.leaf Data.Part004.lookup))))
def rawCells (i : Nat) : Cell :=
  Papers.RationalityTen.PackedFacetCells.unpack ((dispatch.get i) i)
def cells (i : Fin cellCount) : Cell := rawCells i.val
def kind (i : Fin cellCount) : Nat := (cells i).kind
def ridgeList := Papers.RationalityTen.ConcreteGrowth.ridgeList cells
def literalCompatible (a b : Fin cellCount) : Bool :=
  Papers.RationalityTen.ConcreteGrowth.compatible (cells a) (cells b)
end Papers.RationalityTen.FacetUniverses.RootedSixExtra06

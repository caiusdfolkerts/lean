module
prelude
public import RootedSixExtra03Data000
public import RootedSixExtra03Data001
public import RootedSixExtra03Data002
public import RootedSixExtra03Data003
public import RootedSixExtra03Data004
public import RootedSixExtra03Data005
public import RootedSixExtra03Data006

@[expose] public section
/-! The exact original cell order is retained. This table alone asserts no
template coverage or realizability; the independent coverage certificates
refer to these complete decoded records. -/
namespace Papers.RationalityTen.FacetUniverses.RootedSixExtra03
open Papers.RationalityTen.ConcreteGrowth
abbrev cellCount : Nat := 3150
def dispatch : Table (Nat → Nat) :=
(.branch 1536
 (.branch 512
 (.leaf Data.Part000.lookup)
 (.branch 1024
 (.leaf Data.Part001.lookup)
 (.leaf Data.Part002.lookup)))
 (.branch 2560
 (.branch 2048
 (.leaf Data.Part003.lookup)
 (.leaf Data.Part004.lookup))
 (.branch 3072
 (.leaf Data.Part005.lookup)
 (.leaf Data.Part006.lookup))))
def rawCells (i : Nat) : Cell :=
  Papers.RationalityTen.PackedFacetCells.unpack ((dispatch.get i) i)
def cells (i : Fin cellCount) : Cell := rawCells i.val
def kind (i : Fin cellCount) : Nat := (cells i).kind
def ridgeList := Papers.RationalityTen.ConcreteGrowth.ridgeList cells
def literalCompatible (a b : Fin cellCount) : Bool :=
  Papers.RationalityTen.ConcreteGrowth.compatible (cells a) (cells b)
end Papers.RationalityTen.FacetUniverses.RootedSixExtra03

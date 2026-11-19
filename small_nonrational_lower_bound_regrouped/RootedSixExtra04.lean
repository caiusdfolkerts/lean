module
prelude
public import RootedSixExtra04Data000
public import RootedSixExtra04Data001
public import RootedSixExtra04Data002
public import RootedSixExtra04Data003
public import RootedSixExtra04Data004
public import RootedSixExtra04Data005
public import RootedSixExtra04Data006
public import RootedSixExtra04Data007

@[expose] public section
/-! The exact original cell order is retained. This table alone asserts no
template coverage or realizability; the independent coverage certificates
refer to these complete decoded records. -/
namespace Papers.RationalityTen.FacetUniverses.RootedSixExtra04
open Papers.RationalityTen.ConcreteGrowth
abbrev cellCount : Nat := 3640
def dispatch : Table (Nat → Nat) :=
(.branch 2048
 (.branch 1024
 (.branch 512
 (.leaf Data.Part000.lookup)
 (.leaf Data.Part001.lookup))
 (.branch 1536
 (.leaf Data.Part002.lookup)
 (.leaf Data.Part003.lookup)))
 (.branch 3072
 (.branch 2560
 (.leaf Data.Part004.lookup)
 (.leaf Data.Part005.lookup))
 (.branch 3584
 (.leaf Data.Part006.lookup)
 (.leaf Data.Part007.lookup))))
def rawCells (i : Nat) : Cell :=
  Papers.RationalityTen.PackedFacetCells.unpack ((dispatch.get i) i)
def cells (i : Fin cellCount) : Cell := rawCells i.val
def kind (i : Fin cellCount) : Nat := (cells i).kind
def ridgeList := Papers.RationalityTen.ConcreteGrowth.ridgeList cells
def literalCompatible (a b : Fin cellCount) : Bool :=
  Papers.RationalityTen.ConcreteGrowth.compatible (cells a) (cells b)
end Papers.RationalityTen.FacetUniverses.RootedSixExtra04

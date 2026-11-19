module
prelude
public import RootedSixExtra00Data000
public import RootedSixExtra00Data001
public import RootedSixExtra00Data002
public import RootedSixExtra00Data003
public import RootedSixExtra00Data004
public import RootedSixExtra00Data005
public import RootedSixExtra00Data006
public import RootedSixExtra00Data007
public import RootedSixExtra00Data008
public import RootedSixExtra00Data009
public import RootedSixExtra00Data010
public import RootedSixExtra00Data011
public import RootedSixExtra00Data012
public import RootedSixExtra00Data013
public import RootedSixExtra00Data014
public import RootedSixExtra00Data015
public import RootedSixExtra00Data016
public import RootedSixExtra00Data017

@[expose] public section
/-! The exact original cell order is retained. This table alone asserts no
template coverage or realizability; the independent coverage certificates
refer to these complete decoded records. -/
namespace Papers.RationalityTen.FacetUniverses.RootedSixExtra00
open Papers.RationalityTen.ConcreteGrowth
abbrev cellCount : Nat := 8824
def dispatch : Table (Nat → Nat) :=
(.branch 4608
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
 (.branch 4096
 (.leaf Data.Part007.lookup)
 (.leaf Data.Part008.lookup)))))
 (.branch 6656
 (.branch 5632
 (.branch 5120
 (.leaf Data.Part009.lookup)
 (.leaf Data.Part010.lookup))
 (.branch 6144
 (.leaf Data.Part011.lookup)
 (.leaf Data.Part012.lookup)))
 (.branch 7680
 (.branch 7168
 (.leaf Data.Part013.lookup)
 (.leaf Data.Part014.lookup))
 (.branch 8192
 (.leaf Data.Part015.lookup)
 (.branch 8704
 (.leaf Data.Part016.lookup)
 (.leaf Data.Part017.lookup))))))
def rawCells (i : Nat) : Cell :=
  Papers.RationalityTen.PackedFacetCells.unpack ((dispatch.get i) i)
def cells (i : Fin cellCount) : Cell := rawCells i.val
def kind (i : Fin cellCount) : Nat := (cells i).kind
def ridgeList := Papers.RationalityTen.ConcreteGrowth.ridgeList cells
def literalCompatible (a b : Fin cellCount) : Bool :=
  Papers.RationalityTen.ConcreteGrowth.compatible (cells a) (cells b)
end Papers.RationalityTen.FacetUniverses.RootedSixExtra00

module
prelude
public import RootedSixExtra02Data000
public import RootedSixExtra02Data001
public import RootedSixExtra02Data002
public import RootedSixExtra02Data003
public import RootedSixExtra02Data004
public import RootedSixExtra02Data005
public import RootedSixExtra02Data006
public import RootedSixExtra02Data007
public import RootedSixExtra02Data008
public import RootedSixExtra02Data009
public import RootedSixExtra02Data010
public import RootedSixExtra02Data011
public import RootedSixExtra02Data012

@[expose] public section
/-! The exact original cell order is retained. This table alone asserts no
template coverage or realizability; the independent coverage certificates
refer to these complete decoded records. -/
namespace Papers.RationalityTen.FacetUniverses.RootedSixExtra02
open Papers.RationalityTen.ConcreteGrowth
abbrev cellCount : Nat := 6620
def dispatch : Table (Nat → Nat) :=
(.branch 3072
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
 (.branch 4608
 (.branch 3584
 (.leaf Data.Part006.lookup)
 (.branch 4096
 (.leaf Data.Part007.lookup)
 (.leaf Data.Part008.lookup)))
 (.branch 5632
 (.branch 5120
 (.leaf Data.Part009.lookup)
 (.leaf Data.Part010.lookup))
 (.branch 6144
 (.leaf Data.Part011.lookup)
 (.leaf Data.Part012.lookup)))))
def rawCells (i : Nat) : Cell :=
  Papers.RationalityTen.PackedFacetCells.unpack ((dispatch.get i) i)
def cells (i : Fin cellCount) : Cell := rawCells i.val
def kind (i : Fin cellCount) : Nat := (cells i).kind
def ridgeList := Papers.RationalityTen.ConcreteGrowth.ridgeList cells
def literalCompatible (a b : Fin cellCount) : Bool :=
  Papers.RationalityTen.ConcreteGrowth.compatible (cells a) (cells b)
end Papers.RationalityTen.FacetUniverses.RootedSixExtra02

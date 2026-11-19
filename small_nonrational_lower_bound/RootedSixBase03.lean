module
prelude
public import RootedSixBase03Data000
public import RootedSixBase03Data001
public import RootedSixBase03Data002
public import RootedSixBase03Data003
public import RootedSixBase03Data004
public import RootedSixBase03Data005
public import RootedSixBase03Data006
public import RootedSixBase03Data007
public import RootedSixBase03Data008
public import RootedSixBase03Data009
public import RootedSixBase03Data010

@[expose] public section
/-! The exact original cell order is retained. This table alone asserts no
template coverage or realizability; the independent coverage certificates
refer to these complete decoded records. -/
namespace Papers.RationalityTen.FacetUniverses.RootedSixBase03
open Papers.RationalityTen.ConcreteGrowth
abbrev cellCount : Nat := 5238
def dispatch : Table (Nat → Nat) :=
(.branch 2560
 (.branch 1024
 (.branch 512
 (.leaf Data.Part000.lookup)
 (.leaf Data.Part001.lookup))
 (.branch 1536
 (.leaf Data.Part002.lookup)
 (.branch 2048
 (.leaf Data.Part003.lookup)
 (.leaf Data.Part004.lookup))))
 (.branch 4096
 (.branch 3072
 (.leaf Data.Part005.lookup)
 (.branch 3584
 (.leaf Data.Part006.lookup)
 (.leaf Data.Part007.lookup)))
 (.branch 4608
 (.leaf Data.Part008.lookup)
 (.branch 5120
 (.leaf Data.Part009.lookup)
 (.leaf Data.Part010.lookup)))))
def rawCells (i : Nat) : Cell :=
  Papers.RationalityTen.PackedFacetCells.unpack ((dispatch.get i) i)
def cells (i : Fin cellCount) : Cell := rawCells i.val
def kind (i : Fin cellCount) : Nat := (cells i).kind
def ridgeList := Papers.RationalityTen.ConcreteGrowth.ridgeList cells
def literalCompatible (a b : Fin cellCount) : Bool :=
  Papers.RationalityTen.ConcreteGrowth.compatible (cells a) (cells b)
end Papers.RationalityTen.FacetUniverses.RootedSixBase03

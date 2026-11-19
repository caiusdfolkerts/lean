module
prelude
public import RootedSixBase02Data000
public import RootedSixBase02Data001
public import RootedSixBase02Data002
public import RootedSixBase02Data003
public import RootedSixBase02Data004
public import RootedSixBase02Data005
public import RootedSixBase02Data006
public import RootedSixBase02Data007
public import RootedSixBase02Data008
public import RootedSixBase02Data009
public import RootedSixBase02Data010
public import RootedSixBase02Data011
public import RootedSixBase02Data012
public import RootedSixBase02Data013
public import RootedSixBase02Data014
public import RootedSixBase02Data015

@[expose] public section
/-! The exact original cell order is retained. This table alone asserts no
template coverage or realizability; the independent coverage certificates
refer to these complete decoded records. -/
namespace Papers.RationalityTen.FacetUniverses.RootedSixBase02
open Papers.RationalityTen.ConcreteGrowth
abbrev cellCount : Nat := 8084
def dispatch : Table (Nat → Nat) :=
(.branch 4096
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
 (.branch 6144
 (.branch 5120
 (.branch 4608
 (.leaf Data.Part008.lookup)
 (.leaf Data.Part009.lookup))
 (.branch 5632
 (.leaf Data.Part010.lookup)
 (.leaf Data.Part011.lookup)))
 (.branch 7168
 (.branch 6656
 (.leaf Data.Part012.lookup)
 (.leaf Data.Part013.lookup))
 (.branch 7680
 (.leaf Data.Part014.lookup)
 (.leaf Data.Part015.lookup)))))
def rawCells (i : Nat) : Cell :=
  Papers.RationalityTen.PackedFacetCells.unpack ((dispatch.get i) i)
def cells (i : Fin cellCount) : Cell := rawCells i.val
def kind (i : Fin cellCount) : Nat := (cells i).kind
def ridgeList := Papers.RationalityTen.ConcreteGrowth.ridgeList cells
def literalCompatible (a b : Fin cellCount) : Bool :=
  Papers.RationalityTen.ConcreteGrowth.compatible (cells a) (cells b)
end Papers.RationalityTen.FacetUniverses.RootedSixBase02

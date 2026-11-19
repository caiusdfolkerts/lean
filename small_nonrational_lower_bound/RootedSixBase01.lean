module
prelude
public import RootedSixBase01Data000
public import RootedSixBase01Data001
public import RootedSixBase01Data002
public import RootedSixBase01Data003
public import RootedSixBase01Data004
public import RootedSixBase01Data005
public import RootedSixBase01Data006
public import RootedSixBase01Data007
public import RootedSixBase01Data008
public import RootedSixBase01Data009
public import RootedSixBase01Data010
public import RootedSixBase01Data011
public import RootedSixBase01Data012
public import RootedSixBase01Data013
public import RootedSixBase01Data014
public import RootedSixBase01Data015
public import RootedSixBase01Data016
public import RootedSixBase01Data017
public import RootedSixBase01Data018
public import RootedSixBase01Data019
public import RootedSixBase01Data020
public import RootedSixBase01Data021
public import RootedSixBase01Data022
public import RootedSixBase01Data023
public import RootedSixBase01Data024
public import RootedSixBase01Data025
public import RootedSixBase01Data026
public import RootedSixBase01Data027
public import RootedSixBase01Data028
public import RootedSixBase01Data029

@[expose] public section
/-! The exact original cell order is retained. This table alone asserts no
template coverage or realizability; the independent coverage certificates
refer to these complete decoded records. -/
namespace Papers.RationalityTen.FacetUniverses.RootedSixBase01
open Papers.RationalityTen.ConcreteGrowth
abbrev cellCount : Nat := 15246
def dispatch : Table (Nat → Nat) :=
(.branch 7680
 (.branch 3584
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
 (.branch 5632
 (.branch 4608
 (.branch 4096
 (.leaf Data.Part007.lookup)
 (.leaf Data.Part008.lookup))
 (.branch 5120
 (.leaf Data.Part009.lookup)
 (.leaf Data.Part010.lookup)))
 (.branch 6656
 (.branch 6144
 (.leaf Data.Part011.lookup)
 (.leaf Data.Part012.lookup))
 (.branch 7168
 (.leaf Data.Part013.lookup)
 (.leaf Data.Part014.lookup)))))
 (.branch 11264
 (.branch 9216
 (.branch 8192
 (.leaf Data.Part015.lookup)
 (.branch 8704
 (.leaf Data.Part016.lookup)
 (.leaf Data.Part017.lookup)))
 (.branch 10240
 (.branch 9728
 (.leaf Data.Part018.lookup)
 (.leaf Data.Part019.lookup))
 (.branch 10752
 (.leaf Data.Part020.lookup)
 (.leaf Data.Part021.lookup))))
 (.branch 13312
 (.branch 12288
 (.branch 11776
 (.leaf Data.Part022.lookup)
 (.leaf Data.Part023.lookup))
 (.branch 12800
 (.leaf Data.Part024.lookup)
 (.leaf Data.Part025.lookup)))
 (.branch 14336
 (.branch 13824
 (.leaf Data.Part026.lookup)
 (.leaf Data.Part027.lookup))
 (.branch 14848
 (.leaf Data.Part028.lookup)
 (.leaf Data.Part029.lookup))))))
def rawCells (i : Nat) : Cell :=
  Papers.RationalityTen.PackedFacetCells.unpack ((dispatch.get i) i)
def cells (i : Fin cellCount) : Cell := rawCells i.val
def kind (i : Fin cellCount) : Nat := (cells i).kind
def ridgeList := Papers.RationalityTen.ConcreteGrowth.ridgeList cells
def literalCompatible (a b : Fin cellCount) : Bool :=
  Papers.RationalityTen.ConcreteGrowth.compatible (cells a) (cells b)
end Papers.RationalityTen.FacetUniverses.RootedSixBase01

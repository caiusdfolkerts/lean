module
prelude
public import RootedSixBase00Data000
public import RootedSixBase00Data001
public import RootedSixBase00Data002
public import RootedSixBase00Data003
public import RootedSixBase00Data004
public import RootedSixBase00Data005
public import RootedSixBase00Data006
public import RootedSixBase00Data007
public import RootedSixBase00Data008
public import RootedSixBase00Data009
public import RootedSixBase00Data010
public import RootedSixBase00Data011
public import RootedSixBase00Data012
public import RootedSixBase00Data013
public import RootedSixBase00Data014
public import RootedSixBase00Data015
public import RootedSixBase00Data016
public import RootedSixBase00Data017
public import RootedSixBase00Data018
public import RootedSixBase00Data019
public import RootedSixBase00Data020
public import RootedSixBase00Data021
public import RootedSixBase00Data022
public import RootedSixBase00Data023
public import RootedSixBase00Data024
public import RootedSixBase00Data025
public import RootedSixBase00Data026
public import RootedSixBase00Data027
public import RootedSixBase00Data028
public import RootedSixBase00Data029
public import RootedSixBase00Data030
public import RootedSixBase00Data031
public import RootedSixBase00Data032
public import RootedSixBase00Data033
public import RootedSixBase00Data034
public import RootedSixBase00Data035
public import RootedSixBase00Data036
public import RootedSixBase00Data037
public import RootedSixBase00Data038
public import RootedSixBase00Data039
public import RootedSixBase00Data040
public import RootedSixBase00Data041
public import RootedSixBase00Data042

@[expose] public section
/-! The exact original cell order is retained. This table alone asserts no
template coverage or realizability; the independent coverage certificates
refer to these complete decoded records. -/
namespace Papers.RationalityTen.FacetUniverses.RootedSixBase00
open Papers.RationalityTen.ConcreteGrowth
abbrev cellCount : Nat := 21976
def dispatch : Table (Nat → Nat) :=
(.branch 10752
 (.branch 5120
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
 (.branch 3584
 (.branch 3072
 (.leaf Data.Part005.lookup)
 (.leaf Data.Part006.lookup))
 (.branch 4096
 (.leaf Data.Part007.lookup)
 (.branch 4608
 (.leaf Data.Part008.lookup)
 (.leaf Data.Part009.lookup)))))
 (.branch 7680
 (.branch 6144
 (.branch 5632
 (.leaf Data.Part010.lookup)
 (.leaf Data.Part011.lookup))
 (.branch 6656
 (.leaf Data.Part012.lookup)
 (.branch 7168
 (.leaf Data.Part013.lookup)
 (.leaf Data.Part014.lookup))))
 (.branch 9216
 (.branch 8192
 (.leaf Data.Part015.lookup)
 (.branch 8704
 (.leaf Data.Part016.lookup)
 (.leaf Data.Part017.lookup)))
 (.branch 9728
 (.leaf Data.Part018.lookup)
 (.branch 10240
 (.leaf Data.Part019.lookup)
 (.leaf Data.Part020.lookup))))))
 (.branch 16384
 (.branch 13312
 (.branch 11776
 (.branch 11264
 (.leaf Data.Part021.lookup)
 (.leaf Data.Part022.lookup))
 (.branch 12288
 (.leaf Data.Part023.lookup)
 (.branch 12800
 (.leaf Data.Part024.lookup)
 (.leaf Data.Part025.lookup))))
 (.branch 14848
 (.branch 13824
 (.leaf Data.Part026.lookup)
 (.branch 14336
 (.leaf Data.Part027.lookup)
 (.leaf Data.Part028.lookup)))
 (.branch 15360
 (.leaf Data.Part029.lookup)
 (.branch 15872
 (.leaf Data.Part030.lookup)
 (.leaf Data.Part031.lookup)))))
 (.branch 18944
 (.branch 17408
 (.branch 16896
 (.leaf Data.Part032.lookup)
 (.leaf Data.Part033.lookup))
 (.branch 17920
 (.leaf Data.Part034.lookup)
 (.branch 18432
 (.leaf Data.Part035.lookup)
 (.leaf Data.Part036.lookup))))
 (.branch 20480
 (.branch 19456
 (.leaf Data.Part037.lookup)
 (.branch 19968
 (.leaf Data.Part038.lookup)
 (.leaf Data.Part039.lookup)))
 (.branch 20992
 (.leaf Data.Part040.lookup)
 (.branch 21504
 (.leaf Data.Part041.lookup)
 (.leaf Data.Part042.lookup)))))))
def rawCells (i : Nat) : Cell :=
  Papers.RationalityTen.PackedFacetCells.unpack ((dispatch.get i) i)
def cells (i : Fin cellCount) : Cell := rawCells i.val
def kind (i : Fin cellCount) : Nat := (cells i).kind
def ridgeList := Papers.RationalityTen.ConcreteGrowth.ridgeList cells
def literalCompatible (a b : Fin cellCount) : Bool :=
  Papers.RationalityTen.ConcreteGrowth.compatible (cells a) (cells b)
end Papers.RationalityTen.FacetUniverses.RootedSixBase00

module
prelude
public import RootedSixBase02GrowthCacheData
public import RootedSixBase02FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0138
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 8084
abbrev nodeCount : Nat := 61
abbrev leafCount : Nat := 1
def widths : PackedRawNatGrowth.Widths := ⟨13,6,6,1⟩
def blocks : Table PackedRawNatGrowth.Block :=
(.leaf ⟨0x18ef2decf796e63acb6b3d65b1aef2d6e7796a6bacb4b9d65a1bef2ceef79666facb2bbd65924ef2c757796293acb0d5d65825ef2bf5f795e97acaed7d65728ef2b777795aa3acacddd65618e429acf214c7390a5d5c85280070000000ec00010780a6809852c64c294000600000077be80000809c29801214b1890a500018000001defa80002678cb7b33e5b1ce32d6e4f9686d3cb3ba9e599b272cae93964ab8cb1d53e58254f2bf5a795e949caed64e57284f2b772795aa09cacdc4e5600048000000ec424000131b900dedc7d72223e26911f0bd48f818a47bef503de6281ee800400000038efa429800019bb07f80cc3f60601f6000300047303cb7084411c000201a82f82d017a00040008210f96b10907e8104000280000065ac89e5ac17c2000000000055cb787ec16200020d902cc0c416000040008e20f96e10887ec11c4000000059113cb708441643000000058093cb70844160302f071036038400080000005f2dc2110fb023800051ae1838168c0c00080011cc172dc2110fb038811c00030000000c18c2e5b860c1f7065100000000001572dc3030710000835631c02a18c000100084a22e5bc4241f606a8268000600000000005518d82f4000300000000005518c0354000300000003510bcb708440d4300000003408bcb708440d030260470d301d86540d602a06a30703484381a06500ce02806600080000000fdf5053000033651af8110d700786ae0b62f501915b00c0ad465c56602c2af000800047305df5053011c000201202f828c17600040008210e35b0a6820860000000be50635b05f020860000000af12635c0a682bc63420b3020057000100023883efa86b814c0471000000016444f7d435e0a602c8803e1e3000100057113df50d702980ae047140000002988c77d435c0f18530803a0e205c06f80010000000befa86ae14c0470000a0000000000abbea1ab83880004000000000055df58d5c1a6000200d02c000040013441c5e809a0000c0000000001545e80b00000c00000029884f7d42b60a60238800000008e20fbea15a823860000002b242bbea15901d8600000000002fbea1578238000400000003510bdf505300d4300000003308ddf505300cc33521c6b678e2013070a00060014b253be80a580006c223ed8101f5000100052858ef946ec14a180000065a885e5a80e4200000003408bcb70de00d0364e2813c693fc0008006e06872d43701088000800000000001e1550a68000600000000001e1630a6000060960980ca04b800100000007efa46e014b00010000000118c2470a08c10000000229848e6811423081bc0028dcc2086e000060014b253bea0a58000600e074206039800100052845ef986ec14a18000006f9886ef980e8200000003308ddf50de00cc3644208b6190380008000001c77d43730a58000800000008a61238504508000000118c2473408c10209104600876000400370343be61b8053000040000000000712160534000300000000007121d05300003,0x1f2000001e8600001dec00001bdb00001ab700001a030000195b0000190c000018a300001808000017ac00001750000016a8000015f30000158a000015210000146c00001410000013b400001358000012fc000011d8000010a70000101900000fbd00000f6100000ec600000e5d00000dce00000d6500000cbd00000c5400000beb00000b7600000b1a00000ab100000a55000009f90000099000000934000008d800000831000007a300000754000006f80000065d00000601000005a50000050a000004bb0000046c000003c500000337000002e80000028c000001f1000001a200000153000000b80000005c00000000⟩)
def counterTable : Table Nat :=
(.leaf 0x10000100000000200002000000004000000000400080000800008001000010000108020000200002200400004000002000000080000080100001000011000000020000210000000400004200000008000088010000100001180200002000003000000040000040080000800008c0100000000001002000000000020040000400004200000008000084000000100001000200002000021004000000000440000000000000c000000000001100000002000022000000040000440000000800008c0000001000011000000020000220040000400000400800008000008010000000000100200000000002004000040000440000000800000800000010000010000000200000200400004000042000000080000840000001000010002000020000210000000400000200000008000008000000100001080200000000021004000000000420080000800008401000000000010000000000000200000004000040008000080000840000001000000800000020000020000000400004200800000000008000000000000100000002000021004000000000420080000000008401)
def codes (i : Nat) : Nat :=
  let b := blocks.get (i / 128)
  PackedRawNatGrowth.drop
    (PackedRawNatGrowth.take 32 (PackedRawNatGrowth.drop (32*(i%128)) b.offsets)) b.payload
def counters (i : Nat) : Nat :=
  PackedRawNatGrowth.take 55 (PackedRawNatGrowth.drop (55*(i%128)) (counterTable.get (i/128)))
def rawNodes (i : Nat) := PackedRawNatGrowth.decodeNode widths (codes i)

def leafTable : Table (List Nat) :=
(.leaf [])
def rawLeaves := leafTable.get

def leaves : Fin leafCount → List (Fin cellCount) := decodedLeaves rawLeaves
def quota : Nat → Nat
  | 0 => 1
  | 1 => 0
  | 2 => 7
  | 3 => 1
  | 4 => 0
  | 5 => 0
  | 6 => 0
  | 7 => 1
  | 8 => 0
  | 9 => 0
  | 10 => 0
  | _ => 0

def nodeTest (i : Nat) : Bool :=
  SubsumedCounterReplay.check widths cellCount 1024 48 leafCount nodeCount
    Papers.RationalityTen.RootedCaches.RootedSixBase02.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixBase02.badMasks
    Papers.RationalityTen.RootedCaches.RootedSixBase02.kindMasks Papers.RationalityTen.RootedCaches.RootedSixBase02.keys Papers.RationalityTen.RootedCaches.RootedSixBase02.fastKind quota
    Papers.RationalityTen.FacetUniverses.RootedSixBase02.Generators.FastWords.rawMaps rawLeaves codes counters i
theorem nodeTest_sound (i : Nat) (h : nodeTest i = true) :
    nodeBounds cellCount 1024 48 leafCount nodeCount (rawNodes i) = true ∧
      SubsumedRawGrowth.nodeCheck Papers.RationalityTen.RootedCaches.RootedSixBase02.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixBase02.badMasks
        Papers.RationalityTen.RootedCaches.RootedSixBase02.kindMasks Papers.RationalityTen.RootedCaches.RootedSixBase02.keys Papers.RationalityTen.RootedCaches.RootedSixBase02.fastKind quota
        Papers.RationalityTen.FacetUniverses.RootedSixBase02.Generators.FastWords.rawMaps rawLeaves rawNodes i = true :=
  SubsumedCounterReplay.check_sound widths cellCount 1024 48 leafCount nodeCount
    Papers.RationalityTen.RootedCaches.RootedSixBase02.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixBase02.badMasks
    Papers.RationalityTen.RootedCaches.RootedSixBase02.kindMasks Papers.RationalityTen.RootedCaches.RootedSixBase02.keys Papers.RationalityTen.RootedCaches.RootedSixBase02.fastKind quota
    Papers.RationalityTen.FacetUniverses.RootedSixBase02.Generators.FastWords.rawMaps rawLeaves codes counters i h
def leafTest (i : Nat) : Bool :=
  listBounds cellCount (rawLeaves i) &&
    (WitnessGrowthDAG.closedCheck FacetUniverses.RootedSixBase02.ridgeList
      ((rawLeaves i).map (Fin.ofNat cellCount)) &&
      decide (((rawLeaves i).map (Fin.ofNat cellCount)).Nodup))

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0138

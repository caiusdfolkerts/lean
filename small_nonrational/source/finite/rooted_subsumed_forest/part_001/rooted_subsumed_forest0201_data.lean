module
prelude
public import RootedSixBase00GrowthCacheData
public import RootedSixBase00FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0201
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 21976
abbrev nodeCount : Nat := 50
abbrev leafCount : Nat := 1
def widths : PackedRawNatGrowth.Widths := ⟨15,6,7,1⟩
def blocks : Table PackedRawNatGrowth.Block :=
(.leaf ⟨0xc30a7d6cb0a7d4c70a7d2cf0a7d0d30a7ced70a7ccdb0a7caf30a7c8df0a7c6f70a7c50b0a7c30f0a7c0e30a7befb0a7bceb0a7bb030a7b9130a7b71b0a7b4e70a7b2ff0a7b0ef0a7af070a7ad170a7ab1f0a7a922fa4a72afa4a526fa4a32efa4a132fa49f36fa49d3afa49b52fa4993efa49756fa4956afa4936efa49142fa48f5afa48d4afa48b62fa48972fa4877afa48546fa4835efa4814efa47f66fa47d76fa47b7efa47922d019326d0191224018f264018d217018b25701892ad017b32d01792a401773240175297017331701712ed016336d01612e4015f364015d2d7015b357015952d014b6ad014952401476a401455170143697014156d01336ed0131564012f6e4012d557012b6d7012962d011b7ad011962401177a401156170113797011000a8000000078000087b42fe00008000000e356e8000080240c5805c0c50000800000035a6c400004000000000034d36206280000672cab76aacab6a02a09e4bd70976a5709741a7097202709701a6096e026096c00120000003485fb00002395834d00010000000d6aeb84da0000300000000000d42f80299000030d4841f014841e0d4041d014041c3d4041b314041a00060000001642fd84f200003000000083c3442fd841e1000000000003617ec279041c000040000000bf69442fd84b810294154800080000005a17ec25b00001800000000006a17bc15a80001cd8eabfdb8eabc988022b067420f807420f066820e806820e1e6420d986420d00048000000b217f400008044043c000400000017a90802b80000c04209dc01609d400080000002da908043c05700002000000000006b521013b80001867c2e2007c2e196682e110682e086782e000782df80030000000e213d022c0000180000005c31c2170c27a080000000000350b7e13d022c0000241700b6000080000003617f420f00001986c05c800080000001e11680d400d200004000000020340c22d8101011430000000bfa9842fe841c102600cf000080000003613d020e00001800000000001e13a021401aa0000408b551f24b5519009834d0c3831600383150c2031400203130c08312000831100090000000d42ff800010454086000080000002f548c00008c280ad000040000002daa4003d00000c00000000001706a002b00000e02549d232549c8022041401a040c32203b431a03ac31203540120350310034c010034988c0345b8c03400030000000170bfe0d340000c000000000059a6c40c580000c02005c001c05b400080000001b0bfe04140000d71f4f7400040000000f0bfe05c008280002000000000006b512025d0000180000005ff8a217fc0b68971951e0c14067c00080000001b0bfe0d3408180002002c087800080000002f521013a80001800000027530b521013a810f180000000000b213d80d08000180000000d412a17fc06a080000000690950bfe0348440601a000020000000b85ff062a000060c5032800020000000d85c302180000600000000002c85cf035800006083020800020000000b85ff062600006302031000020000000d85f3063e04400001000000000000f067006b0082000020200082000080000002e17fc18880001800000000003617cc18e811000004,0x1b2b00001aba00001a2d000019c900001878000017f8000017940000168800001633000015c00000156b000014eb0000148700001336000012b60000120b000011a70000109b0000104600000fd300000f5300000ec400000e6000000e0b00000d8b00000d1800000bc700000b5600000ad600000a72000008be0000085a000007be0000072f000006cb00000676000005cb0000054b000004e7000004830000042e000003d900000359000002d900000275000001f500000166000000f30000007300000000⟩)
def counterTable : Table Nat :=
(.leaf 0x80200000000001000200000000020004000002000400000000040008020000000800100000000020002000000000400040000000008000000000000180010000000002000000000000040004000000000800080000000008001004000000100020080000004000401000000040008000000001000100000000020000000000000600040000000008000800000000180010000000003000000000000040000000000000800080000000018001000000000100020080000000000401000000040008000000001000100000000020002000400000200040000000008000800000000180010040000001000200000000040000000000000c00080200000008001004000000200000000000004000400000000080000000000001000000000000020002000000000400040000000008000800000000100010000000003000200000000060004000000000800080000000018001)
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
  | 2 => 0
  | 3 => 7
  | 4 => 0
  | 5 => 0
  | 6 => 0
  | 7 => 0
  | 8 => 1
  | 9 => 1
  | 10 => 0
  | _ => 0

def nodeTest (i : Nat) : Bool :=
  SubsumedCounterReplay.check widths cellCount 1024 96 leafCount nodeCount
    Papers.RationalityTen.RootedCaches.RootedSixBase00.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixBase00.badMasks
    Papers.RationalityTen.RootedCaches.RootedSixBase00.kindMasks Papers.RationalityTen.RootedCaches.RootedSixBase00.keys Papers.RationalityTen.RootedCaches.RootedSixBase00.fastKind quota
    Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.FastWords.rawMaps rawLeaves codes counters i
theorem nodeTest_sound (i : Nat) (h : nodeTest i = true) :
    nodeBounds cellCount 1024 96 leafCount nodeCount (rawNodes i) = true ∧
      SubsumedRawGrowth.nodeCheck Papers.RationalityTen.RootedCaches.RootedSixBase00.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixBase00.badMasks
        Papers.RationalityTen.RootedCaches.RootedSixBase00.kindMasks Papers.RationalityTen.RootedCaches.RootedSixBase00.keys Papers.RationalityTen.RootedCaches.RootedSixBase00.fastKind quota
        Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.FastWords.rawMaps rawLeaves rawNodes i = true :=
  SubsumedCounterReplay.check_sound widths cellCount 1024 96 leafCount nodeCount
    Papers.RationalityTen.RootedCaches.RootedSixBase00.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixBase00.badMasks
    Papers.RationalityTen.RootedCaches.RootedSixBase00.kindMasks Papers.RationalityTen.RootedCaches.RootedSixBase00.keys Papers.RationalityTen.RootedCaches.RootedSixBase00.fastKind quota
    Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.FastWords.rawMaps rawLeaves codes counters i h
def leafTest (i : Nat) : Bool :=
  listBounds cellCount (rawLeaves i) &&
    (WitnessGrowthDAG.closedCheck FacetUniverses.RootedSixBase00.ridgeList
      ((rawLeaves i).map (Fin.ofNat cellCount)) &&
      decide (((rawLeaves i).map (Fin.ofNat cellCount)).Nodup))

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0201

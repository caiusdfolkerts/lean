module
prelude
public import RootedSixExtra05GrowthCacheData
public import RootedSixExtra05FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0861
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 2170
abbrev nodeCount : Nat := 15
abbrev leafCount : Nat := 1
def widths : PackedRawNatGrowth.Widths := ⟨12,4,9,1⟩
def blocks : Table PackedRawNatGrowth.Block :=
(.leaf ⟨0x49d585246ac2127160c918b044cd581256ac013315fc958afc4dd57d25eabe13715ec978af45ad5792a6abc16b15dca98aec5bd5752aeaba16f15ccab8ae45ed5712c6ab817b15bcb18adc48b0a324d851132c284b561400038000000dc000200a0a200485081a4280000c000001bb10000080101420680a000020000006ec3c00023cd2c21f29600f72afa7d957c3ec2bd9ee15e9154af085957545caba22e15cd0b0ae4889571474ab823a15bd110adc1870a30c205106902844881400026000000dc70000040030fb0c107c87883e0000c000002db100510000c0241f60060f903087c00018000005b6200a1000180143e40c01f000040000016d87828400064d657d25b2be13555ec96aaf45b65752ab2ba16d55ccaaaae45e65712c32b817955bcb0aadc0018000000dc7003ec0006000000c418358803e42846000000c3d8958783e428464835842612c01f495f4b44af08b25752f0ab896055c0bc0ade58056e00090000006e3801f40003000000620c1ac401f61443000000621c1ac421f41423000000620c1ac401f2140300000061ec4ac3c1f21403,0x9d900000942000008c40000069d000005fa00000557000004cd00000349000002f1000002990000016000000108000000b00000005800000000⟩)
def counterTable : Table Nat :=
(.leaf 0x4010000000000080200000000001000000000100020080000002000401000000040008020000000800100000000020002008000000400000100000008000000000000100010040000002000000800000040000010000000800000200000010000)
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
  | 1 => 3
  | 2 => 6
  | 3 => 2
  | 4 => 0
  | 5 => 0
  | 6 => 0
  | 7 => 0
  | 8 => 0
  | 9 => 1
  | 10 => 0
  | _ => 0

def nodeTest (i : Nat) : Bool :=
  SubsumedCounterReplay.check widths cellCount 1024 288 leafCount nodeCount
    Papers.RationalityTen.RootedCaches.RootedSixExtra05.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixExtra05.badMasks
    Papers.RationalityTen.RootedCaches.RootedSixExtra05.kindMasks Papers.RationalityTen.RootedCaches.RootedSixExtra05.keys Papers.RationalityTen.RootedCaches.RootedSixExtra05.fastKind quota
    Papers.RationalityTen.FacetUniverses.RootedSixExtra05.Generators.FastWords.rawMaps rawLeaves codes counters i
theorem nodeTest_sound (i : Nat) (h : nodeTest i = true) :
    nodeBounds cellCount 1024 288 leafCount nodeCount (rawNodes i) = true ∧
      SubsumedRawGrowth.nodeCheck Papers.RationalityTen.RootedCaches.RootedSixExtra05.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixExtra05.badMasks
        Papers.RationalityTen.RootedCaches.RootedSixExtra05.kindMasks Papers.RationalityTen.RootedCaches.RootedSixExtra05.keys Papers.RationalityTen.RootedCaches.RootedSixExtra05.fastKind quota
        Papers.RationalityTen.FacetUniverses.RootedSixExtra05.Generators.FastWords.rawMaps rawLeaves rawNodes i = true :=
  SubsumedCounterReplay.check_sound widths cellCount 1024 288 leafCount nodeCount
    Papers.RationalityTen.RootedCaches.RootedSixExtra05.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixExtra05.badMasks
    Papers.RationalityTen.RootedCaches.RootedSixExtra05.kindMasks Papers.RationalityTen.RootedCaches.RootedSixExtra05.keys Papers.RationalityTen.RootedCaches.RootedSixExtra05.fastKind quota
    Papers.RationalityTen.FacetUniverses.RootedSixExtra05.Generators.FastWords.rawMaps rawLeaves codes counters i h
def leafTest (i : Nat) : Bool :=
  listBounds cellCount (rawLeaves i) &&
    (WitnessGrowthDAG.closedCheck FacetUniverses.RootedSixExtra05.ridgeList
      ((rawLeaves i).map (Fin.ofNat cellCount)) &&
      decide (((rawLeaves i).map (Fin.ofNat cellCount)).Nodup))

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0861

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
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0822
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 2170
abbrev nodeCount : Nat := 23
abbrev leafCount : Nat := 1
def widths : PackedRawNatGrowth.Widths := ⟨12,5,9,1⟩
def blocks : Table PackedRawNatGrowth.Block :=
(.leaf ⟨0x24d561491558424bd60c90f5822655604955580263d5fc94f57e26d55f497557c26bd5ec96f57a2d555e4a955782d3d5dca8f5762dd55d4ab55742dbd5ccaaf5722f555c4b155702f3d5bcb0f56e242428c9290a22624284b490a0001c0000006e00010cd15f03f45740fc95c43325700fb15bc32c56e00202880050a103142800024000001bb100000801300100010000001ec40bc000030000000000e2c40bc000200042ac40bc000588000036015d0292c40ba000030fc024401006f00020000001ebc0ae800030000000000dabc00de00030c39608bcc5712c315c03ca56f0c295b80010a10304280001c000001bb0f0000800d0a103342800008000001bb0f2f10000c00000178b09b0f2f10508c80b0a200010000006ec40b9c00030000005d0292c3cba0140300000000006ec3cb9c00033ca1610f885803d955f4fa557c3e855ecf6157a45215e10a557545955d116157342855c910557147155c11c156f44055b8003c000001b8e0000093c74e44c1d3813c64cf4c1932400100188306b100510000c0000000002daff8500000c0000000002daf68500000c0045e0030d7600c25d10003000000b6c4014200030000005e0a16c40bc014230000005e0a16c40bc0140300000000001ec40ba0140000403014bc00042840001b0161ec4ac3c14200030000000000b6c3ca521400004,0xc8000000b4a00000ad800000a74000009e000000954000008fc000007fa0000076e00000716000006a40000064c000005f400000422000003620000030a000002b20000020c000001b40000015c000000f80000006400000000⟩)
def counterTable : Table Nat :=
(.leaf 0x401000000000008040000000000100800000000042010000000000040200000000000802000000080010040000000000201000000000004020000000400000400000000001008000000100000100000000000400000000040008020000000800100400000010002008000000200040100000004000804000000080000080000001000001000000020004010000000400080400000008001)
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
  | 1 => 1
  | 2 => 6
  | 3 => 1
  | 4 => 0
  | 5 => 0
  | 6 => 0
  | 7 => 0
  | 8 => 0
  | 9 => 2
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

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0822

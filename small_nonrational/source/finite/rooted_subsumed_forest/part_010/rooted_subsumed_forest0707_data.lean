module
prelude
public import RootedSixBase04GrowthCacheData
public import RootedSixBase04FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification
public import RootedSubsumedForest0707Packed000
public import RootedSubsumedForest0707Packed001

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0707
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 2824
abbrev nodeCount : Nat := 10223
abbrev leafCount : Nat := 18
def widths : PackedRawNatGrowth.Widths := ⟨12,14,11,5⟩
def blocks : Table PackedRawNatGrowth.Block :=
(.branch 50
 nodeBlocks000
 nodeBlocks001)
def counterTable : Table Nat :=
(.branch 50
 nodeCounters000
 nodeCounters001)
def codes (i : Nat) : Nat :=
  let b := blocks.get (i / 128)
  PackedRawNatGrowth.drop
    (PackedRawNatGrowth.take 32 (PackedRawNatGrowth.drop (32*(i%128)) b.offsets)) b.payload
def counters (i : Nat) : Nat :=
  PackedRawNatGrowth.take 55 (PackedRawNatGrowth.drop (55*(i%128)) (counterTable.get (i/128)))
def rawNodes (i : Nat) := PackedRawNatGrowth.decodeNode widths (codes i)

def leafTable : Table (List Nat) :=
(.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf [0,1,41,48,206,374,557,867,934,990,1267,2818])
 (.leaf [0,1,25,46,215,383,909,930,977,1254,1595,2821]))
 (.branch 3
 (.leaf [0,2,17,55,202,495,557,814,890,1267,1658,2818])
 (.leaf [0,1,6,17,297,439,557,807,990,1267,1462,2818])))
 (.branch 6
 (.branch 5
 (.leaf [0,1,41,48,218,362,556,884,1002,1194,1255,2820])
 (.leaf [0,1,25,46,227,371,864,989,1198,1242,1594,2823]))
 (.branch 7
 (.leaf [0,5,41,48,134,398,533,926,966,1188,1267,2812])
 (.branch 8
 (.leaf [0,5,41,48,189,311,398,533,966,1267,1440,2812])
 (.leaf [0,8,16,47,177,357,568,1001,1243,2822])))))
 (.branch 13
 (.branch 11
 (.branch 10
 (.leaf [0,25,41,48,172,216,360,933,1002,1255,1552,2820])
 (.leaf [0,5,9,77,175,405,518,842,966,1185,1510,2705]))
 (.branch 12
 (.leaf [0,5,10,76,172,409,542,766,825,954,1521,2709])
 (.leaf [0,5,10,76,172,409,545,758,825,954,1808,2813])))
 (.branch 15
 (.branch 14
 (.leaf [0,18,41,55,149,205,496,569,802,1266,1637,2819])
 (.leaf [0,5,40,46,134,413,530,765,942,1259,1534,2706]))
 (.branch 16
 (.leaf [0,15,43,56,144,260,354,544,817,1219,1699,2816])
 (.branch 17
 (.leaf [0,25,41,48,189,216,355,360,1002,1255,1552,2820])
 (.leaf [0,5,16,137,521,790,948,1249,1536,1850,2550]))))))
def rawLeaves := leafTable.get

def leaves : Fin leafCount → List (Fin cellCount) := decodedLeaves rawLeaves
def quota : Nat → Nat
  | 0 => 1
  | 1 => 3
  | 2 => 3
  | 3 => 5
  | 4 => 0
  | 5 => 0
  | 6 => 0
  | 7 => 0
  | 8 => 0
  | 9 => 1
  | 10 => 0
  | _ => 0

def nodeTest (i : Nat) : Bool :=
  SubsumedCounterReplay.check widths cellCount 1024 1152 leafCount nodeCount
    Papers.RationalityTen.RootedCaches.RootedSixBase04.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixBase04.badMasks
    Papers.RationalityTen.RootedCaches.RootedSixBase04.kindMasks Papers.RationalityTen.RootedCaches.RootedSixBase04.keys Papers.RationalityTen.RootedCaches.RootedSixBase04.fastKind quota
    Papers.RationalityTen.FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters i
theorem nodeTest_sound (i : Nat) (h : nodeTest i = true) :
    nodeBounds cellCount 1024 1152 leafCount nodeCount (rawNodes i) = true ∧
      SubsumedRawGrowth.nodeCheck Papers.RationalityTen.RootedCaches.RootedSixBase04.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixBase04.badMasks
        Papers.RationalityTen.RootedCaches.RootedSixBase04.kindMasks Papers.RationalityTen.RootedCaches.RootedSixBase04.keys Papers.RationalityTen.RootedCaches.RootedSixBase04.fastKind quota
        Papers.RationalityTen.FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves rawNodes i = true :=
  SubsumedCounterReplay.check_sound widths cellCount 1024 1152 leafCount nodeCount
    Papers.RationalityTen.RootedCaches.RootedSixBase04.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixBase04.badMasks
    Papers.RationalityTen.RootedCaches.RootedSixBase04.kindMasks Papers.RationalityTen.RootedCaches.RootedSixBase04.keys Papers.RationalityTen.RootedCaches.RootedSixBase04.fastKind quota
    Papers.RationalityTen.FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters i h
def leafTest (i : Nat) : Bool :=
  listBounds cellCount (rawLeaves i) &&
    (WitnessGrowthDAG.closedCheck FacetUniverses.RootedSixBase04.ridgeList
      ((rawLeaves i).map (Fin.ofNat cellCount)) &&
      decide (((rawLeaves i).map (Fin.ofNat cellCount)).Nodup))

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0707

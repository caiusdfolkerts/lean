module
prelude
public import RootedSixBase03GrowthCacheData
public import RootedSixBase03FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification
public import RootedSubsumedForest0700Packed000
public import RootedSubsumedForest0700Packed001

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0700
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 5238
abbrev nodeCount : Nat := 12382
abbrev leafCount : Nat := 14
def widths : PackedRawNatGrowth.Widths := ⟨13,14,7,4⟩
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
(.branch 7
 (.branch 3
 (.branch 1
 (.leaf [0,1,15,195,345,556,768,964,1278,1612,4868])
 (.branch 2
 (.leaf [0,2,42,239,347,412,578,1027,1274,1382])
 (.leaf [0,2,83,239,347,412,586,742,1027,1365])))
 (.branch 5
 (.branch 4
 (.leaf [0,1,61,189,344,556,740,940,1336,1549,5233])
 (.leaf [0,1,61,189,344,650,742,1175,1242,1470,5089]))
 (.branch 6
 (.leaf [0,32,60,164,248,347,735,1009,1117,1292])
 (.leaf [0,1,57,209,544,756,850,985,1290,1607,4978]))))
 (.branch 10
 (.branch 8
 (.leaf [0,6,36,161,568,748,949,976,1274,1613,4988])
 (.branch 9
 (.leaf [0,2,31,196,426,472,615,722,976,1297,1602,4997])
 (.leaf [0,1,77,219,405,542,732,1000,1297,1609,4997])))
 (.branch 12
 (.branch 11
 (.leaf [0,1,197,406,452,544,734,988,1298,1609,4996])
 (.leaf [0,1,195,352,511,554,708,1033,1277,1607,4994]))
 (.branch 13
 (.leaf [0,5,62,132,490,582,700,940,1113,1257,1530,4994])
 (.leaf [0,1,31,219,375,515,732,988,1117,1291,4986])))))
def rawLeaves := leafTable.get

def leaves : Fin leafCount → List (Fin cellCount) := decodedLeaves rawLeaves
def quota : Nat → Nat
  | 0 => 1
  | 1 => 2
  | 2 => 4
  | 3 => 4
  | 4 => 0
  | 5 => 0
  | 6 => 0
  | 7 => 0
  | 8 => 0
  | 9 => 1
  | 10 => 0
  | _ => 0

def nodeTest (i : Nat) : Bool :=
  SubsumedCounterReplay.check widths cellCount 1024 96 leafCount nodeCount
    Papers.RationalityTen.RootedCaches.RootedSixBase03.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixBase03.badMasks
    Papers.RationalityTen.RootedCaches.RootedSixBase03.kindMasks Papers.RationalityTen.RootedCaches.RootedSixBase03.keys Papers.RationalityTen.RootedCaches.RootedSixBase03.fastKind quota
    Papers.RationalityTen.FacetUniverses.RootedSixBase03.Generators.FastWords.rawMaps rawLeaves codes counters i
theorem nodeTest_sound (i : Nat) (h : nodeTest i = true) :
    nodeBounds cellCount 1024 96 leafCount nodeCount (rawNodes i) = true ∧
      SubsumedRawGrowth.nodeCheck Papers.RationalityTen.RootedCaches.RootedSixBase03.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixBase03.badMasks
        Papers.RationalityTen.RootedCaches.RootedSixBase03.kindMasks Papers.RationalityTen.RootedCaches.RootedSixBase03.keys Papers.RationalityTen.RootedCaches.RootedSixBase03.fastKind quota
        Papers.RationalityTen.FacetUniverses.RootedSixBase03.Generators.FastWords.rawMaps rawLeaves rawNodes i = true :=
  SubsumedCounterReplay.check_sound widths cellCount 1024 96 leafCount nodeCount
    Papers.RationalityTen.RootedCaches.RootedSixBase03.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixBase03.badMasks
    Papers.RationalityTen.RootedCaches.RootedSixBase03.kindMasks Papers.RationalityTen.RootedCaches.RootedSixBase03.keys Papers.RationalityTen.RootedCaches.RootedSixBase03.fastKind quota
    Papers.RationalityTen.FacetUniverses.RootedSixBase03.Generators.FastWords.rawMaps rawLeaves codes counters i h
def leafTest (i : Nat) : Bool :=
  listBounds cellCount (rawLeaves i) &&
    (WitnessGrowthDAG.closedCheck FacetUniverses.RootedSixBase03.ridgeList
      ((rawLeaves i).map (Fin.ofNat cellCount)) &&
      decide (((rawLeaves i).map (Fin.ofNat cellCount)).Nodup))

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0700

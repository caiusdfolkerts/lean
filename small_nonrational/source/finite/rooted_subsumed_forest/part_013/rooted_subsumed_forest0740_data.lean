module
prelude
public import RootedSixBase04GrowthCacheData
public import RootedSixBase04FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification
public import RootedSubsumedForest0740Packed000
public import RootedSubsumedForest0740Packed001

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0740
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 2824
abbrev nodeCount : Nat := 10281
abbrev leafCount : Nat := 25
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
(.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf [0,1,5,16,432,547,709,792,960,1239,1513,1848])
 (.branch 2
 (.leaf [0,1,5,16,432,518,792,936,1271,1351,1514,1845])
 (.leaf [0,1,6,121,297,371,516,807,1005,1085,1263,1441,1505])))
 (.branch 4
 (.leaf [0,1,18,71,203,473,542,795,975,1266,1531,1713])
 (.branch 5
 (.leaf [0,1,7,16,278,453,556,804,949,1251,1511,1848])
 (.leaf [0,1,6,15,279,528,651,783,984,1250,1326,1456,1529]))))
 (.branch 9
 (.branch 7
 (.leaf [0,1,6,15,301,566,713,849,908,987,1216,1525])
 (.branch 8
 (.leaf [0,1,15,74,262,296,540,783,973,1238,1327,1457,1530])
 (.leaf [0,1,5,19,395,518,804,936,1263,1450,1502,1849])))
 (.branch 10
 (.leaf [0,1,15,56,250,317,540,795,1160,1271,1330,1515])
 (.branch 11
 (.leaf [0,1,5,128,371,539,795,1006,1065,1236,1513,1818])
 (.leaf [0,1,15,71,203,539,850,909,975,1228,1527,1713])))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf [0,1,5,359,527,780,948,1249,1526,1825,1850])
 (.branch 14
 (.leaf [0,1,9,19,241,398,575,804,940,1264,1450,1491,1715])
 (.leaf [0,1,9,239,383,516,807,998,1185,1260,1505,1824])))
 (.branch 16
 (.leaf [0,8,15,71,131,317,544,818,997,1203,1499,1847])
 (.branch 17
 (.leaf [0,5,16,41,146,495,521,840,950,1251,1476,1845])
 (.leaf [0,1,26,230,386,661,745,807,995,1260,1505]))))
 (.branch 21
 (.branch 19
 (.leaf [0,1,41,206,429,488,554,782,972,1226,1526,1847])
 (.branch 20
 (.leaf [0,2,25,127,207,363,784,948,1225,1536,1595])
 (.leaf [0,5,41,46,134,397,529,994,1044,1249,1493,1823])))
 (.branch 23
 (.branch 22
 (.leaf [0,41,46,123,134,227,398,529,985,1177,1269,1435,1493])
 (.leaf [0,6,41,93,135,374,557,804,937,1263,1512,1847]))
 (.branch 24
 (.leaf [0,2,97,254,410,574,831,995,1260])
 (.leaf [0,4,111,121,267,423,526,844,971,1236,1469]))))))
def rawLeaves := leafTable.get

def leaves : Fin leafCount → List (Fin cellCount) := decodedLeaves rawLeaves
def quota : Nat → Nat
  | 0 => 1
  | 1 => 3
  | 2 => 7
  | 3 => 2
  | 4 => 0
  | 5 => 0
  | 6 => 0
  | 7 => 0
  | 8 => 0
  | 9 => 0
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

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0740

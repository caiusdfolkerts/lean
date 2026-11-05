module
prelude
public import RootedSixBase00GrowthCacheData
public import RootedSixBase00FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification
public import RootedSubsumedForest0310Packed000
public import RootedSubsumedForest0310Packed001

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0310
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 21976
abbrev nodeCount : Nat := 12001
abbrev leafCount : Nat := 18
def widths : PackedRawNatGrowth.Widths := ⟨15,14,7,5⟩
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
 (.leaf [0,2,97,259,415,675,839,1112,1268])
 (.leaf [0,1,61,223,379,627,821,1111,1255,1446,21972]))
 (.branch 3
 (.leaf [0,5,76,155,371,679,800,1086,1452,1509,21669])
 (.leaf [0,1,31,221,401,453,656,1091,1250,1536,1839,21784])))
 (.branch 6
 (.branch 5
 (.leaf [0,1,46,248,289,373,630,1077,1520,1714,21934])
 (.leaf [0,35,61,130,247,403,797,1111,1231,1448,21966]))
 (.branch 7
 (.leaf [0,12,35,130,263,401,805,1029,1091,1207,1531,21920])
 (.branch 8
 (.leaf [0,9,35,145,253,425,609,781,1115,1219,1520,21916])
 (.leaf [0,19,37,144,269,409,609,850,1046,1218,1519,21926])))))
 (.branch 13
 (.branch 11
 (.branch 10
 (.leaf [0,16,35,140,212,792,1101,1221,1528,1716,21820])
 (.leaf [0,19,35,147,265,413,609,793,1103,1207,1532,21918]))
 (.branch 12
 (.leaf [0,32,91,132,257,389,668,1079,1214,1535,1840,21791])
 (.leaf [0,31,35,135,245,377,972,1067,1225,1536,1840,21790])))
 (.branch 15
 (.branch 14
 (.leaf [0,16,35,162,256,468,992,1046,1213,1512,1842,21794])
 (.leaf [0,35,46,147,243,365,601,993,1014,1233,1522,21874]))
 (.branch 16
 (.leaf [0,37,122,170,257,425,598,838,935,1220,1497,21883])
 (.branch 17
 (.leaf [0,15,36,141,213,816,1069,1206,1532,1715,21922])
 (.leaf [0,16,35,140,212,792,1101,1288,1532,1711,21946]))))))
def rawLeaves := leafTable.get

def leaves : Fin leafCount → List (Fin cellCount) := decodedLeaves rawLeaves
def quota : Nat → Nat
  | 0 => 1
  | 1 => 2
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

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0310

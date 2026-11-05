module
prelude
public import RootedSixBase02GrowthCacheData
public import RootedSixBase02FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification
public import RootedSubsumedForest0312Packed000
public import RootedSubsumedForest0312Packed001

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0312
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 8084
abbrev nodeCount : Nat := 6540
abbrev leafCount : Nat := 24
def widths : PackedRawNatGrowth.Widths := ⟨13,13,6,5⟩
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
 (.leaf [0,6,34,153,333,482,529,655,946,1054])
 (.branch 2
 (.leaf [0,18,86,151,213,332,530,667,946,1053])
 (.leaf [0,6,90,153,333,482,528,652,944,1054])))
 (.branch 4
 (.leaf [0,18,91,151,213,332,530,666,951,1030])
 (.branch 5
 (.leaf [0,6,141,332,483,672,961,1053,8052])
 (.leaf [0,1,31,178,332,341,483,672,961,1053,8052]))))
 (.branch 9
 (.branch 7
 (.leaf [0,3,21,188,331,337,684,959,1041,1235,8056])
 (.branch 8
 (.leaf [0,21,27,140,188,331,684,959,1041,1235,8056])
 (.leaf [0,2,42,174,331,534,684,959,1041,1235,8056])))
 (.branch 10
 (.leaf [0,41,53,138,186,332,672,961,1053,1235,8052])
 (.branch 11
 (.leaf [0,6,38,139,331,850,959,1038,8056])
 (.leaf [0,15,37,156,203,330,504,814,882,1002,1335,8055])))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf [0,12,17,157,188,330,506,653,923,1005,1334,8054])
 (.branch 14
 (.leaf [0,17,83,169,188,330,503,651,902,993,1332,8058])
 (.leaf [0,15,27,144,188,330,676,903,1017,1230,1337,8051])))
 (.branch 16
 (.leaf [0,1,31,175,330,609,666,887,993,1333,8059])
 (.branch 17
 (.leaf [0,1,15,177,331,588,642,888,994,1312,8059])
 (.leaf [0,5,37,103,330,609,799,887,990,1333,8059]))))
 (.branch 21
 (.branch 19
 (.leaf [0,5,41,103,330,609,666,887,993,1333,8059])
 (.branch 20
 (.leaf [0,5,21,105,331,588,642,888,994,1312,8059])
 (.leaf [0,1,187,330,589,651,902,993,1232,1332,8058])))
 (.branch 22
 (.leaf [0,6,12,169,333,488,655,1055,8058])
 (.branch 23
 (.leaf [0,1,31,178,332,341,483,609,667,1056,8059])
 (.leaf [0,2,22,176,332,337,609,667,1056,1235,8059]))))))
def rawLeaves := leafTable.get

def leaves : Fin leafCount → List (Fin cellCount) := decodedLeaves rawLeaves
def quota : Nat → Nat
  | 0 => 1
  | 1 => 2
  | 2 => 5
  | 3 => 3
  | 4 => 0
  | 5 => 0
  | 6 => 0
  | 7 => 0
  | 8 => 0
  | 9 => 1
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

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0312

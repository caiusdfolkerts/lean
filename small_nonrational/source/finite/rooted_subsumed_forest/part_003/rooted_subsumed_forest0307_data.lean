module
prelude
public import RootedSixBase02GrowthCacheData
public import RootedSixBase02FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification
public import RootedSubsumedForest0307Packed000
public import RootedSubsumedForest0307Packed001

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0307
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 8084
abbrev nodeCount : Nat := 11452
abbrev leafCount : Nat := 25
def widths : PackedRawNatGrowth.Widths := ⟨13,14,6,5⟩
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
 (.leaf [0,2,60,223,331,529,599,677,1044,1335])
 (.branch 2
 (.leaf [0,7,61,169,333,481,528,610,656,1042])
 (.leaf [0,6,60,141,332,483,528,664,1056,1333])))
 (.branch 4
 (.leaf [0,56,60,138,235,332,528,665,1056,1333])
 (.branch 5
 (.leaf [0,7,62,163,332,530,682,1058])
 (.leaf [0,46,57,102,211,331,527,644,865,994,1239]))))
 (.branch 9
 (.branch 7
 (.leaf [0,55,57,103,187,330,528,682,800,990,1203])
 (.branch 8
 (.leaf [0,6,74,151,331,530,660,854,944,1050])
 (.leaf [0,5,93,127,330,530,642,902,1002,1328,1378])))
 (.branch 10
 (.leaf [0,6,92,151,331,530,685,765,944,1029])
 (.branch 11
 (.leaf [0,6,95,102,331,527,620,882,1018,1136,1242])
 (.leaf [0,6,16,145,330,530,614,667,926,1017,7424])))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf [0,6,16,330,428,530,667,926,1017,1252,7418])
 (.branch 14
 (.leaf [0,56,74,163,210,332,530,670,943,1046])
 (.leaf [0,18,56,151,214,332,530,682,946,1058])))
 (.branch 16
 (.leaf [0,18,74,163,212,331,530,682,950,1058])
 (.branch 17
 (.leaf [0,15,27,188,330,530,678,908,998,1165,1318,7420])
 (.leaf [0,19,69,139,225,333,529,655,954,1135]))))
 (.branch 21
 (.branch 19
 (.leaf [0,2,86,211,331,528,684,850,1040])
 (.branch 20
 (.leaf [0,6,154,333,482,530,660,854,1051])
 (.leaf [0,21,55,106,187,331,528,682,800,991,1203])))
 (.branch 23
 (.branch 22
 (.leaf [0,21,48,107,223,330,527,680,866,1004,1240])
 (.leaf [0,21,53,106,187,331,528,684,850,1040,1235]))
 (.branch 24
 (.leaf [0,21,27,143,188,331,528,684,850,1040,1235])
 (.leaf [0,27,53,106,190,331,483,528,684,850,1040]))))))
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
  | 8 => 1
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

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0307

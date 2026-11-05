module
prelude
public import RootedSmallCacheData
public import RootedSmallGeneratorWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification
public import SmallSubsumedForest11Packed000
public import SmallSubsumedForest11Packed001
public import SmallSubsumedForest11Packed002

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest11
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 3436
abbrev nodeCount : Nat := 17200
abbrev leafCount : Nat := 39
def widths : PackedRawNatGrowth.Widths := ⟨12,15,11,6⟩
def blocks : Table PackedRawNatGrowth.Block :=
(.branch 50
 nodeBlocks000
 (.branch 100
 nodeBlocks001
 nodeBlocks002))
def counterTable : Table Nat :=
(.branch 50
 nodeCounters000
 (.branch 100
 nodeCounters001
 nodeCounters002))
def codes (i : Nat) : Nat :=
  let b := blocks.get (i / 128)
  PackedRawNatGrowth.drop
    (PackedRawNatGrowth.take 32 (PackedRawNatGrowth.drop (32*(i%128)) b.offsets)) b.payload
def counters (i : Nat) : Nat :=
  PackedRawNatGrowth.take 25 (PackedRawNatGrowth.drop (25*(i%128)) (counterTable.get (i/128)))
def rawNodes (i : Nat) := PackedRawNatGrowth.decodeNode widths (codes i)

def leafTable : Table (List Nat) :=
(.branch 19
 (.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf [0,1,370,533,631,795,1562,1650,1847,2067,3041,3388])
 (.leaf [0,1,394,467,631,798,1598,1650,1856,2560,3031,3041]))
 (.branch 3
 (.leaf [0,1,414,536,631,795,1331,1650,1825,3078,3131,3391])
 (.leaf [0,1,379,474,631,795,1650,1856,2567,3031,3044,3311])))
 (.branch 6
 (.branch 5
 (.leaf [0,1,297,736,784,1151,1593,1704,1824,2073,3266,3313])
 (.leaf [0,1,299,736,842,1106,1458,1726,1755,2171,3233,3318]))
 (.branch 7
 (.leaf [0,1,299,722,820,1113,1264,1635,1846,2381,3243,3338])
 (.branch 8
 (.leaf [0,1,336,632,822,1548,1706,1841,2165,2656,3140,3256])
 (.leaf [0,1,339,643,799,1455,1525,1650,1801,2404,3125,3150])))))
 (.branch 14
 (.branch 11
 (.branch 10
 (.leaf [0,1,341,631,807,1346,1638,1859,2065,2517,3042,3387])
 (.leaf [0,1,327,628,856,1014,1553,1669,1841,2165,2406,3203]))
 (.branch 12
 (.leaf [0,1,329,628,822,1411,1523,1723,1851,2072,2573,2778])
 (.branch 13
 (.leaf [0,11,239,341,654,791,1498,1675,1841,2524,2761,3120])
 (.leaf [0,11,191,363,723,834,1502,1668,1810,1921,3145,3187]))))
 (.branch 16
 (.branch 15
 (.leaf [0,41,259,379,639,817,903,1717,1849,3118,3193,3336])
 (.leaf [0,61,190,349,651,791,1346,1716,1814,2003,3095,3162]))
 (.branch 17
 (.leaf [0,151,280,370,626,807,1238,1633,1859,2065,3042,3387])
 (.branch 18
 (.leaf [0,171,250,394,687,801,1521,1739,1859,2972,3211,3361])
 (.leaf [0,41,189,299,709,829,1719,1779,2568,3175,3284,3338]))))))
 (.branch 29
 (.branch 24
 (.branch 21
 (.branch 20
 (.leaf [0,41,214,394,680,831,1526,1739,1859,2761,3216,3386])
 (.leaf [0,294,414,662,818,1645,1801,3059,3084,3237,3387]))
 (.branch 22
 (.leaf [0,41,214,392,697,817,1331,1724,1826,2823,3216,3390])
 (.branch 23
 (.leaf [0,202,356,639,774,1717,1819,2242,3011,3122,3247])
 (.leaf [0,61,284,394,630,762,1232,1681,1856,3031,3042,3280]))))
 (.branch 26
 (.branch 25
 (.leaf [0,41,225,298,742,787,1196,1706,1795,2841,3119,3169])
 (.leaf [0,151,272,406,626,810,1253,1633,1844,3033,3042,3277]))
 (.branch 27
 (.leaf [0,151,189,299,735,811,1104,1718,1759,2843,3147,3272])
 (.branch 28
 (.leaf [0,151,284,370,685,805,1118,1705,1856,3031,3241,3311])
 (.leaf [0,61,181,357,731,800,1176,1658,1769,2493,2971,3120])))))
 (.branch 34
 (.branch 31
 (.branch 30
 (.leaf [0,151,254,406,626,810,1597,1633,1844,2235,3033,3042])
 (.leaf [0,180,309,687,751,1737,1843,2254,2523,2925,3091]))
 (.branch 32
 (.leaf [0,176,372,704,854,1638,1834,2490,2523,2673,3116])
 (.branch 33
 (.leaf [0,61,181,351,643,843,1650,1853,2448,2547,3051,3160])
 (.leaf [0,177,312,734,848,1164,1692,1843,2049,2523,3216]))))
 (.branch 36
 (.branch 35
 (.leaf [0,61,178,351,735,835,1143,1694,1798,3079,3132,3218])
 (.leaf [0,202,411,627,786,1572,1681,1858,3074,3155,3163]))
 (.branch 37
 (.leaf [0,171,188,387,716,806,1662,1818,2423,2525,2694,3095])
 (.branch 38
 (.leaf [0,248,400,734,850,1692,1757,1898,2523,3118,3211])
 (.leaf [0,61,191,303,728,823,1598,1646,1750,2822,3092,3162])))))))
def rawLeaves := leafTable.get

def leaves : Fin leafCount → List (Fin cellCount) := decodedLeaves rawLeaves
def quota : Nat → Nat
  | 0 => 1
  | 1 => 1
  | 2 => 6
  | 3 => 4
  | 4 => 0
  | _ => 0

def nodeTest (i : Nat) : Bool :=
  SubsumedCounterReplay.check widths cellCount 1024 1440 leafCount nodeCount
    RootedSmallCache.candidateMasks RootedSmallCache.badMasks
    RootedSmallCache.kindMasks RootedSmallCache.keys RootedSmallCache.fastKind quota
    RootedSmallGeneratorWords.rawMaps rawLeaves codes counters i
theorem nodeTest_sound (i : Nat) (h : nodeTest i = true) :
    nodeBounds cellCount 1024 1440 leafCount nodeCount (rawNodes i) = true ∧
      SubsumedRawGrowth.nodeCheck RootedSmallCache.candidateMasks RootedSmallCache.badMasks
        RootedSmallCache.kindMasks RootedSmallCache.keys RootedSmallCache.fastKind quota
        RootedSmallGeneratorWords.rawMaps rawLeaves rawNodes i = true :=
  SubsumedCounterReplay.check_sound widths cellCount 1024 1440 leafCount nodeCount
    RootedSmallCache.candidateMasks RootedSmallCache.badMasks
    RootedSmallCache.kindMasks RootedSmallCache.keys RootedSmallCache.fastKind quota
    RootedSmallGeneratorWords.rawMaps rawLeaves codes counters i h
def leafTest (i : Nat) : Bool :=
  listBounds cellCount (rawLeaves i) &&
    (WitnessGrowthDAG.closedCheck FacetUniverses.Small.ridgeList
      ((rawLeaves i).map (Fin.ofNat cellCount)) &&
      decide (((rawLeaves i).map (Fin.ofNat cellCount)).Nodup))

end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest11

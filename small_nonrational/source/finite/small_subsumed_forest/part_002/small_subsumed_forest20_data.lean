module
prelude
public import RootedSmallCacheData
public import RootedSmallGeneratorWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification
public import SmallSubsumedForest20Packed000
public import SmallSubsumedForest20Packed001
public import SmallSubsumedForest20Packed002

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest20
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 3436
abbrev nodeCount : Nat := 17783
abbrev leafCount : Nat := 61
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
(.branch 30
 (.branch 15
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf [0,1,404,462,631,822,1638,1832,2571,3035,3068])
 (.branch 2
 (.leaf [0,1,370,533,631,795,1562,1650,1847,2067,3041,3388])
 (.leaf [0,1,394,467,631,798,1598,1650,1856,2560,3031,3041])))
 (.branch 5
 (.branch 4
 (.leaf [0,1,414,536,631,795,1331,1650,1825,3078,3131,3391])
 (.leaf [0,1,379,474,631,795,1650,1856,2567,3031,3044,3311]))
 (.branch 6
 (.leaf [0,1,297,736,784,1151,1593,1704,1824,2073,3266,3313])
 (.leaf [0,1,299,724,824,1080,1598,1733,1767,2167,2585,3011,3288]))))
 (.branch 11
 (.branch 9
 (.branch 8
 (.leaf [0,1,299,736,842,1106,1458,1726,1755,2171,3233,3318])
 (.leaf [0,1,299,722,820,1113,1264,1635,1846,2381,3243,3338]))
 (.branch 10
 (.leaf [0,1,300,724,854,1080,1442,1668,1803,1984,2493,3238,3405])
 (.leaf [0,1,336,627,842,972,1733,1833,2114,2489,2767,3046,3433])))
 (.branch 13
 (.branch 12
 (.leaf [0,1,336,722,854,1119,1622,1834,1951,2490,2752,3091,3284])
 (.leaf [0,1,300,640,849,1455,1528,1705,1803,2129,2257,3033,3241]))
 (.branch 14
 (.leaf [0,1,336,627,846,942,1594,1713,1853,2114,2279,2769,3093])
 (.leaf [0,1,336,632,822,1548,1706,1841,2165,2656,3140,3256])))))
 (.branch 22
 (.branch 18
 (.branch 16
 (.leaf [0,1,336,687,822,1124,1706,1841,2161,3148,3273])
 (.branch 17
 (.leaf [0,1,336,631,822,1548,1638,1841,2568,3050,3159])
 (.leaf [0,1,339,643,799,1455,1525,1650,1801,2404,3125,3150])))
 (.branch 20
 (.branch 19
 (.leaf [0,1,341,631,807,1346,1638,1859,2065,2517,3042,3387])
 (.leaf [0,1,327,628,856,1014,1553,1669,1841,2165,2406,3203]))
 (.branch 21
 (.leaf [0,1,329,628,822,1411,1523,1723,1851,2072,2573,2778])
 (.leaf [0,11,189,357,632,819,1718,1832,2498,2677,3035,3238,3336]))))
 (.branch 26
 (.branch 24
 (.branch 23
 (.leaf [0,11,239,341,654,791,1498,1675,1841,2524,2761,3120])
 (.leaf [0,11,191,363,723,834,1502,1668,1810,1921,3145,3187]))
 (.branch 25
 (.leaf [0,41,193,401,687,851,874,1734,1745,1952,2099,2458,3003])
 (.leaf [0,41,259,379,639,817,903,1717,1849,3118,3193,3336])))
 (.branch 28
 (.branch 27
 (.leaf [0,151,176,359,745,865,1203,1658,1800,1877,2913,3241,3392])
 (.leaf [0,284,334,635,759,1138,1681,1847,2067,3042,3262,3312]))
 (.branch 29
 (.leaf [0,61,190,349,651,791,1346,1716,1814,2003,3095,3162])
 (.leaf [0,41,193,346,697,817,1524,1646,1848,1961,2934,3214,3393]))))))
 (.branch 45
 (.branch 37
 (.branch 33
 (.branch 31
 (.leaf [0,151,280,370,626,807,1238,1633,1859,2065,3042,3387])
 (.branch 32
 (.leaf [0,61,178,347,731,831,1176,1695,1857,2464,3111,3213,3286])
 (.leaf [0,171,250,394,687,801,1521,1739,1859,2972,3211,3361])))
 (.branch 35
 (.branch 34
 (.leaf [0,41,189,299,709,829,1719,1779,2568,3175,3284,3338])
 (.leaf [0,41,214,394,680,831,1526,1739,1859,2761,3216,3386]))
 (.branch 36
 (.leaf [0,294,414,662,818,1645,1801,3059,3084,3237,3387])
 (.leaf [0,41,214,392,697,817,1331,1724,1826,2823,3216,3390]))))
 (.branch 41
 (.branch 39
 (.branch 38
 (.leaf [0,41,225,298,742,784,1196,1706,1846,2444,3136,3166,3338])
 (.leaf [0,212,370,683,807,1243,1634,1774,2406,3040,3238,3387]))
 (.branch 40
 (.leaf [0,212,370,683,807,1243,1634,1784,2949,3040,3238,3387])
 (.leaf [0,202,356,639,774,1717,1819,2242,3011,3122,3247])))
 (.branch 43
 (.branch 42
 (.leaf [0,61,284,394,630,762,1232,1681,1856,3031,3042,3280])
 (.leaf [0,41,225,298,742,787,1196,1706,1795,2841,3119,3169]))
 (.branch 44
 (.leaf [0,151,272,406,626,810,1253,1633,1844,3033,3042,3277])
 (.leaf [0,151,189,299,735,811,1104,1718,1759,2843,3147,3272])))))
 (.branch 53
 (.branch 49
 (.branch 47
 (.branch 46
 (.leaf [0,151,284,370,685,805,1118,1705,1856,3031,3241,3311])
 (.leaf [0,61,181,357,731,800,1176,1658,1769,2493,2971,3120]))
 (.branch 48
 (.leaf [0,151,254,406,626,810,1597,1633,1844,2235,3033,3042])
 (.leaf [0,180,309,687,751,1737,1843,2254,2523,2925,3091])))
 (.branch 51
 (.branch 50
 (.leaf [0,176,372,704,854,1638,1834,2490,2523,2673,3116])
 (.leaf [0,61,180,312,679,843,1686,1858,2486,2497,3142]))
 (.branch 52
 (.leaf [0,61,181,351,643,843,1650,1853,2448,2547,3051,3160])
 (.leaf [0,177,312,734,848,1164,1692,1843,2049,2523,3216]))))
 (.branch 57
 (.branch 55
 (.branch 54
 (.leaf [0,41,214,410,675,810,1551,1717,1857,3143,3191])
 (.leaf [0,61,178,351,735,835,1143,1694,1798,3079,3132,3218]))
 (.branch 56
 (.leaf [0,202,411,627,786,1572,1681,1858,3074,3155,3163])
 (.leaf [0,171,188,387,716,806,1662,1818,2423,2525,2694,3095])))
 (.branch 59
 (.branch 58
 (.leaf [0,151,176,377,675,827,1722,1769,1910,2139,2481,3026,3044])
 (.leaf [0,248,400,734,850,1692,1757,1898,2523,3118,3211]))
 (.branch 60
 (.leaf [0,61,191,303,728,823,1598,1646,1750,2822,3092,3162])
 (.leaf [0,61,180,341,679,791,931,1698,1830,1974,2439,2499,2984])))))))
def rawLeaves := leafTable.get

def leaves : Fin leafCount → List (Fin cellCount) := decodedLeaves rawLeaves
def quota : Nat → Nat
  | 0 => 1
  | 1 => 1
  | 2 => 7
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

end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest20

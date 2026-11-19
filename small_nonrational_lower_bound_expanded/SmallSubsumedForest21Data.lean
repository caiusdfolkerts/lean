module
prelude
public meta import LowerSchemas.FiniteSmallSubsumedForest
public import RootedSmallCacheData
public import RootedSmallGeneratorWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification
public import SmallSubsumedForest21Packed000
public import SmallSubsumedForest21Packed001
public import SmallSubsumedForest21Packed002

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest21
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 3436
abbrev nodeCount : Nat := 18154
abbrev leafCount : Nat := 25
cert_widths_4 15 5
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
cert_codes_4
cert_counters_4
cert_rawNodes_4
def leafTable : Table (List Nat) :=
(.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf [0,1,358,534,639,750,1563,1725,1855,2170,3009,3068])
 (.branch 2
 (.leaf [0,1,414,536,639,828,923,1713,1801,2149,3043,3336])
 (.leaf [0,1,297,718,772,1154,1717,1857,2122,2464,3136,3205,3288])))
 (.branch 4
 (.leaf [0,1,324,649,806,949,1717,1821,2185,2466,3140,3252])
 (.branch 5
 (.leaf [0,1,324,718,806,1154,1663,1821,2466,2567,2717,3140])
 (.leaf [0,1,336,637,861,907,1572,1681,1856,2170,2277,3168]))))
 (.branch 9
 (.branch 7
 (.leaf [0,1,327,705,810,1190,1597,1634,1774,2781,3040,3252])
 (.branch 8
 (.leaf [0,1,339,674,846,1196,1280,1622,1786,3099,3152,3166])
 (.leaf [0,1,339,628,864,1049,1523,1681,1827,2143,2383,3177,3386])))
 (.branch 10
 (.leaf [0,61,255,301,734,764,1024,1709,1759,2257,2497,3157])
 (.branch 11
 (.leaf [0,41,189,299,697,817,1706,1788,1963,3018,3200,3281,3341])
 (.leaf [0,61,178,403,579,651,765,1699,1849,2801,2909,3163,3386])))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf [0,171,210,369,454,710,812,1727,1847,2117,2969,3245,3311])
 (.branch 14
 (.leaf [0,41,238,322,673,793,1498,1740,1860,3199,3280,3362])
 (.leaf [0,151,284,368,732,852,1680,1800,2106,2565,3243,3311])))
 (.branch 16
 (.leaf [0,41,293,358,639,750,1260,1717,1855,3009,3072,3197])
 (.branch 17
 (.leaf [0,61,201,300,673,800,968,1740,1795,2066,2499,3237])
 (.leaf [0,41,281,313,687,752,1176,1739,1747,2044,2523,3216]))))
 (.branch 21
 (.branch 19
 (.leaf [0,151,224,399,728,782,1687,1770,2381,2500,2652,2715])
 (.branch 20
 (.leaf [0,41,189,303,709,829,1711,1853,2343,2571,2824,3193])
 (.leaf [0,41,189,341,697,817,1346,1723,1849,2517,2822,3167,3387])))
 (.branch 23
 (.branch 22
 (.leaf [0,151,177,341,639,791,1713,1853,2212,2546,3076,3157])
 (.leaf [0,228,360,728,860,1607,1723,1855,2602]))
 (.branch 24
 (.leaf [0,11,207,377,690,827,1498,1654,1781,2518,3126,3151])
 (.leaf [0,171,216,329,705,798,1367,1530,1700,1835,2002,2550]))))))
def rawLeaves := leafTable.get

cert_leaves_4
cert_quota_5 1 6 5
cert_nodeTest_6
cert_nodeTest_sound_5
cert_leafTest_6
end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest21

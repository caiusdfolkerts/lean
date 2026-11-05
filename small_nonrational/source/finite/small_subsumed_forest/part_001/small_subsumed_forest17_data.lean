module
prelude
public import RootedSmallCacheData
public import RootedSmallGeneratorWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification
public import SmallSubsumedForest17Packed000
public import SmallSubsumedForest17Packed001
public import SmallSubsumedForest17Packed002

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest17
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 3436
abbrev nodeCount : Nat := 16019
abbrev leafCount : Nat := 87
def widths : PackedRawNatGrowth.Widths := ⟨12,14,11,7⟩
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
(.branch 43
 (.branch 21
 (.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf [0,1,7,422,652,858,1437,1577,1734,1815,2138,2596])
 (.leaf [0,1,11,357,667,842,1331,1650,1825,2544,3115,3390]))
 (.branch 3
 (.leaf [0,1,11,345,655,855,1310,1662,1839,2521,3087,3393])
 (.branch 4
 (.leaf [0,1,11,357,667,820,1523,1650,1850,2493,3112,3387])
 (.leaf [0,1,11,345,655,808,1549,1662,1839,2521,2934,3393]))))
 (.branch 7
 (.branch 6
 (.leaf [0,2,26,334,567,654,1206,1575,1682,1817,2935,3137])
 (.leaf [0,3,62,322,545,727,784,1526,1710,1850,3136,3337]))
 (.branch 8
 (.leaf [0,2,52,381,419,630,783,1698,1851,2596,3063,3366])
 (.branch 9
 (.leaf [0,1,171,393,420,631,797,1650,1852,2572,2850,3392])
 (.leaf [0,1,161,368,525,655,857,1638,1791,2525,2897,3343])))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf [0,3,131,368,503,642,785,1710,1806,2600,3042,3313])
 (.leaf [0,6,22,238,527,798,1376,1602,1734,1779,2746,3019]))
 (.branch 13
 (.leaf [0,3,62,298,548,727,784,1575,1710,1803,3018,3344])
 (.branch 14
 (.leaf [0,1,11,372,643,846,1528,1650,1853,2548,3118])
 (.leaf [0,2,52,337,588,691,835,1576,1674,1755,2520,3139]))))
 (.branch 18
 (.branch 16
 (.leaf [0,3,142,409,500,678,810,1603,1637,1769,2542,3064])
 (.branch 17
 (.leaf [0,1,41,321,700,842,1332,1647,1825,2808,3218,3365])
 (.leaf [0,1,41,309,688,855,1311,1729,1839,2159,3219,3368])))
 (.branch 19
 (.leaf [0,1,41,309,687,748,1729,1839,2159,2998,3216,3318])
 (.branch 20
 (.leaf [0,6,22,179,795,1309,1659,1837,2387,2767,3213,3393])
 (.leaf [0,2,144,345,650,808,1246,1633,1826,2220,3242,3389]))))))
 (.branch 32
 (.branch 26
 (.branch 23
 (.branch 22
 (.leaf [0,2,154,369,638,796,1204,1645,1852,2244,2892,3394])
 (.leaf [0,2,26,345,654,1246,1313,1729,1839,2222,2938,3393]))
 (.branch 24
 (.leaf [0,3,162,393,677,807,1286,1681,1852,2265,3161,3367])
 (.branch 25
 (.leaf [0,1,61,299,739,820,1143,1601,1646,1778,3112,3313])
 (.leaf [0,1,171,309,651,783,1734,1839,2138,2591,3087,3312]))))
 (.branch 29
 (.branch 27
 (.leaf [0,3,51,346,739,784,1205,1551,1706,1838,3136,3316])
 (.branch 28
 (.leaf [0,1,141,321,627,759,1693,1851,2180,2976,3188,3368])
 (.leaf [0,1,141,321,663,747,1721,1789,2180,2475,3113,3294])))
 (.branch 30
 (.leaf [0,1,171,297,639,783,1710,1850,2075,2411,3119,3344])
 (.branch 31
 (.leaf [0,3,31,383,666,809,1269,1551,1718,1789,3066,3389])
 (.leaf [0,3,51,310,738,811,1163,1551,1718,1789,3143,3314])))))
 (.branch 37
 (.branch 34
 (.branch 33
 (.leaf [0,3,162,393,711,758,1685,1741,2265,2456,3043,3367])
 (.leaf [0,1,161,297,655,855,1350,1662,1815,2518,3112,3391]))
 (.branch 35
 (.leaf [0,2,52,348,738,772,1227,1577,1695,1854,2344,2596])
 (.branch 36
 (.leaf [0,3,51,313,678,819,1499,1722,1779,2568,3138,3338])
 (.leaf [0,6,157,204,689,795,1313,1669,1840,2265,2393,3392]))))
 (.branch 40
 (.branch 38
 (.leaf [0,1,55,300,738,835,1122,1601,1659,1791,2051,2521])
 (.branch 39
 (.leaf [0,3,131,396,642,785,1522,1710,1806,2323,2600,3042])
 (.leaf [0,2,64,372,688,835,1373,1550,1709,1840,2244,2566])))
 (.branch 41
 (.leaf [0,3,62,396,642,774,1457,1527,1710,1852,2591,3037])
 (.branch 42
 (.leaf [0,1,67,336,676,834,1124,1457,1705,1852,2182,3269])
 (.leaf [0,2,64,372,654,762,1249,1479,1683,1840,1924,2595])))))))
 (.branch 65
 (.branch 54
 (.branch 48
 (.branch 45
 (.branch 44
 (.leaf [0,1,147,324,664,810,1014,1550,1721,1829,2180,2591])
 (.leaf [0,2,122,360,662,859,1248,1671,1829,2594,3116,3190]))
 (.branch 46
 (.leaf [0,1,41,324,675,810,1549,1717,1854,2180,3143,3191])
 (.branch 47
 (.leaf [0,2,144,360,722,859,1248,1637,1769,2220,2495,3136])
 (.leaf [0,1,171,324,675,810,1102,1722,1854,2072,2572,3142]))))
 (.branch 51
 (.branch 49
 (.leaf [0,1,67,336,678,822,1145,1550,1705,1853,2181,3144])
 (.branch 50
 (.leaf [0,1,41,324,700,859,1553,1635,1829,2569,2809,3193])
 (.leaf [0,1,41,324,700,859,1553,1718,1829,2139,3111,3193])))
 (.branch 52
 (.leaf [0,1,125,336,628,822,1523,1710,1853,2072,2571,3141])
 (.branch 53
 (.leaf [0,2,144,360,700,859,1597,1637,1769,2220,2495,2809])
 (.leaf [0,1,171,324,664,859,1547,1718,1829,2139,3136,3187])))))
 (.branch 59
 (.branch 56
 (.branch 55
 (.leaf [0,1,41,336,687,822,1523,1647,1853,2567,3137,3163])
 (.leaf [0,3,62,396,654,786,1205,1526,1707,1853,2591,3087]))
 (.branch 57
 (.leaf [0,68,83,252,347,726,831,1661,1803,2545,3115,3389])
 (.branch 58
 (.leaf [0,45,103,273,308,687,797,1732,1801,2572,3267,3290])
 (.leaf [0,41,102,189,299,687,819,1706,1838,3145,3167,3317]))))
 (.branch 62
 (.branch 60
 (.leaf [0,42,112,201,297,723,760,1730,1803,3020,3242,3293])
 (.branch 61
 (.leaf [0,51,92,181,369,639,771,1722,1849,2523,3118,3343])
 (.leaf [0,63,114,272,370,665,749,1636,1768,2473,3238,3343])))
 (.branch 63
 (.leaf [0,41,61,213,311,687,797,1729,1779,2998,3216,3320])
 (.branch 64
 (.leaf [0,151,152,189,323,652,855,1672,1814,2286,2789,3342])
 (.leaf [0,188,383,712,806,1659,1813,2368,2787,3241,3390]))))))
 (.branch 76
 (.branch 70
 (.branch 67
 (.branch 66
 (.leaf [0,64,153,193,383,698,856,1185,1622,1756,2872,3369])
 (.leaf [0,62,92,205,358,639,749,1722,1851,2573,2914,3344]))
 (.branch 68
 (.leaf [0,47,64,276,310,691,772,1600,1693,1839,2997,3367])
 (.branch 69
 (.leaf [0,41,64,193,383,703,856,1553,1622,1756,2872,3369])
 (.leaf [0,42,101,277,368,655,857,1578,1636,1766,2523,3343]))))
 (.branch 73
 (.branch 71
 (.leaf [0,42,106,277,409,655,806,1577,1633,1794,2597,3040])
 (.branch 72
 (.leaf [0,61,171,180,311,679,843,1686,1850,2306,3142,3367])
 (.leaf [0,64,113,204,297,714,760,1734,1815,2567,3019,3318])))
 (.branch 74
 (.leaf [0,63,154,251,301,722,787,1705,1770,2100,3120,3193])
 (.branch 75
 (.leaf [0,41,61,213,312,687,798,1729,1842,2517,3143,3216])
 (.leaf [0,151,152,200,408,675,822,1249,1634,1781,2542,3070])))))
 (.branch 81
 (.branch 78
 (.branch 77
 (.leaf [0,61,62,204,311,690,797,1734,1779,2542,2998,3320])
 (.leaf [0,228,357,727,782,1437,1710,1765,2594,3115,3340]))
 (.branch 79
 (.leaf [0,62,92,179,324,675,810,1722,1854,2572,3142,3164])
 (.branch 80
 (.leaf [0,64,91,191,324,723,834,1695,1854,2548,3111,3193])
 (.leaf [0,44,67,252,360,643,834,1525,1657,1854,2592,3116]))))
 (.branch 84
 (.branch 82
 (.leaf [0,61,171,192,299,678,819,1722,1779,2568,3138,3338])
 (.branch 83
 (.leaf [0,151,171,176,372,676,846,1598,1634,1781,2543,3113])
 (.leaf [0,252,345,738,808,1546,1721,1826,2516,3111,3286])))
 (.branch 85
 (.leaf [0,62,115,204,336,690,822,1523,1709,1841,2492,3145])
 (.branch 86
 (.leaf [0,61,62,193,349,655,811,1662,1818,2525,3095])
 (.leaf [0,204,336,690,822,1550,1709,1841,2570,3140]))))))))
def rawLeaves := leafTable.get

def leaves : Fin leafCount → List (Fin cellCount) := decodedLeaves rawLeaves
def quota : Nat → Nat
  | 0 => 1
  | 1 => 2
  | 2 => 10
  | 3 => 0
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

end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest17

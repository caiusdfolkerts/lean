module
prelude
public import RootedSmallCacheData
public import RootedSmallGeneratorWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification
public import SmallSubsumedForest10Packed000
public import SmallSubsumedForest10Packed001

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest10
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 3436
abbrev nodeCount : Nat := 10529
abbrev leafCount : Nat := 32
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
  PackedRawNatGrowth.take 25 (PackedRawNatGrowth.drop (25*(i%128)) (counterTable.get (i/128)))
def rawNodes (i : Nat) := PackedRawNatGrowth.decodeNode widths (codes i)

def leafTable : Table (List Nat) :=
(.branch 16
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf [0,1,404,462,631,822,1638,1832,2571,3035,3068])
 (.leaf [0,1,309,734,784,1119,1707,1858,2072,2486,3266,3312]))
 (.branch 3
 (.leaf [0,1,299,734,820,1122,1709,1755,2189,2583,3019,3318])
 (.leaf [0,1,299,722,820,1122,1635,1860,2066,2348,3238,3343])))
 (.branch 6
 (.branch 5
 (.leaf [0,1,297,639,783,1710,1850,2075,2411,3076,3157,3341])
 (.leaf [0,1,309,627,771,1698,1843,2076,2593,3032,3092,3287]))
 (.branch 7
 (.leaf [0,1,300,664,796,1056,1526,1733,1825,2117,2459,3403])
 (.leaf [0,1,300,726,796,1122,1598,1659,1855,2408,2546,3030]))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf [0,1,300,723,799,1080,1668,1806,1984,2493,3142,3238])
 (.leaf [0,1,336,687,822,1124,1706,1841,2161,3148,3273]))
 (.branch 11
 (.leaf [0,1,300,711,799,1080,1734,1818,2135,2548,3079,3132])
 (.leaf [0,1,336,628,822,1523,1707,1853,2072,2571,2794,3278])))
 (.branch 14
 (.branch 13
 (.leaf [0,1,336,628,822,1548,1669,1841,2191,2275,3138,3166])
 (.leaf [0,1,336,631,822,1548,1638,1841,2568,3050,3159]))
 (.branch 15
 (.leaf [0,11,227,321,724,784,1526,1740,1860,2095,3268,3337])
 (.leaf [0,41,237,298,639,783,1705,1824,2047,3119,3168,3338])))))
 (.branch 24
 (.branch 20
 (.branch 18
 (.branch 17
 (.leaf [0,41,241,382,643,843,1502,1621,1860,2045,3067,3386])
 (.leaf [0,41,201,333,675,752,1705,1853,2542,2887,3144,3166]))
 (.branch 19
 (.leaf [0,61,190,346,734,820,1122,1707,1858,2486,3241,3311])
 (.leaf [0,41,205,358,709,829,1498,1659,1851,2567,3188,3387])))
 (.branch 22
 (.branch 21
 (.leaf [0,151,190,381,664,844,1522,1740,1860,2197,3216,3386])
 (.leaf [0,41,225,298,743,772,1197,1719,1849,2432,3191,3343]))
 (.branch 23
 (.leaf [0,151,284,394,626,798,1230,1645,1856,3031,3044,3242])
 (.leaf [0,41,249,359,643,834,1503,1657,1819,3011,3119,3213]))))
 (.branch 28
 (.branch 26
 (.branch 25
 (.leaf [0,171,260,322,699,751,1100,1718,1832,2905,3067,3270])
 (.leaf [0,41,229,393,655,836,1501,1621,1817,2593,3034,3092]))
 (.branch 27
 (.leaf [0,61,228,298,642,783,1710,1850,2411,3076,3157,3341])
 (.leaf [0,61,229,310,630,771,1698,1843,2593,3032,3092,3287])))
 (.branch 30
 (.branch 29
 (.leaf [0,61,229,381,630,853,966,1686,1850,2491,3094,3361])
 (.leaf [0,61,180,312,679,843,1686,1858,2486,2497,3142]))
 (.branch 31
 (.leaf [0,61,229,395,630,786,1573,1686,1831,2491,3034,3094])
 (.leaf [0,41,214,410,675,810,1551,1717,1857,3143,3191]))))))
def rawLeaves := leafTable.get

def leaves : Fin leafCount → List (Fin cellCount) := decodedLeaves rawLeaves
def quota : Nat → Nat
  | 0 => 1
  | 1 => 1
  | 2 => 8
  | 3 => 2
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

end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest10

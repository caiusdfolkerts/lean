module
prelude
public import RootedSixBase04GrowthCacheData
public import RootedSixBase04FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification
public import RootedSubsumedForest0741Packed000
public import RootedSubsumedForest0741Packed001
public import RootedSubsumedForest0741Packed002

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0741
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 2824
abbrev nodeCount : Nat := 13485
abbrev leafCount : Nat := 47
def widths : PackedRawNatGrowth.Widths := ⟨12,14,11,6⟩
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
  PackedRawNatGrowth.take 55 (PackedRawNatGrowth.drop (55*(i%128)) (counterTable.get (i/128)))
def rawNodes (i : Nat) := PackedRawNatGrowth.decodeNode widths (codes i)

def leafTable : Table (List Nat) :=
(.branch 23
 (.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf [0,1,6,15,276,571,707,850,909,975,1228,1527,1705])
 (.leaf [0,1,5,16,432,518,795,997,1040,1194,1271,1351,1517]))
 (.branch 3
 (.leaf [0,1,6,15,276,520,850,909,974,1227,1475,1847])
 (.branch 4
 (.leaf [0,3,5,16,278,495,518,797,960,1255,1417,1520,1707])
 (.leaf [0,1,6,41,297,373,553,810,990,1233,1522,1823]))))
 (.branch 8
 (.branch 6
 (.leaf [0,1,16,57,215,453,518,812,1151,1270,1350,1505,1708])
 (.branch 7
 (.leaf [0,1,6,297,371,516,800,990,1153,1261,1522,1821])
 (.leaf [0,3,5,76,318,376,515,823,963,1173,1289,1516,1707])))
 (.branch 9
 (.leaf [0,3,5,76,318,376,515,837,931,963,1289,1516,1707])
 (.branch 10
 (.leaf [0,3,5,76,318,376,515,846,963,1289,1435,1516,1707])
 (.leaf [0,1,6,93,276,365,563,795,975,1266,1313,1531,1705])))))
 (.branch 17
 (.branch 14
 (.branch 12
 (.leaf [0,1,6,41,297,377,557,806,986,1223,1512,1848])
 (.branch 13
 (.leaf [0,1,6,15,301,540,650,810,980,1174,1233,1527])
 (.leaf [0,1,26,47,206,362,858,1006,1086,1271,1351,1517])))
 (.branch 15
 (.leaf [0,2,5,77,301,403,542,753,824,963,1174,1525])
 (.branch 16
 (.leaf [0,2,5,77,301,403,542,753,834,963,1437,1525])
 (.leaf [0,3,5,76,322,402,542,752,837,931,963,1513]))))
 (.branch 20
 (.branch 18
 (.leaf [0,1,5,128,397,464,530,774,807,1005,1064,1251,1501])
 (.branch 19
 (.leaf [0,1,15,56,246,322,540,668,810,1158,1233,1515])
 (.leaf [0,1,15,68,227,527,798,988,1187,1221,1503,1717])))
 (.branch 21
 (.leaf [0,1,15,71,215,515,786,1004,1170,1209,1516,1711])
 (.branch 22
 (.leaf [0,1,9,97,254,362,582,748,783,1003,1169,1237])
 (.leaf [0,6,9,15,143,520,842,986,1186,1215,1475,1850]))))))
 (.branch 35
 (.branch 29
 (.branch 26
 (.branch 24
 (.leaf [0,2,25,71,207,384,505,767,819,1006,1065,1262,1493])
 (.branch 25
 (.leaf [0,1,41,58,235,362,552,646,783,1166,1188,1237,1528])
 (.leaf [0,1,41,58,261,311,374,553,849,908,1236,1516,1839])))
 (.branch 27
 (.leaf [0,1,42,97,206,428,487,569,782,972,1214,1618,1842])
 (.branch 28
 (.leaf [0,5,41,48,201,332,396,517,966,1264,1498,1822])
 (.leaf [0,2,25,127,207,363,784,948,1225,1536,1595]))))
 (.branch 32
 (.branch 30
 (.leaf [0,1,27,126,218,429,488,782,976,1178,1226,1524,1618])
 (.branch 31
 (.leaf [0,1,26,249,290,391,709,804,949,1248,1504,1848])
 (.leaf [0,8,15,125,198,487,570,706,817,988,1175,1215,1465])))
 (.branch 33
 (.leaf [0,1,41,58,209,374,553,849,908,1048,1236,1516,1839])
 (.branch 34
 (.leaf [0,5,41,76,146,399,547,709,846,963,1176,1435,1513])
 (.leaf [0,16,41,55,168,219,573,623,793,1271,1351,1491,1840])))))
 (.branch 41
 (.branch 38
 (.branch 36
 (.leaf [0,1,41,58,235,362,552,646,837,887,1237,1528,1839])
 (.branch 37
 (.leaf [0,1,41,56,206,374,585,665,812,1130,1264,1441,1515])
 (.leaf [0,5,41,48,149,396,517,913,966,1264,1498,1822])))
 (.branch 39
 (.leaf [0,1,26,244,321,389,737,794,981,1235,1514,1843])
 (.branch 40
 (.leaf [0,9,15,47,143,251,519,1000,1186,1219,1484,1716])
 (.leaf [0,5,41,46,134,429,509,529,942,1253,1474,1820]))))
 (.branch 44
 (.branch 42
 (.leaf [0,2,36,254,401,543,766,830,959,1247,1478,1851])
 (.branch 43
 (.leaf [0,1,42,125,230,365,582,748,794,1000,1176,1211,1501])
 (.leaf [0,1,41,128,218,391,556,709,807,998,1176,1248,1511])))
 (.branch 45
 (.leaf [0,1,41,72,206,373,553,810,990,1233,1522,1823])
 (.branch 46
 (.leaf [0,1,41,206,377,571,751,782,984,1223,1525,1845])
 (.leaf [0,5,41,48,163,396,490,517,966,1264,1498,1822])))))))
def rawLeaves := leafTable.get

def leaves : Fin leafCount → List (Fin cellCount) := decodedLeaves rawLeaves
def quota : Nat → Nat
  | 0 => 1
  | 1 => 3
  | 2 => 5
  | 3 => 4
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

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0741

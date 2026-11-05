module
prelude
public import RootedSixBase00GrowthCacheData
public import RootedSixBase00FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification
public import RootedSubsumedForest0298Packed000
public import RootedSubsumedForest0298Packed001
public import RootedSubsumedForest0298Packed002
public import RootedSubsumedForest0298Packed003

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0298
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 21976
abbrev nodeCount : Nat := 19423
abbrev leafCount : Nat := 43
def widths : PackedRawNatGrowth.Widths := ⟨15,15,7,6⟩
def blocks : Table PackedRawNatGrowth.Block :=
(.branch 100
 (.branch 50
 nodeBlocks000
 nodeBlocks001)
 (.branch 150
 nodeBlocks002
 nodeBlocks003))
def counterTable : Table Nat :=
(.branch 100
 (.branch 50
 nodeCounters000
 nodeCounters001)
 (.branch 150
 nodeCounters002
 nodeCounters003))
def codes (i : Nat) : Nat :=
  let b := blocks.get (i / 128)
  PackedRawNatGrowth.drop
    (PackedRawNatGrowth.take 32 (PackedRawNatGrowth.drop (32*(i%128)) b.offsets)) b.payload
def counters (i : Nat) : Nat :=
  PackedRawNatGrowth.take 55 (PackedRawNatGrowth.drop (55*(i%128)) (counterTable.get (i/128)))
def rawNodes (i : Nat) := PackedRawNatGrowth.decodeNode widths (codes i)

def leafTable : Table (List Nat) :=
(.branch 21
 (.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf [0,1,76,235,391,651,839,1347,1509,16876])
 (.leaf [0,1,124,391,627,838,1110,1240,1445,1533,14081]))
 (.branch 3
 (.leaf [0,19,75,171,265,389,608,623,817,1079,1532,17013])
 (.branch 4
 (.leaf [0,19,75,171,265,389,603,623,821,1079,1767,17660])
 (.leaf [0,2,97,259,415,675,839,1112,1268]))))
 (.branch 7
 (.branch 6
 (.leaf [0,1,124,223,379,639,815,1269,1522,16819])
 (.leaf [0,1,46,203,371,627,1108,1255,1451,1520,1716]))
 (.branch 8
 (.leaf [0,5,36,188,310,384,783,1112,1508,1710,17356])
 (.branch 9
 (.leaf [0,2,95,273,353,397,678,803,1052,1710,17230])
 (.leaf [0,5,94,151,381,659,795,1111,1255,17635])))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf [0,1,66,235,391,651,839,1191,1507,17404])
 (.leaf [0,1,91,379,650,849,1086,1204,1509,1822,14152]))
 (.branch 13
 (.leaf [0,9,75,145,257,421,609,626,838,1058,1531,17011])
 (.branch 14
 (.leaf [0,6,75,145,308,396,618,650,834,1058,1787,17659])
 (.leaf [0,1,121,310,389,626,826,1079,1213,1528,1840,14234]))))
 (.branch 18
 (.branch 16
 (.leaf [0,1,15,203,626,816,1077,1233,1529,1715,1824])
 (.branch 17
 (.leaf [0,16,75,150,243,447,650,834,1028,1050,17518])
 (.leaf [0,1,5,371,624,792,1111,1252,1451,1534,1825])))
 (.branch 19
 (.leaf [0,15,76,143,227,664,833,1031,1077,1523,16250])
 (.branch 20
 (.leaf [0,2,15,237,313,432,660,833,1069,1214,1854,17678])
 (.leaf [0,1,6,279,400,474,648,785,1090,1262,1860,17532]))))))
 (.branch 32
 (.branch 26
 (.branch 23
 (.branch 22
 (.leaf [0,1,16,209,432,636,790,1269,1522,1820,16829])
 (.leaf [0,5,36,131,371,800,953,1111,1255,1446,17635]))
 (.branch 24
 (.leaf [0,6,35,130,395,824,1111,1228,1450,1534,14920])
 (.branch 25
 (.leaf [0,1,16,205,432,644,800,1101,1532,1711,17359])
 (.leaf [0,2,15,237,313,432,668,1069,1214,1535,1840,16065]))))
 (.branch 29
 (.branch 27
 (.leaf [0,1,6,279,400,474,656,1090,1262,1524,1839,15919])
 (.branch 28
 (.leaf [0,1,16,240,318,435,654,846,1046,1235,1852,17691])
 (.leaf [0,1,16,244,318,435,654,1046,1235,1524,1841,16076])))
 (.branch 30
 (.leaf [0,6,35,154,338,412,822,982,1213,1512,1859,16729])
 (.branch 31
 (.leaf [0,6,35,162,338,822,982,1055,1213,1512,1842,14634])
 (.leaf [0,1,31,241,297,374,654,834,1080,1524,1857,17330])))))
 (.branch 37
 (.branch 34
 (.branch 33
 (.leaf [0,4,61,239,295,412,653,793,1102,1503,1857,17318])
 (.leaf [0,35,46,142,246,402,940,1099,1231,1449,17491]))
 (.branch 35
 (.leaf [0,36,45,166,236,333,425,940,1200,1492,1852,16875])
 (.branch 36
 (.leaf [0,36,45,134,229,413,600,937,1245,1496,1790,16838])
 (.leaf [0,15,36,176,228,356,477,833,1059,1239,1859,17545]))))
 (.branch 40
 (.branch 38
 (.leaf [0,15,36,176,232,356,477,1059,1239,1476,1842,15930])
 (.branch 39
 (.leaf [0,15,36,174,216,445,820,1077,1520,1714,17215])
 (.leaf [0,15,36,174,216,820,1072,1255,1520,1717,12858])))
 (.branch 41
 (.leaf [0,15,65,194,216,463,617,671,846,1202,1636,17662])
 (.branch 42
 (.leaf [0,15,36,188,216,354,476,817,1071,1255,1483,17113])
 (.leaf [0,15,36,225,774,820,1072,1255,1520,1709,13390])))))))
def rawLeaves := leafTable.get

def leaves : Fin leafCount → List (Fin cellCount) := decodedLeaves rawLeaves
def quota : Nat → Nat
  | 0 => 1
  | 1 => 2
  | 2 => 4
  | 3 => 4
  | 4 => 0
  | 5 => 0
  | 6 => 1
  | 7 => 0
  | 8 => 0
  | 9 => 0
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

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0298

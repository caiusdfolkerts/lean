module
prelude
public import RootedSixBase00GrowthCacheData
public import RootedSixBase00FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification
public import RootedSubsumedForest0319Packed000
public import RootedSubsumedForest0319Packed001
public import RootedSubsumedForest0319Packed002
public import RootedSubsumedForest0319Packed003
public import RootedSubsumedForest0319Packed004
public import RootedSubsumedForest0319Packed005
public import RootedSubsumedForest0319Packed006

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0319
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 21976
abbrev nodeCount : Nat := 42707
abbrev leafCount : Nat := 69
def widths : PackedRawNatGrowth.Widths := ⟨15,16,7,7⟩
def blocks : Table PackedRawNatGrowth.Block :=
(.branch 150
 (.branch 50
 nodeBlocks000
 (.branch 100
 nodeBlocks001
 nodeBlocks002))
 (.branch 250
 (.branch 200
 nodeBlocks003
 nodeBlocks004)
 (.branch 300
 nodeBlocks005
 nodeBlocks006)))
def counterTable : Table Nat :=
(.branch 150
 (.branch 50
 nodeCounters000
 (.branch 100
 nodeCounters001
 nodeCounters002))
 (.branch 250
 (.branch 200
 nodeCounters003
 nodeCounters004)
 (.branch 300
 nodeCounters005
 nodeCounters006)))
def codes (i : Nat) : Nat :=
  let b := blocks.get (i / 128)
  PackedRawNatGrowth.drop
    (PackedRawNatGrowth.take 32 (PackedRawNatGrowth.drop (32*(i%128)) b.offsets)) b.payload
def counters (i : Nat) : Nat :=
  PackedRawNatGrowth.take 55 (PackedRawNatGrowth.drop (55*(i%128)) (counterTable.get (i/128)))
def rawNodes (i : Nat) := PackedRawNatGrowth.decodeNode widths (codes i)

def leafTable : Table (List Nat) :=
(.branch 34
 (.branch 17
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf [0,1,37,39,211,367,760,822,1099,1267,21970])
 (.leaf [0,2,35,67,259,415,722,808,1166,1219,1484]))
 (.branch 3
 (.leaf [0,2,35,93,247,403,701,797,1111,1231,21966])
 (.leaf [0,2,35,77,259,415,722,805,1110,1320,1533])))
 (.branch 6
 (.branch 5
 (.leaf [0,1,16,37,206,453,750,822,1036,1099,1267,21970])
 (.leaf [0,1,5,35,371,780,1113,1209,1516,1716,21822]))
 (.branch 7
 (.leaf [0,1,35,55,211,367,816,1089,1233,1526,1824,21821])
 (.leaf [0,1,19,35,209,395,790,1107,1231,1450,1508,21917]))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf [0,1,5,35,359,792,1093,1207,1532,1716,21918])
 (.leaf [0,1,5,35,359,792,1101,1288,1532,1711,21946]))
 (.branch 11
 (.leaf [0,3,69,78,246,402,648,702,784,1075,1498])
 (.leaf [0,1,15,76,215,671,746,843,1098,1170,1521])))
 (.branch 14
 (.branch 13
 (.leaf [0,1,39,47,211,367,666,916,1101,1532,21946])
 (.leaf [0,1,76,113,272,331,385,624,796,1051,1474]))
 (.branch 15
 (.leaf [0,31,35,98,135,245,373,804,867,1077,1233])
 (.branch 16
 (.leaf [0,17,39,78,176,248,648,784,1075,1123,1498])
 (.leaf [0,31,45,78,133,217,401,648,1075,1132,1498]))))))
 (.branch 25
 (.branch 21
 (.branch 19
 (.branch 18
 (.leaf [0,15,61,78,135,247,530,648,796,1075,1498])
 (.leaf [0,31,45,78,135,245,373,648,867,1075,1498]))
 (.branch 20
 (.leaf [0,2,97,259,415,675,839,1112,1268])
 (.leaf [0,8,91,121,186,416,623,832,1087,1216,1510])))
 (.branch 23
 (.branch 22
 (.leaf [0,1,15,58,227,627,845,1029,1077,1245,1535,21821])
 (.leaf [0,1,61,223,379,627,821,1111,1255,1446,21972]))
 (.branch 24
 (.leaf [0,1,91,92,235,391,639,845,1020,1098,1242,21975])
 (.leaf [0,1,15,96,331,550,638,825,1053,1209,1817,21579]))))
 (.branch 29
 (.branch 27
 (.branch 26
 (.leaf [0,6,35,80,152,291,400,781,1269,1522,1820,21888])
 (.leaf [0,1,9,31,245,377,626,826,1233,1534,1822,21880]))
 (.branch 28
 (.leaf [0,1,61,68,203,383,638,822,1231,1496,1553])
 (.leaf [0,2,17,45,224,291,495,625,1111,1255,1552,21972])))
 (.branch 31
 (.branch 30
 (.leaf [0,1,5,15,624,792,1051,1249,1534,1825,21858])
 (.leaf [0,1,5,15,624,792,1132,1257,1534,1820,21886]))
 (.branch 32
 (.leaf [0,1,19,31,221,401,624,802,1257,1534,1820,21886])
 (.branch 33
 (.leaf [0,1,5,128,359,632,788,1081,1249,1536,1616])
 (.leaf [0,1,5,128,359,632,788,1114,1194,1251,1504])))))))
 (.branch 51
 (.branch 42
 (.branch 38
 (.branch 36
 (.branch 35
 (.leaf [0,1,19,77,206,407,644,836,1110,1451,1533,21664])
 (.leaf [0,5,76,155,371,679,800,1086,1452,1509,21669]))
 (.branch 37
 (.leaf [0,1,15,76,215,632,848,1048,1518,1716,21666])
 (.leaf [0,5,15,76,143,667,909,1069,1366,1523,1862,21793])))
 (.branch 40
 (.branch 39
 (.leaf [0,2,15,77,208,453,668,1071,1430,1488,1854,21774])
 (.leaf [0,1,31,221,401,453,656,1091,1250,1536,1839,21784]))
 (.branch 41
 (.leaf [0,1,15,61,203,642,819,1077,1532,1713,21940])
 (.leaf [0,1,46,248,289,373,630,1077,1520,1714,21934]))))
 (.branch 46
 (.branch 44
 (.branch 43
 (.leaf [0,36,39,93,142,271,427,833,1026,1074,1206,21963])
 (.leaf [0,16,35,56,130,251,845,1030,1101,1221,1535,21820]))
 (.branch 45
 (.leaf [0,35,61,130,247,403,797,1111,1231,1448,21966])
 (.leaf [0,35,91,94,142,271,427,809,1020,1098,1207,21962])))
 (.branch 48
 (.branch 47
 (.leaf [0,12,35,130,263,401,805,1029,1091,1207,1531,21920])
 (.leaf [0,9,35,39,169,233,421,608,814,1082,1207,1531,21920]))
 (.branch 49
 (.leaf [0,9,35,145,253,425,609,781,1115,1219,1520,21916])
 (.branch 50
 (.leaf [0,15,31,36,132,245,558,826,1077,1290,1532,21940])
 (.leaf [0,31,35,79,133,221,401,802,1257,1534,1820,21886]))))))
 (.branch 60
 (.branch 55
 (.branch 53
 (.branch 52
 (.leaf [0,19,37,144,269,409,609,850,1046,1218,1519,21926])
 (.leaf [0,16,35,140,212,792,1101,1221,1528,1716,21820]))
 (.branch 54
 (.leaf [0,19,35,147,265,413,609,793,1103,1207,1532,21918])
 (.leaf [0,32,91,132,257,389,668,1079,1214,1535,1840,21791])))
 (.branch 57
 (.branch 56
 (.leaf [0,15,37,69,200,204,352,458,822,1099,1267,21970])
 (.leaf [0,31,35,135,245,377,972,1067,1225,1536,1840,21790]))
 (.branch 58
 (.leaf [0,16,35,162,256,468,992,1046,1213,1512,1842,21794])
 (.branch 59
 (.leaf [0,35,46,147,243,365,601,993,1014,1233,1522,21874])
 (.leaf [0,31,35,55,135,245,377,826,1233,1534,1822,21880])))))
 (.branch 64
 (.branch 62
 (.branch 61
 (.leaf [0,37,122,170,257,425,598,838,935,1220,1497,21883])
 (.leaf [0,16,35,123,140,212,792,1049,1225,1534,1679]))
 (.branch 63
 (.leaf [0,16,35,40,198,255,508,785,1025,1087,1219,21954])
 (.leaf [0,16,35,40,177,249,793,1095,1231,1452,1507,21919])))
 (.branch 66
 (.branch 65
 (.leaf [0,15,37,69,141,213,760,822,1099,1267,21970])
 (.leaf [0,15,36,141,213,816,1069,1206,1532,1715,21922]))
 (.branch 67
 (.leaf [0,16,35,140,212,792,1101,1288,1532,1711,21946])
 (.branch 68
 (.leaf [0,15,19,37,177,237,844,1048,1242,1507,1715,21377])
 (.leaf [0,35,45,79,140,212,395,1105,1243,1496,1715,21917]))))))))
def rawLeaves := leafTable.get

def leaves : Fin leafCount → List (Fin cellCount) := decodedLeaves rawLeaves
def quota : Nat → Nat
  | 0 => 1
  | 1 => 3
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

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0319

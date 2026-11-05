module
prelude
public import RootedSixBase03GrowthCacheData
public import RootedSixBase03FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification
public import RootedSubsumedForest0717Packed000
public import RootedSubsumedForest0717Packed001

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0717
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 5238
abbrev nodeCount : Nat := 11956
abbrev leafCount : Nat := 92
def widths : PackedRawNatGrowth.Widths := ⟨13,14,7,7⟩
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
(.branch 46
 (.branch 23
 (.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf [0,3,15,255,345,395,456,553,768,964,1278,1608])
 (.leaf [0,1,9,227,346,385,429,566,699,1025,1265,1606]))
 (.branch 3
 (.leaf [0,1,62,213,344,577,660,759,1039,1285,1335,1601])
 (.branch 4
 (.leaf [0,3,112,257,345,348,511,558,723,938,964,1278])
 (.leaf [0,5,62,131,346,476,542,722,1037,1285,1379,1603]))))
 (.branch 8
 (.branch 6
 (.leaf [0,16,62,117,204,346,592,761,943,1037,1285,1379])
 (.branch 7
 (.leaf [0,2,31,233,347,369,515,618,711,988,1289,1602])
 (.leaf [0,1,62,213,344,557,759,938,1039,1183,1285,1335])))
 (.branch 9
 (.leaf [0,1,9,225,345,371,569,760,942,1032,1112,1267])
 (.branch 10
 (.leaf [0,1,258,317,347,370,542,711,1012,1289,1608])
 (.leaf [0,27,61,155,193,346,476,546,722,1038,1294,1550])))))
 (.branch 17
 (.branch 14
 (.branch 12
 (.leaf [0,22,62,131,189,346,545,746,1037,1294,1473,1571])
 (.branch 13
 (.leaf [0,2,31,258,338,347,369,618,711,988,1289,1602])
 (.leaf [0,1,31,191,345,371,710,992,1098,1267,1470,1551])))
 (.branch 15
 (.leaf [0,1,31,215,347,370,710,1015,1120,1263,1352,1594])
 (.branch 16
 (.leaf [0,5,32,143,347,475,615,704,1000,1079,1292,1403])
 (.leaf [0,2,42,239,347,412,578,1027,1274,1382]))))
 (.branch 20
 (.branch 18
 (.leaf [0,1,111,215,347,370,542,710,1015,1263,1352,1594])
 (.branch 19
 (.leaf [0,1,111,215,347,370,542,710,1009,1117,1292,1468])
 (.leaf [0,1,82,215,347,391,554,698,1027,1374,1480,1492])))
 (.branch 21
 (.leaf [0,2,41,227,346,348,546,792,979,1256,1373,1591])
 (.branch 22
 (.leaf [0,5,35,131,346,433,590,701,1026,1208,1286,1380])
 (.leaf [0,2,83,239,347,412,586,742,1027,1365]))))))
 (.branch 34
 (.branch 28
 (.branch 25
 (.branch 24
 (.leaf [0,1,191,345,350,611,670,724,1001,1229,1609])
 (.leaf [0,1,81,227,283,346,352,568,752,979,1303,1420]))
 (.branch 26
 (.leaf [0,3,112,226,345,348,575,672,761,964,1278,1467])
 (.branch 27
 (.leaf [0,7,65,130,344,433,605,755,849,1013,1208,1231])
 (.leaf [0,5,77,143,347,454,557,743,784,1001,1058,1280]))))
 (.branch 31
 (.branch 29
 (.leaf [0,5,38,120,345,455,604,725,942,1002,1297,1377])
 (.branch 30
 (.leaf [0,2,31,243,347,369,618,711,850,988,1289,1602])
 (.leaf [0,2,22,245,346,351,469,592,721,1000,1241,1610])))
 (.branch 32
 (.leaf [0,2,61,228,344,353,476,596,761,937,1155,1254])
 (.branch 33
 (.leaf [0,1,31,192,347,373,496,737,908,954,988,1289])
 (.leaf [0,1,77,216,346,395,495,545,750,939,1004,1269])))))
 (.branch 40
 (.branch 37
 (.branch 35
 (.leaf [0,21,63,120,213,345,581,763,942,1099,1295,1323])
 (.branch 36
 (.leaf [0,2,41,231,347,415,474,543,785,1012,1253,1603])
 (.leaf [0,2,81,243,344,374,475,580,709,850,965,1604])))
 (.branch 38
 (.leaf [0,1,111,251,261,347,394,544,735,991,1249,1360])
 (.branch 39
 (.leaf [0,1,82,226,304,345,353,568,761,964,1418,1488])
 (.leaf [0,1,91,251,261,347,394,544,738,992,1257,1475]))))
 (.branch 43
 (.branch 41
 (.leaf [0,1,77,250,282,346,395,545,750,1004,1269,1467])
 (.branch 42
 (.leaf [0,2,61,202,325,344,353,596,761,1155,1254,1468])
 (.leaf [0,1,31,255,261,347,394,699,848,988,1277,1603])))
 (.branch 44
 (.leaf [0,2,41,255,260,347,415,543,827,1012,1253,1603])
 (.branch 45
 (.leaf [0,1,216,346,396,495,569,745,1020,1114,1268])
 (.leaf [0,1,6,287,346,396,501,569,749,1029,1294])))))))
 (.branch 69
 (.branch 57
 (.branch 51
 (.branch 48
 (.branch 47
 (.leaf [0,1,30,226,308,345,375,569,760,1032,1112,1267])
 (.leaf [0,1,61,250,282,346,400,544,747,1089,1291,1514]))
 (.branch 49
 (.leaf [0,4,111,227,281,346,422,570,699,976,1217,1265])
 (.branch 50
 (.leaf [0,6,31,140,335,347,507,737,901,988,1289])
 (.leaf [0,1,32,189,344,636,734,1016,1077,1243,1470,1572]))))
 (.branch 54
 (.branch 52
 (.leaf [0,2,31,188,345,615,722,1002,1162,1287,1331,1597])
 (.branch 53
 (.leaf [0,5,77,129,344,577,768,827,965,1254,1609])
 (.leaf [0,21,61,121,237,344,556,762,948,1242,1478])))
 (.branch 55
 (.leaf [0,1,97,189,344,544,734,987,1298,1357,1609])
 (.branch 56
 (.leaf [0,1,35,201,344,592,760,948,965,1242,1612])
 (.leaf [0,1,57,189,344,612,671,736,989,1230,1609])))))
 (.branch 63
 (.branch 60
 (.branch 58
 (.leaf [0,1,57,201,344,544,735,987,1298,1357,1609])
 (.branch 59
 (.leaf [0,8,77,140,347,557,733,822,1001,1058,1280,1485])
 (.leaf [0,4,57,212,347,580,637,713,1015,1263,1352,1594])))
 (.branch 61
 (.leaf [0,15,129,191,345,602,712,1013,1213,1229,1612])
 (.branch 62
 (.leaf [0,16,112,117,203,346,590,700,1026,1209,1262,1359])
 (.leaf [0,15,86,165,190,344,601,749,978,1213,1290,1478]))))
 (.branch 66
 (.branch 64
 (.leaf [0,15,97,129,191,345,602,713,1014,1208,1298,1378])
 (.branch 65
 (.leaf [0,31,140,250,346,411,723,1003,1145,1285,1379])
 (.leaf [0,31,45,116,239,347,412,710,1028,1122,1293,1473])))
 (.branch 67
 (.leaf [0,77,111,128,251,347,411,542,711,1015,1273,1381])
 (.branch 68
 (.leaf [0,71,97,179,200,347,495,558,698,1016,1208,1281])
 (.leaf [0,38,41,181,212,346,495,543,942,1004,1269,1409]))))))
 (.branch 80
 (.branch 74
 (.branch 71
 (.branch 70
 (.leaf [0,41,77,164,212,347,546,939,976,1100,1295,1440])
 (.leaf [0,27,31,119,203,346,413,722,1029,1143,1294,1468]))
 (.branch 72
 (.leaf [0,15,16,169,250,346,527,541,747,976,1290,1612])
 (.branch 73
 (.leaf [0,27,77,119,204,345,497,557,758,1033,1113,1279])
 (.leaf [0,28,72,167,193,347,475,546,710,1028,1209,1293]))))
 (.branch 77
 (.branch 75
 (.leaf [0,28,57,120,215,347,412,581,713,1028,1293,1468])
 (.branch 76
 (.leaf [0,57,58,140,236,347,556,737,991,1239,1373,1591])
 (.leaf [0,57,112,128,224,346,544,746,979,1251,1373,1591])))
 (.branch 78
 (.leaf [0,9,27,143,231,347,477,544,744,988,1289,1609])
 (.branch 79
 (.leaf [0,30,31,183,226,345,369,671,711,964,1266,1604])
 (.leaf [0,15,27,185,202,344,427,589,760,965,1242,1607])))))
 (.branch 86
 (.branch 83
 (.branch 81
 (.leaf [0,32,60,164,248,347,735,1009,1117,1292])
 (.branch 82
 (.leaf [0,77,116,237,345,557,759,943,1033,1113,1279])
 (.leaf [0,31,77,116,237,345,723,939,1002,1162,1297,1377])))
 (.branch 84
 (.leaf [0,31,35,164,248,347,711,943,1015,1120,1273,1381])
 (.branch 85
 (.leaf [0,111,164,248,347,543,711,943,1015,1273,1381])
 (.leaf [0,57,112,128,224,346,566,699,1026,1203,1286,1380]))))
 (.branch 89
 (.branch 87
 (.leaf [0,31,77,116,237,345,723,939,980,1099,1279,1553])
 (.branch 88
 (.leaf [0,31,35,152,249,346,723,942,968,1099,1291,1532])
 (.leaf [0,32,43,164,248,347,922,1012,1289])))
 (.branch 90
 (.leaf [0,31,51,140,248,347,735,947,988,1289,1611])
 (.branch 91
 (.leaf [0,140,236,347,556,736,949,988,1277,1613])
 (.leaf [0,77,98,153,237,345,558,726,946,968,1233]))))))))
def rawLeaves := leafTable.get

def leaves : Fin leafCount → List (Fin cellCount) := decodedLeaves rawLeaves
def quota : Nat → Nat
  | 0 => 1
  | 1 => 2
  | 2 => 6
  | 3 => 3
  | 4 => 0
  | 5 => 0
  | 6 => 0
  | 7 => 0
  | 8 => 0
  | 9 => 0
  | 10 => 0
  | _ => 0

def nodeTest (i : Nat) : Bool :=
  SubsumedCounterReplay.check widths cellCount 1024 96 leafCount nodeCount
    Papers.RationalityTen.RootedCaches.RootedSixBase03.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixBase03.badMasks
    Papers.RationalityTen.RootedCaches.RootedSixBase03.kindMasks Papers.RationalityTen.RootedCaches.RootedSixBase03.keys Papers.RationalityTen.RootedCaches.RootedSixBase03.fastKind quota
    Papers.RationalityTen.FacetUniverses.RootedSixBase03.Generators.FastWords.rawMaps rawLeaves codes counters i
theorem nodeTest_sound (i : Nat) (h : nodeTest i = true) :
    nodeBounds cellCount 1024 96 leafCount nodeCount (rawNodes i) = true ∧
      SubsumedRawGrowth.nodeCheck Papers.RationalityTen.RootedCaches.RootedSixBase03.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixBase03.badMasks
        Papers.RationalityTen.RootedCaches.RootedSixBase03.kindMasks Papers.RationalityTen.RootedCaches.RootedSixBase03.keys Papers.RationalityTen.RootedCaches.RootedSixBase03.fastKind quota
        Papers.RationalityTen.FacetUniverses.RootedSixBase03.Generators.FastWords.rawMaps rawLeaves rawNodes i = true :=
  SubsumedCounterReplay.check_sound widths cellCount 1024 96 leafCount nodeCount
    Papers.RationalityTen.RootedCaches.RootedSixBase03.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixBase03.badMasks
    Papers.RationalityTen.RootedCaches.RootedSixBase03.kindMasks Papers.RationalityTen.RootedCaches.RootedSixBase03.keys Papers.RationalityTen.RootedCaches.RootedSixBase03.fastKind quota
    Papers.RationalityTen.FacetUniverses.RootedSixBase03.Generators.FastWords.rawMaps rawLeaves codes counters i h
def leafTest (i : Nat) : Bool :=
  listBounds cellCount (rawLeaves i) &&
    (WitnessGrowthDAG.closedCheck FacetUniverses.RootedSixBase03.ridgeList
      ((rawLeaves i).map (Fin.ofNat cellCount)) &&
      decide (((rawLeaves i).map (Fin.ofNat cellCount)).Nodup))

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0717

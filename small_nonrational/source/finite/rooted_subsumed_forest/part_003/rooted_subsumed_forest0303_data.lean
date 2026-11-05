module
prelude
public import RootedSixBase01GrowthCacheData
public import RootedSixBase01FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification
public import RootedSubsumedForest0303Packed000
public import RootedSubsumedForest0303Packed001
public import RootedSubsumedForest0303Packed002

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0303
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 15246
abbrev nodeCount : Nat := 18357
abbrev leafCount : Nat := 105
def widths : PackedRawNatGrowth.Widths := ⟨14,15,6,7⟩
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
(.branch 52
 (.branch 26
 (.branch 13
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf [0,7,72,185,415,662,766,838,1015])
 (.branch 2
 (.leaf [0,5,36,117,357,768,928,1031,1187,1193,12497])
 (.leaf [0,6,71,153,393,626,765,991,1370,12504])))
 (.branch 4
 (.leaf [0,1,48,189,369,767,934,1030,1186,1472,13427])
 (.branch 5
 (.leaf [0,35,48,143,192,398,586,767,857,1149,1552,13990])
 (.leaf [0,45,73,135,215,411,585,766,1033,1407,1557,13360]))))
 (.branch 9
 (.branch 7
 (.leaf [0,2,61,231,366,661,768,852,1144,1429,11798])
 (.branch 8
 (.leaf [0,35,121,243,372,586,767,850,857,1030,14307])
 (.leaf [0,35,62,133,255,603,766,848,858,1122,12960])))
 (.branch 11
 (.branch 10
 (.leaf [0,2,15,201,294,450,661,767,898,1186,13959])
 (.leaf [0,3,98,188,336,673,765,878,994,1150,13071]))
 (.branch 12
 (.leaf [0,2,16,225,666,767,934,1186,14013])
 (.leaf [0,15,36,117,201,767,929,951,1186,1214,13959])))))
 (.branch 19
 (.branch 16
 (.branch 14
 (.leaf [0,2,61,225,344,648,767,1438,1484,1573,14235])
 (.branch 15
 (.leaf [0,15,36,117,201,767,856,1032,1173,1573,12777])
 (.leaf [0,15,36,117,201,767,856,1173,1374,1573,13974])))
 (.branch 17
 (.leaf [0,16,37,153,237,768,919,1005,1179,1466])
 (.branch 18
 (.leaf [0,16,37,153,237,768,919,1187,14015])
 (.leaf [0,15,36,117,201,767,856,1030,1064,1486,14361]))))
 (.branch 22
 (.branch 20
 (.leaf [0,15,36,117,201,767,856,993,1371,1443,14376])
 (.branch 21
 (.leaf [0,16,35,116,225,767,1017,1178,1220,1464,13147])
 (.leaf [0,2,61,225,344,648,767,1153,1229,1566,13773])))
 (.branch 24
 (.branch 23
 (.leaf [0,15,57,117,213,648,768,906,1175,1594,13907])
 (.leaf [0,1,87,213,345,768,1001,1189,1415,1622,13475]))
 (.branch 25
 (.leaf [0,1,87,213,345,630,768,915,1005,1179,13757])
 (.leaf [0,1,57,189,369,651,725,766,1028,1164,13743]))))))
 (.branch 39
 (.branch 32
 (.branch 29
 (.branch 27
 (.leaf [0,15,54,141,189,675,766,942,993,1422,14339])
 (.branch 28
 (.leaf [0,15,42,117,213,676,768,942,969,1424,14351])
 (.leaf [0,1,57,189,369,766,932,1018,1174,1469,13481])))
 (.branch 30
 (.leaf [0,4,107,212,392,765,910,970,1126,1469,13505])
 (.branch 31
 (.leaf [0,1,87,213,345,630,768,915,1019,1469,14362])
 (.leaf [0,9,63,161,213,676,768,945,1189,1428,12881]))))
 (.branch 35
 (.branch 33
 (.leaf [0,35,87,138,237,277,385,768,878,1151,13906])
 (.branch 34
 (.leaf [0,35,150,224,319,406,766,858,992,1119,13741])
 (.leaf [0,35,150,225,298,394,767,857,1030,1467,14307])))
 (.branch 37
 (.branch 36
 (.leaf [0,36,61,174,200,340,410,765,858,1123,12777])
 (.leaf [0,58,63,140,236,404,616,766,1129,1326,13774]))
 (.branch 38
 (.leaf [0,57,88,116,225,393,628,767,992,1141,13747])
 (.leaf [0,36,62,172,248,402,767,921,1155,1451])))))
 (.branch 45
 (.branch 42
 (.branch 40
 (.leaf [0,35,65,136,249,366,768,899,1019,1474,14255])
 (.branch 41
 (.leaf [0,37,91,184,212,414,765,900,1006,1475,14171])
 (.leaf [0,58,73,149,189,379,766,1024,1407,1568,13543])))
 (.branch 43
 (.leaf [0,57,112,160,200,390,765,1013,1152,1388,13417])
 (.branch 44
 (.leaf [0,57,125,213,355,649,768,898,1005,1179,13757])
 (.leaf [0,53,97,161,188,391,673,765,945,1150,13957]))))
 (.branch 48
 (.branch 46
 (.leaf [0,35,224,415,766,858,988,1119,1455,1614,12141])
 (.branch 47
 (.leaf [0,36,61,200,415,765,858,1064,1123,1486,12195])
 (.leaf [0,39,61,172,248,628,767,944,1141,1430,12923])))
 (.branch 50
 (.branch 49
 (.leaf [0,35,224,415,766,858,1010,1149,1467,1531,12141])
 (.leaf [0,51,97,185,200,662,765,943,970,1126,13029]))
 (.branch 51
 (.leaf [0,58,97,149,201,662,767,856,1007,1163,12919])
 (.leaf [0,31,35,121,228,377,560,767,857,1030,14307])))))))
 (.branch 78
 (.branch 65
 (.branch 58
 (.branch 55
 (.branch 53
 (.leaf [0,31,35,119,203,415,495,765,1016,1121,13735])
 (.branch 54
 (.leaf [0,31,35,119,203,765,1021,1121,1434,1617,13033])
 (.leaf [0,51,73,147,192,394,586,766,1028,1461,1495,13453])))
 (.branch 56
 (.leaf [0,35,131,216,411,585,768,875,1033,1575,14195])
 (.branch 57
 (.leaf [0,52,72,144,204,410,585,665,767,889,1495,14001])
 (.leaf [0,31,35,121,228,767,857,1032,1149,1552,12993]))))
 (.branch 61
 (.branch 59
 (.leaf [0,35,104,140,256,412,767,1000,1122,1368,13204])
 (.branch 60
 (.leaf [0,2,71,259,339,383,768,964,1450,1525,13439])
 (.leaf [0,1,111,258,317,371,767,965,1165,1430,13367])))
 (.branch 63
 (.branch 62
 (.leaf [0,15,54,145,256,557,613,767,945,1163,13853])
 (.leaf [0,2,61,259,339,661,768,1144,1381,1429,12897]))
 (.branch 64
 (.leaf [0,36,99,117,259,318,359,768,877,1175,13907])
 (.leaf [0,36,61,157,257,344,579,768,920,1413,14262])))))
 (.branch 71
 (.branch 68
 (.branch 66
 (.leaf [0,35,97,145,256,345,557,767,900,1007,14201])
 (.branch 67
 (.leaf [0,35,75,116,258,338,396,767,860,1030,14361])
 (.leaf [0,35,104,128,246,340,411,766,859,1134,13989])))
 (.branch 69
 (.leaf [0,1,35,244,306,360,580,766,880,998,1570,14301])
 (.branch 70
 (.leaf [0,1,54,233,286,372,583,612,767,1022,1149,14098])
 (.leaf [0,1,62,244,303,624,766,926,1122,1590,12945]))))
 (.branch 74
 (.branch 72
 (.leaf [0,1,35,318,360,766,880,998,1151,1334,1556,12681])
 (.branch 73
 (.leaf [0,1,54,296,372,612,767,1022,1145,1501,1623,12682])
 (.leaf [0,1,365,618,768,894,1026,1170,1365,12618])))
 (.branch 76
 (.branch 75
 (.leaf [0,1,377,625,767,1016,1156,1362,1463,12619])
 (.leaf [0,35,75,116,401,767,860,1022,1173,1573,12673]))
 (.branch 77
 (.leaf [0,35,104,128,413,766,859,1018,1134,1354,12675])
 (.leaf [0,35,110,140,400,767,901,1007,1163,1217,12676]))))))
 (.branch 91
 (.branch 84
 (.branch 81
 (.branch 79
 (.leaf [0,57,71,152,413,614,765,991,1366,12621])
 (.branch 80
 (.leaf [0,31,35,119,384,768,907,1031,1187,1194,12654])
 (.leaf [0,31,35,121,359,768,878,995,1151,1482,12716])))
 (.branch 82
 (.leaf [0,35,121,372,597,767,857,1022,1149,1552,12720])
 (.branch 83
 (.leaf [0,53,111,170,384,602,667,765,974,1157,1518,12670])
 (.leaf [0,35,97,145,347,597,767,900,983,1139,12725]))))
 (.branch 87
 (.branch 85
 (.leaf [0,35,62,133,375,599,766,858,1073,1122,12722])
 (.branch 86
 (.leaf [0,2,5,262,401,537,666,934,986,1178,1602,14388])
 (.leaf [0,1,110,201,345,618,873,1019,1175,1473,14402])))
 (.branch 89
 (.branch 88
 (.leaf [0,1,110,201,345,628,1019,1175,1208,1473,14402])
 (.leaf [0,1,110,201,345,655,696,1019,1175,1473,14402]))
 (.branch 90
 (.leaf [0,1,75,201,345,624,1019,1175,1478,1587,14402])
 (.leaf [0,1,51,189,357,622,1031,1187,1478,1587,14398])))))
 (.branch 98
 (.branch 94
 (.branch 92
 (.leaf [0,35,107,148,236,378,879,983,1139,1476,14394])
 (.branch 93
 (.leaf [0,57,108,160,200,390,611,1019,1175,1476,14390])
 (.leaf [0,57,74,125,201,355,652,1014,1273,1473,14402])))
 (.branch 96
 (.branch 95
 (.leaf [0,1,107,215,402,452,610,1007,1163,1476,14386])
 (.leaf [0,31,108,122,227,359,619,995,1151,1476,14398]))
 (.branch 97
 (.leaf [0,57,112,179,229,398,584,623,1020,1185,1550,14385])
 (.leaf [0,2,113,202,336,349,598,660,975,1124,1532,14404]))))
 (.branch 101
 (.branch 99
 (.leaf [0,10,101,123,251,396,595,620,1022,1169,1612,14389])
 (.branch 100
 (.leaf [0,9,111,171,203,409,590,668,974,1184,1570,14384])
 (.leaf [0,31,101,130,257,351,579,672,973,1135,1582,14399])))
 (.branch 103
 (.branch 102
 (.leaf [0,1,107,246,296,371,612,983,1139,1476,14394])
 (.leaf [0,1,72,259,318,359,640,966,1229,1474,14399]))
 (.branch 104
 (.leaf [0,35,107,150,222,392,1007,1163,1216,1476,14386])
 (.leaf [0,87,108,162,234,356,609,995,1151,1476,14398]))))))))
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
  | 7 => 1
  | 8 => 0
  | 9 => 0
  | 10 => 0
  | _ => 0

def nodeTest (i : Nat) : Bool :=
  SubsumedCounterReplay.check widths cellCount 1024 48 leafCount nodeCount
    Papers.RationalityTen.RootedCaches.RootedSixBase01.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixBase01.badMasks
    Papers.RationalityTen.RootedCaches.RootedSixBase01.kindMasks Papers.RationalityTen.RootedCaches.RootedSixBase01.keys Papers.RationalityTen.RootedCaches.RootedSixBase01.fastKind quota
    Papers.RationalityTen.FacetUniverses.RootedSixBase01.Generators.FastWords.rawMaps rawLeaves codes counters i
theorem nodeTest_sound (i : Nat) (h : nodeTest i = true) :
    nodeBounds cellCount 1024 48 leafCount nodeCount (rawNodes i) = true ∧
      SubsumedRawGrowth.nodeCheck Papers.RationalityTen.RootedCaches.RootedSixBase01.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixBase01.badMasks
        Papers.RationalityTen.RootedCaches.RootedSixBase01.kindMasks Papers.RationalityTen.RootedCaches.RootedSixBase01.keys Papers.RationalityTen.RootedCaches.RootedSixBase01.fastKind quota
        Papers.RationalityTen.FacetUniverses.RootedSixBase01.Generators.FastWords.rawMaps rawLeaves rawNodes i = true :=
  SubsumedCounterReplay.check_sound widths cellCount 1024 48 leafCount nodeCount
    Papers.RationalityTen.RootedCaches.RootedSixBase01.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixBase01.badMasks
    Papers.RationalityTen.RootedCaches.RootedSixBase01.kindMasks Papers.RationalityTen.RootedCaches.RootedSixBase01.keys Papers.RationalityTen.RootedCaches.RootedSixBase01.fastKind quota
    Papers.RationalityTen.FacetUniverses.RootedSixBase01.Generators.FastWords.rawMaps rawLeaves codes counters i h
def leafTest (i : Nat) : Bool :=
  listBounds cellCount (rawLeaves i) &&
    (WitnessGrowthDAG.closedCheck FacetUniverses.RootedSixBase01.ridgeList
      ((rawLeaves i).map (Fin.ofNat cellCount)) &&
      decide (((rawLeaves i).map (Fin.ofNat cellCount)).Nodup))

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0303

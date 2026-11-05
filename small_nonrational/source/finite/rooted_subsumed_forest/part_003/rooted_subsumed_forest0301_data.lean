module
prelude
public import RootedSixBase01GrowthCacheData
public import RootedSixBase01FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification
public import RootedSubsumedForest0301Packed000
public import RootedSubsumedForest0301Packed001
public import RootedSubsumedForest0301Packed002
public import RootedSubsumedForest0301Packed003

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0301
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 15246
abbrev nodeCount : Nat := 23092
abbrev leafCount : Nat := 120
def widths : PackedRawNatGrowth.Widths := ⟨14,15,6,7⟩
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
(.branch 60
 (.branch 30
 (.branch 15
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf [0,1,5,357,766,775,932,1029,1166,1462,5304])
 (.branch 2
 (.leaf [0,7,72,185,415,662,766,838,1015])
 (.leaf [0,5,36,379,767,817,921,1016,1155,1463,2613])))
 (.branch 5
 (.branch 4
 (.leaf [0,1,62,219,392,459,625,767,829,1456,7034])
 (.leaf [0,57,71,157,255,399,584,614,765,827,6150]))
 (.branch 6
 (.leaf [0,71,87,155,243,411,584,614,765,806,6258])
 (.leaf [0,31,74,121,231,359,637,768,990,3252]))))
 (.branch 11
 (.branch 9
 (.branch 8
 (.leaf [0,35,48,140,244,400,767,1002,1134,1370,4569])
 (.leaf [0,2,52,233,649,765,813,986,1185,1550,4487]))
 (.branch 10
 (.leaf [0,2,102,245,661,765,823,907,974,1183,4485])
 (.leaf [0,1,72,221,377,650,729,766,841,6349])))
 (.branch 13
 (.branch 12
 (.leaf [0,1,9,225,348,767,934,1017,1178,1464,5196])
 (.leaf [0,1,61,237,262,347,628,768,919,1399,1466,6983]))
 (.branch 14
 (.leaf [0,1,111,249,261,363,616,768,920,985,1446,6875])
 (.leaf [0,2,71,200,336,661,765,904,979,1241,4424])))))
 (.branch 22
 (.branch 18
 (.branch 16
 (.leaf [0,2,76,249,274,614,768,902,1031,1187,4103])
 (.branch 17
 (.leaf [0,1,62,201,345,625,767,1372,1422,1443,7028])
 (.leaf [0,16,37,153,237,768,919,1005,1179,1466])))
 (.branch 20
 (.branch 19
 (.leaf [0,16,35,116,225,767,860,1032,1112,1573,6864])
 (.leaf [0,16,35,165,188,735,765,953,1133,1399,6412]))
 (.branch 21
 (.leaf [0,1,189,357,766,892,1025,1166,1394,1625,5348])
 (.leaf [0,16,40,116,237,676,768,943,1189,1466,6084]))))
 (.branch 26
 (.branch 24
 (.branch 23
 (.leaf [0,2,71,188,666,765,890,979,1236,1481,4404])
 (.leaf [0,4,87,212,665,765,889,979,1123,1482,4409]))
 (.branch 25
 (.leaf [0,2,35,188,683,765,1033,1133,1413,1620,4434])
 (.leaf [0,1,87,189,613,766,1033,1157,1415,1622,4326])))
 (.branch 28
 (.branch 27
 (.leaf [0,10,36,117,249,360,768,1031,1187,1201,4625])
 (.leaf [0,36,71,174,200,340,409,765,863,979,4983]))
 (.branch 29
 (.leaf [0,57,71,150,224,319,406,612,766,988,1455,6427])
 (.leaf [0,57,71,186,188,338,394,626,765,1483,6241]))))))
 (.branch 45
 (.branch 37
 (.branch 33
 (.branch 31
 (.leaf [0,35,57,160,200,390,704,765,1017,1145,5886])
 (.branch 32
 (.leaf [0,36,62,172,248,402,767,921,1155,1451])
 (.leaf [0,107,184,212,414,645,765,900,1004,1118,5893])))
 (.branch 35
 (.branch 34
 (.leaf [0,58,87,172,212,402,614,765,1005,1133,5892])
 (.leaf [0,37,58,236,414,766,856,1006,1162,1467,2731]))
 (.branch 36
 (.leaf [0,1,62,203,390,634,765,1172,1388,1528,2076])
 (.leaf [0,2,71,227,415,495,766,988,1450,1526,5150]))))
 (.branch 41
 (.branch 39
 (.branch 38
 (.leaf [0,15,36,118,227,555,601,766,995,1450,6842])
 (.leaf [0,35,81,119,203,598,765,979,1172,1236,1528,4424]))
 (.branch 40
 (.leaf [0,82,88,131,191,598,634,765,967,1184,1549,4422])
 (.leaf [0,36,102,167,228,410,584,767,853,1173,1529,6313])))
 (.branch 43
 (.branch 42
 (.leaf [0,73,101,182,241,386,584,679,766,874,1539,6097])
 (.leaf [0,38,87,214,361,599,768,969,1168,1424,2759]))
 (.branch 44
 (.leaf [0,36,61,227,410,605,766,1091,1120,1388,2541])
 (.leaf [0,35,90,140,244,400,766,880,1001,1570,6973])))))
 (.branch 52
 (.branch 48
 (.branch 46
 (.leaf [0,36,63,164,256,412,767,926,7046])
 (.branch 47
 (.leaf [0,36,71,174,246,404,766,976,1451,1505,4983])
 (.leaf [0,73,88,116,245,401,622,768,878,1545,6233])))
 (.branch 50
 (.branch 49
 (.leaf [0,35,39,174,246,368,766,855,966,1247,1469,7063])
 (.leaf [0,71,75,129,197,353,650,766,940,1332,1515,6360]))
 (.branch 51
 (.leaf [0,2,35,222,298,395,683,765,1005,1133,5892])
 (.leaf [0,1,87,258,317,371,625,767,969,1156,5896]))))
 (.branch 56
 (.branch 54
 (.branch 53
 (.leaf [0,2,73,258,338,399,649,767,6368])
 (.leaf [0,35,116,258,338,395,767,857,968,1131,5897]))
 (.branch 55
 (.leaf [0,35,128,246,340,408,766,859,1010,1571,6972])
 (.leaf [0,35,72,140,234,342,409,766,884,1003,4977])))
 (.branch 58
 (.branch 57
 (.leaf [0,37,88,153,223,299,349,768,927,990,7049])
 (.leaf [0,35,62,128,246,340,411,766,858,1122,3954]))
 (.branch 59
 (.leaf [0,35,87,116,258,338,399,767,857,1134,6368])
 (.leaf [0,1,72,244,306,360,580,766,1003,1378,5174])))))))
 (.branch 90
 (.branch 75
 (.branch 67
 (.branch 63
 (.branch 61
 (.leaf [0,31,71,119,259,318,383,636,768,964,1455,6430])
 (.branch 62
 (.leaf [0,31,74,119,259,318,383,637,768,1488,6137])
 (.leaf [0,31,74,121,245,363,581,637,768,939,6262])))
 (.branch 65
 (.branch 64
 (.leaf [0,35,101,136,246,340,766,858,1010,1145,1603,4343])
 (.leaf [0,35,107,124,259,339,768,881,1023,1134,1558,4127]))
 (.branch 66
 (.leaf [0,15,36,118,233,767,918,975,1175,1311,1534,3110])
 (.leaf [0,1,72,259,360,636,768,1004,1195,1465,1516,1874]))))
 (.branch 71
 (.branch 69
 (.branch 68
 (.leaf [0,2,61,220,324,652,765,901,1147,1273,4239])
 (.leaf [0,35,62,150,232,319,766,859,1159,1237,4457]))
 (.branch 70
 (.leaf [0,2,89,233,649,767,992,1132,1442,4487])
 (.leaf [0,3,62,232,678,766,932,1171,4499])))
 (.branch 73
 (.branch 72
 (.leaf [0,35,62,140,244,766,866,960,1159,1237,4497])
 (.leaf [0,37,88,258,392,767,964,1132,1456,1615,2737]))
 (.branch 74
 (.leaf [0,39,45,172,364,496,625,766,921,966,1159,3653])
 (.leaf [0,39,45,128,388,664,765,902,967,1135,1271,3803])))))
 (.branch 82
 (.branch 78
 (.branch 76
 (.leaf [0,2,35,344,686,768,899,995,1151,1480,3709])
 (.branch 77
 (.leaf [0,1,57,345,613,768,920,1019,1175,1483,3601])
 (.leaf [0,53,107,154,399,602,623,768,1021,1159,1516,3623])))
 (.branch 80
 (.branch 79
 (.leaf [0,51,71,178,386,605,638,766,1008,1321,1494,3513])
 (.leaf [0,2,56,389,649,768,1031,1187,3791]))
 (.branch 81
 (.leaf [0,2,76,389,649,768,895,980,1143,1444,3791])
 (.leaf [0,2,102,401,661,767,895,985,1096,1147,3789]))))
 (.branch 86
 (.branch 84
 (.branch 83
 (.leaf [0,2,35,389,687,768,899,980,1143,1444,3791])
 (.leaf [0,35,57,116,389,768,902,1031,1187,1194,3791]))
 (.branch 85
 (.leaf [0,1,54,365,613,767,1025,1173,1364,1573,3476])
 (.leaf [0,8,87,184,414,621,1000,1125,1512,7163])))
 (.branch 88
 (.branch 87
 (.leaf [0,1,54,213,345,613,947,1007,1163,1477,7163])
 (.leaf [0,1,57,189,369,642,913,1030,1186,1475,7146]))
 (.branch 89
 (.leaf [0,37,58,161,188,391,919,1031,1187,1472,7138])
 (.leaf [0,71,172,248,402,614,948,967,1478,7131]))))))
 (.branch 105
 (.branch 97
 (.branch 93
 (.branch 91
 (.leaf [0,7,75,130,353,520,667,761,1002,1134,1582,7165])
 (.branch 92
 (.leaf [0,5,36,131,413,558,704,991,1135,1263,1590,7125])
 (.leaf [0,5,36,129,369,757,951,1028,1133,1216,1440,7125])))
 (.branch 95
 (.branch 94
 (.leaf [0,7,39,128,380,664,943,968,1132,1271,1402,7165])
 (.leaf [0,6,35,186,338,397,688,1001,1184,1218,1570,7124]))
 (.branch 96
 (.leaf [0,1,81,201,345,628,1011,1141,1478,1612,7167])
 (.leaf [0,1,111,189,369,616,1030,1129,1331,1475,7151]))))
 (.branch 101
 (.branch 99
 (.branch 98
 (.leaf [0,57,71,161,188,391,626,1031,1332,1475,7143])
 (.leaf [0,58,111,172,212,402,615,999,1128,1476,7135]))
 (.branch 100
 (.leaf [0,10,101,183,191,397,595,680,962,1171,1587,7133])
 (.leaf [0,9,107,159,215,408,592,656,986,1185,1550,7125])))
 (.branch 103
 (.branch 102
 (.leaf [0,1,114,209,365,625,1021,1115,1156,7167])
 (.leaf [0,38,97,163,235,344,723,978,1158,1222,1597,7165]))
 (.branch 104
 (.leaf [0,57,81,116,233,389,625,997,1094,1156,1609,7167])
 (.leaf [0,2,15,223,299,418,646,981,1179,1445,1576,7156])))))
 (.branch 112
 (.branch 108
 (.branch 106
 (.leaf [0,2,61,259,339,366,433,609,1143,1429,1578,7156])
 (.branch 107
 (.leaf [0,31,35,121,245,363,581,878,985,1143,1602,7166])
 (.leaf [0,32,102,119,209,399,562,624,1021,1121,1608,7167])))
 (.branch 110
 (.branch 109
 (.leaf [0,32,87,118,233,375,583,649,997,1132,1602,7167])
 (.leaf [0,1,72,234,275,359,613,995,1313,1476,7159]))
 (.branch 111
 (.leaf [0,1,111,258,317,371,628,963,1141,1475,7150])
 (.leaf [0,35,111,126,198,393,1030,1121,1352,1473,7135]))))
 (.branch 116
 (.branch 114
 (.branch 113
 (.leaf [0,37,81,163,235,344,987,1156,1477,1611,7167])
 (.leaf [0,36,59,128,257,413,708,988,1136,1259,1553,7156]))
 (.branch 115
 (.leaf [0,5,72,131,413,558,634,991,1262,1279,1589,7129])
 (.leaf [0,7,75,154,352,519,621,978,1175,1355,1582,7169])))
 (.branch 118
 (.branch 117
 (.leaf [0,6,71,153,393,678,932,1028,1218,1281,1461,7128])
 (.leaf [0,1,114,209,365,625,1000,1177,1271,7169]))
 (.branch 119
 (.leaf [0,57,74,116,233,389,625,976,1256,1304,1620,7169])
 (.leaf [0,57,81,116,233,389,625,976,1177,1271,1607,7169]))))))))
def rawLeaves := leafTable.get

def leaves : Fin leafCount → List (Fin cellCount) := decodedLeaves rawLeaves
def quota : Nat → Nat
  | 0 => 1
  | 1 => 2
  | 2 => 4
  | 3 => 4
  | 4 => 0
  | 5 => 1
  | 6 => 0
  | 7 => 0
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

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0301

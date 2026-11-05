module
prelude
public import RootedSixBase01GrowthCacheData
public import RootedSixBase01FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification
public import RootedSubsumedForest0348Packed000
public import RootedSubsumedForest0348Packed001

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0348
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 15246
abbrev nodeCount : Nat := 11851
abbrev leafCount : Nat := 89
def widths : PackedRawNatGrowth.Widths := ⟨14,14,6,7⟩
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
(.branch 44
 (.branch 22
 (.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf [0,5,72,129,369,650,766,827,848,1015,1362])
 (.leaf [0,1,5,345,630,768,791,915,1014,1182,1365]))
 (.branch 3
 (.leaf [0,1,5,345,637,768,791,1005,1180,1363,1466])
 (.branch 4
 (.leaf [0,5,72,143,412,557,613,766,771,1003,1366])
 (.leaf [0,5,36,117,357,766,771,1029,1169,1364,1462]))))
 (.branch 8
 (.branch 6
 (.leaf [0,7,72,185,415,662,766,838,1015])
 (.branch 7
 (.leaf [0,1,35,192,382,471,601,768,833,878,1026,1146])
 (.leaf [0,35,61,133,255,371,585,766,848,858,1119,1409])))
 (.branch 9
 (.leaf [0,35,72,145,254,360,585,766,847,879,1003,1195])
 (.branch 10
 (.leaf [0,35,87,145,254,360,585,766,847,879,1003,1122])
 (.leaf [0,31,74,118,231,360,661,768,852,1026,1364])))))
 (.branch 16
 (.branch 13
 (.branch 12
 (.leaf [0,59,72,140,256,412,613,766,772,1003,1366])
 (.leaf [0,1,107,248,282,371,612,767,921,983,1139,1468]))
 (.branch 14
 (.leaf [0,1,62,236,303,371,625,766,921,1044,1159,1490])
 (.branch 15
 (.leaf [0,1,65,249,261,359,613,768,920,1019,1175,1473])
 (.leaf [0,1,72,224,304,359,640,766,920,966,1229,1470]))))
 (.branch 19
 (.branch 17
 (.leaf [0,15,35,121,225,523,767,857,987,1131,1457,1616])
 (.branch 18
 (.leaf [0,1,87,237,262,348,625,768,919,1005,1179,1466])
 (.leaf [0,1,72,248,282,372,613,767,926,1022,1298,1568])))
 (.branch 20
 (.leaf [0,1,87,225,283,348,636,767,927,1002,1134,1591])
 (.branch 21
 (.leaf [0,2,61,249,260,387,614,768,899,1050,1143,1429])
 (.leaf [0,1,15,224,315,555,637,766,920,990,1166,1450]))))))
 (.branch 33
 (.branch 27
 (.branch 24
 (.branch 23
 (.leaf [0,16,37,153,237,768,919,1005,1179,1466])
 (.leaf [0,1,72,213,357,618,768,894,1000,1361,1428,1556]))
 (.branch 25
 (.leaf [0,1,72,213,357,660,694,768,960,1000,1428,1556])
 (.branch 26
 (.leaf [0,1,35,213,357,768,875,1000,1167,1195,1436,1619])
 (.leaf [0,1,36,213,357,683,768,877,1000,1167,1436,1619]))))
 (.branch 30
 (.branch 28
 (.leaf [0,15,54,141,189,674,766,947,966,1159,1368])
 (.branch 29
 (.leaf [0,1,97,189,357,613,766,1029,1169,1364,1462])
 (.leaf [0,1,35,189,357,766,876,998,1151,1334,1470,1556])))
 (.branch 31
 (.leaf [0,1,36,213,357,683,768,877,1023,1161,1468,1575])
 (.branch 32
 (.leaf [0,2,71,225,344,643,719,767,919,975,1470,1539])
 (.leaf [0,1,72,213,357,618,768,894,1023,1277,1468,1556])))))
 (.branch 38
 (.branch 35
 (.branch 34
 (.leaf [0,15,57,117,201,649,767,993,1181,1366,1443])
 (.leaf [0,9,61,141,225,347,671,767,945,1148,1387,1551]))
 (.branch 36
 (.leaf [0,9,113,129,237,347,676,768,944,977,1189,1408])
 (.branch 37
 (.leaf [0,25,57,120,213,381,649,768,898,1031,1187,1475])
 (.leaf [0,10,72,177,189,361,662,766,948,966,1369]))))
 (.branch 41
 (.branch 39
 (.leaf [0,25,35,119,213,381,768,896,1031,1187,1194,1475])
 (.branch 40
 (.leaf [0,35,62,143,201,400,536,767,854,1155,1216,1386])
 (.leaf [0,35,150,224,319,409,766,858,1003,1122,1366])))
 (.branch 42
 (.leaf [0,57,71,186,188,338,397,626,765,967,1364])
 (.branch 43
 (.leaf [0,51,61,180,224,376,559,638,766,945,1119,1388])
 (.leaf [0,57,61,156,237,364,517,626,768,878,1143,1408])))))))
 (.branch 66
 (.branch 55
 (.branch 49
 (.branch 46
 (.branch 45
 (.leaf [0,35,87,138,236,321,407,766,879,1003,1122,1467])
 (.leaf [0,36,71,162,212,342,407,765,879,979,1195,1468]))
 (.branch 47
 (.leaf [0,35,62,128,249,380,768,899,1125,1361,1450,1533])
 (.branch 48
 (.leaf [0,35,62,128,249,380,768,899,1143,1279,1418,1488])
 (.leaf [0,35,87,116,237,381,768,878,976,1143,1457,1616]))))
 (.branch 52
 (.branch 50
 (.leaf [0,35,87,116,237,381,768,878,1023,1137,1467,1554])
 (.branch 51
 (.leaf [0,35,57,116,225,393,767,897,1030,1186,1215,1467])
 (.leaf [0,87,108,128,249,380,610,768,899,1019,1175,1467])))
 (.branch 53
 (.leaf [0,36,62,172,248,402,767,921,1155,1451])
 (.branch 54
 (.leaf [0,39,71,172,248,402,624,767,943,964,1451,1493])
 (.leaf [0,71,185,224,415,633,766,920,988,1450,1519])))))
 (.branch 60
 (.branch 57
 (.branch 56
 (.leaf [0,107,111,184,236,414,621,766,921,976,1119,1451])
 (.leaf [0,51,111,184,236,414,626,766,943,976,1119,1451]))
 (.branch 58
 (.leaf [0,57,71,136,249,366,612,768,920,987,1468,1517])
 (.branch 59
 (.leaf [0,51,99,184,236,414,626,766,944,979,1119,1409])
 (.leaf [0,57,97,125,213,355,649,768,898,1002,1179,1428]))))
 (.branch 63
 (.branch 61
 (.leaf [0,58,87,172,248,402,614,767,900,1002,1134,1467])
 (.branch 62
 (.leaf [0,12,61,130,239,371,593,647,766,1136,1409,1509])
 (.leaf [0,9,111,131,239,407,590,616,766,976,1129,1451])))
 (.branch 64
 (.leaf [0,11,97,119,250,383,592,640,768,967,1153,1429])
 (.branch 65
 (.leaf [0,9,71,167,203,409,595,614,765,979,1369])
 (.leaf [0,28,35,143,204,397,593,767,854,1007,1163,1216]))))))
 (.branch 77
 (.branch 71
 (.branch 68
 (.branch 67
 (.leaf [0,10,36,120,251,396,590,767,856,1022,1173,1573])
 (.leaf [0,31,74,120,204,401,581,658,767,856,1022,1558]))
 (.branch 69
 (.leaf [0,31,71,155,193,413,558,614,765,991,1366])
 (.branch 70
 (.leaf [0,31,35,119,203,384,765,1029,1145,1366,1441])
 (.leaf [0,57,71,121,240,375,586,624,768,919,997,1538]))))
 (.branch 74
 (.branch 72
 (.leaf [0,35,72,119,216,399,586,768,896,1021,1192,1559])
 (.branch 73
 (.leaf [0,35,107,131,216,411,585,768,875,1033,1134,1558])
 (.leaf [0,19,71,157,252,375,589,609,768,920,997,1517])))
 (.branch 75
 (.leaf [0,35,54,116,233,389,767,876,1025,1146,1363,1558])
 (.branch 76
 (.leaf [0,71,152,257,413,609,768,920,988,1363,1517])
 (.leaf [0,35,111,150,222,404,765,1000,1121,1366,1430])))))
 (.branch 83
 (.branch 80
 (.branch 78
 (.leaf [0,57,64,128,257,413,613,768,920,1170,1364])
 (.branch 79
 (.leaf [0,1,15,257,261,558,613,768,920,990,1170,1360])
 (.leaf [0,35,111,116,258,338,395,767,857,964,1131,1451])))
 (.branch 81
 (.leaf [0,51,61,181,244,356,580,626,766,943,1119,1388])
 (.branch 82
 (.leaf [0,57,71,116,258,338,395,624,767,964,1451,1493])
 (.leaf [0,35,116,259,339,384,768,878,1026,1146,1363]))))
 (.branch 86
 (.branch 84
 (.leaf [0,35,84,116,259,339,384,768,881,1023,1122,1556])
 (.branch 85
 (.leaf [0,35,72,128,247,341,385,768,902,1011,1196,1559])
 (.leaf [0,57,71,152,222,319,408,614,765,991,1366])))
 (.branch 87
 (.leaf [0,1,35,257,264,348,579,768,899,1014,1146,1360])
 (.branch 88
 (.leaf [0,1,54,233,286,372,583,613,767,1027,1158,1363])
 (.leaf [0,32,73,142,235,343,348,674,767,1002,1363]))))))))
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

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0348

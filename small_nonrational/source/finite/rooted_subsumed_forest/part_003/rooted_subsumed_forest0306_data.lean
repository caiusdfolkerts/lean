module
prelude
public import RootedSixBase02GrowthCacheData
public import RootedSixBase02FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification
public import RootedSubsumedForest0306Packed000
public import RootedSubsumedForest0306Packed001

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0306
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 8084
abbrev nodeCount : Nat := 11719
abbrev leafCount : Nat := 119
def widths : PackedRawNatGrowth.Widths := ⟨13,14,6,7⟩
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
(.branch 59
 (.branch 29
 (.branch 14
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf [0,1,57,175,330,530,559,944,1058,1068,6967])
 (.branch 2
 (.leaf [0,15,57,151,176,330,530,944,1058,1068,6967])
 (.leaf [0,1,57,283,332,341,527,641,945,1053,1279,6192])))
 (.branch 5
 (.branch 4
 (.leaf [0,57,71,163,215,331,334,530,623,926,1014,6578])
 (.leaf [0,1,60,199,330,528,665,935,1017,1321,5473]))
 (.branch 6
 (.leaf [0,3,57,238,331,407,439,527,644,994,5485])
 (.leaf [0,3,57,331,334,527,578,644,994,1242,6212]))))
 (.branch 10
 (.branch 8
 (.leaf [0,2,60,223,331,529,599,681,7343])
 (.branch 9
 (.leaf [0,57,93,102,223,331,527,683,1001,1129,6563])
 (.leaf [0,29,57,132,239,330,419,528,656,993,5451])))
 (.branch 12
 (.branch 11
 (.leaf [0,7,61,331,494,530,679,1041,5741])
 (.leaf [0,57,93,102,223,331,527,641,857,1312,7339]))
 (.branch 13
 (.leaf [0,27,59,176,330,392,530,667,1017,1231,5725])
 (.leaf [0,56,60,138,235,332,528,669,7341])))))
 (.branch 21
 (.branch 17
 (.branch 15
 (.leaf [0,1,31,187,330,528,684,903,1037,1107,6571])
 (.branch 16
 (.leaf [0,1,31,199,330,528,665,857,882,1333,7285])
 (.leaf [0,1,90,199,330,529,578,881,993,1242,6979])))
 (.branch 19
 (.branch 18
 (.leaf [0,1,101,175,330,530,556,923,1058,1065,6967])
 (.leaf [0,1,101,175,330,529,535,654,924,1334,7229]))
 (.branch 20
 (.leaf [0,3,87,235,332,527,578,641,881,1376,7357])
 (.leaf [0,15,143,188,330,505,528,903,1045,1107,6963]))))
 (.branch 25
 (.branch 23
 (.branch 22
 (.leaf [0,15,131,224,331,504,527,641,882,1312,7339])
 (.leaf [0,6,74,151,331,530,944,1058,6967]))
 (.branch 24
 (.leaf [0,12,37,102,241,333,401,527,905,1018,5929])
 (.leaf [0,22,38,150,240,330,380,528,906,993,5911])))
 (.branch 27
 (.branch 26
 (.leaf [0,8,90,150,333,528,944,1057,6955])
 (.leaf [0,5,41,115,330,529,672,924,1049,1086,6577]))
 (.branch 28
 (.leaf [0,7,77,163,332,530,659,922,1014,1065,6559])
 (.leaf [0,5,50,103,330,528,631,858,903,1119,7319]))))))
 (.branch 44
 (.branch 36
 (.branch 32
 (.branch 30
 (.leaf [0,5,41,115,330,529,654,858,924,1334,7229])
 (.branch 31
 (.leaf [0,6,32,333,439,527,620,869,926,1018,5727])
 (.leaf [0,71,83,151,211,331,530,682,855,901,7291])))
 (.branch 34
 (.branch 33
 (.leaf [0,71,83,151,211,331,530,635,901,1014,6579])
 (.leaf [0,6,32,129,259,333,529,655,925,1054,5848]))
 (.branch 35
 (.leaf [0,16,54,103,332,528,668,883,1030,1247,6160])
 (.leaf [0,16,84,138,330,528,668,873,885,993,6154]))))
 (.branch 40
 (.branch 38
 (.branch 37
 (.leaf [0,1,5,332,346,530,553,643,946,1053,5746])
 (.leaf [0,1,15,195,331,530,577,679,904,1041,5774]))
 (.branch 39
 (.leaf [0,1,15,331,530,577,679,904,1041,1253,6052])
 (.leaf [0,126,222,333,527,660,923,1001,1127,6562])))
 (.branch 42
 (.branch 41
 (.leaf [0,53,101,138,186,332,528,945,1045,1106,6857])
 (.leaf [0,5,21,331,530,593,643,947,1041,1231,5541]))
 (.branch 43
 (.leaf [0,5,101,332,419,528,570,619,948,1030,5649])
 (.leaf [0,5,21,331,352,530,643,947,1041,1231,5636])))))
 (.branch 51
 (.branch 47
 (.branch 45
 (.leaf [0,53,101,114,210,332,527,617,924,1290,7335])
 (.branch 46
 (.leaf [0,126,234,333,527,629,856,902,1270,7336])
 (.leaf [0,15,21,221,330,530,679,905,1017,1234,5696])))
 (.branch 49
 (.branch 48
 (.leaf [0,16,84,176,330,516,530,667,926,1017,5739])
 (.leaf [0,6,34,153,333,482,529,655,946,1054]))
 (.branch 50
 (.leaf [0,42,71,151,174,331,530,682,862,901,7291])
 (.leaf [0,26,31,208,332,528,619,883,1030,1237,5655]))))
 (.branch 55
 (.branch 53
 (.branch 52
 (.leaf [0,18,86,151,213,332,530,667,946,1053])
 (.leaf [0,4,83,332,390,528,560,619,883,1030,6168]))
 (.branch 54
 (.leaf [0,53,94,138,186,332,528,880,1045,1111,6857])
 (.leaf [0,6,90,153,333,482,528,652,944,1054])))
 (.branch 57
 (.branch 56
 (.leaf [0,21,163,191,331,337,530,624,947,1038,6580])
 (.leaf [0,5,101,117,332,419,527,616,924,1290,7335]))
 (.branch 58
 (.leaf [0,5,87,129,333,461,527,628,902,1377,7355])
 (.leaf [0,21,83,163,188,331,337,530,947,1046,6966])))))))
 (.branch 89
 (.branch 74
 (.branch 66
 (.branch 62
 (.branch 60
 (.leaf [0,1,24,178,332,341,530,559,946,1058,6967])
 (.branch 61
 (.leaf [0,31,126,234,333,528,657,860,904,7340])
 (.leaf [0,9,15,127,211,331,530,682,860,904,7345])))
 (.branch 64
 (.branch 63
 (.leaf [0,15,42,151,179,330,530,682,862,905,7291])
 (.leaf [0,21,163,191,331,337,530,646,856,947,7236]))
 (.branch 65
 (.leaf [0,14,15,128,212,331,507,530,682,904,7345])
 (.leaf [0,63,101,138,237,333,376,528,657,904,7340]))))
 (.branch 70
 (.branch 68
 (.branch 67
 (.leaf [0,15,16,167,224,331,508,529,681,883,7343])
 (.leaf [0,1,101,189,332,335,530,553,646,946,7290]))
 (.branch 69
 (.leaf [0,5,101,103,330,530,598,682,691,905,7291])
 (.leaf [0,53,101,114,210,332,530,556,670,925,7344])))
 (.branch 72
 (.branch 71
 (.leaf [0,21,140,191,331,505,530,576,646,947,7236])
 (.leaf [0,17,50,103,202,333,528,681,860,904,7315]))
 (.branch 73
 (.leaf [0,9,48,115,225,333,359,529,617,925,1377,7353])
 (.leaf [0,18,91,151,213,332,530,666,951,1030])))))
 (.branch 81
 (.branch 77
 (.branch 75
 (.leaf [0,16,68,163,188,330,530,929,1067,1326,6985])
 (.branch 76
 (.leaf [0,15,95,115,177,331,529,888,1057,1090,6911])
 (.leaf [0,5,71,103,330,530,598,682,694,908,7345])))
 (.branch 79
 (.branch 78
 (.leaf [0,53,138,186,332,530,555,642,951,1294,7172])
 (.leaf [0,21,71,104,211,330,530,598,682,908,7345]))
 (.branch 80
 (.leaf [0,63,102,225,333,398,527,929,1009,1127,6801])
 (.leaf [0,1,201,333,356,529,532,630,951,1273,7226]))))
 (.branch 85
 (.branch 83
 (.branch 82
 (.leaf [0,63,114,237,333,397,527,629,908,1270,7336])
 (.leaf [0,1,15,236,271,332,402,527,641,887,1291,7338]))
 (.branch 84
 (.leaf [0,1,31,236,268,332,381,528,665,888,1293,7284])
 (.leaf [0,9,53,139,201,333,358,529,630,951,1273,7226])))
 (.branch 87
 (.branch 86
 (.leaf [0,9,27,117,225,333,400,527,617,929,1269,7334])
 (.leaf [0,1,68,201,333,377,528,533,619,952,6377]))
 (.branch 88
 (.leaf [0,1,93,175,330,530,666,934,993,1321,5413])
 (.leaf [0,3,84,186,332,530,643,957,1041,1064,5419]))))))
 (.branch 104
 (.branch 96
 (.branch 92
 (.branch 90
 (.leaf [0,18,37,114,212,331,527,731,1018,1133,6305])
 (.branch 91
 (.leaf [0,16,84,103,189,332,528,619,1042,1114,6309])
 (.leaf [0,15,72,151,176,330,530,667,1053,1240,6348])))
 (.branch 94
 (.branch 93
 (.leaf [0,5,154,259,333,530,631,837,1051,5842])
 (.leaf [0,83,154,211,333,439,530,635,1015,6579]))
 (.branch 95
 (.leaf [0,2,58,174,527,533,640,1056,1237,1312,6500])
 (.leaf [0,16,61,103,189,528,619,975,1042,1240,6508]))))
 (.branch 100
 (.branch 98
 (.branch 97
 (.leaf [0,57,93,102,223,331,677,861,1044,1335,7130])
 (.leaf [0,3,57,235,527,567,611,644,994,1234,6501]))
 (.branch 99
 (.leaf [0,57,95,102,211,331,682,863,1058,1061,7134])
 (.leaf [0,71,95,139,174,331,646,863,880,1022,7146])))
 (.branch 102
 (.branch 101
 (.leaf [0,15,63,127,178,530,652,803,925,1050,1384,6500])
 (.leaf [0,15,95,139,179,330,646,863,884,1022,7146]))
 (.branch 103
 (.leaf [0,5,60,130,331,398,445,643,1034,1228,7145])
 (.leaf [0,27,59,142,176,330,378,654,1048,1098,1363,7144])))))
 (.branch 111
 (.branch 107
 (.branch 105
 (.leaf [0,3,87,241,333,397,686,901,1013,1368,7137])
 (.branch 106
 (.leaf [0,3,71,184,265,331,399,630,901,1014,1364,7144])
 (.leaf [0,1,63,205,333,356,650,946,1049,1364,7128])))
 (.branch 109
 (.branch 108
 (.leaf [0,2,85,174,331,628,1055,1090,1311,7127])
 (.leaf [0,5,50,130,333,440,619,860,1036,1144,7147]))
 (.branch 110
 (.leaf [0,21,95,107,211,330,682,863,1058,1065,7134])
 (.leaf [0,1,175,530,556,660,854,1051,1234,6496]))))
 (.branch 115
 (.branch 113
 (.branch 112
 (.leaf [0,5,109,333,398,443,551,630,1015,1364,7144])
 (.leaf [0,1,183,333,377,459,535,654,1039,1363,7144]))
 (.branch 114
 (.leaf [0,1,5,333,380,433,500,616,1039,1365,7132])
 (.leaf [0,1,27,193,333,359,484,638,1051,1364,7132])))
 (.branch 117
 (.branch 116
 (.leaf [0,5,77,123,333,396,440,630,1039,1370,7144])
 (.leaf [0,3,77,216,333,400,439,661,1015,1368,7144]))
 (.branch 118
 (.leaf [0,5,47,111,333,375,461,628,1051,1370,7140])
 (.leaf [0,1,37,177,333,359,482,1051,1154,1385,7132]))))))))
def rawLeaves := leafTable.get

def leaves : Fin leafCount → List (Fin cellCount) := decodedLeaves rawLeaves
def quota : Nat → Nat
  | 0 => 1
  | 1 => 2
  | 2 => 5
  | 3 => 3
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
    Papers.RationalityTen.RootedCaches.RootedSixBase02.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixBase02.badMasks
    Papers.RationalityTen.RootedCaches.RootedSixBase02.kindMasks Papers.RationalityTen.RootedCaches.RootedSixBase02.keys Papers.RationalityTen.RootedCaches.RootedSixBase02.fastKind quota
    Papers.RationalityTen.FacetUniverses.RootedSixBase02.Generators.FastWords.rawMaps rawLeaves codes counters i
theorem nodeTest_sound (i : Nat) (h : nodeTest i = true) :
    nodeBounds cellCount 1024 48 leafCount nodeCount (rawNodes i) = true ∧
      SubsumedRawGrowth.nodeCheck Papers.RationalityTen.RootedCaches.RootedSixBase02.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixBase02.badMasks
        Papers.RationalityTen.RootedCaches.RootedSixBase02.kindMasks Papers.RationalityTen.RootedCaches.RootedSixBase02.keys Papers.RationalityTen.RootedCaches.RootedSixBase02.fastKind quota
        Papers.RationalityTen.FacetUniverses.RootedSixBase02.Generators.FastWords.rawMaps rawLeaves rawNodes i = true :=
  SubsumedCounterReplay.check_sound widths cellCount 1024 48 leafCount nodeCount
    Papers.RationalityTen.RootedCaches.RootedSixBase02.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixBase02.badMasks
    Papers.RationalityTen.RootedCaches.RootedSixBase02.kindMasks Papers.RationalityTen.RootedCaches.RootedSixBase02.keys Papers.RationalityTen.RootedCaches.RootedSixBase02.fastKind quota
    Papers.RationalityTen.FacetUniverses.RootedSixBase02.Generators.FastWords.rawMaps rawLeaves codes counters i h
def leafTest (i : Nat) : Bool :=
  listBounds cellCount (rawLeaves i) &&
    (WitnessGrowthDAG.closedCheck FacetUniverses.RootedSixBase02.ridgeList
      ((rawLeaves i).map (Fin.ofNat cellCount)) &&
      decide (((rawLeaves i).map (Fin.ofNat cellCount)).Nodup))

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0306

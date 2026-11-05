module
prelude
public import RootedSixBase02GrowthCacheData
public import RootedSixBase02FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification
public import RootedSubsumedForest0305Packed000
public import RootedSubsumedForest0305Packed001

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0305
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 8084
abbrev nodeCount : Nat := 9750
abbrev leafCount : Nat := 93
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
(.branch 46
 (.branch 23
 (.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf [0,1,71,187,330,530,577,679,902,1041,1236])
 (.leaf [0,31,85,150,234,333,527,632,862,905,1018]))
 (.branch 3
 (.leaf [0,6,34,153,333,482,529,655,946,1054])
 (.branch 4
 (.leaf [0,18,86,151,213,332,530,667,946,1053])
 (.leaf [0,6,90,153,333,482,528,652,944,1054]))))
 (.branch 8
 (.branch 6
 (.leaf [0,18,91,151,213,332,530,666,951,1030])
 (.branch 7
 (.leaf [0,5,21,166,253,333,485,530,619,838,1039])
 (.leaf [0,5,30,154,252,333,467,530,631,837,1051])))
 (.branch 9
 (.leaf [0,28,48,107,226,330,461,527,680,862,1004])
 (.branch 10
 (.leaf [0,23,53,130,175,333,530,655,816,1051,1237])
 (.leaf [0,53,83,154,174,333,482,530,631,837,1051])))))
 (.branch 17
 (.branch 14
 (.branch 12
 (.leaf [0,27,98,143,191,331,441,528,640,776,1040])
 (.branch 13
 (.leaf [0,1,178,332,338,483,667,857,940,1053,4795])
 (.leaf [0,1,213,269,332,338,667,940,1053,1229,4795])))
 (.branch 15
 (.leaf [0,2,55,174,331,534,643,959,1041,1231,4843])
 (.branch 16
 (.leaf [0,5,34,106,331,441,643,860,959,1041,4843])
 (.leaf [0,6,39,151,331,755,958,1029,4842]))))
 (.branch 20
 (.branch 18
 (.leaf [0,5,9,139,331,441,643,860,959,1041,4843])
 (.branch 19
 (.leaf [0,53,54,138,186,332,643,961,1053,1230,4827])
 (.leaf [0,1,31,201,356,528,619,958,1030,1234,3725])))
 (.branch 21
 (.leaf [0,1,9,225,359,527,620,937,1006,1236,3725])
 (.branch 22
 (.leaf [0,15,27,143,188,528,656,919,1042,1238,3676])
 (.leaf [0,15,63,115,177,529,631,961,1054,1235,3708]))))))
 (.branch 34
 (.branch 28
 (.branch 25
 (.branch 24
 (.leaf [0,1,175,530,556,667,942,1053,1236,3660])
 (.leaf [0,83,151,174,331,631,861,958,1029,4842]))
 (.branch 26
 (.leaf [0,6,86,139,529,655,961,1054,3708])
 (.branch 27
 (.leaf [0,5,21,165,253,333,485,619,962,1042,4810])
 (.leaf [0,5,30,140,294,331,445,643,959,1041,4843]))))
 (.branch 31
 (.branch 29
 (.leaf [0,22,54,117,175,332,667,940,1053,1236,4795])
 (.branch 30
 (.leaf [0,53,83,165,186,333,481,619,962,1042,4810])
 (.leaf [0,3,71,212,331,399,684,901,1017,1234,4839])))
 (.branch 32
 (.leaf [0,1,63,201,333,356,636,946,1054,1230,4775])
 (.branch 33
 (.leaf [0,2,65,211,331,531,684,904,1041,1229,4839])
 (.leaf [0,5,53,103,330,610,630,905,1014,1364,4837])))))
 (.branch 40
 (.branch 37
 (.branch 35
 (.leaf [0,6,48,102,331,589,617,904,1038,1370,4837])
 (.branch 36
 (.leaf [0,5,162,268,529,619,839,943,1026,1100,3683])
 (.leaf [0,15,65,115,177,331,630,909,994,1311,4830])))
 (.branch 38
 (.leaf [0,1,66,187,330,537,653,929,1005,1334,4814])
 (.branch 39
 (.leaf [0,1,177,331,357,628,944,1029,1232,1313,4782])
 (.leaf [0,1,77,175,330,556,666,937,1002,1370,4829]))))
 (.branch 43
 (.branch 41
 (.leaf [0,1,87,187,330,577,678,916,1004,1370,4813])
 (.branch 42
 (.leaf [0,12,67,102,235,527,644,863,896,1108,3703])
 (.leaf [0,6,100,139,331,654,959,1038,4828])))
 (.branch 44
 (.leaf [0,9,83,153,189,508,528,619,958,1030,3734])
 (.branch 45
 (.leaf [0,17,83,107,213,510,527,620,937,1006,3734])
 (.leaf [0,11,83,162,175,529,655,863,939,1005,3686])))))))
 (.branch 69
 (.branch 57
 (.branch 51
 (.branch 48
 (.branch 47
 (.leaf [0,7,77,140,331,418,627,959,1038,1369,4828])
 (.leaf [0,7,87,116,330,462,676,895,1016,1371,4797]))
 (.branch 49
 (.leaf [0,5,21,163,253,530,619,838,962,1038,3702])
 (.branch 50
 (.leaf [0,58,84,114,210,332,667,864,1020,1065,4786])
 (.leaf [0,1,31,189,392,528,619,904,1042,1236,3737]))))
 (.branch 54
 (.branch 52
 (.leaf [0,2,58,225,372,529,531,655,1005,1238,3688])
 (.branch 53
 (.leaf [0,5,97,127,330,630,856,902,990,1332,4835])
 (.leaf [0,5,21,115,371,529,631,925,1054,1236,3721])))
 (.branch 55
 (.leaf [0,57,93,103,187,330,678,861,1005,1335,4818])
 (.branch 56
 (.leaf [0,1,31,187,330,678,861,882,1005,1335,4818])
 (.leaf [0,5,152,289,331,444,630,901,994,1311,4835])))))
 (.branch 63
 (.branch 60
 (.branch 58
 (.leaf [0,5,41,127,330,654,860,902,993,1332,4835])
 (.branch 59
 (.leaf [0,6,55,102,331,678,690,882,1029,1314,4786])
 (.leaf [0,53,54,138,186,332,642,880,1006,1291,4818])))
 (.branch 61
 (.leaf [0,127,175,330,654,860,902,993,1332,4835])
 (.branch 62
 (.leaf [0,15,55,115,177,331,642,888,994,1312,4834])
 (.leaf [0,21,22,152,239,331,509,627,901,994,1311,4835]))))
 (.branch 66
 (.branch 64
 (.leaf [0,21,83,128,227,330,504,652,923,1005,1334,4819])
 (.branch 65
 (.leaf [0,27,101,104,214,330,462,676,903,1017,1337,4802])
 (.leaf [0,27,28,141,226,332,468,639,880,1006,1291,4818])))
 (.branch 67
 (.leaf [0,21,104,223,330,675,882,1005,1235,1335,4818])
 (.branch 68
 (.leaf [0,83,165,210,333,460,615,922,1018,1269,4803])
 (.leaf [0,53,102,211,331,676,903,1041,1229,1316,4770]))))))
 (.branch 81
 (.branch 75
 (.branch 72
 (.branch 70
 (.leaf [0,15,67,151,179,330,630,862,905,1311,4835])
 (.branch 71
 (.leaf [0,28,58,107,225,391,527,620,1006,1236,3736])
 (.leaf [0,3,98,215,333,400,439,615,850,1015,4839])))
 (.branch 73
 (.leaf [0,2,5,252,333,401,467,631,852,1051,4823])
 (.branch 74
 (.leaf [0,5,34,106,333,398,446,619,850,1039,4839])
 (.leaf [0,6,100,157,333,482,652,1051,4821]))))
 (.branch 78
 (.branch 76
 (.leaf [0,6,29,169,249,333,442,654,1039,1363,4837])
 (.branch 77
 (.leaf [0,28,83,157,176,333,461,652,1051,1363,4821])
 (.leaf [0,6,48,169,246,333,485,617,1039,1369,4837])))
 (.branch 79
 (.leaf [0,21,53,166,191,508,530,619,838,1048,3715])
 (.branch 80
 (.leaf [0,27,47,121,178,332,483,664,1052,1369,4773])
 (.leaf [0,6,20,154,332,487,667,1056,4831])))))
 (.branch 87
 (.branch 84
 (.branch 82
 (.leaf [0,1,27,178,333,383,488,535,655,1055,4830])
 (.branch 83
 (.leaf [0,1,66,190,333,383,481,537,656,1043,4814])
 (.leaf [0,22,28,154,176,332,379,667,1056,1236,4831])))
 (.branch 85
 (.leaf [0,21,65,162,224,330,359,680,1008,1236,4767])
 (.branch 86
 (.leaf [0,1,21,187,331,357,577,679,1044,1236,4815])
 (.leaf [0,1,31,190,331,339,483,679,861,1044,4818]))))
 (.branch 90
 (.branch 88
 (.leaf [0,4,39,234,333,1055,4835])
 (.branch 89
 (.leaf [0,6,56,154,333,482,655,1055,4835])
 (.leaf [0,5,21,159,248,530,631,837,1051,1235,3721])))
 (.branch 91
 (.leaf [0,83,154,174,333,482,631,861,1055,4835])
 (.branch 92
 (.leaf [0,27,118,178,332,483,667,861,1056,4834])
 (.leaf [0,22,68,118,175,332,666,861,1064,1333,4834]))))))))
def rawLeaves := leafTable.get

def leaves : Fin leafCount → List (Fin cellCount) := decodedLeaves rawLeaves
def quota : Nat → Nat
  | 0 => 1
  | 1 => 2
  | 2 => 6
  | 3 => 2
  | 4 => 0
  | 5 => 0
  | 6 => 1
  | 7 => 0
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

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0305

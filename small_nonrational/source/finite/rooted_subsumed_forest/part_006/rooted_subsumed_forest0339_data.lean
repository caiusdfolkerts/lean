module
prelude
public import RootedSixBase00GrowthCacheData
public import RootedSixBase00FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification
public import RootedSubsumedForest0339Packed000
public import RootedSubsumedForest0339Packed001
public import RootedSubsumedForest0339Packed002

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0339
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 21976
abbrev nodeCount : Nat := 14699
abbrev leafCount : Nat := 29
def widths : PackedRawNatGrowth.Widths := ⟨15,14,7,5⟩
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
(.branch 14
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf [0,5,76,151,381,659,795,1113,1435,1523,1617])
 (.branch 2
 (.leaf [0,5,76,151,381,659,795,1103,1197,1532,1809])
 (.leaf [0,2,97,259,415,675,839,1112,1268])))
 (.branch 5
 (.branch 4
 (.leaf [0,1,46,235,391,651,926,1010,1112,1268,1505])
 (.leaf [0,1,46,203,371,627,1108,1255,1451,1520,1716]))
 (.branch 6
 (.leaf [0,2,45,236,312,403,597,628,1108,1231,1445,1496])
 (.leaf [0,1,15,203,626,816,1077,1233,1529,1715,1824]))))
 (.branch 10
 (.branch 8
 (.leaf [0,2,127,216,350,363,612,674,846,1057,1206,1536,1770])
 (.branch 9
 (.leaf [0,1,5,371,624,792,1111,1252,1451,1534,1825])
 (.leaf [0,15,76,147,271,572,627,833,1026,1077,1395,1523])))
 (.branch 12
 (.branch 11
 (.leaf [0,4,111,256,405,513,683,837,1064,1220,1470,1820])
 (.leaf [0,1,5,359,656,812,1084,1266,1450,1531,1715]))
 (.branch 13
 (.leaf [0,2,45,224,291,415,595,680,972,1104,1224,1480,1840])
 (.leaf [0,2,5,276,415,551,680,798,1016,1068,1260,1488,1840])))))
 (.branch 21
 (.branch 17
 (.branch 15
 (.leaf [0,35,46,142,246,402,993,1014,1099,1228,1444,1522])
 (.branch 16
 (.leaf [0,35,46,142,260,354,425,941,1115,1216,1520,1811])
 (.leaf [0,35,121,185,241,424,598,732,781,1114,1231,1505,1790])))
 (.branch 19
 (.branch 18
 (.leaf [0,15,128,143,203,690,834,1025,1053,1271,1376,1524])
 (.leaf [0,15,128,131,215,678,846,1025,1091,1132,1259,1536]))
 (.branch 20
 (.leaf [0,15,85,131,215,678,846,1030,1057,1259,1536,1850])
 (.leaf [0,15,31,172,220,453,669,801,1075,1252,1498,1823]))))
 (.branch 25
 (.branch 23
 (.branch 22
 (.leaf [0,32,91,160,256,362,657,837,1087,1216,1510,1823])
 (.leaf [0,31,35,133,273,332,401,805,1091,1259,1309,1527,1839]))
 (.branch 24
 (.leaf [0,32,121,200,209,331,412,637,790,1102,1263,1502,1839])
 (.leaf [0,9,116,149,253,422,609,646,785,1092,1263,1475,1850])))
 (.branch 27
 (.branch 26
 (.leaf [0,9,125,145,257,421,604,630,838,1058,1211,1531,1808])
 (.leaf [0,15,125,159,258,550,642,822,1028,1045,1223,1512]))
 (.branch 28
 (.leaf [0,31,126,147,243,365,654,834,1028,1055,1235,1524])
 (.leaf [0,35,45,152,224,394,1096,1231,1452,1496,1717]))))))
def rawLeaves := leafTable.get

def leaves : Fin leafCount → List (Fin cellCount) := decodedLeaves rawLeaves
def quota : Nat → Nat
  | 0 => 1
  | 1 => 2
  | 2 => 4
  | 3 => 6
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

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0339

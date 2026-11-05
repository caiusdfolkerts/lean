module
prelude
public import RootedSixBase01GrowthCacheData
public import RootedSixBase01FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification
public import RootedSubsumedForest0311Packed000
public import RootedSubsumedForest0311Packed001
public import RootedSubsumedForest0311Packed002

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0311
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 15246
abbrev nodeCount : Nat := 13230
abbrev leafCount : Nat := 42
def widths : PackedRawNatGrowth.Widths := ⟨14,14,6,6⟩
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
(.branch 21
 (.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf [0,7,72,185,415,662,766,838,1015])
 (.leaf [0,16,37,153,237,768,919,1005,1179,1466]))
 (.branch 3
 (.leaf [0,36,62,172,248,402,767,921,1155,1451])
 (.branch 4
 (.leaf [0,35,71,119,203,387,587,765,1311,1441,15156])
 (.leaf [0,37,101,156,239,411,584,766,853,1138,1421,15153]))))
 (.branch 7
 (.branch 6
 (.leaf [0,35,51,150,234,409,766,1003,1122,1368,14717])
 (.leaf [0,71,155,196,413,614,765,991,1368,14844]))
 (.branch 8
 (.leaf [0,35,51,131,197,413,766,1015,1122,1369,14840])
 (.branch 9
 (.leaf [0,40,72,181,244,364,613,766,948,966,14848])
 (.leaf [0,52,72,172,256,611,767,943,1009,1495,14968])))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf [0,71,81,172,256,609,767,921,1009,1499,14968])
 (.leaf [0,35,51,150,412,766,787,1003,1122,1366,14902]))
 (.branch 13
 (.leaf [0,71,174,412,614,765,785,979,1364,14908])
 (.branch 14
 (.leaf [0,31,74,130,226,351,678,1029,1054,15242])
 (.leaf [0,31,74,132,195,382,678,789,1029,15242]))))
 (.branch 18
 (.branch 16
 (.leaf [0,35,57,116,233,389,911,1029,1146,1366,15242])
 (.branch 17
 (.leaf [0,6,35,138,277,385,890,1017,1146,1367,15238])
 (.leaf [0,1,107,221,377,610,910,1028,1158,1366,15243])))
 (.branch 19
 (.leaf [0,1,57,209,365,613,932,1029,1170,1364,15242])
 (.branch 20
 (.leaf [0,88,111,142,250,363,585,665,985,1120,1463,15239])
 (.leaf [0,35,62,119,204,383,587,911,1125,1462,1533,15242]))))))
 (.branch 31
 (.branch 26
 (.branch 23
 (.branch 22
 (.leaf [0,36,61,157,202,349,587,932,1153,1229,1441,15242])
 (.leaf [0,36,61,118,228,359,587,932,1153,1229,1441,15242]))
 (.branch 24
 (.leaf [0,35,71,133,226,351,587,911,973,1462,1514,15242])
 (.branch 25
 (.leaf [0,35,111,145,250,363,585,889,985,1119,1463,15239])
 (.leaf [0,6,71,173,403,633,936,988,1466,1540,15234]))))
 (.branch 28
 (.branch 27
 (.leaf [0,31,35,119,207,401,581,1027,1137,1364,15228])
 (.leaf [0,9,63,143,231,409,594,613,1161,1368,15236]))
 (.branch 29
 (.leaf [0,36,71,155,243,407,584,980,1195,1444,1529,15240])
 (.branch 30
 (.leaf [0,71,87,154,255,395,584,621,968,1423,1550,15244])
 (.leaf [0,9,71,131,243,407,591,612,980,1444,1529,15240])))))
 (.branch 36
 (.branch 33
 (.branch 32
 (.leaf [0,35,111,145,254,363,585,875,985,1119,1570,15245])
 (.leaf [0,16,35,145,242,429,607,896,1001,1134,1572,15241]))
 (.branch 34
 (.leaf [0,87,112,130,255,375,585,645,997,1120,1571,15244])
 (.branch 35
 (.leaf [0,10,112,119,255,399,591,624,1021,1121,1550,15244])
 (.leaf [0,19,35,133,255,399,590,854,1021,1122,1571,15244]))))
 (.branch 39
 (.branch 37
 (.leaf [0,9,107,131,243,411,590,612,1033,1134,1573,15240])
 (.branch 38
 (.leaf [0,35,62,145,242,348,586,896,1139,1292,1572,15241])
 (.leaf [0,5,36,162,275,361,806,990,1173,1367,15240])))
 (.branch 40
 (.leaf [0,1,57,197,353,625,848,1014,1185,1364,15244])
 (.branch 41
 (.leaf [0,35,57,116,233,389,829,1026,1149,1366,15232])
 (.leaf [0,1,35,221,377,851,901,1010,1146,1574,15237])))))))
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
  | 7 => 0
  | 8 => 0
  | 9 => 1
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

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0311

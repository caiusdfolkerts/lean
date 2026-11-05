module
prelude
public import RootedSixBase01GrowthCacheData
public import RootedSixBase01FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification
public import RootedSubsumedForest0304Packed000
public import RootedSubsumedForest0304Packed001

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0304
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 15246
abbrev nodeCount : Nat := 12127
abbrev leafCount : Nat := 20
def widths : PackedRawNatGrowth.Widths := ⟨14,14,6,5⟩
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
(.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf [0,6,71,171,412,578,626,762,765,775,979])
 (.leaf [0,6,35,173,403,724,765,796,1028,1133,1440]))
 (.branch 3
 (.leaf [0,7,88,160,390,614,765,776,1017,1145,1420])
 (.branch 4
 (.leaf [0,7,72,185,415,662,766,838,1015])
 (.leaf [0,1,5,345,622,765,1017,1185,1365,1420,1550]))))
 (.branch 7
 (.branch 6
 (.leaf [0,5,71,174,296,412,557,614,765,979,1365])
 (.leaf [0,5,35,119,401,537,765,1028,1133,1365,1440]))
 (.branch 8
 (.leaf [0,45,71,184,236,414,626,765,948,979,1478])
 (.branch 9
 (.leaf [0,45,71,176,244,400,626,765,948,967,1369])
 (.leaf [0,16,52,175,247,638,767,819,983,1061,1139])))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf [0,2,16,225,666,767,934,1017,1178,1464])
 (.leaf [0,15,57,117,213,652,768,903,995,1151,1206]))
 (.branch 13
 (.leaf [0,16,60,153,237,676,768,1005,1189,1466])
 (.branch 14
 (.leaf [0,53,87,162,213,275,361,614,768,995,1151])
 (.leaf [0,36,100,160,249,390,768,920,1019,1175]))))
 (.branch 17
 (.branch 16
 (.leaf [0,51,61,176,220,376,650,765,947,1123,1368])
 (.leaf [0,59,62,129,197,353,676,766,882,1122,1248]))
 (.branch 18
 (.leaf [0,57,61,152,208,364,666,765,890,1147,1367])
 (.branch 19
 (.leaf [0,16,36,157,257,579,768,920,1019,1175])
 (.leaf [0,31,53,135,385,632,768,1011,1156,1545,1619,14496]))))))
def rawLeaves := leafTable.get

def leaves : Fin leafCount → List (Fin cellCount) := decodedLeaves rawLeaves
def quota : Nat → Nat
  | 0 => 1
  | 1 => 2
  | 2 => 3
  | 3 => 5
  | 4 => 0
  | 5 => 0
  | 6 => 0
  | 7 => 0
  | 8 => 1
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

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0304

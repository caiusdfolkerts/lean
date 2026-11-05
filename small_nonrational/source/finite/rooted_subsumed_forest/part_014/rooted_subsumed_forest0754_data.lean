module
prelude
public import RootedSixExtra03GrowthCacheData
public import RootedSixExtra03FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0754
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 3150
abbrev nodeCount : Nat := 2
abbrev leafCount : Nat := 1
def widths : PackedRawNatGrowth.Widths := ⟨12,1,7,1⟩
def blocks : Table PackedRawNatGrowth.Block :=
(.leaf ⟨0x3279d3079c0279b0079a387993479808797047963a795367940a7930679254791487902478f1878e5678d4a78c2678b1a78a5c789507882c78720786001800000076000100000079ac26f341,0x4000000000⟩)
def counterTable : Table Nat :=
(.leaf 0x80200000000000)
def codes (i : Nat) : Nat :=
  let b := blocks.get (i / 128)
  PackedRawNatGrowth.drop
    (PackedRawNatGrowth.take 32 (PackedRawNatGrowth.drop (32*(i%128)) b.offsets)) b.payload
def counters (i : Nat) : Nat :=
  PackedRawNatGrowth.take 55 (PackedRawNatGrowth.drop (55*(i%128)) (counterTable.get (i/128)))
def rawNodes (i : Nat) := PackedRawNatGrowth.decodeNode widths (codes i)

def leafTable : Table (List Nat) :=
(.leaf [])
def rawLeaves := leafTable.get

def leaves : Fin leafCount → List (Fin cellCount) := decodedLeaves rawLeaves
def quota : Nat → Nat
  | 0 => 1
  | 1 => 0
  | 2 => 8
  | 3 => 0
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
    Papers.RationalityTen.RootedCaches.RootedSixExtra03.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixExtra03.badMasks
    Papers.RationalityTen.RootedCaches.RootedSixExtra03.kindMasks Papers.RationalityTen.RootedCaches.RootedSixExtra03.keys Papers.RationalityTen.RootedCaches.RootedSixExtra03.fastKind quota
    Papers.RationalityTen.FacetUniverses.RootedSixExtra03.Generators.FastWords.rawMaps rawLeaves codes counters i
theorem nodeTest_sound (i : Nat) (h : nodeTest i = true) :
    nodeBounds cellCount 1024 96 leafCount nodeCount (rawNodes i) = true ∧
      SubsumedRawGrowth.nodeCheck Papers.RationalityTen.RootedCaches.RootedSixExtra03.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixExtra03.badMasks
        Papers.RationalityTen.RootedCaches.RootedSixExtra03.kindMasks Papers.RationalityTen.RootedCaches.RootedSixExtra03.keys Papers.RationalityTen.RootedCaches.RootedSixExtra03.fastKind quota
        Papers.RationalityTen.FacetUniverses.RootedSixExtra03.Generators.FastWords.rawMaps rawLeaves rawNodes i = true :=
  SubsumedCounterReplay.check_sound widths cellCount 1024 96 leafCount nodeCount
    Papers.RationalityTen.RootedCaches.RootedSixExtra03.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixExtra03.badMasks
    Papers.RationalityTen.RootedCaches.RootedSixExtra03.kindMasks Papers.RationalityTen.RootedCaches.RootedSixExtra03.keys Papers.RationalityTen.RootedCaches.RootedSixExtra03.fastKind quota
    Papers.RationalityTen.FacetUniverses.RootedSixExtra03.Generators.FastWords.rawMaps rawLeaves codes counters i h
def leafTest (i : Nat) : Bool :=
  listBounds cellCount (rawLeaves i) &&
    (WitnessGrowthDAG.closedCheck FacetUniverses.RootedSixExtra03.ridgeList
      ((rawLeaves i).map (Fin.ofNat cellCount)) &&
      decide (((rawLeaves i).map (Fin.ofNat cellCount)).Nodup))

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0754

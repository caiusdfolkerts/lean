module
prelude
public import RootedSixExtra02GrowthCacheData
public import RootedSixExtra02FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0762
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 6620
abbrev nodeCount : Nat := 1
abbrev leafCount : Nat := 1
def widths : PackedRawNatGrowth.Widths := ⟨13,1,6,1⟩
def blocks : Table PackedRawNatGrowth.Block :=
(.leaf ⟨0xec0001,0x0⟩)
def counterTable : Table Nat :=
(.leaf 0x1)
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
  | 2 => 7
  | 3 => 0
  | 4 => 0
  | 5 => 0
  | 6 => 0
  | 7 => 0
  | 8 => 0
  | 9 => 0
  | 10 => 2
  | _ => 0

def nodeTest (i : Nat) : Bool :=
  SubsumedCounterReplay.check widths cellCount 1024 48 leafCount nodeCount
    Papers.RationalityTen.RootedCaches.RootedSixExtra02.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixExtra02.badMasks
    Papers.RationalityTen.RootedCaches.RootedSixExtra02.kindMasks Papers.RationalityTen.RootedCaches.RootedSixExtra02.keys Papers.RationalityTen.RootedCaches.RootedSixExtra02.fastKind quota
    Papers.RationalityTen.FacetUniverses.RootedSixExtra02.Generators.FastWords.rawMaps rawLeaves codes counters i
theorem nodeTest_sound (i : Nat) (h : nodeTest i = true) :
    nodeBounds cellCount 1024 48 leafCount nodeCount (rawNodes i) = true ∧
      SubsumedRawGrowth.nodeCheck Papers.RationalityTen.RootedCaches.RootedSixExtra02.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixExtra02.badMasks
        Papers.RationalityTen.RootedCaches.RootedSixExtra02.kindMasks Papers.RationalityTen.RootedCaches.RootedSixExtra02.keys Papers.RationalityTen.RootedCaches.RootedSixExtra02.fastKind quota
        Papers.RationalityTen.FacetUniverses.RootedSixExtra02.Generators.FastWords.rawMaps rawLeaves rawNodes i = true :=
  SubsumedCounterReplay.check_sound widths cellCount 1024 48 leafCount nodeCount
    Papers.RationalityTen.RootedCaches.RootedSixExtra02.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixExtra02.badMasks
    Papers.RationalityTen.RootedCaches.RootedSixExtra02.kindMasks Papers.RationalityTen.RootedCaches.RootedSixExtra02.keys Papers.RationalityTen.RootedCaches.RootedSixExtra02.fastKind quota
    Papers.RationalityTen.FacetUniverses.RootedSixExtra02.Generators.FastWords.rawMaps rawLeaves codes counters i h
def leafTest (i : Nat) : Bool :=
  listBounds cellCount (rawLeaves i) &&
    (WitnessGrowthDAG.closedCheck FacetUniverses.RootedSixExtra02.ridgeList
      ((rawLeaves i).map (Fin.ofNat cellCount)) &&
      decide (((rawLeaves i).map (Fin.ofNat cellCount)).Nodup))

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0762

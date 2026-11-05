module
prelude
public import RootedSixExtra01GrowthCacheData
public import RootedSixExtra01FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0752
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 3150
abbrev nodeCount : Nat := 3
abbrev leafCount : Nat := 1
def widths : PackedRawNatGrowth.Widths := ⟨12,2,6,1⟩
def blocks : Table PackedRawNatGrowth.Block :=
(.leaf ⟨0x588d0188c0488b0088a11889098881088708886158850d884148830c88249881318804887f3087e4d87d3587c4c87b3487a598794187858877408760018000000ea000100000088cc2b118100000088ac4b1141,0x800000004000000000⟩)
def counterTable : Table Nat :=
(.leaf 0x4010000000000000200000000000)
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
  SubsumedCounterReplay.check widths cellCount 1024 48 leafCount nodeCount
    Papers.RationalityTen.RootedCaches.RootedSixExtra01.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixExtra01.badMasks
    Papers.RationalityTen.RootedCaches.RootedSixExtra01.kindMasks Papers.RationalityTen.RootedCaches.RootedSixExtra01.keys Papers.RationalityTen.RootedCaches.RootedSixExtra01.fastKind quota
    Papers.RationalityTen.FacetUniverses.RootedSixExtra01.Generators.FastWords.rawMaps rawLeaves codes counters i
theorem nodeTest_sound (i : Nat) (h : nodeTest i = true) :
    nodeBounds cellCount 1024 48 leafCount nodeCount (rawNodes i) = true ∧
      SubsumedRawGrowth.nodeCheck Papers.RationalityTen.RootedCaches.RootedSixExtra01.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixExtra01.badMasks
        Papers.RationalityTen.RootedCaches.RootedSixExtra01.kindMasks Papers.RationalityTen.RootedCaches.RootedSixExtra01.keys Papers.RationalityTen.RootedCaches.RootedSixExtra01.fastKind quota
        Papers.RationalityTen.FacetUniverses.RootedSixExtra01.Generators.FastWords.rawMaps rawLeaves rawNodes i = true :=
  SubsumedCounterReplay.check_sound widths cellCount 1024 48 leafCount nodeCount
    Papers.RationalityTen.RootedCaches.RootedSixExtra01.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixExtra01.badMasks
    Papers.RationalityTen.RootedCaches.RootedSixExtra01.kindMasks Papers.RationalityTen.RootedCaches.RootedSixExtra01.keys Papers.RationalityTen.RootedCaches.RootedSixExtra01.fastKind quota
    Papers.RationalityTen.FacetUniverses.RootedSixExtra01.Generators.FastWords.rawMaps rawLeaves codes counters i h
def leafTest (i : Nat) : Bool :=
  listBounds cellCount (rawLeaves i) &&
    (WitnessGrowthDAG.closedCheck FacetUniverses.RootedSixExtra01.ridgeList
      ((rawLeaves i).map (Fin.ofNat cellCount)) &&
      decide (((rawLeaves i).map (Fin.ofNat cellCount)).Nodup))

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0752

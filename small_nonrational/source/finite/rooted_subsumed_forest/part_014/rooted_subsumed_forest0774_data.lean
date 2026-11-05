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
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0774
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 6620
abbrev nodeCount : Nat := 8
abbrev leafCount : Nat := 1
def widths : PackedRawNatGrowth.Widths := ⟨13,3,6,1⟩
def blocks : Table PackedRawNatGrowth.Block :=
(.leaf ⟨0xceb13b1ac4cc3b12b2ec48e6b11b5ac44d3b10b8ec40eeb0fb7ac3cdbb0ebaec3956b0dc9ac3523b0cd4ec315eb0bcbac2d2bb0ad6ec2976b09d1ac2543b08dcec200030000000760000816c4435b0d0d2c2604b090c6c2201b0800030000001ddb08000200000000000fb615888000300000000000fb6158480003015892f3613a4d848616110058400014000000eed800001000000589309db02c48200000000000fb6158400003000000000017b6058400003,0x34f0000027c00000220000001c400000107000000b80000005c00000000⟩)
def counterTable : Table Nat :=
(.leaf 0x2008000000000040200000000000804000000000010040000000000201000000000000020000000000080400000000001)
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
  | 9 => 2
  | 10 => 0
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

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0774

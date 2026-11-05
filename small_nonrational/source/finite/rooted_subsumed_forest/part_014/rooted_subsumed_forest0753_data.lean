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
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0753
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 6620
abbrev nodeCount : Nat := 9
abbrev leafCount : Nat := 1
def widths : PackedRawNatGrowth.Widths := ⟨13,4,6,1⟩
def blocks : Table PackedRawNatGrowth.Block :=
(.leaf ⟨0x18774db2ee9a619d32cb3a618574bb2ae96611d2aca3a5183749b26e92609d22c93a4181747b22e8e601d1ac83a31a7745b8ee8a699d12e33a21a5743b8ae86691d0ae23a11a3741b86e82689d02e13a01a173fb82e7e681cfae039f1b773dbaee7a6d9cf2eb39e1b573bbaae766d1ceaea39d1b3739ba6e726c9ce2e939c1b1737ba2e6e6c1cdae839b247735d4ee6a919cd35339a245733d4ae66911ccb52399243731d46e62909cc35139824172fd42e5e901cbb5039725772dd6ee5a959cb35b39625572bd6ae56951cab5a395253729d66e52949ca359394251727d62e4e941c9b58393287725dcee4aa19c9373392285723dcae46a11c8b72391283721dc6e42a09c837139028171fdc2e3ea01c7b7038f00180000000ec000100000000003b970800040000000000772e3000080000000000ee5ba000100000000001dcb7c000200000000003b972800040000000000772e7000080000000000ee5d2000100000000001dcbac0002,0x27800000229000001da0000018b0000013c000000ed0000009e0000004f00000000⟩)
def counterTable : Table Nat :=
(.leaf 0x100000080000002000001000000040000020000000800000400000010000008000000200000100000004000002000000080000040000001)
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
  | 6 => 1
  | 7 => 0
  | 8 => 0
  | 9 => 0
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

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0753

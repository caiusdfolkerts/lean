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
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0805
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 6620
abbrev nodeCount : Nat := 7
abbrev leafCount : Nat := 1
def widths : PackedRawNatGrowth.Widths := ⟨13,3,6,1⟩
def blocks : Table PackedRawNatGrowth.Block :=
(.leaf ⟨0x66d89d8b6266258959962472d88dab6226a5885c962076d87dbb61e6e5875d961caad86e4b61a925866a9618aed85e5b616965856b9614bad84e8b612a25846e96106185359614c71852ea614a001c0000003b000041414d00852c6214a00030000003bb6100004000a58c02940004000000776c00000995626715889d361f6cd879b161d745872a561aacd85e53616945856b1614b8d84e83612a05846e1610000f0000003b109000040000016c3c1b6c30a608000002d85836d8414b10000005b0314db002962,0x3920000030100000286000000ed0000009e0000004f00000000⟩)
def counterTable : Table Nat :=
(.leaf 0x40100000000000802000000000010000000001000200800000020000010000000400000200000008000)
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
  | 1 => 1
  | 2 => 7
  | 3 => 1
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

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0805

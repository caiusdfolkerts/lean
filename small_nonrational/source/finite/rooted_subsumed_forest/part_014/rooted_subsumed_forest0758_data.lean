module
prelude
public import RootedSixExtra05GrowthCacheData
public import RootedSixExtra05FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0758
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 2170
abbrev nodeCount : Nat := 16
abbrev leafCount : Nat := 1
def widths : PackedRawNatGrowth.Widths := ⟨12,4,9,1⟩
def blocks : Table PackedRawNatGrowth.Block :=
(.leaf ⟨0x93cb0a48e58424eac1923560899cb024ae580266abf92b55f89bcafa4be57c26eabd92f55e8b5caf254e5782d6abb95355d8b7caea55e5742deab995755c8bdcae258e5702f6ab796355b891814649c0a226605096b02800070000001b8000401614400a0a1035050000180000037620000100242840d21400004000000dd878000479b5843e5ac01ee95f4fb4af87d957b3dcabd22ad5e10b4aea8ba57445cab9a1655c9114ae28ea570474ab7a2255b830e1461840a20d20508910280004c000001b8e0000080061f61820f90f107c00018000005b6200a2000180483ec00c1f20610f80003000000b6c40142000302c1320000b0f00006c02142495878284000600000000016d85c99c28c00084d657d25b2be13555ec96aaf45b65752ab2ba16d55ccaaaae45e65712c32b817955bcb0aadc0018000000dc7003ec0006000000c418358803e428460000001424958783e428464835842612c01f495f4b44af08b25752f0ab896055c0bc0ade58056e00090000006e3801f40003000000620c1ac401f61443000000621c1ac421f41423000000620c1ac401f214030000000a014ac3c1f21403,0xa46000009af000009310000070a00000667000005c400000531000004cd00000349000002f1000002990000016000000108000000b00000005800000000⟩)
def counterTable : Table Nat :=
(.leaf 0x200800000000004010000000000080000000008001004000000100020080000002000401000000040008020000001000100000000020002008000000400000100000008000000000000100010040000002000000800000040000010000000800000200000010000)
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
  | 2 => 6
  | 3 => 2
  | 4 => 0
  | 5 => 0
  | 6 => 0
  | 7 => 0
  | 8 => 0
  | 9 => 1
  | 10 => 0
  | _ => 0

def nodeTest (i : Nat) : Bool :=
  SubsumedCounterReplay.check widths cellCount 1024 288 leafCount nodeCount
    Papers.RationalityTen.RootedCaches.RootedSixExtra05.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixExtra05.badMasks
    Papers.RationalityTen.RootedCaches.RootedSixExtra05.kindMasks Papers.RationalityTen.RootedCaches.RootedSixExtra05.keys Papers.RationalityTen.RootedCaches.RootedSixExtra05.fastKind quota
    Papers.RationalityTen.FacetUniverses.RootedSixExtra05.Generators.FastWords.rawMaps rawLeaves codes counters i
theorem nodeTest_sound (i : Nat) (h : nodeTest i = true) :
    nodeBounds cellCount 1024 288 leafCount nodeCount (rawNodes i) = true ∧
      SubsumedRawGrowth.nodeCheck Papers.RationalityTen.RootedCaches.RootedSixExtra05.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixExtra05.badMasks
        Papers.RationalityTen.RootedCaches.RootedSixExtra05.kindMasks Papers.RationalityTen.RootedCaches.RootedSixExtra05.keys Papers.RationalityTen.RootedCaches.RootedSixExtra05.fastKind quota
        Papers.RationalityTen.FacetUniverses.RootedSixExtra05.Generators.FastWords.rawMaps rawLeaves rawNodes i = true :=
  SubsumedCounterReplay.check_sound widths cellCount 1024 288 leafCount nodeCount
    Papers.RationalityTen.RootedCaches.RootedSixExtra05.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixExtra05.badMasks
    Papers.RationalityTen.RootedCaches.RootedSixExtra05.kindMasks Papers.RationalityTen.RootedCaches.RootedSixExtra05.keys Papers.RationalityTen.RootedCaches.RootedSixExtra05.fastKind quota
    Papers.RationalityTen.FacetUniverses.RootedSixExtra05.Generators.FastWords.rawMaps rawLeaves codes counters i h
def leafTest (i : Nat) : Bool :=
  listBounds cellCount (rawLeaves i) &&
    (WitnessGrowthDAG.closedCheck FacetUniverses.RootedSixExtra05.ridgeList
      ((rawLeaves i).map (Fin.ofNat cellCount)) &&
      decide (((rawLeaves i).map (Fin.ofNat cellCount)).Nodup))

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0758

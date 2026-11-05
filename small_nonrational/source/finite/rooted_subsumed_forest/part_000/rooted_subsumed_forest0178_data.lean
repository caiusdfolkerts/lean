module
prelude
public import RootedSixBase01GrowthCacheData
public import RootedSixBase01FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0178
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 15246
abbrev nodeCount : Nat := 27
abbrev leafCount : Nat := 1
def widths : PackedRawNatGrowth.Widths := ⟨14,5,6,1⟩
def blocks : Table PackedRawNatGrowth.Block :=
(.leaf ⟨0x321800390bfc4c85fc9642fd00040000003a80001171c57078e2b13c71506e38a65b1c51218e2817af13e8d789e56bc4e9f5e270baf1364d789a028081b1404042a01eed500f509807580c03a9a601d2c300e80900738080398ca01bf2500dd3180698cc034a4601a2f300d03100678c80338e6018e4300c6998062c0c0310e401864200c200240000000b8600000082b8110158086000200000007f15e00008000000000037c5680f80000c00000007a307c5680f420000000bf44af15817e884982a694c13e02005d800180020781c300040c0001812025008812400040ab81d6c180800003c2ff055c0eb0000800000007591303ac094100000005fe8942ff055c09218cf058c0782c433816101c0b00cd057c0682bc000c0000001b0c0010302ec000200000000000b430005880bb00008000000000059058010302ec000200000000000b430005780bb0000842c32481419080010600000074020751150c000ea0000600000000002d0d380d300007224095000100000007869c06880003000000000007833e0750000300e1a9800081cc000016021804150c000e600006a1b8c408a10d84408582183261081620800af80030001cc44c3530c000e600008000000000059e3503150000600001aa04618400800016435408c00001800000000006c35408ac000180000000001643540c0019f00008d040ad00010000000786a80b701ce0001000000000005a1aa033e03e000040000000c022886a818002d63,0x106c00000c9600000c1200000bb200000b6000000b0e00000a630000099d0000094b000008eb000007e7000007790000070b0000069d000005e5000005850000050c000004ac0000040d00000309000002a900000223000001c300000155000000ce0000006000000000⟩)
def counterTable : Table Nat :=
(.leaf 0x400000000040008001000000000100020000010002000400000200000008000004000000000000100010000000003000200000000040000000000000c000000000000180010000000003000200000000060004000000000c00080000000010001000000000200020000000004000400000000080008000000001000100000000030002000400000200040000000008000800000000100010000000003000200000000060004000000000c00080000000018000)
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
  | 2 => 0
  | 3 => 7
  | 4 => 0
  | 5 => 0
  | 6 => 0
  | 7 => 0
  | 8 => 2
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

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0178

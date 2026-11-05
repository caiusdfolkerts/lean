module
prelude
public import RootedSixBase04GrowthCacheData
public import RootedSixBase04FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0693
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 2824
abbrev nodeCount : Nat := 29
abbrev leafCount : Nat := 1
def widths : PackedRawNatGrowth.Widths := ⟨12,5,11,1⟩
def blocks : Table PackedRawNatGrowth.Block :=
(.leaf ⟨0x57bb91b577b91a579b919575b918573b917571b916597b91558bb914595b913589b91257fb91157db91059db90f591b90e599b90d58db90c585b90b581b90a59fb909593b90859bb90758fb906587b905583b90457390c957190c85d390c75d190c687390c587190c457990bd57590bc5d990bb5d590ba87990b987590b857b90b157790b05db90af5d790ae87b90ad87790ac59590a558990a45f590a35e990a289590a188990a0597909958b90985f790975eb9096897909588b909459d908d591908c5fd908b5f1908a89d90898919088003c0000001e0001189aa00305822d000200000067604000286590e900010000002f60f54600034898a134a58a0d301424426e320d262320c1dc320b1d0320a30c12093001208000900000066bfe0002185717d185617b00020000005760e9b4000300000000005760e62c0003005517b00010000005760e9b4628000400000000001e6402de000318131a11b1019f18d31891bd018718e517118251701be416f1b2416e60e316d602316c000a00000056bf69e40003001217d3f8517b0002000000569e668c000348110b90cf109700020000001e68c2fa00032e4220a00010000006677a20a0003000f34400010000009abf89e67c0000415cd0b0150e099150d098120c097720b095154a08d124608b00070000001ebf89e67c068800050000004e72529ce42e200000000001e6a042c00030000004e72529ce2fa2000000000056988222000300090d500010000002ebf89e67c068842e0006130808d00010000001ebf89e67c068842e1aa0007000708c00010000001ebf89e679065845e3261a8000800000008c312bf89e679065845e3261a8118800000034421a6882fa2000000315192bf662a20000003af1a2bf675e200020bd00010000001e97069e000300000000005697017a000318401a0000100000056bf696c00030000000000aabe06a20003,0xefc00000e7800000e0400000cbc00000c2c00000bd400000b5400000afc0000098c000008fc0000086c000007f80000077800000644000005f8000005a000000554000004fc00000464000003c0000003100000027c00000230000001e40000019800000124000000cc0000005800000000⟩)
def counterTable : Table Nat :=
(.leaf 0x1004000000000020100000000000400000000040008020000000800100400000010002008000000400040000000008000800000000100010000000002000200000000040004000000000800080000000018001000000000400020000000004000000000000080008000000001000000000000020002000000000a000400000000180008000000003800100000000080000000000000400000000000008000000000000100000000000002000200000000040004000000000800080000000010001)
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
  | 3 => 8
  | 4 => 0
  | 5 => 0
  | 6 => 0
  | 7 => 0
  | 8 => 0
  | 9 => 2
  | 10 => 0
  | _ => 0

def nodeTest (i : Nat) : Bool :=
  SubsumedCounterReplay.check widths cellCount 1024 1152 leafCount nodeCount
    Papers.RationalityTen.RootedCaches.RootedSixBase04.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixBase04.badMasks
    Papers.RationalityTen.RootedCaches.RootedSixBase04.kindMasks Papers.RationalityTen.RootedCaches.RootedSixBase04.keys Papers.RationalityTen.RootedCaches.RootedSixBase04.fastKind quota
    Papers.RationalityTen.FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters i
theorem nodeTest_sound (i : Nat) (h : nodeTest i = true) :
    nodeBounds cellCount 1024 1152 leafCount nodeCount (rawNodes i) = true ∧
      SubsumedRawGrowth.nodeCheck Papers.RationalityTen.RootedCaches.RootedSixBase04.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixBase04.badMasks
        Papers.RationalityTen.RootedCaches.RootedSixBase04.kindMasks Papers.RationalityTen.RootedCaches.RootedSixBase04.keys Papers.RationalityTen.RootedCaches.RootedSixBase04.fastKind quota
        Papers.RationalityTen.FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves rawNodes i = true :=
  SubsumedCounterReplay.check_sound widths cellCount 1024 1152 leafCount nodeCount
    Papers.RationalityTen.RootedCaches.RootedSixBase04.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixBase04.badMasks
    Papers.RationalityTen.RootedCaches.RootedSixBase04.kindMasks Papers.RationalityTen.RootedCaches.RootedSixBase04.keys Papers.RationalityTen.RootedCaches.RootedSixBase04.fastKind quota
    Papers.RationalityTen.FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters i h
def leafTest (i : Nat) : Bool :=
  listBounds cellCount (rawLeaves i) &&
    (WitnessGrowthDAG.closedCheck FacetUniverses.RootedSixBase04.ridgeList
      ((rawLeaves i).map (Fin.ofNat cellCount)) &&
      decide (((rawLeaves i).map (Fin.ofNat cellCount)).Nodup))

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0693

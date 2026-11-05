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
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0659
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 2824
abbrev nodeCount : Nat := 28
abbrev leafCount : Nat := 1
def widths : PackedRawNatGrowth.Widths := ⟨12,5,11,1⟩
def blocks : Table PackedRawNatGrowth.Block :=
(.leaf ⟨0x57ba91b577a91a579a919575a918573a917571a916597a91558ba914595a913589a91257fa91157da91059da90f591a90e599a90d58da90c585a90b581a90a59fa909593a90859ba90758fa906587a905583a90457b9783577978257997815759780573977f571977e597977d58b977c595977b589977a57f977957d977859d97775919776599977558d97745859773581977259f9771593977059b976f58f976e587976d583976c57380c957180c85d380c75d180c687380c587180c457980bd57580bc5d980bb5d580ba87980b987580b857b80b157780b05db80af5d780ae87b80ad87780ac59580a558980a45f580a35e980a289580a188980a0597809958b80985f780975eb8096897809588b809459d808d591808c5fd808b5f1808a89d8089891808800540000001e0001305722d0001000000676040002623820d681820b00020000006712400024897a134a57a0d301524426e320d262320c1dc320b1d0320a30c12093001208000900000066bfe00024b9624400010000006760e9b400030000000000e29d07a6000365d47d465147d218131a11b1019f18d31891bd018718e517118251701be416f1b2416e60e316d602316c000c00000056bf69e400030000000000d31287600003001217d3f8517b0002000000569e668c000348110b90cf109700020000001e68c2fa00032e4220a00010000006677a20a0003000f34400010000009abf89e67c0000477ee76d15cc0b0150d099150c098120b097720a095154908d124608b00080000001ebf89e67c0688000500000000005712411800030000004e72529ce42e200000000001e6a042c00030000004e72529ce2fa2000000000056988222000300080d500010000002ebf89e67c068842e0006130708d00010000001ebf89e67c068842e1aa000700000000001ebf89e679065845e3261a8000800000034421a6882fa2000000315192bf662a20000003af1a2bf675e200020bd00010000001e97069e000300000000005697017a000318401a0000100000056bf696c00030000000000aabe06a20003,0xe5000000de800000d6400000c1c00000ba800000b50000009a800000950000008c000000830000007bc0000073c000005ec0000059400000548000004f0000004a40000044c000003b4000003100000027c00000230000001e40000019800000124000000cc0000005800000000⟩)
def counterTable : Table Nat :=
(.leaf 0x200800000000004000800000000080000000008001004000000100020000000004000400000000080008001000000800100000000020002000000000400040000000008000800000000180010000000004000200040000020004000000000800000000000010001000000000200000000000004000400000000140008000000003000100000000070002000000000400000000000008000000000000100000000000002000200000000040004000000000800080000000010001)
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
  | 8 => 1
  | 9 => 1
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

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0659

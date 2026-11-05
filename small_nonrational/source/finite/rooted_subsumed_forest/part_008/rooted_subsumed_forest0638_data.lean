module
prelude
public import RootedSixBase03GrowthCacheData
public import RootedSixBase03FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0638
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 5238
abbrev nodeCount : Nat := 43
abbrev leafCount : Nat := 1
def widths : PackedRawNatGrowth.Widths := ⟨13,6,7,1⟩
def blocks : Table PackedRawNatGrowth.Block :=
(.leaf ⟨0xd2bbd014aef00a6bbb009aee8252bb9054aee0226bb7049aed82d2bb5074aed02a6bb3069aec8952bb1194aec0926baf189aeb89d2bad1b4aeb09a6bab1a9aea8b52ba9214aea0b26ba7209ae980060000000ec0001014027014c09b00d0260350084193020c3340800cb01e402c0780ca81dc02a0760ca01d4028074000c0000000f5de0000485e11703804561a7114800180000026aef01380001800000000034aef04820840001074a22e01108ac03a22900030000004d5dc026800036d20fa9c463e90002000000695dc08b40ee00020000000f18c4aec078c082180000000000baef043c08000011bbe2d60108b4c3be2d20003000000555dc08ac000331003f000040000005d7702d30000c0000000001a577223705a00008c5e284000080000038aeb05bc0001800000000038aec05dc0fc00010d380fc02d83ec00080000005d77022904d0000800000000009abbd15c82a000040000000000555da08d41f4000219641b035806b865c1a800060000002ebbc04c0000600000008410e0ec042080000001c481c1c408c100000002010383b0100200000003c10b5de01e04000000076116bbc03b080000000e842d7780741004813809104d80401301920420c4410619004006080f200203c06040ee00103b06000ea00003a000600000007aee800023c10304c020be30002f0000c0000005d77409c0000d0040cd3408328d000c80003000000175db026800030c7832000040000005d7740980000c09c252006894401824f02589383142390e408d800c2210c208800020000001357740e0040000080000000000aa246076023000040000000000695dd0944100000200000000002a893c1c0080000100000000001544840ec0460000818916a80008000002aaee84a20c8000100000000001a57742ed11c800080071e7000080000034aeec4840001800000090984aeec79c242181145d40002000000aabba110838000040000000000715dd8b784420002010c5a40002000000aa21f0640000600000021f30a2c610f83506000000078216bba03c080000000ec22d774076100000001d085aee80e82,0x15980000141100001367000012fe00001254000011b70000115b000010f20000104800000fd200000f6900000ef300000e8a00000ded00000d8400000d1b00000c7100000c2200000bd300000b8400000b3500000ae600000a970000091000000866000007bc000007460000060d000005a40000053b000004d200000469000003e60000037d00000307000002ab00000228000001bf00000149000000ed0000009e0000004f00000000⟩)
def counterTable : Table Nat :=
(.leaf 0x40000400000000800008000004010000100000100200002000001004000040000040080000800000800000010000010020000200000100400004000002008000080000080100001000000802000020000020040000400000400800008000008010000100000100200002000001004000000000040000000000000800000000000010000000200000100000004000002000000080000040000001000000002000020000010040000400000200800008000004010000100000100200000000003004000040000040080000000000c01000000000018020000200000200400004000004008000080000040100001000001000000020000020040000400000400800000000008010000000000180000002000001000000040000020000000800000400)
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
  | 7 => 1
  | 8 => 0
  | 9 => 0
  | 10 => 0
  | _ => 0

def nodeTest (i : Nat) : Bool :=
  SubsumedCounterReplay.check widths cellCount 1024 96 leafCount nodeCount
    Papers.RationalityTen.RootedCaches.RootedSixBase03.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixBase03.badMasks
    Papers.RationalityTen.RootedCaches.RootedSixBase03.kindMasks Papers.RationalityTen.RootedCaches.RootedSixBase03.keys Papers.RationalityTen.RootedCaches.RootedSixBase03.fastKind quota
    Papers.RationalityTen.FacetUniverses.RootedSixBase03.Generators.FastWords.rawMaps rawLeaves codes counters i
theorem nodeTest_sound (i : Nat) (h : nodeTest i = true) :
    nodeBounds cellCount 1024 96 leafCount nodeCount (rawNodes i) = true ∧
      SubsumedRawGrowth.nodeCheck Papers.RationalityTen.RootedCaches.RootedSixBase03.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixBase03.badMasks
        Papers.RationalityTen.RootedCaches.RootedSixBase03.kindMasks Papers.RationalityTen.RootedCaches.RootedSixBase03.keys Papers.RationalityTen.RootedCaches.RootedSixBase03.fastKind quota
        Papers.RationalityTen.FacetUniverses.RootedSixBase03.Generators.FastWords.rawMaps rawLeaves rawNodes i = true :=
  SubsumedCounterReplay.check_sound widths cellCount 1024 96 leafCount nodeCount
    Papers.RationalityTen.RootedCaches.RootedSixBase03.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixBase03.badMasks
    Papers.RationalityTen.RootedCaches.RootedSixBase03.kindMasks Papers.RationalityTen.RootedCaches.RootedSixBase03.keys Papers.RationalityTen.RootedCaches.RootedSixBase03.fastKind quota
    Papers.RationalityTen.FacetUniverses.RootedSixBase03.Generators.FastWords.rawMaps rawLeaves codes counters i h
def leafTest (i : Nat) : Bool :=
  listBounds cellCount (rawLeaves i) &&
    (WitnessGrowthDAG.closedCheck FacetUniverses.RootedSixBase03.ridgeList
      ((rawLeaves i).map (Fin.ofNat cellCount)) &&
      decide (((rawLeaves i).map (Fin.ofNat cellCount)).Nodup))

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0638

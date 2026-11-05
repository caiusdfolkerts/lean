module
prelude
public import RootedSixExtra06GrowthCacheData
public import RootedSixExtra06FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0747
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 2300
abbrev nodeCount : Nat := 42
abbrev leafCount : Nat := 1
def widths : PackedRawNatGrowth.Widths := ⟨12,6,8,1⟩
def blocks : Table PackedRawNatGrowth.Block :=
(.leaf ⟨0xa23ec0688fa04a23e44a88f80004000000ee0001019c2acc200a8008029812709f32802700a009a023824c00e0923224244c09090022423c00908e129c21cf200840c8020830e07b06381e8f0907936241e030907706241d838e06f08381b8f8906d38241b038906b08241a8006c0000007c7d800098c9244c09890704923f6d248b31a6229c72489dc9a214646884f322212c288847321210c28483c0030000000ec7d0550000dce522c36908a4da322700030000003a28813c000300000000009667a422134000400000000007249a27010c00040000000000d249a26c10c000400000007a4162700f420000000764162700ec2027c4d831f11e244442c69110a2440424690108243c41c68f1060008000000971f614c000300788dc0922340c6c88019b21f066887509121c374486c399214085484421220f000a0000003b1f628413400046074b6001c2d500020023742b1f646e28430000000dc50a6ac1b811c300000023760a5aa46e284300000008211a46e104200000008211a46a10420660b759972d80658b54000c008dd0ac7d91b88f04d1000000087d4297910f89b0c0000001d9429a507883b0c00000087d4297510f8410c9143c51e4cf080008000003491a88f053000100000000001c9da11989b000100000000001c9e011b8a100010d822d500010023342b1f646614c000400000007811626c0f0200000007a10f1f626c0f4300000007640f1f626c0ec3133433cc0c0ca003031c000c0024883c7d8490000f4011d4c40073c0008001e941c7c86683d0001068b1460128514000800000258638490000c0000004b5818e609684e0c0000002c9818a2059084880e4061437c7820dc00030008e40f1f611c0003181c4e80c613900020006a2171f41ee0d430000008fa40f1f420c138300000012c2871f62580ec336108acdc322a00020000003b1f61e80ec00040000000906062741b812030000008fa42b1f425a1b8138400054c020052c0002001125831f63c222400040000000000d31f6a6000030000000000d31f6a540003,0x16e8000013de0000124e000011a800001144000010e00000107c0000103000000fe400000ebc00000d5400000cc800000c7000000c1800000bcc00000b8000000ace00000a7600000a1e000009c60000092e000008ca00000866000007e80000079c00000744000006ec00000646000005ae00000522000004ca0000047e000003d80000034c000002f40000029c00000204000001ac00000148000000b00000005800000000⟩)
def counterTable : Table Nat :=
(.leaf 0x840000000000010800000000080200000000002004000000000060080000000000c0100000000001802000000000020000000000000400040000000004010800000000100210000000002000000000000060000000000000c000000000000100000000000002000200000000060000000000000c000000000000180000000000003000000000000060080000000000c010000000000180210000000002004000000000040004000000000800080000000010001000000000100420000000004008000000000080100000000001800000000000020002000000000200840000000008000800000000100010000000002000200000000040080000000000c000800000000180010000000002004200000000020084000000000401)
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
  | 9 => 0
  | 10 => 1
  | _ => 0

def nodeTest (i : Nat) : Bool :=
  SubsumedCounterReplay.check widths cellCount 1024 240 leafCount nodeCount
    Papers.RationalityTen.RootedCaches.RootedSixExtra06.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixExtra06.badMasks
    Papers.RationalityTen.RootedCaches.RootedSixExtra06.kindMasks Papers.RationalityTen.RootedCaches.RootedSixExtra06.keys Papers.RationalityTen.RootedCaches.RootedSixExtra06.fastKind quota
    Papers.RationalityTen.FacetUniverses.RootedSixExtra06.Generators.FastWords.rawMaps rawLeaves codes counters i
theorem nodeTest_sound (i : Nat) (h : nodeTest i = true) :
    nodeBounds cellCount 1024 240 leafCount nodeCount (rawNodes i) = true ∧
      SubsumedRawGrowth.nodeCheck Papers.RationalityTen.RootedCaches.RootedSixExtra06.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixExtra06.badMasks
        Papers.RationalityTen.RootedCaches.RootedSixExtra06.kindMasks Papers.RationalityTen.RootedCaches.RootedSixExtra06.keys Papers.RationalityTen.RootedCaches.RootedSixExtra06.fastKind quota
        Papers.RationalityTen.FacetUniverses.RootedSixExtra06.Generators.FastWords.rawMaps rawLeaves rawNodes i = true :=
  SubsumedCounterReplay.check_sound widths cellCount 1024 240 leafCount nodeCount
    Papers.RationalityTen.RootedCaches.RootedSixExtra06.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixExtra06.badMasks
    Papers.RationalityTen.RootedCaches.RootedSixExtra06.kindMasks Papers.RationalityTen.RootedCaches.RootedSixExtra06.keys Papers.RationalityTen.RootedCaches.RootedSixExtra06.fastKind quota
    Papers.RationalityTen.FacetUniverses.RootedSixExtra06.Generators.FastWords.rawMaps rawLeaves codes counters i h
def leafTest (i : Nat) : Bool :=
  listBounds cellCount (rawLeaves i) &&
    (WitnessGrowthDAG.closedCheck FacetUniverses.RootedSixExtra06.ridgeList
      ((rawLeaves i).map (Fin.ofNat cellCount)) &&
      decide (((rawLeaves i).map (Fin.ofNat cellCount)).Nodup))

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0747

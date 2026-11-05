module
prelude
public import RootedSixExtra04GrowthCacheData
public import RootedSixExtra04FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0755
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 3640
abbrev nodeCount : Nat := 54
abbrev leafCount : Nat := 1
def widths : PackedRawNatGrowth.Widths := ⟨12,6,11,1⟩
def blocks : Table PackedRawNatGrowth.Block :=
(.leaf ⟨0x2bdd1f2d5de8f94af347c9575a3e42b9d1f1d5c68f8cb2f47c558ba3e22cad1f0d6268f84aff47c157da3e02ced1efd6468f7cb3347bd58da3de2c2d1eed6068f74b3f47b9593a3dc2cdd1edd63e8f6cb0f47b5583a3da2b9cc3255c66190ba730c75d19863439cc3161c66188ea700c37518061379c0305bc60180ae700bf571805f2bccc2f55d66178bb330bb5d5985d43ccc2e61d66170eb300b7755805b37cc02d5bd60168af300b357580592bdcc2c55de6160bb730af5d7985743dcc2b61de6158eb700ab757805537dc02a5bde0150af700a757780532cacc2956266148beb30a35e9985144acc2862266140eeb009f769804f38ac0275c260138b2b009b589804d2cbcc26562e6130bef30975eb984b44bcc25622e6128eef009376b804938bc0245c2e0120b2f008f58b80472cecc2356466118bfb308b5f1984544ecc2262466110efb0087771804338ec0215c460108b3b0083591804100300000000f000084b808b400040000019cd90000a04c118703e08bd02d9456010ca2a00b6312e04318910006005ffc62bfe0002000000000067154b86000300000000002f13400024b9091ea44bc8ecd85a46c60252343091119a6a84895295e4466dad21e30d290e1928886d2b0a41a940520c4ac2105a50108292b06412940320837811039b208818c60240a608120431801019820080800580000019afa80008515d2b263dc9440002005fdca2bfa9ac000300000000002f36a6160003625610cc744485d833c424c7aa21019949078002800000335f94e20001a594436801561ae00040000005d7d0f2cc6c00080000000000cd80032c0006ff510a3390f04f20a8826c000c0000007a6a1e19a38001054d06a4182734903331a400018000004d5eb4cc3cb00020000000000176003b732f000200000000000f4e03e3327000200000026b3415c94d63e31a6c90625db1830e848b18230118c01dc885fc00140000015afba710000c0000000002aaffa6c18d8001000000000034afc9ed991800112942312949f187300f0c11803460069922fe000a000000ad77d3b00006f1a082000010000002e7dc65e000300000000009b2c221a00030000000000e29687d20003030ea7b0016d3bc00249d80006000001a5784f8cc9c0008021c8a80001005ffc62bfe9b0786000400000000002f15a7b600038fed04647f6422a2b3010ec7d6085152984100028000000f5ed4ee3e431b000280000000004d5fb0cd08f000200000000004d5fd0cd08f00020025d72800040000038a581218c5071000140000016f8d0adf11b8c58c012ab900002000001c4fa0c5c8083f02f8000c03944c10001000000d2b787b861641c2101640007000000000056bbe9807b866041e1c8164000800000000001e7c8666404000479088463f8442299e2010ec310085004704100028000000f5e14ec3e332700028000000000553380e400018063d32c000400000349d399e8b907d0001400000000019a718c50710001000000000019af12701eb84700015811820ac00b0fc000507d8001800000175e13e3323000200000000002b24609a000180000000002b23210609a000200000000000f3e33230fb000203020fb4008e7cc00863e30003000000aab929aa6760004000000000056b929ec67a000400000032f682baa9c27ca65e40000004d4682b7a9a87ae3000000000066bfe96400030000004b22c2bfa96420000004b22c2bf696420000004be4c2bda97c20000004be4c2bd697c20000004bc1c2bd69782,0x1cab00001c4200001b4800001af000001aa4000017da00001748000016f0000016070000156900001511000014560000139b00001337000012d30000127b000011920000112e000010ca00000fe100000f6c00000f1400000ebc00000e0100000d8000000d2800000c2700000bc300000b5f00000ad200000a7a000009e10000093c000008a80000084400000743000006eb0000065e000005fa0000058a000004cf0000047700000413000003af000002f4000002900000022c000001d40000017c00000130000000e4000000980000004c00000000⟩)
def counterTable : Table Nat :=
(.leaf 0x80200000000001000000000100020080000002000401000000000008000000000040100000000010802008000000010040000000000400800000000088010000000001080200000000003004000000000060080000000008801000000000018020000000000300000000000004008000000000880100000000001802000000000020040000000004200802000000080010000000001080200000000003004000000000440080200000000401000000000020020000000002200400000000044008000000000100100000000001800000000000050040000000000c0080000000001c0100000000001802000000000040040000000004200800000000010010000000000180200000000004004000000000060080000000008401000000000018020000000000300400000000006008000000000880100000000002000000000000030000000000004200800000000084000000000001080000000000002000000000000040000000000000800)
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
  SubsumedCounterReplay.check widths cellCount 1024 1152 leafCount nodeCount
    Papers.RationalityTen.RootedCaches.RootedSixExtra04.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixExtra04.badMasks
    Papers.RationalityTen.RootedCaches.RootedSixExtra04.kindMasks Papers.RationalityTen.RootedCaches.RootedSixExtra04.keys Papers.RationalityTen.RootedCaches.RootedSixExtra04.fastKind quota
    Papers.RationalityTen.FacetUniverses.RootedSixExtra04.Generators.FastWords.rawMaps rawLeaves codes counters i
theorem nodeTest_sound (i : Nat) (h : nodeTest i = true) :
    nodeBounds cellCount 1024 1152 leafCount nodeCount (rawNodes i) = true ∧
      SubsumedRawGrowth.nodeCheck Papers.RationalityTen.RootedCaches.RootedSixExtra04.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixExtra04.badMasks
        Papers.RationalityTen.RootedCaches.RootedSixExtra04.kindMasks Papers.RationalityTen.RootedCaches.RootedSixExtra04.keys Papers.RationalityTen.RootedCaches.RootedSixExtra04.fastKind quota
        Papers.RationalityTen.FacetUniverses.RootedSixExtra04.Generators.FastWords.rawMaps rawLeaves rawNodes i = true :=
  SubsumedCounterReplay.check_sound widths cellCount 1024 1152 leafCount nodeCount
    Papers.RationalityTen.RootedCaches.RootedSixExtra04.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixExtra04.badMasks
    Papers.RationalityTen.RootedCaches.RootedSixExtra04.kindMasks Papers.RationalityTen.RootedCaches.RootedSixExtra04.keys Papers.RationalityTen.RootedCaches.RootedSixExtra04.fastKind quota
    Papers.RationalityTen.FacetUniverses.RootedSixExtra04.Generators.FastWords.rawMaps rawLeaves codes counters i h
def leafTest (i : Nat) : Bool :=
  listBounds cellCount (rawLeaves i) &&
    (WitnessGrowthDAG.closedCheck FacetUniverses.RootedSixExtra04.ridgeList
      ((rawLeaves i).map (Fin.ofNat cellCount)) &&
      decide (((rawLeaves i).map (Fin.ofNat cellCount)).Nodup))

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0755

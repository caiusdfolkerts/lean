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
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0680
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 2824
abbrev nodeCount : Nat := 48
abbrev leafCount : Nat := 1
def widths : PackedRawNatGrowth.Widths := ⟨12,6,11,1⟩
def blocks : Table PackedRawNatGrowth.Block :=
(.leaf ⟨0x15edcf06aeee78257973c0abab9e015cdcefeae2e77e59773beac5b9df1655cef6b12e77a57f73bcabeb9de1675ceeeb22e77659973baac6b9dd1615cee6b02e77259f73b8ac9b9dc166dcedeb1ee76e58773b6ac1b9db15cda192ae2d0c85d36863ae8b431a1cda18b0e2d0c47526061ba830309bc98182de0c0c0572605fab8302f95e5a17aaead0bc5d9685daeab42ea1e5a1730ead0b8758605bbaa302d9be1816ade8c0b45786059aba302c95eda162aeed0b05db6857aebb42ba1eda15b0eed0ac75a6055bab302a9be98152decc0a857a6053abb30299655a14ab12d0a45f56851af4b428a255a143112d0a0774604fbb430279c51813ae10c09c594604dac43026965da132b16d0985f7684baf5b425a25da12b116d0947766049bb530249c598122e14c0905966047ac530239675a11ab22d08c5fd6845af8b422a275a113122d08877c6043bb830219c71810ae20c08459c6041ac830208018000000078000588da41ad02d20b36259031802c8112b18406000a000000ce2480004012c64f025631d180ac910000c017ff18aff80008912044a36102237fc610f3cc308712918436000aca6bcecc008000336535e70001b2ea9f519454fa430291a11b100cf8c124669f018330a48c19718d48c48de8061c6392304f98c18053860bf8c74c5c460a62e037d216f1b290b7307445b580a22d8618416b30020b5187385a4c09c2d031cd16718268b3000c0000002b5fb4f200018000000000698943b00001801a0e90524c6f0b4a40b9000300346a1abf89e668c000412138528308828e3b1813d118c09c598604d80029d319d30c0200003d7ece98ce8000800000000003d528fac61c000825a50a4718604eaf430268000c0000007aa526f190000100000e44c89460100001e72264433c00046c8a0693c28c341179c19e8a040cc5c260650002800000173eb34f1a10bb000281e890b000044140000b013bd52a9e877a20a00043c30a89800080052c895fd3a50a5000200000000000f2ef11800018007cd1000040000026afe2799f000011dfbceda2a1d0b07066054ac13029854381325a920982dca04bb906c2563b98124e34c09170e60481583423d639811c2a9a08d124a845bb930219c498108bfcc08300120000001ebf89e67c068800050000000000671241a8000373a606d0000800000173ec22e00018000002739294e7217100000000002b4c43430c90002000645ec00040000015afe2799f01a210b800180f3011ae24c08459c604180018000000f5fc4f33e034421717b00038005c23000040000007afe2799e41961178c986a00020deacb503c965a500020008c312bf89e679065845e3261a811880000003215829a66425ec300000034421a6882fa20000005d71a2bae7ac2000000315192bf662a20000003af1a2bf675e201282af80009a780004c029707252e0d3c0006018f09871a6048af530238000c0000007acf26e1960001000000000015ac4a6205800010000000c2ca2afe98588000000c2c64afd985892b16ff0940b7f6488511ea44208ed291444a94882234ac1906a500c8312b04416940220a4ac0904a500482000300000019afa8000800000000019c4aa590000d20124880002000000cd7fd35800060000000001557ecccc0006930722549821118001000000335fd4d60001bc01867400040000015b0027598780010000a1ea00020000005d3ac91420800080000000001353ac3d4208000800000061e5157f8c3c40000009645857fd2c840000009645857f52c8490001a0000100000056bf696400030000000000e29ea7c461e0004,0x1dae00001cd100001c2e00001b2300001813000017bb00001700000015e900001585000014ca0000144400001343000012a00000121f000011c70000114600000ecc00000e7400000dff00000db300000d4f00000cb600000bd700000b2600000a5800000a00000009b4000009680000091c000008d0000008390000077e0000071a000006ce00000682000004da000004820000040d000003b500000323000002a200000221000001bd0000017100000125000000d90000006400000000⟩)
def counterTable : Table Nat :=
(.leaf 0x2000400000000040000000004000800000000100010000000002000200040000020004000000000c000800000000180010000000003000200000000060004000000000c000800000000200010000000003000200000000060004000000000420080000000018001000000000400020004000002000400000000080008000000001000000000000030002000000000a0004000000001800080000000038001000000000800000000000004100000000000080000000000001000000000000020000000000000400000000000008000800000000180010000000003000200000000021000000000000420000000000000401000200000008020000000002100400000000042008000000000840100000000020802000000000410040000000008200800000000084000000000001080000000000021000000000000420080000000010401)
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
  | 2 => 1
  | 3 => 8
  | 4 => 0
  | 5 => 0
  | 6 => 0
  | 7 => 0
  | 8 => 1
  | 9 => 0
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

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0680

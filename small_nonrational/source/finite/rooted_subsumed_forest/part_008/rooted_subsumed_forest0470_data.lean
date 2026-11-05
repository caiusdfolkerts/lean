module
prelude
public import RootedSevenTwoSix13GrowthCacheData
public import RootedSevenTwoSix13FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0470
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 2038
abbrev nodeCount : Nat := 40
abbrev leafCount : Nat := 1
def widths : PackedRawNatGrowth.Widths := ⟨11,6,6,1⟩
def blocks : Table PackedRawNatGrowth.Block :=
(.leaf ⟨0x139be5a537ca4e0f92941f2169be3a937c65a0f8aa41f1179be1ab37c25e0f82ac1f01e7740beee80499cfe9b39f92773ea6ee7c799cf6fb39e9e573cbeae78491cee9a39d92573aa6ae74791ce6fa39ca07738c4ee70519cdeb339b947736acee6c819cd71339aa05734c4ae68511cceb2399945732acae64811cc712398a17730c6ee60559cbebb39795772eaeee5c859cb71b396a1572cc6ae58551caeba39595572aaeae54851ca71a3949f3683bc6d064cda0a91b41223681c06d0258da02a1b4023367fc26cfe5cd9faa9b3f12259ca64b3878666ef8ccd92199aa63334482666984cc942598ac4b3080665f10ccb941996ac332c502656b04ca952594ae4b2884664f18cc9951992ae3324542646b84c880180000003700010a51620482c028c578110ae021158000a0000058fd600020000000000dfe90b000030000000000dfeb0b000030000000000dfe90ae00030000000000dfeb0ae00030000000000dfeb0ac000349f00a63e00c2780100018000001ff5000080000000005dfc0004000c00000000037fa0004000d2700298d80309a00400060000007eb100020000000000df6e8010003000000002c2770801100000000006fa8400800186c0f61d71e60ac3c4000c00000d1d56000400000000058e9a1d200060000000001beae1ca00060000000001beaa1ca00069a8044d4c0786900e00030000003f52800100000000006fb6000800180000000006fb5000800180000000006fa50008001a6801134f01e19c038000c000000fd4e00040000000001bed200200060000000002eed600200060000000001be960020006918014c2c0184500200030000003e88000100000000006f47800800180000000006f47000800180000000006f430008001a4400530800610e008000c000000f6a200040000000001bb69002000600000000582b4900224c502268803c30c0700018000001ed340008000000000376cc004000c000000000376c8004000c00000000037688004000d304089a080f0c001c00060000007b4b00020000000000ddb100100030000000000dda10010003,0xf2800000e6c00000e1800000dc400000d7000000d1c00000cc800000c3a00000be600000b9200000b0400000ab000000a6700000a130000098500000931000008dd00000889000007fb000007a700000753000006ff000006710000061d000005c900000575000004e7000004930000043f000003eb0000035d00000309000002c000000232000001de0000018a00000136000000a80000005400000000⟩)
def counterTable : Table Nat :=
(.leaf 0x8400004200802100401080200840100420080210000108020084010042000021004010802000401004200002100401080200840100420000210040108020084010042000021004010802008401004200002100401080200840100420000210040108020004000042008021004010802008400004200802100401)
def codes (i : Nat) : Nat :=
  let b := blocks.get (i / 128)
  PackedRawNatGrowth.drop
    (PackedRawNatGrowth.take 32 (PackedRawNatGrowth.drop (32*(i%128)) b.offsets)) b.payload
def counters (i : Nat) : Nat :=
  PackedRawNatGrowth.take 25 (PackedRawNatGrowth.drop (25*(i%128)) (counterTable.get (i/128)))
def rawNodes (i : Nat) := PackedRawNatGrowth.decodeNode widths (codes i)

def leafTable : Table (List Nat) :=
(.leaf [])
def rawLeaves := leafTable.get

def leaves : Fin leafCount → List (Fin cellCount) := decodedLeaves rawLeaves
def quota : Nat → Nat
  | 0 => 1
  | 1 => 0
  | 2 => 7
  | 3 => 0
  | 4 => 2
  | _ => 0

def nodeTest (i : Nat) : Bool :=
  SubsumedCounterReplay.check widths cellCount 1024 36 leafCount nodeCount
    Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13.candidateMasks Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13.badMasks
    Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13.kindMasks Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13.keys Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13.fastKind quota
    Papers.RationalityTen.FacetUniverses.RootedSevenTwoSix13.Generators.FastWords.rawMaps rawLeaves codes counters i
theorem nodeTest_sound (i : Nat) (h : nodeTest i = true) :
    nodeBounds cellCount 1024 36 leafCount nodeCount (rawNodes i) = true ∧
      SubsumedRawGrowth.nodeCheck Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13.candidateMasks Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13.badMasks
        Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13.kindMasks Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13.keys Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13.fastKind quota
        Papers.RationalityTen.FacetUniverses.RootedSevenTwoSix13.Generators.FastWords.rawMaps rawLeaves rawNodes i = true :=
  SubsumedCounterReplay.check_sound widths cellCount 1024 36 leafCount nodeCount
    Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13.candidateMasks Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13.badMasks
    Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13.kindMasks Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13.keys Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13.fastKind quota
    Papers.RationalityTen.FacetUniverses.RootedSevenTwoSix13.Generators.FastWords.rawMaps rawLeaves codes counters i h
def leafTest (i : Nat) : Bool :=
  listBounds cellCount (rawLeaves i) &&
    (WitnessGrowthDAG.closedCheck FacetUniverses.RootedSevenTwoSix13.ridgeList
      ((rawLeaves i).map (Fin.ofNat cellCount)) &&
      decide (((rawLeaves i).map (Fin.ofNat cellCount)).Nodup))

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0470

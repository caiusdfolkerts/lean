module
prelude
public import RootedSixBase00GrowthCacheData
public import RootedSixBase00FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0291
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 21976
abbrev nodeCount : Nat := 56
abbrev leafCount : Nat := 1
def widths : PackedRawNatGrowth.Widths := ⟨15,6,7,1⟩
def blocks : Table PackedRawNatGrowth.Block :=
(.leaf ⟨0x246d4fae56d4faa4ed4fa65ed4fa266d4f9e6ed4f9a76d4f96a6d4f927ed4f8eaed4f8ad6d4f86ded4f8286d4f7eb6d4f7a96d4f76c6d4f72e6d4f6ef6d4f6a8ed4f66bed4f629ed4f5eced4f5aeed4f56fed4f5246803264e80322450031e4d0031a43603164b6031256802f666802f255002ee65002ea53602e663602e25e802c66e802c25d002be6d002ba5b602b66b602b2a680296d680292a50028ed50028aa360286d360282ae80266de80262ad0025edd0025aab60256db60252c680236f680232c50022ef50022ac360226f36022000f00000000f0000102cd50c05a833600020000000d6ae9000013dd0070bda006f800100000002f575019a800019cceaddaaceada80b82792f6c25da96c25d06ac25c80ac25c06a825b80a825b00048000000d217ec00008ce41128000400000059abae13680000c16205f4d5e05ec00080000001bab7a17bc2200000200c0045800080000001f56ec2fd81710000400000002e2646add85fb02e2022c800000000000bd5d302e2000061ad083e02d083c1ac083a02c08387ac083662c0834000c0000002c85fb09e40000600000010786885fb083c2000000000006c2fd84f208380000800000017ed2885fb0970205482a900010000000b42fd84b60000300000000000d42f782b500003393d57f553d57931204560d0841f010841e0cf041d00f041c3ce841b30e841a00090000001642fe8000132982f880008000000e3560426e00001809413b802c13a800100000005b521008780ae0000400000000000d6a420277000030d185c401185c32cf05c220f05c10d105c001105bf00060000001c427a0458000030000000b863842e184f41000000000006a16fc27a045800004830016c000100000006c2fe841e0000330f80b9000100000003c22d01a801a400008000000040681845b02020228600000017f53085fd0838204e019e000100000006c27a041c00003000000000003c274042803540000811aaa3e49aaa32012069a187062c007062a184062800406261810624001062200120000001a85ff0000278cd44108c010c000200000005ea9185e700003000000000006eae9d5120000304b809660b0094000200000003ea9005f401e80000800000000000dd51e011400006915a9c0000200000016d522098e0400000102280430000400000017aa47536805000002314c0b680008000000375482a6f00f401280000a000000107ce0d520a9bc107c6011020a00d020619101da18d01d618901aa00901a818801a600801a4c4601a2dc601a000140000000b85ff069a0000601002e000e02da00040000000d85ff020a00006b8fa7ba00020000000785ff02e0041400010000000000035a89012e80000c0000002ffc510bfe05b44b8ca8f060a033e00040000000d85ff069a040c00010016043c000400000017a90809d405700002000000027530b521013a810f180000000000b213d80d08000180000000d412a17fc06a080000000690950bfe0348440601a000020000000b85ff062a000060c5032800020000000d85c302180000600000000002c85cf035800006083020800020000000b85ff062600006302031000020000000d85f3063e04400001000000000000f067006b0082000020200082000080000002e17fc18880001800000000003617cc18e811000004,0x1eec00001e5f00001dc300001c7200001bf200001b4700001ab800001a45000019e1000018d5000018800000180d000017b800001738000016d4000015830000150300001458000013f4000012e80000129300001220000011a000001111000010ad0000105800000fd800000f6500000e1400000d7800000d1400000c6900000c0500000b7600000ae700000a49000009e500000869000007cd0000073e000006da00000685000005da0000054b000004e7000004830000042e000003d900000359000002d900000275000001f500000166000000f30000007300000000⟩)
def counterTable : Table Nat :=
(.leaf 0x2008000000000040100000004000800000000080010040000001000200800000040004010000000800080200000018000004000000100020000000004000400000000080000000000001800100000000020000000000000400040000000008000800000000080010040000001000200800000040004010000000400080000000010001000000000200000000000006000400000000080008000000001800100000000030000000000000400000000000008000800000000180010000000001000200800000020004020000000000080200000010001004000000100020080000004000402000000040008040000001000100800000010000000000000400040000000008000800000000180010040000001000200000000040000000000000c00080200000010001004000000200000000000004000400000000080000000000001000000000000020002000000000400040000000008000800000000100010000000003000200000000060004000000000800080000000018001)
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
  SubsumedCounterReplay.check widths cellCount 1024 96 leafCount nodeCount
    Papers.RationalityTen.RootedCaches.RootedSixBase00.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixBase00.badMasks
    Papers.RationalityTen.RootedCaches.RootedSixBase00.kindMasks Papers.RationalityTen.RootedCaches.RootedSixBase00.keys Papers.RationalityTen.RootedCaches.RootedSixBase00.fastKind quota
    Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.FastWords.rawMaps rawLeaves codes counters i
theorem nodeTest_sound (i : Nat) (h : nodeTest i = true) :
    nodeBounds cellCount 1024 96 leafCount nodeCount (rawNodes i) = true ∧
      SubsumedRawGrowth.nodeCheck Papers.RationalityTen.RootedCaches.RootedSixBase00.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixBase00.badMasks
        Papers.RationalityTen.RootedCaches.RootedSixBase00.kindMasks Papers.RationalityTen.RootedCaches.RootedSixBase00.keys Papers.RationalityTen.RootedCaches.RootedSixBase00.fastKind quota
        Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.FastWords.rawMaps rawLeaves rawNodes i = true :=
  SubsumedCounterReplay.check_sound widths cellCount 1024 96 leafCount nodeCount
    Papers.RationalityTen.RootedCaches.RootedSixBase00.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixBase00.badMasks
    Papers.RationalityTen.RootedCaches.RootedSixBase00.kindMasks Papers.RationalityTen.RootedCaches.RootedSixBase00.keys Papers.RationalityTen.RootedCaches.RootedSixBase00.fastKind quota
    Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.FastWords.rawMaps rawLeaves codes counters i h
def leafTest (i : Nat) : Bool :=
  listBounds cellCount (rawLeaves i) &&
    (WitnessGrowthDAG.closedCheck FacetUniverses.RootedSixBase00.ridgeList
      ((rawLeaves i).map (Fin.ofNat cellCount)) &&
      decide (((rawLeaves i).map (Fin.ofNat cellCount)).Nodup))

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0291

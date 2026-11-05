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
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0725
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 2824
abbrev nodeCount : Nat := 33
abbrev leafCount : Nat := 1
def widths : PackedRawNatGrowth.Widths := ⟨12,6,11,1⟩
def blocks : Table PackedRawNatGrowth.Block :=
(.leaf ⟨0x752f861ba87c309bcbe182de1f0c0572f85fab87c2f9d63e16eea9f0b66f8f85ab7a7c2d15e3e166ae9f0b275af855bab7c2a9bebe152dedf0a857af853abb7c299dd3e13eed1f09e714f84eb847c271653e136b11f09a776f849bb57c249c5be122e15f090596f847ac57c239df3e10eee1f08671cf842b887c211673e106b21f08200240000001e0001360f11b180648d0c22e4666d9e21e30cc90e1925c86cde0440e6c82206318090298204810c6004066080202000c00000066bea000260cb10931e74840663841e0006000000cd7e53880006721609e414b84d80010000000f4d43c334700020606cd240cb46900004000001357ad330f2c000800000000003d380f8cc9c00080000009acd05725358f8c68487182300c0c01dc5c5fc000c0000015afba710000c00000000034afc9ed99180010c02c30460081801a628bf80018000002b5df4ec0001801553bc00189d80004000001a5784f8cc9c0009159408763e90428a934208000c0000007af6a771f218d800140126b940002000001c52c090c628388000a000000b7c6856f88dc62c600915c80001000000e27d062e4041f817c000601c82608000800000695bc3dc30b20e1080b2000380d3c60c00040000015a60198107872059000185e9cb50380e5a50002000823129e064847e31c1e2104600000008e512d5aba677011c400000000001e7c866640400046785843b0c2c214011210400060000003d7853b0f8cc9c000a018a4cb0001000000d274e67a2e41f400050000000000669c63141c40004000000000066bc49c07ae11c0005600387e000183ec0008000000baf09f1991800100000000001591908304d00010000000000079f199187d8001000887cc00833e30002000000aab929aa676000400000032f682baa9c27ca65e40000004d4682b7a9a87ae30000004be4c2bda97c20000004be4c2bd697c20000004bc1c2bd69782,0x117c00000fd400000f2500000e8700000de900000d8500000d2d00000c7e00000c1a00000b6b00000acd00000a06000009790000092100000888000007e30000074a0000069400000630000005cc000005050000047800000414000003a400000306000002a20000023e000001a00000013c000000e4000000980000004c00000000⟩)
def counterTable : Table Nat :=
(.leaf 0x10000000000080200000000002004000000000060080000000000c010000000000180200000000003000000000000040080000000000c01000000000010020000000000300400000000008008000000000100100000000001800000000000050040000000000c008000000000140100000000003000000000000040000000000000600800000000010010000000000200200000000003004000000000080080000000000c0100000000001802000000000030040000000000600800000000010000000000000180000000000002000000000000040000000000000800)
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
  | 2 => 9
  | 3 => 0
  | 4 => 0
  | 5 => 0
  | 6 => 0
  | 7 => 0
  | 8 => 0
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

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0725

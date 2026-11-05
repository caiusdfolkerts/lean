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
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0127
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 15246
abbrev nodeCount : Nat := 34
abbrev leafCount : Nat := 1
def widths : PackedRawNatGrowth.Widths := ⟨14,6,6,1⟩
def blocks : Table PackedRawNatGrowth.Block :=
(.leaf ⟨0x660e115883844060e10c083842720e105a83840120e0fc28383e760e0f5b8383c160e0ec38383aaa0e0e64838384a0e0dcc83836ae0e0d65838344e0e0ccd83832ba0e0c68838305a0e0bd08382e00180000003a8000161f03900400e208c0385e7c0cc1900328c300c978203058080c018102fc0040be18002f40000bc000c0000000bf0840000987815c195056c04c15800030000000df0880710000301d0a24064288000200000016f08407200ec000100703de61b0f707683db00030000002cf08414481c803b0000500000000000d87bc14480ec000100000000000d3c2207d413c8000400000000000d87ce13e80ee0001186017401705cc05817100030000000df08414401c803b00005000000000016f088071011c000100000000000b3c2102e60720000400000000002cf0840b881c8000118283ea0940f9c0008000000b3c2202b40650000400000002f8c8f0801f3017c301202d01440b1000200000007f0880ac01c4000100000000000b3c2202b005a0000400000005608582b005808c3c08500e0208034080000300000007f08407100003000000000016f07c05f01380001000000000005bc2101c404100004000000000016f084071010000010e2c0850080208014080000300000007f07c0700000308a0a28624287000200000016f07c05e8108000100000000000d3c21051203c0000400000002f0c2f06c1378178300705d071817350405c4000c00000037c1f01c00410000400000000002cf07c0ba01c00001000000017f4260bf81a820440654000400000037c1f01c0040000046830f400004000000b3c1d03280000c00000383d60bc1e84c20520c0000000be22bc22017c200000002f88af08405f080000000bc12bc2101782,0x115000000fc600000f1800000e7600000dac00000d3e00000cd000000c6200000b9800000b2a00000abc00000a4e000009ac0000094c000008aa0000083c000007ea0000073c000006ce00000660000005f200000544000004a200000434000003d400000318000002aa00000258000001d000000156000000f6000000a40000005200000000⟩)
def counterTable : Table Nat :=
(.leaf 0x800008000000010000100000080200002000002004000040000060080000000000c010000100000100200000000003004000040000060080000800000801000010000010020000200000200400004000004008000080000080000001000001002000020000020040000000000400000008000004010000100000100200002000002004000040000040080000800000401000010000010020000200000200400004000004000000080000080100001000001002000000000020000000400000400800008000004010000100000100000002000001000000040000020000000800000400)
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

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0127

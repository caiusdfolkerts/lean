module
prelude
public import RootedSixExtra05GrowthCacheData
public import RootedSixExtra05FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0746
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 2170
abbrev nodeCount : Nat := 57
abbrev leafCount : Nat := 1
def widths : PackedRawNatGrowth.Widths := ⟨12,6,9,1⟩
def blocks : Table PackedRawNatGrowth.Block :=
(.leaf ⟨0x12370a324ee1444cdc284b5b850000200000037000086360a30c5e1441abc2844978500002000000371c0000100350a3005c14402b82841970500002000000371c00fb000192b4081246810032d01fc61a03f00b407d00680f854d01a49da0340f340671b680cc0cd01940da03215b405d28680b83ed016c71a02d03b405904680b000240000003c7003ec28c000813cc7789180ec8c301d600030007c21a3801f61460f8400641d203c4394000800284838ee0df07c850832140000003e4858ee07c8748c000000720c28e40718380c0000001f9038e008887d85183f14317051986e0a2003414206682800010000001b8e007d0000c0968cba42a192005431e12b46092d50be81aa17a06382b0027055d2cd8aa241b15303362a2006c540003000289098e007d8510001062e118356c22f605645a45b08b06159150002800509251bf1950fa0a12000010e8dfa24021f484c8746fc5943e8800004b437e890087d21325a1bf1650fa206290980cbe0e824781a400e833018406400050000001e38031e1f6144000500d06a60c98d400129a6002232160a2612000a001470c470063c3e828c258000c189cb040004006fd2499f0df87d84b900000006fd309c912a0df8de9018c31923150002000000e26c83802ca1f21460006544862e928cc580008d3028e18010000e26983801f414612c000600000011131265e2220fc300000007e41a3801f219c1460fc54842716000200642544c8463c3e825880080abc0004003e92499687e07d045100000003f0c495787e0450c000000198458df8c787d851033140000001f9038e00b287c85183f14000000198458e00c787d85103314000000558498e00ab07d85090000000540898e00a807d8511000c8caa4d719401ae3220d3c5b40270b5a64d16a48982d0093459c0260b2830b158480a2a60014540003000284898e007d0508001180c1168c1822a0002000a124a38032a1f414240c8611800020014241c9686fc5943ec284a0258cf920a19bb6933187324600c044bf520817d8003000512311be18f0fb0a20002b01525900011bf0000d8042849299e8df85080010000000000078c88550000cf6084580008000000f1be1920a4000212010d100010007c40e4b01f41460f8400000022e30a45c0c8200000006450a4ae0c8200001920a242404191058c90510320c000000558898df0ab07d85010000000558498df8ab07d85090000000540898de8a807d85110000000541098df8a807d8509002512332082431c104800006001402947005583e4280000a48241d0000400280439228df8b587c85000018683073800083800000e0214241cac88c03e82841c0000cde1cbd00004002849890e8df8b287d8509464307380008002c10728922e0fa0a305828000000df10d2881be0e319f030960e8812a610c230062044860308001060fe000c0000003c7005403e8284000a00002f4144848083e20b17a0a207c180821f300023dc30007ac000c001f9068e007c85103f1000007781fc86010a124a3bc1420fe300001ee07e41804289128f705103f0c00004981f105010a242624c1440f83,0x22d70000221f0000215b00001f1100001e5c00001db600001d5e00001d0600001c9600001bd200001a2a0000193f000018b9000018330000173c00001639000015ba00001562000014b0000013dc00001384000013140000129500001216000011be0000114e000010de0000106e0000100a00000fa600000dfe00000d6400000cd900000bc700000b2600000ace00000a4f000009d00000098400000938000008be0000085a000007f6000007920000072e0000066d000005d60000051d0000049200000407000003af0000029d000002230000016e000000f40000007a00000000⟩)
def counterTable : Table Nat :=
(.leaf 0x10000000001000200000000040004000000000c0008000000001840000000000031000000000000220000000000000600000000000188000000000002000200000000060004000000000c200000000000108000000000002100000000000061004000000000c400800000000108000000000001100000000000062004000000000c40080000000000c000000000003100000000000023000000000000460000000000000c000000000003100000000000062000000000000c400000000000184000000000003080000000000060004000000000c20000000000018800000000000308020000000004100400000000004008000000000880100000000021000000000000020000000000000400000000000088000000000003080000000000061000000000000c2000000000001840000000000030802000000000620040000000008600800000000188000000000002180000000000022000000000000c200800000000088000000000003080000000000022000000000000440000000000008800)
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
  | 2 => 6
  | 3 => 3
  | 4 => 0
  | 5 => 0
  | 6 => 0
  | 7 => 0
  | 8 => 0
  | 9 => 0
  | 10 => 0
  | _ => 0

def nodeTest (i : Nat) : Bool :=
  SubsumedCounterReplay.check widths cellCount 1024 288 leafCount nodeCount
    Papers.RationalityTen.RootedCaches.RootedSixExtra05.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixExtra05.badMasks
    Papers.RationalityTen.RootedCaches.RootedSixExtra05.kindMasks Papers.RationalityTen.RootedCaches.RootedSixExtra05.keys Papers.RationalityTen.RootedCaches.RootedSixExtra05.fastKind quota
    Papers.RationalityTen.FacetUniverses.RootedSixExtra05.Generators.FastWords.rawMaps rawLeaves codes counters i
theorem nodeTest_sound (i : Nat) (h : nodeTest i = true) :
    nodeBounds cellCount 1024 288 leafCount nodeCount (rawNodes i) = true ∧
      SubsumedRawGrowth.nodeCheck Papers.RationalityTen.RootedCaches.RootedSixExtra05.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixExtra05.badMasks
        Papers.RationalityTen.RootedCaches.RootedSixExtra05.kindMasks Papers.RationalityTen.RootedCaches.RootedSixExtra05.keys Papers.RationalityTen.RootedCaches.RootedSixExtra05.fastKind quota
        Papers.RationalityTen.FacetUniverses.RootedSixExtra05.Generators.FastWords.rawMaps rawLeaves rawNodes i = true :=
  SubsumedCounterReplay.check_sound widths cellCount 1024 288 leafCount nodeCount
    Papers.RationalityTen.RootedCaches.RootedSixExtra05.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixExtra05.badMasks
    Papers.RationalityTen.RootedCaches.RootedSixExtra05.kindMasks Papers.RationalityTen.RootedCaches.RootedSixExtra05.keys Papers.RationalityTen.RootedCaches.RootedSixExtra05.fastKind quota
    Papers.RationalityTen.FacetUniverses.RootedSixExtra05.Generators.FastWords.rawMaps rawLeaves codes counters i h
def leafTest (i : Nat) : Bool :=
  listBounds cellCount (rawLeaves i) &&
    (WitnessGrowthDAG.closedCheck FacetUniverses.RootedSixExtra05.ridgeList
      ((rawLeaves i).map (Fin.ofNat cellCount)) &&
      decide (((rawLeaves i).map (Fin.ofNat cellCount)).Nodup))

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0746

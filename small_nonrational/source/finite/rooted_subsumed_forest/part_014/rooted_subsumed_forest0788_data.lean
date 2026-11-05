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
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0788
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 2170
abbrev nodeCount : Nat := 46
abbrev leafCount : Nat := 1
def widths : PackedRawNatGrowth.Widths := ⟨12,6,9,1⟩
def blocks : Table PackedRawNatGrowth.Block :=
(.leaf ⟨0x24d8b0a48b16109342c192285822658b024ab16009942bf92a857e26d8afa4bb15f09b42bd92e857a2d58af254b15e0b542bb95285762dd8aea55b15d0b742b995685722f58ae258b15c0bd42b7962856e243c146497828898f050969e0a0001c0000006e00010cd6af81fad5d03f4ab886695700fc2ade19855b800e85100160a1032c1400012000000dd880000490a93f000040000007b102f00000c00000000007b1a3102f000010000188000036015d0292c40ba000030c4eb045e855c4b10ab807a056f0c40adc00442840c885000038000003761e000100265820346ae2008d5c00d12b7802256e2c3c1425e78280001c000001bb0f2f10000c0d283180250620f4a0c21894180cd282f982505e27480ba48901706d202d8c2405a03480b2009016000300000007b0f2f12c1000100001878000360106211ac3c0c40003000061e0000d80416046b0f02c0000c00000178905af12b8080000015b8c9b0f2f12b70c00000173845b102e70804fad00000b0f00006c02b9c72587973800060000000000dd86974967800087975610f8eac01ed657d3eacaf87d455ecf68abd229d57842acaea8b595d1168ab9a151572442cae28e595c11c8ab7a21156e0c1a146182028834405089080a000130000006e38000024f389c89871381682267aa844c90236420126c7ed20c84d80038031060d6200a200018000000500935ff0a01049a5e60001006186c2c3042814200040000000000b6bf03aa14000046b30ba2d061741a0bae7b5975ce0004000000b6c4066414400040000000000e2c40ba01400c200050000000000e2c3cba01400c20005002a446905488078a10eb012218182442a000ac400001b008509256200a1000180000000000f6202230a10002019314d000100156606bc02ac1403000000156522bb02ac27014240000000a120ebc82a014230c00a5e0540990000987800036010a124ac3c1420003181ebb642397640008000002db0b93385180010000176c689890161764ac2ebb6344146400000000001ec402c614400042698afa4b315f09a4abd92c957a2d98aea55315d0b64ab995495722f18ae258315c0bc4ab7960956e000c0000006e3801f600034b169ec002816000080000007b1007c8508001000000028052b1a07c0500c00000016046b1007c85082c1030029780008005092561e0f90a100021207584260cb007d195f4b432bc22c65752f06ae2580d5c0bc0ab7960156e00090000006e3801f4000353049c8a009381682267aa844c9000400620c1ac401f614400044e0a9cc9c1134400080188706b1087d0508001000000000038b0187c8500001000018757aab0010000e2c3abd4000348049c0000200c418358803e428000080000000001c58003e428000081e014a4000587800036010a014ac3c1f2140000400000000001eb1e0002,0x1d1000001bd100001b5e00001afa00001a800000197700001862000016ba00001640000015c60000157a00001522000014d600001441000013dd000011900000107b0000102f00000fb000000f4c00000e7c00000e0c00000d9c00000c9b00000c3700000bc400000b6000000b0800000a58000009be00000938000008d4000007380000069e00000646000005e2000005630000041800000348000002ae0000024a000001d000000151000000ed0000004c00000000⟩)
def counterTable : Table Nat :=
(.leaf 0x8020000000000100800000000002018000000000040200000000000802000000000010080000000000201800000000004010000000400080200000000401008000000000000180000000000002000000000000040000000000100c00000000002000000000200040100000004000802000000080000040000002000200800000040004010000000800080400000010001008000000200020080000002000401000000080008020000000840000400000020800008000000210000100000004000802000000100010080000002000000800000040004000000000800080200000010001004000000200000080000004100001000000080008000000001000100400000020002008000000400040100000008000804000000000010040000002000200800000040004010000000800080200000000001)
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
  | 2 => 4
  | 3 => 2
  | 4 => 0
  | 5 => 0
  | 6 => 0
  | 7 => 0
  | 8 => 0
  | 9 => 3
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

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0788

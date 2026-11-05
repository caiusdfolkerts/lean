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
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0663
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 2824
abbrev nodeCount : Nat := 48
abbrev leafCount : Nat := 1
def widths : PackedRawNatGrowth.Widths := ⟨12,6,11,1⟩
def blocks : Table PackedRawNatGrowth.Block :=
(.leaf ⟨0x2bdba46d5ddd234af2e919575748c2b9ba45d5c5d22cb2ee91558b748a2caba44d625d224afee91157d74882ceba43d645d21cb32e90d58d74862c2ba42d605d214b3ee90959374842cdba41d63dd20cb0ee90558374822b9b03255c58190ba6c0c75d16063439b03161c58188ea4d0c3750686137934305bc1a180ae4d0bf570685f2bcb02f55d58178bb2c0bb5d5605d43cb02e61d58170eb0d0b7754685b37c342d5bd1a168af0d0b357468592bdb02c55dd8160bb6c0af5d7605743db02b61dd8158eb4d0ab756685537d342a5bd9a150af4d0a757668532cab02956258148beac0a35e9605144ab02862258140ee8d09f768684f38a34275c21a138b28d09b588684d2cbb026562d8130beec0975eb604b44bb025622d8128eecd09376a684938b34245c29a120b2cd08f58a68472ceb02356458118bfac08b5f1604544eb02262458110ef8d087770684338e34215c41a108b38d083590684100300000000f0000983b6800c15645a0004000000cec08000460aa1790001000000576055c800034895d09a52ae835284f3f895a79f802d2cf3810967840248c9e04a463a30119220004802ffe315ff000130caa8352e504880004000000cec1d368000696e90e900010000002f60f54662800044a4690d80008000003317d0d50001878296f400040000038d3aa741e98001066cc340f88d19951468cb00018000002bad44b60001800000000055ad631500018000000000179ea0001122448946c22446ff8d21e798690e2523486c001594d79d9801000066ca6bce000318110d08d87467da81a334f80d19852468cb8c6886246f3a30ed58d1827cc68c029c345fc63a82e230541701be98b78d94c5b983a42dac05216c30c20b5980105a8c39e2d2604f16818e70b38c13859800580000015afda790000c00422fa7f1417b6ae68bb13a105d0a11e2e6000a000000ad7f13ccd18000890200b90cf004b80010000000f5fc34617d000201e7d0b000044140000b013bd52a9e877a20a00043c2f289800080052c895fd3a50a5000200000000000f2ef118000180070d1000040000026afe2799f0000105436160e0cd0a958268530a868264b5261305b95097720c84ac7734249c69a122e1cd0902b07047ac734238553011a249608b7726843389342117f9a10600220000003d7f13ccf80d10000ae74d0da00010000002e7d845c00030000004e72529ce42e20000000000569886861920004000b8bd80008000002b5fc4f33e0344217000338934211671a10600040000003d7f13ccf80d1085c5ec000e000000688434d105f44000000bae34575cf58400000062a3257ecc54400000075e3457ecebc4025155f000134f000098052e0e4a5c1a78000c0320130e34d0915ea684700018000000f59e4dc32c000200000000002b5894c40b000020000001859455fd30b10000001858c95fb30b1244308f52210476948c2254a44111a560c8352806418958220b4a011052560482528024100014000000cd7d40004a74817d49858bd80010000002b5ff4d600018002ac1400040000038a731e898780011f8121be00020000005ec14f44c3c00080000000001353082080006930722549821118001000000335fd4d60001bc01867400040000015b0027598780010000a1ea00020000005d3ac91420800080000000001353ac3d4208000800000061e5157f8c3c40000009645857fd2c840000009645857f52c8490001a0000100000056bf696400030000000000e29ea7c461e0004,0x1c8300001bfd00001b8800001a37000019a500001924000018af0000182e0000177f00001727000016db000015d0000012fa0000120500001167000010c40000104300000feb00000f6a00000d0d00000c9800000c4c00000be800000b4f00000a8d00000a41000009f5000009a90000095d000008c60000080b000007a70000075b0000070f000005a10000050f0000048e0000040d000003b500000323000002a200000221000001bd0000017100000125000000d90000006400000000⟩)
def counterTable : Table Nat :=
(.leaf 0x200800000000004020000000000080000000008001004000000100020100000002000400000000080008020000001000100400000010002008000000200040100000000000800000000100010000000002000200000000060004000000000c000800000000180010000000003000200000000021004000000000c000800000000200010000000002000200000000040000000000000c0008000000002800100000000060002000000000400000000000008000000000000100000000000002000000000000040004000000000c000800000000180010000000001080000000000021000000000000020080000000008401000000000208020080000002100400000000042008000000000840100000000020802000000000410040000000008200800000000084000000000001080000000000021000000000000420080000000010401)
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
  | 3 => 6
  | 4 => 0
  | 5 => 0
  | 6 => 0
  | 7 => 0
  | 8 => 0
  | 9 => 2
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

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0663

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
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0666
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 2824
abbrev nodeCount : Nat := 46
abbrev leafCount : Nat := 1
def widths : PackedRawNatGrowth.Widths := ⟨12,6,11,1⟩
def blocks : Table PackedRawNatGrowth.Block :=
(.leaf ⟨0x57b648dabbb24695e59232aeac918573648bab8b245965d922ab16c9145956489ac4b24495fd9222afac91059d6487ac8b2439665921ab1ac90c5856485ac0b242967d9212b26c90859b6483ac7b241961d920ab06c9045735064ab8a832174d418eba2a0c68735062c38a8311d49a186ea0d0c26f26860b78343015c9a17eae0d0be579505eabaa82f17654176baaa0ba879505cc3aa82e1d61a16eea8d0b66f8685ab7a342d15e1a166ae8d0b257b5058abba82c176d415ebaea0ae87b5056c3ba82b1d69a156eacd0aa6fa6854b7b342a15e9a14eaecd0a65955052ac4a82917d54146bd2a0a28955050c44a8281dd1a13eed0d09e714684eb8434271651a136b10d09a597504cac5a82617dd412ebd6a096897504ac45a8251dd9a126ed4d0927166848b8534241659a11eb14d08e59d5046ac8a82317f54116be2a08a89d5044c48a8221df1a10eee0d08671c6842b8834211671a106b20d08200600000001e00013075d00182a48b400080000019d8100008c1502f20002000000aec0ab9000069129a134a54d06a50967f12b4b3f005a39e70211cf08048993c0944c7460202440009005ffc62bfe00026194506a5c9891000080000019d83a6d0000d2dce1d200020000005ec1ea8cc500008948d21b0001000000662fa1aa00030f052de800080000071a754e83d300020cd90681f11a332a28d1960003000000575a896c00030000000000ab5ac62a000300000000002f3d4000230109129b28488dff1a43cf30d21c4a4690d8002b29af3b30020000cd94d79c00069091185000100000056e28bc69a60004180f8d08d87067da81a334f80d19852468cb8c67c6246f3830ed58d1827cc68c029c345fc63a82e230541701be98b78d94c5b983a42dac05216c30c20b5980105a8c39e2d2604f16818e70b38c13859800580000015afda790000c003c2fa7f1417b6ae68bb13a105d0a11e2e6000a000000ad7f13ccd180008901d0b90cee84b80010000000f5fc4f334617d00028000001dea954f43bd34d1050bd28006cd1000040000026afe2799f0000105434160e0cd0a958268530a864264b5261305b95097720c04ac7734249c69a122e1cd0902b07047ac734238552e11a249608b7726843389342117f9a10600220000003d7f13ccf80d10000a0000000000ad7c139cfb0d408b8000c0000000000ad7c139cfb0d4085c000c0000000000ad310d0c32400080000000000ad7f13ccf80d1085c000c00000000003d7f13ccf80d105f4000c000000bae34575cf58400000062a3257ecc54400000075e3457ecebc4025155f000134f000098052e0e4a5c1f59a7800100320130e34d0915ea684700018000000f59e4dc3c832c00028000000000175894c43e03440b000030000001859455fd30b10000001858c95fb30b1244308f52210476948c2254a44111a560c8352806418958220b4a011052560482528024100014000000cd7d40004a74817d49858bd80010000002b5ff4d600018002ac1400040000038a731e898780011f8121be00020000005ec14f44c3c00080000000001353082080006930722549821118001000000335fd4d60001bc01867400040000015b0027598780010000a1ea00020000005d3ac91420800080000000001353ac3d4208000800000061e5157f8c3c40000009645857fd2c840000009645857f52c8490001a0000100000056bf696400030000000000e29ea7c461e0004,0x1bbc00001b3600001ac100001970000018de0000185d000017e800001767000016b800001660000016140000150900001488000011b2000010bd0000101300000fa300000f2200000cc500000c4900000bcd00000b6900000aed00000a7100000a25000009d90000098d000008ea00000823000007a70000075b0000070f000005a10000050f0000048e0000040d000003b500000323000002a200000221000001bd0000017100000125000000d90000006400000000⟩)
def counterTable : Table Nat :=
(.leaf 0x80200000000001008000000000020000000002000401000000040008040000000800100000000020002008000000400040100000004000802000000080010040000000000200000000040004000000000c00080000000010001000000000300020000000008000400000000140000000000001800100000000040002000000000a000400000000140008000000001800100000000050002000000000a000400000000080000000000001000000000000020000000000000600040000000010000800000000280010000000001080000000000021000000000000020080000000008401000000000208020080000002100400000000042008000000000840100000000020802000000000410040000000008200800000000084000000000001080000000000021000000000000420080000000010401)
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
  | 3 => 5
  | 4 => 0
  | 5 => 0
  | 6 => 0
  | 7 => 0
  | 8 => 0
  | 9 => 3
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

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0666

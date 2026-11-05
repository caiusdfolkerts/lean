module
prelude
public import RootedSixBase03GrowthCacheData
public import RootedSixBase03FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification
public import RootedSubsumedForest0706Packed000
public import RootedSubsumedForest0706Packed001
public import RootedSubsumedForest0706Packed002
public import RootedSubsumedForest0706Packed003
public import RootedSubsumedForest0706Packed004
public import RootedSubsumedForest0706Packed005
public import RootedSubsumedForest0706Packed006

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0706
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 5238
abbrev nodeCount : Nat := 42911
abbrev leafCount : Nat := 139
def widths : PackedRawNatGrowth.Widths := ⟨13,16,7,8⟩
def blocks : Table PackedRawNatGrowth.Block :=
(.branch 150
 (.branch 50
 nodeBlocks000
 (.branch 100
 nodeBlocks001
 nodeBlocks002))
 (.branch 250
 (.branch 200
 nodeBlocks003
 nodeBlocks004)
 (.branch 300
 nodeBlocks005
 nodeBlocks006)))
def counterTable : Table Nat :=
(.branch 150
 (.branch 50
 nodeCounters000
 (.branch 100
 nodeCounters001
 nodeCounters002))
 (.branch 250
 (.branch 200
 nodeCounters003
 nodeCounters004)
 (.branch 300
 nodeCounters005
 nodeCounters006)))
def codes (i : Nat) : Nat :=
  let b := blocks.get (i / 128)
  PackedRawNatGrowth.drop
    (PackedRawNatGrowth.take 32 (PackedRawNatGrowth.drop (32*(i%128)) b.offsets)) b.payload
def counters (i : Nat) : Nat :=
  PackedRawNatGrowth.take 55 (PackedRawNatGrowth.drop (55*(i%128)) (counterTable.get (i/128)))
def rawNodes (i : Nat) := PackedRawNatGrowth.decodeNode widths (codes i)

def leafTable : Table Nat :=
(.branch 69
 (.branch 34
 (.branch 17
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf 0x2b114487e62de11085641800720078004000b)
 (.leaf 0x145331110c47582e011805641800520078004000c))
 (.branch 3
 (.leaf 0x130a26d92f48022ff12885601840420078008000c)
 (.leaf 0x98219309fc3c418008b02b20c30078004000b)))
 (.branch 6
 (.branch 5
 (.leaf 0x5070a2044c12b05681ce0400090008000a)
 (.leaf 0x15989f440312106702b60ef0150008000a))
 (.branch 7
 (.leaf 0x15548062e612506702b60ef0298008000a)
 (.leaf 0x146c2920f845f828f0ae05641c4041011000c000c))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf 0x13f87482fe0f8856413a03e010001c000a)
 (.leaf 0x13dc89c2e3129056816203e01e001c000a))
 (.branch 11
 (.leaf 0x142127b90344aa2050ad03f811c04e01f0040000c)
 (.leaf 0x14348082450d1056c1f602b0060008000a)))
 (.branch 14
 (.branch 13
 (.leaf 0x10006002450d1056c1fe0540060008000a)
 (.leaf 0x14047f02e20fb856c13a020009801c000a))
 (.branch 15
 (.leaf 0x13f85f22500fe05642a003e0038008000a)
 (.branch 16
 (.leaf 0x1588a243f31cb05641c202b0100008000a)
 (.leaf 0x26d0f146e433a17f85600ea0710100014000b))))))
 (.branch 25
 (.branch 21
 (.branch 19
 (.branch 18
 (.leaf 0x16d47d22fb15485641da0520108008000a)
 (.leaf 0x14287d035217a0568130072010001c000a))
 (.branch 20
 (.leaf 0x50a12e05681f203f016000c0008)
 (.leaf 0x1590a0c3ff12185681c0072015000c000a)))
 (.branch 23
 (.branch 22
 (.leaf 0x2c21530a223cf110056017a0710150004000b)
 (.leaf 0x2e293987662f911c056017a03d0180004000b))
 (.branch 24
 (.leaf 0x13f89542f715705641da03e0108008000a)
 (.leaf 0x14348082df155856c1f004a0100010000a))))
 (.branch 29
 (.branch 27
 (.branch 26
 (.leaf 0x32593987662f711005601aa03d01b0004000b)
 (.leaf 0x13d47d82ee15485681f2064010000c000a))
 (.branch 28
 (.leaf 0xa389834a703ac17208b02b00bd01e8004000b)
 (.leaf 0x147429b8fb47542fb11685601aa04d0208004000c)))
 (.branch 31
 (.branch 30
 (.leaf 0x147129c12cc8082e4116856017a04301c8004000c)
 (.leaf 0x9f096f89b44971730a282b00bd01e8004000b))
 (.branch 32
 (.leaf 0x13e22de13989062fe0ac032813c03d00d803c000c)
 (.branch 33
 (.leaf 0x13e326712085ca2050ac032816e06101e8044000c)
 (.leaf 0x131e32213c87882d00ff056425402300f8008000c)))))))
 (.branch 51
 (.branch 42
 (.branch 38
 (.branch 36
 (.branch 35
 (.leaf 0x14348082df0ad83ec13004a0100050000a)
 (.leaf 0x143f26f12f87f02df0ac03281300430100040000c))
 (.branch 37
 (.leaf 0x140127612f87e82e30ac03281300430100040000c)
 (.leaf 0x14732a692d87f02e30ac03281300430100040000c)))
 (.branch 40
 (.branch 39
 (.leaf 0x130232614287a02f40ad033c0ea0470100040000c)
 (.leaf 0x141d28791307a03650ad83cc0e804d00f804c000c))
 (.branch 41
 (.leaf 0x141827612d87e83a40ac03381300430100040000c)
 (.leaf 0x131428590dc7e82f40f605680fe04e0100040000c))))
 (.branch 46
 (.branch 44
 (.branch 43
 (.leaf 0x14308ba3f116f856c1f00a401e0080000a)
 (.leaf 0x125c32614287a02eb0ad040c0fe0470100040000c))
 (.branch 45
 (.leaf 0x125d32693c47a024f0ad03a812e0490150040000c)
 (.leaf 0x131432414287a02f40f605680fe0470100040000c)))
 (.branch 48
 (.branch 47
 (.leaf 0x131b27912247882ff0e1056412e06f011003c000c)
 (.leaf 0x131632114287a02dc10085680fc04d00f8048000c))
 (.branch 49
 (.leaf 0x131e27912d07882d00ff056412c06f00f804c000c)
 (.branch 50
 (.leaf 0x27f0f107482fe0ac83840e8064019807c000b)
 (.leaf 0x14047f02460ad83b016005001e00a8000a))))))
 (.branch 60
 (.branch 55
 (.branch 53
 (.branch 52
 (.leaf 0x9bb13f47ca3851a98b9c1ba07200f8004000b)
 (.leaf 0x9b9191ca143d91a90bd04400d101c8004000b))
 (.branch 54
 (.leaf 0x9c119308123b417588ac202054019800c000b)
 (.leaf 0x9be19349f43d01da8bb04700a10120018000b)))
 (.branch 57
 (.branch 56
 (.leaf 0x137d2d113e47883b116b83e414006f011807c000c)
 (.leaf 0x138532614447a03b415d83b017005f012007c000c))
 (.branch 58
 (.leaf 0x138432394487e82d010f06ac19e01b0078004000c)
 (.branch 59
 (.leaf 0x137c32093e85d829e13185b023603f0030004000c)
 (.leaf 0x137932313b45ec24410186081d204701e8008000c)))))
 (.branch 64
 (.branch 62
 (.branch 61
 (.leaf 0x138132414145ec21e0f706001a203e01a0004000c)
 (.leaf 0x13752708ebc5f422210085b41ea03d01a0008000c))
 (.branch 63
 (.leaf 0x137932313b45be21d0c1054820406001e8008000c)
 (.leaf 0x137c32493e85a829e13185b017e05b01f8004000c)))
 (.branch 66
 (.branch 65
 (.leaf 0x4e10a243a612b06ac1c80400158008000a)
 (.leaf 0x138432094485be28a12c065819804001c8004000c))
 (.branch 67
 (.leaf 0x137927691b47522eb123865c1f807001e800c000c)
 (.branch 68
 (.leaf 0x4e04a0a30012086b01fe07201f000c000a)
 (.leaf 0x138532114447a02d213387603540c400f8008000c))))))))
 (.branch 104
 (.branch 86
 (.branch 77
 (.branch 73
 (.branch 71
 (.branch 70
 (.leaf 0x138532394447a02f413386a81e603300f8008000c)
 (.leaf 0x138432b94487b835e13e06ac1c802b00f8008000c))
 (.branch 72
 (.leaf 0x13842890f7077a2c714386ac1c807100f8008000c)
 (.leaf 0x9c29924a223e816e087832a0db0268004000b)))
 (.branch 75
 (.branch 74
 (.leaf 0x13842890fd076e3a1110865819804e0158004000c)
 (.leaf 0x4e14a223e817a06a81e60720100008000a))
 (.branch 76
 (.leaf 0x13842890f7077a37716f865819807200f8004000c)
 (.leaf 0x4e10a243f41cb06ac1c802b0100008000a))))
 (.branch 81
 (.branch 79
 (.branch 78
 (.leaf 0x13842890f707022e10e2065818a03900f8004000c)
 (.leaf 0x138432494487b82de0e2065818a03300f8004000c))
 (.branch 80
 (.leaf 0x138432494487b82bb0cb044c1d405e00f8004000c)
 (.leaf 0x13842890f7076e3a111006581980700158004000c)))
 (.branch 83
 (.branch 82
 (.leaf 0x13842b394487b82200cb044c1d40710150004000c)
 (.leaf 0x13802830f705ba22c0e106041a20700378004000c))
 (.branch 84
 (.leaf 0x138232393f48122bb0ff85bc0f804800f8018000c)
 (.branch 85
 (.leaf 0x138232393f48122bb0ff845411404800f8018000c)
 (.leaf 0x138232393f48122bb13a87fc13e04800f8018000c))))))
 (.branch 95
 (.branch 90
 (.branch 88
 (.branch 87
 (.leaf 0x9c21924a243dc16f08803881960628004000b)
 (.leaf 0x137e32513947fa2c813a092c3aa00f0028004000c))
 (.branch 89
 (.leaf 0x138432494487b82e811006581ce01b0048004000c)
 (.leaf 0x1382281916475e2ef110857420203e0050004000c)))
 (.branch 92
 (.branch 91
 (.leaf 0x13842fb944885438110f065819803e0158004000c)
 (.leaf 0x137a32b94208ba3dc1af09f01d202b00f8008000c))
 (.branch 93
 (.leaf 0x138432b94487b835e0d583900e804e015807c000c)
 (.branch 94
 (.leaf 0x13852888f407503650d503c00e804d016007c000c)
 (.leaf 0x13842890f7077438c0d583900e804e015807c000c)))))
 (.branch 99
 (.branch 97
 (.branch 96
 (.leaf 0x137628391187d03b61d008841ba04d0160004000c)
 (.leaf 0x138327791607883bc1638a1820006f00f8010000c))
 (.branch 98
 (.leaf 0x26fc642283916c7a02d308a83d411403a00f8048000d)
 (.leaf 0x13812828f106ac3000d603fc100072026807c000c)))
 (.branch 101
 (.branch 100
 (.leaf 0x138532394447a02f40d503cc0e804d019807c000c)
 (.leaf 0x137e287916c7a03af17d88881ea04d01a0008000c))
 (.branch 102
 (.leaf 0x138132c14148d02d20ef06b010603e00f8014000c)
 (.branch 103
 (.leaf 0x138532114447a02dc0d5036c0ee04d00f8070000c)
 (.leaf 0x138432394487e82d00d5833c0ee04700f806c000c)))))))
 (.branch 121
 (.branch 112
 (.branch 108
 (.branch 106
 (.branch 105
 (.leaf 0x138132094146002410c003fc10404d01f0074000c)
 (.leaf 0x13792768e905fc21d0f9060813a07001e801c000c))
 (.branch 107
 (.leaf 0x13702d013585f62410b8035816a06f01f0074000c)
 (.leaf 0x138532314445b82420d5036c0f003f0198070000c)))
 (.branch 110
 (.branch 109
 (.leaf 0x13822048e985e422d0ff858018005401c8004000c)
 (.leaf 0x13842890f706ca2e60d986580f207100f8018000c))
 (.branch 111
 (.leaf 0x138227290247022700f5059c1820290108008000c)
 (.leaf 0x13802bc14187b82cb0c0838810a07000f806c000c))))
 (.branch 116
 (.branch 114
 (.branch 113
 (.leaf 0x138432494487b82e80cb039c0f203300f806c000c)
 (.leaf 0x137932293b45d424c0f9865c13e04801e8018000c))
 (.branch 115
 (.leaf 0x137e27291787fa2cf0ea8338134070010806c000c)
 (.leaf 0x137e2728ff459e2410ea857c19c070037800c000c)))
 (.branch 118
 (.branch 117
 (.leaf 0x137e32394247fa2d010f080419e01b0078004000c)
 (.leaf 0x137632494247ca2e811007b01ce01b0048004000c))
 (.branch 119
 (.leaf 0x137e32394247fa2d0100833c0ee04700f806c000c)
 (.branch 120
 (.leaf 0x137632494247ca2e80f6039c0f203300f806c000c)
 (.leaf 0x137e32394247fa2d0100858419e04700f8004000c))))))
 (.branch 130
 (.branch 125
 (.branch 123
 (.branch 122
 (.leaf 0x9c1191c9fa40916208a83fe1600618004000b)
 (.leaf 0x138432114487b82c70d5845c0fc04e00f801c000c))
 (.branch 124
 (.leaf 0x138432394487e82c70d5845c0fc04700f801c000c)
 (.leaf 0x137932193b45d621d0cb855814404d01e8020000c)))
 (.branch 127
 (.branch 126
 (.leaf 0x13822fd13a48b23ac15e09183d408401f0014000c)
 (.leaf 0x13852b08f9874a2f111686541b005201d8004000c))
 (.branch 128
 (.leaf 0x13852b08fb875a2ee12386541b00520120004000c)
 (.branch 129
 (.leaf 0x138332a93bc8fa45816307a411e03e00f8014000c)
 (.leaf 0x270664427791607882c60f484a015c02300f8014000d)))))
 (.branch 134
 (.branch 132
 (.branch 131
 (.leaf 0x137e27411b885e2c8124075420c03d0028008000c)
 (.leaf 0x13852f195307d82bc13386541ae0510100004000c))
 (.branch 133
 (.leaf 0x9c113a08882220f5059018203d0148008000b)
 (.leaf 0x9c114008b23c415d87fc13602300f8018000b)))
 (.branch 136
 (.branch 135
 (.leaf 0x138228011647882bb0ff845411404d00f8018000c)
 (.leaf 0x9c113a08883c515e07a80ea0200080014000b))
 (.branch 137
 (.leaf 0x1382280118c8b22c40ff830c10603e00f806c000c)
 (.branch 138
 (.leaf 0x9bd142c8ba3dc16e080c2ee0db00f8004000b)
 (.leaf 0x137e286116c7a02d0100833c0ee04d00f806c000c)))))))))
def rawLeaves (i : Nat) : List Nat :=
  let code := leafTable.get i
  (PackedRawNatGrowth.readList 13 (PackedRawNatGrowth.take 5 code)
    (PackedRawNatGrowth.drop 5 code)).1

def leaves : Fin leafCount → List (Fin cellCount) := decodedLeaves rawLeaves
def quota : Nat → Nat
  | 0 => 1
  | 1 => 3
  | 2 => 4
  | 3 => 4
  | 4 => 0
  | 5 => 0
  | 6 => 0
  | 7 => 0
  | 8 => 0
  | 9 => 1
  | 10 => 0
  | _ => 0

def nodeTest (i : Nat) : Bool :=
  SubsumedCounterReplay.check widths cellCount 1024 96 leafCount nodeCount
    Papers.RationalityTen.RootedCaches.RootedSixBase03.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixBase03.badMasks
    Papers.RationalityTen.RootedCaches.RootedSixBase03.kindMasks Papers.RationalityTen.RootedCaches.RootedSixBase03.keys Papers.RationalityTen.RootedCaches.RootedSixBase03.fastKind quota
    Papers.RationalityTen.FacetUniverses.RootedSixBase03.Generators.FastWords.rawMaps rawLeaves codes counters i
theorem nodeTest_sound (i : Nat) (h : nodeTest i = true) :
    nodeBounds cellCount 1024 96 leafCount nodeCount (rawNodes i) = true ∧
      SubsumedRawGrowth.nodeCheck Papers.RationalityTen.RootedCaches.RootedSixBase03.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixBase03.badMasks
        Papers.RationalityTen.RootedCaches.RootedSixBase03.kindMasks Papers.RationalityTen.RootedCaches.RootedSixBase03.keys Papers.RationalityTen.RootedCaches.RootedSixBase03.fastKind quota
        Papers.RationalityTen.FacetUniverses.RootedSixBase03.Generators.FastWords.rawMaps rawLeaves rawNodes i = true :=
  SubsumedCounterReplay.check_sound widths cellCount 1024 96 leafCount nodeCount
    Papers.RationalityTen.RootedCaches.RootedSixBase03.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixBase03.badMasks
    Papers.RationalityTen.RootedCaches.RootedSixBase03.kindMasks Papers.RationalityTen.RootedCaches.RootedSixBase03.keys Papers.RationalityTen.RootedCaches.RootedSixBase03.fastKind quota
    Papers.RationalityTen.FacetUniverses.RootedSixBase03.Generators.FastWords.rawMaps rawLeaves codes counters i h
def leafTest (i : Nat) : Bool :=
  listBounds cellCount (rawLeaves i) &&
    (WitnessGrowthDAG.closedCheck FacetUniverses.RootedSixBase03.ridgeList
      ((rawLeaves i).map (Fin.ofNat cellCount)) &&
      decide (((rawLeaves i).map (Fin.ofNat cellCount)).Nodup))

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0706

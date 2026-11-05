module
prelude
public import RootedSixBase01GrowthCacheData
public import RootedSixBase01FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification
public import RootedSubsumedForest0352Packed000
public import RootedSubsumedForest0352Packed001
public import RootedSubsumedForest0352Packed002

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0352
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 15246
abbrev nodeCount : Nat := 15697
abbrev leafCount : Nat := 152
def widths : PackedRawNatGrowth.Widths := ⟨14,14,6,8⟩
def blocks : Table PackedRawNatGrowth.Block :=
(.branch 50
 nodeBlocks000
 (.branch 100
 nodeBlocks001
 nodeBlocks002))
def counterTable : Table Nat :=
(.branch 50
 nodeCounters000
 (.branch 100
 nodeCounters001
 nodeCounters002))
def codes (i : Nat) : Nat :=
  let b := blocks.get (i / 128)
  PackedRawNatGrowth.drop
    (PackedRawNatGrowth.take 32 (PackedRawNatGrowth.drop (32*(i%128)) b.offsets)) b.payload
def counters (i : Nat) : Nat :=
  PackedRawNatGrowth.take 55 (PackedRawNatGrowth.drop (55*(i%128)) (counterTable.get (i/128)))
def rawNodes (i : Nat) := PackedRawNatGrowth.decodeNode widths (codes i)

def leafTable : Table Nat :=
(.branch 76
 (.branch 38
 (.branch 19
 (.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf 0x30c0aa41f4070417f85220b2811a024005c0028000c)
 (.leaf 0x2a9090c1e9073217f82ea097814801700480028000c))
 (.branch 3
 (.leaf 0x2aa893e1e9070417f852a0ae8236017000a0010000c)
 (.leaf 0x2a9893e1f5072e18d85fe13e82b2018000a0008000c)))
 (.branch 6
 (.branch 5
 (.leaf 0x2ab88f41fb06dc18206000be010001880460038000c)
 (.leaf 0xaa623d08041b7068218002fa03a00460030000b))
 (.branch 7
 (.leaf 0x2ff88c61ff86e419606000b280ea02900480028000c)
 (.branch 8
 (.leaf 0x30b89581f9870c1a006000be010002400460038000c)
 (.leaf 0xaae1fb863017f05140b8810202400720028000b)))))
 (.branch 14
 (.branch 11
 (.branch 10
 (.leaf 0x2aa0924201068618004ca0b4020a01b800e0008000c)
 (.leaf 0x2a808f41fb07061a206000ae020c011800c0008000c))
 (.branch 12
 (.leaf 0x2a909261f4072819805fe13e82ca034000a0008000c)
 (.branch 13
 (.leaf 0x2f68aa61ee068618004c20ca8130023806e0038000c)
 (.leaf 0x2a988c61ee06d41a186000ca813003380480038000c))))
 (.branch 16
 (.branch 15
 (.leaf 0x2a909241ef06861800514110010401b801e0038000c)
 (.leaf 0x23d08041c1868e18003980bf0214011800c0008000c))
 (.branch 17
 (.leaf 0x2aa893e1e8870017e852a0ae8236033000a0010000c)
 (.branch 18
 (.leaf 0x2aa88de1e385fa151041c097814c01a00200028000c)
 (.leaf 0x3018aaa1e886dc17e853a0ae814a02480120028000c))))))
 (.branch 28
 (.branch 23
 (.branch 21
 (.branch 20
 (.leaf 0x2aa88de1e3870817e831a08e816001280320028000c)
 (.leaf 0x2ff8aaa24908021b605fa0b280ea02e00480028000c))
 (.branch 22
 (.leaf 0x30b8b7e1f98704180050a0be0190024005e0018000c)
 (.leaf 0x2a788f420106dc1a086000b2817a03080460008000c)))
 (.branch 25
 (.branch 24
 (.leaf 0x2aa0924201068218004ca0b2817a030806e0008000c)
 (.leaf 0x8041a3860015685420b2817a03080940008000b))
 (.branch 26
 (.leaf 0x93c1ef072e180058813883c20b201c8017805c0010000d)
 (.branch 27
 (.leaf 0x2ab88f41fb06dc18003020600106018804600f8000c)
 (.leaf 0x2a988f420106dc1a086000be818001180260008000c)))))
 (.branch 33
 (.branch 30
 (.branch 29
 (.leaf 0x23d07ec1c1868018003980be019802d00460008000c)
 (.leaf 0x8061a305fe16285440c4818002480260008000b))
 (.branch 31
 (.leaf 0x8041a3860015082fc0600108025007200f8000b)
 (.branch 32
 (.leaf 0x2f88b2a1e2870618004c40b381f202400140008000c)
 (.leaf 0x2aa093c1fb072e18004e20ae01da01c80120008000c))))
 (.branch 35
 (.branch 34
 (.leaf 0x2aa8924201070618004c40b401f203600140008000c)
 (.leaf 0x2aa093c1fb072e18004e208301da00980200008000c))
 (.branch 36
 (.leaf 0x2f68b781ed873018004c80b3820a07c808e0008000c)
 (.branch 37
 (.leaf 0xc5a2d489341ef05fe13d041607080f201b00660078000d)
 (.leaf 0xc542d5091c1ef05fc13d0440070010a01c80660078000d)))))))
 (.branch 57
 (.branch 47
 (.branch 42
 (.branch 40
 (.branch 39
 (.leaf 0xb2c241878a1cc85fe13282e608d01f003980de0008000d)
 (.leaf 0xb0624d87a21cb860013882b608301da03900de0008000d))
 (.branch 41
 (.leaf 0x2d489361e9072e18004e20ad820c07680c20008000c)
 (.leaf 0x2d589041e9075a17f04e210f81d8048806c0078000c)))
 (.branch 44
 (.branch 43
 (.leaf 0x2de090c1e9073217f84ca0b9823407c00ae0008000c)
 (.leaf 0x2a788f420106dc18002d008281f201e00460008000c))
 (.branch 45
 (.leaf 0x2aa88c41fb85fc139033009701d801d00660018000c)
 (.branch 46
 (.leaf 0x2aa0924201073018002d008281f201380480008000c)
 (.leaf 0x2a907be1c205fa14483180a201a8026008e0010000c)))))
 (.branch 52
 (.branch 49
 (.branch 48
 (.leaf 0x2d4895224d87a41ca86000fb01da03b00480078000c)
 (.leaf 0x2ca8aa423c87ec17e846a064013401400460080000c))
 (.branch 50
 (.leaf 0x2d509201e3060017403ea07c810402b804c0078000c)
 (.branch 51
 (.leaf 0x24908041cc060013282d008281f202d00ae0008000c)
 (.leaf 0xaa824908041cc060013282d008281f20008000b))))
 (.branch 54
 (.branch 53
 (.leaf 0x23107e61ce060013802b808301da03580d20008000c)
 (.leaf 0x26b08061cd05fe13202e808d01f003600920008000c))
 (.branch 55
 (.leaf 0x24387e61ce060013882b808301da03480ae0008000c)
 (.branch 56
 (.leaf 0x2ab08f42010706180030008401f201180260008000c)
 (.leaf 0x2d5091e1cc060013282fe08581f201f00260008000c))))))
 (.branch 66
 (.branch 61
 (.branch 59
 (.branch 58
 (.leaf 0x24907fc1cd05fe132831809001f003500260008000c)
 (.leaf 0x24908041cc0600132830008581f202d00260008000c))
 (.branch 60
 (.leaf 0x2ca88ee1e3870618003f807c80ee01180200050000c)
 (.leaf 0x2d489381e9060017583f40768104013001e0060000c)))
 (.branch 63
 (.branch 62
 (.leaf 0x201060015081f2025002200180008)
 (.leaf 0x2d5092018005d00be01f201f004c0018000a))
 (.branch 64
 (.leaf 0x24908041cc060007c813002d00480088000a)
 (.branch 65
 (.leaf 0x24387e61ce06000768132034804a0080000a)
 (.leaf 0x3098b7e23d07e41c085fe0b8819202f00460008000c)))))
 (.branch 71
 (.branch 68
 (.branch 67
 (.leaf 0x30b88f01e1875c17f053e05e811a038006c0078000c)
 (.leaf 0x2f6090e1f9876418004de0768132035806a0080000c))
 (.branch 69
 (.leaf 0x30a8b282a907e817f850a0b8819202400500008000c)
 (.branch 70
 (.leaf 0x2f50b541e2060017404f20be01f202c008e0018000c)
 (.leaf 0x3000b522a907b817f85120c481c2026008e0010000c))))
 (.branch 73
 (.branch 72
 (.leaf 0x30d0b281f40704180050a0b281aa02400500008000c)
 (.leaf 0x2f78b541ee05fc17584f20ca81c0023806e0018000c))
 (.branch 74
 (.leaf 0x30d0b2825607d01c006000b281aa02400460008000c)
 (.branch 75
 (.leaf 0x30c8b2826087e817f84e00b8819203680900008000c)
 (.leaf 0xb522a908f01e8060014a82fa07680e20010000b))))))))
 (.branch 114
 (.branch 95
 (.branch 85
 (.branch 80
 (.branch 78
 (.branch 77
 (.leaf 0x2f80b5c25587a018005280be81da037808e0010000c)
 (.leaf 0x2bf891e1f586da18005560b281aa03080480008000c))
 (.branch 79
 (.leaf 0x2ca095424d87d41c006000ac81aa03080460008000c)
 (.leaf 0xaac24f07bc1c1060014481aa03a80720078000b)))
 (.branch 82
 (.branch 81
 (.leaf 0x2e188be1ef86b417f05aa0ca81c002d80460018000c)
 (.leaf 0x2eb0a521f3076217f04fc070016202380660088000c))
 (.branch 83
 (.leaf 0x2e189aa24108061ab85fc0b8817a02f00460008000c)
 (.branch 84
 (.leaf 0x30b8b7a25407e61c006000ac81aa02400460008000c)
 (.leaf 0x30b0b7823707fe1b586000b281aa03580460008000c)))))
 (.branch 90
 (.branch 87
 (.branch 86
 (.leaf 0x3010b7a1ed872a18004c20ac01da035808e0010000c)
 (.leaf 0x2de895424f07ec1c006000ac81aa02d00460008000c))
 (.branch 88
 (.leaf 0x2de09ca20106d618004dc0b281aa03580940008000c)
 (.branch 89
 (.leaf 0x2dd89aa20186b217f85800c481c202480460010000c)
 (.leaf 0x2dd88f41fb070618005540be01f202c00460018000c))))
 (.branch 92
 (.branch 91
 (.leaf 0xc2c2e008f41ff06d817f82e207080f201b004600c8000d)
 (.leaf 0x30a0b281f4075a18005280b301aa04c00900050000c))
 (.branch 93
 (.leaf 0x2b58a521d885fe15102b6070811a024807a0048000c)
 (.branch 94
 (.leaf 0x2ca88f01d8060014a82ce07c80ea02c007a0050000c)
 (.leaf 0x2aa893c1fb070418002b8076810201d004a0048000c))))))
 (.branch 104
 (.branch 99
 (.branch 97
 (.branch 96
 (.leaf 0x2aa0924201073018002d007c80ea01c80480050000c)
 (.leaf 0x2ab88f41fb06dc18003020768106011803e0048000c))
 (.branch 98
 (.leaf 0x2d50958247872818002f807c810001f00680118000c)
 (.leaf 0x2d58aa4242070817f831007c0118026007c0118000c)))
 (.branch 101
 (.branch 100
 (.leaf 0x2cb0982235873417f82e007c0148036807a0120000c)
 (.leaf 0x2f50b542a887881c186000be01f2040008e0118000c))
 (.branch 102
 (.leaf 0x2ca88ee1c1860013302c807c813002b807a01c8000c)
 (.branch 103
 (.leaf 0x2cb08d61d805fe13302e007c014802c007a01a0000c)
 (.leaf 0x30189821e7873417f82e007c0148031808e0120000c)))))
 (.branch 109
 (.branch 106
 (.branch 105
 (.leaf 0x2f4890e1ed873818002b0076813203100a20128000c)
 (.leaf 0x2f50b7627f87e61c186000be01f2040008e0118000c))
 (.branch 107
 (.leaf 0xaa424907bc1cc06000b201f204c00c60120000b)
 (.branch 108
 (.leaf 0x2dd88f41fb070618002f807c810002c00ae0118000c)
 (.leaf 0x2dd897e1fb070618002f807c810002b80940118000c))))
 (.branch 111
 (.branch 110
 (.leaf 0x2f68b781ed873018004c20b201f204c00ae0238000c)
 (.leaf 0xaae1ef85fa139031205e0132031008e01c8000b))
 (.branch 112
 (.leaf 0x2ab89261f585fc13e82d008d81c601b803e0008000c)
 (.branch 113
 (.leaf 0xb7a26a890e1e306ae17f03c00b801de01380460010000d)
 (.leaf 0x3000b002aa880017e84dc0c4817e02480260008000c)))))))
 (.branch 133
 (.branch 123
 (.branch 118
 (.branch 116
 (.branch 115
 (.leaf 0x3000b0020005fa13703960c5017e02480400008000c)
 (.leaf 0x30a8b2e28a85fe14283be0b801f6024007a0018000c))
 (.branch 117
 (.leaf 0x30b0b30236060014883be0b201f4027007a0020000c)
 (.leaf 0x2ab89261f586da17f02d0071811a013003e0048000c)))
 (.branch 120
 (.branch 119
 (.leaf 0xc0424907b41cb05fa1260318066813a01a004800d8000d)
 (.leaf 0x2f58b541ee05fc132049a0cb01c6047808e0048000c))
 (.branch 121
 (.leaf 0x2cb09fc17e84cc128032e06b8136023807e0048000c)
 (.branch 122
 (.leaf 0x2d5890817f84e2127031607d80ee02b807c0050000c)
 (.leaf 0x2cb08d61ac85fe12802e607d80f201e80460060000c)))))
 (.branch 128
 (.branch 125
 (.branch 124
 (.leaf 0x26a87be1ac85fa128033006b8138023804a0048000c)
 (.leaf 0x23107ee1ad05fc12882e8077810a02c00460060000c))
 (.branch 126
 (.leaf 0xb4e27e89381d5860014a83960c401b001f004e0008000d)
 (.branch 127
 (.leaf 0xc8224e87ea17f858014483980be019802f00720008000d)
 (.leaf 0x2d50aa024887bc17f044007180ec012003e0078000c))))
 (.branch 130
 (.branch 129
 (.leaf 0x2d5890817f831607d813401f004a0110000a)
 (.leaf 0x2cb09081e105fe124031607d813403780c40128000c))
 (.branch 131
 (.leaf 0x2d589081e305fe12482e607d810403100ae0128000c)
 (.branch 132
 (.leaf 0x27408de1c005fa12502ba06c814c02b807a0130000c)
 (.leaf 0x27288de1b585fa12482d206c8164035807a0130000c))))))
 (.branch 142
 (.branch 137
 (.branch 135
 (.branch 134
 (.leaf 0x2d509201e3060012702ce07d014c030804c0098000c)
 (.leaf 0x25489241ca0600127031807e0104020004a0098000c))
 (.branch 136
 (.leaf 0x2d588d81e205fe127031607d8104037804a0098000c)
 (.leaf 0xc82248880217f85aa142836e0c00198034003e0008000d)))
 (.branch 139
 (.branch 138
 (.leaf 0xc5024f07ea17f058014303980c08180034803e0008000d)
 (.leaf 0x2ea8b561e205fe136831607d813402b808e0110000c))
 (.branch 140
 (.leaf 0x2ab88f41fa86d817f03020600106034804600f8000c)
 (.branch 141
 (.leaf 0x2f60aae1fa85fc13d03020600106025006600f8000c)
 (.leaf 0xc2827e880018005a814884940c601b002400260008000d)))))
 (.branch 147
 (.branch 144
 (.branch 143
 (.leaf 0xc2c254880018005a814884940c601b002480260008000d)
 (.leaf 0xc2e23d07ea1c085fc12582b8072810a02c006c0118000d))
 (.branch 145
 (.leaf 0xbb2275078a17e857e12482d206c816402600900118000d)
 (.branch 146
 (.leaf 0xbac29487d217f05d212502b8078811c025808e0120000d)
 (.leaf 0xbb226a87ee17f050c12502e807780ec02d00a20238000d))))
 (.branch 149
 (.branch 148
 (.leaf 0xc2c2c988ee1b605fe12582ce07200f201e806c0118000d)
 (.leaf 0xc022d3890818004de126031606c013401f006a0050000d))
 (.branch 150
 (.leaf 0xc2623707d21c0060012502b8077012202f80ae0118000d)
 (.branch 151
 (.leaf 0x2f80ad81fa85fa14902fe06580f0025006600f8000c)
 (.leaf 0xc2623707d21c00600125031606c00ee02f80ae0118000d)))))))))
def rawLeaves (i : Nat) : List Nat :=
  let code := leafTable.get i
  (PackedRawNatGrowth.readList 14 (PackedRawNatGrowth.take 5 code)
    (PackedRawNatGrowth.drop 5 code)).1

def leaves : Fin leafCount → List (Fin cellCount) := decodedLeaves rawLeaves
def quota : Nat → Nat
  | 0 => 1
  | 1 => 3
  | 2 => 8
  | 3 => 1
  | 4 => 0
  | 5 => 0
  | 6 => 0
  | 7 => 0
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

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0352

module
prelude
public import RootedSixBase03GrowthCacheData
public import RootedSixBase03FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification
public import RootedSubsumedForest0721Packed000
public import RootedSubsumedForest0721Packed001
public import RootedSubsumedForest0721Packed002

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0721
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 5238
abbrev nodeCount : Nat := 15427
abbrev leafCount : Nat := 180
def widths : PackedRawNatGrowth.Widths := ⟨13,14,7,8⟩
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
(.branch 90
 (.branch 45
 (.branch 22
 (.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf 0x5091fa0b7c44219f0ad842c1f60720078004000c)
 (.leaf 0x5561fb8b8844219f0ad842c1f60520078004000c))
 (.branch 3
 (.leaf 0x50b1fa0bac4421a10ad04801f40460078004000c)
 (.branch 4
 (.leaf 0x64a2788f405d82380d985682360100030004000c)
 (.leaf 0x6472850f405d42200f885682120100030004000c))))
 (.branch 8
 (.branch 6
 (.leaf 0x6492848f705bc2200ed856c17a0610088004000c)
 (.branch 7
 (.leaf 0x64727f0f105ec22c0f8856419801b0078004000c)
 (.leaf 0x6462790f105f02380ac846c1c203c0078004000c)))
 (.branch 9
 (.leaf 0x6492790f105f02380ac84c01c401b0078004000c)
 (.branch 10
 (.leaf 0x4d01ee8b444ba1cd0c605641f8041007800c000c)
 (.leaf 0x32414247e82c610f076c2e415b0028004000b)))))
 (.branch 16
 (.branch 13
 (.branch 12
 (.leaf 0x6492660fa45a825c0ae8560260041002800c000c)
 (.leaf 0x6492730f145ec2440ee056020a0230038004000c))
 (.branch 14
 (.leaf 0x5c02730be45502350b985601c203d00a8008000c)
 (.branch 15
 (.leaf 0x64a2790fd458e2360b985641c20390048004000c)
 (.leaf 0x4f224f0eb85f02390b985641c203e0048004000c))))
 (.branch 19
 (.branch 17
 (.leaf 0x4f21fa8eb85f02390b985641c20720048004000c)
 (.branch 18
 (.leaf 0x5571f58ebc5dc2210ae85681f20520050004000c)
 (.leaf 0x64927890045762360c405681c601b0048004000c)))
 (.branch 20
 (.leaf 0x5bc28611307a02c60b9056c1ae04d00f8004000c)
 (.branch 21
 (.leaf 0x5bc28491807e82c60b9056c1ae07200f8004000c)
 (.leaf 0x540278917c8062ba0c3856c1ae06100f8004000c))))))
 (.branch 33
 (.branch 27
 (.branch 24
 (.branch 23
 (.leaf 0x5c328512287d42d20af056417e05800f8004000c)
 (.leaf 0x5bd280118c89a2ba0c3856c1ae03e00f8004000c))
 (.branch 25
 (.leaf 0x5bf26e10e45ac19e0ad03b811803d00f8060000c)
 (.branch 26
 (.leaf 0x4e821c0b284d61da0d1056c1c803d00f8008000c)
 (.leaf 0x64927290005782420c3856c1ae04d0118004000c))))
 (.branch 30
 (.branch 28
 (.leaf 0x64827e900057622a0b8856c1de04f0118008000c)
 (.branch 29
 (.leaf 0x4e821c0b1448a1da0d1056c1c804801e8008000c)
 (.leaf 0x540278900c60e2430c3856c1ae02a0120004000c)))
 (.branch 31
 (.leaf 0x64a2728fd05902440b9056c1ae0390118004000c)
 (.branch 32
 (.leaf 0x142893e2ea0f8856813603f0100018000a)
 (.leaf 0x13f48002420ce056c1de0720150008000a)))))
 (.branch 39
 (.branch 36
 (.branch 34
 (.leaf 0x32493c48022ba11b06202b40cb0308004000b)
 (.branch 35
 (.leaf 0x50c21b8eb45c222d0f8056c15003f0128018000c)
 (.leaf 0x5002110eb05c42210f786282b60cc01f0004000c)))
 (.branch 37
 (.leaf 0x5411ef8b284441790ad84301f605100e8008000c)
 (.branch 38
 (.leaf 0x50c21b8fa058c21e0ed856c11e06f0268014000c)
 (.leaf 0x5bc284927858c21e0b9056c1ae06f0200004000c))))
 (.branch 42
 (.branch 40
 (.leaf 0x5bb27e8f705ba2290c3056c1f6070037800c000c)
 (.branch 41
 (.leaf 0x5bb28010885c42210c5056c20a0fb01f0004000c)
 (.leaf 0x4e825d8f445722420e2856c14e06f0218018000c)))
 (.branch 43
 (.leaf 0x50c2260f405c226b0f8056c14e03400f8018000c)
 (.branch 44
 (.leaf 0x5c1285127c5d42210ae856819603f0168004000c)
 (.leaf 0x4fd25b900057a2420e3056c11e0720118014000c)))))))
 (.branch 67
 (.branch 56
 (.branch 50
 (.branch 47
 (.branch 46
 (.leaf 0x6472848fd058e2660cd856c1f604700f800c000c)
 (.leaf 0x6422848f7058e2660cd856c1f604e00f800c000c))
 (.branch 48
 (.leaf 0x5be278928857a27c0c4056819603f0100004000c)
 (.branch 49
 (.leaf 0x6492848f705be2690c3056c1f603300f800c000c)
 (.leaf 0x64a27e0f705c022c0b9856418004501c8004000c))))
 (.branch 53
 (.branch 51
 (.leaf 0x14285da25c0f8856813803f01e0018000a)
 (.branch 52
 (.leaf 0x4da2448ec05f02510b9856018203d0170008000c)
 (.leaf 0x4fe1e20eb85f22380f8856413a070011801c000c)))
 (.branch 54
 (.leaf 0x6482848fd058e21e0c5056c1f604e0050004000c)
 (.branch 55
 (.leaf 0x541266109c59421e0c5056c1f603e0050004000c)
 (.leaf 0x5412670f7c6122200c5056c1f602a0050004000c)))))
 (.branch 61
 (.branch 58
 (.branch 57
 (.leaf 0x64a27e8f705c022c0ba856c1de0390048004000c)
 (.leaf 0x64327e8f704401f30c5056c18002a00d8004000c))
 (.branch 59
 (.leaf 0x6421ee0bd84581f20ba856c19805400d8004000c)
 (.branch 60
 (.leaf 0x6422848b1846c1f00ba856c17e0610200004000c)
 (.leaf 0x6422848f7058c1f00ba856c17e06100f8004000c))))
 (.branch 64
 (.branch 62
 (.leaf 0x64a27e8f705c022c0ba856c18003900c8004000c)
 (.branch 63
 (.leaf 0x6462848f705bc1f00ba856c18003300f8004000c)
 (.leaf 0x4fd1ee0e045ba1ef0c5056c19807200f8004000c)))
 (.branch 65
 (.leaf 0x6472850ba84541f10b0056818003f0198004000c)
 (.branch 66
 (.leaf 0x4f21d70be84881f00bb05641b003e0118004000c)
 (.leaf 0x4da1d80be84441db0bb05601e003d01a0008000c))))))
 (.branch 78
 (.branch 72
 (.branch 69
 (.branch 68
 (.leaf 0x4f11e80eac5dc2200f7862c2b40d80378004000c)
 (.leaf 0x6492848f705be18a0ad84141f603300f8004000c))
 (.branch 70
 (.leaf 0x64927290004861890ad84141ae033014800c000c)
 (.branch 71
 (.leaf 0x6462730bdc4881760ac05101ac04701e8008000c)
 (.leaf 0x6472670bb04b81b50ac051410404801e8018000c))))
 (.branch 75
 (.branch 73
 (.leaf 0x5911ee0b7c44018a0ad84141f606f02a0004000c)
 (.branch 74
 (.leaf 0x4fd1ee0b804581750ad84181de0700378004000c)
 (.leaf 0x32494247b82df11006282b610507d8004000b)))
 (.branch 76
 (.leaf 0x5d62940f7c5c022c0ba856c20c0ef0290004000c)
 (.branch 77
 (.leaf 0x5bb2788f405dc2200c585682340fa0378004000c)
 (.leaf 0xbd453d1e98bac43a20b0ad03e8152054008003c000d)))))
 (.branch 84
 (.branch 81
 (.branch 79
 (.leaf 0xc544ff1ed8b4c45c1f30ac84b813404d0208020000d)
 (.branch 80
 (.leaf 0xaae4cb1e98bb844018b0ad04681f40730358004000d)
 (.leaf 0xbac5002100b744581f70ad833011e03d00e006c000d)))
 (.branch 82
 (.leaf 0x5c226d0f1c5f422c0bb056425e0ee02a8004000c)
 (.branch 83
 (.leaf 0x5412670f7c5c42200c5056c20a0fb0308004000c)
 (.leaf 0x6421ee8b204b61750ac051018205101c8010000c))))
 (.branch 87
 (.branch 85
 (.leaf 0x64327e8f705761f30c5056c21201f0030004000c)
 (.branch 86
 (.leaf 0x6442788aec4541f40c5856823c03f0030004000c)
 (.leaf 0x6422848f7058e1750ad84201f601f00f0004000c)))
 (.branch 88
 (.leaf 0x642272900045619e0ad84201ae02900e000c000c)
 (.branch 89
 (.leaf 0x5091ee0e045c21f60c5056c21401f0030004000c)
 (.leaf 0x50a17689f84b21f50c6056818003f00e0004000c))))))))
 (.branch 135
 (.branch 112
 (.branch 101
 (.branch 95
 (.branch 92
 (.branch 91
 (.leaf 0x13f85f224d0fa856416803e009801c000a)
 (.leaf 0x27912785ea2390f805dc2b20d801f0004000b))
 (.branch 93
 (.leaf 0x4da17d0aa84521db0bb85601e004f01e8008000c)
 (.branch 94
 (.leaf 0x5091ee0e045c21f60c3056c13802400f8018000c)
 (.leaf 0x27e90005ba22d0f786342b60cc0390004000b))))
 (.branch 98
 (.branch 96
 (.leaf 0x52d27810445dc2420ac035815203f00e003c000c)
 (.branch 97
 (.leaf 0x4d01ee8b444ba1c50d085641f804e020800c000c)
 (.leaf 0x5001e20b804581780ad84181de06f0228004000c)))
 (.branch 99
 (.leaf 0x50a2518bac44218c0ad04681f404e01f8004000c)
 (.branch 100
 (.leaf 0x5001f48b8045a1780ad84181de04d0228004000c)
 (.leaf 0x4da2448be04a21770ac052419403d00e8008000c)))))
 (.branch 106
 (.branch 103
 (.branch 102
 (.leaf 0x4d91f40af04a41a30ad048019606f00d8010000c)
 (.leaf 0x6432ab13947e632d10f85641c20390148008000c))
 (.branch 104
 (.leaf 0x6462aa93947fe31812185681c0033014800c000c)
 (.branch 105
 (.leaf 0x64327f0f106882d314a056413204d00f8018000c)
 (.leaf 0x6462850fa06862d313f856813004700f801c000c))))
 (.branch 109
 (.branch 107
 (.leaf 0x2ab13947ec33115408dc2b20e10148008000b)
 (.branch 108
 (.leaf 0x50a12e05681f203f016000c0008)
 (.leaf 0x5bc28611307a02c613d856c1a804d00f8010000c)))
 (.branch 110
 (.leaf 0x5bc26d127878a2f513d85601aa06f0110004000c)
 (.branch 111
 (.leaf 0x5c126d11885f42a90ac03b40ec03d0108054000c)
 (.leaf 0x540278917c8062ba148056c1a806100f8010000c))))))
 (.branch 123
 (.branch 117
 (.branch 114
 (.branch 113
 (.leaf 0x2730ec45f22380ee05601c807901e806c000b)
 (.leaf 0x32395549b23fe15c893c2b60ec0308010000b))
 (.branch 115
 (.leaf 0x5c227f0be449a1740ac832816803e00e8054000c)
 (.branch 116
 (.leaf 0x5c226d0be84521750ac03b816004f01e8054000c)
 (.leaf 0x14287d02eb15485681f2072010000c000a))))
 (.branch 120
 (.branch 118
 (.leaf 0x13f89462f70ac83b816003e010804c000a)
 (.branch 119
 (.leaf 0x324939878a2f714a09042b00d50268004000b)
 (.leaf 0x32393f48002bb15388ac2b60ec01c8010000b)))
 (.branch 121
 (.leaf 0x64826d0be049a1720ac032816804701e8074000c)
 (.branch 122
 (.leaf 0x4ff21110007602f711685641da04f0118008000c)
 (.leaf 0x4e62450bd848a1dc0ac03900ec04d01e806c000c)))))
 (.branch 129
 (.branch 126
 (.branch 124
 (.leaf 0x5c327312285ec2450ac03840ec04d01e8054000c)
 (.branch 125
 (.leaf 0x5bc26c8fa05ac2a910f85681f206f01d000c000c)
 (.leaf 0x6492730bd84881dc0ac03900ec04701e806c000c)))
 (.branch 127
 (.leaf 0x51827f0f1875e2f912805601920640118004000c)
 (.branch 128
 (.leaf 0x540278900c57a292121856c1a806101c8010000c)
 (.leaf 0x5c027311d45ec2440ac03840ec07201e8054000c))))
 (.branch 132
 (.branch 130
 (.leaf 0x5572668f987542d611585681f206f031000c000c)
 (.branch 131
 (.leaf 0x13cc8022f80ac83881620440110048000a)
 (.leaf 0x64a26c8fa05a824d0ad032c11a04e0268040000c)))
 (.branch 133
 (.leaf 0x64a26d0f745be24e0ac032813004e0268040000c)
 (.branch 134
 (.leaf 0x4da25d8f745be24e0ac03281300700378040000c)
 (.leaf 0x4d925d8fa05a824d0ad032c11a0700378040000c)))))))
 (.branch 157
 (.branch 146
 (.branch 140
 (.branch 137
 (.branch 136
 (.leaf 0x4da25d0f745c225a0ac02f8132071030803c000c)
 (.leaf 0x4db25c90045ea2510ed85601e00760210070000c))
 (.branch 138
 (.leaf 0x54027e92e48042bd12705681960750310040000c)
 (.branch 139
 (.leaf 0x52b2848fd866225b0ac82fc11a04e015803c000c)
 (.leaf 0x5972680f744b61cd0ac83e011c041015803c000c))))
 (.branch 143
 (.branch 141
 (.leaf 0x64a26c8fa05a82500ad032c0ea04d01d0040000c)
 (.branch 142
 (.leaf 0x4d925d8fa05782520ad032c11a06f01d0040000c)
 (.leaf 0x6422848f7058e19b0ad83ec10004e026807c000c)))
 (.branch 144
 (.leaf 0x6472848fd058e19b0ad83ec10004d023807c000c)
 (.branch 145
 (.leaf 0x28491907e82c70cd856c1f6080039007c000b)
 (.leaf 0x55526c91888063030ce056c1de074014807c000c)))))
 (.branch 151
 (.branch 148
 (.branch 147
 (.leaf 0x52d2790f186902440ac035815202b00e003c000c)
 (.leaf 0x64927290004841870ad835c0ea04d01980a4000c))
 (.branch 149
 (.leaf 0x4fd1ee0b804521710ad83bc1320700378134000c)
 (.branch 150
 (.leaf 0x32394247e82c710f066c2b60fb0400134000b)
 (.leaf 0x5bb27e8f705c421d0c3056c1f60980380134000c))))
 (.branch 154
 (.branch 152
 (.leaf 0xa824ce1ef8b8843a20c0ad83ec13a061008803c000d)
 (.branch 153
 (.leaf 0xaae4cd1f58b5843c2050ad03e81220620268040000d)
 (.leaf 0xa184371f40b784421f00ad830011e0730268070000d)))
 (.branch 155
 (.leaf 0xa004221f48b7445a1f70ad833011e04d00e006c000d)
 (.branch 156
 (.leaf 0x55526c900c57c22a0ce056c1de0740308134000c)
 (.leaf 0x4fd1ee0aec45c1710ad83bc13207002680e4000c))))))
 (.branch 168
 (.branch 162
 (.branch 159
 (.branch 158
 (.leaf 0xaae4d72448f1c5ea2060ac83b811c06b011003c000d)
 (.leaf 0x642272900045419c0ad835c0ee04d0148070000c))
 (.branch 160
 (.leaf 0xaae4d71e38be845220a0ac83b816a06b008003c000d)
 (.branch 161
 (.leaf 0x64a27f0fa45a622a0ac83b812204d00e003c000c)
 (.leaf 0x64a2788f405d82380ad038c0f203a00d8040000c))))
 (.branch 165
 (.branch 163
 (.leaf 0xaae4cb1e98bb84402050ad03e812206b01d0040000d)
 (.branch 164
 (.leaf 0x6482848fd058e1720ad83ec10a04700f8074000c)
 (.leaf 0x6472850f405d41f10ad030010603300f806c000c)))
 (.branch 166
 (.leaf 0x4f21fa8b1c46c1730ac838810a070037806c000c)
 (.branch 167
 (.leaf 0x32393648022bc12706742b40cb03c006c000b)
 (.leaf 0x4fe1e20b4845c1c70ac8334134070026806c000c)))))
 (.branch 174
 (.branch 171
 (.branch 169
 (.leaf 0x4e72078fcc5d42460e385601ca082036006c000c)
 (.branch 170
 (.leaf 0x64127e90005c01890ad83bc13802100e006c000c)
 (.leaf 0x5092300fd075e2c70ad83e0148072011807c000c)))
 (.branch 172
 (.leaf 0x6412850fa05d627f0ad03e410004d01d8080000c)
 (.branch 173
 (.leaf 0xa123f41cd056c1f00a401580800009)
 (.leaf 0x2850fa07362210ad03e410004d01c80b0000b))))
 (.branch 177
 (.branch 175
 (.leaf 0x278900470c2bb0ad038016206f01c8088000b)
 (.branch 176
 (.leaf 0x14247e82df0ad83e014807201e0080000a)
 (.leaf 0x32513f87d22d311505641da07402680e8000b)))
 (.branch 178
 (.leaf 0x4e525910005902450ad835014807101d00e4000c)
 (.branch 179
 (.leaf 0x32513f47b82e0116056c1d808c01d00e4000b)
 (.leaf 0x32513f87d22d311585641da09901d00e4000b)))))))))
def rawLeaves (i : Nat) : List Nat :=
  let code := leafTable.get i
  (PackedRawNatGrowth.readList 13 (PackedRawNatGrowth.take 5 code)
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

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0721

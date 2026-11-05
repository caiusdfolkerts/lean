module
prelude
public import RootedSixBase01GrowthCacheData
public import RootedSixBase01FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification
public import RootedSubsumedForest0354Packed000
public import RootedSubsumedForest0354Packed001
public import RootedSubsumedForest0354Packed002

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0354
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 15246
abbrev nodeCount : Nat := 16186
abbrev leafCount : Nat := 156
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
(.branch 78
 (.branch 39
 (.branch 19
 (.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf 0xaa41fb86a019d85fc14502e204080900028000b)
 (.leaf 0xaaa24f07ec1c9862e18004ec0ac800a0008000b))
 (.branch 3
 (.leaf 0xb742a989381f6862e18004fa0ac800a0008000b)
 (.leaf 0xaac1f5860617f04ca116833804780900028000b)))
 (.branch 6
 (.branch 5
 (.leaf 0xb6c2aa0922202860617f02ca03a80480028000b)
 (.leaf 0x7a618385fa17d04e41210338055808e0030000b))
 (.branch 7
 (.leaf 0xb40236880818e05fa16a032605680460030000b)
 (.branch 8
 (.leaf 0xb1823c87f218405fa133030c05000b00038000b)
 (.leaf 0x7ee1a305fc14b033e05c809000380009)))))
 (.branch 14
 (.branch 11
 (.branch 10
 (.leaf 0x2e70952251880e1ca863e18002ca03a80480028000c)
 (.leaf 0xc1c2c60aaa25087f217e84dc0ac800a0008000b))
 (.branch 12
 (.leaf 0xaaa1e985fa133045a0ce0250057008e0028000b)
 (.branch 13
 (.leaf 0xb402aa88da20205fa10c832203b80460028000b)
 (.leaf 0x2e0099e251080c1cb05fe13402e205e80600008000c))))
 (.branch 16
 (.branch 15
 (.leaf 0xb8c1e9876817e84e40cf01d805c008e0168000b)
 (.leaf 0xc202a688fa1f786b217f84940c6818004780600118000d))
 (.branch 17
 (.leaf 0xc2a2bf897420485fc13404920cd81ae04180920168000d)
 (.branch 18
 (.leaf 0x23d07ec1c186a618004b80e101cc04280460080000c)
 (.leaf 0x23987ae1c206a217f84940ad81e404880c20118000c))))))
 (.branch 29
 (.branch 24
 (.branch 21
 (.branch 20
 (.leaf 0x30808fa1ff06b21a905fe12502e807980f20118000c)
 (.leaf 0x23108621ad06a017f04920bb81fe042807c0118000c))
 (.branch 22
 (.leaf 0xbdc242879c19d05fa14d84900c001fc05500de01a8000d)
 (.branch 23
 (.leaf 0xaa820106a8180052a0b401ce03b009400f8000b)
 (.leaf 0xab21e3876817e84e40c801e8058008e0168000b))))
 (.branch 26
 (.branch 25
 (.leaf 0x2e189aa24507dc1ab85fc0ca01bc04b005a0118000c)
 (.leaf 0xaac1f5860817f04ca0ce0200046009001d8000b))
 (.branch 27
 (.leaf 0x8e621287ae19985fe13f01ee05780680080000b)
 (.branch 28
 (.leaf 0x31b88e61eb873e17f84f80ad823607080c20008000c)
 (.leaf 0x99e251080c1cd05fe13402e808d01f00008000b)))))
 (.branch 34
 (.branch 31
 (.branch 30
 (.leaf 0x24b88361fd86da18005140b5020a06a80c40018000c)
 (.leaf 0x31b08c4218873c17f04e00bb825e076007c0008000c))
 (.branch 32
 (.leaf 0x2d189341f0870417f852a0e1024c064801e0010000c)
 (.branch 33
 (.leaf 0x2dc09341fc874c17f853407080200010000a)
 (.leaf 0x3008b922d9899624c85fe13802b2064807c0008000c))))
 (.branch 36
 (.branch 35
 (.leaf 0x2d1897c24d07c21db874217f819203a80480078000c)
 (.leaf 0x3128b462a8092a1f086b017f819203a80480078000c))
 (.branch 37
 (.leaf 0x3128b9c24a88501ff06b017f819203a80480078000c)
 (.branch 38
 (.leaf 0x2e50b6829089061f186b017f819203a80480078000c)
 (.leaf 0x3298b38241885e1fe86b017f819203a80480078000c)))))))
 (.branch 58
 (.branch 48
 (.branch 43
 (.branch 41
 (.branch 40
 (.leaf 0x2dd09361f6872e18001da04c804a0080000a)
 (.leaf 0x31d0b2024787921c5060014401aa03a80720078000c))
 (.branch 42
 (.leaf 0x2b509481fa877817f859415182b206480e40008000c)
 (.leaf 0x2b509e825207ea1b485fe13502b206480e40008000c)))
 (.branch 45
 (.branch 44
 (.leaf 0x32b0b0e24d87d21c9860013b02b206a80ae0008000c)
 (.leaf 0x3298b3824687e817f858014602e206480720008000c))
 (.branch 46
 (.leaf 0x2d18a9a24587c21d685fe14b0192046806c0078000c)
 (.branch 47
 (.leaf 0xab0243878c1d985fc151017a046806c0078000b)
 (.leaf 0xb6c2aa092220285fc13282ca05e80c20008000b)))))
 (.branch 53
 (.branch 50
 (.branch 49
 (.leaf 0x96c23f87c61c3860014601aa03a80720078000b)
 (.leaf 0x3138b4a24487aa1d6860014a01aa04080540078000c))
 (.branch 51
 (.leaf 0x3130b7a24407e61c9860013b02b206a80ae0008000c)
 (.branch 52
 (.leaf 0xb462ab093a1f085fe144819203a80720078000b)
 (.leaf 0x2dd094a1f6860015201da04c80780080000a))))
 (.branch 55
 (.branch 54
 (.leaf 0x2de89c824b07f41cb05fc13a02e205e80720008000c)
 (.leaf 0x2de892c1fd06b017f05c615402e205e80dc0008000c))
 (.branch 56
 (.leaf 0x2e30946203876818004e20b281da03c807000c8000c)
 (.branch 57
 (.leaf 0x2dc09481fc875e17f85460ad019205280c20048000c)
 (.leaf 0xab21e3076817f052c0b4817a05880900050000b))))))
 (.branch 68
 (.branch 63
 (.branch 60
 (.branch 59
 (.leaf 0x2dd094a1f6875e18005480ae01da04080ae0048000c)
 (.leaf 0x2bf893220d876418005300b501aa04c007c0050000c))
 (.branch 61
 (.leaf 0x2c788ee1e406dc180030208a81da04500ae0118000c)
 (.branch 62
 (.leaf 0x97e251080c1c285fe0c6025807c00fc0118000b)
 (.leaf 0x3058a261ff071217f831809601f003f008e0118000c))))
 (.branch 65
 (.branch 64
 (.leaf 0xaa81e385fa139031a0a9017805d008e01c8000b)
 (.leaf 0x26009161f786ac17f84300c8019204780c20118000c))
 (.branch 66
 (.leaf 0x8fe1f1860013302d208981aa05100ae01a8000b)
 (.branch 67
 (.leaf 0x3270b5e22f87b81ad05fc0cb027e070012c0118000c)
 (.leaf 0x2e708c621406b417e832c0aa0190057007a0120000c)))))
 (.branch 73
 (.branch 70
 (.branch 69
 (.leaf 0x2ca89021d88600140040e0b001f204e807a0138000c)
 (.leaf 0x3080b7623e87fc1ac85fe0c50254070812c0118000c))
 (.branch 71
 (.leaf 0x23307941d785fa14b04880c8019005a00c20198000c)
 (.branch 72
 (.leaf 0x24b87f61b6860014504060c201aa04200c401c8000c)
 (.leaf 0x2b608be22186b417f033409f81c004b007a0118000c))))
 (.branch 75
 (.branch 74
 (.leaf 0x2548946203876c1d006000b281aa03a80c60120000c)
 (.leaf 0x3280b6224087a018005000be81da03a00ae01d0000c))
 (.branch 76
 (.leaf 0x2dd8946203872618004ec0be81da03a00ae01d0000c)
 (.branch 77
 (.leaf 0x2e808c421506b417f04fc0cf81c005c807c01d8000c)
 (.leaf 0x2d589061cc85fe0c901f0056007c0120000a))))))))
 (.branch 117
 (.branch 97
 (.branch 87
 (.branch 82
 (.branch 80
 (.branch 79
 (.leaf 0x3280b6223b879e1b706000b101da03e00c20118000c)
 (.leaf 0x2c0896a24607a21b785fc0bd01d804a00de0118000c))
 (.branch 81
 (.leaf 0x2c08a16239076417e85120c901a8056007c01a0000c)
 (.leaf 0x2f38b2c232076217f85100bd01f004a007a0138000c)))
 (.branch 84
 (.branch 83
 (.leaf 0x2ec8b7a1e187461c705fc0bd01d804a008e0118000c)
 (.leaf 0x2de89501e387461c705fa0c901a8056008e0120000c))
 (.branch 85
 (.leaf 0x24b87f61cc06000c301f205000c80120000a)
 (.branch 86
 (.leaf 0x2d588ea1e2075e17f84e80c901f005600de0138000c)
 (.leaf 0x2e0892e1fd873018004ca0b701f2044008201c8000c)))))
 (.branch 92
 (.branch 89
 (.branch 88
 (.leaf 0x2f48ad81ee85fc16705380b701c0044009401c8000c)
 (.leaf 0x3270b5e23b87881c18600133030c07c814001c8000c))
 (.branch 90
 (.leaf 0x2b608ec1fa86f417e85340c3019005000e001c8000c)
 (.branch 91
 (.leaf 0x2dd892e1fd870618004c60c301f205000d801c8000c)
 (.leaf 0x2e288bc1f5876617e85140cf01a805c00b60198000c))))
 (.branch 94
 (.branch 93
 (.leaf 0x2c588bc1fc076017e852c0cf819005c80c60198000c)
 (.leaf 0x2de89be1ef86b217e85460c98178056808e01e0000c))
 (.branch 95
 (.leaf 0x2e308d21e985fc13404a60cb81de04180b60048000c)
 (.branch 96
 (.leaf 0x2d0890020285fa13f84a00bf017e05900c20058000c)
 (.leaf 0xab21e985fa13304a60cc8196053808e0048000b))))))
 (.branch 107
 (.branch 102
 (.branch 99
 (.branch 98
 (.leaf 0x2d209021ea060014004a00c001f403b80ae0058000c)
 (.leaf 0x2b608d222185fc13404a00cd01c6047807a0048000c))
 (.branch 100
 (.leaf 0x24f07ec1d40600162051c12303a00c201b00008000c)
 (.branch 101
 (.leaf 0x30808fa1ff06b217f84600bc81c803c804600f8000c)
 (.leaf 0x24b07f41ad05fc13d04360bc81ca04280d800f8000c))))
 (.branch 104
 (.branch 103
 (.leaf 0x23f07c41d885fa150845c0ce818204e006a00f8000c)
 (.leaf 0xaac1ef85fa133045c0ce818204d808e00f8000b))
 (.branch 105
 (.leaf 0x2dd09381f68780180056c14a83960c401b00008000c)
 (.branch 106
 (.leaf 0x2c809201e4875c18004fa0f902e007e01400138000c)
 (.leaf 0x3288b3423087e817e83de0cf819603b804600f8000c)))))
 (.branch 112
 (.branch 109
 (.branch 108
 (.leaf 0xb422ab08f220285fa0c0019603b804600f8000b)
 (.leaf 0x2fe08c822e87b81800522126830607d011c0098000c))
 (.branch 110
 (.leaf 0x3138912200060016a052212f835a0c601b00008000c)
 (.branch 111
 (.leaf 0xbae2da88081c705fc15284940c5018004800920198000d)
 (.leaf 0x30107ca1d406ca18004940bb81e003c808e0118000c))))
 (.branch 114
 (.branch 113
 (.leaf 0x30a0a1c23388121b58600124833606c01060118000c)
 (.leaf 0x2f509fe1fe872418004ea124031e07e01340238000c))
 (.branch 115
 (.leaf 0x2f687ca1ca060013b84920bb81f804300d60238000c)
 (.branch 116
 (.leaf 0x30908e220486dc180049e0cd81e004180460048000c)
 (.leaf 0x30b08121b68600148049a0cd81b004f80920048000c)))))))
 (.branch 136
 (.branch 126
 (.branch 121
 (.branch 119
 (.branch 118
 (.leaf 0x2fe88ca1fe8706180049e0c781f804280460098000c)
 (.leaf 0x2f687ca1cc060013204bc0bb822007e008e0008000c))
 (.branch 120
 (.leaf 0x2a988c41f4074a1bc85fe0ce020004600d00118000c)
 (.leaf 0xc242aa88e220006dc180032207a80e80118000b)))
 (.branch 123
 (.branch 122
 (.leaf 0x2ec0a9e1e8074a1bc85fe0ce0200046008e0118000c)
 (.leaf 0xb2c2ab08c21f405fa0ca01bc04b00de0118000b))
 (.branch 124
 (.leaf 0xab0231876617e85140bc01b8058007a0198000b)
 (.branch 125
 (.leaf 0xaa8249073018004ca0ce8202040008001c8000b)
 (.leaf 0x9c023106e417f05480b0818a040807c01d8000b)))))
 (.branch 131
 (.branch 128
 (.branch 127
 (.leaf 0xaae23d86f417e85340b601a004c007a01c8000b)
 (.leaf 0x2ec0aae1e806f617f85020c281d2052808e01b0000c))
 (.branch 129
 (.leaf 0x2ca8aa023c060014a840e0b002a6081807a0010000c)
 (.branch 130
 (.leaf 0x2aa08c21fb85fa13904860ce822e06300b60018000c)
 (.leaf 0x24b87f61cc0600121820204e80480080000a))))
 (.branch 133
 (.branch 132
 (.leaf 0x2f48b2a1e2860016685360b3827c08180900008000c)
 (.leaf 0x2cb09061e286d217f84d40b9827a08100de0008000c))
 (.branch 134
 (.leaf 0x2bd08d61e4075e17f84cc121020005480680080000c)
 (.branch 135
 (.leaf 0xaaa24f07ec1c9860013b02b809481ee0008000b)
 (.leaf 0xb6e2a909081fc05fe13882e809e82040008000b))))))
 (.branch 146
 (.branch 141
 (.branch 138
 (.branch 137
 (.leaf 0x2bd08d61e406b217f83160a9020403a00c80118000c)
 (.leaf 0x2ca8a3e24b86da18002ce09f020603a807a0120000c))
 (.branch 139
 (.leaf 0x2e008fe1f186dc18002fe0a9820603a00820118000c)
 (.branch 140
 (.leaf 0x3050b521e8071018002fc0aa81ee040008e0118000c)
 (.leaf 0x2f38b2c23205fe14402e609e820403a807a01c8000c))))
 (.branch 143
 (.branch 142
 (.leaf 0x2d588ea1e205fe13a03160a9020403a00de01c8000c)
 (.leaf 0x23387961d785fc13904880b201e805a80c20198000c))
 (.branch 144
 (.leaf 0x312892a1ff06b817f83180a9020403a00960118000c)
 (.branch 145
 (.leaf 0x2a408c420306b817f83180a9020403a00d00118000c)
 (.leaf 0x256894620386e218003000a9820603a00dc0118000c)))))
 (.branch 151
 (.branch 148
 (.branch 147
 (.leaf 0xaac1ef85fa133033009f81bc04c008e01c8000b)
 (.leaf 0x30a08f420406e017f03340ab01d404600bc0118000c))
 (.branch 149
 (.leaf 0xc2629088fe1f3870a17f84840ae023a08000460008000d)
 (.branch 150
 (.leaf 0xcae2ee88f21ff05fe132048e0ba023c074806c0008000d)
 (.leaf 0x946203872e18004e212282d008501ea0008000b))))
 (.branch 153
 (.branch 152
 (.leaf 0x251880e1cb8600138848a0b401ea03c807200f8000c)
 (.leaf 0x23f87c61d88600133045c0ae820204e806a00f8000c))
 (.branch 154
 (.leaf 0xaa61f505fe15102b80ab81d604700920100000b)
 (.branch 155
 (.leaf 0x2550946203870018004600c001ba03b804600f8000c)
 (.leaf 0x2de08fe1f186dc18002ce0a9820603c804600f8000c)))))))))
def rawLeaves (i : Nat) : List Nat :=
  let code := leafTable.get i
  (PackedRawNatGrowth.readList 14 (PackedRawNatGrowth.take 5 code)
    (PackedRawNatGrowth.drop 5 code)).1

def leaves : Fin leafCount → List (Fin cellCount) := decodedLeaves rawLeaves
def quota : Nat → Nat
  | 0 => 1
  | 1 => 2
  | 2 => 5
  | 3 => 5
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

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0354

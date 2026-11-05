module
prelude
public import RootedSixBase01GrowthCacheData
public import RootedSixBase01FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification
public import RootedSubsumedForest0320Packed000
public import RootedSubsumedForest0320Packed001
public import RootedSubsumedForest0320Packed002
public import RootedSubsumedForest0320Packed003
public import RootedSubsumedForest0320Packed004
public import RootedSubsumedForest0320Packed005
public import RootedSubsumedForest0320Packed006
public import RootedSubsumedForest0320Packed007

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0320
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 15246
abbrev nodeCount : Nat := 47122
abbrev leafCount : Nat := 192
def widths : PackedRawNatGrowth.Widths := ⟨14,16,6,8⟩
def blocks : Table PackedRawNatGrowth.Block :=
(.branch 200
 (.branch 100
 (.branch 50
 nodeBlocks000
 nodeBlocks001)
 (.branch 150
 nodeBlocks002
 nodeBlocks003))
 (.branch 300
 (.branch 250
 nodeBlocks004
 nodeBlocks005)
 (.branch 350
 nodeBlocks006
 nodeBlocks007)))
def counterTable : Table Nat :=
(.branch 200
 (.branch 100
 (.branch 50
 nodeCounters000
 nodeCounters001)
 (.branch 150
 nodeCounters002
 nodeCounters003))
 (.branch 300
 (.branch 250
 nodeCounters004
 nodeCounters005)
 (.branch 350
 nodeCounters006
 nodeCounters007)))
def codes (i : Nat) : Nat :=
  let b := blocks.get (i / 128)
  PackedRawNatGrowth.drop
    (PackedRawNatGrowth.take 32 (PackedRawNatGrowth.drop (32*(i%128)) b.offsets)) b.payload
def counters (i : Nat) : Nat :=
  PackedRawNatGrowth.take 55 (PackedRawNatGrowth.drop (55*(i%128)) (counterTable.get (i/128)))
def rawNodes (i : Nat) := PackedRawNatGrowth.decodeNode widths (codes i)

def leafTable : Table Nat :=
(.branch 96
 (.branch 48
 (.branch 24
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf 0x251880e1a3860014482fa01c000c0010000a)
 (.branch 2
 (.leaf 0x8c41fb868c17f058a0cf817201980460038000b)
 (.leaf 0x7ee1a305fc14b033e05c809000380009)))
 (.branch 4
 (.leaf 0x1d460c3e27e87fe19b860013502ca024000a0008000c)
 (.branch 5
 (.leaf 0x8821f5868e17f05ba14501aa024001e0008000b)
 (.leaf 0x7ec18e860014a830c0640140030809401c8000b))))
 (.branch 9
 (.branch 7
 (.leaf 0x8881e305fc132833606b8106024005a0108000b)
 (.branch 8
 (.leaf 0x73382e287be17e833e07180f8023805a0118000b)
 (.leaf 0x78c19d85fc13282e607f810a024005a0108000b)))
 (.branch 10
 (.leaf 0x1fb86a017f05140ef81fe02400240018000a)
 (.branch 11
 (.leaf 0x7881a805fc130831607f813a032808e0110000b)
 (.leaf 0x7a618285fa17784cc0ce020002b808e0020000b)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf 0x78c18485fc16d04ca0ce020002400840020000b)
 (.branch 14
 (.leaf 0x78c18f05fc132845c080810a02400760078000b)
 (.leaf 0x63a17e84cc12182b0080813a023807a01e0000b)))
 (.branch 16
 (.leaf 0x1d008ab023185fa14502f0074016601e80660168000c)
 (.branch 17
 (.leaf 0x72f82e307a617e832e07b0114023805a0118000b)
 (.leaf 0x73b82e087a617e85720cf01ec023805a0118000b))))
 (.branch 21
 (.branch 19
 (.leaf 0x1cee0bb02e0879c17e85200cf01ec02480660168000c)
 (.branch 20
 (.leaf 0x251880e18005120c001f201c00180010000a)
 (.leaf 0x1d970b6c290875817f04ca0b581c002400140008000c)))
 (.branch 22
 (.leaf 0x7ee17f05be14b033009b81d802400280008000b)
 (.branch 23
 (.leaf 0x2dc093a1fc85fe17501c201280200010000a)
 (.leaf 0xb6a242884c20205fc132817a02d001e0008000b))))))
 (.branch 36
 (.branch 30
 (.branch 27
 (.branch 25
 (.leaf 0x2dc093a1fc85fe14481c202d00200010000a)
 (.branch 26
 (.leaf 0x201060015081f2025002200180008)
 (.leaf 0x2dd09361f6872e18001da04c804a0080000a)))
 (.branch 28
 (.leaf 0x251880e1cd860007c813002700480088000a)
 (.branch 29
 (.leaf 0x2d88a8817f85120c481c202480800010000a)
 (.leaf 0x1da80b0a238073e18005520ac01da01e804a0010000c))))
 (.branch 33
 (.branch 31
 (.leaf 0xab21e3076817f052c05e810202400580078000b)
 (.branch 32
 (.leaf 0x7a417f859c13882ea064815602480400048000b)
 (.leaf 0x7a417f84e20ba8250064815c02c00920138000b)))
 (.branch 34
 (.leaf 0x78e17e85600c682a405e017402d008e0118000b)
 (.branch 35
 (.leaf 0x1da60b5e232871018002f807c810002b807c0118000c)
 (.leaf 0x2d589061cc85fe0c901f0056007c0120000a)))))
 (.branch 42
 (.branch 39
 (.branch 37
 (.leaf 0x1f585fc145033c0760170032009001e0000a)
 (.branch 38
 (.leaf 0x1d970b6c29085fc13284960b581c602400120008000c)
 (.leaf 0x2db092220285fc0f081c601200220010000a)))
 (.branch 40
 (.leaf 0x2d5890a17f03dc0cf01de01f80480010000a)
 (.branch 41
 (.leaf 0x7a617e84cc116837a0ce018202c808e0010000b)
 (.leaf 0xb6c248880a17f04ca0be818002d00260008000b))))
 (.branch 45
 (.branch 43
 (.leaf 0x8c41fb85fc0f7833e07180e803200660118000b)
 (.branch 44
 (.leaf 0x76682d08a3e17e84960c1819603b808e0118000b)
 (.leaf 0xab01ef85fa129033006b80ee023804600b0000b)))
 (.branch 46
 (.leaf 0xb8a1ef85fa129032c05f811e023804600e0000b)
 (.branch 47
 (.leaf 0x8b21e205fc13083360778136032808e0110000b)
 (.leaf 0x1d988b1a23906aa17f04900cd81de04e00ca0128000c)))))))
 (.branch 72
 (.branch 60
 (.branch 54
 (.branch 51
 (.branch 49
 (.leaf 0x17f85440ce0200024807e00200008)
 (.branch 50
 (.leaf 0x243073217f8338080014802d007e0120000a)
 (.leaf 0x24f0736180033a080813002700800120000a)))
 (.branch 52
 (.leaf 0x1f505fe1448484080015202480780080000a)
 (.branch 53
 (.leaf 0x20185fe14483180a9020402d00920010000a)
 (.leaf 0x1caf0b5624287a417f056c11501ec012001e0008000c))))
 (.branch 57
 (.branch 55
 (.leaf 0x1cfb0ab2237080617f84cc0c881a201a00120010000c)
 (.branch 56
 (.leaf 0x73f02ac87ee17f04ca0ce818a02400280008000b)
 (.leaf 0x72f82ac87a617e8332069015c023804e0118000b)))
 (.branch 58
 (.leaf 0x72fa2ac08c41f585fc0cc81d404b00660118000b)
 (.branch 59
 (.leaf 0x73f82ac07be17e833a0620136023804e0118000b)
 (.leaf 0x1cfe0ab01ef85fa133033a06201360238000a)))))
 (.branch 66
 (.branch 63
 (.branch 61
 (.leaf 0x73f02ac88c41fb85fc0ce818a04180660118000b)
 (.branch 62
 (.leaf 0x74001e3076817f04ca0b601e805a80900140000b)
 (.leaf 0x1cbe0b8c22f87a617f032e07b011402d80660118000c)))
 (.branch 64
 (.leaf 0x1cbe8b8a23087d617e832e06f014402d804e0118000c)
 (.branch 65
 (.leaf 0x1d0007861da05fc13902d807a016a032808e0198000c)
 (.leaf 0x1d00878e1d985fa145030806e016a025808e0198000c))))
 (.branch 69
 (.branch 67
 (.leaf 0x1cee0bac2d587a017f05720cf01ec02380660118000c)
 (.branch 68
 (.leaf 0x1d3a0c2c23708121ad860007a814201b80500118000c)
 (.leaf 0x1d3c07e21cc85fe080015803400900120000a)))
 (.branch 70
 (.leaf 0x1d380bda1f2873018004c80808110039808e01c8000c)
 (.branch 71
 (.leaf 0x1d380c041f2873618004c80808110035808e01c8000c)
 (.leaf 0x74f02eb87e21d785fe1318200056009001a0000b))))))
 (.branch 84
 (.branch 78
 (.branch 75
 (.branch 73
 (.leaf 0x74f02ed87e21cc85fe130820005600a20238000b)
 (.branch 74
 (.leaf 0x1d1b0bae26a87cc18985fc0ce012c02480660118000c)
 (.leaf 0x1d1b0bac29487cc18985fc0ce012c02380660118000c)))
 (.branch 76
 (.leaf 0x746c2ab08c41f5862617f033804b00660118000b)
 (.branch 77
 (.leaf 0x74782aa07a618885fa0ce015c023804e0118000b)
 (.leaf 0x74601f5062a17f84e20c8012c02c00ae0248000b))))
 (.branch 81
 (.branch 79
 (.leaf 0x1d1e0aa81e9862217e84cc0ce015c0238000a)
 (.branch 80
 (.leaf 0x7714202854c0c281d2025005400100009)
 (.leaf 0x1dc5083c202854c0af81c4041009400f8000a)))
 (.branch 82
 (.leaf 0x1dc5080a18a854c0bf0186042009400f8000a)
 (.branch 83
 (.leaf 0x7714202854c0c38142025006000300009)
 (.leaf 0x1dc58aa823708081d1832207a80e803580660118000c)))))
 (.branch 90
 (.branch 87
 (.branch 85
 (.leaf 0x1dc109aa1f686ca12a83d6060011e02480460080000c)
 (.branch 86
 (.leaf 0x770e2f288e01fc074a12482e807e010402c00a20128000d)
 (.leaf 0x1dc5890c20207460c881ea02d00480010000a)))
 (.branch 88
 (.leaf 0x1dc508f4202871e12e03840c0019802d00460008000c)
 (.branch 89
 (.leaf 0x1dc5092420287480f081c801200220010000a)
 (.leaf 0x1dc508f4202871e18a83980bf0186011803e0008000c))))
 (.branch 93
 (.branch 91
 (.leaf 0x1dc50aac23d080a1c7862a0be818601180260008000c)
 (.branch 92
 (.leaf 0x1dc50aac23d080a1c782b808a01d602200460008000c)
 (.leaf 0x77142ab08f4202871e0c281d203a00720118000b)))
 (.branch 94
 (.leaf 0x1dc508f4202871e12b03d806600ee02c00460088000c)
 (.branch 95
 (.leaf 0x1dc30aae23d07f21bd04060c2010601680460028000c)
 (.leaf 0x1dc50b6c2aa092015302b808a01d601f00500008000c))))))))
 (.branch 144
 (.branch 120
 (.branch 108
 (.branch 102
 (.branch 99
 (.branch 97
 (.leaf 0x1dc508f4202871e18603fe0e600f201180220030000c)
 (.branch 98
 (.leaf 0x770c2ab88f41fc86f40c0822a04500460030000b)
 (.leaf 0x1dc30b182ab88f014d02d8068013001e80720168000c)))
 (.branch 100
 (.leaf 0x771423d080a1c7855e0c281d202c80460010000b)
 (.branch 101
 (.leaf 0x1dc50be828d080a1c784c40e6019802400220008000c)
 (.leaf 0x1dc58bb02aa08081d184c20c881ea029008e0010000c))))
 (.branch 105
 (.branch 103
 (.leaf 0x77162ab090c202071c13102f206e80d60008000b)
 (.branch 104
 (.leaf 0x76fc2d18aa424807d014102ca039000a0008000b)
 (.leaf 0x77142aa0924202874813282da06880720008000b)))
 (.branch 106
 (.leaf 0x76fc2ab093c1f0872214480ea01c801e0028000b)
 (.branch 107
 (.leaf 0x77062f58b721f2851a12482ee07d810402b80960238000d)
 (.leaf 0x1dc38b6e23007b214c84920b581f404700de02c0000c)))))
 (.branch 114
 (.branch 111
 (.branch 109
 (.leaf 0x1dc50bfa2db08ca1c784960bf819803b807c0118000c)
 (.branch 110
 (.leaf 0x1dc50bfa2db0aa2232871e0be010001f00460038000c)
 (.leaf 0x1dc50b4226689021d204960ae819404e807a0120000c)))
 (.branch 112
 (.leaf 0x1dc50b4226689021d204960b381c803b007a0120000c)
 (.branch 113
 (.leaf 0x77142d08a3e24b874813284960b381c801e80120008000d)
 (.leaf 0x1dc50bd42db079a1c784960af81c4042808e0118000c))))
 (.branch 117
 (.branch 115
 (.leaf 0x1dc38b6e22f87b21bc84920b581f404880de0118000c)
 (.branch 116
 (.leaf 0x1dc50b6c24787480c3014001f00480038000a)
 (.leaf 0x77142d088ee1c786120b100f801e80460030000b)))
 (.branch 118
 (.leaf 0x1dc50b4223b88341c784cc0c1820801e800e0010000c)
 (.branch 119
 (.leaf 0x77142d088ee1c784cc0b0018801e805c0010000b)
 (.leaf 0x1dc50b6c2478748132835e0c3019801f00720008000c))))))
 (.branch 132
 (.branch 126
 (.branch 123
 (.branch 121
 (.leaf 0x77142db091e1d204ca0ae01c201f00120008000b)
 (.branch 122
 (.leaf 0x77142db091e1e3074818400ea012001e0028000b)
 (.leaf 0x1dbf0b1c24786f814504060c2010801f00720028000c)))
 (.branch 124
 (.leaf 0x1dc38b6e22f87a01d284da0cf017003780d60040000c)
 (.branch 125
 (.leaf 0x77043020b741ee075013c8326056808e0030000b)
 (.leaf 0x77142f88b421e2871e1310192024001e0008000b))))
 (.branch 129
 (.branch 127
 (.leaf 0x77042dd09341ef075018e04fa007800a0008000b)
 (.branch 128
 (.leaf 0x1dc10b7424d07bc1d404fa10b024c007800c0008000c)
 (.leaf 0x77142db091e1e30748132817a018001e0008000b)))
 (.branch 130
 (.leaf 0x1dbf0b4624d87d41c885120b180fa03080720028000c)
 (.branch 131
 (.leaf 0x770023e87ec12303a00c201b602d00460008000b)
 (.leaf 0x76f82aa08e2201848a0c8819e03b804600f8000b)))))
 (.branch 138
 (.branch 135
 (.branch 133
 (.leaf 0x77182ac8942129831807f8104020004a0098000b)
 (.branch 134
 (.leaf 0x77082ac091213284a40cc81ce047807e0048000b)
 (.leaf 0x1dc20aac244880613284600bc81ce00f80120008000c)))
 (.branch 136
 (.leaf 0x1dc60ab225087ec13884a60ae01fe00e80140008000c)
 (.branch 137
 (.leaf 0x77183070b1e1e406aa124031607f813a025808e0120000d)
 (.leaf 0x77183070b1e1e406b2124031607f813a023804e0118000d))))
 (.branch 141
 (.branch 139
 (.leaf 0x1dc60c1c1f286b212802ee07f80f202380460060000c)
 (.branch 140
 (.leaf 0x1dc40bf22d209561ea04900cb81e604d808e0120000c)
 (.leaf 0x1dc60c1c25507ca12802ee07f8134023804a0098000c)))
 (.branch 142
 (.leaf 0x1dc20bc826007a012d03b0073814e02380480088000c)
 (.branch 143
 (.leaf 0x77102fc8b481ea04da124032e0798138035808e01b0000d)
 (.leaf 0x77102fc8b481ea04e4124032e079813802380720198000d)))))))
 (.branch 168
 (.branch 156
 (.branch 150
 (.branch 147
 (.branch 145
 (.leaf 0x1dc68c1a2bd079013c83940be01fc02b808e0020000c)
 (.branch 146
 (.leaf 0x1dbe0bcc2db8aa81fc04c40ca819e02400280008000c)
 (.leaf 0x1dc60c1c2c7879013684900c581fe04d00ae0238000c)))
 (.branch 148
 (.leaf 0x1dc40bf22d207a8132049e0cb81e6041808e0048000c)
 (.branch 149
 (.leaf 0x1dc60c461fa050a0ef81fe02400240018000a)
 (.leaf 0x1dc68c1a1e804f212e83860c001fc02b808e0020000c))))
 (.branch 153
 (.branch 151
 (.leaf 0x1dc60c1c1f284da12802ee07f813402b808e0098000c)
 (.branch 152
 (.leaf 0x1dc40c4a204850e1270336079810802480720048000c)
 (.leaf 0x1dc68c4422f87b21b584920b581fc04880de0118000c)))
 (.branch 154
 (.leaf 0x77183070af82308570124031607f813c01f00680118000d)
 (.branch 155
 (.leaf 0x1dc48c4823707d21c004be0d681e404880460080000c)
 (.leaf 0x1dc68c4423107d01b883e007f015801380460088000c)))))
 (.branch 162
 (.branch 159
 (.branch 157
 (.leaf 0x1dc28c4c23d07ea1c605c00f081cc01180200018000c)
 (.branch 158
 (.leaf 0x1dc60c4623007ca14284920bb81fe04100e002b8000c)
 (.leaf 0x771a3110ad0230052812d82ce09281fc01e804e0008000d)))
 (.branch 160
 (.leaf 0x1dc60c1c23087fa138049e0c781fe03b80e00050000c)
 (.branch 161
 (.leaf 0x770831388f41ff06d811802f207380f2039804600f8000d)
 (.leaf 0x77103128b24236057214804940b981e601e80120008000d))))
 (.branch 165
 (.branch 163
 (.leaf 0x1dc60c4623107fa1ae031e07f813a01380460110000c)
 (.branch 164
 (.leaf 0x1dc00bf624387fa1ae031e06d813201280400048000c)
 (.leaf 0x1dc00bf624387fa13703440c781b603580400008000c)))
 (.branch 166
 (.leaf 0x1dc40bf223787ca14302ee07980ec03580ae0100000c)
 (.branch 167
 (.leaf 0x1dc60c4623107fa1ab049c0c781fe04280460098000c)
 (.leaf 0x1dc40c4a2370812132049c0cd81e604180d60048000c))))))
 (.branch 180
 (.branch 174
 (.branch 171
 (.branch 169
 (.leaf 0x1dc48c4828608e61c004940ae01e4048807c0118000c)
 (.branch 170
 (.leaf 0x77102fc8b2223a04e6124032e079813801f80720198000d)
 (.leaf 0x771825087bc19d84e20b100f802c805a0030000b)))
 (.branch 172
 (.leaf 0x1dc68a9e250069e13e840c0b6823601f800c0008000c)
 (.branch 173
 (.leaf 0x771a2aa894019d052a0b280ea01f80740028000b)
 (.leaf 0x77102ab892a1ef064c0b4822605100480028000b))))
 (.branch 177
 (.branch 175
 (.leaf 0x77182ab09421ef067614480ea01c801e0028000b)
 (.branch 176
 (.leaf 0x1dc609421a804e212c03ac0c5018002000720008000c)
 (.leaf 0x770023e87ec19405600c201d002c00460018000b)))
 (.branch 178
 (.leaf 0x771825087bc19d84e20b0018802c804e0010000b)
 (.branch 179
 (.leaf 0x1dc40aa824a88041ad06a40b681a202580460008000c)
 (.leaf 0x77182aa09421fb06a013882c206280720008000b)))))
 (.branch 186
 (.branch 183
 (.branch 181
 (.leaf 0x77002ab08fa201067a0c281d203a00720118000b)
 (.branch 182
 (.leaf 0x1dc68c442a887d01bf067413502ca024000a0008000c)
 (.leaf 0x771231208d81e1864a15384920b4816c03780160028000d)))
 (.branch 184
 (.leaf 0x771830707b619d84e00b100f8023805a0030000b)
 (.branch 185
 (.leaf 0x1dc40bf225587b619302d2089814402380480028000c)
 (.leaf 0x1dc60c1c25b07b619d85180ae820c023800a0010000c))))
 (.branch 189
 (.branch 187
 (.leaf 0x771a30688c61e786e419d00ea012001e0028000b)
 (.branch 188
 (.leaf 0x771830707b619d84e00b00188023804e0010000b)
 (.leaf 0x771830707b619d84cc0b0018802380680010000b)))
 (.branch 190
 (.leaf 0x770a31308f41f9070a1a982f206e80460008000b)
 (.branch 191
 (.leaf 0x1dc40c4a23707fe1a904c80b681a203580720008000c)
 (.leaf 0x1dc00bf625587e61940308074010002400720118000c)))))))))
def rawLeaves (i : Nat) : List Nat :=
  let code := leafTable.get i
  (PackedRawNatGrowth.readList 14 (PackedRawNatGrowth.take 5 code)
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

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0320

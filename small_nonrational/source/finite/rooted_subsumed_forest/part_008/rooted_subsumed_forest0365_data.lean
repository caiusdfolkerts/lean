module
prelude
public import RootedSixBase02GrowthCacheData
public import RootedSixBase02FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification
public import RootedSubsumedForest0365Packed000
public import RootedSubsumedForest0365Packed001

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0365
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 8084
abbrev nodeCount : Nat := 12767
abbrev leafCount : Nat := 192
def widths : PackedRawNatGrowth.Widths := ⟨13,14,6,8⟩
def blocks : Table PackedRawNatGrowth.Block :=
(.branch 50
 nodeBlocks000
 nodeBlocks001)
def counterTable : Table Nat :=
(.branch 50
 nodeCounters000
 nodeCounters001)
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
 (.leaf 0x42c20d0ec06ac29411788482940af01c8004000c)
 (.branch 2
 (.leaf 0x43a2108e706bc2a9108852c1be06601c8080000c)
 (.leaf 0x42c20d0ec06ac294109052816009701c803c000c)))
 (.branch 4
 (.leaf 0x43a2108e706ae2a9108852c1be08b01f80e4000c)
 (.branch 5
 (.leaf 0x9d441e1d80c004ea20f0b505341f00e501c8004000d)
 (.leaf 0x502264108876226910d083c2980d201c800c000c))))
 (.branch 9
 (.branch 7
 (.leaf 0x5281fc8e1c6da2a510f88442940c701e0004000c)
 (.branch 8
 (.leaf 0x503259908873826a108053017a06701c8040000c)
 (.leaf 0xac03f61cf0d2c4ce2120a7052c1ae0a302380e4000d)))
 (.branch 10
 (.leaf 0x40a1cf8d5c5242110b1852c1c60a202e80e4000c)
 (.branch 11
 (.leaf 0x21d10847402a9108858c2960e005100e4000b)
 (.leaf 0x5491f68ee851e2110b2852816008b02980ec000c)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf 0x4ea20f0f44776274107873429a08101c8014000c)
 (.branch 14
 (.leaf 0x54c2090e944d621510806e029a08101e0014000c)
 (.leaf 0x3e11b78a704422100dc05f42940ee01c800c000c)))
 (.branch 16
 (.leaf 0x4cf1f10a1048420f0a7052c28e0e901c800c000c)
 (.branch 17
 (.leaf 0x14dc8282a512b88442960df01e0008000a)
 (.leaf 0x4d01f08a404c42100b205281780a901c8074000c))))
 (.branch 21
 (.branch 19
 (.leaf 0x5662348fa46422a3107852c1be06602e80e4000c)
 (.branch 20
 (.leaf 0x3ed1e98a3c4ba2110d205281c608001d0070000c)
 (.leaf 0x1048520262108078429a0a901e801c000a)))
 (.branch 22
 (.leaf 0x14d4840298108078c29808d01e0018000a)
 (.branch 23
 (.leaf 0x14d484029910805301d608a01e00e0000a)
 (.leaf 0x51226610286b2281107852c1be06602e80e4000c))))))
 (.branch 36
 (.branch 30
 (.branch 27
 (.branch 25
 (.leaf 0x42215508482980a301f001c0008)
 (.branch 26
 (.leaf 0x26b8f886c2284107852c1a606601c80b8000b)
 (.leaf 0x2598f786402aa108052817606701c80dc000b)))
 (.branch 28
 (.leaf 0x43c1df8ea86b426b108052817e08a0220040000c)
 (.branch 29
 (.leaf 0x4d02030f0072826810785e82980bd02b8004000c)
 (.leaf 0x4d320e8f0c70029b1090528160097024003c000c))))
 (.branch 33
 (.branch 31
 (.leaf 0x4d01f68f0472a28f108852816008b02f803c000c)
 (.branch 32
 (.leaf 0x52625a8ff870e35a14688402940bb00f8004000c)
 (.leaf 0x56822a10046e432315188402940c700f8004000c)))
 (.branch 34
 (.leaf 0x26a104470c2a712088482940bb0238004000b)
 (.branch 35
 (.leaf 0x4cf1f08dc46a629f12108442940c702d0004000c)
 (.leaf 0x5252500ff873828e10b88442940af0328004000c)))))
 (.branch 42
 (.branch 39
 (.branch 37
 (.leaf 0x42920d0e6c6ac29411608482940af0328004000c)
 (.branch 38
 (.leaf 0x43f1ba8a704c22100fb85281900a80220040000c)
 (.leaf 0x4d320e0dd06a82a0108852816008b024003c000c)))
 (.branch 40
 (.leaf 0x43e2108e706bc2a910885281be06b0100054000c)
 (.branch 41
 (.leaf 0x4732118dcc6ba29b108852c16407301a003c000c)
 (.leaf 0x45e2118dd060e280108852816608b031803c000c))))
 (.branch 45
 (.branch 43
 (.leaf 0xaac4782060e744d22110b385341c20730180024000d)
 (.branch 44
 (.leaf 0x511265105870e27510787e42960d403b803c000c)
 (.leaf 0x4641f88e184f220f0fb85341da07702e8044000c)))
 (.branch 46
 (.leaf 0x4532068e1c6a42ac10807e42940bc047803c000c)
 (.branch 47
 (.leaf 0x47422f8e1c4f020f0fc852c1a8077021803c000c)
 (.leaf 0x53526990806e6298108053017a0670148040000c)))))))
 (.branch 72
 (.branch 60
 (.branch 54
 (.branch 51
 (.branch 49
 (.leaf 0x53526990806e626b108053017a0670288040000c)
 (.branch 50
 (.leaf 0x5241f80e246bc2a61090528166097015003c000c)
 (.leaf 0x53720a0dcc6ba2a5108852c1be0730078024000c)))
 (.branch 52
 (.leaf 0x53420f8e2051a2100fd85341da0680088030000c)
 (.branch 53
 (.leaf 0x5352100dcc5322100fe05301d809b008003c000c)
 (.leaf 0x29a107c71035c146884029a0ea03f007c000b))))
 (.branch 57
 (.branch 55
 (.leaf 0x5382038e7453422c10905301a407203280d4000c)
 (.branch 56
 (.leaf 0x5241f80e245662a612b08482940670328014000c)
 (.leaf 0x53526990806e6298108053015e07500f8058000c)))
 (.branch 58
 (.leaf 0x5352100dcc5302100f1853016407500f806c000c)
 (.branch 59
 (.leaf 0x50e1f18ecc50424010907e42960bf0460054000c)
 (.leaf 0x53420f8e2051a2100bc05341da08a03280fc000c)))))
 (.branch 66
 (.branch 63
 (.branch 61
 (.leaf 0x5231f78ec8504229109053c2980bd0328004000c)
 (.branch 62
 (.leaf 0x50e1f18ecc6b028210905442960bf0518054000c)
 (.leaf 0x106876035614a08482960970250018000a)))
 (.branch 64
 (.leaf 0x2b114c07d4386141084829407f02e8014000b)
 (.branch 65
 (.leaf 0x10147602fd156884829609702e0018000a)
 (.leaf 0x4e52090e205742100be05341da0670130028000c))))
 (.branch 69
 (.branch 67
 (.leaf 0x3e11c50dbc57a2100be05281de0960130058000c)
 (.branch 68
 (.leaf 0x5252500ff873835a14708442940730148014000c)
 (.leaf 0x5682149068736323146084829407f0148014000c)))
 (.branch 70
 (.leaf 0x4dc1fd0e2443020f0f605341740990128030000c)
 (.branch 71
 (.leaf 0x4c9229905470e35a13b88402940670190014000c)
 (.leaf 0x26d11c07f4372136083c29606602f8018000b))))))
 (.branch 84
 (.branch 78
 (.branch 75
 (.branch 73
 (.leaf 0x4282110ec06ba2aa109052c17609700a8024000c)
 (.branch 74
 (.leaf 0x4d31f68dd06a82a0108852816008b029003c000c)
 (.leaf 0x4d01f70e7c4d820f0cf85cc2980d50048004000c)))
 (.branch 76
 (.leaf 0x1fd0e246bc27810785341d409602a807c000b)
 (.branch 77
 (.leaf 0x3fa1cf0d684d820f0db868429a0930100018000c)
 (.leaf 0x5621fb0e1469a273109052c1a6097029811c000c))))
 (.branch 81
 (.branch 79
 (.leaf 0x5241f80e146ae2a6109052c1a6097029811c000c)
 (.branch 80
 (.leaf 0x4dc1fd0e244f020f0f605341ec09900f801c000c)
 (.leaf 0x4ce1fc8e2454e2120ce85281780ab00d803c000c)))
 (.branch 82
 (.leaf 0x4d42088e2054e2120c4052c1780ab00a803c000c)
 (.branch 83
 (.leaf 0x4cd2030dcc5382100a604c01ea06701b0040000c)
 (.leaf 0x3e11ba8d5c5382100ee05281e608a02a0040000c)))))
 (.branch 90
 (.branch 87
 (.branch 85
 (.leaf 0x4cf2088ecc5062120a8852c2600ad00a8014000c)
 (.branch 86
 (.leaf 0x4ce1fc8e2454e2120a5051c1780a100d803c000c)
 (.leaf 0x4fc264108873826910785301a407203280d4000c)))
 (.branch 88
 (.leaf 0x273931c84239b1ac89a441e14d06f01f8000b)
 (.branch 89
 (.leaf 0x41d1d90a0c4522120f9871c2aa14c0028004000c)
 (.leaf 0x21d1028734357149084429a0de0510174000b))))
 (.branch 93
 (.branch 91
 (.leaf 0x4111c40a9c48221210207b82960be0078004000c)
 (.branch 92
 (.leaf 0x4cd2088e2054e241109052c20c0dd0078004000c)
 (.leaf 0x4e320e8ec850622b10906ac29808d0048014000c)))
 (.branch 94
 (.leaf 0x41d1d90a0c4562120f9871c29808d0048014000c)
 (.branch 95
 (.leaf 0x41d1d90a0c456212103876429808d0048014000c)
 (.leaf 0x2b090f87d439a1a6099c42214d06f0288000b))))))))
 (.branch 144
 (.branch 120
 (.branch 108
 (.branch 102
 (.branch 99
 (.branch 97
 (.leaf 0x3e11ba8a704ae2100f885281e607400d8054000c)
 (.branch 98
 (.leaf 0x4671fa8e706502a010785301a407203280d4000c)
 (.leaf 0x2718fe47122b8153895842414a0338014000b)))
 (.branch 100
 (.leaf 0x4cf2088ecc506240109052c20c09500a8014000c)
 (.branch 101
 (.leaf 0x4061da09ac4562100d185302600ad0328014000c)
 (.leaf 0x21e902875e35c149084429a0c605100a4000b))))
 (.branch 105
 (.branch 103
 (.leaf 0x2678fe473c29b133088c42414a0578004000b)
 (.branch 104
 (.leaf 0x4ce1fc8e2454e265109052817809000d803c000c)
 (.leaf 0x3e11c50a404c42100fb85281780a90298044000c)))
 (.branch 106
 (.leaf 0x105875e29e10905301a40a302500e0000a)
 (.branch 107
 (.leaf 0x5621fb0e1469a276109052c15c09702380d4000c)
 (.leaf 0x107876428f108878829a0990110018000a)))))
 (.branch 114
 (.branch 111
 (.branch 109
 (.leaf 0x4061b989ac4982100d185301960a800f8074000c)
 (.branch 110
 (.leaf 0x5241f80e146bc2a6109052c15c09702380a8000c)
 (.leaf 0x4d52030dcc4d624c108053018c0a800f8068000c)))
 (.branch 112
 (.leaf 0x51824f10586e0276108852c15c08b02f00d4000c)
 (.branch 113
 (.leaf 0x107476429b10905301aa09702b0048000a)
 (.leaf 0x4d62088e205062120a584181ba07f015003c000c))))
 (.branch 117
 (.branch 115
 (.leaf 0x4061b98ba04d62100be85301e0067029802c000c)
 (.branch 116
 (.leaf 0x4061b98ba04d623010805e02980f00298010000c)
 (.leaf 0x4572068dc0654288108053017408a02f00d4000c)))
 (.branch 118
 (.leaf 0x4111c40a0c48a2120dc852c20c09501f8014000c)
 (.branch 119
 (.leaf 0x3f61c28c704f02120d8052c208097023801c000c)
 (.leaf 0x48b2090e204f421810806e029a0810190014000c))))))
 (.branch 132
 (.branch 126
 (.branch 123
 (.branch 121
 (.leaf 0x5291f08e6c5422120fc05281c808002e8054000c)
 (.branch 122
 (.leaf 0x50325990886e0267108068829808d02f8018000c)
 (.leaf 0x5621f50dd069a282108852821a08b0078014000c)))
 (.branch 124
 (.leaf 0x4d52028dc86782ab107852c18e06902c0054000c)
 (.branch 125
 (.leaf 0x40e1c40c6c5202120da052c18607f01a803c000c)
 (.leaf 0x107876028c108078829a09902d0018000a))))
 (.branch 129
 (.branch 127
 (.leaf 0x5652070e2067028e109052c16407f01a803c000c)
 (.branch 128
 (.leaf 0x40e1d98d545262120a8852c1780a30298054000c)
 (.leaf 0x5601fb0e7869626710905482940d70518054000c)))
 (.branch 130
 (.leaf 0x4e720f0e6c57e296107873429a0810178014000c)
 (.branch 131
 (.leaf 0x4fc2641088738268107868c2980750328014000c)
 (.leaf 0x5142138ec05122120fc052c1980980218054000c)))))
 (.branch 138
 (.branch 135
 (.branch 133
 (.leaf 0x42820b0ebc53c2120fe05301600a400b0034000c)
 (.branch 134
 (.leaf 0x41a1d90d5852822f10905542980b200c0004000c)
 (.leaf 0x55523a905c6e2280107873829807502b8014000c)))
 (.branch 136
 (.leaf 0x10887642aa10905301ac09701c0048000a)
 (.branch 137
 (.leaf 0x2108e746ae2a9108858c29a0e204580fc000b)
 (.leaf 0x4161d98d7453c2120a8852c17e0a30148054000c))))
 (.branch 141
 (.branch 139
 (.leaf 0x2108ec86b82a9108859829a0ca0458024000b)
 (.branch 140
 (.leaf 0x46321b8ed84d621510805e429a0c90220004000c)
 (.leaf 0x5291f08e8453426611188482940af02e8004000c)))
 (.branch 142
 (.leaf 0x4282088edc50623c11388482980ba02a000c000c)
 (.branch 143
 (.leaf 0x4c71f08ddc5962a912b884429406702d0014000c)
 (.leaf 0x4b21f10de0552242108852c18e06902c0054000c)))))))
 (.branch 168
 (.branch 156
 (.branch 150
 (.branch 147
 (.branch 145
 (.leaf 0x108876c2aa109052c1a80a30250048000a)
 (.branch 146
 (.leaf 0x52d2458fc871829a109052816009702e803c000c)
 (.leaf 0x101876e29a10905301aa09702d8048000a)))
 (.branch 148
 (.leaf 0x5111f10e345d02ad109052c16207f027003c000c)
 (.branch 149
 (.leaf 0x5282160e305fa2ad1090528160097022803c000c)
 (.leaf 0x44220c8de067e288108852c16207302f803c000c))))
 (.branch 153
 (.branch 151
 (.leaf 0x4282110ed8554244109052c17606901f8054000c)
 (.branch 152
 (.leaf 0x42520b0e8853c22c10905301a407202f00d4000c)
 (.leaf 0x43b1f90edc4f4214108859029a0c902e8004000c)))
 (.branch 154
 (.leaf 0x44f2048e345222100bc05341da08a02e80fc000c)
 (.branch 155
 (.leaf 0x42d20b0e8853c22c109053015e07502f0058000c)
 (.leaf 0x5392040e3056c2a612b08482940670238014000c)))))
 (.branch 162
 (.branch 159
 (.branch 157
 (.leaf 0x4522030ed857822010805e429a0c90130004000c)
 (.branch 158
 (.leaf 0x4fb244102476e28211588482980ba04500d4000c)
 (.leaf 0x5392040e3054c25610905281a60680238054000c)))
 (.branch 160
 (.leaf 0x4671f48e84626294107863829a0e103300fc000c)
 (.branch 161
 (.leaf 0x21e908476a2a910885982960c80510054000b)
 (.leaf 0x42820b0edc53c22f109053c2980bd0148004000c))))
 (.branch 165
 (.branch 163
 (.leaf 0x42820b0edc53c2120a8853017a0970148024000c)
 (.branch 164
 (.leaf 0x4e624e905476e27610a08442c814d0648004000c)
 (.leaf 0x4e72639084742269107863829a0e103300fc000c)))
 (.branch 166
 (.leaf 0x9d04c920a8e304ea20f0c885341f40ed0078004000d)
 (.branch 167
 (.leaf 0x9d04b41fe8e3451a2100be05341ee0ed00f8004000d)
 (.leaf 0x9cc49d20a8edc4ec2110b3053419208b01a8024000d))))))
 (.branch 180
 (.branch 174
 (.branch 171
 (.branch 169
 (.leaf 0x9ce4c72108e844d220f0c805341c207500d8024000d)
 (.branch 170
 (.leaf 0x51d2490e9054a2110b385281c00a20218054000c)
 (.leaf 0x11bc77428f10885341c208b022804c000a)))
 (.branch 172
 (.leaf 0x5291f08f5074c29a109052816009702e803c000c)
 (.branch 173
 (.leaf 0x5481f70ee44d422a10805e82980bd02b8004000c)
 (.leaf 0x4522090f487782c6108053017a0670130040000c))))
 (.branch 177
 (.branch 175
 (.leaf 0x4522030f4477626b10805341920670298044000c)
 (.branch 176
 (.leaf 0x82035215608402960d302b00080009)
 (.leaf 0x2b10fdc69a27610906ec29a0f804d0014000b)))
 (.branch 178
 (.leaf 0x250100c69428610886a429810d0470014000b)
 (.branch 179
 (.leaf 0x26e903c68c26b109075429a0f70530014000b)
 (.leaf 0x2078d184d62120f285341fa0a600a8014000b)))))
 (.branch 186
 (.branch 183
 (.branch 181
 (.leaf 0x20d8d144ee2120e985341f809a00f0014000b)
 (.branch 182
 (.leaf 0x83635614a08483c414d04d00180009)
 (.leaf 0x2598f7c6402aa108052c17606a01b8054000b)))
 (.branch 184
 (.leaf 0x1f60d7855020f0e685281c406b0180070000b)
 (.branch 185
 (.leaf 0x26c0fb06c42a810785281be06b0180054000b)
 (.leaf 0x26a906c66028f109053415e08201a805c000b))))
 (.branch 189
 (.branch 187
 (.leaf 0x26990406a42ac108052c17606a01a8054000b)
 (.branch 188
 (.leaf 0x2b10fdc69a27310906dc29a0d304d014c000b)
 (.leaf 0x20d8d144ee2120f1053415c09a02980d4000b)))
 (.branch 190
 (.leaf 0x26990406a42ac108052c17808f00d8054000b)
 (.branch 191
 (.leaf 0x2080c205002100dc852c17e08f031006c000b)
 (.leaf 0x2080d485582100f1852c17c06a01a806c000b)))))))))
def rawLeaves (i : Nat) : List Nat :=
  let code := leafTable.get i
  (PackedRawNatGrowth.readList 13 (PackedRawNatGrowth.take 5 code)
    (PackedRawNatGrowth.drop 5 code)).1

def leaves : Fin leafCount → List (Fin cellCount) := decodedLeaves rawLeaves
def quota : Nat → Nat
  | 0 => 1
  | 1 => 2
  | 2 => 6
  | 3 => 4
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
    Papers.RationalityTen.RootedCaches.RootedSixBase02.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixBase02.badMasks
    Papers.RationalityTen.RootedCaches.RootedSixBase02.kindMasks Papers.RationalityTen.RootedCaches.RootedSixBase02.keys Papers.RationalityTen.RootedCaches.RootedSixBase02.fastKind quota
    Papers.RationalityTen.FacetUniverses.RootedSixBase02.Generators.FastWords.rawMaps rawLeaves codes counters i
theorem nodeTest_sound (i : Nat) (h : nodeTest i = true) :
    nodeBounds cellCount 1024 48 leafCount nodeCount (rawNodes i) = true ∧
      SubsumedRawGrowth.nodeCheck Papers.RationalityTen.RootedCaches.RootedSixBase02.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixBase02.badMasks
        Papers.RationalityTen.RootedCaches.RootedSixBase02.kindMasks Papers.RationalityTen.RootedCaches.RootedSixBase02.keys Papers.RationalityTen.RootedCaches.RootedSixBase02.fastKind quota
        Papers.RationalityTen.FacetUniverses.RootedSixBase02.Generators.FastWords.rawMaps rawLeaves rawNodes i = true :=
  SubsumedCounterReplay.check_sound widths cellCount 1024 48 leafCount nodeCount
    Papers.RationalityTen.RootedCaches.RootedSixBase02.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixBase02.badMasks
    Papers.RationalityTen.RootedCaches.RootedSixBase02.kindMasks Papers.RationalityTen.RootedCaches.RootedSixBase02.keys Papers.RationalityTen.RootedCaches.RootedSixBase02.fastKind quota
    Papers.RationalityTen.FacetUniverses.RootedSixBase02.Generators.FastWords.rawMaps rawLeaves codes counters i h
def leafTest (i : Nat) : Bool :=
  listBounds cellCount (rawLeaves i) &&
    (WitnessGrowthDAG.closedCheck FacetUniverses.RootedSixBase02.ridgeList
      ((rawLeaves i).map (Fin.ofNat cellCount)) &&
      decide (((rawLeaves i).map (Fin.ofNat cellCount)).Nodup))

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0365

module
prelude
public import RootedSixExtra05GrowthCacheData
public import RootedSixExtra05FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification
public import RootedSubsumedForest0869Packed000
public import RootedSubsumedForest0869Packed001

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0869
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 2170
abbrev nodeCount : Nat := 12041
abbrev leafCount : Nat := 181
def widths : PackedRawNatGrowth.Widths := ⟨12,14,9,8⟩
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
(.branch 90
 (.branch 45
 (.branch 22
 (.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf 0x6404b83801f214411207805e028010000b)
 (.leaf 0x6304b83801f214411209a05e028010000b))
 (.branch 3
 (.leaf 0x6585844ae3801f2144112084028010000b)
 (.branch 4
 (.leaf 0x6744b237c3541f214411a06c024022014000c)
 (.leaf 0x62e4b237e3541f414213208a024022012000c))))
 (.branch 8
 (.branch 6
 (.leaf 0x65e4ae3801f614411809002a028010000b)
 (.branch 7
 (.leaf 0x6464b83801f614411807802a028010000b)
 (.leaf 0x66037e1f414604c02c0140060009)))
 (.branch 9
 (.leaf 0x65e3801f614413004c02c0008)
 (.branch 10
 (.leaf 0x65e4ae38027e1f614403e02c010004000b)
 (.leaf 0x6424083803261f214605e014010004000b)))))
 (.branch 16
 (.branch 13
 (.branch 12
 (.leaf 0x62858c37e1f214212e04803401e010000b)
 (.leaf 0x64458a37c1f614212e03c03402a010000b))
 (.branch 14
 (.leaf 0x65e4843803561f614411805002c00c00a000c)
 (.branch 15
 (.leaf 0x6464d63803261f61420e804a03202e00a000c)
 (.leaf 0x60048837a1f01ca1440ba0ae05002e024000c))))
 (.branch 19
 (.branch 17
 (.leaf 0x61845c37a1f01d61460d204e03002e026000c)
 (.branch 18
 (.leaf 0x6464b03803541f614213004e02a00c00a000c)
 (.leaf 0x6464b03801f614213003402a010000a)))
 (.branch 20
 (.leaf 0x60048837a1f01cc1440ea0ae03002e024000c)
 (.branch 21
 (.leaf 0x6285844aa3ba3801f214209c01600a002000c)
 (.leaf 0x6585864ac37c1f414409a01c010004000b))))))
 (.branch 33
 (.branch 27
 (.branch 24
 (.branch 23
 (.leaf 0x6604aa37c3201f2146098084012004000b)
 (.leaf 0x6f260048037a2cc1f01460ae08a00e002000c))
 (.branch 25
 (.leaf 0x6fa5e848037a2f61f014609e08a00e002000c)
 (.branch 26
 (.leaf 0x6484ac37c3221f214407c010004000a)
 (.leaf 0x66048237e2f81f414010007604e02e00a000c))))
 (.branch 30
 (.branch 28
 (.leaf 0x65e45c3802f61f61401180a207403000a000c)
 (.branch 29
 (.leaf 0x61845c37a2fc1f01ce1460ae02e00a002000c)
 (.leaf 0x61848637a2fc1f01d414604e02e00a002000c)))
 (.branch 31
 (.leaf 0x6604ae37e3241f4146012010006000a)
 (.branch 32
 (.leaf 0x64645a3803261f61a41420ae02e00a008000c)
 (.leaf 0x6464b03803261f61aa14204e02e00a008000c)))))
 (.branch 39
 (.branch 36
 (.branch 34
 (.leaf 0x6484b037c3261f2156146036016014002000c)
 (.branch 35
 (.leaf 0x6604ae37e3241f414603c01c012004000b)
 (.leaf 0x6585884ae3801f414411201c010000a)))
 (.branch 37
 (.leaf 0x66048437e2fa1f414610004e02e00e00a000c)
 (.branch 38
 (.leaf 0x65e4843803241f61440e80ae03002e00c000c)
 (.leaf 0x65e4ae3803241f614411804e02e00c00a000c))))
 (.branch 42
 (.branch 40
 (.leaf 0x65e4ae3803241f61441180100009)
 (.branch 41
 (.leaf 0xc3c61057849e1f01420ca07204202200a000c)
 (.leaf 0xc3e5e857649c1f01420e209404202200a000c)))
 (.branch 43
 (.leaf 0xbc662e57642e37a3121420e609408a02200a000d)
 (.branch 44
 (.leaf 0xb045e450e49e37a3141f20fc07603802e022000d)
 (.leaf 0xb045e449e37a3141f20b607605602200c000c)))))))
 (.branch 67
 (.branch 56
 (.branch 50
 (.branch 47
 (.branch 46
 (.leaf 0xc347c065a5a64741fe1f414007602400a004000d)
 (.leaf 0xc347c06165a64741fe1f414008802400a004000d))
 (.branch 48
 (.leaf 0xc2c65c5aa44a2f62281f61400ae07400a004000d)
 (.branch 49
 (.leaf 0xc1c62e58044e32022a1f61420ae08800a002000d)
 (.leaf 0xc367185a447234a1f414012c09206a02400e000d))))
 (.branch 53
 (.branch 51
 (.leaf 0xc3e6725764c634c1f01420e409406a022012000d)
 (.branch 52
 (.leaf 0xaf664453044837a3442541f60ae09200c002000d)
 (.leaf 0xaf65de53044837a3442541f60ae08600c002000d)))
 (.branch 54
 (.leaf 0xc3e7c462e5764c63b41f014208002200a002000d)
 (.branch 55
 (.leaf 0xc3e7c45fa5764c63b41f014207802200a002000d)
 (.leaf 0xc3e62e5764c63b42a41f01420ae08000a002000d)))))
 (.branch 61
 (.branch 58
 (.branch 57
 (.leaf 0xc3e5fa5764c63b42a41f01420ae07800a002000d)
 (.leaf 0xc3e5f85a049c34c1f21401140a607e02200e000d))
 (.branch 59
 (.leaf 0xc3e6285a049c34c1f214011409e07202200e000d)
 (.branch 60
 (.leaf 0xbc662e57642e37a33c1420e60ae09403000a000d)
 (.leaf 0xbc66265a042e37c3121401160ae07403000a000d))))
 (.branch 64
 (.branch 62
 (.leaf 0xc3e5e45a049c34c1f21401140a609402200e000d)
 (.branch 63
 (.leaf 0xafc65a55c47437a3421f40ce0ae09602e00a000d)
 (.leaf 0xc3e5e85764c634c1f01420e409e094022012000d)))
 (.branch 65
 (.leaf 0xb0460e53249e37a33e1f20b60ae08602e00c000d)
 (.branch 66
 (.leaf 0xc3c7c26165a249e1f21400fc08602e02200c000d)
 (.leaf 0xc265e857a4763561f414212c080024022012000d))))))
 (.branch 78
 (.branch 72
 (.branch 69
 (.branch 68
 (.leaf 0xc2e6485224ce3261f01460cc07e02e022014000d)
 (.leaf 0xc2e5e65a84483261f614012e08602e02200c000d))
 (.branch 70
 (.leaf 0xc3c6165a249e2ce1f21400fc0ae08602e00c000d)
 (.branch 71
 (.leaf 0xc166005544503041f614411608203002e010000d)
 (.leaf 0xc3662c5a44723521f414012c07202802200e000d))))
 (.branch 75
 (.branch 73
 (.leaf 0xc2e6445a84483261f614012e07202e02200c000d)
 (.branch 74
 (.leaf 0xc3c7c26425a249e1f21400fc07602e02200c000d)
 (.leaf 0xc1e5e45264a42fc1f21460fc07602e022014000d)))
 (.branch 76
 (.leaf 0xc3465a5a64742f81f41400fe0ae07602e00a000d)
 (.branch 77
 (.leaf 0xc2e6445a84482d81f614012e07203402e00c000d)
 (.leaf 0xc408645e452e3561f214013604402201e00c000d)))))
 (.branch 84
 (.branch 81
 (.branch 79
 (.leaf 0xc308106145582fc1f614010604202e02000a000d)
 (.branch 80
 (.leaf 0xc428625e84643f41f014205802200a002000c)
 (.leaf 0xc4088e5e25303f61f014c1420ae048022002000d)))
 (.branch 82
 (.leaf 0xb086e25e437a1f21bc0b6056046024022000c)
 (.branch 83
 (.leaf 0xbc878a5e053e37c26c1400b2042024000b)
 (.leaf 0xc4066443032c1f614213607802e00c00a000c))))
 (.branch 87
 (.branch 85
 (.leaf 0xc2861c4322a81f61440ee07402601000a000c)
 (.branch 86
 (.leaf 0xbc86746684b638014213a02e024022010000c)
 (.leaf 0xbc86684b638014213a078028010000a)))
 (.branch 88
 (.leaf 0xc3867864c32e1f614011e04202e02400a000c)
 (.branch 89
 (.leaf 0xc2867061c1f614a1440ee048042026024000c)
 (.leaf 0xbc86746684b638014e14213a024022000b))))))))
 (.branch 135
 (.branch 112
 (.branch 101
 (.branch 95
 (.branch 92
 (.branch 91
 (.leaf 0xc2867661c1f61501440ee044028026022000c)
 (.leaf 0xbc86706684b638014a14013a042024000b))
 (.branch 93
 (.leaf 0xba869a6084b837e1741460da09e04e026000c)
 (.branch 94
 (.leaf 0xc427c066245c41e1fa1f4140076036024002000d)
 (.leaf 0xb0866c55a3b43802a81f01e60ae08000a002000d))))
 (.branch 98
 (.branch 96
 (.leaf 0xc3069e6343a23041f417414608a04a018002000d)
 (.branch 97
 (.leaf 0xc427c066245c41e1fe1f414007602400a004000d)
 (.leaf 0xc406644324202f62281f61400ae07400a004000d)))
 (.branch 99
 (.leaf 0xc387c264c4242521f614a140072042026006000d)
 (.branch 100
 (.leaf 0xc387c264c5604241f01420ca08204e02200a000d)
 (.leaf 0xbc065056045837a29a1420ce0ae09602e00a000d)))))
 (.branch 106
 (.branch 103
 (.branch 102
 (.leaf 0xc4067e6643f62f61f61420ba04404202201a000d)
 (.leaf 0xafa77a63a53e37c1f61660e60a6036026024000d))
 (.branch 104
 (.leaf 0xc406746643f62f61f61420ba04e04802201a000d)
 (.branch 105
 (.leaf 0xb007166545683801f41920ce0a803a02e028000d)
 (.leaf 0xc407cc6645343f61f21440b608602402200c000d))))
 (.branch 109
 (.branch 107
 (.leaf 0xc408645e842a2fc1f614213608202e022010000d)
 (.branch 108
 (.leaf 0xc226025383fc3561f214411407e024022014000d)
 (.leaf 0xc3a64a50e4223261f01460cc07e02e022014000d)))
 (.branch 110
 (.leaf 0xc387c264c5604241f01420cc08202e022010000d)
 (.branch 111
 (.leaf 0xc328947c26164821f214010408602e02200c000d)
 (.leaf 0xc3280e61847e2fc1f214610407e02e022014000d))))))
 (.branch 123
 (.branch 117
 (.branch 114
 (.branch 113
 (.leaf 0xc1a5ea5603a82fc1f614212e08202e022010000d)
 (.leaf 0xc328946164822ce1f21401040ae08602e00c000d))
 (.branch 115
 (.leaf 0xc3883a60042a3041f614411e08203002e010000d)
 (.branch 116
 (.leaf 0xc406645364202f81f01440b40ae08202e010000d)
 (.leaf 0xc3a64a50a3ca32e1f41460ce08403002e00e000d))))
 (.branch 120
 (.branch 118
 (.leaf 0xc408645e843a2fc1f614213608202200c00a000d)
 (.branch 119
 (.leaf 0xc3280e61848e2da1f214610407e02e00e00c000d)
 (.leaf 0xc406644203201f614207804801e004000b)))
 (.branch 121
 (.leaf 0xc406766643f632022a1f61400ae044022002000d)
 (.branch 122
 (.leaf 0xc388927c45fa55a3cc1f014207802200a002000d)
 (.leaf 0xc388925fa55a3cc2a41f01420ae07800a002000d)))))
 (.branch 129
 (.branch 126
 (.branch 124
 (.leaf 0xc4088e7466724202281f614c14006c044026004000e)
 (.branch 125
 (.leaf 0xb026b65fc51437c1f41900ce092036026024000d)
 (.leaf 0xc3a83860048e3ca2b01f214407e01600c002000d)))
 (.branch 127
 (.leaf 0xc3883a5fc5683cc1f41420ce07202402200a000d)
 (.branch 128
 (.leaf 0xbb076462859243837e2461400fa07200a000c)
 (.leaf 0xc426621f414613409003402a028000a))))
 (.branch 132
 (.branch 130
 (.leaf 0xc426621f414613402c0007)
 (.branch 131
 (.leaf 0xbc86684ae3ba38029614401601000a002000c)
 (.leaf 0xc306344282581f417e14203a034028002000c)))
 (.branch 133
 (.leaf 0xb0a66a58839037e2301f61e400a002000b)
 (.branch 134
 (.leaf 0xc406644203241f614401e010004000a)
 (.leaf 0xc3864c3cc3262541f61420ae02e00a002000c)))))))
 (.branch 158
 (.branch 146
 (.branch 140
 (.branch 137
 (.branch 136
 (.leaf 0xc407c06644202281f614e144026024004000c)
 (.leaf 0xc185ec3d427e1f21a41400ae02e022008000c))
 (.branch 138
 (.leaf 0xb0a66a58838437e2241f61ba0ae002000b)
 (.branch 139
 (.leaf 0xc206043fe3561f414011805002402000a000c)
 (.leaf 0xc406644203241f61440b804e02e01e00c000c))))
 (.branch 143
 (.branch 141
 (.leaf 0xc4088e7466744202281f614e14406c026024004000e)
 (.branch 142
 (.leaf 0x3801f61460700080006)
 (.leaf 0xb046a64c837a33e1f015606a042022002000c)))
 (.branch 144
 (.leaf 0xb065e84c637a33c1f0180078042022002000c)
 (.branch 145
 (.leaf 0xb045e649e37c3141f20b807604202200c000c)
 (.leaf 0xb046a049e37a33e1f01500ae06a022002000c)))))
 (.branch 152
 (.branch 149
 (.branch 147
 (.leaf 0xb0660049c37a33c1f017a0ae08a022002000c)
 (.branch 148
 (.leaf 0xc3c8225784c834e1f014010006a04201800a000d)
 (.leaf 0xc3e5f85764c634c1f014011809e04201a00a000d)))
 (.branch 150
 (.leaf 0xbc461457837a33e1400ce0ae08c02e022000c)
 (.branch 151
 (.leaf 0xbbc65c5a639037e34214401601000a002000c)
 (.leaf 0xbbc65c5a638437e34214402e01600c002000c))))
 (.branch 155
 (.branch 153
 (.leaf 0xc3c6405a24c83901f214201600a002000b)
 (.branch 154
 (.leaf 0xbbc65c5a638837e34214402e00c00a004000c)
 (.leaf 0xc346585a64cc1f414401c010004000a)))
 (.branch 156
 (.leaf 0xb044c837c33e1f207a06c010004000a)
 (.branch 157
 (.leaf 0xb046484c837c33e1f20100040009)
 (.leaf 0xc3c6405a24c81f21420ca06204e01600a000c))))))
 (.branch 169
 (.branch 163
 (.branch 160
 (.branch 159
 (.leaf 0xc3c61057849e1f014010004e02e01800a000c)
 (.leaf 0xafc6604cc37e3421f40d004e02e00a000b))
 (.branch 161
 (.leaf 0xc2c6565aa4d01f61461100008)
 (.branch 162
 (.leaf 0xae087076c5f440238024e1f60c60a606204a026000e)
 (.leaf 0xaf884474063c3de38022a1f61680a604c02a002000e))))
 (.branch 166
 (.branch 164
 (.leaf 0xc4088e53042c34a1f014013609206a01a00c000d)
 (.branch 165
 (.leaf 0xc388925f855a34c1f014011e09e04201a00a000d)
 (.leaf 0xc3089661055c4581f01401060ae02e01800a000d)))
 (.branch 167
 (.leaf 0xc3089661055c45834e1f014010601800a000c)
 (.branch 168
 (.leaf 0xb088247206e23b637c2021f21bc06a04a028002000e)
 (.leaf 0xc428625de5144643f41f214201600a002000c)))))
 (.branch 175
 (.branch 172
 (.branch 170
 (.leaf 0xc408645de53e3f61f214c14209e048016002000d)
 (.branch 171
 (.leaf 0xb0a6e043237a2d21f01e40ae06a00a002000c)
 (.leaf 0xb0a70a43837a2d81f01e407206a00a002000c)))
 (.branch 173
 (.leaf 0xb0870c5e846237a1f01e602802200a002000c)
 (.branch 174
 (.leaf 0xb0a70a5e843837a2d81f01e400a002000b)
 (.leaf 0xb086e25e637c1f21bc0b8046042024022000c))))
 (.branch 178
 (.branch 176
 (.leaf 0xbc878a5e253e37c26c1420b4024022000b)
 (.branch 177
 (.leaf 0xbc07b85fc56637a29a1400ce08a02e022000c)
 (.leaf 0xc428625de5144643f41f21420b0000a)))
 (.branch 179
 (.leaf 0xbc076056037a29a1400ce0ae06a02e022000c)
 (.branch 180
 (.leaf 0xb0a70a5e842c37a2cc1f01ba0ae002000b)
 (.leaf 0xb0870c37c1f21e606c04a028004000a)))))))))
def rawLeaves (i : Nat) : List Nat :=
  let code := leafTable.get i
  (PackedRawNatGrowth.readList 12 (PackedRawNatGrowth.take 5 code)
    (PackedRawNatGrowth.drop 5 code)).1

def leaves : Fin leafCount → List (Fin cellCount) := decodedLeaves rawLeaves
def quota : Nat → Nat
  | 0 => 1
  | 1 => 4
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

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0869

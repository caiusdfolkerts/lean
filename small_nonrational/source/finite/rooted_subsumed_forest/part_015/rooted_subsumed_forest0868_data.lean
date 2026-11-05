module
prelude
public import RootedSixExtra05GrowthCacheData
public import RootedSixExtra05FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification
public import RootedSubsumedForest0868Packed000
public import RootedSubsumedForest0868Packed001

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0868
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 2170
abbrev nodeCount : Nat := 8057
abbrev leafCount : Nat := 180
def widths : PackedRawNatGrowth.Widths := ⟨12,13,9,8⟩
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
 (.leaf 0x74662859237e2281f61420fa048026022000c)
 (.leaf 0x71c6604843aa37e2f61f21460be05c02200e000d))
 (.branch 3
 (.leaf 0x7aa5fe59838437e2a42301f614004402a002000d)
 (.branch 4
 (.leaf 0x7aa5fe59838837e2a41f614011604402a00a000d)
 (.leaf 0x68465c55e44037e2f61f61420e603802200a000d))))
 (.branch 8
 (.branch 6
 (.leaf 0x75663054443037c2a21f61440e603602600c000d)
 (.branch 7
 (.leaf 0x67261048e3801f014c1420e205a048022000c)
 (.leaf 0x71a6405ca59e45a3801f01420e205802200a000d)))
 (.branch 9
 (.leaf 0x75e6c864e4ac37c34e1f01440b4056024010000d)
 (.branch 10
 (.leaf 0x81a78a6684ac37c34e1f01440b4056024010000d)
 (.leaf 0x7926085884d837e2281f61400fa04402600a000d)))))
 (.branch 16
 (.branch 13
 (.branch 12
 (.leaf 0x79260858838837e34c1f614011604402600a000d)
 (.leaf 0x7706b665258637c34e1f41400fe04202400a000d))
 (.branch 14
 (.leaf 0x8206e266c58637c34e1f41400fe04202400a000d)
 (.branch 15
 (.leaf 0x6e266c5883b238034e1f41400fe04602400a000d)
 (.leaf 0x7346c86364b637c1f019e1460b205604e026000d))))
 (.branch 19
 (.branch 17
 (.leaf 0x7f07886664b637c1f019e1460b205604e026000d)
 (.branch 18
 (.leaf 0x7466e066a58e3da37e2261f2140044022002000d)
 (.leaf 0x7b46684ae3801f214411205e028010000b)))
 (.branch 20
 (.leaf 0x6405a85224b03e43801f014c14207e022002000d)
 (.branch 21
 (.leaf 0x64058a4ce4483801fe1f214012a07202200c000d)
 (.leaf 0x5e658a4ce4483801fe1f214012a09a02200c000d))))))
 (.branch 33
 (.branch 27
 (.branch 24
 (.branch 23
 (.leaf 0x5e25a454c4b23e237e1f0176142098022002000d)
 (.leaf 0x5e450448842237e34c1f214011c09402200e000d))
 (.branch 25
 (.leaf 0x8e85fc59845c3801fe1f414011209602400a000d)
 (.branch 26
 (.leaf 0x5e658a4f846c3801fe1f214012a09a02200c000d)
 (.leaf 0x8b85e658a4903801fe1f214012a09a02200c000d))))
 (.branch 30
 (.branch 28
 (.leaf 0x88e74266443037c2f81f01440b20ae05600c000d)
 (.branch 29
 (.leaf 0x89663455e45a38034e1f41420ce03a02800a000d)
 (.leaf 0x86c60458845c3801fe1f41401120ae02400a000d)))
 (.branch 31
 (.leaf 0x8967c463455a45a3801f01420e208002200a000d)
 (.branch 32
 (.leaf 0x8e46105944863801fe1f214012a07e02200c000d)
 (.leaf 0x64058a4f846c3801fe1f214012a07202200c000d)))))
 (.branch 39
 (.branch 36
 (.branch 34
 (.leaf 0x8b864058a4903801fe1f214012a07202200c000d)
 (.branch 35
 (.leaf 0x74870a66a55c43037e1f01420ca0ae02200a000d)
 (.leaf 0x6e860a50446437c1f419c1460f809204e02c000d)))
 (.branch 37
 (.leaf 0x78c61e50446437c1f419c1460f809204e02c000d)
 (.branch 38
 (.leaf 0x88c66250646237a1f41c61460c809204e02c000d)
 (.leaf 0x71a61059a4864123801f214c1400aa022004000d))))
 (.branch 42
 (.branch 40
 (.leaf 0x88a5fa5304be3801f014a1440e20a6050024000d)
 (.branch 41
 (.leaf 0x7bc63855a42e37a34c1f61420e609402a00a000d)
 (.leaf 0x89264c55a42e37a34c1f61420e609402a00a000d)))
 (.branch 43
 (.leaf 0x70a66a55a42e37a34c1f61420e609402a00a000d)
 (.branch 44
 (.leaf 0x7bc63855e43037e34c1f61420e603802a00a000d)
 (.leaf 0x70c66c55e45a38034e1f41420ce03a02800a000d)))))))
 (.branch 67
 (.branch 56
 (.branch 50
 (.branch 47
 (.branch 46
 (.leaf 0x78e62058845c3801fe1f41401120ae02400a000d)
 (.leaf 0x6e266c58845c3801fe1f41401120ae02400a000d))
 (.branch 48
 (.leaf 0x78866650c48437e1f01821460fa04e026016000d)
 (.branch 49
 (.leaf 0x7685f059243837e2281f61400fa09802600a000d)
 (.leaf 0x83e61c59243837e2281f61400fa09802600a000d))))
 (.branch 53
 (.branch 51
 (.leaf 0x6b665259243837e2281f61400fa09802600a000d)
 (.branch 52
 (.leaf 0x8327185924663801fe1f414011206a02400a000d)
 (.leaf 0x88067259448c3801fe1f214012a06c02200c000d)))
 (.branch 54
 (.leaf 0x8845fe5984623801fe1f414011209e02400a000d)
 (.branch 55
 (.leaf 0x85c5e45904903801fe1f214012a0a602200c000d)
 (.leaf 0x6585844ae3801f2144112084028010000b)))))
 (.branch 61
 (.branch 58
 (.branch 57
 (.leaf 0x7506e066a50443237e1f21400fa0aa02200a000d)
 (.leaf 0x62c55652c45a3802a61f41420e209a01800a000d))
 (.branch 59
 (.leaf 0x8ee62c56e45a3802a61f41420e209a01800a000d)
 (.branch 60
 (.leaf 0x62c5ca59e45a3802a61f41420e209a01800a000d)
 (.leaf 0x8946325304843802a21f01440e20ae07e00c000d))))
 (.branch 64
 (.branch 62
 (.leaf 0x64055652c45a3802a61f41420e208401800a000d)
 (.branch 63
 (.leaf 0x8ee64056e45a3802a61f41420e208401800a000d)
 (.leaf 0x6405ca59e45a3802a61f41420e208401800a000d)))
 (.branch 65
 (.leaf 0x7106545304843802a21f01440e20ae07e00c000d)
 (.branch 66
 (.leaf 0x7b46685304843802a21f01440e20ae07e00c000d)
 (.leaf 0x7e865c55e43037e2e01f61420ca07801a00a000d))))))
 (.branch 78
 (.branch 72
 (.branch 69
 (.branch 68
 (.leaf 0x85a62e56e4643802a61f41420e209e01800a000d)
 (.leaf 0x6b462850a48e37e2e01f21460ca09e01600e000d))
 (.branch 70
 (.leaf 0x78062e56e43037e2da1f61420ca08a01a00a000d)
 (.branch 71
 (.leaf 0x6e266c55e4643802b01f41420e207201800a000d)
 (.leaf 0x86466453e43a37c2fa1f61440b209201a00c000d))))
 (.branch 75
 (.branch 73
 (.leaf 0x89663455e45a3802a61f41420e20ae01800a000d)
 (.branch 74
 (.leaf 0x7106545344843802a61f21440e20ae01600c000d)
 (.leaf 0x7ca65e4ae3801f614e14411802a024022000c)))
 (.branch 76
 (.leaf 0x6746464b83801f614e14411802a024022000c)
 (.branch 77
 (.leaf 0x67261648e3801f614c1420e8048026022000c)
 (.leaf 0x7c460048837a1f01ea192144028022002000c)))))
 (.branch 84
 (.branch 81
 (.branch 79
 (.leaf 0x89071a64a48037a34c1f01460ea09402a022000d)
 (.branch 80
 (.leaf 0x7c26484b037c1f219e1460b804e026022000c)
 (.leaf 0x7c26484b037c1f21a214610202e026022000c)))
 (.branch 82
 (.leaf 0x7c462c58c3b237c1f41bc14213e02402200a000d)
 (.branch 83
 (.leaf 0x67c65e4aa3be3803202341f6140042022002000d)
 (.leaf 0x8b26fe61837a2f81f0152142042028002000c))))
 (.branch 87
 (.branch 85
 (.leaf 0x6c86484ac37c2ce1f214e1440ae024004000c)
 (.branch 86
 (.leaf 0x6a66604ac37e3221f4156140042022006000c)
 (.leaf 0x77a62c54a37c2a42381f61420a6026004000c)))
 (.branch 88
 (.leaf 0x7706445c859c37c2ce1f41420ce03602400a000d)
 (.branch 89
 (.leaf 0x78062c56e38637c2a41f61420e605c02600a000d)
 (.leaf 0x7706445863a637c2ce1f41420d60ae02400a000d))))))))
 (.branch 135
 (.branch 112
 (.branch 101
 (.branch 95
 (.branch 92
 (.branch 91
 (.leaf 0x67465e4ec4c03802f61f61420e802200a000c)
 (.leaf 0x67e65e4803802f61f61420e804202200a000c))
 (.branch 93
 (.leaf 0x67e65e4643802f61f61420e80a202200a000c)
 (.branch 94
 (.leaf 0x69e6604ac37e2f81f41421000ae02e022000c)
 (.leaf 0x6a866042a37e2f81f41421000a202e022000c))))
 (.branch 98
 (.branch 96
 (.leaf 0x8b86d464837c3221f21400b804202e024000c)
 (.branch 97
 (.leaf 0x67665e48038032c1f61400e803202e022000c)
 (.leaf 0x6f260048c37a2ac1f01cc14602a00c002000c)))
 (.branch 99
 (.leaf 0x67665e48c38032c1f614013002e02200c000c)
 (.branch 100
 (.leaf 0x71c65a59a3803022881f214602e022008000c)
 (.leaf 0x71e65a5703e838032c1f0150146022014002000d)))))
 (.branch 106
 (.branch 103
 (.branch 102
 (.leaf 0x6f461845837a36a30e1f014202800a002000c)
 (.leaf 0x8b25e64ba37c1f21a014010204602e022000c))
 (.branch 104
 (.leaf 0x7de5e843437a3061f01d014202a00c002000c)
 (.branch 105
 (.leaf 0x7dc61645c3803341f614011802e02400a000c)
 (.leaf 0x7d86164863803301f6150140130022000b))))
 (.branch 109
 (.branch 107
 (.leaf 0x5de3f437a2081f2182142134056042032000c)
 (.branch 108
 (.leaf 0x5e25c841437c1f01761420ca056052022000c)
 (.leaf 0x65e3801f614413004c02c0008)))
 (.branch 110
 (.leaf 0x88e7466644d837c2f81f21440b804802200c000d)
 (.branch 111
 (.leaf 0x69c4c849e37a34e1f01420d206a022010000c)
 (.leaf 0x5e64c849e37c34e1f21401020a002200c000c))))))
 (.branch 123
 (.branch 117
 (.branch 114
 (.branch 113
 (.leaf 0x7b46684ac37c1f214410209a028000a)
 (.leaf 0x5e84ee37a2d41f01da1420d2042032000b))
 (.branch 115
 (.leaf 0x6464b03801f614213003402a010000a)
 (.branch 116
 (.leaf 0x6125604063801f01741460ca0ae04e026000c)
 (.leaf 0x62c58c3b237c3521f414212c02800e00a000c))))
 (.branch 120
 (.branch 118
 (.leaf 0x5fc5623b037a3642901f414002400a004000c)
 (.branch 119
 (.leaf 0x5fa56240437e2261f014e1440ae024004000c)
 (.leaf 0x5fa56240437e34e1f01440b4064024010000c)))
 (.branch 121
 (.leaf 0x5fe3fa37e2a827c1f41400ee0ae044030000c)
 (.branch 122
 (.leaf 0x64258a3e43802041f21cc14602a00c002000c)
 (.leaf 0x61648640e38024e1f61400b206204e026000c)))))
 (.branch 129
 (.branch 126
 (.branch 124
 (.leaf 0x5e65c845e41437c1f21400ca052022016000c)
 (.branch 125
 (.leaf 0x5e643441237c2881f21aa14002e022008000c)
 (.leaf 0x5e645e41e3f437c1fc1f21400ae022002000c)))
 (.branch 127
 (.leaf 0x5e643442037c3541f214013602201e00c000c)
 (.branch 128
 (.leaf 0x82c75265e4ac37a3221f0156144042022002000d)
 (.leaf 0x71e6604d044a37a3201f0180146094022002000d))))
 (.branch 132
 (.branch 130
 (.leaf 0x8ee78064443037e2ce1f41420d009802400a000d)
 (.branch 131
 (.leaf 0x83677a62c46a3802a41f61420e80a602600a000d)
 (.leaf 0x71c6604a644e37c2f61f21460b809802200e000d)))
 (.branch 133
 (.leaf 0x8c271c66046a37c2f61f21460b809802200e000d)
 (.branch 134
 (.leaf 0x71c6604ec4c037c2f61f21460b809802200e000d)
 (.leaf 0x83075665e48237c2f81f21440b804202200c000d)))))))
 (.branch 157
 (.branch 146
 (.branch 140
 (.branch 137
 (.branch 136
 (.leaf 0x85a78062e4643802a41f61420e809e02600a000d)
 (.leaf 0x86475066443a37c2f81f21440b809202200c000d))
 (.branch 138
 (.leaf 0x88e74666443037c2f81f21440b80ae02200c000d)
 (.branch 139
 (.leaf 0x85a78064642a37e2ce1f41421000a002e024000d)
 (.leaf 0x86475066442a37c2f81f214410209202e022000d))))
 (.branch 143
 (.branch 141
 (.leaf 0x8805e059448c3801fa1f014012a09e05600c000d)
 (.branch 142
 (.leaf 0x7e264845a37c30a1f21460b802e02800e000c)
 (.leaf 0x7dc60043237a3341f017c144026010002000c)))
 (.branch 144
 (.leaf 0x7de64458a38837c3061f614212e02200c00a000d)
 (.branch 145
 (.leaf 0x8e861059845c3801fc1f014011205800a000c)
 (.leaf 0x5e64a047637c2a01f21ca1440ae074004000c)))))
 (.branch 151
 (.branch 148
 (.branch 147
 (.leaf 0x6285a057642e37a34c1f21420e609401e00a000d)
 (.leaf 0x5f65a454c43237a1f41c61440e00a6050020000d))
 (.branch 149
 (.leaf 0x60e57e52646437c1f619c1460f809204e020000d)
 (.branch 150
 (.leaf 0x5fe4cc47437e2a81f41401000ae0a200a000c)
 (.leaf 0x65e4803c23802f62381f614007400a004000c))))
 (.branch 154
 (.branch 152
 (.leaf 0x6484ac37c3221f214407c010004000a)
 (.branch 153
 (.leaf 0x85877e6f845837a2ce1f014206e00a002000c)
 (.leaf 0x6145323a037a2ce1f214010408602e00c000c)))
 (.branch 155
 (.leaf 0x88e66443037c3221f21440b808602e00c000c)
 (.branch 156
 (.leaf 0x6604ae37e3241f4146012010006000a)
 (.leaf 0x5e843437a2d41f01e41ba1420ae002000b))))))
 (.branch 168
 (.branch 162
 (.branch 159
 (.branch 158
 (.leaf 0x64458a38637c32625a1f614202e00a002000c)
 (.leaf 0x65c58838837e3241f614411602e00c00a000c))
 (.branch 160
 (.leaf 0x64845a3a637c2d01f21460d602e01c00e000c)
 (.branch 161
 (.leaf 0x61056045c42838034e1f014010601800a000c)
 (.leaf 0x64058a45a3803521f214212c01c00e00a000c))))
 (.branch 165
 (.branch 163
 (.leaf 0x64458a38637c2d024e1f61420ae00a002000c)
 (.branch 164
 (.leaf 0x65655e4ae37e1f61741460ca0ae04e01a000c)
 (.leaf 0x62c58c3b237c2a61f41bc14213e0ae00a000c)))
 (.branch 166
 (.leaf 0x6585884ae3801f414411201c010000a)
 (.branch 167
 (.leaf 0x6304303f637c2a62321f2144136036032000c)
 (.leaf 0x65c58839037e3242301f614401000a002000c)))))
 (.branch 174
 (.branch 171
 (.branch 169
 (.leaf 0x6604ae37e2fa1f41781461000ae02e000b)
 (.branch 170
 (.leaf 0x6604ae37e3241f41801460d004e02e000b)
 (.leaf 0x65e4ae3803241f61441180100009)))
 (.branch 172
 (.leaf 0x65e4843c23802fa2381f614400c00a004000c)
 (.branch 173
 (.leaf 0x6464b03e838032625e1f6154142002000b)
 (.leaf 0x61645c4163802d228c1f61400d004e02e000c))))
 (.branch 177
 (.branch 175
 (.leaf 0x4203f637c2261f214c1420ae06c002000b)
 (.branch 176
 (.leaf 0x3801f61460700080006)
 (.leaf 0x5c841437c1f21761420ca06c052016000b)))
 (.branch 178
 (.leaf 0x4123802881f61aa1460b807004e02e000b)
 (.branch 179
 (.leaf 0x41e37a2061f018014013406a036034000b)
 (.leaf 0x41e37c1fe1f21781421340ae06c032000b)))))))))
def rawLeaves (i : Nat) : List Nat :=
  let code := leafTable.get i
  (PackedRawNatGrowth.readList 12 (PackedRawNatGrowth.take 5 code)
    (PackedRawNatGrowth.drop 5 code)).1

def leaves : Fin leafCount → List (Fin cellCount) := decodedLeaves rawLeaves
def quota : Nat → Nat
  | 0 => 1
  | 1 => 3
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

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0868

module
prelude
public import RootedSixExtra05GrowthCacheData
public import RootedSixExtra05FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification
public import RootedSubsumedForest0867Packed000
public import RootedSubsumedForest0867Packed001

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0867
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 2170
abbrev nodeCount : Nat := 9525
abbrev leafCount : Nat := 172
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
(.branch 86
 (.branch 43
 (.branch 21
 (.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf 0x7485f855837e1f617a14012805204402a022000d)
 (.leaf 0x7485f855837e3561f614012e04402a02200c000d))
 (.branch 3
 (.leaf 0x74662859237e2281f61420fa048026022000c)
 (.branch 4
 (.leaf 0x71c6585844ae3801f214411202e024022010000d)
 (.leaf 0x71e65855a4843801f015014403a028022002000d))))
 (.branch 7
 (.branch 6
 (.leaf 0x71c6585844ae3801f214e144112024022000c)
 (.leaf 0x67665c58838437e3202301f6140044022002000d))
 (.branch 8
 (.leaf 0x6a065a5883ae3803221f41400ce06204602e022000e)
 (.branch 9
 (.leaf 0x6c263e53445837c2541f615814404402c016004000e)
 (.leaf 0x6706585884aa3801fe1f414011204202400a000d)))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf 0x67261048e3801f014c1420e205a048022000c)
 (.leaf 0x67e65c55a37a2f61f61420e609404202200a000d))
 (.branch 13
 (.leaf 0x72666048037a2f61f21460b609405602200e000d)
 (.branch 14
 (.leaf 0x6f05de48237a34e1f21440b60a005602800c000d)
 (.leaf 0x8246c64ac37c34e1f01440b406a056024010000d))))
 (.branch 18
 (.branch 16
 (.leaf 0x84e5e84ac37e34e1f01420cc0a0058022010000d)
 (.branch 17
 (.leaf 0x76c5e058437c34c1f61401160a604202600a000d)
 (.leaf 0x81e76e58637c34e1f41400fe06a04202400a000d)))
 (.branch 19
 (.leaf 0x8485e458637e34e1f21400fc0a804402200c000d)
 (.branch 20
 (.leaf 0x6c45e04b637c1f019e1460b209e05604e026000d)
 (.leaf 0x76c5e059038637c24e1f61400a6042026002000d))))))
 (.branch 32
 (.branch 26
 (.branch 23
 (.branch 22
 (.leaf 0x8226004b83801f014a1440e209e05a050024000d)
 (.leaf 0x84874458e3da37e2261f214006a044022002000d))
 (.branch 24
 (.leaf 0x6404b83801f214411207805e028010000b)
 (.branch 25
 (.leaf 0x6304b83801f214411209a05e028010000b)
 (.leaf 0x61850c48e37e1f01821460fa09404e026016000d))))
 (.branch 29
 (.branch 27
 (.leaf 0x5e856242a37e3581f014212e09402201a010000d)
 (.branch 28
 (.leaf 0x61455843237e3581f614012e09402601000a000d)
 (.leaf 0x5e658c42c3da37e2261f21400ae098022002000d)))
 (.branch 30
 (.leaf 0x5e25064b237e1f01761420ca0ae098052022000d)
 (.branch 31
 (.leaf 0x61055845c3803561f414012c08002401200a000d)
 (.leaf 0x61053648e3801f0158144112074050024016000d)))))
 (.branch 37
 (.branch 34
 (.branch 33
 (.leaf 0x6105604543803561f014212c072022018012000d)
 (.leaf 0x64058a4563d83801fc1f21400ae072022002000d))
 (.branch 35
 (.leaf 0x71a61058445c3801f21401120ae0aa02200a000d)
 (.branch 36
 (.leaf 0x76a63e50445a37c1f419c1460f80a804e02c000d)
 (.leaf 0x7425f859243237e2281f61400fa0a602600a000d))))
 (.branch 40
 (.branch 38
 (.leaf 0x66e65855e4643802001f41420e20a202800a000d)
 (.branch 39
 (.leaf 0x74662858242c37e34a1f614012e07202600c000d)
 (.leaf 0x67465855a4aa38034c1f01420e4080022012000d)))
 (.branch 41
 (.leaf 0x71c6405924623801fe1f414011207202400a000d)
 (.branch 42
 (.leaf 0x67665859048c3801fe1f214012a08402200c000d)
 (.leaf 0x6585844ae3801f2144112084028010000b)))))))
 (.branch 64
 (.branch 53
 (.branch 48
 (.branch 45
 (.branch 44
 (.leaf 0x65855e4803bc3802081f414007402400a004000d)
 (.leaf 0x65c58443037c3241f614411609802e00c00a000d))
 (.branch 46
 (.leaf 0x64850e45637a2d01f21460ce09202e01c00e000d)
 (.branch 47
 (.leaf 0x6105684643802b01f41420e208007201800a000d)
 (.leaf 0x5fc5684643802b01f41420e209607201800a000d))))
 (.branch 50
 (.branch 49
 (.leaf 0x7ce65c55e37e1f61501440e6038028026022000d)
 (.leaf 0x7ca65e4ae3801f614e14411802a024022000c))
 (.branch 51
 (.leaf 0x6746464b83801f614e14411802a024022000c)
 (.branch 52
 (.leaf 0x67065e4aa38034a1f61400e805004202c024000d)
 (.leaf 0x67065e4aa3803541f614011804202c02400a000d)))))
 (.branch 58
 (.branch 55
 (.branch 54
 (.leaf 0x67261648e3801f614c1420e8048026022000c)
 (.leaf 0x7c462e40437e2501f41420b4064048024022000d))
 (.branch 56
 (.leaf 0x7c462e40637e2521f4178142048024022008000d)
 (.branch 57
 (.leaf 0x6744b237c3541f214411a06c024022014000c)
 (.leaf 0x62e4b237e3541f414213208a024022012000c))))
 (.branch 61
 (.branch 59
 (.leaf 0x7c06604ae37e1fe1f417814603c026024004000d)
 (.branch 60
 (.leaf 0x7c065a5883801f41781460fe03e02e026024000d)
 (.leaf 0x7c26484b037c1f219e1460b804e026022000c)))
 (.branch 62
 (.leaf 0x7c26484b037c1f21a214610202e026022000c)
 (.branch 63
 (.leaf 0x7c462c58c3b037c2501f414202402200a002000d)
 (.leaf 0x7c462a58c3da37e1f21440b606402402200c000d))))))
 (.branch 75
 (.branch 69
 (.branch 66
 (.branch 65
 (.leaf 0x6c45e64b637c1f219e1460b809e04e026022000d)
 (.leaf 0x6c45e64b637c1f21a214610209e02e026022000d))
 (.branch 67
 (.leaf 0x6c86304b637c1f21a214610208a02e026022000d)
 (.branch 68
 (.leaf 0x65e4ae3801f614411809002a028010000b)
 (.leaf 0x6464b83801f614411807802a028010000b))))
 (.branch 72
 (.branch 70
 (.leaf 0x6a066048237e3222001f41400ae038022002000d)
 (.branch 71
 (.leaf 0x6a666042c37e3222001f41400a4038022002000d)
 (.leaf 0x6c86484ac37c2ce1f214e1440ae024004000c)))
 (.branch 73
 (.leaf 0x6a66604ac37e3221f4156140042022006000c)
 (.branch 74
 (.leaf 0x74665c5864d837e2f81f21440b803c02200c000d)
 (.leaf 0x6a866048237e2f81f41420ba042038022018000d)))))
 (.branch 80
 (.branch 77
 (.branch 76
 (.leaf 0x77a62c53e37c2a41f61420e60a603602600a000d)
 (.leaf 0x71c65a5903d83802f61f21460b606202200e000d))
 (.branch 78
 (.leaf 0x6425923ae3802d02061f414608402800e002000d)
 (.branch 79
 (.leaf 0x6125683b43802d21f41460ce08002401200a000d)
 (.leaf 0x69a6604ac37e34e1f414010008e04202400a000d))))
 (.branch 83
 (.branch 81
 (.leaf 0x69e6604ac37e2f81f41420d00ae04e02200a000d)
 (.branch 82
 (.leaf 0x66e65e48038032c1f61420e804203202e00a000d)
 (.leaf 0x67e65e4803802f61f61420e804202200a000c)))
 (.branch 84
 (.leaf 0x67e65e4643802f61f61420e80a202200a000c)
 (.branch 85
 (.leaf 0x65a55e3b43802d21f41460ce08e02401200a000d)
 (.leaf 0x65a5883ae3802d02061f414609002800e002000d))))))))
 (.branch 129
 (.branch 107
 (.branch 96
 (.branch 91
 (.branch 88
 (.branch 87
 (.leaf 0x69e6604ac37e2f81f41421000ae02e022000c)
 (.leaf 0x6a66604ac37e3221f41400d004e04202e022000d))
 (.branch 89
 (.leaf 0x6a866042a37e2f81f41421000a202e022000c)
 (.branch 90
 (.leaf 0x6c66304b637c1f21a014010208a04602e022000d)
 (.leaf 0x67665e48038032c2541f614003a02e022002000d))))
 (.branch 93
 (.branch 92
 (.leaf 0x67665e48038032c1f61400e803202e022000c)
 (.leaf 0x6f260048c37a2ac1f01cc14602a00c002000c))
 (.branch 94
 (.leaf 0x7725e253e37c2b02541f614203602c00a002000d)
 (.branch 95
 (.leaf 0x71e6125683802da1f41460ce03a02e02800e000d)
 (.leaf 0x67465e4b63803021f614213004e02200c00a000d)))))
 (.branch 101
 (.branch 98
 (.branch 97
 (.leaf 0x67665e48c38032c1f614013002e02200c000c)
 (.leaf 0x67465e4b63803021f614e142130022000b))
 (.branch 99
 (.leaf 0x66037e1f414604c02c0140060009)
 (.branch 100
 (.leaf 0x65e3801f614413004c02c0008)
 (.leaf 0x7f274e65c37a3221f01501440ac044022002000d))))
 (.branch 104
 (.branch 102
 (.leaf 0x89a71e66037a3201f017a146094046022002000d)
 (.branch 103
 (.leaf 0x7f077a64437e2ce1f41421000a804802e024000d)
 (.leaf 0x5fc58c3ae37a34a1f414012c0a605602400e000d)))
 (.branch 105
 (.leaf 0x65e4ae38027e1f614403e02c010004000b)
 (.branch 106
 (.leaf 0x6424083803261f214605e014010004000b)
 (.leaf 0x62858c37e1f214212e04803401e010000b))))))
 (.branch 118
 (.branch 112
 (.branch 109
 (.branch 108
 (.leaf 0x64458a37c1f614212e03c03402a010000b)
 (.leaf 0x65e4843803561f614411805002c00c00a000c))
 (.branch 110
 (.leaf 0x6464d63803261f61420e804a03202e00a000c)
 (.branch 111
 (.leaf 0x60048837a1f01ca1440ba0ae05002e024000c)
 (.leaf 0x61845c37a1f01d61460d204e03002e026000c))))
 (.branch 115
 (.branch 113
 (.leaf 0x6464b03803541f614213004e02a00c00a000c)
 (.branch 114
 (.leaf 0x6464b03801f614213003402a010000a)
 (.leaf 0x60048837a1f01cc1440ea0ae03002e024000c)))
 (.branch 116
 (.leaf 0x6125604063801f01741460ca0ae04e026000c)
 (.branch 117
 (.leaf 0x62c58c3b237c3521f414212c02800e00a000c)
 (.leaf 0x5fa56240437e2261f014e1440ae024004000c)))))
 (.branch 123
 (.branch 120
 (.branch 119
 (.leaf 0x5fa56240437e34e1f01440b4064024010000c)
 (.leaf 0x64258a3e43802041f21cc14602a00c002000c))
 (.branch 121
 (.leaf 0x61648640e38024e1f61400b206204e026000c)
 (.branch 122
 (.leaf 0x71e66048037a3201f017a1460ae094022002000d)
 (.leaf 0x67465c59038637c2f61f61420e609806602200a000e))))
 (.branch 126
 (.branch 124
 (.leaf 0x67665c58838637a3201f614011609405802200a000e)
 (.branch 125
 (.leaf 0x67065855a4aa38034c1f014011808004201a00a000e)
 (.leaf 0x71e66048037a3201f01460ea0ae094030022000d)))
 (.branch 127
 (.leaf 0x72064845637a32e1f01460ea09203002e024000d)
 (.branch 128
 (.leaf 0x72064846237a32e1f0152146092024012002000d)
 (.leaf 0x72061846437c3041f21460b809202e02800e000d)))))))
 (.branch 150
 (.branch 139
 (.branch 134
 (.branch 131
 (.branch 130
 (.leaf 0x67465c59038837c3021f614212e09802200c00a000e)
 (.leaf 0x67264053c4b83801f014c14011207e044016000d))
 (.branch 132
 (.leaf 0x6285844aa3ba3801f214209c01600a002000c)
 (.branch 133
 (.leaf 0x6585864ac37c1f414409a01c010004000b)
 (.leaf 0x6604aa37c3201f2146098084012004000b))))
 (.branch 136
 (.branch 135
 (.leaf 0x6f260048037a2cc1f01460ae08a00e002000c)
 (.leaf 0x6fa5e848037a2f61f014609e08a00e002000c))
 (.branch 137
 (.leaf 0x6484ac37c3221f214407c010004000a)
 (.branch 138
 (.leaf 0x66048237e2f81f414010007604e02e00a000c)
 (.leaf 0x65e45c3802f61f61401180a207403000a000c)))))
 (.branch 144
 (.branch 141
 (.branch 140
 (.leaf 0x61845c37a2fc1f01ce1460ae02e00a002000c)
 (.leaf 0x61848637a2fc1f01d414604e02e00a002000c))
 (.branch 142
 (.leaf 0x6604ae37e3241f4146012010006000a)
 (.branch 143
 (.leaf 0x64645a3803261f61a41420ae02e00a008000c)
 (.leaf 0x6464b03803261f61aa14204e02e00a008000c))))
 (.branch 147
 (.branch 145
 (.leaf 0x64458a38637c32625a1f614202e00a002000c)
 (.branch 146
 (.leaf 0x65a5883ae3803241f41460ce06203002e00e000d)
 (.leaf 0x65a5883b23803241f415614603c03000e006000d)))
 (.branch 148
 (.leaf 0x65c58838837e3241f614411602e00c00a000c)
 (.branch 149
 (.leaf 0x6484b037c3261f2156146036016014002000c)
 (.leaf 0x65855e4ae3b438034e1f414401801000a002000d))))))
 (.branch 161
 (.branch 155
 (.branch 152
 (.branch 151
 (.leaf 0x65e5b04843803241f61440b603a02e01e00c000d)
 (.leaf 0x64058a45a3803521f214212c01c00e00a000c))
 (.branch 153
 (.leaf 0x64458a38637c2d024e1f61420ae00a002000c)
 (.branch 154
 (.leaf 0x65655e4ae37e1f61741460ca0ae04e01a000c)
 (.leaf 0x65e4843ae3803242021f61440ae01e00c002000d))))
 (.branch 158
 (.branch 156
 (.leaf 0x60e56045c37a2001f61ce1460ae02000a002000d)
 (.branch 157
 (.leaf 0x63e58a45a37c2521f61460fe0ae02e00e00a000d)
 (.leaf 0x65a5883b23802fa1f41460fe0ae02e00e00a000d)))
 (.branch 159
 (.leaf 0x6604ae37e3241f414603c01c012004000b)
 (.branch 160
 (.leaf 0x6585884ae3801f414411201c010000a)
 (.leaf 0x65e4ae3ba3803242021f614404e01e00c002000d)))))
 (.branch 166
 (.branch 163
 (.branch 162
 (.leaf 0x61256038a3802fc1f01d414604002e00a002000d)
 (.leaf 0x63e53445a37c25c1f61460fe06202e00e00a000d))
 (.branch 164
 (.leaf 0x65a55e3bc3802fa1f41460fe06202e00e00a000d)
 (.branch 165
 (.leaf 0x65c58839037e3242301f614401000a002000c)
 (.leaf 0x66048437e2fa1f414610004e02e00e00a000c))))
 (.branch 169
 (.branch 167
 (.leaf 0x65e4843803241f61440e80ae03002e00c000c)
 (.branch 168
 (.leaf 0x6604ae37e2fa1f41781461000ae02e000b)
 (.leaf 0x6604ae37e3241f41801460d004e02e000b)))
 (.branch 170
 (.leaf 0x65e4ae3803241f614411804e02e00c00a000c)
 (.branch 171
 (.leaf 0x65e4ae3803241f61441180100009)
 (.leaf 0x3801f61460700080006)))))))))
def rawLeaves (i : Nat) : List Nat :=
  let code := leafTable.get i
  (PackedRawNatGrowth.readList 12 (PackedRawNatGrowth.take 5 code)
    (PackedRawNatGrowth.drop 5 code)).1

def leaves : Fin leafCount → List (Fin cellCount) := decodedLeaves rawLeaves
def quota : Nat → Nat
  | 0 => 1
  | 1 => 4
  | 2 => 6
  | 3 => 3
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

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0867

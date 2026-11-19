module
prelude
public meta import LowerSchemas.FiniteSmallSubsumedForest
public meta import CertificateNumbers
public import RootedSmallCacheData
public import RootedSmallGeneratorWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification
public import SmallSubsumedForest08Packed000
public import SmallSubsumedForest08Packed001
public import SmallSubsumedForest08Packed002
public import SmallSubsumedForest08Packed003
public import SmallSubsumedForest08Packed004
public import SmallSubsumedForest08Packed005
public import SmallSubsumedForest08Packed006
public import SmallSubsumedForest08Packed007
public import SmallSubsumedForest08Packed008
public import SmallSubsumedForest08Packed009

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest08
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 3436
abbrev nodeCount : Nat := 61753
abbrev leafCount : Nat := 257
cert_widths_4 16 9
def blocks : Table PackedRawNatGrowth.Block :=
(.branch 250
 (.branch 100
 (.branch 50
 nodeBlocks000
 nodeBlocks001)
 (.branch 150
 nodeBlocks002
 (.branch 200
 nodeBlocks003
 nodeBlocks004)))
 (.branch 350
 (.branch 300
 nodeBlocks005
 nodeBlocks006)
 (.branch 400
 nodeBlocks007
 (.branch 450
 nodeBlocks008
 nodeBlocks009))))
def counterTable : Table Nat :=
(.branch 250
 (.branch 100
 (.branch 50
 nodeCounters000
 nodeCounters001)
 (.branch 150
 nodeCounters002
 (.branch 200
 nodeCounters003
 nodeCounters004)))
 (.branch 350
 (.branch 300
 nodeCounters005
 nodeCounters006)
 (.branch 400
 nodeCounters007
 (.branch 450
 nodeCounters008
 nodeCounters009))))
cert_codes_4
cert_counters_4
cert_rawNodes_4
def leafTable : Table Nat :=
(.branch 128
 (.branch 64
 (.branch 32
 (.branch 16
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf (certNat% 0))
 (.leaf (certNat% 1)))
 (.branch 3
 (.leaf (certNat% 2))
 (.leaf (certNat% 3))))
 (.branch 6
 (.branch 5
 (.leaf (certNat% 4))
 (.leaf (certNat% 5)))
 (.branch 7
 (.leaf (certNat% 6))
 (.leaf (certNat% 7)))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf (certNat% 8))
 (.leaf (certNat% 9)))
 (.branch 11
 (.leaf (certNat% 10))
 (.leaf (certNat% 11))))
 (.branch 14
 (.branch 13
 (.leaf (certNat% 12))
 (.leaf (certNat% 13)))
 (.branch 15
 (.leaf (certNat% 14))
 (.leaf (certNat% 15))))))
 (.branch 24
 (.branch 20
 (.branch 18
 (.branch 17
 (.leaf (certNat% 16))
 (.leaf (certNat% 17)))
 (.branch 19
 (.leaf (certNat% 18))
 (.leaf (certNat% 19))))
 (.branch 22
 (.branch 21
 (.leaf (certNat% 20))
 (.leaf (certNat% 21)))
 (.branch 23
 (.leaf (certNat% 22))
 (.leaf (certNat% 23)))))
 (.branch 28
 (.branch 26
 (.branch 25
 (.leaf (certNat% 24))
 (.leaf (certNat% 25)))
 (.branch 27
 (.leaf (certNat% 26))
 (.leaf (certNat% 27))))
 (.branch 30
 (.branch 29
 (.leaf (certNat% 28))
 (.leaf (certNat% 29)))
 (.branch 31
 (.leaf (certNat% 30))
 (.leaf (certNat% 31)))))))
 (.branch 48
 (.branch 40
 (.branch 36
 (.branch 34
 (.branch 33
 (.leaf (certNat% 32))
 (.leaf (certNat% 33)))
 (.branch 35
 (.leaf (certNat% 34))
 (.leaf (certNat% 35))))
 (.branch 38
 (.branch 37
 (.leaf (certNat% 36))
 (.leaf (certNat% 37)))
 (.branch 39
 (.leaf (certNat% 38))
 (.leaf (certNat% 39)))))
 (.branch 44
 (.branch 42
 (.branch 41
 (.leaf (certNat% 40))
 (.leaf (certNat% 41)))
 (.branch 43
 (.leaf (certNat% 42))
 (.leaf (certNat% 43))))
 (.branch 46
 (.branch 45
 (.leaf (certNat% 44))
 (.leaf (certNat% 45)))
 (.branch 47
 (.leaf (certNat% 46))
 (.leaf (certNat% 47))))))
 (.branch 56
 (.branch 52
 (.branch 50
 (.branch 49
 (.leaf (certNat% 48))
 (.leaf (certNat% 49)))
 (.branch 51
 (.leaf (certNat% 50))
 (.leaf (certNat% 51))))
 (.branch 54
 (.branch 53
 (.leaf (certNat% 52))
 (.leaf (certNat% 53)))
 (.branch 55
 (.leaf (certNat% 54))
 (.leaf (certNat% 55)))))
 (.branch 60
 (.branch 58
 (.branch 57
 (.leaf (certNat% 56))
 (.leaf (certNat% 57)))
 (.branch 59
 (.leaf (certNat% 58))
 (.leaf (certNat% 59))))
 (.branch 62
 (.branch 61
 (.leaf (certNat% 60))
 (.leaf (certNat% 61)))
 (.branch 63
 (.leaf (certNat% 62))
 (.leaf (certNat% 63))))))))
 (.branch 96
 (.branch 80
 (.branch 72
 (.branch 68
 (.branch 66
 (.branch 65
 (.leaf (certNat% 64))
 (.leaf (certNat% 65)))
 (.branch 67
 (.leaf (certNat% 66))
 (.leaf (certNat% 67))))
 (.branch 70
 (.branch 69
 (.leaf (certNat% 68))
 (.leaf (certNat% 69)))
 (.branch 71
 (.leaf (certNat% 70))
 (.leaf (certNat% 71)))))
 (.branch 76
 (.branch 74
 (.branch 73
 (.leaf (certNat% 72))
 (.leaf (certNat% 73)))
 (.branch 75
 (.leaf (certNat% 74))
 (.leaf (certNat% 75))))
 (.branch 78
 (.branch 77
 (.leaf (certNat% 76))
 (.leaf (certNat% 77)))
 (.branch 79
 (.leaf (certNat% 78))
 (.leaf (certNat% 79))))))
 (.branch 88
 (.branch 84
 (.branch 82
 (.branch 81
 (.leaf (certNat% 80))
 (.leaf (certNat% 81)))
 (.branch 83
 (.leaf (certNat% 82))
 (.leaf (certNat% 83))))
 (.branch 86
 (.branch 85
 (.leaf (certNat% 84))
 (.leaf (certNat% 85)))
 (.branch 87
 (.leaf (certNat% 86))
 (.leaf (certNat% 87)))))
 (.branch 92
 (.branch 90
 (.branch 89
 (.leaf (certNat% 88))
 (.leaf (certNat% 89)))
 (.branch 91
 (.leaf (certNat% 90))
 (.leaf (certNat% 91))))
 (.branch 94
 (.branch 93
 (.leaf (certNat% 92))
 (.leaf (certNat% 93)))
 (.branch 95
 (.leaf (certNat% 94))
 (.leaf (certNat% 95)))))))
 (.branch 112
 (.branch 104
 (.branch 100
 (.branch 98
 (.branch 97
 (.leaf (certNat% 96))
 (.leaf (certNat% 97)))
 (.branch 99
 (.leaf (certNat% 98))
 (.leaf (certNat% 99))))
 (.branch 102
 (.branch 101
 (.leaf (certNat% 100))
 (.leaf (certNat% 101)))
 (.branch 103
 (.leaf (certNat% 102))
 (.leaf (certNat% 103)))))
 (.branch 108
 (.branch 106
 (.branch 105
 (.leaf (certNat% 104))
 (.leaf (certNat% 105)))
 (.branch 107
 (.leaf (certNat% 106))
 (.leaf (certNat% 107))))
 (.branch 110
 (.branch 109
 (.leaf (certNat% 108))
 (.leaf (certNat% 109)))
 (.branch 111
 (.leaf (certNat% 110))
 (.leaf (certNat% 111))))))
 (.branch 120
 (.branch 116
 (.branch 114
 (.branch 113
 (.leaf (certNat% 112))
 (.leaf (certNat% 113)))
 (.branch 115
 (.leaf (certNat% 114))
 (.leaf (certNat% 115))))
 (.branch 118
 (.branch 117
 (.leaf (certNat% 116))
 (.leaf (certNat% 117)))
 (.branch 119
 (.leaf (certNat% 118))
 (.leaf (certNat% 119)))))
 (.branch 124
 (.branch 122
 (.branch 121
 (.leaf (certNat% 120))
 (.leaf (certNat% 121)))
 (.branch 123
 (.leaf (certNat% 122))
 (.leaf (certNat% 123))))
 (.branch 126
 (.branch 125
 (.leaf (certNat% 124))
 (.leaf (certNat% 125)))
 (.branch 127
 (.leaf (certNat% 126))
 (.leaf (certNat% 127)))))))))
 (.branch 192
 (.branch 160
 (.branch 144
 (.branch 136
 (.branch 132
 (.branch 130
 (.branch 129
 (.leaf (certNat% 128))
 (.leaf (certNat% 129)))
 (.branch 131
 (.leaf (certNat% 130))
 (.leaf (certNat% 131))))
 (.branch 134
 (.branch 133
 (.leaf (certNat% 132))
 (.leaf (certNat% 133)))
 (.branch 135
 (.leaf (certNat% 134))
 (.leaf (certNat% 135)))))
 (.branch 140
 (.branch 138
 (.branch 137
 (.leaf (certNat% 136))
 (.leaf (certNat% 137)))
 (.branch 139
 (.leaf (certNat% 138))
 (.leaf (certNat% 139))))
 (.branch 142
 (.branch 141
 (.leaf (certNat% 140))
 (.leaf (certNat% 141)))
 (.branch 143
 (.leaf (certNat% 142))
 (.leaf (certNat% 143))))))
 (.branch 152
 (.branch 148
 (.branch 146
 (.branch 145
 (.leaf (certNat% 144))
 (.leaf (certNat% 145)))
 (.branch 147
 (.leaf (certNat% 146))
 (.leaf (certNat% 147))))
 (.branch 150
 (.branch 149
 (.leaf (certNat% 148))
 (.leaf (certNat% 149)))
 (.branch 151
 (.leaf (certNat% 150))
 (.leaf (certNat% 151)))))
 (.branch 156
 (.branch 154
 (.branch 153
 (.leaf (certNat% 152))
 (.leaf (certNat% 153)))
 (.branch 155
 (.leaf (certNat% 154))
 (.leaf (certNat% 155))))
 (.branch 158
 (.branch 157
 (.leaf (certNat% 156))
 (.leaf (certNat% 157)))
 (.branch 159
 (.leaf (certNat% 158))
 (.leaf (certNat% 159)))))))
 (.branch 176
 (.branch 168
 (.branch 164
 (.branch 162
 (.branch 161
 (.leaf (certNat% 160))
 (.leaf (certNat% 161)))
 (.branch 163
 (.leaf (certNat% 162))
 (.leaf (certNat% 163))))
 (.branch 166
 (.branch 165
 (.leaf (certNat% 164))
 (.leaf (certNat% 165)))
 (.branch 167
 (.leaf (certNat% 166))
 (.leaf (certNat% 167)))))
 (.branch 172
 (.branch 170
 (.branch 169
 (.leaf (certNat% 168))
 (.leaf (certNat% 169)))
 (.branch 171
 (.leaf (certNat% 170))
 (.leaf (certNat% 171))))
 (.branch 174
 (.branch 173
 (.leaf (certNat% 172))
 (.leaf (certNat% 173)))
 (.branch 175
 (.leaf (certNat% 174))
 (.leaf (certNat% 175))))))
 (.branch 184
 (.branch 180
 (.branch 178
 (.branch 177
 (.leaf (certNat% 176))
 (.leaf (certNat% 177)))
 (.branch 179
 (.leaf (certNat% 178))
 (.leaf (certNat% 179))))
 (.branch 182
 (.branch 181
 (.leaf (certNat% 180))
 (.leaf (certNat% 181)))
 (.branch 183
 (.leaf (certNat% 182))
 (.leaf (certNat% 183)))))
 (.branch 188
 (.branch 186
 (.branch 185
 (.leaf (certNat% 184))
 (.leaf (certNat% 185)))
 (.branch 187
 (.leaf (certNat% 186))
 (.leaf (certNat% 187))))
 (.branch 190
 (.branch 189
 (.leaf (certNat% 188))
 (.leaf (certNat% 189)))
 (.branch 191
 (.leaf (certNat% 190))
 (.leaf (certNat% 191))))))))
 (.branch 224
 (.branch 208
 (.branch 200
 (.branch 196
 (.branch 194
 (.branch 193
 (.leaf (certNat% 192))
 (.leaf (certNat% 193)))
 (.branch 195
 (.leaf (certNat% 194))
 (.leaf (certNat% 195))))
 (.branch 198
 (.branch 197
 (.leaf (certNat% 196))
 (.leaf (certNat% 197)))
 (.branch 199
 (.leaf (certNat% 198))
 (.leaf (certNat% 199)))))
 (.branch 204
 (.branch 202
 (.branch 201
 (.leaf (certNat% 200))
 (.leaf (certNat% 201)))
 (.branch 203
 (.leaf (certNat% 202))
 (.leaf (certNat% 203))))
 (.branch 206
 (.branch 205
 (.leaf (certNat% 204))
 (.leaf (certNat% 205)))
 (.branch 207
 (.leaf (certNat% 206))
 (.leaf (certNat% 207))))))
 (.branch 216
 (.branch 212
 (.branch 210
 (.branch 209
 (.leaf (certNat% 208))
 (.leaf (certNat% 209)))
 (.branch 211
 (.leaf (certNat% 210))
 (.leaf (certNat% 211))))
 (.branch 214
 (.branch 213
 (.leaf (certNat% 212))
 (.leaf (certNat% 213)))
 (.branch 215
 (.leaf (certNat% 214))
 (.leaf (certNat% 215)))))
 (.branch 220
 (.branch 218
 (.branch 217
 (.leaf (certNat% 216))
 (.leaf (certNat% 217)))
 (.branch 219
 (.leaf (certNat% 218))
 (.leaf (certNat% 219))))
 (.branch 222
 (.branch 221
 (.leaf (certNat% 220))
 (.leaf (certNat% 221)))
 (.branch 223
 (.leaf (certNat% 222))
 (.leaf (certNat% 223)))))))
 (.branch 240
 (.branch 232
 (.branch 228
 (.branch 226
 (.branch 225
 (.leaf (certNat% 224))
 (.leaf (certNat% 225)))
 (.branch 227
 (.leaf (certNat% 226))
 (.leaf (certNat% 227))))
 (.branch 230
 (.branch 229
 (.leaf (certNat% 228))
 (.leaf (certNat% 229)))
 (.branch 231
 (.leaf (certNat% 230))
 (.leaf (certNat% 231)))))
 (.branch 236
 (.branch 234
 (.branch 233
 (.leaf (certNat% 232))
 (.leaf (certNat% 233)))
 (.branch 235
 (.leaf (certNat% 234))
 (.leaf (certNat% 235))))
 (.branch 238
 (.branch 237
 (.leaf (certNat% 236))
 (.leaf (certNat% 237)))
 (.branch 239
 (.leaf (certNat% 238))
 (.leaf (certNat% 239))))))
 (.branch 248
 (.branch 244
 (.branch 242
 (.branch 241
 (.leaf (certNat% 240))
 (.leaf (certNat% 241)))
 (.branch 243
 (.leaf (certNat% 242))
 (.leaf (certNat% 243))))
 (.branch 246
 (.branch 245
 (.leaf (certNat% 244))
 (.leaf (certNat% 245)))
 (.branch 247
 (.leaf (certNat% 246))
 (.leaf (certNat% 247)))))
 (.branch 252
 (.branch 250
 (.branch 249
 (.leaf (certNat% 248))
 (.leaf (certNat% 249)))
 (.branch 251
 (.leaf (certNat% 250))
 (.leaf (certNat% 251))))
 (.branch 254
 (.branch 253
 (.leaf (certNat% 252))
 (.leaf (certNat% 253)))
 (.branch 255
 (.leaf (certNat% 254))
 (.branch 256
 (.leaf (certNat% 255))
 (.leaf (certNat% 256)))))))))))
def rawLeaves (i : Nat) : List Nat :=
  let code := leafTable.get i
  (PackedRawNatGrowth.readList 12 (PackedRawNatGrowth.take 5 code)
    (PackedRawNatGrowth.drop 5 code)).1

cert_leaves_4
cert_quota_5 2 2 7
cert_nodeTest_6
cert_nodeTest_sound_5
cert_leafTest_6
end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest08

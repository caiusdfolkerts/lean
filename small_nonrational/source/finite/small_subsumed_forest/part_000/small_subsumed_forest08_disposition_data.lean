module
prelude
public import SmallSubsumedForest08Data
public import RawLeafCertificate
public import OldTerminalMatches.M000

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest08
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 128
 (.branch 64
 (.branch 32
 (.branch 16
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf (.quota 2))
 (.leaf (.incidence 3)))
 (.branch 3
 (.leaf (.incidence 3))
 (.leaf (.quota 2))))
 (.branch 6
 (.branch 5
 (.leaf (.incidence 8))
 (.leaf (.incidence 9)))
 (.leaf (.incidence 3))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf (.incidence 3))
 (.leaf (.matching Nonrational.OldTerminalMatches.M000.r0015)))
 (.branch 11
 (.leaf (.incidence 9))
 (.leaf (.incidence 8))))
 (.branch 14
 (.branch 13
 (.leaf (.incidence 9))
 (.leaf (.incidence 3)))
 (.leaf (.incidence 3)))))
 (.branch 24
 (.branch 20
 (.leaf (.incidence 3))
 (.branch 22
 (.leaf (.incidence 3))
 (.branch 23
 (.leaf (.incidence 5))
 (.leaf (.incidence 7)))))
 (.leaf (.incidence 3))))
 (.branch 48
 (.branch 40
 (.branch 36
 (.branch 34
 (.branch 33
 (.leaf (.quota 1))
 (.leaf (.incidence 3)))
 (.branch 35
 (.leaf (.incidence 6))
 (.leaf (.incidence 5))))
 (.branch 38
 (.branch 37
 (.leaf (.incidence 5))
 (.leaf (.incidence 3)))
 (.leaf (.incidence 3))))
 (.branch 44
 (.branch 42
 (.leaf (.incidence 3))
 (.branch 43
 (.leaf (.incidence 3))
 (.leaf (.matching Nonrational.OldTerminalMatches.M000.r0016))))
 (.branch 46
 (.leaf (.incidence 3))
 (.branch 47
 (.leaf (.incidence 4))
 (.leaf (.incidence 3))))))
 (.branch 56
 (.branch 52
 (.branch 50
 (.leaf (.incidence 3))
 (.branch 51
 (.leaf (.incidence 3))
 (.leaf (.incidence 4))))
 (.branch 54
 (.leaf (.incidence 3))
 (.branch 55
 (.leaf (.incidence 4))
 (.leaf (.quota 2)))))
 (.branch 60
 (.branch 58
 (.branch 57
 (.leaf (.incidence 4))
 (.leaf (.incidence 9)))
 (.leaf (.incidence 3)))
 (.branch 62
 (.branch 61
 (.leaf (.incidence 3))
 (.leaf (.incidence 9)))
 (.branch 63
 (.leaf (.incidence 6))
 (.leaf (.incidence 5))))))))
 (.branch 96
 (.branch 80
 (.branch 72
 (.branch 68
 (.leaf (.incidence 3))
 (.branch 70
 (.leaf (.incidence 3))
 (.branch 71
 (.leaf (.incidence 3))
 (.leaf (.quota 2)))))
 (.branch 76
 (.branch 74
 (.leaf (.incidence 6))
 (.branch 75
 (.leaf (.incidence 9))
 (.leaf (.incidence 5))))
 (.branch 78
 (.branch 77
 (.leaf (.incidence 5))
 (.leaf (.incidence 9)))
 (.branch 79
 (.leaf (.incidence 5))
 (.leaf (.incidence 6))))))
 (.branch 88
 (.branch 84
 (.branch 82
 (.branch 81
 (.leaf (.incidence 5))
 (.leaf (.incidence 6)))
 (.branch 83
 (.leaf (.incidence 6))
 (.leaf (.quota 2))))
 (.branch 86
 (.leaf (.incidence 6))
 (.branch 87
 (.leaf (.incidence 9))
 (.leaf (.incidence 6)))))
 (.branch 92
 (.branch 90
 (.branch 89
 (.leaf (.matching Nonrational.OldTerminalMatches.M000.r0017))
 (.leaf (.incidence 9)))
 (.branch 91
 (.leaf (.incidence 9))
 (.leaf (.incidence 6))))
 (.branch 94
 (.leaf (.incidence 5))
 (.leaf (.incidence 3))))))
 (.branch 112
 (.branch 104
 (.branch 100
 (.branch 98
 (.branch 97
 (.leaf (.incidence 3))
 (.leaf (.quota 2)))
 (.leaf (.incidence 3)))
 (.leaf (.incidence 3)))
 (.branch 108
 (.branch 106
 (.branch 105
 (.leaf (.incidence 3))
 (.leaf (.quota 2)))
 (.leaf (.incidence 6)))
 (.leaf (.incidence 5))))
 (.branch 120
 (.branch 116
 (.branch 114
 (.branch 113
 (.leaf (.quota 2))
 (.leaf (.incidence 5)))
 (.leaf (.incidence 5)))
 (.branch 118
 (.leaf (.incidence 3))
 (.branch 119
 (.leaf (.incidence 3))
 (.leaf (.incidence 5)))))
 (.branch 124
 (.branch 122
 (.branch 121
 (.leaf (.incidence 5))
 (.leaf (.incidence 3)))
 (.branch 123
 (.leaf (.quota 2))
 (.leaf (.incidence 5))))
 (.branch 126
 (.branch 125
 (.leaf (.incidence 3))
 (.leaf (.incidence 5)))
 (.branch 127
 (.leaf (.incidence 5))
 (.leaf (.incidence 3)))))))))
 (.branch 192
 (.branch 160
 (.branch 144
 (.branch 136
 (.branch 132
 (.branch 130
 (.leaf (.incidence 5))
 (.branch 131
 (.leaf (.incidence 5))
 (.leaf (.incidence 3))))
 (.branch 134
 (.branch 133
 (.leaf (.incidence 6))
 (.leaf (.quota 2)))
 (.branch 135
 (.leaf (.quota 2))
 (.leaf (.incidence 3)))))
 (.branch 140
 (.branch 138
 (.branch 137
 (.leaf (.incidence 5))
 (.leaf (.incidence 6)))
 (.branch 139
 (.leaf (.incidence 5))
 (.leaf (.incidence 6))))
 (.branch 142
 (.leaf (.incidence 3))
 (.branch 143
 (.leaf (.incidence 5))
 (.leaf (.incidence 3))))))
 (.branch 152
 (.branch 148
 (.branch 146
 (.branch 145
 (.leaf (.incidence 3))
 (.leaf (.incidence 4)))
 (.branch 147
 (.leaf (.incidence 4))
 (.leaf (.quota 1))))
 (.leaf (.incidence 4)))
 (.branch 156
 (.leaf (.incidence 4))
 (.branch 158
 (.branch 157
 (.leaf (.incidence 4))
 (.leaf (.quota 1)))
 (.leaf (.incidence 4))))))
 (.branch 176
 (.branch 168
 (.branch 164
 (.leaf (.incidence 4))
 (.branch 166
 (.leaf (.incidence 4))
 (.leaf (.quota 2))))
 (.leaf (.incidence 3)))
 (.branch 184
 (.branch 180
 (.branch 178
 (.branch 177
 (.leaf (.quota 2))
 (.leaf (.incidence 3)))
 (.branch 179
 (.leaf (.incidence 6))
 (.leaf (.incidence 7))))
 (.branch 182
 (.leaf (.incidence 5))
 (.branch 183
 (.leaf (.quota 2))
 (.leaf (.incidence 3)))))
 (.branch 188
 (.branch 186
 (.leaf (.incidence 6))
 (.branch 187
 (.leaf (.incidence 6))
 (.leaf (.incidence 4))))
 (.leaf (.incidence 4))))))
 (.branch 224
 (.branch 208
 (.branch 200
 (.branch 196
 (.leaf (.incidence 4))
 (.branch 198
 (.leaf (.incidence 7))
 (.branch 199
 (.leaf (.incidence 7))
 (.leaf (.incidence 5)))))
 (.branch 204
 (.branch 202
 (.branch 201
 (.leaf (.incidence 6))
 (.leaf (.incidence 8)))
 (.leaf (.incidence 6)))
 (.branch 206
 (.branch 205
 (.leaf (.incidence 6))
 (.leaf (.incidence 7)))
 (.branch 207
 (.leaf (.incidence 6))
 (.leaf (.matching Nonrational.OldTerminalMatches.M000.r0018))))))
 (.branch 216
 (.branch 212
 (.branch 210
 (.branch 209
 (.leaf (.incidence 6))
 (.leaf (.incidence 8)))
 (.branch 211
 (.leaf (.incidence 6))
 (.leaf (.incidence 5))))
 (.branch 214
 (.branch 213
 (.leaf (.incidence 6))
 (.leaf (.quota 2)))
 (.leaf (.incidence 6))))
 (.branch 220
 (.branch 218
 (.leaf (.incidence 7))
 (.leaf (.incidence 9)))
 (.branch 222
 (.leaf (.incidence 7))
 (.leaf (.incidence 9))))))
 (.branch 240
 (.branch 232
 (.branch 228
 (.branch 226
 (.leaf (.incidence 6))
 (.branch 227
 (.leaf (.incidence 6))
 (.leaf (.incidence 7))))
 (.branch 230
 (.branch 229
 (.leaf (.incidence 7))
 (.leaf (.incidence 9)))
 (.branch 231
 (.leaf (.incidence 9))
 (.leaf (.matching Nonrational.OldTerminalMatches.M000.r0019)))))
 (.branch 236
 (.branch 234
 (.leaf (.incidence 6))
 (.leaf (.incidence 4)))
 (.branch 238
 (.branch 237
 (.leaf (.incidence 4))
 (.leaf (.incidence 3)))
 (.branch 239
 (.leaf (.incidence 4))
 (.leaf (.quota 1))))))
 (.branch 248
 (.branch 244
 (.branch 242
 (.leaf (.incidence 3))
 (.branch 243
 (.leaf (.incidence 3))
 (.leaf (.incidence 4))))
 (.branch 246
 (.branch 245
 (.leaf (.quota 1))
 (.leaf (.incidence 4)))
 (.leaf (.incidence 4))))
 (.branch 252
 (.branch 250
 (.branch 249
 (.leaf (.quota 2))
 (.leaf (.incidence 4)))
 (.leaf (.incidence 4)))
 (.branch 254
 (.leaf (.incidence 4))
 (.branch 255
 (.leaf (.incidence 4))
 (.leaf (.incidence 3))))))))))
def disposition (j : Fin leafCount) := dispositionTable.get j.val
def dispositionTest (i : Nat) : Bool := RawLeafCertificate.check quota
  ((rawLeaves i).map RootedSmallCache.rawCells) (dispositionTable.get i)

end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest08

module
prelude
public import RootedSubsumedForest0364Data
public import RawLeafCertificate
public import OldTerminalMatches.M017
public import OldTerminalMatches.M018

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0364
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 175
 (.branch 87
 (.branch 43
 (.branch 21
 (.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf (.incidence 5))
 (.leaf (.quota 2)))
 (.branch 3
 (.leaf (.quota 2))
 (.branch 4
 (.leaf (.matching Nonrational.OldTerminalMatches.M017.r1121))
 (.leaf (.matching Nonrational.OldTerminalMatches.M017.r1122)))))
 (.branch 7
 (.leaf (.quota 2))
 (.branch 8
 (.leaf (.incidence 5))
 (.branch 9
 (.leaf (.quota 1))
 (.leaf (.matching Nonrational.OldTerminalMatches.M017.r1123))))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf (.matching Nonrational.OldTerminalMatches.M017.r1124))
 (.leaf (.matching Nonrational.OldTerminalMatches.M017.r1125)))
 (.branch 13
 (.leaf (.matching Nonrational.OldTerminalMatches.M017.r1126))
 (.branch 14
 (.leaf (.matching Nonrational.OldTerminalMatches.M017.r1127))
 (.leaf (.quota 1)))))
 (.branch 18
 (.branch 16
 (.leaf (.matching Nonrational.OldTerminalMatches.M017.r1128))
 (.branch 17
 (.leaf (.matching Nonrational.OldTerminalMatches.M017.r1129))
 (.leaf (.matching Nonrational.OldTerminalMatches.M017.r1130))))
 (.branch 19
 (.leaf (.matching Nonrational.OldTerminalMatches.M017.r1131))
 (.branch 20
 (.leaf (.matching Nonrational.OldTerminalMatches.M017.r1132))
 (.leaf (.matching Nonrational.OldTerminalMatches.M017.r1133)))))))
 (.branch 32
 (.branch 26
 (.branch 23
 (.branch 22
 (.leaf (.matching Nonrational.OldTerminalMatches.M017.r1134))
 (.leaf (.matching Nonrational.OldTerminalMatches.M017.r1135)))
 (.branch 24
 (.leaf (.quota 1))
 (.branch 25
 (.leaf (.incidence 5))
 (.leaf (.matching Nonrational.OldTerminalMatches.M017.r1136)))))
 (.branch 29
 (.branch 27
 (.leaf (.matching Nonrational.OldTerminalMatches.M017.r1137))
 (.branch 28
 (.leaf (.matching Nonrational.OldTerminalMatches.M017.r1138))
 (.leaf (.quota 1))))
 (.leaf (.quota 2))))
 (.leaf (.quota 2))))
 (.branch 65
 (.branch 54
 (.leaf (.quota 2))
 (.branch 59
 (.leaf (.quota 2))
 (.branch 62
 (.branch 60
 (.leaf (.quota 2))
 (.branch 61
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M017.r1139))))
 (.branch 63
 (.leaf (.quota 2))
 (.branch 64
 (.leaf (.matching Nonrational.OldTerminalMatches.M017.r1140))
 (.leaf (.quota 2)))))))
 (.branch 76
 (.branch 70
 (.leaf (.quota 2))
 (.branch 73
 (.leaf (.quota 2))
 (.branch 74
 (.leaf (.quota 2))
 (.branch 75
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 81
 (.branch 78
 (.leaf (.quota 2))
 (.branch 79
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 84
 (.leaf (.quota 2))
 (.branch 85
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))))
 (.branch 131
 (.branch 109
 (.branch 98
 (.branch 92
 (.branch 89
 (.branch 88
 (.leaf (.matching Nonrational.OldTerminalMatches.M017.r1141))
 (.leaf (.quota 2)))
 (.branch 90
 (.leaf (.matching Nonrational.OldTerminalMatches.M017.r1142))
 (.branch 91
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M017.r1143)))))
 (.branch 95
 (.branch 93
 (.leaf (.matching Nonrational.OldTerminalMatches.M017.r1144))
 (.branch 94
 (.leaf (.matching Nonrational.OldTerminalMatches.M017.r1145))
 (.leaf (.matching Nonrational.OldTerminalMatches.M017.r1146))))
 (.branch 96
 (.leaf (.quota 2))
 (.branch 97
 (.leaf (.matching Nonrational.OldTerminalMatches.M017.r1147))
 (.leaf (.matching Nonrational.OldTerminalMatches.M017.r1148))))))
 (.branch 103
 (.branch 100
 (.branch 99
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M017.r1149)))
 (.branch 101
 (.leaf (.matching Nonrational.OldTerminalMatches.M017.r1150))
 (.branch 102
 (.leaf (.matching Nonrational.OldTerminalMatches.M017.r1151))
 (.leaf (.quota 2)))))
 (.branch 106
 (.branch 104
 (.leaf (.matching Nonrational.OldTerminalMatches.M018.r1152))
 (.branch 105
 (.leaf (.matching Nonrational.OldTerminalMatches.M018.r1153))
 (.leaf (.matching Nonrational.OldTerminalMatches.M018.r1154))))
 (.branch 107
 (.leaf (.matching Nonrational.OldTerminalMatches.M018.r1155))
 (.branch 108
 (.leaf (.matching Nonrational.OldTerminalMatches.M018.r1156))
 (.leaf (.matching Nonrational.OldTerminalMatches.M018.r1157)))))))
 (.branch 120
 (.branch 114
 (.branch 111
 (.branch 110
 (.leaf (.matching Nonrational.OldTerminalMatches.M018.r1158))
 (.leaf (.quota 1)))
 (.branch 112
 (.leaf (.quota 1))
 (.branch 113
 (.leaf (.matching Nonrational.OldTerminalMatches.M018.r1159))
 (.leaf (.matching Nonrational.OldTerminalMatches.M018.r1160)))))
 (.branch 117
 (.branch 115
 (.leaf (.matching Nonrational.OldTerminalMatches.M018.r1161))
 (.branch 116
 (.leaf (.matching Nonrational.OldTerminalMatches.M018.r1162))
 (.leaf (.quota 1))))
 (.branch 118
 (.leaf (.quota 1))
 (.branch 119
 (.leaf (.matching Nonrational.OldTerminalMatches.M018.r1163))
 (.leaf (.matching Nonrational.OldTerminalMatches.M018.r1164))))))
 (.branch 125
 (.branch 122
 (.branch 121
 (.leaf (.matching Nonrational.OldTerminalMatches.M018.r1165))
 (.leaf (.matching Nonrational.OldTerminalMatches.M018.r1166)))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))))
 (.branch 153
 (.branch 142
 (.leaf (.quota 2))
 (.branch 147
 (.branch 144
 (.leaf (.quota 2))
 (.branch 145
 (.leaf (.quota 2))
 (.branch 146
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M018.r1167)))))
 (.branch 150
 (.branch 148
 (.leaf (.matching Nonrational.OldTerminalMatches.M018.r1168))
 (.branch 149
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 151
 (.leaf (.quota 2))
 (.branch 152
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))))
 (.branch 164
 (.branch 158
 (.branch 155
 (.leaf (.quota 2))
 (.branch 156
 (.leaf (.quota 2))
 (.branch 157
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 161
 (.branch 159
 (.leaf (.quota 2))
 (.branch 160
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 2))))
 (.branch 169
 (.branch 166
 (.leaf (.quota 2))
 (.branch 167
 (.leaf (.quota 1))
 (.branch 168
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 172
 (.leaf (.quota 2))
 (.branch 173
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))))))
 (.branch 262
 (.branch 218
 (.branch 196
 (.branch 185
 (.branch 180
 (.leaf (.quota 2))
 (.branch 182
 (.leaf (.quota 2))
 (.branch 183
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 190
 (.leaf (.quota 2))
 (.branch 193
 (.branch 191
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 194
 (.leaf (.quota 1))
 (.branch 195
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))))
 (.branch 207
 (.branch 201
 (.branch 198
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 204
 (.branch 202
 (.leaf (.quota 2))
 (.branch 203
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 205
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 212
 (.branch 209
 (.leaf (.quota 2))
 (.branch 210
 (.leaf (.quota 2))
 (.branch 211
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 215
 (.branch 213
 (.leaf (.quota 2))
 (.branch 214
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 216
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))))
 (.branch 240
 (.branch 229
 (.branch 223
 (.branch 220
 (.leaf (.quota 2))
 (.branch 221
 (.leaf (.quota 2))
 (.branch 222
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 226
 (.branch 224
 (.leaf (.quota 1))
 (.branch 225
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 227
 (.leaf (.quota 2))
 (.branch 228
 (.leaf (.matching Nonrational.OldTerminalMatches.M018.r1169))
 (.leaf (.quota 2))))))
 (.branch 234
 (.branch 231
 (.branch 230
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M018.r1170)))
 (.branch 232
 (.leaf (.matching Nonrational.OldTerminalMatches.M018.r1171))
 (.leaf (.quota 2))))
 (.branch 237
 (.branch 235
 (.leaf (.quota 1))
 (.branch 236
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M018.r1172))))
 (.branch 238
 (.leaf (.matching Nonrational.OldTerminalMatches.M018.r1173))
 (.leaf (.quota 2))))))
 (.branch 251
 (.branch 245
 (.branch 242
 (.branch 241
 (.leaf (.quota 1))
 (.leaf (.matching Nonrational.OldTerminalMatches.M018.r1174)))
 (.branch 243
 (.leaf (.matching Nonrational.OldTerminalMatches.M018.r1175))
 (.branch 244
 (.leaf (.matching Nonrational.OldTerminalMatches.M018.r1176))
 (.leaf (.matching Nonrational.OldTerminalMatches.M018.r1177)))))
 (.branch 248
 (.branch 246
 (.leaf (.quota 1))
 (.branch 247
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 2))))
 (.branch 256
 (.leaf (.quota 2))
 (.branch 259
 (.branch 257
 (.leaf (.quota 2))
 (.branch 258
 (.leaf (.matching Nonrational.OldTerminalMatches.M018.r1178))
 (.leaf (.matching Nonrational.OldTerminalMatches.M018.r1179))))
 (.branch 260
 (.leaf (.matching Nonrational.OldTerminalMatches.M018.r1180))
 (.branch 261
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))))))
 (.branch 306
 (.branch 284
 (.branch 273
 (.branch 267
 (.branch 264
 (.leaf (.quota 2))
 (.branch 265
 (.leaf (.quota 2))
 (.branch 266
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M018.r1181)))))
 (.branch 270
 (.leaf (.quota 2))
 (.branch 271
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 278
 (.branch 275
 (.leaf (.incidence 5))
 (.branch 276
 (.leaf (.incidence 5))
 (.branch 277
 (.leaf (.incidence 5))
 (.leaf (.quota 1)))))
 (.branch 281
 (.branch 279
 (.leaf (.quota 1))
 (.branch 280
 (.leaf (.quota 1))
 (.leaf (.matching Nonrational.OldTerminalMatches.M018.r1182))))
 (.branch 282
 (.leaf (.matching Nonrational.OldTerminalMatches.M018.r1183))
 (.branch 283
 (.leaf (.matching Nonrational.OldTerminalMatches.M018.r1184))
 (.leaf (.quota 2)))))))
 (.branch 295
 (.branch 289
 (.branch 286
 (.branch 285
 (.leaf (.matching Nonrational.OldTerminalMatches.M018.r1185))
 (.leaf (.matching Nonrational.OldTerminalMatches.M018.r1186)))
 (.branch 287
 (.leaf (.matching Nonrational.OldTerminalMatches.M018.r1187))
 (.branch 288
 (.leaf (.matching Nonrational.OldTerminalMatches.M018.r1188))
 (.leaf (.quota 1)))))
 (.branch 292
 (.branch 290
 (.leaf (.quota 1))
 (.branch 291
 (.leaf (.matching Nonrational.OldTerminalMatches.M018.r1189))
 (.leaf (.matching Nonrational.OldTerminalMatches.M018.r1190))))
 (.branch 293
 (.leaf (.matching Nonrational.OldTerminalMatches.M018.r1191))
 (.branch 294
 (.leaf (.matching Nonrational.OldTerminalMatches.M018.r1192))
 (.leaf (.matching Nonrational.OldTerminalMatches.M018.r1193))))))
 (.branch 300
 (.branch 297
 (.branch 296
 (.leaf (.matching Nonrational.OldTerminalMatches.M018.r1194))
 (.leaf (.quota 1)))
 (.branch 298
 (.leaf (.quota 1))
 (.branch 299
 (.leaf (.matching Nonrational.OldTerminalMatches.M018.r1195))
 (.leaf (.matching Nonrational.OldTerminalMatches.M018.r1196)))))
 (.branch 303
 (.branch 301
 (.leaf (.matching Nonrational.OldTerminalMatches.M018.r1197))
 (.branch 302
 (.leaf (.matching Nonrational.OldTerminalMatches.M018.r1198))
 (.leaf (.matching Nonrational.OldTerminalMatches.M018.r1199))))
 (.branch 304
 (.leaf (.quota 1))
 (.branch 305
 (.leaf (.matching Nonrational.OldTerminalMatches.M018.r1200))
 (.leaf (.matching Nonrational.OldTerminalMatches.M018.r1201))))))))
 (.branch 328
 (.branch 317
 (.branch 311
 (.branch 308
 (.branch 307
 (.leaf (.matching Nonrational.OldTerminalMatches.M018.r1202))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 339
 (.branch 333
 (.leaf (.quota 2))
 (.branch 336
 (.branch 334
 (.leaf (.quota 2))
 (.branch 335
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 337
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 344
 (.branch 341
 (.branch 340
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 342
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 347
 (.branch 345
 (.leaf (.quota 2))
 (.branch 346
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 348
 (.leaf (.quota 2))
 (.branch 349
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))))))))
def disposition (j : Fin leafCount) := dispositionTable.get j.val
def dispositionTest (i : Nat) : Bool := RawLeafCertificate.check quota
  ((rawLeaves i).map Papers.RationalityTen.RootedCaches.RootedSixBase02.rawCells) (dispositionTable.get i)

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0364

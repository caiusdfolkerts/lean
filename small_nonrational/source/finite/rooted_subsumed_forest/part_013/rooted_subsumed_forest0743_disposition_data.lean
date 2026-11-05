module
prelude
public import RootedSubsumedForest0743Data
public import RawLeafCertificate
public import OldTerminalMatches.M025

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0743
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 225
 (.branch 112
 (.branch 56
 (.branch 28
 (.branch 14
 (.branch 7
 (.branch 3
 (.leaf (.quota 2))
 (.branch 5
 (.branch 4
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.leaf (.quota 2))))
 (.branch 10
 (.branch 8
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.branch 12
 (.branch 11
 (.leaf (.quota 3))
 (.leaf (.matching Nonrational.OldTerminalMatches.M025.r1621)))
 (.leaf (.quota 2)))))
 (.leaf (.quota 2)))
 (.branch 42
 (.branch 35
 (.branch 31
 (.leaf (.quota 2))
 (.branch 33
 (.leaf (.quota 2))
 (.branch 34
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.leaf (.quota 2)))
 (.branch 49
 (.branch 45
 (.leaf (.quota 2))
 (.branch 47
 (.branch 46
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))))
 (.branch 84
 (.branch 70
 (.branch 63
 (.branch 59
 (.leaf (.quota 2))
 (.branch 61
 (.branch 60
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.branch 77
 (.leaf (.quota 2))
 (.branch 80
 (.branch 78
 (.leaf (.quota 2))
 (.branch 79
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 82
 (.branch 81
 (.leaf (.quota 3))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))))
 (.branch 98
 (.branch 91
 (.branch 87
 (.branch 85
 (.leaf (.quota 2))
 (.branch 86
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 89
 (.leaf (.quota 2))
 (.branch 90
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 94
 (.branch 92
 (.leaf (.quota 2))
 (.branch 93
 (.leaf (.matching Nonrational.OldTerminalMatches.M025.r1622))
 (.leaf (.quota 2))))
 (.branch 96
 (.leaf (.quota 2))
 (.branch 97
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 105
 (.branch 101
 (.leaf (.quota 2))
 (.branch 103
 (.branch 102
 (.leaf (.quota 3))
 (.leaf (.quota 2)))
 (.branch 104
 (.leaf (.quota 3))
 (.leaf (.quota 2)))))
 (.leaf (.quota 2))))))
 (.branch 168
 (.branch 140
 (.branch 126
 (.branch 119
 (.leaf (.quota 2))
 (.branch 122
 (.branch 120
 (.leaf (.matching Nonrational.OldTerminalMatches.M025.r1623))
 (.leaf (.quota 1)))
 (.branch 124
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 133
 (.branch 129
 (.branch 127
 (.leaf (.quota 1))
 (.branch 128
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 131
 (.branch 130
 (.leaf (.quota 3))
 (.leaf (.quota 2)))
 (.branch 132
 (.leaf (.matching Nonrational.OldTerminalMatches.M025.r1624))
 (.leaf (.quota 2)))))
 (.branch 136
 (.branch 134
 (.leaf (.quota 2))
 (.branch 135
 (.leaf (.quota 3))
 (.leaf (.quota 1))))
 (.branch 138
 (.leaf (.quota 1))
 (.branch 139
 (.leaf (.quota 1))
 (.leaf (.quota 3)))))))
 (.branch 154
 (.branch 147
 (.branch 143
 (.branch 141
 (.leaf (.quota 3))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 161
 (.leaf (.quota 2))
 (.branch 164
 (.leaf (.quota 2))
 (.branch 166
 (.leaf (.quota 2))
 (.branch 167
 (.leaf (.quota 2))
 (.leaf (.quota 3))))))))
 (.branch 196
 (.branch 182
 (.branch 175
 (.branch 171
 (.branch 169
 (.leaf (.quota 2))
 (.branch 170
 (.leaf (.quota 2))
 (.leaf (.quota 3))))
 (.branch 173
 (.branch 172
 (.leaf (.quota 3))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.branch 189
 (.branch 185
 (.branch 183
 (.leaf (.matching Nonrational.OldTerminalMatches.M025.r1625))
 (.branch 184
 (.leaf (.quota 1))
 (.leaf (.matching Nonrational.OldTerminalMatches.M025.r1626))))
 (.branch 187
 (.branch 186
 (.leaf (.matching Nonrational.OldTerminalMatches.M025.r1627))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))))
 (.branch 338
 (.branch 281
 (.branch 253
 (.branch 239
 (.branch 232
 (.branch 228
 (.branch 226
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 235
 (.branch 233
 (.leaf (.quota 2))
 (.branch 234
 (.leaf (.quota 3))
 (.leaf (.quota 1))))
 (.branch 237
 (.branch 236
 (.leaf (.quota 3))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))))
 (.branch 246
 (.branch 242
 (.leaf (.quota 2))
 (.branch 244
 (.leaf (.quota 2))
 (.branch 245
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M025.r1628)))))
 (.branch 249
 (.branch 247
 (.leaf (.quota 1))
 (.branch 248
 (.leaf (.quota 2))
 (.leaf (.quota 3))))
 (.leaf (.quota 2)))))
 (.branch 267
 (.branch 260
 (.branch 256
 (.leaf (.quota 2))
 (.branch 258
 (.branch 257
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M025.r1629)))
 (.branch 259
 (.leaf (.quota 3))
 (.leaf (.quota 2)))))
 (.branch 263
 (.branch 261
 (.leaf (.quota 3))
 (.leaf (.quota 2)))
 (.branch 265
 (.branch 264
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.branch 266
 (.leaf (.quota 3))
 (.leaf (.quota 2))))))
 (.branch 274
 (.branch 270
 (.branch 268
 (.leaf (.quota 2))
 (.branch 269
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 272
 (.leaf (.quota 2))
 (.branch 273
 (.leaf (.quota 2))
 (.leaf (.quota 3)))))
 (.branch 277
 (.leaf (.quota 2))
 (.branch 279
 (.leaf (.quota 2))
 (.branch 280
 (.leaf (.matching Nonrational.OldTerminalMatches.M025.r1630))
 (.leaf (.quota 3))))))))
 (.branch 309
 (.branch 295
 (.branch 288
 (.branch 284
 (.branch 282
 (.leaf (.matching Nonrational.OldTerminalMatches.M025.r1631))
 (.branch 283
 (.leaf (.matching Nonrational.OldTerminalMatches.M025.r1632))
 (.leaf (.quota 2))))
 (.branch 286
 (.branch 285
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M025.r1633)))
 (.leaf (.quota 2))))
 (.branch 291
 (.branch 289
 (.leaf (.quota 3))
 (.branch 290
 (.leaf (.quota 3))
 (.leaf (.quota 2))))
 (.leaf (.quota 2))))
 (.branch 302
 (.branch 298
 (.branch 296
 (.leaf (.quota 2))
 (.branch 297
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 2)))
 (.branch 305
 (.branch 303
 (.leaf (.quota 2))
 (.branch 304
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))))
 (.branch 323
 (.branch 316
 (.branch 312
 (.leaf (.quota 2))
 (.branch 314
 (.leaf (.quota 2))
 (.branch 315
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 319
 (.leaf (.quota 2))
 (.branch 321
 (.branch 320
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))))
 (.branch 330
 (.branch 326
 (.branch 324
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 328
 (.leaf (.quota 2))
 (.branch 329
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 334
 (.branch 332
 (.branch 331
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 336
 (.leaf (.quota 2))
 (.branch 337
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))))))
 (.branch 394
 (.branch 366
 (.branch 352
 (.branch 345
 (.branch 341
 (.branch 339
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 359
 (.branch 355
 (.leaf (.quota 2))
 (.branch 357
 (.branch 356
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 358
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 362
 (.branch 360
 (.leaf (.quota 1))
 (.branch 361
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))))
 (.branch 380
 (.branch 373
 (.branch 369
 (.branch 367
 (.leaf (.quota 2))
 (.branch 368
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.branch 422
 (.branch 408
 (.branch 401
 (.branch 397
 (.branch 395
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 404
 (.leaf (.quota 2))
 (.branch 406
 (.branch 405
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 407
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 415
 (.leaf (.quota 2))
 (.branch 418
 (.branch 416
 (.leaf (.matching Nonrational.OldTerminalMatches.M025.r1634))
 (.branch 417
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M025.r1635))))
 (.branch 420
 (.leaf (.quota 2))
 (.branch 421
 (.leaf (.quota 2))
 (.leaf (.quota 3)))))))
 (.branch 436
 (.leaf (.quota 2))
 (.branch 443
 (.branch 439
 (.branch 437
 (.leaf (.quota 2))
 (.branch 438
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 441
 (.branch 440
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 442
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 447
 (.branch 445
 (.branch 444
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 449
 (.branch 448
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 450
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))))))))
def disposition (j : Fin leafCount) := dispositionTable.get j.val
def dispositionTest (i : Nat) : Bool := RawLeafCertificate.check quota
  ((rawLeaves i).map Papers.RationalityTen.RootedCaches.RootedSixBase04.rawCells) (dispositionTable.get i)

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0743

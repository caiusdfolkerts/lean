module
prelude
public import SmallSubsumedForest18Data
public import RawLeafCertificate
public import OldTerminalMatches.M003
public import OldTerminalMatches.M004

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest18
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 216
 (.branch 108
 (.branch 54
 (.branch 27
 (.branch 13
 (.branch 6
 (.branch 3
 (.leaf (.quota 2))
 (.branch 4
 (.leaf (.quota 2))
 (.branch 5
 (.leaf (.matching Nonrational.OldTerminalMatches.M003.r0192))
 (.leaf (.matching Nonrational.OldTerminalMatches.M003.r0193)))))
 (.branch 9
 (.branch 7
 (.leaf (.matching Nonrational.OldTerminalMatches.M003.r0194))
 (.leaf (.quota 2)))
 (.branch 11
 (.leaf (.quota 2))
 (.branch 12
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M003.r0195))))))
 (.branch 20
 (.branch 16
 (.branch 14
 (.leaf (.matching Nonrational.OldTerminalMatches.M003.r0196))
 (.branch 15
 (.leaf (.matching Nonrational.OldTerminalMatches.M003.r0197))
 (.leaf (.quota 2))))
 (.branch 18
 (.leaf (.quota 2))
 (.branch 19
 (.leaf (.matching Nonrational.OldTerminalMatches.M003.r0198))
 (.leaf (.quota 2)))))
 (.branch 23
 (.branch 21
 (.leaf (.incidence 9))
 (.branch 22
 (.leaf (.incidence 9))
 (.leaf (.quota 2))))
 (.branch 25
 (.leaf (.quota 2))
 (.branch 26
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M003.r0199)))))))
 (.branch 40
 (.branch 33
 (.branch 30
 (.branch 28
 (.leaf (.matching Nonrational.OldTerminalMatches.M003.r0200))
 (.branch 29
 (.leaf (.matching Nonrational.OldTerminalMatches.M003.r0201))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.branch 36
 (.branch 34
 (.leaf (.quota 2))
 (.branch 35
 (.leaf (.incidence 9))
 (.leaf (.matching Nonrational.OldTerminalMatches.M003.r0202))))
 (.branch 38
 (.branch 37
 (.leaf (.matching Nonrational.OldTerminalMatches.M003.r0203))
 (.leaf (.quota 2)))
 (.branch 39
 (.leaf (.quota 2))
 (.leaf (.incidence 8))))))
 (.branch 47
 (.branch 43
 (.branch 41
 (.leaf (.quota 2))
 (.branch 42
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M003.r0204))))
 (.branch 45
 (.branch 44
 (.leaf (.matching Nonrational.OldTerminalMatches.M003.r0205))
 (.leaf (.quota 2)))
 (.branch 46
 (.leaf (.matching Nonrational.OldTerminalMatches.M003.r0206))
 (.leaf (.quota 2)))))
 (.branch 50
 (.branch 48
 (.leaf (.matching Nonrational.OldTerminalMatches.M003.r0207))
 (.leaf (.quota 2)))
 (.branch 52
 (.leaf (.quota 2))
 (.branch 53
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))))
 (.branch 81
 (.branch 67
 (.branch 60
 (.branch 57
 (.branch 55
 (.leaf (.matching Nonrational.OldTerminalMatches.M003.r0208))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 63
 (.leaf (.quota 2))
 (.branch 65
 (.leaf (.quota 2))
 (.branch 66
 (.leaf (.quota 3))
 (.leaf (.incidence 4))))))
 (.leaf (.quota 2)))
 (.branch 94
 (.branch 87
 (.branch 84
 (.branch 82
 (.leaf (.quota 2))
 (.branch 83
 (.leaf (.incidence 9))
 (.leaf (.quota 2))))
 (.branch 85
 (.leaf (.incidence 8))
 (.leaf (.quota 2))))
 (.branch 90
 (.branch 88
 (.leaf (.matching Nonrational.OldTerminalMatches.M003.r0209))
 (.branch 89
 (.leaf (.matching Nonrational.OldTerminalMatches.M003.r0210))
 (.leaf (.quota 2))))
 (.leaf (.quota 2))))
 (.branch 101
 (.leaf (.quota 2))
 (.branch 104
 (.branch 102
 (.leaf (.matching Nonrational.OldTerminalMatches.M003.r0211))
 (.branch 103
 (.leaf (.matching Nonrational.OldTerminalMatches.M003.r0212))
 (.leaf (.matching Nonrational.OldTerminalMatches.M003.r0213))))
 (.branch 106
 (.branch 105
 (.leaf (.matching Nonrational.OldTerminalMatches.M003.r0214))
 (.leaf (.incidence 9)))
 (.branch 107
 (.leaf (.incidence 9))
 (.leaf (.quota 2)))))))))
 (.branch 162
 (.branch 135
 (.branch 121
 (.branch 114
 (.branch 111
 (.branch 109
 (.leaf (.matching Nonrational.OldTerminalMatches.M003.r0215))
 (.branch 110
 (.leaf (.matching Nonrational.OldTerminalMatches.M003.r0216))
 (.leaf (.matching Nonrational.OldTerminalMatches.M003.r0217))))
 (.branch 112
 (.leaf (.matching Nonrational.OldTerminalMatches.M003.r0218))
 (.branch 113
 (.leaf (.quota 1))
 (.leaf (.matching Nonrational.OldTerminalMatches.M003.r0219)))))
 (.branch 117
 (.branch 115
 (.leaf (.quota 2))
 (.branch 116
 (.leaf (.matching Nonrational.OldTerminalMatches.M003.r0220))
 (.leaf (.matching Nonrational.OldTerminalMatches.M003.r0221))))
 (.branch 119
 (.branch 118
 (.leaf (.matching Nonrational.OldTerminalMatches.M003.r0222))
 (.leaf (.matching Nonrational.OldTerminalMatches.M003.r0223)))
 (.branch 120
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M003.r0224))))))
 (.branch 128
 (.branch 124
 (.branch 122
 (.leaf (.matching Nonrational.OldTerminalMatches.M003.r0225))
 (.branch 123
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M003.r0226))))
 (.branch 126
 (.branch 125
 (.leaf (.matching Nonrational.OldTerminalMatches.M003.r0227))
 (.leaf (.quota 2)))
 (.branch 127
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M003.r0228)))))
 (.branch 131
 (.branch 129
 (.leaf (.matching Nonrational.OldTerminalMatches.M003.r0229))
 (.branch 130
 (.leaf (.quota 1))
 (.leaf (.matching Nonrational.OldTerminalMatches.M003.r0230))))
 (.branch 133
 (.branch 132
 (.leaf (.matching Nonrational.OldTerminalMatches.M003.r0231))
 (.leaf (.incidence 9)))
 (.branch 134
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M003.r0232)))))))
 (.branch 148
 (.branch 141
 (.branch 138
 (.branch 136
 (.leaf (.matching Nonrational.OldTerminalMatches.M003.r0233))
 (.branch 137
 (.leaf (.quota 1))
 (.leaf (.matching Nonrational.OldTerminalMatches.M003.r0234))))
 (.branch 139
 (.leaf (.matching Nonrational.OldTerminalMatches.M003.r0235))
 (.branch 140
 (.leaf (.matching Nonrational.OldTerminalMatches.M003.r0236))
 (.leaf (.matching Nonrational.OldTerminalMatches.M003.r0237)))))
 (.branch 144
 (.branch 142
 (.leaf (.matching Nonrational.OldTerminalMatches.M003.r0238))
 (.branch 143
 (.leaf (.matching Nonrational.OldTerminalMatches.M003.r0239))
 (.leaf (.matching Nonrational.OldTerminalMatches.M003.r0240))))
 (.leaf (.quota 2))))
 (.branch 155
 (.branch 151
 (.branch 149
 (.leaf (.quota 2))
 (.branch 150
 (.leaf (.matching Nonrational.OldTerminalMatches.M003.r0241))
 (.leaf (.matching Nonrational.OldTerminalMatches.M003.r0242))))
 (.leaf (.quota 2)))
 (.branch 158
 (.branch 156
 (.leaf (.quota 2))
 (.branch 157
 (.leaf (.quota 1))
 (.leaf (.matching Nonrational.OldTerminalMatches.M003.r0243))))
 (.branch 160
 (.branch 159
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))))))
 (.branch 189
 (.branch 175
 (.leaf (.quota 2))
 (.branch 182
 (.branch 178
 (.leaf (.quota 2))
 (.branch 180
 (.leaf (.quota 2))
 (.branch 181
 (.leaf (.matching Nonrational.OldTerminalMatches.M003.r0244))
 (.leaf (.matching Nonrational.OldTerminalMatches.M003.r0245)))))
 (.branch 185
 (.leaf (.quota 2))
 (.branch 187
 (.leaf (.quota 2))
 (.branch 188
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M003.r0246)))))))
 (.branch 202
 (.branch 195
 (.branch 192
 (.branch 190
 (.leaf (.matching Nonrational.OldTerminalMatches.M003.r0247))
 (.branch 191
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M003.r0248))))
 (.branch 193
 (.leaf (.matching Nonrational.OldTerminalMatches.M003.r0249))
 (.branch 194
 (.leaf (.matching Nonrational.OldTerminalMatches.M003.r0250))
 (.leaf (.quota 2)))))
 (.branch 198
 (.branch 196
 (.leaf (.quota 2))
 (.branch 197
 (.leaf (.matching Nonrational.OldTerminalMatches.M003.r0251))
 (.leaf (.matching Nonrational.OldTerminalMatches.M003.r0252))))
 (.branch 200
 (.branch 199
 (.leaf (.matching Nonrational.OldTerminalMatches.M003.r0253))
 (.leaf (.matching Nonrational.OldTerminalMatches.M003.r0254)))
 (.branch 201
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 209
 (.branch 205
 (.branch 203
 (.leaf (.quota 2))
 (.branch 204
 (.leaf (.matching Nonrational.OldTerminalMatches.M003.r0255))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.branch 212
 (.leaf (.quota 2))
 (.branch 214
 (.leaf (.quota 2))
 (.branch 215
 (.leaf (.matching Nonrational.OldTerminalMatches.M004.r0256))
 (.leaf (.matching Nonrational.OldTerminalMatches.M004.r0257))))))))))
 (.branch 324
 (.branch 270
 (.branch 243
 (.branch 229
 (.branch 222
 (.branch 219
 (.branch 217
 (.leaf (.matching Nonrational.OldTerminalMatches.M004.r0258))
 (.branch 218
 (.leaf (.matching Nonrational.OldTerminalMatches.M004.r0259))
 (.leaf (.quota 2))))
 (.branch 220
 (.leaf (.quota 2))
 (.branch 221
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M004.r0260)))))
 (.branch 225
 (.branch 223
 (.leaf (.matching Nonrational.OldTerminalMatches.M004.r0261))
 (.branch 224
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M004.r0262))))
 (.branch 227
 (.leaf (.quota 2))
 (.branch 228
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M004.r0263))))))
 (.branch 236
 (.branch 232
 (.branch 230
 (.leaf (.matching Nonrational.OldTerminalMatches.M004.r0264))
 (.branch 231
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M004.r0265))))
 (.branch 234
 (.leaf (.quota 2))
 (.branch 235
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M004.r0266)))))
 (.branch 239
 (.branch 237
 (.leaf (.matching Nonrational.OldTerminalMatches.M004.r0267))
 (.branch 238
 (.leaf (.matching Nonrational.OldTerminalMatches.M004.r0268))
 (.leaf (.quota 1))))
 (.branch 241
 (.branch 240
 (.leaf (.matching Nonrational.OldTerminalMatches.M004.r0269))
 (.leaf (.quota 2)))
 (.branch 242
 (.leaf (.quota 2))
 (.leaf (.incidence 4)))))))
 (.branch 256
 (.branch 249
 (.branch 246
 (.branch 244
 (.leaf (.quota 1))
 (.branch 245
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 247
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 252
 (.branch 250
 (.leaf (.quota 2))
 (.branch 251
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 254
 (.branch 253
 (.leaf (.incidence 4))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))))
 (.branch 263
 (.branch 259
 (.branch 257
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 261
 (.branch 260
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))))
 (.branch 297
 (.branch 283
 (.branch 276
 (.branch 273
 (.branch 271
 (.leaf (.quota 2))
 (.branch 272
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M004.r0270))))
 (.branch 274
 (.leaf (.matching Nonrational.OldTerminalMatches.M004.r0271))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.branch 290
 (.branch 286
 (.leaf (.quota 2))
 (.branch 288
 (.leaf (.quota 2))
 (.branch 289
 (.leaf (.matching Nonrational.OldTerminalMatches.M004.r0272))
 (.leaf (.matching Nonrational.OldTerminalMatches.M004.r0273)))))
 (.branch 293
 (.branch 291
 (.leaf (.quota 2))
 (.branch 292
 (.leaf (.incidence 9))
 (.leaf (.matching Nonrational.OldTerminalMatches.M004.r0274))))
 (.branch 295
 (.leaf (.quota 2))
 (.branch 296
 (.leaf (.matching Nonrational.OldTerminalMatches.M004.r0275))
 (.leaf (.incidence 9)))))))
 (.branch 310
 (.branch 303
 (.branch 300
 (.branch 298
 (.leaf (.incidence 9))
 (.branch 299
 (.leaf (.incidence 9))
 (.leaf (.quota 1))))
 (.branch 301
 (.leaf (.matching Nonrational.OldTerminalMatches.M004.r0276))
 (.branch 302
 (.leaf (.matching Nonrational.OldTerminalMatches.M004.r0277))
 (.leaf (.quota 2)))))
 (.leaf (.quota 2)))
 (.branch 317
 (.branch 313
 (.branch 311
 (.leaf (.quota 2))
 (.branch 312
 (.leaf (.incidence 4))
 (.leaf (.quota 2))))
 (.branch 315
 (.leaf (.quota 2))
 (.branch 316
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M004.r0278)))))
 (.branch 320
 (.branch 318
 (.leaf (.quota 1))
 (.branch 319
 (.leaf (.matching Nonrational.OldTerminalMatches.M004.r0279))
 (.leaf (.quota 2))))
 (.branch 322
 (.branch 321
 (.leaf (.quota 1))
 (.leaf (.matching Nonrational.OldTerminalMatches.M004.r0280)))
 (.branch 323
 (.leaf (.matching Nonrational.OldTerminalMatches.M004.r0281))
 (.leaf (.matching Nonrational.OldTerminalMatches.M004.r0282)))))))))
 (.branch 378
 (.branch 351
 (.branch 337
 (.branch 330
 (.branch 327
 (.branch 325
 (.leaf (.matching Nonrational.OldTerminalMatches.M004.r0283))
 (.branch 326
 (.leaf (.matching Nonrational.OldTerminalMatches.M004.r0284))
 (.leaf (.matching Nonrational.OldTerminalMatches.M004.r0285))))
 (.branch 328
 (.leaf (.quota 2))
 (.branch 329
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 333
 (.branch 331
 (.leaf (.matching Nonrational.OldTerminalMatches.M004.r0286))
 (.branch 332
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M004.r0287))))
 (.branch 335
 (.branch 334
 (.leaf (.matching Nonrational.OldTerminalMatches.M004.r0288))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))))
 (.branch 344
 (.branch 340
 (.branch 338
 (.leaf (.quota 2))
 (.branch 339
 (.leaf (.matching Nonrational.OldTerminalMatches.M004.r0289))
 (.leaf (.quota 2))))
 (.branch 342
 (.leaf (.quota 2))
 (.branch 343
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M004.r0290)))))
 (.branch 347
 (.branch 345
 (.leaf (.matching Nonrational.OldTerminalMatches.M004.r0291))
 (.branch 346
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M004.r0292))))
 (.branch 349
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 364
 (.branch 357
 (.branch 354
 (.branch 352
 (.leaf (.matching Nonrational.OldTerminalMatches.M004.r0293))
 (.leaf (.quota 2)))
 (.branch 355
 (.leaf (.quota 1))
 (.branch 356
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M004.r0294)))))
 (.branch 360
 (.branch 358
 (.leaf (.matching Nonrational.OldTerminalMatches.M004.r0295))
 (.branch 359
 (.leaf (.matching Nonrational.OldTerminalMatches.M004.r0296))
 (.leaf (.matching Nonrational.OldTerminalMatches.M004.r0297))))
 (.branch 362
 (.branch 361
 (.leaf (.matching Nonrational.OldTerminalMatches.M004.r0298))
 (.leaf (.matching Nonrational.OldTerminalMatches.M004.r0299)))
 (.branch 363
 (.leaf (.matching Nonrational.OldTerminalMatches.M004.r0300))
 (.leaf (.matching Nonrational.OldTerminalMatches.M004.r0301))))))
 (.branch 371
 (.branch 367
 (.branch 365
 (.leaf (.matching Nonrational.OldTerminalMatches.M004.r0302))
 (.branch 366
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M004.r0303))))
 (.branch 369
 (.branch 368
 (.leaf (.matching Nonrational.OldTerminalMatches.M004.r0304))
 (.leaf (.matching Nonrational.OldTerminalMatches.M004.r0305)))
 (.branch 370
 (.leaf (.matching Nonrational.OldTerminalMatches.M004.r0306))
 (.leaf (.matching Nonrational.OldTerminalMatches.M004.r0307)))))
 (.branch 374
 (.branch 372
 (.leaf (.matching Nonrational.OldTerminalMatches.M004.r0308))
 (.branch 373
 (.leaf (.matching Nonrational.OldTerminalMatches.M004.r0309))
 (.leaf (.matching Nonrational.OldTerminalMatches.M004.r0310))))
 (.leaf (.quota 2))))))
 (.branch 405
 (.branch 391
 (.branch 384
 (.branch 381
 (.branch 379
 (.leaf (.quota 2))
 (.branch 380
 (.leaf (.quota 2))
 (.leaf (.incidence 9))))
 (.branch 382
 (.leaf (.quota 2))
 (.branch 383
 (.leaf (.matching Nonrational.OldTerminalMatches.M004.r0311))
 (.leaf (.quota 1)))))
 (.branch 387
 (.branch 385
 (.leaf (.quota 1))
 (.branch 386
 (.leaf (.quota 1))
 (.leaf (.matching Nonrational.OldTerminalMatches.M004.r0312))))
 (.branch 389
 (.branch 388
 (.leaf (.matching Nonrational.OldTerminalMatches.M004.r0313))
 (.leaf (.matching Nonrational.OldTerminalMatches.M004.r0314)))
 (.branch 390
 (.leaf (.matching Nonrational.OldTerminalMatches.M004.r0315))
 (.leaf (.matching Nonrational.OldTerminalMatches.M004.r0316))))))
 (.branch 398
 (.branch 394
 (.branch 392
 (.leaf (.quota 2))
 (.branch 393
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 396
 (.branch 395
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M004.r0317)))
 (.leaf (.quota 2))))
 (.branch 401
 (.branch 399
 (.leaf (.quota 2))
 (.branch 400
 (.leaf (.incidence 9))
 (.leaf (.quota 2))))
 (.branch 403
 (.leaf (.quota 2))
 (.branch 404
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))))
 (.branch 418
 (.branch 411
 (.branch 408
 (.branch 406
 (.leaf (.quota 2))
 (.branch 407
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 409
 (.leaf (.quota 2))
 (.branch 410
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 414
 (.branch 412
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 416
 (.branch 415
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 417
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 425
 (.leaf (.quota 2))
 (.branch 428
 (.branch 426
 (.leaf (.quota 2))
 (.branch 427
 (.leaf (.quota 2))
 (.leaf (.incidence 4))))
 (.branch 430
 (.leaf (.quota 2))
 (.branch 431
 (.leaf (.quota 2))
 (.leaf (.quota 3)))))))))))
def disposition (j : Fin leafCount) := dispositionTable.get j.val
def dispositionTest (i : Nat) : Bool := RawLeafCertificate.check quota
  ((rawLeaves i).map RootedSmallCache.rawCells) (dispositionTable.get i)

end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest18

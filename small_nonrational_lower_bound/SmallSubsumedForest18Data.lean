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
public import SmallSubsumedForest18Packed000
public import SmallSubsumedForest18Packed001
public import SmallSubsumedForest18Packed002
public import SmallSubsumedForest18Packed003
public import SmallSubsumedForest18Packed004
public import SmallSubsumedForest18Packed005
public import SmallSubsumedForest18Packed006
public import SmallSubsumedForest18Packed007
public import SmallSubsumedForest18Packed008
public import SmallSubsumedForest18Packed009

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest18
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 3436
abbrev nodeCount : Nat := 62769
abbrev leafCount : Nat := 432
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
(.branch 216
 (.branch 108
 (.branch 54
 (.branch 27
 (.branch 13
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf (certNat% 0))
 (.branch 2
 (.leaf (certNat% 1))
 (.leaf (certNat% 2))))
 (.branch 4
 (.leaf (certNat% 3))
 (.branch 5
 (.leaf (certNat% 4))
 (.leaf (certNat% 5)))))
 (.branch 9
 (.branch 7
 (.leaf (certNat% 6))
 (.branch 8
 (.leaf (certNat% 7))
 (.leaf (certNat% 8))))
 (.branch 11
 (.branch 10
 (.leaf (certNat% 9))
 (.leaf (certNat% 10)))
 (.branch 12
 (.leaf (certNat% 11))
 (.leaf (certNat% 12))))))
 (.branch 20
 (.branch 16
 (.branch 14
 (.leaf (certNat% 13))
 (.branch 15
 (.leaf (certNat% 14))
 (.leaf (certNat% 15))))
 (.branch 18
 (.branch 17
 (.leaf (certNat% 16))
 (.leaf (certNat% 17)))
 (.branch 19
 (.leaf (certNat% 18))
 (.leaf (certNat% 19)))))
 (.branch 23
 (.branch 21
 (.leaf (certNat% 20))
 (.branch 22
 (.leaf (certNat% 21))
 (.leaf (certNat% 22))))
 (.branch 25
 (.branch 24
 (.leaf (certNat% 23))
 (.leaf (certNat% 24)))
 (.branch 26
 (.leaf (certNat% 25))
 (.leaf (certNat% 26)))))))
 (.branch 40
 (.branch 33
 (.branch 30
 (.branch 28
 (.leaf (certNat% 27))
 (.branch 29
 (.leaf (certNat% 28))
 (.leaf (certNat% 29))))
 (.branch 31
 (.leaf (certNat% 30))
 (.branch 32
 (.leaf (certNat% 31))
 (.leaf (certNat% 32)))))
 (.branch 36
 (.branch 34
 (.leaf (certNat% 33))
 (.branch 35
 (.leaf (certNat% 34))
 (.leaf (certNat% 35))))
 (.branch 38
 (.branch 37
 (.leaf (certNat% 36))
 (.leaf (certNat% 37)))
 (.branch 39
 (.leaf (certNat% 38))
 (.leaf (certNat% 39))))))
 (.branch 47
 (.branch 43
 (.branch 41
 (.leaf (certNat% 40))
 (.branch 42
 (.leaf (certNat% 41))
 (.leaf (certNat% 42))))
 (.branch 45
 (.branch 44
 (.leaf (certNat% 43))
 (.leaf (certNat% 44)))
 (.branch 46
 (.leaf (certNat% 45))
 (.leaf (certNat% 46)))))
 (.branch 50
 (.branch 48
 (.leaf (certNat% 47))
 (.branch 49
 (.leaf (certNat% 48))
 (.leaf (certNat% 49))))
 (.branch 52
 (.branch 51
 (.leaf (certNat% 50))
 (.leaf (certNat% 51)))
 (.branch 53
 (.leaf (certNat% 52))
 (.leaf (certNat% 53))))))))
 (.branch 81
 (.branch 67
 (.branch 60
 (.branch 57
 (.branch 55
 (.leaf (certNat% 54))
 (.branch 56
 (.leaf (certNat% 55))
 (.leaf (certNat% 56))))
 (.branch 58
 (.leaf (certNat% 57))
 (.branch 59
 (.leaf (certNat% 58))
 (.leaf (certNat% 59)))))
 (.branch 63
 (.branch 61
 (.leaf (certNat% 60))
 (.branch 62
 (.leaf (certNat% 61))
 (.leaf (certNat% 62))))
 (.branch 65
 (.branch 64
 (.leaf (certNat% 63))
 (.leaf (certNat% 64)))
 (.branch 66
 (.leaf (certNat% 65))
 (.leaf (certNat% 66))))))
 (.branch 74
 (.branch 70
 (.branch 68
 (.leaf (certNat% 67))
 (.branch 69
 (.leaf (certNat% 68))
 (.leaf (certNat% 69))))
 (.branch 72
 (.branch 71
 (.leaf (certNat% 70))
 (.leaf (certNat% 71)))
 (.branch 73
 (.leaf (certNat% 72))
 (.leaf (certNat% 73)))))
 (.branch 77
 (.branch 75
 (.leaf (certNat% 74))
 (.branch 76
 (.leaf (certNat% 75))
 (.leaf (certNat% 76))))
 (.branch 79
 (.branch 78
 (.leaf (certNat% 77))
 (.leaf (certNat% 78)))
 (.branch 80
 (.leaf (certNat% 79))
 (.leaf (certNat% 80)))))))
 (.branch 94
 (.branch 87
 (.branch 84
 (.branch 82
 (.leaf (certNat% 81))
 (.branch 83
 (.leaf (certNat% 82))
 (.leaf (certNat% 83))))
 (.branch 85
 (.leaf (certNat% 84))
 (.branch 86
 (.leaf (certNat% 85))
 (.leaf (certNat% 86)))))
 (.branch 90
 (.branch 88
 (.leaf (certNat% 87))
 (.branch 89
 (.leaf (certNat% 88))
 (.leaf (certNat% 89))))
 (.branch 92
 (.branch 91
 (.leaf (certNat% 90))
 (.leaf (certNat% 91)))
 (.branch 93
 (.leaf (certNat% 92))
 (.leaf (certNat% 93))))))
 (.branch 101
 (.branch 97
 (.branch 95
 (.leaf (certNat% 94))
 (.branch 96
 (.leaf (certNat% 95))
 (.leaf (certNat% 96))))
 (.branch 99
 (.branch 98
 (.leaf (certNat% 97))
 (.leaf (certNat% 98)))
 (.branch 100
 (.leaf (certNat% 99))
 (.leaf (certNat% 100)))))
 (.branch 104
 (.branch 102
 (.leaf (certNat% 101))
 (.branch 103
 (.leaf (certNat% 102))
 (.leaf (certNat% 103))))
 (.branch 106
 (.branch 105
 (.leaf (certNat% 104))
 (.leaf (certNat% 105)))
 (.branch 107
 (.leaf (certNat% 106))
 (.leaf (certNat% 107)))))))))
 (.branch 162
 (.branch 135
 (.branch 121
 (.branch 114
 (.branch 111
 (.branch 109
 (.leaf (certNat% 108))
 (.branch 110
 (.leaf (certNat% 109))
 (.leaf (certNat% 110))))
 (.branch 112
 (.leaf (certNat% 111))
 (.branch 113
 (.leaf (certNat% 112))
 (.leaf (certNat% 113)))))
 (.branch 117
 (.branch 115
 (.leaf (certNat% 114))
 (.branch 116
 (.leaf (certNat% 115))
 (.leaf (certNat% 116))))
 (.branch 119
 (.branch 118
 (.leaf (certNat% 117))
 (.leaf (certNat% 118)))
 (.branch 120
 (.leaf (certNat% 119))
 (.leaf (certNat% 120))))))
 (.branch 128
 (.branch 124
 (.branch 122
 (.leaf (certNat% 121))
 (.branch 123
 (.leaf (certNat% 122))
 (.leaf (certNat% 123))))
 (.branch 126
 (.branch 125
 (.leaf (certNat% 124))
 (.leaf (certNat% 125)))
 (.branch 127
 (.leaf (certNat% 126))
 (.leaf (certNat% 127)))))
 (.branch 131
 (.branch 129
 (.leaf (certNat% 128))
 (.branch 130
 (.leaf (certNat% 129))
 (.leaf (certNat% 130))))
 (.branch 133
 (.branch 132
 (.leaf (certNat% 131))
 (.leaf (certNat% 132)))
 (.branch 134
 (.leaf (certNat% 133))
 (.leaf (certNat% 134)))))))
 (.branch 148
 (.branch 141
 (.branch 138
 (.branch 136
 (.leaf (certNat% 135))
 (.branch 137
 (.leaf (certNat% 136))
 (.leaf (certNat% 137))))
 (.branch 139
 (.leaf (certNat% 138))
 (.branch 140
 (.leaf (certNat% 139))
 (.leaf (certNat% 140)))))
 (.branch 144
 (.branch 142
 (.leaf (certNat% 141))
 (.branch 143
 (.leaf (certNat% 142))
 (.leaf (certNat% 143))))
 (.branch 146
 (.branch 145
 (.leaf (certNat% 144))
 (.leaf (certNat% 145)))
 (.branch 147
 (.leaf (certNat% 146))
 (.leaf (certNat% 147))))))
 (.branch 155
 (.branch 151
 (.branch 149
 (.leaf (certNat% 148))
 (.branch 150
 (.leaf (certNat% 149))
 (.leaf (certNat% 150))))
 (.branch 153
 (.branch 152
 (.leaf (certNat% 151))
 (.leaf (certNat% 152)))
 (.branch 154
 (.leaf (certNat% 153))
 (.leaf (certNat% 154)))))
 (.branch 158
 (.branch 156
 (.leaf (certNat% 155))
 (.branch 157
 (.leaf (certNat% 156))
 (.leaf (certNat% 157))))
 (.branch 160
 (.branch 159
 (.leaf (certNat% 158))
 (.leaf (certNat% 159)))
 (.branch 161
 (.leaf (certNat% 160))
 (.leaf (certNat% 161))))))))
 (.branch 189
 (.branch 175
 (.branch 168
 (.branch 165
 (.branch 163
 (.leaf (certNat% 162))
 (.branch 164
 (.leaf (certNat% 163))
 (.leaf (certNat% 164))))
 (.branch 166
 (.leaf (certNat% 165))
 (.branch 167
 (.leaf (certNat% 166))
 (.leaf (certNat% 167)))))
 (.branch 171
 (.branch 169
 (.leaf (certNat% 168))
 (.branch 170
 (.leaf (certNat% 169))
 (.leaf (certNat% 170))))
 (.branch 173
 (.branch 172
 (.leaf (certNat% 171))
 (.leaf (certNat% 172)))
 (.branch 174
 (.leaf (certNat% 173))
 (.leaf (certNat% 174))))))
 (.branch 182
 (.branch 178
 (.branch 176
 (.leaf (certNat% 175))
 (.branch 177
 (.leaf (certNat% 176))
 (.leaf (certNat% 177))))
 (.branch 180
 (.branch 179
 (.leaf (certNat% 178))
 (.leaf (certNat% 179)))
 (.branch 181
 (.leaf (certNat% 180))
 (.leaf (certNat% 181)))))
 (.branch 185
 (.branch 183
 (.leaf (certNat% 182))
 (.branch 184
 (.leaf (certNat% 183))
 (.leaf (certNat% 184))))
 (.branch 187
 (.branch 186
 (.leaf (certNat% 185))
 (.leaf (certNat% 186)))
 (.branch 188
 (.leaf (certNat% 187))
 (.leaf (certNat% 188)))))))
 (.branch 202
 (.branch 195
 (.branch 192
 (.branch 190
 (.leaf (certNat% 189))
 (.branch 191
 (.leaf (certNat% 190))
 (.leaf (certNat% 191))))
 (.branch 193
 (.leaf (certNat% 192))
 (.branch 194
 (.leaf (certNat% 193))
 (.leaf (certNat% 194)))))
 (.branch 198
 (.branch 196
 (.leaf (certNat% 195))
 (.branch 197
 (.leaf (certNat% 196))
 (.leaf (certNat% 197))))
 (.branch 200
 (.branch 199
 (.leaf (certNat% 198))
 (.leaf (certNat% 199)))
 (.branch 201
 (.leaf (certNat% 200))
 (.leaf (certNat% 201))))))
 (.branch 209
 (.branch 205
 (.branch 203
 (.leaf (certNat% 202))
 (.branch 204
 (.leaf (certNat% 203))
 (.leaf (certNat% 204))))
 (.branch 207
 (.branch 206
 (.leaf (certNat% 205))
 (.leaf (certNat% 206)))
 (.branch 208
 (.leaf (certNat% 207))
 (.leaf (certNat% 208)))))
 (.branch 212
 (.branch 210
 (.leaf (certNat% 209))
 (.branch 211
 (.leaf (certNat% 210))
 (.leaf (certNat% 211))))
 (.branch 214
 (.branch 213
 (.leaf (certNat% 212))
 (.leaf (certNat% 213)))
 (.branch 215
 (.leaf (certNat% 214))
 (.leaf (certNat% 215))))))))))
 (.branch 324
 (.branch 270
 (.branch 243
 (.branch 229
 (.branch 222
 (.branch 219
 (.branch 217
 (.leaf (certNat% 216))
 (.branch 218
 (.leaf (certNat% 217))
 (.leaf (certNat% 218))))
 (.branch 220
 (.leaf (certNat% 219))
 (.branch 221
 (.leaf (certNat% 220))
 (.leaf (certNat% 221)))))
 (.branch 225
 (.branch 223
 (.leaf (certNat% 222))
 (.branch 224
 (.leaf (certNat% 223))
 (.leaf (certNat% 224))))
 (.branch 227
 (.branch 226
 (.leaf (certNat% 225))
 (.leaf (certNat% 226)))
 (.branch 228
 (.leaf (certNat% 227))
 (.leaf (certNat% 228))))))
 (.branch 236
 (.branch 232
 (.branch 230
 (.leaf (certNat% 229))
 (.branch 231
 (.leaf (certNat% 230))
 (.leaf (certNat% 231))))
 (.branch 234
 (.branch 233
 (.leaf (certNat% 232))
 (.leaf (certNat% 233)))
 (.branch 235
 (.leaf (certNat% 234))
 (.leaf (certNat% 235)))))
 (.branch 239
 (.branch 237
 (.leaf (certNat% 236))
 (.branch 238
 (.leaf (certNat% 237))
 (.leaf (certNat% 238))))
 (.branch 241
 (.branch 240
 (.leaf (certNat% 239))
 (.leaf (certNat% 240)))
 (.branch 242
 (.leaf (certNat% 241))
 (.leaf (certNat% 242)))))))
 (.branch 256
 (.branch 249
 (.branch 246
 (.branch 244
 (.leaf (certNat% 243))
 (.branch 245
 (.leaf (certNat% 244))
 (.leaf (certNat% 245))))
 (.branch 247
 (.leaf (certNat% 246))
 (.branch 248
 (.leaf (certNat% 247))
 (.leaf (certNat% 248)))))
 (.branch 252
 (.branch 250
 (.leaf (certNat% 249))
 (.branch 251
 (.leaf (certNat% 250))
 (.leaf (certNat% 251))))
 (.branch 254
 (.branch 253
 (.leaf (certNat% 252))
 (.leaf (certNat% 253)))
 (.branch 255
 (.leaf (certNat% 254))
 (.leaf (certNat% 255))))))
 (.branch 263
 (.branch 259
 (.branch 257
 (.leaf (certNat% 256))
 (.branch 258
 (.leaf (certNat% 257))
 (.leaf (certNat% 258))))
 (.branch 261
 (.branch 260
 (.leaf (certNat% 259))
 (.leaf (certNat% 260)))
 (.branch 262
 (.leaf (certNat% 261))
 (.leaf (certNat% 262)))))
 (.branch 266
 (.branch 264
 (.leaf (certNat% 263))
 (.branch 265
 (.leaf (certNat% 264))
 (.leaf (certNat% 265))))
 (.branch 268
 (.branch 267
 (.leaf (certNat% 266))
 (.leaf (certNat% 267)))
 (.branch 269
 (.leaf (certNat% 268))
 (.leaf (certNat% 269))))))))
 (.branch 297
 (.branch 283
 (.branch 276
 (.branch 273
 (.branch 271
 (.leaf (certNat% 270))
 (.branch 272
 (.leaf (certNat% 271))
 (.leaf (certNat% 272))))
 (.branch 274
 (.leaf (certNat% 273))
 (.branch 275
 (.leaf (certNat% 274))
 (.leaf (certNat% 275)))))
 (.branch 279
 (.branch 277
 (.leaf (certNat% 276))
 (.branch 278
 (.leaf (certNat% 277))
 (.leaf (certNat% 278))))
 (.branch 281
 (.branch 280
 (.leaf (certNat% 279))
 (.leaf (certNat% 280)))
 (.branch 282
 (.leaf (certNat% 281))
 (.leaf (certNat% 282))))))
 (.branch 290
 (.branch 286
 (.branch 284
 (.leaf (certNat% 283))
 (.branch 285
 (.leaf (certNat% 284))
 (.leaf (certNat% 285))))
 (.branch 288
 (.branch 287
 (.leaf (certNat% 286))
 (.leaf (certNat% 287)))
 (.branch 289
 (.leaf (certNat% 288))
 (.leaf (certNat% 289)))))
 (.branch 293
 (.branch 291
 (.leaf (certNat% 290))
 (.branch 292
 (.leaf (certNat% 291))
 (.leaf (certNat% 292))))
 (.branch 295
 (.branch 294
 (.leaf (certNat% 293))
 (.leaf (certNat% 294)))
 (.branch 296
 (.leaf (certNat% 295))
 (.leaf (certNat% 296)))))))
 (.branch 310
 (.branch 303
 (.branch 300
 (.branch 298
 (.leaf (certNat% 297))
 (.branch 299
 (.leaf (certNat% 298))
 (.leaf (certNat% 299))))
 (.branch 301
 (.leaf (certNat% 300))
 (.branch 302
 (.leaf (certNat% 301))
 (.leaf (certNat% 302)))))
 (.branch 306
 (.branch 304
 (.leaf (certNat% 303))
 (.branch 305
 (.leaf (certNat% 304))
 (.leaf (certNat% 305))))
 (.branch 308
 (.branch 307
 (.leaf (certNat% 306))
 (.leaf (certNat% 307)))
 (.branch 309
 (.leaf (certNat% 308))
 (.leaf (certNat% 309))))))
 (.branch 317
 (.branch 313
 (.branch 311
 (.leaf (certNat% 310))
 (.branch 312
 (.leaf (certNat% 311))
 (.leaf (certNat% 312))))
 (.branch 315
 (.branch 314
 (.leaf (certNat% 313))
 (.leaf (certNat% 314)))
 (.branch 316
 (.leaf (certNat% 315))
 (.leaf (certNat% 316)))))
 (.branch 320
 (.branch 318
 (.leaf (certNat% 317))
 (.branch 319
 (.leaf (certNat% 318))
 (.leaf (certNat% 319))))
 (.branch 322
 (.branch 321
 (.leaf (certNat% 320))
 (.leaf (certNat% 321)))
 (.branch 323
 (.leaf (certNat% 322))
 (.leaf (certNat% 323)))))))))
 (.branch 378
 (.branch 351
 (.branch 337
 (.branch 330
 (.branch 327
 (.branch 325
 (.leaf (certNat% 324))
 (.branch 326
 (.leaf (certNat% 325))
 (.leaf (certNat% 326))))
 (.branch 328
 (.leaf (certNat% 327))
 (.branch 329
 (.leaf (certNat% 328))
 (.leaf (certNat% 329)))))
 (.branch 333
 (.branch 331
 (.leaf (certNat% 330))
 (.branch 332
 (.leaf (certNat% 331))
 (.leaf (certNat% 332))))
 (.branch 335
 (.branch 334
 (.leaf (certNat% 333))
 (.leaf (certNat% 334)))
 (.branch 336
 (.leaf (certNat% 335))
 (.leaf (certNat% 336))))))
 (.branch 344
 (.branch 340
 (.branch 338
 (.leaf (certNat% 337))
 (.branch 339
 (.leaf (certNat% 338))
 (.leaf (certNat% 339))))
 (.branch 342
 (.branch 341
 (.leaf (certNat% 340))
 (.leaf (certNat% 341)))
 (.branch 343
 (.leaf (certNat% 342))
 (.leaf (certNat% 343)))))
 (.branch 347
 (.branch 345
 (.leaf (certNat% 344))
 (.branch 346
 (.leaf (certNat% 345))
 (.leaf (certNat% 346))))
 (.branch 349
 (.branch 348
 (.leaf (certNat% 347))
 (.leaf (certNat% 348)))
 (.branch 350
 (.leaf (certNat% 349))
 (.leaf (certNat% 350)))))))
 (.branch 364
 (.branch 357
 (.branch 354
 (.branch 352
 (.leaf (certNat% 351))
 (.branch 353
 (.leaf (certNat% 352))
 (.leaf (certNat% 353))))
 (.branch 355
 (.leaf (certNat% 354))
 (.branch 356
 (.leaf (certNat% 355))
 (.leaf (certNat% 356)))))
 (.branch 360
 (.branch 358
 (.leaf (certNat% 357))
 (.branch 359
 (.leaf (certNat% 358))
 (.leaf (certNat% 359))))
 (.branch 362
 (.branch 361
 (.leaf (certNat% 360))
 (.leaf (certNat% 361)))
 (.branch 363
 (.leaf (certNat% 362))
 (.leaf (certNat% 363))))))
 (.branch 371
 (.branch 367
 (.branch 365
 (.leaf (certNat% 364))
 (.branch 366
 (.leaf (certNat% 365))
 (.leaf (certNat% 366))))
 (.branch 369
 (.branch 368
 (.leaf (certNat% 367))
 (.leaf (certNat% 368)))
 (.branch 370
 (.leaf (certNat% 369))
 (.leaf (certNat% 370)))))
 (.branch 374
 (.branch 372
 (.leaf (certNat% 371))
 (.branch 373
 (.leaf (certNat% 372))
 (.leaf (certNat% 373))))
 (.branch 376
 (.branch 375
 (.leaf (certNat% 374))
 (.leaf (certNat% 375)))
 (.branch 377
 (.leaf (certNat% 376))
 (.leaf (certNat% 377))))))))
 (.branch 405
 (.branch 391
 (.branch 384
 (.branch 381
 (.branch 379
 (.leaf (certNat% 378))
 (.branch 380
 (.leaf (certNat% 379))
 (.leaf (certNat% 380))))
 (.branch 382
 (.leaf (certNat% 381))
 (.branch 383
 (.leaf (certNat% 382))
 (.leaf (certNat% 383)))))
 (.branch 387
 (.branch 385
 (.leaf (certNat% 384))
 (.branch 386
 (.leaf (certNat% 385))
 (.leaf (certNat% 386))))
 (.branch 389
 (.branch 388
 (.leaf (certNat% 387))
 (.leaf (certNat% 388)))
 (.branch 390
 (.leaf (certNat% 389))
 (.leaf (certNat% 390))))))
 (.branch 398
 (.branch 394
 (.branch 392
 (.leaf (certNat% 391))
 (.branch 393
 (.leaf (certNat% 392))
 (.leaf (certNat% 393))))
 (.branch 396
 (.branch 395
 (.leaf (certNat% 394))
 (.leaf (certNat% 395)))
 (.branch 397
 (.leaf (certNat% 396))
 (.leaf (certNat% 397)))))
 (.branch 401
 (.branch 399
 (.leaf (certNat% 398))
 (.branch 400
 (.leaf (certNat% 399))
 (.leaf (certNat% 400))))
 (.branch 403
 (.branch 402
 (.leaf (certNat% 401))
 (.leaf (certNat% 402)))
 (.branch 404
 (.leaf (certNat% 403))
 (.leaf (certNat% 404)))))))
 (.branch 418
 (.branch 411
 (.branch 408
 (.branch 406
 (.leaf (certNat% 405))
 (.branch 407
 (.leaf (certNat% 406))
 (.leaf (certNat% 407))))
 (.branch 409
 (.leaf (certNat% 408))
 (.branch 410
 (.leaf (certNat% 409))
 (.leaf (certNat% 410)))))
 (.branch 414
 (.branch 412
 (.leaf (certNat% 411))
 (.branch 413
 (.leaf (certNat% 412))
 (.leaf (certNat% 413))))
 (.branch 416
 (.branch 415
 (.leaf (certNat% 414))
 (.leaf (certNat% 415)))
 (.branch 417
 (.leaf (certNat% 416))
 (.leaf (certNat% 417))))))
 (.branch 425
 (.branch 421
 (.branch 419
 (.leaf (certNat% 418))
 (.branch 420
 (.leaf (certNat% 419))
 (.leaf (certNat% 420))))
 (.branch 423
 (.branch 422
 (.leaf (certNat% 421))
 (.leaf (certNat% 422)))
 (.branch 424
 (.leaf (certNat% 423))
 (.leaf (certNat% 424)))))
 (.branch 428
 (.branch 426
 (.leaf (certNat% 425))
 (.branch 427
 (.leaf (certNat% 426))
 (.leaf (certNat% 427))))
 (.branch 430
 (.branch 429
 (.leaf (certNat% 428))
 (.leaf (certNat% 429)))
 (.branch 431
 (.leaf (certNat% 430))
 (.leaf (certNat% 431)))))))))))
def rawLeaves (i : Nat) : List Nat :=
  let code := leafTable.get i
  (PackedRawNatGrowth.readList 12 (PackedRawNatGrowth.take 5 code)
    (PackedRawNatGrowth.drop 5 code)).1

cert_leaves_4
cert_quota_5 2 2 8
cert_nodeTest_6
cert_nodeTest_sound_5
cert_leafTest_6
end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest18

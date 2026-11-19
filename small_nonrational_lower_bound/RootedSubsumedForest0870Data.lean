module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public meta import CertificateNumbers
public import RootedSixExtra05GrowthCacheData
public import RootedSixExtra05FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification
public import RootedSubsumedForest0870Packed000
public import RootedSubsumedForest0870Packed001
public import RootedSubsumedForest0870Packed002
public import RootedSubsumedForest0870Packed003

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0870
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 2170
abbrev nodeCount : Nat := 22983
abbrev leafCount : Nat := 835
cert_widths_3 12 15 9 10
def blocks : Table PackedRawNatGrowth.Block :=
(.branch 100
 (.branch 50
 nodeBlocks000
 nodeBlocks001)
 (.branch 150
 nodeBlocks002
 nodeBlocks003))
def counterTable : Table Nat :=
(.branch 100
 (.branch 50
 nodeCounters000
 nodeCounters001)
 (.branch 150
 nodeCounters002
 nodeCounters003))
cert_codes_3
cert_counters_3 55
cert_rawNodes_3
def leafTable : Table Nat :=
(.branch 417
 (.branch 208
 (.branch 104
 (.branch 52
 (.branch 26
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
 (.branch 19
 (.branch 16
 (.branch 14
 (.leaf (certNat% 13))
 (.branch 15
 (.leaf (certNat% 14))
 (.leaf (certNat% 15))))
 (.branch 17
 (.leaf (certNat% 16))
 (.branch 18
 (.leaf (certNat% 17))
 (.leaf (certNat% 18)))))
 (.branch 22
 (.branch 20
 (.leaf (certNat% 19))
 (.branch 21
 (.leaf (certNat% 20))
 (.leaf (certNat% 21))))
 (.branch 24
 (.branch 23
 (.leaf (certNat% 22))
 (.leaf (certNat% 23)))
 (.branch 25
 (.leaf (certNat% 24))
 (.leaf (certNat% 25)))))))
 (.branch 39
 (.branch 32
 (.branch 29
 (.branch 27
 (.leaf (certNat% 26))
 (.branch 28
 (.leaf (certNat% 27))
 (.leaf (certNat% 28))))
 (.branch 30
 (.leaf (certNat% 29))
 (.branch 31
 (.leaf (certNat% 30))
 (.leaf (certNat% 31)))))
 (.branch 35
 (.branch 33
 (.leaf (certNat% 32))
 (.branch 34
 (.leaf (certNat% 33))
 (.leaf (certNat% 34))))
 (.branch 37
 (.branch 36
 (.leaf (certNat% 35))
 (.leaf (certNat% 36)))
 (.branch 38
 (.leaf (certNat% 37))
 (.leaf (certNat% 38))))))
 (.branch 45
 (.branch 42
 (.branch 40
 (.leaf (certNat% 39))
 (.branch 41
 (.leaf (certNat% 40))
 (.leaf (certNat% 41))))
 (.branch 43
 (.leaf (certNat% 42))
 (.branch 44
 (.leaf (certNat% 43))
 (.leaf (certNat% 44)))))
 (.branch 48
 (.branch 46
 (.leaf (certNat% 45))
 (.branch 47
 (.leaf (certNat% 46))
 (.leaf (certNat% 47))))
 (.branch 50
 (.branch 49
 (.leaf (certNat% 48))
 (.leaf (certNat% 49)))
 (.branch 51
 (.leaf (certNat% 50))
 (.leaf (certNat% 51))))))))
 (.branch 78
 (.branch 65
 (.branch 58
 (.branch 55
 (.branch 53
 (.leaf (certNat% 52))
 (.branch 54
 (.leaf (certNat% 53))
 (.leaf (certNat% 54))))
 (.branch 56
 (.leaf (certNat% 55))
 (.branch 57
 (.leaf (certNat% 56))
 (.leaf (certNat% 57)))))
 (.branch 61
 (.branch 59
 (.leaf (certNat% 58))
 (.branch 60
 (.leaf (certNat% 59))
 (.leaf (certNat% 60))))
 (.branch 63
 (.branch 62
 (.leaf (certNat% 61))
 (.leaf (certNat% 62)))
 (.branch 64
 (.leaf (certNat% 63))
 (.leaf (certNat% 64))))))
 (.branch 71
 (.branch 68
 (.branch 66
 (.leaf (certNat% 65))
 (.branch 67
 (.leaf (certNat% 66))
 (.leaf (certNat% 67))))
 (.branch 69
 (.leaf (certNat% 68))
 (.branch 70
 (.leaf (certNat% 69))
 (.leaf (certNat% 70)))))
 (.branch 74
 (.branch 72
 (.leaf (certNat% 71))
 (.branch 73
 (.leaf (certNat% 72))
 (.leaf (certNat% 73))))
 (.branch 76
 (.branch 75
 (.leaf (certNat% 74))
 (.leaf (certNat% 75)))
 (.branch 77
 (.leaf (certNat% 76))
 (.leaf (certNat% 77)))))))
 (.branch 91
 (.branch 84
 (.branch 81
 (.branch 79
 (.leaf (certNat% 78))
 (.branch 80
 (.leaf (certNat% 79))
 (.leaf (certNat% 80))))
 (.branch 82
 (.leaf (certNat% 81))
 (.branch 83
 (.leaf (certNat% 82))
 (.leaf (certNat% 83)))))
 (.branch 87
 (.branch 85
 (.leaf (certNat% 84))
 (.branch 86
 (.leaf (certNat% 85))
 (.leaf (certNat% 86))))
 (.branch 89
 (.branch 88
 (.leaf (certNat% 87))
 (.leaf (certNat% 88)))
 (.branch 90
 (.leaf (certNat% 89))
 (.leaf (certNat% 90))))))
 (.branch 97
 (.branch 94
 (.branch 92
 (.leaf (certNat% 91))
 (.branch 93
 (.leaf (certNat% 92))
 (.leaf (certNat% 93))))
 (.branch 95
 (.leaf (certNat% 94))
 (.branch 96
 (.leaf (certNat% 95))
 (.leaf (certNat% 96)))))
 (.branch 100
 (.branch 98
 (.leaf (certNat% 97))
 (.branch 99
 (.leaf (certNat% 98))
 (.leaf (certNat% 99))))
 (.branch 102
 (.branch 101
 (.leaf (certNat% 100))
 (.leaf (certNat% 101)))
 (.branch 103
 (.leaf (certNat% 102))
 (.leaf (certNat% 103)))))))))
 (.branch 156
 (.branch 130
 (.branch 117
 (.branch 110
 (.branch 107
 (.branch 105
 (.leaf (certNat% 104))
 (.branch 106
 (.leaf (certNat% 105))
 (.leaf (certNat% 106))))
 (.branch 108
 (.leaf (certNat% 107))
 (.branch 109
 (.leaf (certNat% 108))
 (.leaf (certNat% 109)))))
 (.branch 113
 (.branch 111
 (.leaf (certNat% 110))
 (.branch 112
 (.leaf (certNat% 111))
 (.leaf (certNat% 112))))
 (.branch 115
 (.branch 114
 (.leaf (certNat% 113))
 (.leaf (certNat% 114)))
 (.branch 116
 (.leaf (certNat% 115))
 (.leaf (certNat% 116))))))
 (.branch 123
 (.branch 120
 (.branch 118
 (.leaf (certNat% 117))
 (.branch 119
 (.leaf (certNat% 118))
 (.leaf (certNat% 119))))
 (.branch 121
 (.leaf (certNat% 120))
 (.branch 122
 (.leaf (certNat% 121))
 (.leaf (certNat% 122)))))
 (.branch 126
 (.branch 124
 (.leaf (certNat% 123))
 (.branch 125
 (.leaf (certNat% 124))
 (.leaf (certNat% 125))))
 (.branch 128
 (.branch 127
 (.leaf (certNat% 126))
 (.leaf (certNat% 127)))
 (.branch 129
 (.leaf (certNat% 128))
 (.leaf (certNat% 129)))))))
 (.branch 143
 (.branch 136
 (.branch 133
 (.branch 131
 (.leaf (certNat% 130))
 (.branch 132
 (.leaf (certNat% 131))
 (.leaf (certNat% 132))))
 (.branch 134
 (.leaf (certNat% 133))
 (.branch 135
 (.leaf (certNat% 134))
 (.leaf (certNat% 135)))))
 (.branch 139
 (.branch 137
 (.leaf (certNat% 136))
 (.branch 138
 (.leaf (certNat% 137))
 (.leaf (certNat% 138))))
 (.branch 141
 (.branch 140
 (.leaf (certNat% 139))
 (.leaf (certNat% 140)))
 (.branch 142
 (.leaf (certNat% 141))
 (.leaf (certNat% 142))))))
 (.branch 149
 (.branch 146
 (.branch 144
 (.leaf (certNat% 143))
 (.branch 145
 (.leaf (certNat% 144))
 (.leaf (certNat% 145))))
 (.branch 147
 (.leaf (certNat% 146))
 (.branch 148
 (.leaf (certNat% 147))
 (.leaf (certNat% 148)))))
 (.branch 152
 (.branch 150
 (.leaf (certNat% 149))
 (.branch 151
 (.leaf (certNat% 150))
 (.leaf (certNat% 151))))
 (.branch 154
 (.branch 153
 (.leaf (certNat% 152))
 (.leaf (certNat% 153)))
 (.branch 155
 (.leaf (certNat% 154))
 (.leaf (certNat% 155))))))))
 (.branch 182
 (.branch 169
 (.branch 162
 (.branch 159
 (.branch 157
 (.leaf (certNat% 156))
 (.branch 158
 (.leaf (certNat% 157))
 (.leaf (certNat% 158))))
 (.branch 160
 (.leaf (certNat% 159))
 (.branch 161
 (.leaf (certNat% 160))
 (.leaf (certNat% 161)))))
 (.branch 165
 (.branch 163
 (.leaf (certNat% 162))
 (.branch 164
 (.leaf (certNat% 163))
 (.leaf (certNat% 164))))
 (.branch 167
 (.branch 166
 (.leaf (certNat% 165))
 (.leaf (certNat% 166)))
 (.branch 168
 (.leaf (certNat% 167))
 (.leaf (certNat% 168))))))
 (.branch 175
 (.branch 172
 (.branch 170
 (.leaf (certNat% 169))
 (.branch 171
 (.leaf (certNat% 170))
 (.leaf (certNat% 171))))
 (.branch 173
 (.leaf (certNat% 172))
 (.branch 174
 (.leaf (certNat% 173))
 (.leaf (certNat% 174)))))
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
 (.leaf (certNat% 181)))))))
 (.branch 195
 (.branch 188
 (.branch 185
 (.branch 183
 (.leaf (certNat% 182))
 (.branch 184
 (.leaf (certNat% 183))
 (.leaf (certNat% 184))))
 (.branch 186
 (.leaf (certNat% 185))
 (.branch 187
 (.leaf (certNat% 186))
 (.leaf (certNat% 187)))))
 (.branch 191
 (.branch 189
 (.leaf (certNat% 188))
 (.branch 190
 (.leaf (certNat% 189))
 (.leaf (certNat% 190))))
 (.branch 193
 (.branch 192
 (.leaf (certNat% 191))
 (.leaf (certNat% 192)))
 (.branch 194
 (.leaf (certNat% 193))
 (.leaf (certNat% 194))))))
 (.branch 201
 (.branch 198
 (.branch 196
 (.leaf (certNat% 195))
 (.branch 197
 (.leaf (certNat% 196))
 (.leaf (certNat% 197))))
 (.branch 199
 (.leaf (certNat% 198))
 (.branch 200
 (.leaf (certNat% 199))
 (.leaf (certNat% 200)))))
 (.branch 204
 (.branch 202
 (.leaf (certNat% 201))
 (.branch 203
 (.leaf (certNat% 202))
 (.leaf (certNat% 203))))
 (.branch 206
 (.branch 205
 (.leaf (certNat% 204))
 (.leaf (certNat% 205)))
 (.branch 207
 (.leaf (certNat% 206))
 (.leaf (certNat% 207))))))))))
 (.branch 312
 (.branch 260
 (.branch 234
 (.branch 221
 (.branch 214
 (.branch 211
 (.branch 209
 (.leaf (certNat% 208))
 (.branch 210
 (.leaf (certNat% 209))
 (.leaf (certNat% 210))))
 (.branch 212
 (.leaf (certNat% 211))
 (.branch 213
 (.leaf (certNat% 212))
 (.leaf (certNat% 213)))))
 (.branch 217
 (.branch 215
 (.leaf (certNat% 214))
 (.branch 216
 (.leaf (certNat% 215))
 (.leaf (certNat% 216))))
 (.branch 219
 (.branch 218
 (.leaf (certNat% 217))
 (.leaf (certNat% 218)))
 (.branch 220
 (.leaf (certNat% 219))
 (.leaf (certNat% 220))))))
 (.branch 227
 (.branch 224
 (.branch 222
 (.leaf (certNat% 221))
 (.branch 223
 (.leaf (certNat% 222))
 (.leaf (certNat% 223))))
 (.branch 225
 (.leaf (certNat% 224))
 (.branch 226
 (.leaf (certNat% 225))
 (.leaf (certNat% 226)))))
 (.branch 230
 (.branch 228
 (.leaf (certNat% 227))
 (.branch 229
 (.leaf (certNat% 228))
 (.leaf (certNat% 229))))
 (.branch 232
 (.branch 231
 (.leaf (certNat% 230))
 (.leaf (certNat% 231)))
 (.branch 233
 (.leaf (certNat% 232))
 (.leaf (certNat% 233)))))))
 (.branch 247
 (.branch 240
 (.branch 237
 (.branch 235
 (.leaf (certNat% 234))
 (.branch 236
 (.leaf (certNat% 235))
 (.leaf (certNat% 236))))
 (.branch 238
 (.leaf (certNat% 237))
 (.branch 239
 (.leaf (certNat% 238))
 (.leaf (certNat% 239)))))
 (.branch 243
 (.branch 241
 (.leaf (certNat% 240))
 (.branch 242
 (.leaf (certNat% 241))
 (.leaf (certNat% 242))))
 (.branch 245
 (.branch 244
 (.leaf (certNat% 243))
 (.leaf (certNat% 244)))
 (.branch 246
 (.leaf (certNat% 245))
 (.leaf (certNat% 246))))))
 (.branch 253
 (.branch 250
 (.branch 248
 (.leaf (certNat% 247))
 (.branch 249
 (.leaf (certNat% 248))
 (.leaf (certNat% 249))))
 (.branch 251
 (.leaf (certNat% 250))
 (.branch 252
 (.leaf (certNat% 251))
 (.leaf (certNat% 252)))))
 (.branch 256
 (.branch 254
 (.leaf (certNat% 253))
 (.branch 255
 (.leaf (certNat% 254))
 (.leaf (certNat% 255))))
 (.branch 258
 (.branch 257
 (.leaf (certNat% 256))
 (.leaf (certNat% 257)))
 (.branch 259
 (.leaf (certNat% 258))
 (.leaf (certNat% 259))))))))
 (.branch 286
 (.branch 273
 (.branch 266
 (.branch 263
 (.branch 261
 (.leaf (certNat% 260))
 (.branch 262
 (.leaf (certNat% 261))
 (.leaf (certNat% 262))))
 (.branch 264
 (.leaf (certNat% 263))
 (.branch 265
 (.leaf (certNat% 264))
 (.leaf (certNat% 265)))))
 (.branch 269
 (.branch 267
 (.leaf (certNat% 266))
 (.branch 268
 (.leaf (certNat% 267))
 (.leaf (certNat% 268))))
 (.branch 271
 (.branch 270
 (.leaf (certNat% 269))
 (.leaf (certNat% 270)))
 (.branch 272
 (.leaf (certNat% 271))
 (.leaf (certNat% 272))))))
 (.branch 279
 (.branch 276
 (.branch 274
 (.leaf (certNat% 273))
 (.branch 275
 (.leaf (certNat% 274))
 (.leaf (certNat% 275))))
 (.branch 277
 (.leaf (certNat% 276))
 (.branch 278
 (.leaf (certNat% 277))
 (.leaf (certNat% 278)))))
 (.branch 282
 (.branch 280
 (.leaf (certNat% 279))
 (.branch 281
 (.leaf (certNat% 280))
 (.leaf (certNat% 281))))
 (.branch 284
 (.branch 283
 (.leaf (certNat% 282))
 (.leaf (certNat% 283)))
 (.branch 285
 (.leaf (certNat% 284))
 (.leaf (certNat% 285)))))))
 (.branch 299
 (.branch 292
 (.branch 289
 (.branch 287
 (.leaf (certNat% 286))
 (.branch 288
 (.leaf (certNat% 287))
 (.leaf (certNat% 288))))
 (.branch 290
 (.leaf (certNat% 289))
 (.branch 291
 (.leaf (certNat% 290))
 (.leaf (certNat% 291)))))
 (.branch 295
 (.branch 293
 (.leaf (certNat% 292))
 (.branch 294
 (.leaf (certNat% 293))
 (.leaf (certNat% 294))))
 (.branch 297
 (.branch 296
 (.leaf (certNat% 295))
 (.leaf (certNat% 296)))
 (.branch 298
 (.leaf (certNat% 297))
 (.leaf (certNat% 298))))))
 (.branch 305
 (.branch 302
 (.branch 300
 (.leaf (certNat% 299))
 (.branch 301
 (.leaf (certNat% 300))
 (.leaf (certNat% 301))))
 (.branch 303
 (.leaf (certNat% 302))
 (.branch 304
 (.leaf (certNat% 303))
 (.leaf (certNat% 304)))))
 (.branch 308
 (.branch 306
 (.leaf (certNat% 305))
 (.branch 307
 (.leaf (certNat% 306))
 (.leaf (certNat% 307))))
 (.branch 310
 (.branch 309
 (.leaf (certNat% 308))
 (.leaf (certNat% 309)))
 (.branch 311
 (.leaf (certNat% 310))
 (.leaf (certNat% 311)))))))))
 (.branch 364
 (.branch 338
 (.branch 325
 (.branch 318
 (.branch 315
 (.branch 313
 (.leaf (certNat% 312))
 (.branch 314
 (.leaf (certNat% 313))
 (.leaf (certNat% 314))))
 (.branch 316
 (.leaf (certNat% 315))
 (.branch 317
 (.leaf (certNat% 316))
 (.leaf (certNat% 317)))))
 (.branch 321
 (.branch 319
 (.leaf (certNat% 318))
 (.branch 320
 (.leaf (certNat% 319))
 (.leaf (certNat% 320))))
 (.branch 323
 (.branch 322
 (.leaf (certNat% 321))
 (.leaf (certNat% 322)))
 (.branch 324
 (.leaf (certNat% 323))
 (.leaf (certNat% 324))))))
 (.branch 331
 (.branch 328
 (.branch 326
 (.leaf (certNat% 325))
 (.branch 327
 (.leaf (certNat% 326))
 (.leaf (certNat% 327))))
 (.branch 329
 (.leaf (certNat% 328))
 (.branch 330
 (.leaf (certNat% 329))
 (.leaf (certNat% 330)))))
 (.branch 334
 (.branch 332
 (.leaf (certNat% 331))
 (.branch 333
 (.leaf (certNat% 332))
 (.leaf (certNat% 333))))
 (.branch 336
 (.branch 335
 (.leaf (certNat% 334))
 (.leaf (certNat% 335)))
 (.branch 337
 (.leaf (certNat% 336))
 (.leaf (certNat% 337)))))))
 (.branch 351
 (.branch 344
 (.branch 341
 (.branch 339
 (.leaf (certNat% 338))
 (.branch 340
 (.leaf (certNat% 339))
 (.leaf (certNat% 340))))
 (.branch 342
 (.leaf (certNat% 341))
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
 (.leaf (certNat% 350))))))
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
 (.leaf (certNat% 363))))))))
 (.branch 390
 (.branch 377
 (.branch 370
 (.branch 367
 (.branch 365
 (.leaf (certNat% 364))
 (.branch 366
 (.leaf (certNat% 365))
 (.leaf (certNat% 366))))
 (.branch 368
 (.leaf (certNat% 367))
 (.branch 369
 (.leaf (certNat% 368))
 (.leaf (certNat% 369)))))
 (.branch 373
 (.branch 371
 (.leaf (certNat% 370))
 (.branch 372
 (.leaf (certNat% 371))
 (.leaf (certNat% 372))))
 (.branch 375
 (.branch 374
 (.leaf (certNat% 373))
 (.leaf (certNat% 374)))
 (.branch 376
 (.leaf (certNat% 375))
 (.leaf (certNat% 376))))))
 (.branch 383
 (.branch 380
 (.branch 378
 (.leaf (certNat% 377))
 (.branch 379
 (.leaf (certNat% 378))
 (.leaf (certNat% 379))))
 (.branch 381
 (.leaf (certNat% 380))
 (.branch 382
 (.leaf (certNat% 381))
 (.leaf (certNat% 382)))))
 (.branch 386
 (.branch 384
 (.leaf (certNat% 383))
 (.branch 385
 (.leaf (certNat% 384))
 (.leaf (certNat% 385))))
 (.branch 388
 (.branch 387
 (.leaf (certNat% 386))
 (.leaf (certNat% 387)))
 (.branch 389
 (.leaf (certNat% 388))
 (.leaf (certNat% 389)))))))
 (.branch 403
 (.branch 396
 (.branch 393
 (.branch 391
 (.leaf (certNat% 390))
 (.branch 392
 (.leaf (certNat% 391))
 (.leaf (certNat% 392))))
 (.branch 394
 (.leaf (certNat% 393))
 (.branch 395
 (.leaf (certNat% 394))
 (.leaf (certNat% 395)))))
 (.branch 399
 (.branch 397
 (.leaf (certNat% 396))
 (.branch 398
 (.leaf (certNat% 397))
 (.leaf (certNat% 398))))
 (.branch 401
 (.branch 400
 (.leaf (certNat% 399))
 (.leaf (certNat% 400)))
 (.branch 402
 (.leaf (certNat% 401))
 (.leaf (certNat% 402))))))
 (.branch 410
 (.branch 406
 (.branch 404
 (.leaf (certNat% 403))
 (.branch 405
 (.leaf (certNat% 404))
 (.leaf (certNat% 405))))
 (.branch 408
 (.branch 407
 (.leaf (certNat% 406))
 (.leaf (certNat% 407)))
 (.branch 409
 (.leaf (certNat% 408))
 (.leaf (certNat% 409)))))
 (.branch 413
 (.branch 411
 (.leaf (certNat% 410))
 (.branch 412
 (.leaf (certNat% 411))
 (.leaf (certNat% 412))))
 (.branch 415
 (.branch 414
 (.leaf (certNat% 413))
 (.leaf (certNat% 414)))
 (.branch 416
 (.leaf (certNat% 415))
 (.leaf (certNat% 416)))))))))))
 (.branch 626
 (.branch 521
 (.branch 469
 (.branch 443
 (.branch 430
 (.branch 423
 (.branch 420
 (.branch 418
 (.leaf (certNat% 417))
 (.branch 419
 (.leaf (certNat% 418))
 (.leaf (certNat% 419))))
 (.branch 421
 (.leaf (certNat% 420))
 (.branch 422
 (.leaf (certNat% 421))
 (.leaf (certNat% 422)))))
 (.branch 426
 (.branch 424
 (.leaf (certNat% 423))
 (.branch 425
 (.leaf (certNat% 424))
 (.leaf (certNat% 425))))
 (.branch 428
 (.branch 427
 (.leaf (certNat% 426))
 (.leaf (certNat% 427)))
 (.branch 429
 (.leaf (certNat% 428))
 (.leaf (certNat% 429))))))
 (.branch 436
 (.branch 433
 (.branch 431
 (.leaf (certNat% 430))
 (.branch 432
 (.leaf (certNat% 431))
 (.leaf (certNat% 432))))
 (.branch 434
 (.leaf (certNat% 433))
 (.branch 435
 (.leaf (certNat% 434))
 (.leaf (certNat% 435)))))
 (.branch 439
 (.branch 437
 (.leaf (certNat% 436))
 (.branch 438
 (.leaf (certNat% 437))
 (.leaf (certNat% 438))))
 (.branch 441
 (.branch 440
 (.leaf (certNat% 439))
 (.leaf (certNat% 440)))
 (.branch 442
 (.leaf (certNat% 441))
 (.leaf (certNat% 442)))))))
 (.branch 456
 (.branch 449
 (.branch 446
 (.branch 444
 (.leaf (certNat% 443))
 (.branch 445
 (.leaf (certNat% 444))
 (.leaf (certNat% 445))))
 (.branch 447
 (.leaf (certNat% 446))
 (.branch 448
 (.leaf (certNat% 447))
 (.leaf (certNat% 448)))))
 (.branch 452
 (.branch 450
 (.leaf (certNat% 449))
 (.branch 451
 (.leaf (certNat% 450))
 (.leaf (certNat% 451))))
 (.branch 454
 (.branch 453
 (.leaf (certNat% 452))
 (.leaf (certNat% 453)))
 (.branch 455
 (.leaf (certNat% 454))
 (.leaf (certNat% 455))))))
 (.branch 462
 (.branch 459
 (.branch 457
 (.leaf (certNat% 456))
 (.branch 458
 (.leaf (certNat% 457))
 (.leaf (certNat% 458))))
 (.branch 460
 (.leaf (certNat% 459))
 (.branch 461
 (.leaf (certNat% 460))
 (.leaf (certNat% 461)))))
 (.branch 465
 (.branch 463
 (.leaf (certNat% 462))
 (.branch 464
 (.leaf (certNat% 463))
 (.leaf (certNat% 464))))
 (.branch 467
 (.branch 466
 (.leaf (certNat% 465))
 (.leaf (certNat% 466)))
 (.branch 468
 (.leaf (certNat% 467))
 (.leaf (certNat% 468))))))))
 (.branch 495
 (.branch 482
 (.branch 475
 (.branch 472
 (.branch 470
 (.leaf (certNat% 469))
 (.branch 471
 (.leaf (certNat% 470))
 (.leaf (certNat% 471))))
 (.branch 473
 (.leaf (certNat% 472))
 (.branch 474
 (.leaf (certNat% 473))
 (.leaf (certNat% 474)))))
 (.branch 478
 (.branch 476
 (.leaf (certNat% 475))
 (.branch 477
 (.leaf (certNat% 476))
 (.leaf (certNat% 477))))
 (.branch 480
 (.branch 479
 (.leaf (certNat% 478))
 (.leaf (certNat% 479)))
 (.branch 481
 (.leaf (certNat% 480))
 (.leaf (certNat% 481))))))
 (.branch 488
 (.branch 485
 (.branch 483
 (.leaf (certNat% 482))
 (.branch 484
 (.leaf (certNat% 483))
 (.leaf (certNat% 484))))
 (.branch 486
 (.leaf (certNat% 485))
 (.branch 487
 (.leaf (certNat% 486))
 (.leaf (certNat% 487)))))
 (.branch 491
 (.branch 489
 (.leaf (certNat% 488))
 (.branch 490
 (.leaf (certNat% 489))
 (.leaf (certNat% 490))))
 (.branch 493
 (.branch 492
 (.leaf (certNat% 491))
 (.leaf (certNat% 492)))
 (.branch 494
 (.leaf (certNat% 493))
 (.leaf (certNat% 494)))))))
 (.branch 508
 (.branch 501
 (.branch 498
 (.branch 496
 (.leaf (certNat% 495))
 (.branch 497
 (.leaf (certNat% 496))
 (.leaf (certNat% 497))))
 (.branch 499
 (.leaf (certNat% 498))
 (.branch 500
 (.leaf (certNat% 499))
 (.leaf (certNat% 500)))))
 (.branch 504
 (.branch 502
 (.leaf (certNat% 501))
 (.branch 503
 (.leaf (certNat% 502))
 (.leaf (certNat% 503))))
 (.branch 506
 (.branch 505
 (.leaf (certNat% 504))
 (.leaf (certNat% 505)))
 (.branch 507
 (.leaf (certNat% 506))
 (.leaf (certNat% 507))))))
 (.branch 514
 (.branch 511
 (.branch 509
 (.leaf (certNat% 508))
 (.branch 510
 (.leaf (certNat% 509))
 (.leaf (certNat% 510))))
 (.branch 512
 (.leaf (certNat% 511))
 (.branch 513
 (.leaf (certNat% 512))
 (.leaf (certNat% 513)))))
 (.branch 517
 (.branch 515
 (.leaf (certNat% 514))
 (.branch 516
 (.leaf (certNat% 515))
 (.leaf (certNat% 516))))
 (.branch 519
 (.branch 518
 (.leaf (certNat% 517))
 (.leaf (certNat% 518)))
 (.branch 520
 (.leaf (certNat% 519))
 (.leaf (certNat% 520)))))))))
 (.branch 573
 (.branch 547
 (.branch 534
 (.branch 527
 (.branch 524
 (.branch 522
 (.leaf (certNat% 521))
 (.branch 523
 (.leaf (certNat% 522))
 (.leaf (certNat% 523))))
 (.branch 525
 (.leaf (certNat% 524))
 (.branch 526
 (.leaf (certNat% 525))
 (.leaf (certNat% 526)))))
 (.branch 530
 (.branch 528
 (.leaf (certNat% 527))
 (.branch 529
 (.leaf (certNat% 528))
 (.leaf (certNat% 529))))
 (.branch 532
 (.branch 531
 (.leaf (certNat% 530))
 (.leaf (certNat% 531)))
 (.branch 533
 (.leaf (certNat% 532))
 (.leaf (certNat% 533))))))
 (.branch 540
 (.branch 537
 (.branch 535
 (.leaf (certNat% 534))
 (.branch 536
 (.leaf (certNat% 535))
 (.leaf (certNat% 536))))
 (.branch 538
 (.leaf (certNat% 537))
 (.branch 539
 (.leaf (certNat% 538))
 (.leaf (certNat% 539)))))
 (.branch 543
 (.branch 541
 (.leaf (certNat% 540))
 (.branch 542
 (.leaf (certNat% 541))
 (.leaf (certNat% 542))))
 (.branch 545
 (.branch 544
 (.leaf (certNat% 543))
 (.leaf (certNat% 544)))
 (.branch 546
 (.leaf (certNat% 545))
 (.leaf (certNat% 546)))))))
 (.branch 560
 (.branch 553
 (.branch 550
 (.branch 548
 (.leaf (certNat% 547))
 (.branch 549
 (.leaf (certNat% 548))
 (.leaf (certNat% 549))))
 (.branch 551
 (.leaf (certNat% 550))
 (.branch 552
 (.leaf (certNat% 551))
 (.leaf (certNat% 552)))))
 (.branch 556
 (.branch 554
 (.leaf (certNat% 553))
 (.branch 555
 (.leaf (certNat% 554))
 (.leaf (certNat% 555))))
 (.branch 558
 (.branch 557
 (.leaf (certNat% 556))
 (.leaf (certNat% 557)))
 (.branch 559
 (.leaf (certNat% 558))
 (.leaf (certNat% 559))))))
 (.branch 566
 (.branch 563
 (.branch 561
 (.leaf (certNat% 560))
 (.branch 562
 (.leaf (certNat% 561))
 (.leaf (certNat% 562))))
 (.branch 564
 (.leaf (certNat% 563))
 (.branch 565
 (.leaf (certNat% 564))
 (.leaf (certNat% 565)))))
 (.branch 569
 (.branch 567
 (.leaf (certNat% 566))
 (.branch 568
 (.leaf (certNat% 567))
 (.leaf (certNat% 568))))
 (.branch 571
 (.branch 570
 (.leaf (certNat% 569))
 (.leaf (certNat% 570)))
 (.branch 572
 (.leaf (certNat% 571))
 (.leaf (certNat% 572))))))))
 (.branch 599
 (.branch 586
 (.branch 579
 (.branch 576
 (.branch 574
 (.leaf (certNat% 573))
 (.branch 575
 (.leaf (certNat% 574))
 (.leaf (certNat% 575))))
 (.branch 577
 (.leaf (certNat% 576))
 (.branch 578
 (.leaf (certNat% 577))
 (.leaf (certNat% 578)))))
 (.branch 582
 (.branch 580
 (.leaf (certNat% 579))
 (.branch 581
 (.leaf (certNat% 580))
 (.leaf (certNat% 581))))
 (.branch 584
 (.branch 583
 (.leaf (certNat% 582))
 (.leaf (certNat% 583)))
 (.branch 585
 (.leaf (certNat% 584))
 (.leaf (certNat% 585))))))
 (.branch 592
 (.branch 589
 (.branch 587
 (.leaf (certNat% 586))
 (.branch 588
 (.leaf (certNat% 587))
 (.leaf (certNat% 588))))
 (.branch 590
 (.leaf (certNat% 589))
 (.branch 591
 (.leaf (certNat% 590))
 (.leaf (certNat% 591)))))
 (.branch 595
 (.branch 593
 (.leaf (certNat% 592))
 (.branch 594
 (.leaf (certNat% 593))
 (.leaf (certNat% 594))))
 (.branch 597
 (.branch 596
 (.leaf (certNat% 595))
 (.leaf (certNat% 596)))
 (.branch 598
 (.leaf (certNat% 597))
 (.leaf (certNat% 598)))))))
 (.branch 612
 (.branch 605
 (.branch 602
 (.branch 600
 (.leaf (certNat% 599))
 (.branch 601
 (.leaf (certNat% 600))
 (.leaf (certNat% 601))))
 (.branch 603
 (.leaf (certNat% 602))
 (.branch 604
 (.leaf (certNat% 603))
 (.leaf (certNat% 604)))))
 (.branch 608
 (.branch 606
 (.leaf (certNat% 605))
 (.branch 607
 (.leaf (certNat% 606))
 (.leaf (certNat% 607))))
 (.branch 610
 (.branch 609
 (.leaf (certNat% 608))
 (.leaf (certNat% 609)))
 (.branch 611
 (.leaf (certNat% 610))
 (.leaf (certNat% 611))))))
 (.branch 619
 (.branch 615
 (.branch 613
 (.leaf (certNat% 612))
 (.branch 614
 (.leaf (certNat% 613))
 (.leaf (certNat% 614))))
 (.branch 617
 (.branch 616
 (.leaf (certNat% 615))
 (.leaf (certNat% 616)))
 (.branch 618
 (.leaf (certNat% 617))
 (.leaf (certNat% 618)))))
 (.branch 622
 (.branch 620
 (.leaf (certNat% 619))
 (.branch 621
 (.leaf (certNat% 620))
 (.leaf (certNat% 621))))
 (.branch 624
 (.branch 623
 (.leaf (certNat% 622))
 (.leaf (certNat% 623)))
 (.branch 625
 (.leaf (certNat% 624))
 (.leaf (certNat% 625))))))))))
 (.branch 730
 (.branch 678
 (.branch 652
 (.branch 639
 (.branch 632
 (.branch 629
 (.branch 627
 (.leaf (certNat% 626))
 (.branch 628
 (.leaf (certNat% 627))
 (.leaf (certNat% 628))))
 (.branch 630
 (.leaf (certNat% 629))
 (.branch 631
 (.leaf (certNat% 630))
 (.leaf (certNat% 631)))))
 (.branch 635
 (.branch 633
 (.leaf (certNat% 632))
 (.branch 634
 (.leaf (certNat% 633))
 (.leaf (certNat% 634))))
 (.branch 637
 (.branch 636
 (.leaf (certNat% 635))
 (.leaf (certNat% 636)))
 (.branch 638
 (.leaf (certNat% 637))
 (.leaf (certNat% 638))))))
 (.branch 645
 (.branch 642
 (.branch 640
 (.leaf (certNat% 639))
 (.branch 641
 (.leaf (certNat% 640))
 (.leaf (certNat% 641))))
 (.branch 643
 (.leaf (certNat% 642))
 (.branch 644
 (.leaf (certNat% 643))
 (.leaf (certNat% 644)))))
 (.branch 648
 (.branch 646
 (.leaf (certNat% 645))
 (.branch 647
 (.leaf (certNat% 646))
 (.leaf (certNat% 647))))
 (.branch 650
 (.branch 649
 (.leaf (certNat% 648))
 (.leaf (certNat% 649)))
 (.branch 651
 (.leaf (certNat% 650))
 (.leaf (certNat% 651)))))))
 (.branch 665
 (.branch 658
 (.branch 655
 (.branch 653
 (.leaf (certNat% 652))
 (.branch 654
 (.leaf (certNat% 653))
 (.leaf (certNat% 654))))
 (.branch 656
 (.leaf (certNat% 655))
 (.branch 657
 (.leaf (certNat% 656))
 (.leaf (certNat% 657)))))
 (.branch 661
 (.branch 659
 (.leaf (certNat% 658))
 (.branch 660
 (.leaf (certNat% 659))
 (.leaf (certNat% 660))))
 (.branch 663
 (.branch 662
 (.leaf (certNat% 661))
 (.leaf (certNat% 662)))
 (.branch 664
 (.leaf (certNat% 663))
 (.leaf (certNat% 664))))))
 (.branch 671
 (.branch 668
 (.branch 666
 (.leaf (certNat% 665))
 (.branch 667
 (.leaf (certNat% 666))
 (.leaf (certNat% 667))))
 (.branch 669
 (.leaf (certNat% 668))
 (.branch 670
 (.leaf (certNat% 669))
 (.leaf (certNat% 670)))))
 (.branch 674
 (.branch 672
 (.leaf (certNat% 671))
 (.branch 673
 (.leaf (certNat% 672))
 (.leaf (certNat% 673))))
 (.branch 676
 (.branch 675
 (.leaf (certNat% 674))
 (.leaf (certNat% 675)))
 (.branch 677
 (.leaf (certNat% 676))
 (.leaf (certNat% 677))))))))
 (.branch 704
 (.branch 691
 (.branch 684
 (.branch 681
 (.branch 679
 (.leaf (certNat% 678))
 (.branch 680
 (.leaf (certNat% 679))
 (.leaf (certNat% 680))))
 (.branch 682
 (.leaf (certNat% 681))
 (.branch 683
 (.leaf (certNat% 682))
 (.leaf (certNat% 683)))))
 (.branch 687
 (.branch 685
 (.leaf (certNat% 684))
 (.branch 686
 (.leaf (certNat% 685))
 (.leaf (certNat% 686))))
 (.branch 689
 (.branch 688
 (.leaf (certNat% 687))
 (.leaf (certNat% 688)))
 (.branch 690
 (.leaf (certNat% 689))
 (.leaf (certNat% 690))))))
 (.branch 697
 (.branch 694
 (.branch 692
 (.leaf (certNat% 691))
 (.branch 693
 (.leaf (certNat% 692))
 (.leaf (certNat% 693))))
 (.branch 695
 (.leaf (certNat% 694))
 (.branch 696
 (.leaf (certNat% 695))
 (.leaf (certNat% 696)))))
 (.branch 700
 (.branch 698
 (.leaf (certNat% 697))
 (.branch 699
 (.leaf (certNat% 698))
 (.leaf (certNat% 699))))
 (.branch 702
 (.branch 701
 (.leaf (certNat% 700))
 (.leaf (certNat% 701)))
 (.branch 703
 (.leaf (certNat% 702))
 (.leaf (certNat% 703)))))))
 (.branch 717
 (.branch 710
 (.branch 707
 (.branch 705
 (.leaf (certNat% 704))
 (.branch 706
 (.leaf (certNat% 705))
 (.leaf (certNat% 706))))
 (.branch 708
 (.leaf (certNat% 707))
 (.branch 709
 (.leaf (certNat% 708))
 (.leaf (certNat% 709)))))
 (.branch 713
 (.branch 711
 (.leaf (certNat% 710))
 (.branch 712
 (.leaf (certNat% 711))
 (.leaf (certNat% 712))))
 (.branch 715
 (.branch 714
 (.leaf (certNat% 713))
 (.leaf (certNat% 714)))
 (.branch 716
 (.leaf (certNat% 715))
 (.leaf (certNat% 716))))))
 (.branch 723
 (.branch 720
 (.branch 718
 (.leaf (certNat% 717))
 (.branch 719
 (.leaf (certNat% 718))
 (.leaf (certNat% 719))))
 (.branch 721
 (.leaf (certNat% 720))
 (.branch 722
 (.leaf (certNat% 721))
 (.leaf (certNat% 722)))))
 (.branch 726
 (.branch 724
 (.leaf (certNat% 723))
 (.branch 725
 (.leaf (certNat% 724))
 (.leaf (certNat% 725))))
 (.branch 728
 (.branch 727
 (.leaf (certNat% 726))
 (.leaf (certNat% 727)))
 (.branch 729
 (.leaf (certNat% 728))
 (.leaf (certNat% 729)))))))))
 (.branch 782
 (.branch 756
 (.branch 743
 (.branch 736
 (.branch 733
 (.branch 731
 (.leaf (certNat% 730))
 (.branch 732
 (.leaf (certNat% 731))
 (.leaf (certNat% 732))))
 (.branch 734
 (.leaf (certNat% 733))
 (.branch 735
 (.leaf (certNat% 734))
 (.leaf (certNat% 735)))))
 (.branch 739
 (.branch 737
 (.leaf (certNat% 736))
 (.branch 738
 (.leaf (certNat% 737))
 (.leaf (certNat% 738))))
 (.branch 741
 (.branch 740
 (.leaf (certNat% 739))
 (.leaf (certNat% 740)))
 (.branch 742
 (.leaf (certNat% 741))
 (.leaf (certNat% 742))))))
 (.branch 749
 (.branch 746
 (.branch 744
 (.leaf (certNat% 743))
 (.branch 745
 (.leaf (certNat% 744))
 (.leaf (certNat% 745))))
 (.branch 747
 (.leaf (certNat% 746))
 (.branch 748
 (.leaf (certNat% 747))
 (.leaf (certNat% 748)))))
 (.branch 752
 (.branch 750
 (.leaf (certNat% 749))
 (.branch 751
 (.leaf (certNat% 750))
 (.leaf (certNat% 751))))
 (.branch 754
 (.branch 753
 (.leaf (certNat% 752))
 (.leaf (certNat% 753)))
 (.branch 755
 (.leaf (certNat% 754))
 (.leaf (certNat% 755)))))))
 (.branch 769
 (.branch 762
 (.branch 759
 (.branch 757
 (.leaf (certNat% 756))
 (.branch 758
 (.leaf (certNat% 757))
 (.leaf (certNat% 758))))
 (.branch 760
 (.leaf (certNat% 759))
 (.branch 761
 (.leaf (certNat% 760))
 (.leaf (certNat% 761)))))
 (.branch 765
 (.branch 763
 (.leaf (certNat% 762))
 (.branch 764
 (.leaf (certNat% 763))
 (.leaf (certNat% 764))))
 (.branch 767
 (.branch 766
 (.leaf (certNat% 765))
 (.leaf (certNat% 766)))
 (.branch 768
 (.leaf (certNat% 767))
 (.leaf (certNat% 768))))))
 (.branch 775
 (.branch 772
 (.branch 770
 (.leaf (certNat% 769))
 (.branch 771
 (.leaf (certNat% 770))
 (.leaf (certNat% 771))))
 (.branch 773
 (.leaf (certNat% 772))
 (.branch 774
 (.leaf (certNat% 773))
 (.leaf (certNat% 774)))))
 (.branch 778
 (.branch 776
 (.leaf (certNat% 775))
 (.branch 777
 (.leaf (certNat% 776))
 (.leaf (certNat% 777))))
 (.branch 780
 (.branch 779
 (.leaf (certNat% 778))
 (.leaf (certNat% 779)))
 (.branch 781
 (.leaf (certNat% 780))
 (.leaf (certNat% 781))))))))
 (.branch 808
 (.branch 795
 (.branch 788
 (.branch 785
 (.branch 783
 (.leaf (certNat% 782))
 (.branch 784
 (.leaf (certNat% 783))
 (.leaf (certNat% 784))))
 (.branch 786
 (.leaf (certNat% 785))
 (.branch 787
 (.leaf (certNat% 786))
 (.leaf (certNat% 787)))))
 (.branch 791
 (.branch 789
 (.leaf (certNat% 788))
 (.branch 790
 (.leaf (certNat% 789))
 (.leaf (certNat% 790))))
 (.branch 793
 (.branch 792
 (.leaf (certNat% 791))
 (.leaf (certNat% 792)))
 (.branch 794
 (.leaf (certNat% 793))
 (.leaf (certNat% 794))))))
 (.branch 801
 (.branch 798
 (.branch 796
 (.leaf (certNat% 795))
 (.branch 797
 (.leaf (certNat% 796))
 (.leaf (certNat% 797))))
 (.branch 799
 (.leaf (certNat% 798))
 (.branch 800
 (.leaf (certNat% 799))
 (.leaf (certNat% 800)))))
 (.branch 804
 (.branch 802
 (.leaf (certNat% 801))
 (.branch 803
 (.leaf (certNat% 802))
 (.leaf (certNat% 803))))
 (.branch 806
 (.branch 805
 (.leaf (certNat% 804))
 (.leaf (certNat% 805)))
 (.branch 807
 (.leaf (certNat% 806))
 (.leaf (certNat% 807)))))))
 (.branch 821
 (.branch 814
 (.branch 811
 (.branch 809
 (.leaf (certNat% 808))
 (.branch 810
 (.leaf (certNat% 809))
 (.leaf (certNat% 810))))
 (.branch 812
 (.leaf (certNat% 811))
 (.branch 813
 (.leaf (certNat% 812))
 (.leaf (certNat% 813)))))
 (.branch 817
 (.branch 815
 (.leaf (certNat% 814))
 (.branch 816
 (.leaf (certNat% 815))
 (.leaf (certNat% 816))))
 (.branch 819
 (.branch 818
 (.leaf (certNat% 817))
 (.leaf (certNat% 818)))
 (.branch 820
 (.leaf (certNat% 819))
 (.leaf (certNat% 820))))))
 (.branch 828
 (.branch 824
 (.branch 822
 (.leaf (certNat% 821))
 (.branch 823
 (.leaf (certNat% 822))
 (.leaf (certNat% 823))))
 (.branch 826
 (.branch 825
 (.leaf (certNat% 824))
 (.leaf (certNat% 825)))
 (.branch 827
 (.leaf (certNat% 826))
 (.leaf (certNat% 827)))))
 (.branch 831
 (.branch 829
 (.leaf (certNat% 828))
 (.branch 830
 (.leaf (certNat% 829))
 (.leaf (certNat% 830))))
 (.branch 833
 (.branch 832
 (.leaf (certNat% 831))
 (.leaf (certNat% 832)))
 (.branch 834
 (.leaf (certNat% 833))
 (.leaf (certNat% 834))))))))))))
cert_rawLeaves_4 12
cert_leaves_3
cert_quota_3 0 5 0 0 0 0 0 0 3 6
cert_nodeTest_4 288 05
cert_nodeTest_sound_3 288 05
cert_leafTest_5 05
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0870

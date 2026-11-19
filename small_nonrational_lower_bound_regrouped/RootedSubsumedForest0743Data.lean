module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public meta import CertificateNumbers
public import RootedSixBase04GrowthCacheData
public import RootedSixBase04FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification
public import RootedSubsumedForest0743Packed000
public import RootedSubsumedForest0743Packed001
public import RootedSubsumedForest0743Packed002
public import RootedSubsumedForest0743Packed003
public import RootedSubsumedForest0743Packed004
public import RootedSubsumedForest0743Packed005
public import RootedSubsumedForest0743Packed006

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0743
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 2824
abbrev nodeCount : Nat := 43949
abbrev leafCount : Nat := 451
cert_widths_3 12 16 11 9
def blocks : Table PackedRawNatGrowth.Block :=
(.branch 150
 (.branch 50
 nodeBlocks000
 (.branch 100
 nodeBlocks001
 nodeBlocks002))
 (.branch 250
 (.branch 200
 nodeBlocks003
 nodeBlocks004)
 (.branch 300
 nodeBlocks005
 nodeBlocks006)))
def counterTable : Table Nat :=
(.branch 150
 (.branch 50
 nodeCounters000
 (.branch 100
 nodeCounters001
 nodeCounters002))
 (.branch 250
 (.branch 200
 nodeCounters003
 nodeCounters004)
 (.branch 300
 nodeCounters005
 nodeCounters006)))
cert_codes_3
cert_counters_3 55
cert_rawNodes_3
def leafTable : Table Nat :=
(.branch 225
 (.branch 112
 (.branch 56
 (.branch 28
 (.branch 14
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf (certNat% 0))
 (.branch 2
 (.leaf (certNat% 1))
 (.leaf (certNat% 2))))
 (.branch 5
 (.branch 4
 (.leaf (certNat% 3))
 (.leaf (certNat% 4)))
 (.branch 6
 (.leaf (certNat% 5))
 (.leaf (certNat% 6)))))
 (.branch 10
 (.branch 8
 (.leaf (certNat% 7))
 (.branch 9
 (.leaf (certNat% 8))
 (.leaf (certNat% 9))))
 (.branch 12
 (.branch 11
 (.leaf (certNat% 10))
 (.leaf (certNat% 11)))
 (.branch 13
 (.leaf (certNat% 12))
 (.leaf (certNat% 13))))))
 (.branch 21
 (.branch 17
 (.branch 15
 (.leaf (certNat% 14))
 (.branch 16
 (.leaf (certNat% 15))
 (.leaf (certNat% 16))))
 (.branch 19
 (.branch 18
 (.leaf (certNat% 17))
 (.leaf (certNat% 18)))
 (.branch 20
 (.leaf (certNat% 19))
 (.leaf (certNat% 20)))))
 (.branch 24
 (.branch 22
 (.leaf (certNat% 21))
 (.branch 23
 (.leaf (certNat% 22))
 (.leaf (certNat% 23))))
 (.branch 26
 (.branch 25
 (.leaf (certNat% 24))
 (.leaf (certNat% 25)))
 (.branch 27
 (.leaf (certNat% 26))
 (.leaf (certNat% 27)))))))
 (.branch 42
 (.branch 35
 (.branch 31
 (.branch 29
 (.leaf (certNat% 28))
 (.branch 30
 (.leaf (certNat% 29))
 (.leaf (certNat% 30))))
 (.branch 33
 (.branch 32
 (.leaf (certNat% 31))
 (.leaf (certNat% 32)))
 (.branch 34
 (.leaf (certNat% 33))
 (.leaf (certNat% 34)))))
 (.branch 38
 (.branch 36
 (.leaf (certNat% 35))
 (.branch 37
 (.leaf (certNat% 36))
 (.leaf (certNat% 37))))
 (.branch 40
 (.branch 39
 (.leaf (certNat% 38))
 (.leaf (certNat% 39)))
 (.branch 41
 (.leaf (certNat% 40))
 (.leaf (certNat% 41))))))
 (.branch 49
 (.branch 45
 (.branch 43
 (.leaf (certNat% 42))
 (.branch 44
 (.leaf (certNat% 43))
 (.leaf (certNat% 44))))
 (.branch 47
 (.branch 46
 (.leaf (certNat% 45))
 (.leaf (certNat% 46)))
 (.branch 48
 (.leaf (certNat% 47))
 (.leaf (certNat% 48)))))
 (.branch 52
 (.branch 50
 (.leaf (certNat% 49))
 (.branch 51
 (.leaf (certNat% 50))
 (.leaf (certNat% 51))))
 (.branch 54
 (.branch 53
 (.leaf (certNat% 52))
 (.leaf (certNat% 53)))
 (.branch 55
 (.leaf (certNat% 54))
 (.leaf (certNat% 55))))))))
 (.branch 84
 (.branch 70
 (.branch 63
 (.branch 59
 (.branch 57
 (.leaf (certNat% 56))
 (.branch 58
 (.leaf (certNat% 57))
 (.leaf (certNat% 58))))
 (.branch 61
 (.branch 60
 (.leaf (certNat% 59))
 (.leaf (certNat% 60)))
 (.branch 62
 (.leaf (certNat% 61))
 (.leaf (certNat% 62)))))
 (.branch 66
 (.branch 64
 (.leaf (certNat% 63))
 (.branch 65
 (.leaf (certNat% 64))
 (.leaf (certNat% 65))))
 (.branch 68
 (.branch 67
 (.leaf (certNat% 66))
 (.leaf (certNat% 67)))
 (.branch 69
 (.leaf (certNat% 68))
 (.leaf (certNat% 69))))))
 (.branch 77
 (.branch 73
 (.branch 71
 (.leaf (certNat% 70))
 (.branch 72
 (.leaf (certNat% 71))
 (.leaf (certNat% 72))))
 (.branch 75
 (.branch 74
 (.leaf (certNat% 73))
 (.leaf (certNat% 74)))
 (.branch 76
 (.leaf (certNat% 75))
 (.leaf (certNat% 76)))))
 (.branch 80
 (.branch 78
 (.leaf (certNat% 77))
 (.branch 79
 (.leaf (certNat% 78))
 (.leaf (certNat% 79))))
 (.branch 82
 (.branch 81
 (.leaf (certNat% 80))
 (.leaf (certNat% 81)))
 (.branch 83
 (.leaf (certNat% 82))
 (.leaf (certNat% 83)))))))
 (.branch 98
 (.branch 91
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
 (.leaf (certNat% 90)))))
 (.branch 94
 (.branch 92
 (.leaf (certNat% 91))
 (.branch 93
 (.leaf (certNat% 92))
 (.leaf (certNat% 93))))
 (.branch 96
 (.branch 95
 (.leaf (certNat% 94))
 (.leaf (certNat% 95)))
 (.branch 97
 (.leaf (certNat% 96))
 (.leaf (certNat% 97))))))
 (.branch 105
 (.branch 101
 (.branch 99
 (.leaf (certNat% 98))
 (.branch 100
 (.leaf (certNat% 99))
 (.leaf (certNat% 100))))
 (.branch 103
 (.branch 102
 (.leaf (certNat% 101))
 (.leaf (certNat% 102)))
 (.branch 104
 (.leaf (certNat% 103))
 (.leaf (certNat% 104)))))
 (.branch 108
 (.branch 106
 (.leaf (certNat% 105))
 (.branch 107
 (.leaf (certNat% 106))
 (.leaf (certNat% 107))))
 (.branch 110
 (.branch 109
 (.leaf (certNat% 108))
 (.leaf (certNat% 109)))
 (.branch 111
 (.leaf (certNat% 110))
 (.leaf (certNat% 111)))))))))
 (.branch 168
 (.branch 140
 (.branch 126
 (.branch 119
 (.branch 115
 (.branch 113
 (.leaf (certNat% 112))
 (.branch 114
 (.leaf (certNat% 113))
 (.leaf (certNat% 114))))
 (.branch 117
 (.branch 116
 (.leaf (certNat% 115))
 (.leaf (certNat% 116)))
 (.branch 118
 (.leaf (certNat% 117))
 (.leaf (certNat% 118)))))
 (.branch 122
 (.branch 120
 (.leaf (certNat% 119))
 (.branch 121
 (.leaf (certNat% 120))
 (.leaf (certNat% 121))))
 (.branch 124
 (.branch 123
 (.leaf (certNat% 122))
 (.leaf (certNat% 123)))
 (.branch 125
 (.leaf (certNat% 124))
 (.leaf (certNat% 125))))))
 (.branch 133
 (.branch 129
 (.branch 127
 (.leaf (certNat% 126))
 (.branch 128
 (.leaf (certNat% 127))
 (.leaf (certNat% 128))))
 (.branch 131
 (.branch 130
 (.leaf (certNat% 129))
 (.leaf (certNat% 130)))
 (.branch 132
 (.leaf (certNat% 131))
 (.leaf (certNat% 132)))))
 (.branch 136
 (.branch 134
 (.leaf (certNat% 133))
 (.branch 135
 (.leaf (certNat% 134))
 (.leaf (certNat% 135))))
 (.branch 138
 (.branch 137
 (.leaf (certNat% 136))
 (.leaf (certNat% 137)))
 (.branch 139
 (.leaf (certNat% 138))
 (.leaf (certNat% 139)))))))
 (.branch 154
 (.branch 147
 (.branch 143
 (.branch 141
 (.leaf (certNat% 140))
 (.branch 142
 (.leaf (certNat% 141))
 (.leaf (certNat% 142))))
 (.branch 145
 (.branch 144
 (.leaf (certNat% 143))
 (.leaf (certNat% 144)))
 (.branch 146
 (.leaf (certNat% 145))
 (.leaf (certNat% 146)))))
 (.branch 150
 (.branch 148
 (.leaf (certNat% 147))
 (.branch 149
 (.leaf (certNat% 148))
 (.leaf (certNat% 149))))
 (.branch 152
 (.branch 151
 (.leaf (certNat% 150))
 (.leaf (certNat% 151)))
 (.branch 153
 (.leaf (certNat% 152))
 (.leaf (certNat% 153))))))
 (.branch 161
 (.branch 157
 (.branch 155
 (.leaf (certNat% 154))
 (.branch 156
 (.leaf (certNat% 155))
 (.leaf (certNat% 156))))
 (.branch 159
 (.branch 158
 (.leaf (certNat% 157))
 (.leaf (certNat% 158)))
 (.branch 160
 (.leaf (certNat% 159))
 (.leaf (certNat% 160)))))
 (.branch 164
 (.branch 162
 (.leaf (certNat% 161))
 (.branch 163
 (.leaf (certNat% 162))
 (.leaf (certNat% 163))))
 (.branch 166
 (.branch 165
 (.leaf (certNat% 164))
 (.leaf (certNat% 165)))
 (.branch 167
 (.leaf (certNat% 166))
 (.leaf (certNat% 167))))))))
 (.branch 196
 (.branch 182
 (.branch 175
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
 (.leaf (certNat% 181))))))
 (.branch 189
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
 (.leaf (certNat% 188)))))
 (.branch 192
 (.branch 190
 (.leaf (certNat% 189))
 (.branch 191
 (.leaf (certNat% 190))
 (.leaf (certNat% 191))))
 (.branch 194
 (.branch 193
 (.leaf (certNat% 192))
 (.leaf (certNat% 193)))
 (.branch 195
 (.leaf (certNat% 194))
 (.leaf (certNat% 195)))))))
 (.branch 210
 (.branch 203
 (.branch 199
 (.branch 197
 (.leaf (certNat% 196))
 (.branch 198
 (.leaf (certNat% 197))
 (.leaf (certNat% 198))))
 (.branch 201
 (.branch 200
 (.leaf (certNat% 199))
 (.leaf (certNat% 200)))
 (.branch 202
 (.leaf (certNat% 201))
 (.leaf (certNat% 202)))))
 (.branch 206
 (.branch 204
 (.leaf (certNat% 203))
 (.branch 205
 (.leaf (certNat% 204))
 (.leaf (certNat% 205))))
 (.branch 208
 (.branch 207
 (.leaf (certNat% 206))
 (.leaf (certNat% 207)))
 (.branch 209
 (.leaf (certNat% 208))
 (.leaf (certNat% 209))))))
 (.branch 217
 (.branch 213
 (.branch 211
 (.leaf (certNat% 210))
 (.branch 212
 (.leaf (certNat% 211))
 (.leaf (certNat% 212))))
 (.branch 215
 (.branch 214
 (.leaf (certNat% 213))
 (.leaf (certNat% 214)))
 (.branch 216
 (.leaf (certNat% 215))
 (.leaf (certNat% 216)))))
 (.branch 221
 (.branch 219
 (.branch 218
 (.leaf (certNat% 217))
 (.leaf (certNat% 218)))
 (.branch 220
 (.leaf (certNat% 219))
 (.leaf (certNat% 220))))
 (.branch 223
 (.branch 222
 (.leaf (certNat% 221))
 (.leaf (certNat% 222)))
 (.branch 224
 (.leaf (certNat% 223))
 (.leaf (certNat% 224))))))))))
 (.branch 338
 (.branch 281
 (.branch 253
 (.branch 239
 (.branch 232
 (.branch 228
 (.branch 226
 (.leaf (certNat% 225))
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
 (.branch 235
 (.branch 233
 (.leaf (certNat% 232))
 (.branch 234
 (.leaf (certNat% 233))
 (.leaf (certNat% 234))))
 (.branch 237
 (.branch 236
 (.leaf (certNat% 235))
 (.leaf (certNat% 236)))
 (.branch 238
 (.leaf (certNat% 237))
 (.leaf (certNat% 238))))))
 (.branch 246
 (.branch 242
 (.branch 240
 (.leaf (certNat% 239))
 (.branch 241
 (.leaf (certNat% 240))
 (.leaf (certNat% 241))))
 (.branch 244
 (.branch 243
 (.leaf (certNat% 242))
 (.leaf (certNat% 243)))
 (.branch 245
 (.leaf (certNat% 244))
 (.leaf (certNat% 245)))))
 (.branch 249
 (.branch 247
 (.leaf (certNat% 246))
 (.branch 248
 (.leaf (certNat% 247))
 (.leaf (certNat% 248))))
 (.branch 251
 (.branch 250
 (.leaf (certNat% 249))
 (.leaf (certNat% 250)))
 (.branch 252
 (.leaf (certNat% 251))
 (.leaf (certNat% 252)))))))
 (.branch 267
 (.branch 260
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
 (.leaf (certNat% 259)))))
 (.branch 263
 (.branch 261
 (.leaf (certNat% 260))
 (.branch 262
 (.leaf (certNat% 261))
 (.leaf (certNat% 262))))
 (.branch 265
 (.branch 264
 (.leaf (certNat% 263))
 (.leaf (certNat% 264)))
 (.branch 266
 (.leaf (certNat% 265))
 (.leaf (certNat% 266))))))
 (.branch 274
 (.branch 270
 (.branch 268
 (.leaf (certNat% 267))
 (.branch 269
 (.leaf (certNat% 268))
 (.leaf (certNat% 269))))
 (.branch 272
 (.branch 271
 (.leaf (certNat% 270))
 (.leaf (certNat% 271)))
 (.branch 273
 (.leaf (certNat% 272))
 (.leaf (certNat% 273)))))
 (.branch 277
 (.branch 275
 (.leaf (certNat% 274))
 (.branch 276
 (.leaf (certNat% 275))
 (.leaf (certNat% 276))))
 (.branch 279
 (.branch 278
 (.leaf (certNat% 277))
 (.leaf (certNat% 278)))
 (.branch 280
 (.leaf (certNat% 279))
 (.leaf (certNat% 280))))))))
 (.branch 309
 (.branch 295
 (.branch 288
 (.branch 284
 (.branch 282
 (.leaf (certNat% 281))
 (.branch 283
 (.leaf (certNat% 282))
 (.leaf (certNat% 283))))
 (.branch 286
 (.branch 285
 (.leaf (certNat% 284))
 (.leaf (certNat% 285)))
 (.branch 287
 (.leaf (certNat% 286))
 (.leaf (certNat% 287)))))
 (.branch 291
 (.branch 289
 (.leaf (certNat% 288))
 (.branch 290
 (.leaf (certNat% 289))
 (.leaf (certNat% 290))))
 (.branch 293
 (.branch 292
 (.leaf (certNat% 291))
 (.leaf (certNat% 292)))
 (.branch 294
 (.leaf (certNat% 293))
 (.leaf (certNat% 294))))))
 (.branch 302
 (.branch 298
 (.branch 296
 (.leaf (certNat% 295))
 (.branch 297
 (.leaf (certNat% 296))
 (.leaf (certNat% 297))))
 (.branch 300
 (.branch 299
 (.leaf (certNat% 298))
 (.leaf (certNat% 299)))
 (.branch 301
 (.leaf (certNat% 300))
 (.leaf (certNat% 301)))))
 (.branch 305
 (.branch 303
 (.leaf (certNat% 302))
 (.branch 304
 (.leaf (certNat% 303))
 (.leaf (certNat% 304))))
 (.branch 307
 (.branch 306
 (.leaf (certNat% 305))
 (.leaf (certNat% 306)))
 (.branch 308
 (.leaf (certNat% 307))
 (.leaf (certNat% 308)))))))
 (.branch 323
 (.branch 316
 (.branch 312
 (.branch 310
 (.leaf (certNat% 309))
 (.branch 311
 (.leaf (certNat% 310))
 (.leaf (certNat% 311))))
 (.branch 314
 (.branch 313
 (.leaf (certNat% 312))
 (.leaf (certNat% 313)))
 (.branch 315
 (.leaf (certNat% 314))
 (.leaf (certNat% 315)))))
 (.branch 319
 (.branch 317
 (.leaf (certNat% 316))
 (.branch 318
 (.leaf (certNat% 317))
 (.leaf (certNat% 318))))
 (.branch 321
 (.branch 320
 (.leaf (certNat% 319))
 (.leaf (certNat% 320)))
 (.branch 322
 (.leaf (certNat% 321))
 (.leaf (certNat% 322))))))
 (.branch 330
 (.branch 326
 (.branch 324
 (.leaf (certNat% 323))
 (.branch 325
 (.leaf (certNat% 324))
 (.leaf (certNat% 325))))
 (.branch 328
 (.branch 327
 (.leaf (certNat% 326))
 (.leaf (certNat% 327)))
 (.branch 329
 (.leaf (certNat% 328))
 (.leaf (certNat% 329)))))
 (.branch 334
 (.branch 332
 (.branch 331
 (.leaf (certNat% 330))
 (.leaf (certNat% 331)))
 (.branch 333
 (.leaf (certNat% 332))
 (.leaf (certNat% 333))))
 (.branch 336
 (.branch 335
 (.leaf (certNat% 334))
 (.leaf (certNat% 335)))
 (.branch 337
 (.leaf (certNat% 336))
 (.leaf (certNat% 337)))))))))
 (.branch 394
 (.branch 366
 (.branch 352
 (.branch 345
 (.branch 341
 (.branch 339
 (.leaf (certNat% 338))
 (.branch 340
 (.leaf (certNat% 339))
 (.leaf (certNat% 340))))
 (.branch 343
 (.branch 342
 (.leaf (certNat% 341))
 (.leaf (certNat% 342)))
 (.branch 344
 (.leaf (certNat% 343))
 (.leaf (certNat% 344)))))
 (.branch 348
 (.branch 346
 (.leaf (certNat% 345))
 (.branch 347
 (.leaf (certNat% 346))
 (.leaf (certNat% 347))))
 (.branch 350
 (.branch 349
 (.leaf (certNat% 348))
 (.leaf (certNat% 349)))
 (.branch 351
 (.leaf (certNat% 350))
 (.leaf (certNat% 351))))))
 (.branch 359
 (.branch 355
 (.branch 353
 (.leaf (certNat% 352))
 (.branch 354
 (.leaf (certNat% 353))
 (.leaf (certNat% 354))))
 (.branch 357
 (.branch 356
 (.leaf (certNat% 355))
 (.leaf (certNat% 356)))
 (.branch 358
 (.leaf (certNat% 357))
 (.leaf (certNat% 358)))))
 (.branch 362
 (.branch 360
 (.leaf (certNat% 359))
 (.branch 361
 (.leaf (certNat% 360))
 (.leaf (certNat% 361))))
 (.branch 364
 (.branch 363
 (.leaf (certNat% 362))
 (.leaf (certNat% 363)))
 (.branch 365
 (.leaf (certNat% 364))
 (.leaf (certNat% 365)))))))
 (.branch 380
 (.branch 373
 (.branch 369
 (.branch 367
 (.leaf (certNat% 366))
 (.branch 368
 (.leaf (certNat% 367))
 (.leaf (certNat% 368))))
 (.branch 371
 (.branch 370
 (.leaf (certNat% 369))
 (.leaf (certNat% 370)))
 (.branch 372
 (.leaf (certNat% 371))
 (.leaf (certNat% 372)))))
 (.branch 376
 (.branch 374
 (.leaf (certNat% 373))
 (.branch 375
 (.leaf (certNat% 374))
 (.leaf (certNat% 375))))
 (.branch 378
 (.branch 377
 (.leaf (certNat% 376))
 (.leaf (certNat% 377)))
 (.branch 379
 (.leaf (certNat% 378))
 (.leaf (certNat% 379))))))
 (.branch 387
 (.branch 383
 (.branch 381
 (.leaf (certNat% 380))
 (.branch 382
 (.leaf (certNat% 381))
 (.leaf (certNat% 382))))
 (.branch 385
 (.branch 384
 (.leaf (certNat% 383))
 (.leaf (certNat% 384)))
 (.branch 386
 (.leaf (certNat% 385))
 (.leaf (certNat% 386)))))
 (.branch 390
 (.branch 388
 (.leaf (certNat% 387))
 (.branch 389
 (.leaf (certNat% 388))
 (.leaf (certNat% 389))))
 (.branch 392
 (.branch 391
 (.leaf (certNat% 390))
 (.leaf (certNat% 391)))
 (.branch 393
 (.leaf (certNat% 392))
 (.leaf (certNat% 393))))))))
 (.branch 422
 (.branch 408
 (.branch 401
 (.branch 397
 (.branch 395
 (.leaf (certNat% 394))
 (.branch 396
 (.leaf (certNat% 395))
 (.leaf (certNat% 396))))
 (.branch 399
 (.branch 398
 (.leaf (certNat% 397))
 (.leaf (certNat% 398)))
 (.branch 400
 (.leaf (certNat% 399))
 (.leaf (certNat% 400)))))
 (.branch 404
 (.branch 402
 (.leaf (certNat% 401))
 (.branch 403
 (.leaf (certNat% 402))
 (.leaf (certNat% 403))))
 (.branch 406
 (.branch 405
 (.leaf (certNat% 404))
 (.leaf (certNat% 405)))
 (.branch 407
 (.leaf (certNat% 406))
 (.leaf (certNat% 407))))))
 (.branch 415
 (.branch 411
 (.branch 409
 (.leaf (certNat% 408))
 (.branch 410
 (.leaf (certNat% 409))
 (.leaf (certNat% 410))))
 (.branch 413
 (.branch 412
 (.leaf (certNat% 411))
 (.leaf (certNat% 412)))
 (.branch 414
 (.leaf (certNat% 413))
 (.leaf (certNat% 414)))))
 (.branch 418
 (.branch 416
 (.leaf (certNat% 415))
 (.branch 417
 (.leaf (certNat% 416))
 (.leaf (certNat% 417))))
 (.branch 420
 (.branch 419
 (.leaf (certNat% 418))
 (.leaf (certNat% 419)))
 (.branch 421
 (.leaf (certNat% 420))
 (.leaf (certNat% 421)))))))
 (.branch 436
 (.branch 429
 (.branch 425
 (.branch 423
 (.leaf (certNat% 422))
 (.branch 424
 (.leaf (certNat% 423))
 (.leaf (certNat% 424))))
 (.branch 427
 (.branch 426
 (.leaf (certNat% 425))
 (.leaf (certNat% 426)))
 (.branch 428
 (.leaf (certNat% 427))
 (.leaf (certNat% 428)))))
 (.branch 432
 (.branch 430
 (.leaf (certNat% 429))
 (.branch 431
 (.leaf (certNat% 430))
 (.leaf (certNat% 431))))
 (.branch 434
 (.branch 433
 (.leaf (certNat% 432))
 (.leaf (certNat% 433)))
 (.branch 435
 (.leaf (certNat% 434))
 (.leaf (certNat% 435))))))
 (.branch 443
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
 (.leaf (certNat% 442)))))
 (.branch 447
 (.branch 445
 (.branch 444
 (.leaf (certNat% 443))
 (.leaf (certNat% 444)))
 (.branch 446
 (.leaf (certNat% 445))
 (.leaf (certNat% 446))))
 (.branch 449
 (.branch 448
 (.leaf (certNat% 447))
 (.leaf (certNat% 448)))
 (.branch 450
 (.leaf (certNat% 449))
 (.leaf (certNat% 450)))))))))))
cert_rawLeaves_4 12
cert_leaves_3
cert_quota_3 0 4 0 0 0 0 0 0 4 5
cert_nodeTest_5 1152 04
cert_nodeTest_sound_4 1152 04
cert_leafTest_4 04
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0743

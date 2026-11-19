module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public meta import CertificateNumbers
public import RootedSixBase01GrowthCacheData
public import RootedSixBase01FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification
public import RootedSubsumedForest0353Packed000
public import RootedSubsumedForest0353Packed001
public import RootedSubsumedForest0353Packed002
public import RootedSubsumedForest0353Packed003
public import RootedSubsumedForest0353Packed004
public import RootedSubsumedForest0353Packed005
public import RootedSubsumedForest0353Packed006
public import RootedSubsumedForest0353Packed007

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0353
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 15246
abbrev nodeCount : Nat := 47342
abbrev leafCount : Nat := 756
cert_widths_3 14 16 6 10
def blocks : Table PackedRawNatGrowth.Block :=
(.branch 200
 (.branch 100
 (.branch 50
 nodeBlocks000
 nodeBlocks001)
 (.branch 150
 nodeBlocks002
 nodeBlocks003))
 (.branch 300
 (.branch 250
 nodeBlocks004
 nodeBlocks005)
 (.branch 350
 nodeBlocks006
 nodeBlocks007)))
def counterTable : Table Nat :=
(.branch 200
 (.branch 100
 (.branch 50
 nodeCounters000
 nodeCounters001)
 (.branch 150
 nodeCounters002
 nodeCounters003))
 (.branch 300
 (.branch 250
 nodeCounters004
 nodeCounters005)
 (.branch 350
 nodeCounters006
 nodeCounters007)))
cert_codes_3
cert_counters_3 55
cert_rawNodes_3
def leafTable : Table Nat :=
(.branch 378
 (.branch 189
 (.branch 94
 (.branch 47
 (.branch 23
 (.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf (certNat% 0))
 (.leaf (certNat% 1)))
 (.branch 3
 (.leaf (certNat% 2))
 (.branch 4
 (.leaf (certNat% 3))
 (.leaf (certNat% 4)))))
 (.branch 8
 (.branch 6
 (.leaf (certNat% 5))
 (.branch 7
 (.leaf (certNat% 6))
 (.leaf (certNat% 7))))
 (.branch 9
 (.leaf (certNat% 8))
 (.branch 10
 (.leaf (certNat% 9))
 (.leaf (certNat% 10))))))
 (.branch 17
 (.branch 14
 (.branch 12
 (.leaf (certNat% 11))
 (.branch 13
 (.leaf (certNat% 12))
 (.leaf (certNat% 13))))
 (.branch 15
 (.leaf (certNat% 14))
 (.branch 16
 (.leaf (certNat% 15))
 (.leaf (certNat% 16)))))
 (.branch 20
 (.branch 18
 (.leaf (certNat% 17))
 (.branch 19
 (.leaf (certNat% 18))
 (.leaf (certNat% 19))))
 (.branch 21
 (.leaf (certNat% 20))
 (.branch 22
 (.leaf (certNat% 21))
 (.leaf (certNat% 22)))))))
 (.branch 35
 (.branch 29
 (.branch 26
 (.branch 24
 (.leaf (certNat% 23))
 (.branch 25
 (.leaf (certNat% 24))
 (.leaf (certNat% 25))))
 (.branch 27
 (.leaf (certNat% 26))
 (.branch 28
 (.leaf (certNat% 27))
 (.leaf (certNat% 28)))))
 (.branch 32
 (.branch 30
 (.leaf (certNat% 29))
 (.branch 31
 (.leaf (certNat% 30))
 (.leaf (certNat% 31))))
 (.branch 33
 (.leaf (certNat% 32))
 (.branch 34
 (.leaf (certNat% 33))
 (.leaf (certNat% 34))))))
 (.branch 41
 (.branch 38
 (.branch 36
 (.leaf (certNat% 35))
 (.branch 37
 (.leaf (certNat% 36))
 (.leaf (certNat% 37))))
 (.branch 39
 (.leaf (certNat% 38))
 (.branch 40
 (.leaf (certNat% 39))
 (.leaf (certNat% 40)))))
 (.branch 44
 (.branch 42
 (.leaf (certNat% 41))
 (.branch 43
 (.leaf (certNat% 42))
 (.leaf (certNat% 43))))
 (.branch 45
 (.leaf (certNat% 44))
 (.branch 46
 (.leaf (certNat% 45))
 (.leaf (certNat% 46))))))))
 (.branch 70
 (.branch 58
 (.branch 52
 (.branch 49
 (.branch 48
 (.leaf (certNat% 47))
 (.leaf (certNat% 48)))
 (.branch 50
 (.leaf (certNat% 49))
 (.branch 51
 (.leaf (certNat% 50))
 (.leaf (certNat% 51)))))
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
 (.leaf (certNat% 57))))))
 (.branch 64
 (.branch 61
 (.branch 59
 (.leaf (certNat% 58))
 (.branch 60
 (.leaf (certNat% 59))
 (.leaf (certNat% 60))))
 (.branch 62
 (.leaf (certNat% 61))
 (.branch 63
 (.leaf (certNat% 62))
 (.leaf (certNat% 63)))))
 (.branch 67
 (.branch 65
 (.leaf (certNat% 64))
 (.branch 66
 (.leaf (certNat% 65))
 (.leaf (certNat% 66))))
 (.branch 68
 (.leaf (certNat% 67))
 (.branch 69
 (.leaf (certNat% 68))
 (.leaf (certNat% 69)))))))
 (.branch 82
 (.branch 76
 (.branch 73
 (.branch 71
 (.leaf (certNat% 70))
 (.branch 72
 (.leaf (certNat% 71))
 (.leaf (certNat% 72))))
 (.branch 74
 (.leaf (certNat% 73))
 (.branch 75
 (.leaf (certNat% 74))
 (.leaf (certNat% 75)))))
 (.branch 79
 (.branch 77
 (.leaf (certNat% 76))
 (.branch 78
 (.leaf (certNat% 77))
 (.leaf (certNat% 78))))
 (.branch 80
 (.leaf (certNat% 79))
 (.branch 81
 (.leaf (certNat% 80))
 (.leaf (certNat% 81))))))
 (.branch 88
 (.branch 85
 (.branch 83
 (.leaf (certNat% 82))
 (.branch 84
 (.leaf (certNat% 83))
 (.leaf (certNat% 84))))
 (.branch 86
 (.leaf (certNat% 85))
 (.branch 87
 (.leaf (certNat% 86))
 (.leaf (certNat% 87)))))
 (.branch 91
 (.branch 89
 (.leaf (certNat% 88))
 (.branch 90
 (.leaf (certNat% 89))
 (.leaf (certNat% 90))))
 (.branch 92
 (.leaf (certNat% 91))
 (.branch 93
 (.leaf (certNat% 92))
 (.leaf (certNat% 93)))))))))
 (.branch 141
 (.branch 117
 (.branch 105
 (.branch 99
 (.branch 96
 (.branch 95
 (.leaf (certNat% 94))
 (.leaf (certNat% 95)))
 (.branch 97
 (.leaf (certNat% 96))
 (.branch 98
 (.leaf (certNat% 97))
 (.leaf (certNat% 98)))))
 (.branch 102
 (.branch 100
 (.leaf (certNat% 99))
 (.branch 101
 (.leaf (certNat% 100))
 (.leaf (certNat% 101))))
 (.branch 103
 (.leaf (certNat% 102))
 (.branch 104
 (.leaf (certNat% 103))
 (.leaf (certNat% 104))))))
 (.branch 111
 (.branch 108
 (.branch 106
 (.leaf (certNat% 105))
 (.branch 107
 (.leaf (certNat% 106))
 (.leaf (certNat% 107))))
 (.branch 109
 (.leaf (certNat% 108))
 (.branch 110
 (.leaf (certNat% 109))
 (.leaf (certNat% 110)))))
 (.branch 114
 (.branch 112
 (.leaf (certNat% 111))
 (.branch 113
 (.leaf (certNat% 112))
 (.leaf (certNat% 113))))
 (.branch 115
 (.leaf (certNat% 114))
 (.branch 116
 (.leaf (certNat% 115))
 (.leaf (certNat% 116)))))))
 (.branch 129
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
 (.branch 127
 (.leaf (certNat% 126))
 (.branch 128
 (.leaf (certNat% 127))
 (.leaf (certNat% 128))))))
 (.branch 135
 (.branch 132
 (.branch 130
 (.leaf (certNat% 129))
 (.branch 131
 (.leaf (certNat% 130))
 (.leaf (certNat% 131))))
 (.branch 133
 (.leaf (certNat% 132))
 (.branch 134
 (.leaf (certNat% 133))
 (.leaf (certNat% 134)))))
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
 (.leaf (certNat% 140))))))))
 (.branch 165
 (.branch 153
 (.branch 147
 (.branch 144
 (.branch 142
 (.leaf (certNat% 141))
 (.branch 143
 (.leaf (certNat% 142))
 (.leaf (certNat% 143))))
 (.branch 145
 (.leaf (certNat% 144))
 (.branch 146
 (.leaf (certNat% 145))
 (.leaf (certNat% 146)))))
 (.branch 150
 (.branch 148
 (.leaf (certNat% 147))
 (.branch 149
 (.leaf (certNat% 148))
 (.leaf (certNat% 149))))
 (.branch 151
 (.leaf (certNat% 150))
 (.branch 152
 (.leaf (certNat% 151))
 (.leaf (certNat% 152))))))
 (.branch 159
 (.branch 156
 (.branch 154
 (.leaf (certNat% 153))
 (.branch 155
 (.leaf (certNat% 154))
 (.leaf (certNat% 155))))
 (.branch 157
 (.leaf (certNat% 156))
 (.branch 158
 (.leaf (certNat% 157))
 (.leaf (certNat% 158)))))
 (.branch 162
 (.branch 160
 (.leaf (certNat% 159))
 (.branch 161
 (.leaf (certNat% 160))
 (.leaf (certNat% 161))))
 (.branch 163
 (.leaf (certNat% 162))
 (.branch 164
 (.leaf (certNat% 163))
 (.leaf (certNat% 164)))))))
 (.branch 177
 (.branch 171
 (.branch 168
 (.branch 166
 (.leaf (certNat% 165))
 (.branch 167
 (.leaf (certNat% 166))
 (.leaf (certNat% 167))))
 (.branch 169
 (.leaf (certNat% 168))
 (.branch 170
 (.leaf (certNat% 169))
 (.leaf (certNat% 170)))))
 (.branch 174
 (.branch 172
 (.leaf (certNat% 171))
 (.branch 173
 (.leaf (certNat% 172))
 (.leaf (certNat% 173))))
 (.branch 175
 (.leaf (certNat% 174))
 (.branch 176
 (.leaf (certNat% 175))
 (.leaf (certNat% 176))))))
 (.branch 183
 (.branch 180
 (.branch 178
 (.leaf (certNat% 177))
 (.branch 179
 (.leaf (certNat% 178))
 (.leaf (certNat% 179))))
 (.branch 181
 (.leaf (certNat% 180))
 (.branch 182
 (.leaf (certNat% 181))
 (.leaf (certNat% 182)))))
 (.branch 186
 (.branch 184
 (.leaf (certNat% 183))
 (.branch 185
 (.leaf (certNat% 184))
 (.leaf (certNat% 185))))
 (.branch 187
 (.leaf (certNat% 186))
 (.branch 188
 (.leaf (certNat% 187))
 (.leaf (certNat% 188))))))))))
 (.branch 283
 (.branch 236
 (.branch 212
 (.branch 200
 (.branch 194
 (.branch 191
 (.branch 190
 (.leaf (certNat% 189))
 (.leaf (certNat% 190)))
 (.branch 192
 (.leaf (certNat% 191))
 (.branch 193
 (.leaf (certNat% 192))
 (.leaf (certNat% 193)))))
 (.branch 197
 (.branch 195
 (.leaf (certNat% 194))
 (.branch 196
 (.leaf (certNat% 195))
 (.leaf (certNat% 196))))
 (.branch 198
 (.leaf (certNat% 197))
 (.branch 199
 (.leaf (certNat% 198))
 (.leaf (certNat% 199))))))
 (.branch 206
 (.branch 203
 (.branch 201
 (.leaf (certNat% 200))
 (.branch 202
 (.leaf (certNat% 201))
 (.leaf (certNat% 202))))
 (.branch 204
 (.leaf (certNat% 203))
 (.branch 205
 (.leaf (certNat% 204))
 (.leaf (certNat% 205)))))
 (.branch 209
 (.branch 207
 (.leaf (certNat% 206))
 (.branch 208
 (.leaf (certNat% 207))
 (.leaf (certNat% 208))))
 (.branch 210
 (.leaf (certNat% 209))
 (.branch 211
 (.leaf (certNat% 210))
 (.leaf (certNat% 211)))))))
 (.branch 224
 (.branch 218
 (.branch 215
 (.branch 213
 (.leaf (certNat% 212))
 (.branch 214
 (.leaf (certNat% 213))
 (.leaf (certNat% 214))))
 (.branch 216
 (.leaf (certNat% 215))
 (.branch 217
 (.leaf (certNat% 216))
 (.leaf (certNat% 217)))))
 (.branch 221
 (.branch 219
 (.leaf (certNat% 218))
 (.branch 220
 (.leaf (certNat% 219))
 (.leaf (certNat% 220))))
 (.branch 222
 (.leaf (certNat% 221))
 (.branch 223
 (.leaf (certNat% 222))
 (.leaf (certNat% 223))))))
 (.branch 230
 (.branch 227
 (.branch 225
 (.leaf (certNat% 224))
 (.branch 226
 (.leaf (certNat% 225))
 (.leaf (certNat% 226))))
 (.branch 228
 (.leaf (certNat% 227))
 (.branch 229
 (.leaf (certNat% 228))
 (.leaf (certNat% 229)))))
 (.branch 233
 (.branch 231
 (.leaf (certNat% 230))
 (.branch 232
 (.leaf (certNat% 231))
 (.leaf (certNat% 232))))
 (.branch 234
 (.leaf (certNat% 233))
 (.branch 235
 (.leaf (certNat% 234))
 (.leaf (certNat% 235))))))))
 (.branch 259
 (.branch 247
 (.branch 241
 (.branch 238
 (.branch 237
 (.leaf (certNat% 236))
 (.leaf (certNat% 237)))
 (.branch 239
 (.leaf (certNat% 238))
 (.branch 240
 (.leaf (certNat% 239))
 (.leaf (certNat% 240)))))
 (.branch 244
 (.branch 242
 (.leaf (certNat% 241))
 (.branch 243
 (.leaf (certNat% 242))
 (.leaf (certNat% 243))))
 (.branch 245
 (.leaf (certNat% 244))
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
 (.branch 257
 (.leaf (certNat% 256))
 (.branch 258
 (.leaf (certNat% 257))
 (.leaf (certNat% 258)))))))
 (.branch 271
 (.branch 265
 (.branch 262
 (.branch 260
 (.leaf (certNat% 259))
 (.branch 261
 (.leaf (certNat% 260))
 (.leaf (certNat% 261))))
 (.branch 263
 (.leaf (certNat% 262))
 (.branch 264
 (.leaf (certNat% 263))
 (.leaf (certNat% 264)))))
 (.branch 268
 (.branch 266
 (.leaf (certNat% 265))
 (.branch 267
 (.leaf (certNat% 266))
 (.leaf (certNat% 267))))
 (.branch 269
 (.leaf (certNat% 268))
 (.branch 270
 (.leaf (certNat% 269))
 (.leaf (certNat% 270))))))
 (.branch 277
 (.branch 274
 (.branch 272
 (.leaf (certNat% 271))
 (.branch 273
 (.leaf (certNat% 272))
 (.leaf (certNat% 273))))
 (.branch 275
 (.leaf (certNat% 274))
 (.branch 276
 (.leaf (certNat% 275))
 (.leaf (certNat% 276)))))
 (.branch 280
 (.branch 278
 (.leaf (certNat% 277))
 (.branch 279
 (.leaf (certNat% 278))
 (.leaf (certNat% 279))))
 (.branch 281
 (.leaf (certNat% 280))
 (.branch 282
 (.leaf (certNat% 281))
 (.leaf (certNat% 282)))))))))
 (.branch 330
 (.branch 306
 (.branch 294
 (.branch 288
 (.branch 285
 (.branch 284
 (.leaf (certNat% 283))
 (.leaf (certNat% 284)))
 (.branch 286
 (.leaf (certNat% 285))
 (.branch 287
 (.leaf (certNat% 286))
 (.leaf (certNat% 287)))))
 (.branch 291
 (.branch 289
 (.leaf (certNat% 288))
 (.branch 290
 (.leaf (certNat% 289))
 (.leaf (certNat% 290))))
 (.branch 292
 (.leaf (certNat% 291))
 (.branch 293
 (.leaf (certNat% 292))
 (.leaf (certNat% 293))))))
 (.branch 300
 (.branch 297
 (.branch 295
 (.leaf (certNat% 294))
 (.branch 296
 (.leaf (certNat% 295))
 (.leaf (certNat% 296))))
 (.branch 298
 (.leaf (certNat% 297))
 (.branch 299
 (.leaf (certNat% 298))
 (.leaf (certNat% 299)))))
 (.branch 303
 (.branch 301
 (.leaf (certNat% 300))
 (.branch 302
 (.leaf (certNat% 301))
 (.leaf (certNat% 302))))
 (.branch 304
 (.leaf (certNat% 303))
 (.branch 305
 (.leaf (certNat% 304))
 (.leaf (certNat% 305)))))))
 (.branch 318
 (.branch 312
 (.branch 309
 (.branch 307
 (.leaf (certNat% 306))
 (.branch 308
 (.leaf (certNat% 307))
 (.leaf (certNat% 308))))
 (.branch 310
 (.leaf (certNat% 309))
 (.branch 311
 (.leaf (certNat% 310))
 (.leaf (certNat% 311)))))
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
 (.leaf (certNat% 317))))))
 (.branch 324
 (.branch 321
 (.branch 319
 (.leaf (certNat% 318))
 (.branch 320
 (.leaf (certNat% 319))
 (.leaf (certNat% 320))))
 (.branch 322
 (.leaf (certNat% 321))
 (.branch 323
 (.leaf (certNat% 322))
 (.leaf (certNat% 323)))))
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
 (.leaf (certNat% 329))))))))
 (.branch 354
 (.branch 342
 (.branch 336
 (.branch 333
 (.branch 331
 (.leaf (certNat% 330))
 (.branch 332
 (.leaf (certNat% 331))
 (.leaf (certNat% 332))))
 (.branch 334
 (.leaf (certNat% 333))
 (.branch 335
 (.leaf (certNat% 334))
 (.leaf (certNat% 335)))))
 (.branch 339
 (.branch 337
 (.leaf (certNat% 336))
 (.branch 338
 (.leaf (certNat% 337))
 (.leaf (certNat% 338))))
 (.branch 340
 (.leaf (certNat% 339))
 (.branch 341
 (.leaf (certNat% 340))
 (.leaf (certNat% 341))))))
 (.branch 348
 (.branch 345
 (.branch 343
 (.leaf (certNat% 342))
 (.branch 344
 (.leaf (certNat% 343))
 (.leaf (certNat% 344))))
 (.branch 346
 (.leaf (certNat% 345))
 (.branch 347
 (.leaf (certNat% 346))
 (.leaf (certNat% 347)))))
 (.branch 351
 (.branch 349
 (.leaf (certNat% 348))
 (.branch 350
 (.leaf (certNat% 349))
 (.leaf (certNat% 350))))
 (.branch 352
 (.leaf (certNat% 351))
 (.branch 353
 (.leaf (certNat% 352))
 (.leaf (certNat% 353)))))))
 (.branch 366
 (.branch 360
 (.branch 357
 (.branch 355
 (.leaf (certNat% 354))
 (.branch 356
 (.leaf (certNat% 355))
 (.leaf (certNat% 356))))
 (.branch 358
 (.leaf (certNat% 357))
 (.branch 359
 (.leaf (certNat% 358))
 (.leaf (certNat% 359)))))
 (.branch 363
 (.branch 361
 (.leaf (certNat% 360))
 (.branch 362
 (.leaf (certNat% 361))
 (.leaf (certNat% 362))))
 (.branch 364
 (.leaf (certNat% 363))
 (.branch 365
 (.leaf (certNat% 364))
 (.leaf (certNat% 365))))))
 (.branch 372
 (.branch 369
 (.branch 367
 (.leaf (certNat% 366))
 (.branch 368
 (.leaf (certNat% 367))
 (.leaf (certNat% 368))))
 (.branch 370
 (.leaf (certNat% 369))
 (.branch 371
 (.leaf (certNat% 370))
 (.leaf (certNat% 371)))))
 (.branch 375
 (.branch 373
 (.leaf (certNat% 372))
 (.branch 374
 (.leaf (certNat% 373))
 (.leaf (certNat% 374))))
 (.branch 376
 (.leaf (certNat% 375))
 (.branch 377
 (.leaf (certNat% 376))
 (.leaf (certNat% 377)))))))))))
 (.branch 567
 (.branch 472
 (.branch 425
 (.branch 401
 (.branch 389
 (.branch 383
 (.branch 380
 (.branch 379
 (.leaf (certNat% 378))
 (.leaf (certNat% 379)))
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
 (.branch 387
 (.leaf (certNat% 386))
 (.branch 388
 (.leaf (certNat% 387))
 (.leaf (certNat% 388))))))
 (.branch 395
 (.branch 392
 (.branch 390
 (.leaf (certNat% 389))
 (.branch 391
 (.leaf (certNat% 390))
 (.leaf (certNat% 391))))
 (.branch 393
 (.leaf (certNat% 392))
 (.branch 394
 (.leaf (certNat% 393))
 (.leaf (certNat% 394)))))
 (.branch 398
 (.branch 396
 (.leaf (certNat% 395))
 (.branch 397
 (.leaf (certNat% 396))
 (.leaf (certNat% 397))))
 (.branch 399
 (.leaf (certNat% 398))
 (.branch 400
 (.leaf (certNat% 399))
 (.leaf (certNat% 400)))))))
 (.branch 413
 (.branch 407
 (.branch 404
 (.branch 402
 (.leaf (certNat% 401))
 (.branch 403
 (.leaf (certNat% 402))
 (.leaf (certNat% 403))))
 (.branch 405
 (.leaf (certNat% 404))
 (.branch 406
 (.leaf (certNat% 405))
 (.leaf (certNat% 406)))))
 (.branch 410
 (.branch 408
 (.leaf (certNat% 407))
 (.branch 409
 (.leaf (certNat% 408))
 (.leaf (certNat% 409))))
 (.branch 411
 (.leaf (certNat% 410))
 (.branch 412
 (.leaf (certNat% 411))
 (.leaf (certNat% 412))))))
 (.branch 419
 (.branch 416
 (.branch 414
 (.leaf (certNat% 413))
 (.branch 415
 (.leaf (certNat% 414))
 (.leaf (certNat% 415))))
 (.branch 417
 (.leaf (certNat% 416))
 (.branch 418
 (.leaf (certNat% 417))
 (.leaf (certNat% 418)))))
 (.branch 422
 (.branch 420
 (.leaf (certNat% 419))
 (.branch 421
 (.leaf (certNat% 420))
 (.leaf (certNat% 421))))
 (.branch 423
 (.leaf (certNat% 422))
 (.branch 424
 (.leaf (certNat% 423))
 (.leaf (certNat% 424))))))))
 (.branch 448
 (.branch 436
 (.branch 430
 (.branch 427
 (.branch 426
 (.leaf (certNat% 425))
 (.leaf (certNat% 426)))
 (.branch 428
 (.leaf (certNat% 427))
 (.branch 429
 (.leaf (certNat% 428))
 (.leaf (certNat% 429)))))
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
 (.leaf (certNat% 435))))))
 (.branch 442
 (.branch 439
 (.branch 437
 (.leaf (certNat% 436))
 (.branch 438
 (.leaf (certNat% 437))
 (.leaf (certNat% 438))))
 (.branch 440
 (.leaf (certNat% 439))
 (.branch 441
 (.leaf (certNat% 440))
 (.leaf (certNat% 441)))))
 (.branch 445
 (.branch 443
 (.leaf (certNat% 442))
 (.branch 444
 (.leaf (certNat% 443))
 (.leaf (certNat% 444))))
 (.branch 446
 (.leaf (certNat% 445))
 (.branch 447
 (.leaf (certNat% 446))
 (.leaf (certNat% 447)))))))
 (.branch 460
 (.branch 454
 (.branch 451
 (.branch 449
 (.leaf (certNat% 448))
 (.branch 450
 (.leaf (certNat% 449))
 (.leaf (certNat% 450))))
 (.branch 452
 (.leaf (certNat% 451))
 (.branch 453
 (.leaf (certNat% 452))
 (.leaf (certNat% 453)))))
 (.branch 457
 (.branch 455
 (.leaf (certNat% 454))
 (.branch 456
 (.leaf (certNat% 455))
 (.leaf (certNat% 456))))
 (.branch 458
 (.leaf (certNat% 457))
 (.branch 459
 (.leaf (certNat% 458))
 (.leaf (certNat% 459))))))
 (.branch 466
 (.branch 463
 (.branch 461
 (.leaf (certNat% 460))
 (.branch 462
 (.leaf (certNat% 461))
 (.leaf (certNat% 462))))
 (.branch 464
 (.leaf (certNat% 463))
 (.branch 465
 (.leaf (certNat% 464))
 (.leaf (certNat% 465)))))
 (.branch 469
 (.branch 467
 (.leaf (certNat% 466))
 (.branch 468
 (.leaf (certNat% 467))
 (.leaf (certNat% 468))))
 (.branch 470
 (.leaf (certNat% 469))
 (.branch 471
 (.leaf (certNat% 470))
 (.leaf (certNat% 471)))))))))
 (.branch 519
 (.branch 495
 (.branch 483
 (.branch 477
 (.branch 474
 (.branch 473
 (.leaf (certNat% 472))
 (.leaf (certNat% 473)))
 (.branch 475
 (.leaf (certNat% 474))
 (.branch 476
 (.leaf (certNat% 475))
 (.leaf (certNat% 476)))))
 (.branch 480
 (.branch 478
 (.leaf (certNat% 477))
 (.branch 479
 (.leaf (certNat% 478))
 (.leaf (certNat% 479))))
 (.branch 481
 (.leaf (certNat% 480))
 (.branch 482
 (.leaf (certNat% 481))
 (.leaf (certNat% 482))))))
 (.branch 489
 (.branch 486
 (.branch 484
 (.leaf (certNat% 483))
 (.branch 485
 (.leaf (certNat% 484))
 (.leaf (certNat% 485))))
 (.branch 487
 (.leaf (certNat% 486))
 (.branch 488
 (.leaf (certNat% 487))
 (.leaf (certNat% 488)))))
 (.branch 492
 (.branch 490
 (.leaf (certNat% 489))
 (.branch 491
 (.leaf (certNat% 490))
 (.leaf (certNat% 491))))
 (.branch 493
 (.leaf (certNat% 492))
 (.branch 494
 (.leaf (certNat% 493))
 (.leaf (certNat% 494)))))))
 (.branch 507
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
 (.branch 505
 (.leaf (certNat% 504))
 (.branch 506
 (.leaf (certNat% 505))
 (.leaf (certNat% 506))))))
 (.branch 513
 (.branch 510
 (.branch 508
 (.leaf (certNat% 507))
 (.branch 509
 (.leaf (certNat% 508))
 (.leaf (certNat% 509))))
 (.branch 511
 (.leaf (certNat% 510))
 (.branch 512
 (.leaf (certNat% 511))
 (.leaf (certNat% 512)))))
 (.branch 516
 (.branch 514
 (.leaf (certNat% 513))
 (.branch 515
 (.leaf (certNat% 514))
 (.leaf (certNat% 515))))
 (.branch 517
 (.leaf (certNat% 516))
 (.branch 518
 (.leaf (certNat% 517))
 (.leaf (certNat% 518))))))))
 (.branch 543
 (.branch 531
 (.branch 525
 (.branch 522
 (.branch 520
 (.leaf (certNat% 519))
 (.branch 521
 (.leaf (certNat% 520))
 (.leaf (certNat% 521))))
 (.branch 523
 (.leaf (certNat% 522))
 (.branch 524
 (.leaf (certNat% 523))
 (.leaf (certNat% 524)))))
 (.branch 528
 (.branch 526
 (.leaf (certNat% 525))
 (.branch 527
 (.leaf (certNat% 526))
 (.leaf (certNat% 527))))
 (.branch 529
 (.leaf (certNat% 528))
 (.branch 530
 (.leaf (certNat% 529))
 (.leaf (certNat% 530))))))
 (.branch 537
 (.branch 534
 (.branch 532
 (.leaf (certNat% 531))
 (.branch 533
 (.leaf (certNat% 532))
 (.leaf (certNat% 533))))
 (.branch 535
 (.leaf (certNat% 534))
 (.branch 536
 (.leaf (certNat% 535))
 (.leaf (certNat% 536)))))
 (.branch 540
 (.branch 538
 (.leaf (certNat% 537))
 (.branch 539
 (.leaf (certNat% 538))
 (.leaf (certNat% 539))))
 (.branch 541
 (.leaf (certNat% 540))
 (.branch 542
 (.leaf (certNat% 541))
 (.leaf (certNat% 542)))))))
 (.branch 555
 (.branch 549
 (.branch 546
 (.branch 544
 (.leaf (certNat% 543))
 (.branch 545
 (.leaf (certNat% 544))
 (.leaf (certNat% 545))))
 (.branch 547
 (.leaf (certNat% 546))
 (.branch 548
 (.leaf (certNat% 547))
 (.leaf (certNat% 548)))))
 (.branch 552
 (.branch 550
 (.leaf (certNat% 549))
 (.branch 551
 (.leaf (certNat% 550))
 (.leaf (certNat% 551))))
 (.branch 553
 (.leaf (certNat% 552))
 (.branch 554
 (.leaf (certNat% 553))
 (.leaf (certNat% 554))))))
 (.branch 561
 (.branch 558
 (.branch 556
 (.leaf (certNat% 555))
 (.branch 557
 (.leaf (certNat% 556))
 (.leaf (certNat% 557))))
 (.branch 559
 (.leaf (certNat% 558))
 (.branch 560
 (.leaf (certNat% 559))
 (.leaf (certNat% 560)))))
 (.branch 564
 (.branch 562
 (.leaf (certNat% 561))
 (.branch 563
 (.leaf (certNat% 562))
 (.leaf (certNat% 563))))
 (.branch 565
 (.leaf (certNat% 564))
 (.branch 566
 (.leaf (certNat% 565))
 (.leaf (certNat% 566))))))))))
 (.branch 661
 (.branch 614
 (.branch 590
 (.branch 578
 (.branch 572
 (.branch 569
 (.branch 568
 (.leaf (certNat% 567))
 (.leaf (certNat% 568)))
 (.branch 570
 (.leaf (certNat% 569))
 (.branch 571
 (.leaf (certNat% 570))
 (.leaf (certNat% 571)))))
 (.branch 575
 (.branch 573
 (.leaf (certNat% 572))
 (.branch 574
 (.leaf (certNat% 573))
 (.leaf (certNat% 574))))
 (.branch 576
 (.leaf (certNat% 575))
 (.branch 577
 (.leaf (certNat% 576))
 (.leaf (certNat% 577))))))
 (.branch 584
 (.branch 581
 (.branch 579
 (.leaf (certNat% 578))
 (.branch 580
 (.leaf (certNat% 579))
 (.leaf (certNat% 580))))
 (.branch 582
 (.leaf (certNat% 581))
 (.branch 583
 (.leaf (certNat% 582))
 (.leaf (certNat% 583)))))
 (.branch 587
 (.branch 585
 (.leaf (certNat% 584))
 (.branch 586
 (.leaf (certNat% 585))
 (.leaf (certNat% 586))))
 (.branch 588
 (.leaf (certNat% 587))
 (.branch 589
 (.leaf (certNat% 588))
 (.leaf (certNat% 589)))))))
 (.branch 602
 (.branch 596
 (.branch 593
 (.branch 591
 (.leaf (certNat% 590))
 (.branch 592
 (.leaf (certNat% 591))
 (.leaf (certNat% 592))))
 (.branch 594
 (.leaf (certNat% 593))
 (.branch 595
 (.leaf (certNat% 594))
 (.leaf (certNat% 595)))))
 (.branch 599
 (.branch 597
 (.leaf (certNat% 596))
 (.branch 598
 (.leaf (certNat% 597))
 (.leaf (certNat% 598))))
 (.branch 600
 (.leaf (certNat% 599))
 (.branch 601
 (.leaf (certNat% 600))
 (.leaf (certNat% 601))))))
 (.branch 608
 (.branch 605
 (.branch 603
 (.leaf (certNat% 602))
 (.branch 604
 (.leaf (certNat% 603))
 (.leaf (certNat% 604))))
 (.branch 606
 (.leaf (certNat% 605))
 (.branch 607
 (.leaf (certNat% 606))
 (.leaf (certNat% 607)))))
 (.branch 611
 (.branch 609
 (.leaf (certNat% 608))
 (.branch 610
 (.leaf (certNat% 609))
 (.leaf (certNat% 610))))
 (.branch 612
 (.leaf (certNat% 611))
 (.branch 613
 (.leaf (certNat% 612))
 (.leaf (certNat% 613))))))))
 (.branch 637
 (.branch 625
 (.branch 619
 (.branch 616
 (.branch 615
 (.leaf (certNat% 614))
 (.leaf (certNat% 615)))
 (.branch 617
 (.leaf (certNat% 616))
 (.branch 618
 (.leaf (certNat% 617))
 (.leaf (certNat% 618)))))
 (.branch 622
 (.branch 620
 (.leaf (certNat% 619))
 (.branch 621
 (.leaf (certNat% 620))
 (.leaf (certNat% 621))))
 (.branch 623
 (.leaf (certNat% 622))
 (.branch 624
 (.leaf (certNat% 623))
 (.leaf (certNat% 624))))))
 (.branch 631
 (.branch 628
 (.branch 626
 (.leaf (certNat% 625))
 (.branch 627
 (.leaf (certNat% 626))
 (.leaf (certNat% 627))))
 (.branch 629
 (.leaf (certNat% 628))
 (.branch 630
 (.leaf (certNat% 629))
 (.leaf (certNat% 630)))))
 (.branch 634
 (.branch 632
 (.leaf (certNat% 631))
 (.branch 633
 (.leaf (certNat% 632))
 (.leaf (certNat% 633))))
 (.branch 635
 (.leaf (certNat% 634))
 (.branch 636
 (.leaf (certNat% 635))
 (.leaf (certNat% 636)))))))
 (.branch 649
 (.branch 643
 (.branch 640
 (.branch 638
 (.leaf (certNat% 637))
 (.branch 639
 (.leaf (certNat% 638))
 (.leaf (certNat% 639))))
 (.branch 641
 (.leaf (certNat% 640))
 (.branch 642
 (.leaf (certNat% 641))
 (.leaf (certNat% 642)))))
 (.branch 646
 (.branch 644
 (.leaf (certNat% 643))
 (.branch 645
 (.leaf (certNat% 644))
 (.leaf (certNat% 645))))
 (.branch 647
 (.leaf (certNat% 646))
 (.branch 648
 (.leaf (certNat% 647))
 (.leaf (certNat% 648))))))
 (.branch 655
 (.branch 652
 (.branch 650
 (.leaf (certNat% 649))
 (.branch 651
 (.leaf (certNat% 650))
 (.leaf (certNat% 651))))
 (.branch 653
 (.leaf (certNat% 652))
 (.branch 654
 (.leaf (certNat% 653))
 (.leaf (certNat% 654)))))
 (.branch 658
 (.branch 656
 (.leaf (certNat% 655))
 (.branch 657
 (.leaf (certNat% 656))
 (.leaf (certNat% 657))))
 (.branch 659
 (.leaf (certNat% 658))
 (.branch 660
 (.leaf (certNat% 659))
 (.leaf (certNat% 660)))))))))
 (.branch 708
 (.branch 684
 (.branch 672
 (.branch 666
 (.branch 663
 (.branch 662
 (.leaf (certNat% 661))
 (.leaf (certNat% 662)))
 (.branch 664
 (.leaf (certNat% 663))
 (.branch 665
 (.leaf (certNat% 664))
 (.leaf (certNat% 665)))))
 (.branch 669
 (.branch 667
 (.leaf (certNat% 666))
 (.branch 668
 (.leaf (certNat% 667))
 (.leaf (certNat% 668))))
 (.branch 670
 (.leaf (certNat% 669))
 (.branch 671
 (.leaf (certNat% 670))
 (.leaf (certNat% 671))))))
 (.branch 678
 (.branch 675
 (.branch 673
 (.leaf (certNat% 672))
 (.branch 674
 (.leaf (certNat% 673))
 (.leaf (certNat% 674))))
 (.branch 676
 (.leaf (certNat% 675))
 (.branch 677
 (.leaf (certNat% 676))
 (.leaf (certNat% 677)))))
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
 (.leaf (certNat% 683)))))))
 (.branch 696
 (.branch 690
 (.branch 687
 (.branch 685
 (.leaf (certNat% 684))
 (.branch 686
 (.leaf (certNat% 685))
 (.leaf (certNat% 686))))
 (.branch 688
 (.leaf (certNat% 687))
 (.branch 689
 (.leaf (certNat% 688))
 (.leaf (certNat% 689)))))
 (.branch 693
 (.branch 691
 (.leaf (certNat% 690))
 (.branch 692
 (.leaf (certNat% 691))
 (.leaf (certNat% 692))))
 (.branch 694
 (.leaf (certNat% 693))
 (.branch 695
 (.leaf (certNat% 694))
 (.leaf (certNat% 695))))))
 (.branch 702
 (.branch 699
 (.branch 697
 (.leaf (certNat% 696))
 (.branch 698
 (.leaf (certNat% 697))
 (.leaf (certNat% 698))))
 (.branch 700
 (.leaf (certNat% 699))
 (.branch 701
 (.leaf (certNat% 700))
 (.leaf (certNat% 701)))))
 (.branch 705
 (.branch 703
 (.leaf (certNat% 702))
 (.branch 704
 (.leaf (certNat% 703))
 (.leaf (certNat% 704))))
 (.branch 706
 (.leaf (certNat% 705))
 (.branch 707
 (.leaf (certNat% 706))
 (.leaf (certNat% 707))))))))
 (.branch 732
 (.branch 720
 (.branch 714
 (.branch 711
 (.branch 709
 (.leaf (certNat% 708))
 (.branch 710
 (.leaf (certNat% 709))
 (.leaf (certNat% 710))))
 (.branch 712
 (.leaf (certNat% 711))
 (.branch 713
 (.leaf (certNat% 712))
 (.leaf (certNat% 713)))))
 (.branch 717
 (.branch 715
 (.leaf (certNat% 714))
 (.branch 716
 (.leaf (certNat% 715))
 (.leaf (certNat% 716))))
 (.branch 718
 (.leaf (certNat% 717))
 (.branch 719
 (.leaf (certNat% 718))
 (.leaf (certNat% 719))))))
 (.branch 726
 (.branch 723
 (.branch 721
 (.leaf (certNat% 720))
 (.branch 722
 (.leaf (certNat% 721))
 (.leaf (certNat% 722))))
 (.branch 724
 (.leaf (certNat% 723))
 (.branch 725
 (.leaf (certNat% 724))
 (.leaf (certNat% 725)))))
 (.branch 729
 (.branch 727
 (.leaf (certNat% 726))
 (.branch 728
 (.leaf (certNat% 727))
 (.leaf (certNat% 728))))
 (.branch 730
 (.leaf (certNat% 729))
 (.branch 731
 (.leaf (certNat% 730))
 (.leaf (certNat% 731)))))))
 (.branch 744
 (.branch 738
 (.branch 735
 (.branch 733
 (.leaf (certNat% 732))
 (.branch 734
 (.leaf (certNat% 733))
 (.leaf (certNat% 734))))
 (.branch 736
 (.leaf (certNat% 735))
 (.branch 737
 (.leaf (certNat% 736))
 (.leaf (certNat% 737)))))
 (.branch 741
 (.branch 739
 (.leaf (certNat% 738))
 (.branch 740
 (.leaf (certNat% 739))
 (.leaf (certNat% 740))))
 (.branch 742
 (.leaf (certNat% 741))
 (.branch 743
 (.leaf (certNat% 742))
 (.leaf (certNat% 743))))))
 (.branch 750
 (.branch 747
 (.branch 745
 (.leaf (certNat% 744))
 (.branch 746
 (.leaf (certNat% 745))
 (.leaf (certNat% 746))))
 (.branch 748
 (.leaf (certNat% 747))
 (.branch 749
 (.leaf (certNat% 748))
 (.leaf (certNat% 749)))))
 (.branch 753
 (.branch 751
 (.leaf (certNat% 750))
 (.branch 752
 (.leaf (certNat% 751))
 (.leaf (certNat% 752))))
 (.branch 754
 (.leaf (certNat% 753))
 (.branch 755
 (.leaf (certNat% 754))
 (.leaf (certNat% 755))))))))))))
cert_rawLeaves_4 14
cert_leaves_3
cert_quota_3 0 3 0 0 0 0 0 0 3 6
cert_nodeTest_5 48 01
cert_nodeTest_sound_4 48 01
cert_leafTest_4 01
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0353

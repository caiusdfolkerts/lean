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
public import SmallSubsumedForest15Packed000
public import SmallSubsumedForest15Packed001
public import SmallSubsumedForest15Packed002
public import SmallSubsumedForest15Packed003
public import SmallSubsumedForest15Packed004
public import SmallSubsumedForest15Packed005
public import SmallSubsumedForest15Packed006
public import SmallSubsumedForest15Packed007
public import SmallSubsumedForest15Packed008
public import SmallSubsumedForest15Packed009
public import SmallSubsumedForest15Packed010
public import SmallSubsumedForest15Packed011
public import SmallSubsumedForest15Packed012

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest15
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 3436
abbrev nodeCount : Nat := 79417
abbrev leafCount : Nat := 578
cert_widths_4 17 10
def blocks : Table PackedRawNatGrowth.Block :=
(.branch 300
 (.branch 150
 (.branch 50
 nodeBlocks000
 (.branch 100
 nodeBlocks001
 nodeBlocks002))
 (.branch 200
 nodeBlocks003
 (.branch 250
 nodeBlocks004
 nodeBlocks005)))
 (.branch 450
 (.branch 350
 nodeBlocks006
 (.branch 400
 nodeBlocks007
 nodeBlocks008))
 (.branch 550
 (.branch 500
 nodeBlocks009
 nodeBlocks010)
 (.branch 600
 nodeBlocks011
 nodeBlocks012))))
def counterTable : Table Nat :=
(.branch 300
 (.branch 150
 (.branch 50
 nodeCounters000
 (.branch 100
 nodeCounters001
 nodeCounters002))
 (.branch 200
 nodeCounters003
 (.branch 250
 nodeCounters004
 nodeCounters005)))
 (.branch 450
 (.branch 350
 nodeCounters006
 (.branch 400
 nodeCounters007
 nodeCounters008))
 (.branch 550
 (.branch 500
 nodeCounters009
 nodeCounters010)
 (.branch 600
 nodeCounters011
 nodeCounters012))))
cert_codes_4
cert_counters_4
cert_rawNodes_4
def leafTable : Table Nat :=
(.branch 289
 (.branch 144
 (.branch 72
 (.branch 36
 (.branch 18
 (.branch 9
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
 (.branch 8
 (.leaf (certNat% 7))
 (.leaf (certNat% 8))))))
 (.branch 13
 (.branch 11
 (.branch 10
 (.leaf (certNat% 9))
 (.leaf (certNat% 10)))
 (.branch 12
 (.leaf (certNat% 11))
 (.leaf (certNat% 12))))
 (.branch 15
 (.branch 14
 (.leaf (certNat% 13))
 (.leaf (certNat% 14)))
 (.branch 16
 (.leaf (certNat% 15))
 (.branch 17
 (.leaf (certNat% 16))
 (.leaf (certNat% 17)))))))
 (.branch 27
 (.branch 22
 (.branch 20
 (.branch 19
 (.leaf (certNat% 18))
 (.leaf (certNat% 19)))
 (.branch 21
 (.leaf (certNat% 20))
 (.leaf (certNat% 21))))
 (.branch 24
 (.branch 23
 (.leaf (certNat% 22))
 (.leaf (certNat% 23)))
 (.branch 25
 (.leaf (certNat% 24))
 (.branch 26
 (.leaf (certNat% 25))
 (.leaf (certNat% 26))))))
 (.branch 31
 (.branch 29
 (.branch 28
 (.leaf (certNat% 27))
 (.leaf (certNat% 28)))
 (.branch 30
 (.leaf (certNat% 29))
 (.leaf (certNat% 30))))
 (.branch 33
 (.branch 32
 (.leaf (certNat% 31))
 (.leaf (certNat% 32)))
 (.branch 34
 (.leaf (certNat% 33))
 (.branch 35
 (.leaf (certNat% 34))
 (.leaf (certNat% 35))))))))
 (.branch 54
 (.branch 45
 (.branch 40
 (.branch 38
 (.branch 37
 (.leaf (certNat% 36))
 (.leaf (certNat% 37)))
 (.branch 39
 (.leaf (certNat% 38))
 (.leaf (certNat% 39))))
 (.branch 42
 (.branch 41
 (.leaf (certNat% 40))
 (.leaf (certNat% 41)))
 (.branch 43
 (.leaf (certNat% 42))
 (.branch 44
 (.leaf (certNat% 43))
 (.leaf (certNat% 44))))))
 (.branch 49
 (.branch 47
 (.branch 46
 (.leaf (certNat% 45))
 (.leaf (certNat% 46)))
 (.branch 48
 (.leaf (certNat% 47))
 (.leaf (certNat% 48))))
 (.branch 51
 (.branch 50
 (.leaf (certNat% 49))
 (.leaf (certNat% 50)))
 (.branch 52
 (.leaf (certNat% 51))
 (.branch 53
 (.leaf (certNat% 52))
 (.leaf (certNat% 53)))))))
 (.branch 63
 (.branch 58
 (.branch 56
 (.branch 55
 (.leaf (certNat% 54))
 (.leaf (certNat% 55)))
 (.branch 57
 (.leaf (certNat% 56))
 (.leaf (certNat% 57))))
 (.branch 60
 (.branch 59
 (.leaf (certNat% 58))
 (.leaf (certNat% 59)))
 (.branch 61
 (.leaf (certNat% 60))
 (.branch 62
 (.leaf (certNat% 61))
 (.leaf (certNat% 62))))))
 (.branch 67
 (.branch 65
 (.branch 64
 (.leaf (certNat% 63))
 (.leaf (certNat% 64)))
 (.branch 66
 (.leaf (certNat% 65))
 (.leaf (certNat% 66))))
 (.branch 69
 (.branch 68
 (.leaf (certNat% 67))
 (.leaf (certNat% 68)))
 (.branch 70
 (.leaf (certNat% 69))
 (.branch 71
 (.leaf (certNat% 70))
 (.leaf (certNat% 71)))))))))
 (.branch 108
 (.branch 90
 (.branch 81
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
 (.branch 80
 (.leaf (certNat% 79))
 (.leaf (certNat% 80))))))
 (.branch 85
 (.branch 83
 (.branch 82
 (.leaf (certNat% 81))
 (.leaf (certNat% 82)))
 (.branch 84
 (.leaf (certNat% 83))
 (.leaf (certNat% 84))))
 (.branch 87
 (.branch 86
 (.leaf (certNat% 85))
 (.leaf (certNat% 86)))
 (.branch 88
 (.leaf (certNat% 87))
 (.branch 89
 (.leaf (certNat% 88))
 (.leaf (certNat% 89)))))))
 (.branch 99
 (.branch 94
 (.branch 92
 (.branch 91
 (.leaf (certNat% 90))
 (.leaf (certNat% 91)))
 (.branch 93
 (.leaf (certNat% 92))
 (.leaf (certNat% 93))))
 (.branch 96
 (.branch 95
 (.leaf (certNat% 94))
 (.leaf (certNat% 95)))
 (.branch 97
 (.leaf (certNat% 96))
 (.branch 98
 (.leaf (certNat% 97))
 (.leaf (certNat% 98))))))
 (.branch 103
 (.branch 101
 (.branch 100
 (.leaf (certNat% 99))
 (.leaf (certNat% 100)))
 (.branch 102
 (.leaf (certNat% 101))
 (.leaf (certNat% 102))))
 (.branch 105
 (.branch 104
 (.leaf (certNat% 103))
 (.leaf (certNat% 104)))
 (.branch 106
 (.leaf (certNat% 105))
 (.branch 107
 (.leaf (certNat% 106))
 (.leaf (certNat% 107))))))))
 (.branch 126
 (.branch 117
 (.branch 112
 (.branch 110
 (.branch 109
 (.leaf (certNat% 108))
 (.leaf (certNat% 109)))
 (.branch 111
 (.leaf (certNat% 110))
 (.leaf (certNat% 111))))
 (.branch 114
 (.branch 113
 (.leaf (certNat% 112))
 (.leaf (certNat% 113)))
 (.branch 115
 (.leaf (certNat% 114))
 (.branch 116
 (.leaf (certNat% 115))
 (.leaf (certNat% 116))))))
 (.branch 121
 (.branch 119
 (.branch 118
 (.leaf (certNat% 117))
 (.leaf (certNat% 118)))
 (.branch 120
 (.leaf (certNat% 119))
 (.leaf (certNat% 120))))
 (.branch 123
 (.branch 122
 (.leaf (certNat% 121))
 (.leaf (certNat% 122)))
 (.branch 124
 (.leaf (certNat% 123))
 (.branch 125
 (.leaf (certNat% 124))
 (.leaf (certNat% 125)))))))
 (.branch 135
 (.branch 130
 (.branch 128
 (.branch 127
 (.leaf (certNat% 126))
 (.leaf (certNat% 127)))
 (.branch 129
 (.leaf (certNat% 128))
 (.leaf (certNat% 129))))
 (.branch 132
 (.branch 131
 (.leaf (certNat% 130))
 (.leaf (certNat% 131)))
 (.branch 133
 (.leaf (certNat% 132))
 (.branch 134
 (.leaf (certNat% 133))
 (.leaf (certNat% 134))))))
 (.branch 139
 (.branch 137
 (.branch 136
 (.leaf (certNat% 135))
 (.leaf (certNat% 136)))
 (.branch 138
 (.leaf (certNat% 137))
 (.leaf (certNat% 138))))
 (.branch 141
 (.branch 140
 (.leaf (certNat% 139))
 (.leaf (certNat% 140)))
 (.branch 142
 (.leaf (certNat% 141))
 (.branch 143
 (.leaf (certNat% 142))
 (.leaf (certNat% 143))))))))))
 (.branch 216
 (.branch 180
 (.branch 162
 (.branch 153
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
 (.branch 152
 (.leaf (certNat% 151))
 (.leaf (certNat% 152))))))
 (.branch 157
 (.branch 155
 (.branch 154
 (.leaf (certNat% 153))
 (.leaf (certNat% 154)))
 (.branch 156
 (.leaf (certNat% 155))
 (.leaf (certNat% 156))))
 (.branch 159
 (.branch 158
 (.leaf (certNat% 157))
 (.leaf (certNat% 158)))
 (.branch 160
 (.leaf (certNat% 159))
 (.branch 161
 (.leaf (certNat% 160))
 (.leaf (certNat% 161)))))))
 (.branch 171
 (.branch 166
 (.branch 164
 (.branch 163
 (.leaf (certNat% 162))
 (.leaf (certNat% 163)))
 (.branch 165
 (.leaf (certNat% 164))
 (.leaf (certNat% 165))))
 (.branch 168
 (.branch 167
 (.leaf (certNat% 166))
 (.leaf (certNat% 167)))
 (.branch 169
 (.leaf (certNat% 168))
 (.branch 170
 (.leaf (certNat% 169))
 (.leaf (certNat% 170))))))
 (.branch 175
 (.branch 173
 (.branch 172
 (.leaf (certNat% 171))
 (.leaf (certNat% 172)))
 (.branch 174
 (.leaf (certNat% 173))
 (.leaf (certNat% 174))))
 (.branch 177
 (.branch 176
 (.leaf (certNat% 175))
 (.leaf (certNat% 176)))
 (.branch 178
 (.leaf (certNat% 177))
 (.branch 179
 (.leaf (certNat% 178))
 (.leaf (certNat% 179))))))))
 (.branch 198
 (.branch 189
 (.branch 184
 (.branch 182
 (.branch 181
 (.leaf (certNat% 180))
 (.leaf (certNat% 181)))
 (.branch 183
 (.leaf (certNat% 182))
 (.leaf (certNat% 183))))
 (.branch 186
 (.branch 185
 (.leaf (certNat% 184))
 (.leaf (certNat% 185)))
 (.branch 187
 (.leaf (certNat% 186))
 (.branch 188
 (.leaf (certNat% 187))
 (.leaf (certNat% 188))))))
 (.branch 193
 (.branch 191
 (.branch 190
 (.leaf (certNat% 189))
 (.leaf (certNat% 190)))
 (.branch 192
 (.leaf (certNat% 191))
 (.leaf (certNat% 192))))
 (.branch 195
 (.branch 194
 (.leaf (certNat% 193))
 (.leaf (certNat% 194)))
 (.branch 196
 (.leaf (certNat% 195))
 (.branch 197
 (.leaf (certNat% 196))
 (.leaf (certNat% 197)))))))
 (.branch 207
 (.branch 202
 (.branch 200
 (.branch 199
 (.leaf (certNat% 198))
 (.leaf (certNat% 199)))
 (.branch 201
 (.leaf (certNat% 200))
 (.leaf (certNat% 201))))
 (.branch 204
 (.branch 203
 (.leaf (certNat% 202))
 (.leaf (certNat% 203)))
 (.branch 205
 (.leaf (certNat% 204))
 (.branch 206
 (.leaf (certNat% 205))
 (.leaf (certNat% 206))))))
 (.branch 211
 (.branch 209
 (.branch 208
 (.leaf (certNat% 207))
 (.leaf (certNat% 208)))
 (.branch 210
 (.leaf (certNat% 209))
 (.leaf (certNat% 210))))
 (.branch 213
 (.branch 212
 (.leaf (certNat% 211))
 (.leaf (certNat% 212)))
 (.branch 214
 (.leaf (certNat% 213))
 (.branch 215
 (.leaf (certNat% 214))
 (.leaf (certNat% 215)))))))))
 (.branch 252
 (.branch 234
 (.branch 225
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
 (.branch 224
 (.leaf (certNat% 223))
 (.leaf (certNat% 224))))))
 (.branch 229
 (.branch 227
 (.branch 226
 (.leaf (certNat% 225))
 (.leaf (certNat% 226)))
 (.branch 228
 (.leaf (certNat% 227))
 (.leaf (certNat% 228))))
 (.branch 231
 (.branch 230
 (.leaf (certNat% 229))
 (.leaf (certNat% 230)))
 (.branch 232
 (.leaf (certNat% 231))
 (.branch 233
 (.leaf (certNat% 232))
 (.leaf (certNat% 233)))))))
 (.branch 243
 (.branch 238
 (.branch 236
 (.branch 235
 (.leaf (certNat% 234))
 (.leaf (certNat% 235)))
 (.branch 237
 (.leaf (certNat% 236))
 (.leaf (certNat% 237))))
 (.branch 240
 (.branch 239
 (.leaf (certNat% 238))
 (.leaf (certNat% 239)))
 (.branch 241
 (.leaf (certNat% 240))
 (.branch 242
 (.leaf (certNat% 241))
 (.leaf (certNat% 242))))))
 (.branch 247
 (.branch 245
 (.branch 244
 (.leaf (certNat% 243))
 (.leaf (certNat% 244)))
 (.branch 246
 (.leaf (certNat% 245))
 (.leaf (certNat% 246))))
 (.branch 249
 (.branch 248
 (.leaf (certNat% 247))
 (.leaf (certNat% 248)))
 (.branch 250
 (.leaf (certNat% 249))
 (.branch 251
 (.leaf (certNat% 250))
 (.leaf (certNat% 251))))))))
 (.branch 270
 (.branch 261
 (.branch 256
 (.branch 254
 (.branch 253
 (.leaf (certNat% 252))
 (.leaf (certNat% 253)))
 (.branch 255
 (.leaf (certNat% 254))
 (.leaf (certNat% 255))))
 (.branch 258
 (.branch 257
 (.leaf (certNat% 256))
 (.leaf (certNat% 257)))
 (.branch 259
 (.leaf (certNat% 258))
 (.branch 260
 (.leaf (certNat% 259))
 (.leaf (certNat% 260))))))
 (.branch 265
 (.branch 263
 (.branch 262
 (.leaf (certNat% 261))
 (.leaf (certNat% 262)))
 (.branch 264
 (.leaf (certNat% 263))
 (.leaf (certNat% 264))))
 (.branch 267
 (.branch 266
 (.leaf (certNat% 265))
 (.leaf (certNat% 266)))
 (.branch 268
 (.leaf (certNat% 267))
 (.branch 269
 (.leaf (certNat% 268))
 (.leaf (certNat% 269)))))))
 (.branch 279
 (.branch 274
 (.branch 272
 (.branch 271
 (.leaf (certNat% 270))
 (.leaf (certNat% 271)))
 (.branch 273
 (.leaf (certNat% 272))
 (.leaf (certNat% 273))))
 (.branch 276
 (.branch 275
 (.leaf (certNat% 274))
 (.leaf (certNat% 275)))
 (.branch 277
 (.leaf (certNat% 276))
 (.branch 278
 (.leaf (certNat% 277))
 (.leaf (certNat% 278))))))
 (.branch 284
 (.branch 281
 (.branch 280
 (.leaf (certNat% 279))
 (.leaf (certNat% 280)))
 (.branch 282
 (.leaf (certNat% 281))
 (.branch 283
 (.leaf (certNat% 282))
 (.leaf (certNat% 283)))))
 (.branch 286
 (.branch 285
 (.leaf (certNat% 284))
 (.leaf (certNat% 285)))
 (.branch 287
 (.leaf (certNat% 286))
 (.branch 288
 (.leaf (certNat% 287))
 (.leaf (certNat% 288)))))))))))
 (.branch 433
 (.branch 361
 (.branch 325
 (.branch 307
 (.branch 298
 (.branch 293
 (.branch 291
 (.branch 290
 (.leaf (certNat% 289))
 (.leaf (certNat% 290)))
 (.branch 292
 (.leaf (certNat% 291))
 (.leaf (certNat% 292))))
 (.branch 295
 (.branch 294
 (.leaf (certNat% 293))
 (.leaf (certNat% 294)))
 (.branch 296
 (.leaf (certNat% 295))
 (.branch 297
 (.leaf (certNat% 296))
 (.leaf (certNat% 297))))))
 (.branch 302
 (.branch 300
 (.branch 299
 (.leaf (certNat% 298))
 (.leaf (certNat% 299)))
 (.branch 301
 (.leaf (certNat% 300))
 (.leaf (certNat% 301))))
 (.branch 304
 (.branch 303
 (.leaf (certNat% 302))
 (.leaf (certNat% 303)))
 (.branch 305
 (.leaf (certNat% 304))
 (.branch 306
 (.leaf (certNat% 305))
 (.leaf (certNat% 306)))))))
 (.branch 316
 (.branch 311
 (.branch 309
 (.branch 308
 (.leaf (certNat% 307))
 (.leaf (certNat% 308)))
 (.branch 310
 (.leaf (certNat% 309))
 (.leaf (certNat% 310))))
 (.branch 313
 (.branch 312
 (.leaf (certNat% 311))
 (.leaf (certNat% 312)))
 (.branch 314
 (.leaf (certNat% 313))
 (.branch 315
 (.leaf (certNat% 314))
 (.leaf (certNat% 315))))))
 (.branch 320
 (.branch 318
 (.branch 317
 (.leaf (certNat% 316))
 (.leaf (certNat% 317)))
 (.branch 319
 (.leaf (certNat% 318))
 (.leaf (certNat% 319))))
 (.branch 322
 (.branch 321
 (.leaf (certNat% 320))
 (.leaf (certNat% 321)))
 (.branch 323
 (.leaf (certNat% 322))
 (.branch 324
 (.leaf (certNat% 323))
 (.leaf (certNat% 324))))))))
 (.branch 343
 (.branch 334
 (.branch 329
 (.branch 327
 (.branch 326
 (.leaf (certNat% 325))
 (.leaf (certNat% 326)))
 (.branch 328
 (.leaf (certNat% 327))
 (.leaf (certNat% 328))))
 (.branch 331
 (.branch 330
 (.leaf (certNat% 329))
 (.leaf (certNat% 330)))
 (.branch 332
 (.leaf (certNat% 331))
 (.branch 333
 (.leaf (certNat% 332))
 (.leaf (certNat% 333))))))
 (.branch 338
 (.branch 336
 (.branch 335
 (.leaf (certNat% 334))
 (.leaf (certNat% 335)))
 (.branch 337
 (.leaf (certNat% 336))
 (.leaf (certNat% 337))))
 (.branch 340
 (.branch 339
 (.leaf (certNat% 338))
 (.leaf (certNat% 339)))
 (.branch 341
 (.leaf (certNat% 340))
 (.branch 342
 (.leaf (certNat% 341))
 (.leaf (certNat% 342)))))))
 (.branch 352
 (.branch 347
 (.branch 345
 (.branch 344
 (.leaf (certNat% 343))
 (.leaf (certNat% 344)))
 (.branch 346
 (.leaf (certNat% 345))
 (.leaf (certNat% 346))))
 (.branch 349
 (.branch 348
 (.leaf (certNat% 347))
 (.leaf (certNat% 348)))
 (.branch 350
 (.leaf (certNat% 349))
 (.branch 351
 (.leaf (certNat% 350))
 (.leaf (certNat% 351))))))
 (.branch 356
 (.branch 354
 (.branch 353
 (.leaf (certNat% 352))
 (.leaf (certNat% 353)))
 (.branch 355
 (.leaf (certNat% 354))
 (.leaf (certNat% 355))))
 (.branch 358
 (.branch 357
 (.leaf (certNat% 356))
 (.leaf (certNat% 357)))
 (.branch 359
 (.leaf (certNat% 358))
 (.branch 360
 (.leaf (certNat% 359))
 (.leaf (certNat% 360)))))))))
 (.branch 397
 (.branch 379
 (.branch 370
 (.branch 365
 (.branch 363
 (.branch 362
 (.leaf (certNat% 361))
 (.leaf (certNat% 362)))
 (.branch 364
 (.leaf (certNat% 363))
 (.leaf (certNat% 364))))
 (.branch 367
 (.branch 366
 (.leaf (certNat% 365))
 (.leaf (certNat% 366)))
 (.branch 368
 (.leaf (certNat% 367))
 (.branch 369
 (.leaf (certNat% 368))
 (.leaf (certNat% 369))))))
 (.branch 374
 (.branch 372
 (.branch 371
 (.leaf (certNat% 370))
 (.leaf (certNat% 371)))
 (.branch 373
 (.leaf (certNat% 372))
 (.leaf (certNat% 373))))
 (.branch 376
 (.branch 375
 (.leaf (certNat% 374))
 (.leaf (certNat% 375)))
 (.branch 377
 (.leaf (certNat% 376))
 (.branch 378
 (.leaf (certNat% 377))
 (.leaf (certNat% 378)))))))
 (.branch 388
 (.branch 383
 (.branch 381
 (.branch 380
 (.leaf (certNat% 379))
 (.leaf (certNat% 380)))
 (.branch 382
 (.leaf (certNat% 381))
 (.leaf (certNat% 382))))
 (.branch 385
 (.branch 384
 (.leaf (certNat% 383))
 (.leaf (certNat% 384)))
 (.branch 386
 (.leaf (certNat% 385))
 (.branch 387
 (.leaf (certNat% 386))
 (.leaf (certNat% 387))))))
 (.branch 392
 (.branch 390
 (.branch 389
 (.leaf (certNat% 388))
 (.leaf (certNat% 389)))
 (.branch 391
 (.leaf (certNat% 390))
 (.leaf (certNat% 391))))
 (.branch 394
 (.branch 393
 (.leaf (certNat% 392))
 (.leaf (certNat% 393)))
 (.branch 395
 (.leaf (certNat% 394))
 (.branch 396
 (.leaf (certNat% 395))
 (.leaf (certNat% 396))))))))
 (.branch 415
 (.branch 406
 (.branch 401
 (.branch 399
 (.branch 398
 (.leaf (certNat% 397))
 (.leaf (certNat% 398)))
 (.branch 400
 (.leaf (certNat% 399))
 (.leaf (certNat% 400))))
 (.branch 403
 (.branch 402
 (.leaf (certNat% 401))
 (.leaf (certNat% 402)))
 (.branch 404
 (.leaf (certNat% 403))
 (.branch 405
 (.leaf (certNat% 404))
 (.leaf (certNat% 405))))))
 (.branch 410
 (.branch 408
 (.branch 407
 (.leaf (certNat% 406))
 (.leaf (certNat% 407)))
 (.branch 409
 (.leaf (certNat% 408))
 (.leaf (certNat% 409))))
 (.branch 412
 (.branch 411
 (.leaf (certNat% 410))
 (.leaf (certNat% 411)))
 (.branch 413
 (.leaf (certNat% 412))
 (.branch 414
 (.leaf (certNat% 413))
 (.leaf (certNat% 414)))))))
 (.branch 424
 (.branch 419
 (.branch 417
 (.branch 416
 (.leaf (certNat% 415))
 (.leaf (certNat% 416)))
 (.branch 418
 (.leaf (certNat% 417))
 (.leaf (certNat% 418))))
 (.branch 421
 (.branch 420
 (.leaf (certNat% 419))
 (.leaf (certNat% 420)))
 (.branch 422
 (.leaf (certNat% 421))
 (.branch 423
 (.leaf (certNat% 422))
 (.leaf (certNat% 423))))))
 (.branch 428
 (.branch 426
 (.branch 425
 (.leaf (certNat% 424))
 (.leaf (certNat% 425)))
 (.branch 427
 (.leaf (certNat% 426))
 (.leaf (certNat% 427))))
 (.branch 430
 (.branch 429
 (.leaf (certNat% 428))
 (.leaf (certNat% 429)))
 (.branch 431
 (.leaf (certNat% 430))
 (.branch 432
 (.leaf (certNat% 431))
 (.leaf (certNat% 432))))))))))
 (.branch 505
 (.branch 469
 (.branch 451
 (.branch 442
 (.branch 437
 (.branch 435
 (.branch 434
 (.leaf (certNat% 433))
 (.leaf (certNat% 434)))
 (.branch 436
 (.leaf (certNat% 435))
 (.leaf (certNat% 436))))
 (.branch 439
 (.branch 438
 (.leaf (certNat% 437))
 (.leaf (certNat% 438)))
 (.branch 440
 (.leaf (certNat% 439))
 (.branch 441
 (.leaf (certNat% 440))
 (.leaf (certNat% 441))))))
 (.branch 446
 (.branch 444
 (.branch 443
 (.leaf (certNat% 442))
 (.leaf (certNat% 443)))
 (.branch 445
 (.leaf (certNat% 444))
 (.leaf (certNat% 445))))
 (.branch 448
 (.branch 447
 (.leaf (certNat% 446))
 (.leaf (certNat% 447)))
 (.branch 449
 (.leaf (certNat% 448))
 (.branch 450
 (.leaf (certNat% 449))
 (.leaf (certNat% 450)))))))
 (.branch 460
 (.branch 455
 (.branch 453
 (.branch 452
 (.leaf (certNat% 451))
 (.leaf (certNat% 452)))
 (.branch 454
 (.leaf (certNat% 453))
 (.leaf (certNat% 454))))
 (.branch 457
 (.branch 456
 (.leaf (certNat% 455))
 (.leaf (certNat% 456)))
 (.branch 458
 (.leaf (certNat% 457))
 (.branch 459
 (.leaf (certNat% 458))
 (.leaf (certNat% 459))))))
 (.branch 464
 (.branch 462
 (.branch 461
 (.leaf (certNat% 460))
 (.leaf (certNat% 461)))
 (.branch 463
 (.leaf (certNat% 462))
 (.leaf (certNat% 463))))
 (.branch 466
 (.branch 465
 (.leaf (certNat% 464))
 (.leaf (certNat% 465)))
 (.branch 467
 (.leaf (certNat% 466))
 (.branch 468
 (.leaf (certNat% 467))
 (.leaf (certNat% 468))))))))
 (.branch 487
 (.branch 478
 (.branch 473
 (.branch 471
 (.branch 470
 (.leaf (certNat% 469))
 (.leaf (certNat% 470)))
 (.branch 472
 (.leaf (certNat% 471))
 (.leaf (certNat% 472))))
 (.branch 475
 (.branch 474
 (.leaf (certNat% 473))
 (.leaf (certNat% 474)))
 (.branch 476
 (.leaf (certNat% 475))
 (.branch 477
 (.leaf (certNat% 476))
 (.leaf (certNat% 477))))))
 (.branch 482
 (.branch 480
 (.branch 479
 (.leaf (certNat% 478))
 (.leaf (certNat% 479)))
 (.branch 481
 (.leaf (certNat% 480))
 (.leaf (certNat% 481))))
 (.branch 484
 (.branch 483
 (.leaf (certNat% 482))
 (.leaf (certNat% 483)))
 (.branch 485
 (.leaf (certNat% 484))
 (.branch 486
 (.leaf (certNat% 485))
 (.leaf (certNat% 486)))))))
 (.branch 496
 (.branch 491
 (.branch 489
 (.branch 488
 (.leaf (certNat% 487))
 (.leaf (certNat% 488)))
 (.branch 490
 (.leaf (certNat% 489))
 (.leaf (certNat% 490))))
 (.branch 493
 (.branch 492
 (.leaf (certNat% 491))
 (.leaf (certNat% 492)))
 (.branch 494
 (.leaf (certNat% 493))
 (.branch 495
 (.leaf (certNat% 494))
 (.leaf (certNat% 495))))))
 (.branch 500
 (.branch 498
 (.branch 497
 (.leaf (certNat% 496))
 (.leaf (certNat% 497)))
 (.branch 499
 (.leaf (certNat% 498))
 (.leaf (certNat% 499))))
 (.branch 502
 (.branch 501
 (.leaf (certNat% 500))
 (.leaf (certNat% 501)))
 (.branch 503
 (.leaf (certNat% 502))
 (.branch 504
 (.leaf (certNat% 503))
 (.leaf (certNat% 504)))))))))
 (.branch 541
 (.branch 523
 (.branch 514
 (.branch 509
 (.branch 507
 (.branch 506
 (.leaf (certNat% 505))
 (.leaf (certNat% 506)))
 (.branch 508
 (.leaf (certNat% 507))
 (.leaf (certNat% 508))))
 (.branch 511
 (.branch 510
 (.leaf (certNat% 509))
 (.leaf (certNat% 510)))
 (.branch 512
 (.leaf (certNat% 511))
 (.branch 513
 (.leaf (certNat% 512))
 (.leaf (certNat% 513))))))
 (.branch 518
 (.branch 516
 (.branch 515
 (.leaf (certNat% 514))
 (.leaf (certNat% 515)))
 (.branch 517
 (.leaf (certNat% 516))
 (.leaf (certNat% 517))))
 (.branch 520
 (.branch 519
 (.leaf (certNat% 518))
 (.leaf (certNat% 519)))
 (.branch 521
 (.leaf (certNat% 520))
 (.branch 522
 (.leaf (certNat% 521))
 (.leaf (certNat% 522)))))))
 (.branch 532
 (.branch 527
 (.branch 525
 (.branch 524
 (.leaf (certNat% 523))
 (.leaf (certNat% 524)))
 (.branch 526
 (.leaf (certNat% 525))
 (.leaf (certNat% 526))))
 (.branch 529
 (.branch 528
 (.leaf (certNat% 527))
 (.leaf (certNat% 528)))
 (.branch 530
 (.leaf (certNat% 529))
 (.branch 531
 (.leaf (certNat% 530))
 (.leaf (certNat% 531))))))
 (.branch 536
 (.branch 534
 (.branch 533
 (.leaf (certNat% 532))
 (.leaf (certNat% 533)))
 (.branch 535
 (.leaf (certNat% 534))
 (.leaf (certNat% 535))))
 (.branch 538
 (.branch 537
 (.leaf (certNat% 536))
 (.leaf (certNat% 537)))
 (.branch 539
 (.leaf (certNat% 538))
 (.branch 540
 (.leaf (certNat% 539))
 (.leaf (certNat% 540))))))))
 (.branch 559
 (.branch 550
 (.branch 545
 (.branch 543
 (.branch 542
 (.leaf (certNat% 541))
 (.leaf (certNat% 542)))
 (.branch 544
 (.leaf (certNat% 543))
 (.leaf (certNat% 544))))
 (.branch 547
 (.branch 546
 (.leaf (certNat% 545))
 (.leaf (certNat% 546)))
 (.branch 548
 (.leaf (certNat% 547))
 (.branch 549
 (.leaf (certNat% 548))
 (.leaf (certNat% 549))))))
 (.branch 554
 (.branch 552
 (.branch 551
 (.leaf (certNat% 550))
 (.leaf (certNat% 551)))
 (.branch 553
 (.leaf (certNat% 552))
 (.leaf (certNat% 553))))
 (.branch 556
 (.branch 555
 (.leaf (certNat% 554))
 (.leaf (certNat% 555)))
 (.branch 557
 (.leaf (certNat% 556))
 (.branch 558
 (.leaf (certNat% 557))
 (.leaf (certNat% 558)))))))
 (.branch 568
 (.branch 563
 (.branch 561
 (.branch 560
 (.leaf (certNat% 559))
 (.leaf (certNat% 560)))
 (.branch 562
 (.leaf (certNat% 561))
 (.leaf (certNat% 562))))
 (.branch 565
 (.branch 564
 (.leaf (certNat% 563))
 (.leaf (certNat% 564)))
 (.branch 566
 (.leaf (certNat% 565))
 (.branch 567
 (.leaf (certNat% 566))
 (.leaf (certNat% 567))))))
 (.branch 573
 (.branch 570
 (.branch 569
 (.leaf (certNat% 568))
 (.leaf (certNat% 569)))
 (.branch 571
 (.leaf (certNat% 570))
 (.branch 572
 (.leaf (certNat% 571))
 (.leaf (certNat% 572)))))
 (.branch 575
 (.branch 574
 (.leaf (certNat% 573))
 (.leaf (certNat% 574)))
 (.branch 576
 (.leaf (certNat% 575))
 (.branch 577
 (.leaf (certNat% 576))
 (.leaf (certNat% 577))))))))))))
def rawLeaves (i : Nat) : List Nat :=
  let code := leafTable.get i
  (PackedRawNatGrowth.readList 12 (PackedRawNatGrowth.take 5 code)
    (PackedRawNatGrowth.drop 5 code)).1

cert_leaves_4
cert_quota_5 3 0 9
cert_nodeTest_6
cert_nodeTest_sound_5
cert_leafTest_6
end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest15

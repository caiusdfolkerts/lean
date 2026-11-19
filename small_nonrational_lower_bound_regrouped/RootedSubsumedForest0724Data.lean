module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public meta import CertificateNumbers
public import RootedSixBase03GrowthCacheData
public import RootedSixBase03FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification
public import RootedSubsumedForest0724Packed000
public import RootedSubsumedForest0724Packed001
public import RootedSubsumedForest0724Packed002
public import RootedSubsumedForest0724Packed003
public import RootedSubsumedForest0724Packed004
public import RootedSubsumedForest0724Packed005
public import RootedSubsumedForest0724Packed006
public import RootedSubsumedForest0724Packed007
public import RootedSubsumedForest0724Packed008
public import RootedSubsumedForest0724Packed009
public import RootedSubsumedForest0724Packed010
public import RootedSubsumedForest0724Packed011
public import RootedSubsumedForest0724Packed012
public import RootedSubsumedForest0724Packed013
public import RootedSubsumedForest0724Packed014
public import RootedSubsumedForest0724Packed015
public import RootedSubsumedForest0724Packed016
public import RootedSubsumedForest0724Packed017
public import RootedSubsumedForest0724Packed018
public import RootedSubsumedForest0724Packed019
public import RootedSubsumedForest0724Packed020
public import RootedSubsumedForest0724Packed021
public import RootedSubsumedForest0724Packed022
public import RootedSubsumedForest0724Packed023

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 5238
abbrev nodeCount : Nat := 148746
abbrev leafCount : Nat := 3428
cert_widths_3 13 18 7 12
def blocks : Table PackedRawNatGrowth.Block :=
(.branch 600
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
 (.branch 500
 nodeBlocks009
 (.branch 550
 nodeBlocks010
 nodeBlocks011))))
 (.branch 900
 (.branch 750
 (.branch 650
 nodeBlocks012
 (.branch 700
 nodeBlocks013
 nodeBlocks014))
 (.branch 800
 nodeBlocks015
 (.branch 850
 nodeBlocks016
 nodeBlocks017)))
 (.branch 1050
 (.branch 950
 nodeBlocks018
 (.branch 1000
 nodeBlocks019
 nodeBlocks020))
 (.branch 1100
 nodeBlocks021
 (.branch 1150
 nodeBlocks022
 nodeBlocks023)))))
def counterTable : Table Nat :=
(.branch 600
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
 (.branch 500
 nodeCounters009
 (.branch 550
 nodeCounters010
 nodeCounters011))))
 (.branch 900
 (.branch 750
 (.branch 650
 nodeCounters012
 (.branch 700
 nodeCounters013
 nodeCounters014))
 (.branch 800
 nodeCounters015
 (.branch 850
 nodeCounters016
 nodeCounters017)))
 (.branch 1050
 (.branch 950
 nodeCounters018
 (.branch 1000
 nodeCounters019
 nodeCounters020))
 (.branch 1100
 nodeCounters021
 (.branch 1150
 nodeCounters022
 nodeCounters023)))))
cert_codes_3
cert_counters_3 55
cert_rawNodes_3
def leafTable : Table Nat :=
(.branch 1714
 (.branch 857
 (.branch 428
 (.branch 214
 (.branch 107
 (.branch 53
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
 (.branch 46
 (.branch 42
 (.branch 40
 (.leaf (certNat% 39))
 (.branch 41
 (.leaf (certNat% 40))
 (.leaf (certNat% 41))))
 (.branch 44
 (.branch 43
 (.leaf (certNat% 42))
 (.leaf (certNat% 43)))
 (.branch 45
 (.leaf (certNat% 44))
 (.leaf (certNat% 45)))))
 (.branch 49
 (.branch 47
 (.leaf (certNat% 46))
 (.branch 48
 (.leaf (certNat% 47))
 (.leaf (certNat% 48))))
 (.branch 51
 (.branch 50
 (.leaf (certNat% 49))
 (.leaf (certNat% 50)))
 (.branch 52
 (.leaf (certNat% 51))
 (.leaf (certNat% 52))))))))
 (.branch 80
 (.branch 66
 (.branch 59
 (.branch 56
 (.branch 54
 (.leaf (certNat% 53))
 (.branch 55
 (.leaf (certNat% 54))
 (.leaf (certNat% 55))))
 (.branch 57
 (.leaf (certNat% 56))
 (.branch 58
 (.leaf (certNat% 57))
 (.leaf (certNat% 58)))))
 (.branch 62
 (.branch 60
 (.leaf (certNat% 59))
 (.branch 61
 (.leaf (certNat% 60))
 (.leaf (certNat% 61))))
 (.branch 64
 (.branch 63
 (.leaf (certNat% 62))
 (.leaf (certNat% 63)))
 (.branch 65
 (.leaf (certNat% 64))
 (.leaf (certNat% 65))))))
 (.branch 73
 (.branch 69
 (.branch 67
 (.leaf (certNat% 66))
 (.branch 68
 (.leaf (certNat% 67))
 (.leaf (certNat% 68))))
 (.branch 71
 (.branch 70
 (.leaf (certNat% 69))
 (.leaf (certNat% 70)))
 (.branch 72
 (.leaf (certNat% 71))
 (.leaf (certNat% 72)))))
 (.branch 76
 (.branch 74
 (.leaf (certNat% 73))
 (.branch 75
 (.leaf (certNat% 74))
 (.leaf (certNat% 75))))
 (.branch 78
 (.branch 77
 (.leaf (certNat% 76))
 (.leaf (certNat% 77)))
 (.branch 79
 (.leaf (certNat% 78))
 (.leaf (certNat% 79)))))))
 (.branch 93
 (.branch 86
 (.branch 83
 (.branch 81
 (.leaf (certNat% 80))
 (.branch 82
 (.leaf (certNat% 81))
 (.leaf (certNat% 82))))
 (.branch 84
 (.leaf (certNat% 83))
 (.branch 85
 (.leaf (certNat% 84))
 (.leaf (certNat% 85)))))
 (.branch 89
 (.branch 87
 (.leaf (certNat% 86))
 (.branch 88
 (.leaf (certNat% 87))
 (.leaf (certNat% 88))))
 (.branch 91
 (.branch 90
 (.leaf (certNat% 89))
 (.leaf (certNat% 90)))
 (.branch 92
 (.leaf (certNat% 91))
 (.leaf (certNat% 92))))))
 (.branch 100
 (.branch 96
 (.branch 94
 (.leaf (certNat% 93))
 (.branch 95
 (.leaf (certNat% 94))
 (.leaf (certNat% 95))))
 (.branch 98
 (.branch 97
 (.leaf (certNat% 96))
 (.leaf (certNat% 97)))
 (.branch 99
 (.leaf (certNat% 98))
 (.leaf (certNat% 99)))))
 (.branch 103
 (.branch 101
 (.leaf (certNat% 100))
 (.branch 102
 (.leaf (certNat% 101))
 (.leaf (certNat% 102))))
 (.branch 105
 (.branch 104
 (.leaf (certNat% 103))
 (.leaf (certNat% 104)))
 (.branch 106
 (.leaf (certNat% 105))
 (.leaf (certNat% 106)))))))))
 (.branch 160
 (.branch 133
 (.branch 120
 (.branch 113
 (.branch 110
 (.branch 108
 (.leaf (certNat% 107))
 (.branch 109
 (.leaf (certNat% 108))
 (.leaf (certNat% 109))))
 (.branch 111
 (.leaf (certNat% 110))
 (.branch 112
 (.leaf (certNat% 111))
 (.leaf (certNat% 112)))))
 (.branch 116
 (.branch 114
 (.leaf (certNat% 113))
 (.branch 115
 (.leaf (certNat% 114))
 (.leaf (certNat% 115))))
 (.branch 118
 (.branch 117
 (.leaf (certNat% 116))
 (.leaf (certNat% 117)))
 (.branch 119
 (.leaf (certNat% 118))
 (.leaf (certNat% 119))))))
 (.branch 126
 (.branch 123
 (.branch 121
 (.leaf (certNat% 120))
 (.branch 122
 (.leaf (certNat% 121))
 (.leaf (certNat% 122))))
 (.branch 124
 (.leaf (certNat% 123))
 (.branch 125
 (.leaf (certNat% 124))
 (.leaf (certNat% 125)))))
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
 (.leaf (certNat% 132)))))))
 (.branch 146
 (.branch 139
 (.branch 136
 (.branch 134
 (.leaf (certNat% 133))
 (.branch 135
 (.leaf (certNat% 134))
 (.leaf (certNat% 135))))
 (.branch 137
 (.leaf (certNat% 136))
 (.branch 138
 (.leaf (certNat% 137))
 (.leaf (certNat% 138)))))
 (.branch 142
 (.branch 140
 (.leaf (certNat% 139))
 (.branch 141
 (.leaf (certNat% 140))
 (.leaf (certNat% 141))))
 (.branch 144
 (.branch 143
 (.leaf (certNat% 142))
 (.leaf (certNat% 143)))
 (.branch 145
 (.leaf (certNat% 144))
 (.leaf (certNat% 145))))))
 (.branch 153
 (.branch 149
 (.branch 147
 (.leaf (certNat% 146))
 (.branch 148
 (.leaf (certNat% 147))
 (.leaf (certNat% 148))))
 (.branch 151
 (.branch 150
 (.leaf (certNat% 149))
 (.leaf (certNat% 150)))
 (.branch 152
 (.leaf (certNat% 151))
 (.leaf (certNat% 152)))))
 (.branch 156
 (.branch 154
 (.leaf (certNat% 153))
 (.branch 155
 (.leaf (certNat% 154))
 (.leaf (certNat% 155))))
 (.branch 158
 (.branch 157
 (.leaf (certNat% 156))
 (.leaf (certNat% 157)))
 (.branch 159
 (.leaf (certNat% 158))
 (.leaf (certNat% 159))))))))
 (.branch 187
 (.branch 173
 (.branch 166
 (.branch 163
 (.branch 161
 (.leaf (certNat% 160))
 (.branch 162
 (.leaf (certNat% 161))
 (.leaf (certNat% 162))))
 (.branch 164
 (.leaf (certNat% 163))
 (.branch 165
 (.leaf (certNat% 164))
 (.leaf (certNat% 165)))))
 (.branch 169
 (.branch 167
 (.leaf (certNat% 166))
 (.branch 168
 (.leaf (certNat% 167))
 (.leaf (certNat% 168))))
 (.branch 171
 (.branch 170
 (.leaf (certNat% 169))
 (.leaf (certNat% 170)))
 (.branch 172
 (.leaf (certNat% 171))
 (.leaf (certNat% 172))))))
 (.branch 180
 (.branch 176
 (.branch 174
 (.leaf (certNat% 173))
 (.branch 175
 (.leaf (certNat% 174))
 (.leaf (certNat% 175))))
 (.branch 178
 (.branch 177
 (.leaf (certNat% 176))
 (.leaf (certNat% 177)))
 (.branch 179
 (.leaf (certNat% 178))
 (.leaf (certNat% 179)))))
 (.branch 183
 (.branch 181
 (.leaf (certNat% 180))
 (.branch 182
 (.leaf (certNat% 181))
 (.leaf (certNat% 182))))
 (.branch 185
 (.branch 184
 (.leaf (certNat% 183))
 (.leaf (certNat% 184)))
 (.branch 186
 (.leaf (certNat% 185))
 (.leaf (certNat% 186)))))))
 (.branch 200
 (.branch 193
 (.branch 190
 (.branch 188
 (.leaf (certNat% 187))
 (.branch 189
 (.leaf (certNat% 188))
 (.leaf (certNat% 189))))
 (.branch 191
 (.leaf (certNat% 190))
 (.branch 192
 (.leaf (certNat% 191))
 (.leaf (certNat% 192)))))
 (.branch 196
 (.branch 194
 (.leaf (certNat% 193))
 (.branch 195
 (.leaf (certNat% 194))
 (.leaf (certNat% 195))))
 (.branch 198
 (.branch 197
 (.leaf (certNat% 196))
 (.leaf (certNat% 197)))
 (.branch 199
 (.leaf (certNat% 198))
 (.leaf (certNat% 199))))))
 (.branch 207
 (.branch 203
 (.branch 201
 (.leaf (certNat% 200))
 (.branch 202
 (.leaf (certNat% 201))
 (.leaf (certNat% 202))))
 (.branch 205
 (.branch 204
 (.leaf (certNat% 203))
 (.leaf (certNat% 204)))
 (.branch 206
 (.leaf (certNat% 205))
 (.leaf (certNat% 206)))))
 (.branch 210
 (.branch 208
 (.leaf (certNat% 207))
 (.branch 209
 (.leaf (certNat% 208))
 (.leaf (certNat% 209))))
 (.branch 212
 (.branch 211
 (.leaf (certNat% 210))
 (.leaf (certNat% 211)))
 (.branch 213
 (.leaf (certNat% 212))
 (.leaf (certNat% 213))))))))))
 (.branch 321
 (.branch 267
 (.branch 240
 (.branch 227
 (.branch 220
 (.branch 217
 (.branch 215
 (.leaf (certNat% 214))
 (.branch 216
 (.leaf (certNat% 215))
 (.leaf (certNat% 216))))
 (.branch 218
 (.leaf (certNat% 217))
 (.branch 219
 (.leaf (certNat% 218))
 (.leaf (certNat% 219)))))
 (.branch 223
 (.branch 221
 (.leaf (certNat% 220))
 (.branch 222
 (.leaf (certNat% 221))
 (.leaf (certNat% 222))))
 (.branch 225
 (.branch 224
 (.leaf (certNat% 223))
 (.leaf (certNat% 224)))
 (.branch 226
 (.leaf (certNat% 225))
 (.leaf (certNat% 226))))))
 (.branch 233
 (.branch 230
 (.branch 228
 (.leaf (certNat% 227))
 (.branch 229
 (.leaf (certNat% 228))
 (.leaf (certNat% 229))))
 (.branch 231
 (.leaf (certNat% 230))
 (.branch 232
 (.leaf (certNat% 231))
 (.leaf (certNat% 232)))))
 (.branch 236
 (.branch 234
 (.leaf (certNat% 233))
 (.branch 235
 (.leaf (certNat% 234))
 (.leaf (certNat% 235))))
 (.branch 238
 (.branch 237
 (.leaf (certNat% 236))
 (.leaf (certNat% 237)))
 (.branch 239
 (.leaf (certNat% 238))
 (.leaf (certNat% 239)))))))
 (.branch 253
 (.branch 246
 (.branch 243
 (.branch 241
 (.leaf (certNat% 240))
 (.branch 242
 (.leaf (certNat% 241))
 (.leaf (certNat% 242))))
 (.branch 244
 (.leaf (certNat% 243))
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
 (.leaf (certNat% 252))))))
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
 (.leaf (certNat% 266))))))))
 (.branch 294
 (.branch 280
 (.branch 273
 (.branch 270
 (.branch 268
 (.leaf (certNat% 267))
 (.branch 269
 (.leaf (certNat% 268))
 (.leaf (certNat% 269))))
 (.branch 271
 (.leaf (certNat% 270))
 (.branch 272
 (.leaf (certNat% 271))
 (.leaf (certNat% 272)))))
 (.branch 276
 (.branch 274
 (.leaf (certNat% 273))
 (.branch 275
 (.leaf (certNat% 274))
 (.leaf (certNat% 275))))
 (.branch 278
 (.branch 277
 (.leaf (certNat% 276))
 (.leaf (certNat% 277)))
 (.branch 279
 (.leaf (certNat% 278))
 (.leaf (certNat% 279))))))
 (.branch 287
 (.branch 283
 (.branch 281
 (.leaf (certNat% 280))
 (.branch 282
 (.leaf (certNat% 281))
 (.leaf (certNat% 282))))
 (.branch 285
 (.branch 284
 (.leaf (certNat% 283))
 (.leaf (certNat% 284)))
 (.branch 286
 (.leaf (certNat% 285))
 (.leaf (certNat% 286)))))
 (.branch 290
 (.branch 288
 (.leaf (certNat% 287))
 (.branch 289
 (.leaf (certNat% 288))
 (.leaf (certNat% 289))))
 (.branch 292
 (.branch 291
 (.leaf (certNat% 290))
 (.leaf (certNat% 291)))
 (.branch 293
 (.leaf (certNat% 292))
 (.leaf (certNat% 293)))))))
 (.branch 307
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
 (.branch 305
 (.branch 304
 (.leaf (certNat% 303))
 (.leaf (certNat% 304)))
 (.branch 306
 (.leaf (certNat% 305))
 (.leaf (certNat% 306))))))
 (.branch 314
 (.branch 310
 (.branch 308
 (.leaf (certNat% 307))
 (.branch 309
 (.leaf (certNat% 308))
 (.leaf (certNat% 309))))
 (.branch 312
 (.branch 311
 (.leaf (certNat% 310))
 (.leaf (certNat% 311)))
 (.branch 313
 (.leaf (certNat% 312))
 (.leaf (certNat% 313)))))
 (.branch 317
 (.branch 315
 (.leaf (certNat% 314))
 (.branch 316
 (.leaf (certNat% 315))
 (.leaf (certNat% 316))))
 (.branch 319
 (.branch 318
 (.leaf (certNat% 317))
 (.leaf (certNat% 318)))
 (.branch 320
 (.leaf (certNat% 319))
 (.leaf (certNat% 320)))))))))
 (.branch 374
 (.branch 347
 (.branch 334
 (.branch 327
 (.branch 324
 (.branch 322
 (.leaf (certNat% 321))
 (.branch 323
 (.leaf (certNat% 322))
 (.leaf (certNat% 323))))
 (.branch 325
 (.leaf (certNat% 324))
 (.branch 326
 (.leaf (certNat% 325))
 (.leaf (certNat% 326)))))
 (.branch 330
 (.branch 328
 (.leaf (certNat% 327))
 (.branch 329
 (.leaf (certNat% 328))
 (.leaf (certNat% 329))))
 (.branch 332
 (.branch 331
 (.leaf (certNat% 330))
 (.leaf (certNat% 331)))
 (.branch 333
 (.leaf (certNat% 332))
 (.leaf (certNat% 333))))))
 (.branch 340
 (.branch 337
 (.branch 335
 (.leaf (certNat% 334))
 (.branch 336
 (.leaf (certNat% 335))
 (.leaf (certNat% 336))))
 (.branch 338
 (.leaf (certNat% 337))
 (.branch 339
 (.leaf (certNat% 338))
 (.leaf (certNat% 339)))))
 (.branch 343
 (.branch 341
 (.leaf (certNat% 340))
 (.branch 342
 (.leaf (certNat% 341))
 (.leaf (certNat% 342))))
 (.branch 345
 (.branch 344
 (.leaf (certNat% 343))
 (.leaf (certNat% 344)))
 (.branch 346
 (.leaf (certNat% 345))
 (.leaf (certNat% 346)))))))
 (.branch 360
 (.branch 353
 (.branch 350
 (.branch 348
 (.leaf (certNat% 347))
 (.branch 349
 (.leaf (certNat% 348))
 (.leaf (certNat% 349))))
 (.branch 351
 (.leaf (certNat% 350))
 (.branch 352
 (.leaf (certNat% 351))
 (.leaf (certNat% 352)))))
 (.branch 356
 (.branch 354
 (.leaf (certNat% 353))
 (.branch 355
 (.leaf (certNat% 354))
 (.leaf (certNat% 355))))
 (.branch 358
 (.branch 357
 (.leaf (certNat% 356))
 (.leaf (certNat% 357)))
 (.branch 359
 (.leaf (certNat% 358))
 (.leaf (certNat% 359))))))
 (.branch 367
 (.branch 363
 (.branch 361
 (.leaf (certNat% 360))
 (.branch 362
 (.leaf (certNat% 361))
 (.leaf (certNat% 362))))
 (.branch 365
 (.branch 364
 (.leaf (certNat% 363))
 (.leaf (certNat% 364)))
 (.branch 366
 (.leaf (certNat% 365))
 (.leaf (certNat% 366)))))
 (.branch 370
 (.branch 368
 (.leaf (certNat% 367))
 (.branch 369
 (.leaf (certNat% 368))
 (.leaf (certNat% 369))))
 (.branch 372
 (.branch 371
 (.leaf (certNat% 370))
 (.leaf (certNat% 371)))
 (.branch 373
 (.leaf (certNat% 372))
 (.leaf (certNat% 373))))))))
 (.branch 401
 (.branch 387
 (.branch 380
 (.branch 377
 (.branch 375
 (.leaf (certNat% 374))
 (.branch 376
 (.leaf (certNat% 375))
 (.leaf (certNat% 376))))
 (.branch 378
 (.leaf (certNat% 377))
 (.branch 379
 (.leaf (certNat% 378))
 (.leaf (certNat% 379)))))
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
 (.leaf (certNat% 386))))))
 (.branch 394
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
 (.leaf (certNat% 393)))))
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
 (.leaf (certNat% 400)))))))
 (.branch 414
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
 (.branch 412
 (.branch 411
 (.leaf (certNat% 410))
 (.leaf (certNat% 411)))
 (.branch 413
 (.leaf (certNat% 412))
 (.leaf (certNat% 413))))))
 (.branch 421
 (.branch 417
 (.branch 415
 (.leaf (certNat% 414))
 (.branch 416
 (.leaf (certNat% 415))
 (.leaf (certNat% 416))))
 (.branch 419
 (.branch 418
 (.leaf (certNat% 417))
 (.leaf (certNat% 418)))
 (.branch 420
 (.leaf (certNat% 419))
 (.leaf (certNat% 420)))))
 (.branch 424
 (.branch 422
 (.leaf (certNat% 421))
 (.branch 423
 (.leaf (certNat% 422))
 (.leaf (certNat% 423))))
 (.branch 426
 (.branch 425
 (.leaf (certNat% 424))
 (.leaf (certNat% 425)))
 (.branch 427
 (.leaf (certNat% 426))
 (.leaf (certNat% 427)))))))))))
 (.branch 642
 (.branch 535
 (.branch 481
 (.branch 454
 (.branch 441
 (.branch 434
 (.branch 431
 (.branch 429
 (.leaf (certNat% 428))
 (.branch 430
 (.leaf (certNat% 429))
 (.leaf (certNat% 430))))
 (.branch 432
 (.leaf (certNat% 431))
 (.branch 433
 (.leaf (certNat% 432))
 (.leaf (certNat% 433)))))
 (.branch 437
 (.branch 435
 (.leaf (certNat% 434))
 (.branch 436
 (.leaf (certNat% 435))
 (.leaf (certNat% 436))))
 (.branch 439
 (.branch 438
 (.leaf (certNat% 437))
 (.leaf (certNat% 438)))
 (.branch 440
 (.leaf (certNat% 439))
 (.leaf (certNat% 440))))))
 (.branch 447
 (.branch 444
 (.branch 442
 (.leaf (certNat% 441))
 (.branch 443
 (.leaf (certNat% 442))
 (.leaf (certNat% 443))))
 (.branch 445
 (.leaf (certNat% 444))
 (.branch 446
 (.leaf (certNat% 445))
 (.leaf (certNat% 446)))))
 (.branch 450
 (.branch 448
 (.leaf (certNat% 447))
 (.branch 449
 (.leaf (certNat% 448))
 (.leaf (certNat% 449))))
 (.branch 452
 (.branch 451
 (.leaf (certNat% 450))
 (.leaf (certNat% 451)))
 (.branch 453
 (.leaf (certNat% 452))
 (.leaf (certNat% 453)))))))
 (.branch 467
 (.branch 460
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
 (.leaf (certNat% 459)))))
 (.branch 463
 (.branch 461
 (.leaf (certNat% 460))
 (.branch 462
 (.leaf (certNat% 461))
 (.leaf (certNat% 462))))
 (.branch 465
 (.branch 464
 (.leaf (certNat% 463))
 (.leaf (certNat% 464)))
 (.branch 466
 (.leaf (certNat% 465))
 (.leaf (certNat% 466))))))
 (.branch 474
 (.branch 470
 (.branch 468
 (.leaf (certNat% 467))
 (.branch 469
 (.leaf (certNat% 468))
 (.leaf (certNat% 469))))
 (.branch 472
 (.branch 471
 (.leaf (certNat% 470))
 (.leaf (certNat% 471)))
 (.branch 473
 (.leaf (certNat% 472))
 (.leaf (certNat% 473)))))
 (.branch 477
 (.branch 475
 (.leaf (certNat% 474))
 (.branch 476
 (.leaf (certNat% 475))
 (.leaf (certNat% 476))))
 (.branch 479
 (.branch 478
 (.leaf (certNat% 477))
 (.leaf (certNat% 478)))
 (.branch 480
 (.leaf (certNat% 479))
 (.leaf (certNat% 480))))))))
 (.branch 508
 (.branch 494
 (.branch 487
 (.branch 484
 (.branch 482
 (.leaf (certNat% 481))
 (.branch 483
 (.leaf (certNat% 482))
 (.leaf (certNat% 483))))
 (.branch 485
 (.leaf (certNat% 484))
 (.branch 486
 (.leaf (certNat% 485))
 (.leaf (certNat% 486)))))
 (.branch 490
 (.branch 488
 (.leaf (certNat% 487))
 (.branch 489
 (.leaf (certNat% 488))
 (.leaf (certNat% 489))))
 (.branch 492
 (.branch 491
 (.leaf (certNat% 490))
 (.leaf (certNat% 491)))
 (.branch 493
 (.leaf (certNat% 492))
 (.leaf (certNat% 493))))))
 (.branch 501
 (.branch 497
 (.branch 495
 (.leaf (certNat% 494))
 (.branch 496
 (.leaf (certNat% 495))
 (.leaf (certNat% 496))))
 (.branch 499
 (.branch 498
 (.leaf (certNat% 497))
 (.leaf (certNat% 498)))
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
 (.leaf (certNat% 507)))))))
 (.branch 521
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
 (.leaf (certNat% 520))))))
 (.branch 528
 (.branch 524
 (.branch 522
 (.leaf (certNat% 521))
 (.branch 523
 (.leaf (certNat% 522))
 (.leaf (certNat% 523))))
 (.branch 526
 (.branch 525
 (.leaf (certNat% 524))
 (.leaf (certNat% 525)))
 (.branch 527
 (.leaf (certNat% 526))
 (.leaf (certNat% 527)))))
 (.branch 531
 (.branch 529
 (.leaf (certNat% 528))
 (.branch 530
 (.leaf (certNat% 529))
 (.leaf (certNat% 530))))
 (.branch 533
 (.branch 532
 (.leaf (certNat% 531))
 (.leaf (certNat% 532)))
 (.branch 534
 (.leaf (certNat% 533))
 (.leaf (certNat% 534)))))))))
 (.branch 588
 (.branch 561
 (.branch 548
 (.branch 541
 (.branch 538
 (.branch 536
 (.leaf (certNat% 535))
 (.branch 537
 (.leaf (certNat% 536))
 (.leaf (certNat% 537))))
 (.branch 539
 (.leaf (certNat% 538))
 (.branch 540
 (.leaf (certNat% 539))
 (.leaf (certNat% 540)))))
 (.branch 544
 (.branch 542
 (.leaf (certNat% 541))
 (.branch 543
 (.leaf (certNat% 542))
 (.leaf (certNat% 543))))
 (.branch 546
 (.branch 545
 (.leaf (certNat% 544))
 (.leaf (certNat% 545)))
 (.branch 547
 (.leaf (certNat% 546))
 (.leaf (certNat% 547))))))
 (.branch 554
 (.branch 551
 (.branch 549
 (.leaf (certNat% 548))
 (.branch 550
 (.leaf (certNat% 549))
 (.leaf (certNat% 550))))
 (.branch 552
 (.leaf (certNat% 551))
 (.branch 553
 (.leaf (certNat% 552))
 (.leaf (certNat% 553)))))
 (.branch 557
 (.branch 555
 (.leaf (certNat% 554))
 (.branch 556
 (.leaf (certNat% 555))
 (.leaf (certNat% 556))))
 (.branch 559
 (.branch 558
 (.leaf (certNat% 557))
 (.leaf (certNat% 558)))
 (.branch 560
 (.leaf (certNat% 559))
 (.leaf (certNat% 560)))))))
 (.branch 574
 (.branch 567
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
 (.leaf (certNat% 566)))))
 (.branch 570
 (.branch 568
 (.leaf (certNat% 567))
 (.branch 569
 (.leaf (certNat% 568))
 (.leaf (certNat% 569))))
 (.branch 572
 (.branch 571
 (.leaf (certNat% 570))
 (.leaf (certNat% 571)))
 (.branch 573
 (.leaf (certNat% 572))
 (.leaf (certNat% 573))))))
 (.branch 581
 (.branch 577
 (.branch 575
 (.leaf (certNat% 574))
 (.branch 576
 (.leaf (certNat% 575))
 (.leaf (certNat% 576))))
 (.branch 579
 (.branch 578
 (.leaf (certNat% 577))
 (.leaf (certNat% 578)))
 (.branch 580
 (.leaf (certNat% 579))
 (.leaf (certNat% 580)))))
 (.branch 584
 (.branch 582
 (.leaf (certNat% 581))
 (.branch 583
 (.leaf (certNat% 582))
 (.leaf (certNat% 583))))
 (.branch 586
 (.branch 585
 (.leaf (certNat% 584))
 (.leaf (certNat% 585)))
 (.branch 587
 (.leaf (certNat% 586))
 (.leaf (certNat% 587))))))))
 (.branch 615
 (.branch 601
 (.branch 594
 (.branch 591
 (.branch 589
 (.leaf (certNat% 588))
 (.branch 590
 (.leaf (certNat% 589))
 (.leaf (certNat% 590))))
 (.branch 592
 (.leaf (certNat% 591))
 (.branch 593
 (.leaf (certNat% 592))
 (.leaf (certNat% 593)))))
 (.branch 597
 (.branch 595
 (.leaf (certNat% 594))
 (.branch 596
 (.leaf (certNat% 595))
 (.leaf (certNat% 596))))
 (.branch 599
 (.branch 598
 (.leaf (certNat% 597))
 (.leaf (certNat% 598)))
 (.branch 600
 (.leaf (certNat% 599))
 (.leaf (certNat% 600))))))
 (.branch 608
 (.branch 604
 (.branch 602
 (.leaf (certNat% 601))
 (.branch 603
 (.leaf (certNat% 602))
 (.leaf (certNat% 603))))
 (.branch 606
 (.branch 605
 (.leaf (certNat% 604))
 (.leaf (certNat% 605)))
 (.branch 607
 (.leaf (certNat% 606))
 (.leaf (certNat% 607)))))
 (.branch 611
 (.branch 609
 (.leaf (certNat% 608))
 (.branch 610
 (.leaf (certNat% 609))
 (.leaf (certNat% 610))))
 (.branch 613
 (.branch 612
 (.leaf (certNat% 611))
 (.leaf (certNat% 612)))
 (.branch 614
 (.leaf (certNat% 613))
 (.leaf (certNat% 614)))))))
 (.branch 628
 (.branch 621
 (.branch 618
 (.branch 616
 (.leaf (certNat% 615))
 (.branch 617
 (.leaf (certNat% 616))
 (.leaf (certNat% 617))))
 (.branch 619
 (.leaf (certNat% 618))
 (.branch 620
 (.leaf (certNat% 619))
 (.leaf (certNat% 620)))))
 (.branch 624
 (.branch 622
 (.leaf (certNat% 621))
 (.branch 623
 (.leaf (certNat% 622))
 (.leaf (certNat% 623))))
 (.branch 626
 (.branch 625
 (.leaf (certNat% 624))
 (.leaf (certNat% 625)))
 (.branch 627
 (.leaf (certNat% 626))
 (.leaf (certNat% 627))))))
 (.branch 635
 (.branch 631
 (.branch 629
 (.leaf (certNat% 628))
 (.branch 630
 (.leaf (certNat% 629))
 (.leaf (certNat% 630))))
 (.branch 633
 (.branch 632
 (.leaf (certNat% 631))
 (.leaf (certNat% 632)))
 (.branch 634
 (.leaf (certNat% 633))
 (.leaf (certNat% 634)))))
 (.branch 638
 (.branch 636
 (.leaf (certNat% 635))
 (.branch 637
 (.leaf (certNat% 636))
 (.leaf (certNat% 637))))
 (.branch 640
 (.branch 639
 (.leaf (certNat% 638))
 (.leaf (certNat% 639)))
 (.branch 641
 (.leaf (certNat% 640))
 (.leaf (certNat% 641))))))))))
 (.branch 749
 (.branch 695
 (.branch 668
 (.branch 655
 (.branch 648
 (.branch 645
 (.branch 643
 (.leaf (certNat% 642))
 (.branch 644
 (.leaf (certNat% 643))
 (.leaf (certNat% 644))))
 (.branch 646
 (.leaf (certNat% 645))
 (.branch 647
 (.leaf (certNat% 646))
 (.leaf (certNat% 647)))))
 (.branch 651
 (.branch 649
 (.leaf (certNat% 648))
 (.branch 650
 (.leaf (certNat% 649))
 (.leaf (certNat% 650))))
 (.branch 653
 (.branch 652
 (.leaf (certNat% 651))
 (.leaf (certNat% 652)))
 (.branch 654
 (.leaf (certNat% 653))
 (.leaf (certNat% 654))))))
 (.branch 661
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
 (.leaf (certNat% 660)))))
 (.branch 664
 (.branch 662
 (.leaf (certNat% 661))
 (.branch 663
 (.leaf (certNat% 662))
 (.leaf (certNat% 663))))
 (.branch 666
 (.branch 665
 (.leaf (certNat% 664))
 (.leaf (certNat% 665)))
 (.branch 667
 (.leaf (certNat% 666))
 (.leaf (certNat% 667)))))))
 (.branch 681
 (.branch 674
 (.branch 671
 (.branch 669
 (.leaf (certNat% 668))
 (.branch 670
 (.leaf (certNat% 669))
 (.leaf (certNat% 670))))
 (.branch 672
 (.leaf (certNat% 671))
 (.branch 673
 (.leaf (certNat% 672))
 (.leaf (certNat% 673)))))
 (.branch 677
 (.branch 675
 (.leaf (certNat% 674))
 (.branch 676
 (.leaf (certNat% 675))
 (.leaf (certNat% 676))))
 (.branch 679
 (.branch 678
 (.leaf (certNat% 677))
 (.leaf (certNat% 678)))
 (.branch 680
 (.leaf (certNat% 679))
 (.leaf (certNat% 680))))))
 (.branch 688
 (.branch 684
 (.branch 682
 (.leaf (certNat% 681))
 (.branch 683
 (.leaf (certNat% 682))
 (.leaf (certNat% 683))))
 (.branch 686
 (.branch 685
 (.leaf (certNat% 684))
 (.leaf (certNat% 685)))
 (.branch 687
 (.leaf (certNat% 686))
 (.leaf (certNat% 687)))))
 (.branch 691
 (.branch 689
 (.leaf (certNat% 688))
 (.branch 690
 (.leaf (certNat% 689))
 (.leaf (certNat% 690))))
 (.branch 693
 (.branch 692
 (.leaf (certNat% 691))
 (.leaf (certNat% 692)))
 (.branch 694
 (.leaf (certNat% 693))
 (.leaf (certNat% 694))))))))
 (.branch 722
 (.branch 708
 (.branch 701
 (.branch 698
 (.branch 696
 (.leaf (certNat% 695))
 (.branch 697
 (.leaf (certNat% 696))
 (.leaf (certNat% 697))))
 (.branch 699
 (.leaf (certNat% 698))
 (.branch 700
 (.leaf (certNat% 699))
 (.leaf (certNat% 700)))))
 (.branch 704
 (.branch 702
 (.leaf (certNat% 701))
 (.branch 703
 (.leaf (certNat% 702))
 (.leaf (certNat% 703))))
 (.branch 706
 (.branch 705
 (.leaf (certNat% 704))
 (.leaf (certNat% 705)))
 (.branch 707
 (.leaf (certNat% 706))
 (.leaf (certNat% 707))))))
 (.branch 715
 (.branch 711
 (.branch 709
 (.leaf (certNat% 708))
 (.branch 710
 (.leaf (certNat% 709))
 (.leaf (certNat% 710))))
 (.branch 713
 (.branch 712
 (.leaf (certNat% 711))
 (.leaf (certNat% 712)))
 (.branch 714
 (.leaf (certNat% 713))
 (.leaf (certNat% 714)))))
 (.branch 718
 (.branch 716
 (.leaf (certNat% 715))
 (.branch 717
 (.leaf (certNat% 716))
 (.leaf (certNat% 717))))
 (.branch 720
 (.branch 719
 (.leaf (certNat% 718))
 (.leaf (certNat% 719)))
 (.branch 721
 (.leaf (certNat% 720))
 (.leaf (certNat% 721)))))))
 (.branch 735
 (.branch 728
 (.branch 725
 (.branch 723
 (.leaf (certNat% 722))
 (.branch 724
 (.leaf (certNat% 723))
 (.leaf (certNat% 724))))
 (.branch 726
 (.leaf (certNat% 725))
 (.branch 727
 (.leaf (certNat% 726))
 (.leaf (certNat% 727)))))
 (.branch 731
 (.branch 729
 (.leaf (certNat% 728))
 (.branch 730
 (.leaf (certNat% 729))
 (.leaf (certNat% 730))))
 (.branch 733
 (.branch 732
 (.leaf (certNat% 731))
 (.leaf (certNat% 732)))
 (.branch 734
 (.leaf (certNat% 733))
 (.leaf (certNat% 734))))))
 (.branch 742
 (.branch 738
 (.branch 736
 (.leaf (certNat% 735))
 (.branch 737
 (.leaf (certNat% 736))
 (.leaf (certNat% 737))))
 (.branch 740
 (.branch 739
 (.leaf (certNat% 738))
 (.leaf (certNat% 739)))
 (.branch 741
 (.leaf (certNat% 740))
 (.leaf (certNat% 741)))))
 (.branch 745
 (.branch 743
 (.leaf (certNat% 742))
 (.branch 744
 (.leaf (certNat% 743))
 (.leaf (certNat% 744))))
 (.branch 747
 (.branch 746
 (.leaf (certNat% 745))
 (.leaf (certNat% 746)))
 (.branch 748
 (.leaf (certNat% 747))
 (.leaf (certNat% 748)))))))))
 (.branch 803
 (.branch 776
 (.branch 762
 (.branch 755
 (.branch 752
 (.branch 750
 (.leaf (certNat% 749))
 (.branch 751
 (.leaf (certNat% 750))
 (.leaf (certNat% 751))))
 (.branch 753
 (.leaf (certNat% 752))
 (.branch 754
 (.leaf (certNat% 753))
 (.leaf (certNat% 754)))))
 (.branch 758
 (.branch 756
 (.leaf (certNat% 755))
 (.branch 757
 (.leaf (certNat% 756))
 (.leaf (certNat% 757))))
 (.branch 760
 (.branch 759
 (.leaf (certNat% 758))
 (.leaf (certNat% 759)))
 (.branch 761
 (.leaf (certNat% 760))
 (.leaf (certNat% 761))))))
 (.branch 769
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
 (.leaf (certNat% 768)))))
 (.branch 772
 (.branch 770
 (.leaf (certNat% 769))
 (.branch 771
 (.leaf (certNat% 770))
 (.leaf (certNat% 771))))
 (.branch 774
 (.branch 773
 (.leaf (certNat% 772))
 (.leaf (certNat% 773)))
 (.branch 775
 (.leaf (certNat% 774))
 (.leaf (certNat% 775)))))))
 (.branch 789
 (.branch 782
 (.branch 779
 (.branch 777
 (.leaf (certNat% 776))
 (.branch 778
 (.leaf (certNat% 777))
 (.leaf (certNat% 778))))
 (.branch 780
 (.leaf (certNat% 779))
 (.branch 781
 (.leaf (certNat% 780))
 (.leaf (certNat% 781)))))
 (.branch 785
 (.branch 783
 (.leaf (certNat% 782))
 (.branch 784
 (.leaf (certNat% 783))
 (.leaf (certNat% 784))))
 (.branch 787
 (.branch 786
 (.leaf (certNat% 785))
 (.leaf (certNat% 786)))
 (.branch 788
 (.leaf (certNat% 787))
 (.leaf (certNat% 788))))))
 (.branch 796
 (.branch 792
 (.branch 790
 (.leaf (certNat% 789))
 (.branch 791
 (.leaf (certNat% 790))
 (.leaf (certNat% 791))))
 (.branch 794
 (.branch 793
 (.leaf (certNat% 792))
 (.leaf (certNat% 793)))
 (.branch 795
 (.leaf (certNat% 794))
 (.leaf (certNat% 795)))))
 (.branch 799
 (.branch 797
 (.leaf (certNat% 796))
 (.branch 798
 (.leaf (certNat% 797))
 (.leaf (certNat% 798))))
 (.branch 801
 (.branch 800
 (.leaf (certNat% 799))
 (.leaf (certNat% 800)))
 (.branch 802
 (.leaf (certNat% 801))
 (.leaf (certNat% 802))))))))
 (.branch 830
 (.branch 816
 (.branch 809
 (.branch 806
 (.branch 804
 (.leaf (certNat% 803))
 (.branch 805
 (.leaf (certNat% 804))
 (.leaf (certNat% 805))))
 (.branch 807
 (.leaf (certNat% 806))
 (.branch 808
 (.leaf (certNat% 807))
 (.leaf (certNat% 808)))))
 (.branch 812
 (.branch 810
 (.leaf (certNat% 809))
 (.branch 811
 (.leaf (certNat% 810))
 (.leaf (certNat% 811))))
 (.branch 814
 (.branch 813
 (.leaf (certNat% 812))
 (.leaf (certNat% 813)))
 (.branch 815
 (.leaf (certNat% 814))
 (.leaf (certNat% 815))))))
 (.branch 823
 (.branch 819
 (.branch 817
 (.leaf (certNat% 816))
 (.branch 818
 (.leaf (certNat% 817))
 (.leaf (certNat% 818))))
 (.branch 821
 (.branch 820
 (.leaf (certNat% 819))
 (.leaf (certNat% 820)))
 (.branch 822
 (.leaf (certNat% 821))
 (.leaf (certNat% 822)))))
 (.branch 826
 (.branch 824
 (.leaf (certNat% 823))
 (.branch 825
 (.leaf (certNat% 824))
 (.leaf (certNat% 825))))
 (.branch 828
 (.branch 827
 (.leaf (certNat% 826))
 (.leaf (certNat% 827)))
 (.branch 829
 (.leaf (certNat% 828))
 (.leaf (certNat% 829)))))))
 (.branch 843
 (.branch 836
 (.branch 833
 (.branch 831
 (.leaf (certNat% 830))
 (.branch 832
 (.leaf (certNat% 831))
 (.leaf (certNat% 832))))
 (.branch 834
 (.leaf (certNat% 833))
 (.branch 835
 (.leaf (certNat% 834))
 (.leaf (certNat% 835)))))
 (.branch 839
 (.branch 837
 (.leaf (certNat% 836))
 (.branch 838
 (.leaf (certNat% 837))
 (.leaf (certNat% 838))))
 (.branch 841
 (.branch 840
 (.leaf (certNat% 839))
 (.leaf (certNat% 840)))
 (.branch 842
 (.leaf (certNat% 841))
 (.leaf (certNat% 842))))))
 (.branch 850
 (.branch 846
 (.branch 844
 (.leaf (certNat% 843))
 (.branch 845
 (.leaf (certNat% 844))
 (.leaf (certNat% 845))))
 (.branch 848
 (.branch 847
 (.leaf (certNat% 846))
 (.leaf (certNat% 847)))
 (.branch 849
 (.leaf (certNat% 848))
 (.leaf (certNat% 849)))))
 (.branch 853
 (.branch 851
 (.leaf (certNat% 850))
 (.branch 852
 (.leaf (certNat% 851))
 (.leaf (certNat% 852))))
 (.branch 855
 (.branch 854
 (.leaf (certNat% 853))
 (.leaf (certNat% 854)))
 (.branch 856
 (.leaf (certNat% 855))
 (.leaf (certNat% 856))))))))))))
 (.branch 1285
 (.branch 1071
 (.branch 964
 (.branch 910
 (.branch 883
 (.branch 870
 (.branch 863
 (.branch 860
 (.branch 858
 (.leaf (certNat% 857))
 (.branch 859
 (.leaf (certNat% 858))
 (.leaf (certNat% 859))))
 (.branch 861
 (.leaf (certNat% 860))
 (.branch 862
 (.leaf (certNat% 861))
 (.leaf (certNat% 862)))))
 (.branch 866
 (.branch 864
 (.leaf (certNat% 863))
 (.branch 865
 (.leaf (certNat% 864))
 (.leaf (certNat% 865))))
 (.branch 868
 (.branch 867
 (.leaf (certNat% 866))
 (.leaf (certNat% 867)))
 (.branch 869
 (.leaf (certNat% 868))
 (.leaf (certNat% 869))))))
 (.branch 876
 (.branch 873
 (.branch 871
 (.leaf (certNat% 870))
 (.branch 872
 (.leaf (certNat% 871))
 (.leaf (certNat% 872))))
 (.branch 874
 (.leaf (certNat% 873))
 (.branch 875
 (.leaf (certNat% 874))
 (.leaf (certNat% 875)))))
 (.branch 879
 (.branch 877
 (.leaf (certNat% 876))
 (.branch 878
 (.leaf (certNat% 877))
 (.leaf (certNat% 878))))
 (.branch 881
 (.branch 880
 (.leaf (certNat% 879))
 (.leaf (certNat% 880)))
 (.branch 882
 (.leaf (certNat% 881))
 (.leaf (certNat% 882)))))))
 (.branch 896
 (.branch 889
 (.branch 886
 (.branch 884
 (.leaf (certNat% 883))
 (.branch 885
 (.leaf (certNat% 884))
 (.leaf (certNat% 885))))
 (.branch 887
 (.leaf (certNat% 886))
 (.branch 888
 (.leaf (certNat% 887))
 (.leaf (certNat% 888)))))
 (.branch 892
 (.branch 890
 (.leaf (certNat% 889))
 (.branch 891
 (.leaf (certNat% 890))
 (.leaf (certNat% 891))))
 (.branch 894
 (.branch 893
 (.leaf (certNat% 892))
 (.leaf (certNat% 893)))
 (.branch 895
 (.leaf (certNat% 894))
 (.leaf (certNat% 895))))))
 (.branch 903
 (.branch 899
 (.branch 897
 (.leaf (certNat% 896))
 (.branch 898
 (.leaf (certNat% 897))
 (.leaf (certNat% 898))))
 (.branch 901
 (.branch 900
 (.leaf (certNat% 899))
 (.leaf (certNat% 900)))
 (.branch 902
 (.leaf (certNat% 901))
 (.leaf (certNat% 902)))))
 (.branch 906
 (.branch 904
 (.leaf (certNat% 903))
 (.branch 905
 (.leaf (certNat% 904))
 (.leaf (certNat% 905))))
 (.branch 908
 (.branch 907
 (.leaf (certNat% 906))
 (.leaf (certNat% 907)))
 (.branch 909
 (.leaf (certNat% 908))
 (.leaf (certNat% 909))))))))
 (.branch 937
 (.branch 923
 (.branch 916
 (.branch 913
 (.branch 911
 (.leaf (certNat% 910))
 (.branch 912
 (.leaf (certNat% 911))
 (.leaf (certNat% 912))))
 (.branch 914
 (.leaf (certNat% 913))
 (.branch 915
 (.leaf (certNat% 914))
 (.leaf (certNat% 915)))))
 (.branch 919
 (.branch 917
 (.leaf (certNat% 916))
 (.branch 918
 (.leaf (certNat% 917))
 (.leaf (certNat% 918))))
 (.branch 921
 (.branch 920
 (.leaf (certNat% 919))
 (.leaf (certNat% 920)))
 (.branch 922
 (.leaf (certNat% 921))
 (.leaf (certNat% 922))))))
 (.branch 930
 (.branch 926
 (.branch 924
 (.leaf (certNat% 923))
 (.branch 925
 (.leaf (certNat% 924))
 (.leaf (certNat% 925))))
 (.branch 928
 (.branch 927
 (.leaf (certNat% 926))
 (.leaf (certNat% 927)))
 (.branch 929
 (.leaf (certNat% 928))
 (.leaf (certNat% 929)))))
 (.branch 933
 (.branch 931
 (.leaf (certNat% 930))
 (.branch 932
 (.leaf (certNat% 931))
 (.leaf (certNat% 932))))
 (.branch 935
 (.branch 934
 (.leaf (certNat% 933))
 (.leaf (certNat% 934)))
 (.branch 936
 (.leaf (certNat% 935))
 (.leaf (certNat% 936)))))))
 (.branch 950
 (.branch 943
 (.branch 940
 (.branch 938
 (.leaf (certNat% 937))
 (.branch 939
 (.leaf (certNat% 938))
 (.leaf (certNat% 939))))
 (.branch 941
 (.leaf (certNat% 940))
 (.branch 942
 (.leaf (certNat% 941))
 (.leaf (certNat% 942)))))
 (.branch 946
 (.branch 944
 (.leaf (certNat% 943))
 (.branch 945
 (.leaf (certNat% 944))
 (.leaf (certNat% 945))))
 (.branch 948
 (.branch 947
 (.leaf (certNat% 946))
 (.leaf (certNat% 947)))
 (.branch 949
 (.leaf (certNat% 948))
 (.leaf (certNat% 949))))))
 (.branch 957
 (.branch 953
 (.branch 951
 (.leaf (certNat% 950))
 (.branch 952
 (.leaf (certNat% 951))
 (.leaf (certNat% 952))))
 (.branch 955
 (.branch 954
 (.leaf (certNat% 953))
 (.leaf (certNat% 954)))
 (.branch 956
 (.leaf (certNat% 955))
 (.leaf (certNat% 956)))))
 (.branch 960
 (.branch 958
 (.leaf (certNat% 957))
 (.branch 959
 (.leaf (certNat% 958))
 (.leaf (certNat% 959))))
 (.branch 962
 (.branch 961
 (.leaf (certNat% 960))
 (.leaf (certNat% 961)))
 (.branch 963
 (.leaf (certNat% 962))
 (.leaf (certNat% 963)))))))))
 (.branch 1017
 (.branch 990
 (.branch 977
 (.branch 970
 (.branch 967
 (.branch 965
 (.leaf (certNat% 964))
 (.branch 966
 (.leaf (certNat% 965))
 (.leaf (certNat% 966))))
 (.branch 968
 (.leaf (certNat% 967))
 (.branch 969
 (.leaf (certNat% 968))
 (.leaf (certNat% 969)))))
 (.branch 973
 (.branch 971
 (.leaf (certNat% 970))
 (.branch 972
 (.leaf (certNat% 971))
 (.leaf (certNat% 972))))
 (.branch 975
 (.branch 974
 (.leaf (certNat% 973))
 (.leaf (certNat% 974)))
 (.branch 976
 (.leaf (certNat% 975))
 (.leaf (certNat% 976))))))
 (.branch 983
 (.branch 980
 (.branch 978
 (.leaf (certNat% 977))
 (.branch 979
 (.leaf (certNat% 978))
 (.leaf (certNat% 979))))
 (.branch 981
 (.leaf (certNat% 980))
 (.branch 982
 (.leaf (certNat% 981))
 (.leaf (certNat% 982)))))
 (.branch 986
 (.branch 984
 (.leaf (certNat% 983))
 (.branch 985
 (.leaf (certNat% 984))
 (.leaf (certNat% 985))))
 (.branch 988
 (.branch 987
 (.leaf (certNat% 986))
 (.leaf (certNat% 987)))
 (.branch 989
 (.leaf (certNat% 988))
 (.leaf (certNat% 989)))))))
 (.branch 1003
 (.branch 996
 (.branch 993
 (.branch 991
 (.leaf (certNat% 990))
 (.branch 992
 (.leaf (certNat% 991))
 (.leaf (certNat% 992))))
 (.branch 994
 (.leaf (certNat% 993))
 (.branch 995
 (.leaf (certNat% 994))
 (.leaf (certNat% 995)))))
 (.branch 999
 (.branch 997
 (.leaf (certNat% 996))
 (.branch 998
 (.leaf (certNat% 997))
 (.leaf (certNat% 998))))
 (.branch 1001
 (.branch 1000
 (.leaf (certNat% 999))
 (.leaf (certNat% 1000)))
 (.branch 1002
 (.leaf (certNat% 1001))
 (.leaf (certNat% 1002))))))
 (.branch 1010
 (.branch 1006
 (.branch 1004
 (.leaf (certNat% 1003))
 (.branch 1005
 (.leaf (certNat% 1004))
 (.leaf (certNat% 1005))))
 (.branch 1008
 (.branch 1007
 (.leaf (certNat% 1006))
 (.leaf (certNat% 1007)))
 (.branch 1009
 (.leaf (certNat% 1008))
 (.leaf (certNat% 1009)))))
 (.branch 1013
 (.branch 1011
 (.leaf (certNat% 1010))
 (.branch 1012
 (.leaf (certNat% 1011))
 (.leaf (certNat% 1012))))
 (.branch 1015
 (.branch 1014
 (.leaf (certNat% 1013))
 (.leaf (certNat% 1014)))
 (.branch 1016
 (.leaf (certNat% 1015))
 (.leaf (certNat% 1016))))))))
 (.branch 1044
 (.branch 1030
 (.branch 1023
 (.branch 1020
 (.branch 1018
 (.leaf (certNat% 1017))
 (.branch 1019
 (.leaf (certNat% 1018))
 (.leaf (certNat% 1019))))
 (.branch 1021
 (.leaf (certNat% 1020))
 (.branch 1022
 (.leaf (certNat% 1021))
 (.leaf (certNat% 1022)))))
 (.branch 1026
 (.branch 1024
 (.leaf (certNat% 1023))
 (.branch 1025
 (.leaf (certNat% 1024))
 (.leaf (certNat% 1025))))
 (.branch 1028
 (.branch 1027
 (.leaf (certNat% 1026))
 (.leaf (certNat% 1027)))
 (.branch 1029
 (.leaf (certNat% 1028))
 (.leaf (certNat% 1029))))))
 (.branch 1037
 (.branch 1033
 (.branch 1031
 (.leaf (certNat% 1030))
 (.branch 1032
 (.leaf (certNat% 1031))
 (.leaf (certNat% 1032))))
 (.branch 1035
 (.branch 1034
 (.leaf (certNat% 1033))
 (.leaf (certNat% 1034)))
 (.branch 1036
 (.leaf (certNat% 1035))
 (.leaf (certNat% 1036)))))
 (.branch 1040
 (.branch 1038
 (.leaf (certNat% 1037))
 (.branch 1039
 (.leaf (certNat% 1038))
 (.leaf (certNat% 1039))))
 (.branch 1042
 (.branch 1041
 (.leaf (certNat% 1040))
 (.leaf (certNat% 1041)))
 (.branch 1043
 (.leaf (certNat% 1042))
 (.leaf (certNat% 1043)))))))
 (.branch 1057
 (.branch 1050
 (.branch 1047
 (.branch 1045
 (.leaf (certNat% 1044))
 (.branch 1046
 (.leaf (certNat% 1045))
 (.leaf (certNat% 1046))))
 (.branch 1048
 (.leaf (certNat% 1047))
 (.branch 1049
 (.leaf (certNat% 1048))
 (.leaf (certNat% 1049)))))
 (.branch 1053
 (.branch 1051
 (.leaf (certNat% 1050))
 (.branch 1052
 (.leaf (certNat% 1051))
 (.leaf (certNat% 1052))))
 (.branch 1055
 (.branch 1054
 (.leaf (certNat% 1053))
 (.leaf (certNat% 1054)))
 (.branch 1056
 (.leaf (certNat% 1055))
 (.leaf (certNat% 1056))))))
 (.branch 1064
 (.branch 1060
 (.branch 1058
 (.leaf (certNat% 1057))
 (.branch 1059
 (.leaf (certNat% 1058))
 (.leaf (certNat% 1059))))
 (.branch 1062
 (.branch 1061
 (.leaf (certNat% 1060))
 (.leaf (certNat% 1061)))
 (.branch 1063
 (.leaf (certNat% 1062))
 (.leaf (certNat% 1063)))))
 (.branch 1067
 (.branch 1065
 (.leaf (certNat% 1064))
 (.branch 1066
 (.leaf (certNat% 1065))
 (.leaf (certNat% 1066))))
 (.branch 1069
 (.branch 1068
 (.leaf (certNat% 1067))
 (.leaf (certNat% 1068)))
 (.branch 1070
 (.leaf (certNat% 1069))
 (.leaf (certNat% 1070))))))))))
 (.branch 1178
 (.branch 1124
 (.branch 1097
 (.branch 1084
 (.branch 1077
 (.branch 1074
 (.branch 1072
 (.leaf (certNat% 1071))
 (.branch 1073
 (.leaf (certNat% 1072))
 (.leaf (certNat% 1073))))
 (.branch 1075
 (.leaf (certNat% 1074))
 (.branch 1076
 (.leaf (certNat% 1075))
 (.leaf (certNat% 1076)))))
 (.branch 1080
 (.branch 1078
 (.leaf (certNat% 1077))
 (.branch 1079
 (.leaf (certNat% 1078))
 (.leaf (certNat% 1079))))
 (.branch 1082
 (.branch 1081
 (.leaf (certNat% 1080))
 (.leaf (certNat% 1081)))
 (.branch 1083
 (.leaf (certNat% 1082))
 (.leaf (certNat% 1083))))))
 (.branch 1090
 (.branch 1087
 (.branch 1085
 (.leaf (certNat% 1084))
 (.branch 1086
 (.leaf (certNat% 1085))
 (.leaf (certNat% 1086))))
 (.branch 1088
 (.leaf (certNat% 1087))
 (.branch 1089
 (.leaf (certNat% 1088))
 (.leaf (certNat% 1089)))))
 (.branch 1093
 (.branch 1091
 (.leaf (certNat% 1090))
 (.branch 1092
 (.leaf (certNat% 1091))
 (.leaf (certNat% 1092))))
 (.branch 1095
 (.branch 1094
 (.leaf (certNat% 1093))
 (.leaf (certNat% 1094)))
 (.branch 1096
 (.leaf (certNat% 1095))
 (.leaf (certNat% 1096)))))))
 (.branch 1110
 (.branch 1103
 (.branch 1100
 (.branch 1098
 (.leaf (certNat% 1097))
 (.branch 1099
 (.leaf (certNat% 1098))
 (.leaf (certNat% 1099))))
 (.branch 1101
 (.leaf (certNat% 1100))
 (.branch 1102
 (.leaf (certNat% 1101))
 (.leaf (certNat% 1102)))))
 (.branch 1106
 (.branch 1104
 (.leaf (certNat% 1103))
 (.branch 1105
 (.leaf (certNat% 1104))
 (.leaf (certNat% 1105))))
 (.branch 1108
 (.branch 1107
 (.leaf (certNat% 1106))
 (.leaf (certNat% 1107)))
 (.branch 1109
 (.leaf (certNat% 1108))
 (.leaf (certNat% 1109))))))
 (.branch 1117
 (.branch 1113
 (.branch 1111
 (.leaf (certNat% 1110))
 (.branch 1112
 (.leaf (certNat% 1111))
 (.leaf (certNat% 1112))))
 (.branch 1115
 (.branch 1114
 (.leaf (certNat% 1113))
 (.leaf (certNat% 1114)))
 (.branch 1116
 (.leaf (certNat% 1115))
 (.leaf (certNat% 1116)))))
 (.branch 1120
 (.branch 1118
 (.leaf (certNat% 1117))
 (.branch 1119
 (.leaf (certNat% 1118))
 (.leaf (certNat% 1119))))
 (.branch 1122
 (.branch 1121
 (.leaf (certNat% 1120))
 (.leaf (certNat% 1121)))
 (.branch 1123
 (.leaf (certNat% 1122))
 (.leaf (certNat% 1123))))))))
 (.branch 1151
 (.branch 1137
 (.branch 1130
 (.branch 1127
 (.branch 1125
 (.leaf (certNat% 1124))
 (.branch 1126
 (.leaf (certNat% 1125))
 (.leaf (certNat% 1126))))
 (.branch 1128
 (.leaf (certNat% 1127))
 (.branch 1129
 (.leaf (certNat% 1128))
 (.leaf (certNat% 1129)))))
 (.branch 1133
 (.branch 1131
 (.leaf (certNat% 1130))
 (.branch 1132
 (.leaf (certNat% 1131))
 (.leaf (certNat% 1132))))
 (.branch 1135
 (.branch 1134
 (.leaf (certNat% 1133))
 (.leaf (certNat% 1134)))
 (.branch 1136
 (.leaf (certNat% 1135))
 (.leaf (certNat% 1136))))))
 (.branch 1144
 (.branch 1140
 (.branch 1138
 (.leaf (certNat% 1137))
 (.branch 1139
 (.leaf (certNat% 1138))
 (.leaf (certNat% 1139))))
 (.branch 1142
 (.branch 1141
 (.leaf (certNat% 1140))
 (.leaf (certNat% 1141)))
 (.branch 1143
 (.leaf (certNat% 1142))
 (.leaf (certNat% 1143)))))
 (.branch 1147
 (.branch 1145
 (.leaf (certNat% 1144))
 (.branch 1146
 (.leaf (certNat% 1145))
 (.leaf (certNat% 1146))))
 (.branch 1149
 (.branch 1148
 (.leaf (certNat% 1147))
 (.leaf (certNat% 1148)))
 (.branch 1150
 (.leaf (certNat% 1149))
 (.leaf (certNat% 1150)))))))
 (.branch 1164
 (.branch 1157
 (.branch 1154
 (.branch 1152
 (.leaf (certNat% 1151))
 (.branch 1153
 (.leaf (certNat% 1152))
 (.leaf (certNat% 1153))))
 (.branch 1155
 (.leaf (certNat% 1154))
 (.branch 1156
 (.leaf (certNat% 1155))
 (.leaf (certNat% 1156)))))
 (.branch 1160
 (.branch 1158
 (.leaf (certNat% 1157))
 (.branch 1159
 (.leaf (certNat% 1158))
 (.leaf (certNat% 1159))))
 (.branch 1162
 (.branch 1161
 (.leaf (certNat% 1160))
 (.leaf (certNat% 1161)))
 (.branch 1163
 (.leaf (certNat% 1162))
 (.leaf (certNat% 1163))))))
 (.branch 1171
 (.branch 1167
 (.branch 1165
 (.leaf (certNat% 1164))
 (.branch 1166
 (.leaf (certNat% 1165))
 (.leaf (certNat% 1166))))
 (.branch 1169
 (.branch 1168
 (.leaf (certNat% 1167))
 (.leaf (certNat% 1168)))
 (.branch 1170
 (.leaf (certNat% 1169))
 (.leaf (certNat% 1170)))))
 (.branch 1174
 (.branch 1172
 (.leaf (certNat% 1171))
 (.branch 1173
 (.leaf (certNat% 1172))
 (.leaf (certNat% 1173))))
 (.branch 1176
 (.branch 1175
 (.leaf (certNat% 1174))
 (.leaf (certNat% 1175)))
 (.branch 1177
 (.leaf (certNat% 1176))
 (.leaf (certNat% 1177)))))))))
 (.branch 1231
 (.branch 1204
 (.branch 1191
 (.branch 1184
 (.branch 1181
 (.branch 1179
 (.leaf (certNat% 1178))
 (.branch 1180
 (.leaf (certNat% 1179))
 (.leaf (certNat% 1180))))
 (.branch 1182
 (.leaf (certNat% 1181))
 (.branch 1183
 (.leaf (certNat% 1182))
 (.leaf (certNat% 1183)))))
 (.branch 1187
 (.branch 1185
 (.leaf (certNat% 1184))
 (.branch 1186
 (.leaf (certNat% 1185))
 (.leaf (certNat% 1186))))
 (.branch 1189
 (.branch 1188
 (.leaf (certNat% 1187))
 (.leaf (certNat% 1188)))
 (.branch 1190
 (.leaf (certNat% 1189))
 (.leaf (certNat% 1190))))))
 (.branch 1197
 (.branch 1194
 (.branch 1192
 (.leaf (certNat% 1191))
 (.branch 1193
 (.leaf (certNat% 1192))
 (.leaf (certNat% 1193))))
 (.branch 1195
 (.leaf (certNat% 1194))
 (.branch 1196
 (.leaf (certNat% 1195))
 (.leaf (certNat% 1196)))))
 (.branch 1200
 (.branch 1198
 (.leaf (certNat% 1197))
 (.branch 1199
 (.leaf (certNat% 1198))
 (.leaf (certNat% 1199))))
 (.branch 1202
 (.branch 1201
 (.leaf (certNat% 1200))
 (.leaf (certNat% 1201)))
 (.branch 1203
 (.leaf (certNat% 1202))
 (.leaf (certNat% 1203)))))))
 (.branch 1217
 (.branch 1210
 (.branch 1207
 (.branch 1205
 (.leaf (certNat% 1204))
 (.branch 1206
 (.leaf (certNat% 1205))
 (.leaf (certNat% 1206))))
 (.branch 1208
 (.leaf (certNat% 1207))
 (.branch 1209
 (.leaf (certNat% 1208))
 (.leaf (certNat% 1209)))))
 (.branch 1213
 (.branch 1211
 (.leaf (certNat% 1210))
 (.branch 1212
 (.leaf (certNat% 1211))
 (.leaf (certNat% 1212))))
 (.branch 1215
 (.branch 1214
 (.leaf (certNat% 1213))
 (.leaf (certNat% 1214)))
 (.branch 1216
 (.leaf (certNat% 1215))
 (.leaf (certNat% 1216))))))
 (.branch 1224
 (.branch 1220
 (.branch 1218
 (.leaf (certNat% 1217))
 (.branch 1219
 (.leaf (certNat% 1218))
 (.leaf (certNat% 1219))))
 (.branch 1222
 (.branch 1221
 (.leaf (certNat% 1220))
 (.leaf (certNat% 1221)))
 (.branch 1223
 (.leaf (certNat% 1222))
 (.leaf (certNat% 1223)))))
 (.branch 1227
 (.branch 1225
 (.leaf (certNat% 1224))
 (.branch 1226
 (.leaf (certNat% 1225))
 (.leaf (certNat% 1226))))
 (.branch 1229
 (.branch 1228
 (.leaf (certNat% 1227))
 (.leaf (certNat% 1228)))
 (.branch 1230
 (.leaf (certNat% 1229))
 (.leaf (certNat% 1230))))))))
 (.branch 1258
 (.branch 1244
 (.branch 1237
 (.branch 1234
 (.branch 1232
 (.leaf (certNat% 1231))
 (.branch 1233
 (.leaf (certNat% 1232))
 (.leaf (certNat% 1233))))
 (.branch 1235
 (.leaf (certNat% 1234))
 (.branch 1236
 (.leaf (certNat% 1235))
 (.leaf (certNat% 1236)))))
 (.branch 1240
 (.branch 1238
 (.leaf (certNat% 1237))
 (.branch 1239
 (.leaf (certNat% 1238))
 (.leaf (certNat% 1239))))
 (.branch 1242
 (.branch 1241
 (.leaf (certNat% 1240))
 (.leaf (certNat% 1241)))
 (.branch 1243
 (.leaf (certNat% 1242))
 (.leaf (certNat% 1243))))))
 (.branch 1251
 (.branch 1247
 (.branch 1245
 (.leaf (certNat% 1244))
 (.branch 1246
 (.leaf (certNat% 1245))
 (.leaf (certNat% 1246))))
 (.branch 1249
 (.branch 1248
 (.leaf (certNat% 1247))
 (.leaf (certNat% 1248)))
 (.branch 1250
 (.leaf (certNat% 1249))
 (.leaf (certNat% 1250)))))
 (.branch 1254
 (.branch 1252
 (.leaf (certNat% 1251))
 (.branch 1253
 (.leaf (certNat% 1252))
 (.leaf (certNat% 1253))))
 (.branch 1256
 (.branch 1255
 (.leaf (certNat% 1254))
 (.leaf (certNat% 1255)))
 (.branch 1257
 (.leaf (certNat% 1256))
 (.leaf (certNat% 1257)))))))
 (.branch 1271
 (.branch 1264
 (.branch 1261
 (.branch 1259
 (.leaf (certNat% 1258))
 (.branch 1260
 (.leaf (certNat% 1259))
 (.leaf (certNat% 1260))))
 (.branch 1262
 (.leaf (certNat% 1261))
 (.branch 1263
 (.leaf (certNat% 1262))
 (.leaf (certNat% 1263)))))
 (.branch 1267
 (.branch 1265
 (.leaf (certNat% 1264))
 (.branch 1266
 (.leaf (certNat% 1265))
 (.leaf (certNat% 1266))))
 (.branch 1269
 (.branch 1268
 (.leaf (certNat% 1267))
 (.leaf (certNat% 1268)))
 (.branch 1270
 (.leaf (certNat% 1269))
 (.leaf (certNat% 1270))))))
 (.branch 1278
 (.branch 1274
 (.branch 1272
 (.leaf (certNat% 1271))
 (.branch 1273
 (.leaf (certNat% 1272))
 (.leaf (certNat% 1273))))
 (.branch 1276
 (.branch 1275
 (.leaf (certNat% 1274))
 (.leaf (certNat% 1275)))
 (.branch 1277
 (.leaf (certNat% 1276))
 (.leaf (certNat% 1277)))))
 (.branch 1281
 (.branch 1279
 (.leaf (certNat% 1278))
 (.branch 1280
 (.leaf (certNat% 1279))
 (.leaf (certNat% 1280))))
 (.branch 1283
 (.branch 1282
 (.leaf (certNat% 1281))
 (.leaf (certNat% 1282)))
 (.branch 1284
 (.leaf (certNat% 1283))
 (.leaf (certNat% 1284)))))))))))
 (.branch 1499
 (.branch 1392
 (.branch 1338
 (.branch 1311
 (.branch 1298
 (.branch 1291
 (.branch 1288
 (.branch 1286
 (.leaf (certNat% 1285))
 (.branch 1287
 (.leaf (certNat% 1286))
 (.leaf (certNat% 1287))))
 (.branch 1289
 (.leaf (certNat% 1288))
 (.branch 1290
 (.leaf (certNat% 1289))
 (.leaf (certNat% 1290)))))
 (.branch 1294
 (.branch 1292
 (.leaf (certNat% 1291))
 (.branch 1293
 (.leaf (certNat% 1292))
 (.leaf (certNat% 1293))))
 (.branch 1296
 (.branch 1295
 (.leaf (certNat% 1294))
 (.leaf (certNat% 1295)))
 (.branch 1297
 (.leaf (certNat% 1296))
 (.leaf (certNat% 1297))))))
 (.branch 1304
 (.branch 1301
 (.branch 1299
 (.leaf (certNat% 1298))
 (.branch 1300
 (.leaf (certNat% 1299))
 (.leaf (certNat% 1300))))
 (.branch 1302
 (.leaf (certNat% 1301))
 (.branch 1303
 (.leaf (certNat% 1302))
 (.leaf (certNat% 1303)))))
 (.branch 1307
 (.branch 1305
 (.leaf (certNat% 1304))
 (.branch 1306
 (.leaf (certNat% 1305))
 (.leaf (certNat% 1306))))
 (.branch 1309
 (.branch 1308
 (.leaf (certNat% 1307))
 (.leaf (certNat% 1308)))
 (.branch 1310
 (.leaf (certNat% 1309))
 (.leaf (certNat% 1310)))))))
 (.branch 1324
 (.branch 1317
 (.branch 1314
 (.branch 1312
 (.leaf (certNat% 1311))
 (.branch 1313
 (.leaf (certNat% 1312))
 (.leaf (certNat% 1313))))
 (.branch 1315
 (.leaf (certNat% 1314))
 (.branch 1316
 (.leaf (certNat% 1315))
 (.leaf (certNat% 1316)))))
 (.branch 1320
 (.branch 1318
 (.leaf (certNat% 1317))
 (.branch 1319
 (.leaf (certNat% 1318))
 (.leaf (certNat% 1319))))
 (.branch 1322
 (.branch 1321
 (.leaf (certNat% 1320))
 (.leaf (certNat% 1321)))
 (.branch 1323
 (.leaf (certNat% 1322))
 (.leaf (certNat% 1323))))))
 (.branch 1331
 (.branch 1327
 (.branch 1325
 (.leaf (certNat% 1324))
 (.branch 1326
 (.leaf (certNat% 1325))
 (.leaf (certNat% 1326))))
 (.branch 1329
 (.branch 1328
 (.leaf (certNat% 1327))
 (.leaf (certNat% 1328)))
 (.branch 1330
 (.leaf (certNat% 1329))
 (.leaf (certNat% 1330)))))
 (.branch 1334
 (.branch 1332
 (.leaf (certNat% 1331))
 (.branch 1333
 (.leaf (certNat% 1332))
 (.leaf (certNat% 1333))))
 (.branch 1336
 (.branch 1335
 (.leaf (certNat% 1334))
 (.leaf (certNat% 1335)))
 (.branch 1337
 (.leaf (certNat% 1336))
 (.leaf (certNat% 1337))))))))
 (.branch 1365
 (.branch 1351
 (.branch 1344
 (.branch 1341
 (.branch 1339
 (.leaf (certNat% 1338))
 (.branch 1340
 (.leaf (certNat% 1339))
 (.leaf (certNat% 1340))))
 (.branch 1342
 (.leaf (certNat% 1341))
 (.branch 1343
 (.leaf (certNat% 1342))
 (.leaf (certNat% 1343)))))
 (.branch 1347
 (.branch 1345
 (.leaf (certNat% 1344))
 (.branch 1346
 (.leaf (certNat% 1345))
 (.leaf (certNat% 1346))))
 (.branch 1349
 (.branch 1348
 (.leaf (certNat% 1347))
 (.leaf (certNat% 1348)))
 (.branch 1350
 (.leaf (certNat% 1349))
 (.leaf (certNat% 1350))))))
 (.branch 1358
 (.branch 1354
 (.branch 1352
 (.leaf (certNat% 1351))
 (.branch 1353
 (.leaf (certNat% 1352))
 (.leaf (certNat% 1353))))
 (.branch 1356
 (.branch 1355
 (.leaf (certNat% 1354))
 (.leaf (certNat% 1355)))
 (.branch 1357
 (.leaf (certNat% 1356))
 (.leaf (certNat% 1357)))))
 (.branch 1361
 (.branch 1359
 (.leaf (certNat% 1358))
 (.branch 1360
 (.leaf (certNat% 1359))
 (.leaf (certNat% 1360))))
 (.branch 1363
 (.branch 1362
 (.leaf (certNat% 1361))
 (.leaf (certNat% 1362)))
 (.branch 1364
 (.leaf (certNat% 1363))
 (.leaf (certNat% 1364)))))))
 (.branch 1378
 (.branch 1371
 (.branch 1368
 (.branch 1366
 (.leaf (certNat% 1365))
 (.branch 1367
 (.leaf (certNat% 1366))
 (.leaf (certNat% 1367))))
 (.branch 1369
 (.leaf (certNat% 1368))
 (.branch 1370
 (.leaf (certNat% 1369))
 (.leaf (certNat% 1370)))))
 (.branch 1374
 (.branch 1372
 (.leaf (certNat% 1371))
 (.branch 1373
 (.leaf (certNat% 1372))
 (.leaf (certNat% 1373))))
 (.branch 1376
 (.branch 1375
 (.leaf (certNat% 1374))
 (.leaf (certNat% 1375)))
 (.branch 1377
 (.leaf (certNat% 1376))
 (.leaf (certNat% 1377))))))
 (.branch 1385
 (.branch 1381
 (.branch 1379
 (.leaf (certNat% 1378))
 (.branch 1380
 (.leaf (certNat% 1379))
 (.leaf (certNat% 1380))))
 (.branch 1383
 (.branch 1382
 (.leaf (certNat% 1381))
 (.leaf (certNat% 1382)))
 (.branch 1384
 (.leaf (certNat% 1383))
 (.leaf (certNat% 1384)))))
 (.branch 1388
 (.branch 1386
 (.leaf (certNat% 1385))
 (.branch 1387
 (.leaf (certNat% 1386))
 (.leaf (certNat% 1387))))
 (.branch 1390
 (.branch 1389
 (.leaf (certNat% 1388))
 (.leaf (certNat% 1389)))
 (.branch 1391
 (.leaf (certNat% 1390))
 (.leaf (certNat% 1391)))))))))
 (.branch 1445
 (.branch 1418
 (.branch 1405
 (.branch 1398
 (.branch 1395
 (.branch 1393
 (.leaf (certNat% 1392))
 (.branch 1394
 (.leaf (certNat% 1393))
 (.leaf (certNat% 1394))))
 (.branch 1396
 (.leaf (certNat% 1395))
 (.branch 1397
 (.leaf (certNat% 1396))
 (.leaf (certNat% 1397)))))
 (.branch 1401
 (.branch 1399
 (.leaf (certNat% 1398))
 (.branch 1400
 (.leaf (certNat% 1399))
 (.leaf (certNat% 1400))))
 (.branch 1403
 (.branch 1402
 (.leaf (certNat% 1401))
 (.leaf (certNat% 1402)))
 (.branch 1404
 (.leaf (certNat% 1403))
 (.leaf (certNat% 1404))))))
 (.branch 1411
 (.branch 1408
 (.branch 1406
 (.leaf (certNat% 1405))
 (.branch 1407
 (.leaf (certNat% 1406))
 (.leaf (certNat% 1407))))
 (.branch 1409
 (.leaf (certNat% 1408))
 (.branch 1410
 (.leaf (certNat% 1409))
 (.leaf (certNat% 1410)))))
 (.branch 1414
 (.branch 1412
 (.leaf (certNat% 1411))
 (.branch 1413
 (.leaf (certNat% 1412))
 (.leaf (certNat% 1413))))
 (.branch 1416
 (.branch 1415
 (.leaf (certNat% 1414))
 (.leaf (certNat% 1415)))
 (.branch 1417
 (.leaf (certNat% 1416))
 (.leaf (certNat% 1417)))))))
 (.branch 1431
 (.branch 1424
 (.branch 1421
 (.branch 1419
 (.leaf (certNat% 1418))
 (.branch 1420
 (.leaf (certNat% 1419))
 (.leaf (certNat% 1420))))
 (.branch 1422
 (.leaf (certNat% 1421))
 (.branch 1423
 (.leaf (certNat% 1422))
 (.leaf (certNat% 1423)))))
 (.branch 1427
 (.branch 1425
 (.leaf (certNat% 1424))
 (.branch 1426
 (.leaf (certNat% 1425))
 (.leaf (certNat% 1426))))
 (.branch 1429
 (.branch 1428
 (.leaf (certNat% 1427))
 (.leaf (certNat% 1428)))
 (.branch 1430
 (.leaf (certNat% 1429))
 (.leaf (certNat% 1430))))))
 (.branch 1438
 (.branch 1434
 (.branch 1432
 (.leaf (certNat% 1431))
 (.branch 1433
 (.leaf (certNat% 1432))
 (.leaf (certNat% 1433))))
 (.branch 1436
 (.branch 1435
 (.leaf (certNat% 1434))
 (.leaf (certNat% 1435)))
 (.branch 1437
 (.leaf (certNat% 1436))
 (.leaf (certNat% 1437)))))
 (.branch 1441
 (.branch 1439
 (.leaf (certNat% 1438))
 (.branch 1440
 (.leaf (certNat% 1439))
 (.leaf (certNat% 1440))))
 (.branch 1443
 (.branch 1442
 (.leaf (certNat% 1441))
 (.leaf (certNat% 1442)))
 (.branch 1444
 (.leaf (certNat% 1443))
 (.leaf (certNat% 1444))))))))
 (.branch 1472
 (.branch 1458
 (.branch 1451
 (.branch 1448
 (.branch 1446
 (.leaf (certNat% 1445))
 (.branch 1447
 (.leaf (certNat% 1446))
 (.leaf (certNat% 1447))))
 (.branch 1449
 (.leaf (certNat% 1448))
 (.branch 1450
 (.leaf (certNat% 1449))
 (.leaf (certNat% 1450)))))
 (.branch 1454
 (.branch 1452
 (.leaf (certNat% 1451))
 (.branch 1453
 (.leaf (certNat% 1452))
 (.leaf (certNat% 1453))))
 (.branch 1456
 (.branch 1455
 (.leaf (certNat% 1454))
 (.leaf (certNat% 1455)))
 (.branch 1457
 (.leaf (certNat% 1456))
 (.leaf (certNat% 1457))))))
 (.branch 1465
 (.branch 1461
 (.branch 1459
 (.leaf (certNat% 1458))
 (.branch 1460
 (.leaf (certNat% 1459))
 (.leaf (certNat% 1460))))
 (.branch 1463
 (.branch 1462
 (.leaf (certNat% 1461))
 (.leaf (certNat% 1462)))
 (.branch 1464
 (.leaf (certNat% 1463))
 (.leaf (certNat% 1464)))))
 (.branch 1468
 (.branch 1466
 (.leaf (certNat% 1465))
 (.branch 1467
 (.leaf (certNat% 1466))
 (.leaf (certNat% 1467))))
 (.branch 1470
 (.branch 1469
 (.leaf (certNat% 1468))
 (.leaf (certNat% 1469)))
 (.branch 1471
 (.leaf (certNat% 1470))
 (.leaf (certNat% 1471)))))))
 (.branch 1485
 (.branch 1478
 (.branch 1475
 (.branch 1473
 (.leaf (certNat% 1472))
 (.branch 1474
 (.leaf (certNat% 1473))
 (.leaf (certNat% 1474))))
 (.branch 1476
 (.leaf (certNat% 1475))
 (.branch 1477
 (.leaf (certNat% 1476))
 (.leaf (certNat% 1477)))))
 (.branch 1481
 (.branch 1479
 (.leaf (certNat% 1478))
 (.branch 1480
 (.leaf (certNat% 1479))
 (.leaf (certNat% 1480))))
 (.branch 1483
 (.branch 1482
 (.leaf (certNat% 1481))
 (.leaf (certNat% 1482)))
 (.branch 1484
 (.leaf (certNat% 1483))
 (.leaf (certNat% 1484))))))
 (.branch 1492
 (.branch 1488
 (.branch 1486
 (.leaf (certNat% 1485))
 (.branch 1487
 (.leaf (certNat% 1486))
 (.leaf (certNat% 1487))))
 (.branch 1490
 (.branch 1489
 (.leaf (certNat% 1488))
 (.leaf (certNat% 1489)))
 (.branch 1491
 (.leaf (certNat% 1490))
 (.leaf (certNat% 1491)))))
 (.branch 1495
 (.branch 1493
 (.leaf (certNat% 1492))
 (.branch 1494
 (.leaf (certNat% 1493))
 (.leaf (certNat% 1494))))
 (.branch 1497
 (.branch 1496
 (.leaf (certNat% 1495))
 (.leaf (certNat% 1496)))
 (.branch 1498
 (.leaf (certNat% 1497))
 (.leaf (certNat% 1498))))))))))
 (.branch 1606
 (.branch 1552
 (.branch 1525
 (.branch 1512
 (.branch 1505
 (.branch 1502
 (.branch 1500
 (.leaf (certNat% 1499))
 (.branch 1501
 (.leaf (certNat% 1500))
 (.leaf (certNat% 1501))))
 (.branch 1503
 (.leaf (certNat% 1502))
 (.branch 1504
 (.leaf (certNat% 1503))
 (.leaf (certNat% 1504)))))
 (.branch 1508
 (.branch 1506
 (.leaf (certNat% 1505))
 (.branch 1507
 (.leaf (certNat% 1506))
 (.leaf (certNat% 1507))))
 (.branch 1510
 (.branch 1509
 (.leaf (certNat% 1508))
 (.leaf (certNat% 1509)))
 (.branch 1511
 (.leaf (certNat% 1510))
 (.leaf (certNat% 1511))))))
 (.branch 1518
 (.branch 1515
 (.branch 1513
 (.leaf (certNat% 1512))
 (.branch 1514
 (.leaf (certNat% 1513))
 (.leaf (certNat% 1514))))
 (.branch 1516
 (.leaf (certNat% 1515))
 (.branch 1517
 (.leaf (certNat% 1516))
 (.leaf (certNat% 1517)))))
 (.branch 1521
 (.branch 1519
 (.leaf (certNat% 1518))
 (.branch 1520
 (.leaf (certNat% 1519))
 (.leaf (certNat% 1520))))
 (.branch 1523
 (.branch 1522
 (.leaf (certNat% 1521))
 (.leaf (certNat% 1522)))
 (.branch 1524
 (.leaf (certNat% 1523))
 (.leaf (certNat% 1524)))))))
 (.branch 1538
 (.branch 1531
 (.branch 1528
 (.branch 1526
 (.leaf (certNat% 1525))
 (.branch 1527
 (.leaf (certNat% 1526))
 (.leaf (certNat% 1527))))
 (.branch 1529
 (.leaf (certNat% 1528))
 (.branch 1530
 (.leaf (certNat% 1529))
 (.leaf (certNat% 1530)))))
 (.branch 1534
 (.branch 1532
 (.leaf (certNat% 1531))
 (.branch 1533
 (.leaf (certNat% 1532))
 (.leaf (certNat% 1533))))
 (.branch 1536
 (.branch 1535
 (.leaf (certNat% 1534))
 (.leaf (certNat% 1535)))
 (.branch 1537
 (.leaf (certNat% 1536))
 (.leaf (certNat% 1537))))))
 (.branch 1545
 (.branch 1541
 (.branch 1539
 (.leaf (certNat% 1538))
 (.branch 1540
 (.leaf (certNat% 1539))
 (.leaf (certNat% 1540))))
 (.branch 1543
 (.branch 1542
 (.leaf (certNat% 1541))
 (.leaf (certNat% 1542)))
 (.branch 1544
 (.leaf (certNat% 1543))
 (.leaf (certNat% 1544)))))
 (.branch 1548
 (.branch 1546
 (.leaf (certNat% 1545))
 (.branch 1547
 (.leaf (certNat% 1546))
 (.leaf (certNat% 1547))))
 (.branch 1550
 (.branch 1549
 (.leaf (certNat% 1548))
 (.leaf (certNat% 1549)))
 (.branch 1551
 (.leaf (certNat% 1550))
 (.leaf (certNat% 1551))))))))
 (.branch 1579
 (.branch 1565
 (.branch 1558
 (.branch 1555
 (.branch 1553
 (.leaf (certNat% 1552))
 (.branch 1554
 (.leaf (certNat% 1553))
 (.leaf (certNat% 1554))))
 (.branch 1556
 (.leaf (certNat% 1555))
 (.branch 1557
 (.leaf (certNat% 1556))
 (.leaf (certNat% 1557)))))
 (.branch 1561
 (.branch 1559
 (.leaf (certNat% 1558))
 (.branch 1560
 (.leaf (certNat% 1559))
 (.leaf (certNat% 1560))))
 (.branch 1563
 (.branch 1562
 (.leaf (certNat% 1561))
 (.leaf (certNat% 1562)))
 (.branch 1564
 (.leaf (certNat% 1563))
 (.leaf (certNat% 1564))))))
 (.branch 1572
 (.branch 1568
 (.branch 1566
 (.leaf (certNat% 1565))
 (.branch 1567
 (.leaf (certNat% 1566))
 (.leaf (certNat% 1567))))
 (.branch 1570
 (.branch 1569
 (.leaf (certNat% 1568))
 (.leaf (certNat% 1569)))
 (.branch 1571
 (.leaf (certNat% 1570))
 (.leaf (certNat% 1571)))))
 (.branch 1575
 (.branch 1573
 (.leaf (certNat% 1572))
 (.branch 1574
 (.leaf (certNat% 1573))
 (.leaf (certNat% 1574))))
 (.branch 1577
 (.branch 1576
 (.leaf (certNat% 1575))
 (.leaf (certNat% 1576)))
 (.branch 1578
 (.leaf (certNat% 1577))
 (.leaf (certNat% 1578)))))))
 (.branch 1592
 (.branch 1585
 (.branch 1582
 (.branch 1580
 (.leaf (certNat% 1579))
 (.branch 1581
 (.leaf (certNat% 1580))
 (.leaf (certNat% 1581))))
 (.branch 1583
 (.leaf (certNat% 1582))
 (.branch 1584
 (.leaf (certNat% 1583))
 (.leaf (certNat% 1584)))))
 (.branch 1588
 (.branch 1586
 (.leaf (certNat% 1585))
 (.branch 1587
 (.leaf (certNat% 1586))
 (.leaf (certNat% 1587))))
 (.branch 1590
 (.branch 1589
 (.leaf (certNat% 1588))
 (.leaf (certNat% 1589)))
 (.branch 1591
 (.leaf (certNat% 1590))
 (.leaf (certNat% 1591))))))
 (.branch 1599
 (.branch 1595
 (.branch 1593
 (.leaf (certNat% 1592))
 (.branch 1594
 (.leaf (certNat% 1593))
 (.leaf (certNat% 1594))))
 (.branch 1597
 (.branch 1596
 (.leaf (certNat% 1595))
 (.leaf (certNat% 1596)))
 (.branch 1598
 (.leaf (certNat% 1597))
 (.leaf (certNat% 1598)))))
 (.branch 1602
 (.branch 1600
 (.leaf (certNat% 1599))
 (.branch 1601
 (.leaf (certNat% 1600))
 (.leaf (certNat% 1601))))
 (.branch 1604
 (.branch 1603
 (.leaf (certNat% 1602))
 (.leaf (certNat% 1603)))
 (.branch 1605
 (.leaf (certNat% 1604))
 (.leaf (certNat% 1605)))))))))
 (.branch 1660
 (.branch 1633
 (.branch 1619
 (.branch 1612
 (.branch 1609
 (.branch 1607
 (.leaf (certNat% 1606))
 (.branch 1608
 (.leaf (certNat% 1607))
 (.leaf (certNat% 1608))))
 (.branch 1610
 (.leaf (certNat% 1609))
 (.branch 1611
 (.leaf (certNat% 1610))
 (.leaf (certNat% 1611)))))
 (.branch 1615
 (.branch 1613
 (.leaf (certNat% 1612))
 (.branch 1614
 (.leaf (certNat% 1613))
 (.leaf (certNat% 1614))))
 (.branch 1617
 (.branch 1616
 (.leaf (certNat% 1615))
 (.leaf (certNat% 1616)))
 (.branch 1618
 (.leaf (certNat% 1617))
 (.leaf (certNat% 1618))))))
 (.branch 1626
 (.branch 1622
 (.branch 1620
 (.leaf (certNat% 1619))
 (.branch 1621
 (.leaf (certNat% 1620))
 (.leaf (certNat% 1621))))
 (.branch 1624
 (.branch 1623
 (.leaf (certNat% 1622))
 (.leaf (certNat% 1623)))
 (.branch 1625
 (.leaf (certNat% 1624))
 (.leaf (certNat% 1625)))))
 (.branch 1629
 (.branch 1627
 (.leaf (certNat% 1626))
 (.branch 1628
 (.leaf (certNat% 1627))
 (.leaf (certNat% 1628))))
 (.branch 1631
 (.branch 1630
 (.leaf (certNat% 1629))
 (.leaf (certNat% 1630)))
 (.branch 1632
 (.leaf (certNat% 1631))
 (.leaf (certNat% 1632)))))))
 (.branch 1646
 (.branch 1639
 (.branch 1636
 (.branch 1634
 (.leaf (certNat% 1633))
 (.branch 1635
 (.leaf (certNat% 1634))
 (.leaf (certNat% 1635))))
 (.branch 1637
 (.leaf (certNat% 1636))
 (.branch 1638
 (.leaf (certNat% 1637))
 (.leaf (certNat% 1638)))))
 (.branch 1642
 (.branch 1640
 (.leaf (certNat% 1639))
 (.branch 1641
 (.leaf (certNat% 1640))
 (.leaf (certNat% 1641))))
 (.branch 1644
 (.branch 1643
 (.leaf (certNat% 1642))
 (.leaf (certNat% 1643)))
 (.branch 1645
 (.leaf (certNat% 1644))
 (.leaf (certNat% 1645))))))
 (.branch 1653
 (.branch 1649
 (.branch 1647
 (.leaf (certNat% 1646))
 (.branch 1648
 (.leaf (certNat% 1647))
 (.leaf (certNat% 1648))))
 (.branch 1651
 (.branch 1650
 (.leaf (certNat% 1649))
 (.leaf (certNat% 1650)))
 (.branch 1652
 (.leaf (certNat% 1651))
 (.leaf (certNat% 1652)))))
 (.branch 1656
 (.branch 1654
 (.leaf (certNat% 1653))
 (.branch 1655
 (.leaf (certNat% 1654))
 (.leaf (certNat% 1655))))
 (.branch 1658
 (.branch 1657
 (.leaf (certNat% 1656))
 (.leaf (certNat% 1657)))
 (.branch 1659
 (.leaf (certNat% 1658))
 (.leaf (certNat% 1659))))))))
 (.branch 1687
 (.branch 1673
 (.branch 1666
 (.branch 1663
 (.branch 1661
 (.leaf (certNat% 1660))
 (.branch 1662
 (.leaf (certNat% 1661))
 (.leaf (certNat% 1662))))
 (.branch 1664
 (.leaf (certNat% 1663))
 (.branch 1665
 (.leaf (certNat% 1664))
 (.leaf (certNat% 1665)))))
 (.branch 1669
 (.branch 1667
 (.leaf (certNat% 1666))
 (.branch 1668
 (.leaf (certNat% 1667))
 (.leaf (certNat% 1668))))
 (.branch 1671
 (.branch 1670
 (.leaf (certNat% 1669))
 (.leaf (certNat% 1670)))
 (.branch 1672
 (.leaf (certNat% 1671))
 (.leaf (certNat% 1672))))))
 (.branch 1680
 (.branch 1676
 (.branch 1674
 (.leaf (certNat% 1673))
 (.branch 1675
 (.leaf (certNat% 1674))
 (.leaf (certNat% 1675))))
 (.branch 1678
 (.branch 1677
 (.leaf (certNat% 1676))
 (.leaf (certNat% 1677)))
 (.branch 1679
 (.leaf (certNat% 1678))
 (.leaf (certNat% 1679)))))
 (.branch 1683
 (.branch 1681
 (.leaf (certNat% 1680))
 (.branch 1682
 (.leaf (certNat% 1681))
 (.leaf (certNat% 1682))))
 (.branch 1685
 (.branch 1684
 (.leaf (certNat% 1683))
 (.leaf (certNat% 1684)))
 (.branch 1686
 (.leaf (certNat% 1685))
 (.leaf (certNat% 1686)))))))
 (.branch 1700
 (.branch 1693
 (.branch 1690
 (.branch 1688
 (.leaf (certNat% 1687))
 (.branch 1689
 (.leaf (certNat% 1688))
 (.leaf (certNat% 1689))))
 (.branch 1691
 (.leaf (certNat% 1690))
 (.branch 1692
 (.leaf (certNat% 1691))
 (.leaf (certNat% 1692)))))
 (.branch 1696
 (.branch 1694
 (.leaf (certNat% 1693))
 (.branch 1695
 (.leaf (certNat% 1694))
 (.leaf (certNat% 1695))))
 (.branch 1698
 (.branch 1697
 (.leaf (certNat% 1696))
 (.leaf (certNat% 1697)))
 (.branch 1699
 (.leaf (certNat% 1698))
 (.leaf (certNat% 1699))))))
 (.branch 1707
 (.branch 1703
 (.branch 1701
 (.leaf (certNat% 1700))
 (.branch 1702
 (.leaf (certNat% 1701))
 (.leaf (certNat% 1702))))
 (.branch 1705
 (.branch 1704
 (.leaf (certNat% 1703))
 (.leaf (certNat% 1704)))
 (.branch 1706
 (.leaf (certNat% 1705))
 (.leaf (certNat% 1706)))))
 (.branch 1710
 (.branch 1708
 (.leaf (certNat% 1707))
 (.branch 1709
 (.leaf (certNat% 1708))
 (.leaf (certNat% 1709))))
 (.branch 1712
 (.branch 1711
 (.leaf (certNat% 1710))
 (.leaf (certNat% 1711)))
 (.branch 1713
 (.leaf (certNat% 1712))
 (.leaf (certNat% 1713)))))))))))))
 (.branch 2571
 (.branch 2142
 (.branch 1928
 (.branch 1821
 (.branch 1767
 (.branch 1740
 (.branch 1727
 (.branch 1720
 (.branch 1717
 (.branch 1715
 (.leaf (certNat% 1714))
 (.branch 1716
 (.leaf (certNat% 1715))
 (.leaf (certNat% 1716))))
 (.branch 1718
 (.leaf (certNat% 1717))
 (.branch 1719
 (.leaf (certNat% 1718))
 (.leaf (certNat% 1719)))))
 (.branch 1723
 (.branch 1721
 (.leaf (certNat% 1720))
 (.branch 1722
 (.leaf (certNat% 1721))
 (.leaf (certNat% 1722))))
 (.branch 1725
 (.branch 1724
 (.leaf (certNat% 1723))
 (.leaf (certNat% 1724)))
 (.branch 1726
 (.leaf (certNat% 1725))
 (.leaf (certNat% 1726))))))
 (.branch 1733
 (.branch 1730
 (.branch 1728
 (.leaf (certNat% 1727))
 (.branch 1729
 (.leaf (certNat% 1728))
 (.leaf (certNat% 1729))))
 (.branch 1731
 (.leaf (certNat% 1730))
 (.branch 1732
 (.leaf (certNat% 1731))
 (.leaf (certNat% 1732)))))
 (.branch 1736
 (.branch 1734
 (.leaf (certNat% 1733))
 (.branch 1735
 (.leaf (certNat% 1734))
 (.leaf (certNat% 1735))))
 (.branch 1738
 (.branch 1737
 (.leaf (certNat% 1736))
 (.leaf (certNat% 1737)))
 (.branch 1739
 (.leaf (certNat% 1738))
 (.leaf (certNat% 1739)))))))
 (.branch 1753
 (.branch 1746
 (.branch 1743
 (.branch 1741
 (.leaf (certNat% 1740))
 (.branch 1742
 (.leaf (certNat% 1741))
 (.leaf (certNat% 1742))))
 (.branch 1744
 (.leaf (certNat% 1743))
 (.branch 1745
 (.leaf (certNat% 1744))
 (.leaf (certNat% 1745)))))
 (.branch 1749
 (.branch 1747
 (.leaf (certNat% 1746))
 (.branch 1748
 (.leaf (certNat% 1747))
 (.leaf (certNat% 1748))))
 (.branch 1751
 (.branch 1750
 (.leaf (certNat% 1749))
 (.leaf (certNat% 1750)))
 (.branch 1752
 (.leaf (certNat% 1751))
 (.leaf (certNat% 1752))))))
 (.branch 1760
 (.branch 1756
 (.branch 1754
 (.leaf (certNat% 1753))
 (.branch 1755
 (.leaf (certNat% 1754))
 (.leaf (certNat% 1755))))
 (.branch 1758
 (.branch 1757
 (.leaf (certNat% 1756))
 (.leaf (certNat% 1757)))
 (.branch 1759
 (.leaf (certNat% 1758))
 (.leaf (certNat% 1759)))))
 (.branch 1763
 (.branch 1761
 (.leaf (certNat% 1760))
 (.branch 1762
 (.leaf (certNat% 1761))
 (.leaf (certNat% 1762))))
 (.branch 1765
 (.branch 1764
 (.leaf (certNat% 1763))
 (.leaf (certNat% 1764)))
 (.branch 1766
 (.leaf (certNat% 1765))
 (.leaf (certNat% 1766))))))))
 (.branch 1794
 (.branch 1780
 (.branch 1773
 (.branch 1770
 (.branch 1768
 (.leaf (certNat% 1767))
 (.branch 1769
 (.leaf (certNat% 1768))
 (.leaf (certNat% 1769))))
 (.branch 1771
 (.leaf (certNat% 1770))
 (.branch 1772
 (.leaf (certNat% 1771))
 (.leaf (certNat% 1772)))))
 (.branch 1776
 (.branch 1774
 (.leaf (certNat% 1773))
 (.branch 1775
 (.leaf (certNat% 1774))
 (.leaf (certNat% 1775))))
 (.branch 1778
 (.branch 1777
 (.leaf (certNat% 1776))
 (.leaf (certNat% 1777)))
 (.branch 1779
 (.leaf (certNat% 1778))
 (.leaf (certNat% 1779))))))
 (.branch 1787
 (.branch 1783
 (.branch 1781
 (.leaf (certNat% 1780))
 (.branch 1782
 (.leaf (certNat% 1781))
 (.leaf (certNat% 1782))))
 (.branch 1785
 (.branch 1784
 (.leaf (certNat% 1783))
 (.leaf (certNat% 1784)))
 (.branch 1786
 (.leaf (certNat% 1785))
 (.leaf (certNat% 1786)))))
 (.branch 1790
 (.branch 1788
 (.leaf (certNat% 1787))
 (.branch 1789
 (.leaf (certNat% 1788))
 (.leaf (certNat% 1789))))
 (.branch 1792
 (.branch 1791
 (.leaf (certNat% 1790))
 (.leaf (certNat% 1791)))
 (.branch 1793
 (.leaf (certNat% 1792))
 (.leaf (certNat% 1793)))))))
 (.branch 1807
 (.branch 1800
 (.branch 1797
 (.branch 1795
 (.leaf (certNat% 1794))
 (.branch 1796
 (.leaf (certNat% 1795))
 (.leaf (certNat% 1796))))
 (.branch 1798
 (.leaf (certNat% 1797))
 (.branch 1799
 (.leaf (certNat% 1798))
 (.leaf (certNat% 1799)))))
 (.branch 1803
 (.branch 1801
 (.leaf (certNat% 1800))
 (.branch 1802
 (.leaf (certNat% 1801))
 (.leaf (certNat% 1802))))
 (.branch 1805
 (.branch 1804
 (.leaf (certNat% 1803))
 (.leaf (certNat% 1804)))
 (.branch 1806
 (.leaf (certNat% 1805))
 (.leaf (certNat% 1806))))))
 (.branch 1814
 (.branch 1810
 (.branch 1808
 (.leaf (certNat% 1807))
 (.branch 1809
 (.leaf (certNat% 1808))
 (.leaf (certNat% 1809))))
 (.branch 1812
 (.branch 1811
 (.leaf (certNat% 1810))
 (.leaf (certNat% 1811)))
 (.branch 1813
 (.leaf (certNat% 1812))
 (.leaf (certNat% 1813)))))
 (.branch 1817
 (.branch 1815
 (.leaf (certNat% 1814))
 (.branch 1816
 (.leaf (certNat% 1815))
 (.leaf (certNat% 1816))))
 (.branch 1819
 (.branch 1818
 (.leaf (certNat% 1817))
 (.leaf (certNat% 1818)))
 (.branch 1820
 (.leaf (certNat% 1819))
 (.leaf (certNat% 1820)))))))))
 (.branch 1874
 (.branch 1847
 (.branch 1834
 (.branch 1827
 (.branch 1824
 (.branch 1822
 (.leaf (certNat% 1821))
 (.branch 1823
 (.leaf (certNat% 1822))
 (.leaf (certNat% 1823))))
 (.branch 1825
 (.leaf (certNat% 1824))
 (.branch 1826
 (.leaf (certNat% 1825))
 (.leaf (certNat% 1826)))))
 (.branch 1830
 (.branch 1828
 (.leaf (certNat% 1827))
 (.branch 1829
 (.leaf (certNat% 1828))
 (.leaf (certNat% 1829))))
 (.branch 1832
 (.branch 1831
 (.leaf (certNat% 1830))
 (.leaf (certNat% 1831)))
 (.branch 1833
 (.leaf (certNat% 1832))
 (.leaf (certNat% 1833))))))
 (.branch 1840
 (.branch 1837
 (.branch 1835
 (.leaf (certNat% 1834))
 (.branch 1836
 (.leaf (certNat% 1835))
 (.leaf (certNat% 1836))))
 (.branch 1838
 (.leaf (certNat% 1837))
 (.branch 1839
 (.leaf (certNat% 1838))
 (.leaf (certNat% 1839)))))
 (.branch 1843
 (.branch 1841
 (.leaf (certNat% 1840))
 (.branch 1842
 (.leaf (certNat% 1841))
 (.leaf (certNat% 1842))))
 (.branch 1845
 (.branch 1844
 (.leaf (certNat% 1843))
 (.leaf (certNat% 1844)))
 (.branch 1846
 (.leaf (certNat% 1845))
 (.leaf (certNat% 1846)))))))
 (.branch 1860
 (.branch 1853
 (.branch 1850
 (.branch 1848
 (.leaf (certNat% 1847))
 (.branch 1849
 (.leaf (certNat% 1848))
 (.leaf (certNat% 1849))))
 (.branch 1851
 (.leaf (certNat% 1850))
 (.branch 1852
 (.leaf (certNat% 1851))
 (.leaf (certNat% 1852)))))
 (.branch 1856
 (.branch 1854
 (.leaf (certNat% 1853))
 (.branch 1855
 (.leaf (certNat% 1854))
 (.leaf (certNat% 1855))))
 (.branch 1858
 (.branch 1857
 (.leaf (certNat% 1856))
 (.leaf (certNat% 1857)))
 (.branch 1859
 (.leaf (certNat% 1858))
 (.leaf (certNat% 1859))))))
 (.branch 1867
 (.branch 1863
 (.branch 1861
 (.leaf (certNat% 1860))
 (.branch 1862
 (.leaf (certNat% 1861))
 (.leaf (certNat% 1862))))
 (.branch 1865
 (.branch 1864
 (.leaf (certNat% 1863))
 (.leaf (certNat% 1864)))
 (.branch 1866
 (.leaf (certNat% 1865))
 (.leaf (certNat% 1866)))))
 (.branch 1870
 (.branch 1868
 (.leaf (certNat% 1867))
 (.branch 1869
 (.leaf (certNat% 1868))
 (.leaf (certNat% 1869))))
 (.branch 1872
 (.branch 1871
 (.leaf (certNat% 1870))
 (.leaf (certNat% 1871)))
 (.branch 1873
 (.leaf (certNat% 1872))
 (.leaf (certNat% 1873))))))))
 (.branch 1901
 (.branch 1887
 (.branch 1880
 (.branch 1877
 (.branch 1875
 (.leaf (certNat% 1874))
 (.branch 1876
 (.leaf (certNat% 1875))
 (.leaf (certNat% 1876))))
 (.branch 1878
 (.leaf (certNat% 1877))
 (.branch 1879
 (.leaf (certNat% 1878))
 (.leaf (certNat% 1879)))))
 (.branch 1883
 (.branch 1881
 (.leaf (certNat% 1880))
 (.branch 1882
 (.leaf (certNat% 1881))
 (.leaf (certNat% 1882))))
 (.branch 1885
 (.branch 1884
 (.leaf (certNat% 1883))
 (.leaf (certNat% 1884)))
 (.branch 1886
 (.leaf (certNat% 1885))
 (.leaf (certNat% 1886))))))
 (.branch 1894
 (.branch 1890
 (.branch 1888
 (.leaf (certNat% 1887))
 (.branch 1889
 (.leaf (certNat% 1888))
 (.leaf (certNat% 1889))))
 (.branch 1892
 (.branch 1891
 (.leaf (certNat% 1890))
 (.leaf (certNat% 1891)))
 (.branch 1893
 (.leaf (certNat% 1892))
 (.leaf (certNat% 1893)))))
 (.branch 1897
 (.branch 1895
 (.leaf (certNat% 1894))
 (.branch 1896
 (.leaf (certNat% 1895))
 (.leaf (certNat% 1896))))
 (.branch 1899
 (.branch 1898
 (.leaf (certNat% 1897))
 (.leaf (certNat% 1898)))
 (.branch 1900
 (.leaf (certNat% 1899))
 (.leaf (certNat% 1900)))))))
 (.branch 1914
 (.branch 1907
 (.branch 1904
 (.branch 1902
 (.leaf (certNat% 1901))
 (.branch 1903
 (.leaf (certNat% 1902))
 (.leaf (certNat% 1903))))
 (.branch 1905
 (.leaf (certNat% 1904))
 (.branch 1906
 (.leaf (certNat% 1905))
 (.leaf (certNat% 1906)))))
 (.branch 1910
 (.branch 1908
 (.leaf (certNat% 1907))
 (.branch 1909
 (.leaf (certNat% 1908))
 (.leaf (certNat% 1909))))
 (.branch 1912
 (.branch 1911
 (.leaf (certNat% 1910))
 (.leaf (certNat% 1911)))
 (.branch 1913
 (.leaf (certNat% 1912))
 (.leaf (certNat% 1913))))))
 (.branch 1921
 (.branch 1917
 (.branch 1915
 (.leaf (certNat% 1914))
 (.branch 1916
 (.leaf (certNat% 1915))
 (.leaf (certNat% 1916))))
 (.branch 1919
 (.branch 1918
 (.leaf (certNat% 1917))
 (.leaf (certNat% 1918)))
 (.branch 1920
 (.leaf (certNat% 1919))
 (.leaf (certNat% 1920)))))
 (.branch 1924
 (.branch 1922
 (.leaf (certNat% 1921))
 (.branch 1923
 (.leaf (certNat% 1922))
 (.leaf (certNat% 1923))))
 (.branch 1926
 (.branch 1925
 (.leaf (certNat% 1924))
 (.leaf (certNat% 1925)))
 (.branch 1927
 (.leaf (certNat% 1926))
 (.leaf (certNat% 1927))))))))))
 (.branch 2035
 (.branch 1981
 (.branch 1954
 (.branch 1941
 (.branch 1934
 (.branch 1931
 (.branch 1929
 (.leaf (certNat% 1928))
 (.branch 1930
 (.leaf (certNat% 1929))
 (.leaf (certNat% 1930))))
 (.branch 1932
 (.leaf (certNat% 1931))
 (.branch 1933
 (.leaf (certNat% 1932))
 (.leaf (certNat% 1933)))))
 (.branch 1937
 (.branch 1935
 (.leaf (certNat% 1934))
 (.branch 1936
 (.leaf (certNat% 1935))
 (.leaf (certNat% 1936))))
 (.branch 1939
 (.branch 1938
 (.leaf (certNat% 1937))
 (.leaf (certNat% 1938)))
 (.branch 1940
 (.leaf (certNat% 1939))
 (.leaf (certNat% 1940))))))
 (.branch 1947
 (.branch 1944
 (.branch 1942
 (.leaf (certNat% 1941))
 (.branch 1943
 (.leaf (certNat% 1942))
 (.leaf (certNat% 1943))))
 (.branch 1945
 (.leaf (certNat% 1944))
 (.branch 1946
 (.leaf (certNat% 1945))
 (.leaf (certNat% 1946)))))
 (.branch 1950
 (.branch 1948
 (.leaf (certNat% 1947))
 (.branch 1949
 (.leaf (certNat% 1948))
 (.leaf (certNat% 1949))))
 (.branch 1952
 (.branch 1951
 (.leaf (certNat% 1950))
 (.leaf (certNat% 1951)))
 (.branch 1953
 (.leaf (certNat% 1952))
 (.leaf (certNat% 1953)))))))
 (.branch 1967
 (.branch 1960
 (.branch 1957
 (.branch 1955
 (.leaf (certNat% 1954))
 (.branch 1956
 (.leaf (certNat% 1955))
 (.leaf (certNat% 1956))))
 (.branch 1958
 (.leaf (certNat% 1957))
 (.branch 1959
 (.leaf (certNat% 1958))
 (.leaf (certNat% 1959)))))
 (.branch 1963
 (.branch 1961
 (.leaf (certNat% 1960))
 (.branch 1962
 (.leaf (certNat% 1961))
 (.leaf (certNat% 1962))))
 (.branch 1965
 (.branch 1964
 (.leaf (certNat% 1963))
 (.leaf (certNat% 1964)))
 (.branch 1966
 (.leaf (certNat% 1965))
 (.leaf (certNat% 1966))))))
 (.branch 1974
 (.branch 1970
 (.branch 1968
 (.leaf (certNat% 1967))
 (.branch 1969
 (.leaf (certNat% 1968))
 (.leaf (certNat% 1969))))
 (.branch 1972
 (.branch 1971
 (.leaf (certNat% 1970))
 (.leaf (certNat% 1971)))
 (.branch 1973
 (.leaf (certNat% 1972))
 (.leaf (certNat% 1973)))))
 (.branch 1977
 (.branch 1975
 (.leaf (certNat% 1974))
 (.branch 1976
 (.leaf (certNat% 1975))
 (.leaf (certNat% 1976))))
 (.branch 1979
 (.branch 1978
 (.leaf (certNat% 1977))
 (.leaf (certNat% 1978)))
 (.branch 1980
 (.leaf (certNat% 1979))
 (.leaf (certNat% 1980))))))))
 (.branch 2008
 (.branch 1994
 (.branch 1987
 (.branch 1984
 (.branch 1982
 (.leaf (certNat% 1981))
 (.branch 1983
 (.leaf (certNat% 1982))
 (.leaf (certNat% 1983))))
 (.branch 1985
 (.leaf (certNat% 1984))
 (.branch 1986
 (.leaf (certNat% 1985))
 (.leaf (certNat% 1986)))))
 (.branch 1990
 (.branch 1988
 (.leaf (certNat% 1987))
 (.branch 1989
 (.leaf (certNat% 1988))
 (.leaf (certNat% 1989))))
 (.branch 1992
 (.branch 1991
 (.leaf (certNat% 1990))
 (.leaf (certNat% 1991)))
 (.branch 1993
 (.leaf (certNat% 1992))
 (.leaf (certNat% 1993))))))
 (.branch 2001
 (.branch 1997
 (.branch 1995
 (.leaf (certNat% 1994))
 (.branch 1996
 (.leaf (certNat% 1995))
 (.leaf (certNat% 1996))))
 (.branch 1999
 (.branch 1998
 (.leaf (certNat% 1997))
 (.leaf (certNat% 1998)))
 (.branch 2000
 (.leaf (certNat% 1999))
 (.leaf (certNat% 2000)))))
 (.branch 2004
 (.branch 2002
 (.leaf (certNat% 2001))
 (.branch 2003
 (.leaf (certNat% 2002))
 (.leaf (certNat% 2003))))
 (.branch 2006
 (.branch 2005
 (.leaf (certNat% 2004))
 (.leaf (certNat% 2005)))
 (.branch 2007
 (.leaf (certNat% 2006))
 (.leaf (certNat% 2007)))))))
 (.branch 2021
 (.branch 2014
 (.branch 2011
 (.branch 2009
 (.leaf (certNat% 2008))
 (.branch 2010
 (.leaf (certNat% 2009))
 (.leaf (certNat% 2010))))
 (.branch 2012
 (.leaf (certNat% 2011))
 (.branch 2013
 (.leaf (certNat% 2012))
 (.leaf (certNat% 2013)))))
 (.branch 2017
 (.branch 2015
 (.leaf (certNat% 2014))
 (.branch 2016
 (.leaf (certNat% 2015))
 (.leaf (certNat% 2016))))
 (.branch 2019
 (.branch 2018
 (.leaf (certNat% 2017))
 (.leaf (certNat% 2018)))
 (.branch 2020
 (.leaf (certNat% 2019))
 (.leaf (certNat% 2020))))))
 (.branch 2028
 (.branch 2024
 (.branch 2022
 (.leaf (certNat% 2021))
 (.branch 2023
 (.leaf (certNat% 2022))
 (.leaf (certNat% 2023))))
 (.branch 2026
 (.branch 2025
 (.leaf (certNat% 2024))
 (.leaf (certNat% 2025)))
 (.branch 2027
 (.leaf (certNat% 2026))
 (.leaf (certNat% 2027)))))
 (.branch 2031
 (.branch 2029
 (.leaf (certNat% 2028))
 (.branch 2030
 (.leaf (certNat% 2029))
 (.leaf (certNat% 2030))))
 (.branch 2033
 (.branch 2032
 (.leaf (certNat% 2031))
 (.leaf (certNat% 2032)))
 (.branch 2034
 (.leaf (certNat% 2033))
 (.leaf (certNat% 2034)))))))))
 (.branch 2088
 (.branch 2061
 (.branch 2048
 (.branch 2041
 (.branch 2038
 (.branch 2036
 (.leaf (certNat% 2035))
 (.branch 2037
 (.leaf (certNat% 2036))
 (.leaf (certNat% 2037))))
 (.branch 2039
 (.leaf (certNat% 2038))
 (.branch 2040
 (.leaf (certNat% 2039))
 (.leaf (certNat% 2040)))))
 (.branch 2044
 (.branch 2042
 (.leaf (certNat% 2041))
 (.branch 2043
 (.leaf (certNat% 2042))
 (.leaf (certNat% 2043))))
 (.branch 2046
 (.branch 2045
 (.leaf (certNat% 2044))
 (.leaf (certNat% 2045)))
 (.branch 2047
 (.leaf (certNat% 2046))
 (.leaf (certNat% 2047))))))
 (.branch 2054
 (.branch 2051
 (.branch 2049
 (.leaf (certNat% 2048))
 (.branch 2050
 (.leaf (certNat% 2049))
 (.leaf (certNat% 2050))))
 (.branch 2052
 (.leaf (certNat% 2051))
 (.branch 2053
 (.leaf (certNat% 2052))
 (.leaf (certNat% 2053)))))
 (.branch 2057
 (.branch 2055
 (.leaf (certNat% 2054))
 (.branch 2056
 (.leaf (certNat% 2055))
 (.leaf (certNat% 2056))))
 (.branch 2059
 (.branch 2058
 (.leaf (certNat% 2057))
 (.leaf (certNat% 2058)))
 (.branch 2060
 (.leaf (certNat% 2059))
 (.leaf (certNat% 2060)))))))
 (.branch 2074
 (.branch 2067
 (.branch 2064
 (.branch 2062
 (.leaf (certNat% 2061))
 (.branch 2063
 (.leaf (certNat% 2062))
 (.leaf (certNat% 2063))))
 (.branch 2065
 (.leaf (certNat% 2064))
 (.branch 2066
 (.leaf (certNat% 2065))
 (.leaf (certNat% 2066)))))
 (.branch 2070
 (.branch 2068
 (.leaf (certNat% 2067))
 (.branch 2069
 (.leaf (certNat% 2068))
 (.leaf (certNat% 2069))))
 (.branch 2072
 (.branch 2071
 (.leaf (certNat% 2070))
 (.leaf (certNat% 2071)))
 (.branch 2073
 (.leaf (certNat% 2072))
 (.leaf (certNat% 2073))))))
 (.branch 2081
 (.branch 2077
 (.branch 2075
 (.leaf (certNat% 2074))
 (.branch 2076
 (.leaf (certNat% 2075))
 (.leaf (certNat% 2076))))
 (.branch 2079
 (.branch 2078
 (.leaf (certNat% 2077))
 (.leaf (certNat% 2078)))
 (.branch 2080
 (.leaf (certNat% 2079))
 (.leaf (certNat% 2080)))))
 (.branch 2084
 (.branch 2082
 (.leaf (certNat% 2081))
 (.branch 2083
 (.leaf (certNat% 2082))
 (.leaf (certNat% 2083))))
 (.branch 2086
 (.branch 2085
 (.leaf (certNat% 2084))
 (.leaf (certNat% 2085)))
 (.branch 2087
 (.leaf (certNat% 2086))
 (.leaf (certNat% 2087))))))))
 (.branch 2115
 (.branch 2101
 (.branch 2094
 (.branch 2091
 (.branch 2089
 (.leaf (certNat% 2088))
 (.branch 2090
 (.leaf (certNat% 2089))
 (.leaf (certNat% 2090))))
 (.branch 2092
 (.leaf (certNat% 2091))
 (.branch 2093
 (.leaf (certNat% 2092))
 (.leaf (certNat% 2093)))))
 (.branch 2097
 (.branch 2095
 (.leaf (certNat% 2094))
 (.branch 2096
 (.leaf (certNat% 2095))
 (.leaf (certNat% 2096))))
 (.branch 2099
 (.branch 2098
 (.leaf (certNat% 2097))
 (.leaf (certNat% 2098)))
 (.branch 2100
 (.leaf (certNat% 2099))
 (.leaf (certNat% 2100))))))
 (.branch 2108
 (.branch 2104
 (.branch 2102
 (.leaf (certNat% 2101))
 (.branch 2103
 (.leaf (certNat% 2102))
 (.leaf (certNat% 2103))))
 (.branch 2106
 (.branch 2105
 (.leaf (certNat% 2104))
 (.leaf (certNat% 2105)))
 (.branch 2107
 (.leaf (certNat% 2106))
 (.leaf (certNat% 2107)))))
 (.branch 2111
 (.branch 2109
 (.leaf (certNat% 2108))
 (.branch 2110
 (.leaf (certNat% 2109))
 (.leaf (certNat% 2110))))
 (.branch 2113
 (.branch 2112
 (.leaf (certNat% 2111))
 (.leaf (certNat% 2112)))
 (.branch 2114
 (.leaf (certNat% 2113))
 (.leaf (certNat% 2114)))))))
 (.branch 2128
 (.branch 2121
 (.branch 2118
 (.branch 2116
 (.leaf (certNat% 2115))
 (.branch 2117
 (.leaf (certNat% 2116))
 (.leaf (certNat% 2117))))
 (.branch 2119
 (.leaf (certNat% 2118))
 (.branch 2120
 (.leaf (certNat% 2119))
 (.leaf (certNat% 2120)))))
 (.branch 2124
 (.branch 2122
 (.leaf (certNat% 2121))
 (.branch 2123
 (.leaf (certNat% 2122))
 (.leaf (certNat% 2123))))
 (.branch 2126
 (.branch 2125
 (.leaf (certNat% 2124))
 (.leaf (certNat% 2125)))
 (.branch 2127
 (.leaf (certNat% 2126))
 (.leaf (certNat% 2127))))))
 (.branch 2135
 (.branch 2131
 (.branch 2129
 (.leaf (certNat% 2128))
 (.branch 2130
 (.leaf (certNat% 2129))
 (.leaf (certNat% 2130))))
 (.branch 2133
 (.branch 2132
 (.leaf (certNat% 2131))
 (.leaf (certNat% 2132)))
 (.branch 2134
 (.leaf (certNat% 2133))
 (.leaf (certNat% 2134)))))
 (.branch 2138
 (.branch 2136
 (.leaf (certNat% 2135))
 (.branch 2137
 (.leaf (certNat% 2136))
 (.leaf (certNat% 2137))))
 (.branch 2140
 (.branch 2139
 (.leaf (certNat% 2138))
 (.leaf (certNat% 2139)))
 (.branch 2141
 (.leaf (certNat% 2140))
 (.leaf (certNat% 2141)))))))))))
 (.branch 2356
 (.branch 2249
 (.branch 2195
 (.branch 2168
 (.branch 2155
 (.branch 2148
 (.branch 2145
 (.branch 2143
 (.leaf (certNat% 2142))
 (.branch 2144
 (.leaf (certNat% 2143))
 (.leaf (certNat% 2144))))
 (.branch 2146
 (.leaf (certNat% 2145))
 (.branch 2147
 (.leaf (certNat% 2146))
 (.leaf (certNat% 2147)))))
 (.branch 2151
 (.branch 2149
 (.leaf (certNat% 2148))
 (.branch 2150
 (.leaf (certNat% 2149))
 (.leaf (certNat% 2150))))
 (.branch 2153
 (.branch 2152
 (.leaf (certNat% 2151))
 (.leaf (certNat% 2152)))
 (.branch 2154
 (.leaf (certNat% 2153))
 (.leaf (certNat% 2154))))))
 (.branch 2161
 (.branch 2158
 (.branch 2156
 (.leaf (certNat% 2155))
 (.branch 2157
 (.leaf (certNat% 2156))
 (.leaf (certNat% 2157))))
 (.branch 2159
 (.leaf (certNat% 2158))
 (.branch 2160
 (.leaf (certNat% 2159))
 (.leaf (certNat% 2160)))))
 (.branch 2164
 (.branch 2162
 (.leaf (certNat% 2161))
 (.branch 2163
 (.leaf (certNat% 2162))
 (.leaf (certNat% 2163))))
 (.branch 2166
 (.branch 2165
 (.leaf (certNat% 2164))
 (.leaf (certNat% 2165)))
 (.branch 2167
 (.leaf (certNat% 2166))
 (.leaf (certNat% 2167)))))))
 (.branch 2181
 (.branch 2174
 (.branch 2171
 (.branch 2169
 (.leaf (certNat% 2168))
 (.branch 2170
 (.leaf (certNat% 2169))
 (.leaf (certNat% 2170))))
 (.branch 2172
 (.leaf (certNat% 2171))
 (.branch 2173
 (.leaf (certNat% 2172))
 (.leaf (certNat% 2173)))))
 (.branch 2177
 (.branch 2175
 (.leaf (certNat% 2174))
 (.branch 2176
 (.leaf (certNat% 2175))
 (.leaf (certNat% 2176))))
 (.branch 2179
 (.branch 2178
 (.leaf (certNat% 2177))
 (.leaf (certNat% 2178)))
 (.branch 2180
 (.leaf (certNat% 2179))
 (.leaf (certNat% 2180))))))
 (.branch 2188
 (.branch 2184
 (.branch 2182
 (.leaf (certNat% 2181))
 (.branch 2183
 (.leaf (certNat% 2182))
 (.leaf (certNat% 2183))))
 (.branch 2186
 (.branch 2185
 (.leaf (certNat% 2184))
 (.leaf (certNat% 2185)))
 (.branch 2187
 (.leaf (certNat% 2186))
 (.leaf (certNat% 2187)))))
 (.branch 2191
 (.branch 2189
 (.leaf (certNat% 2188))
 (.branch 2190
 (.leaf (certNat% 2189))
 (.leaf (certNat% 2190))))
 (.branch 2193
 (.branch 2192
 (.leaf (certNat% 2191))
 (.leaf (certNat% 2192)))
 (.branch 2194
 (.leaf (certNat% 2193))
 (.leaf (certNat% 2194))))))))
 (.branch 2222
 (.branch 2208
 (.branch 2201
 (.branch 2198
 (.branch 2196
 (.leaf (certNat% 2195))
 (.branch 2197
 (.leaf (certNat% 2196))
 (.leaf (certNat% 2197))))
 (.branch 2199
 (.leaf (certNat% 2198))
 (.branch 2200
 (.leaf (certNat% 2199))
 (.leaf (certNat% 2200)))))
 (.branch 2204
 (.branch 2202
 (.leaf (certNat% 2201))
 (.branch 2203
 (.leaf (certNat% 2202))
 (.leaf (certNat% 2203))))
 (.branch 2206
 (.branch 2205
 (.leaf (certNat% 2204))
 (.leaf (certNat% 2205)))
 (.branch 2207
 (.leaf (certNat% 2206))
 (.leaf (certNat% 2207))))))
 (.branch 2215
 (.branch 2211
 (.branch 2209
 (.leaf (certNat% 2208))
 (.branch 2210
 (.leaf (certNat% 2209))
 (.leaf (certNat% 2210))))
 (.branch 2213
 (.branch 2212
 (.leaf (certNat% 2211))
 (.leaf (certNat% 2212)))
 (.branch 2214
 (.leaf (certNat% 2213))
 (.leaf (certNat% 2214)))))
 (.branch 2218
 (.branch 2216
 (.leaf (certNat% 2215))
 (.branch 2217
 (.leaf (certNat% 2216))
 (.leaf (certNat% 2217))))
 (.branch 2220
 (.branch 2219
 (.leaf (certNat% 2218))
 (.leaf (certNat% 2219)))
 (.branch 2221
 (.leaf (certNat% 2220))
 (.leaf (certNat% 2221)))))))
 (.branch 2235
 (.branch 2228
 (.branch 2225
 (.branch 2223
 (.leaf (certNat% 2222))
 (.branch 2224
 (.leaf (certNat% 2223))
 (.leaf (certNat% 2224))))
 (.branch 2226
 (.leaf (certNat% 2225))
 (.branch 2227
 (.leaf (certNat% 2226))
 (.leaf (certNat% 2227)))))
 (.branch 2231
 (.branch 2229
 (.leaf (certNat% 2228))
 (.branch 2230
 (.leaf (certNat% 2229))
 (.leaf (certNat% 2230))))
 (.branch 2233
 (.branch 2232
 (.leaf (certNat% 2231))
 (.leaf (certNat% 2232)))
 (.branch 2234
 (.leaf (certNat% 2233))
 (.leaf (certNat% 2234))))))
 (.branch 2242
 (.branch 2238
 (.branch 2236
 (.leaf (certNat% 2235))
 (.branch 2237
 (.leaf (certNat% 2236))
 (.leaf (certNat% 2237))))
 (.branch 2240
 (.branch 2239
 (.leaf (certNat% 2238))
 (.leaf (certNat% 2239)))
 (.branch 2241
 (.leaf (certNat% 2240))
 (.leaf (certNat% 2241)))))
 (.branch 2245
 (.branch 2243
 (.leaf (certNat% 2242))
 (.branch 2244
 (.leaf (certNat% 2243))
 (.leaf (certNat% 2244))))
 (.branch 2247
 (.branch 2246
 (.leaf (certNat% 2245))
 (.leaf (certNat% 2246)))
 (.branch 2248
 (.leaf (certNat% 2247))
 (.leaf (certNat% 2248)))))))))
 (.branch 2302
 (.branch 2275
 (.branch 2262
 (.branch 2255
 (.branch 2252
 (.branch 2250
 (.leaf (certNat% 2249))
 (.branch 2251
 (.leaf (certNat% 2250))
 (.leaf (certNat% 2251))))
 (.branch 2253
 (.leaf (certNat% 2252))
 (.branch 2254
 (.leaf (certNat% 2253))
 (.leaf (certNat% 2254)))))
 (.branch 2258
 (.branch 2256
 (.leaf (certNat% 2255))
 (.branch 2257
 (.leaf (certNat% 2256))
 (.leaf (certNat% 2257))))
 (.branch 2260
 (.branch 2259
 (.leaf (certNat% 2258))
 (.leaf (certNat% 2259)))
 (.branch 2261
 (.leaf (certNat% 2260))
 (.leaf (certNat% 2261))))))
 (.branch 2268
 (.branch 2265
 (.branch 2263
 (.leaf (certNat% 2262))
 (.branch 2264
 (.leaf (certNat% 2263))
 (.leaf (certNat% 2264))))
 (.branch 2266
 (.leaf (certNat% 2265))
 (.branch 2267
 (.leaf (certNat% 2266))
 (.leaf (certNat% 2267)))))
 (.branch 2271
 (.branch 2269
 (.leaf (certNat% 2268))
 (.branch 2270
 (.leaf (certNat% 2269))
 (.leaf (certNat% 2270))))
 (.branch 2273
 (.branch 2272
 (.leaf (certNat% 2271))
 (.leaf (certNat% 2272)))
 (.branch 2274
 (.leaf (certNat% 2273))
 (.leaf (certNat% 2274)))))))
 (.branch 2288
 (.branch 2281
 (.branch 2278
 (.branch 2276
 (.leaf (certNat% 2275))
 (.branch 2277
 (.leaf (certNat% 2276))
 (.leaf (certNat% 2277))))
 (.branch 2279
 (.leaf (certNat% 2278))
 (.branch 2280
 (.leaf (certNat% 2279))
 (.leaf (certNat% 2280)))))
 (.branch 2284
 (.branch 2282
 (.leaf (certNat% 2281))
 (.branch 2283
 (.leaf (certNat% 2282))
 (.leaf (certNat% 2283))))
 (.branch 2286
 (.branch 2285
 (.leaf (certNat% 2284))
 (.leaf (certNat% 2285)))
 (.branch 2287
 (.leaf (certNat% 2286))
 (.leaf (certNat% 2287))))))
 (.branch 2295
 (.branch 2291
 (.branch 2289
 (.leaf (certNat% 2288))
 (.branch 2290
 (.leaf (certNat% 2289))
 (.leaf (certNat% 2290))))
 (.branch 2293
 (.branch 2292
 (.leaf (certNat% 2291))
 (.leaf (certNat% 2292)))
 (.branch 2294
 (.leaf (certNat% 2293))
 (.leaf (certNat% 2294)))))
 (.branch 2298
 (.branch 2296
 (.leaf (certNat% 2295))
 (.branch 2297
 (.leaf (certNat% 2296))
 (.leaf (certNat% 2297))))
 (.branch 2300
 (.branch 2299
 (.leaf (certNat% 2298))
 (.leaf (certNat% 2299)))
 (.branch 2301
 (.leaf (certNat% 2300))
 (.leaf (certNat% 2301))))))))
 (.branch 2329
 (.branch 2315
 (.branch 2308
 (.branch 2305
 (.branch 2303
 (.leaf (certNat% 2302))
 (.branch 2304
 (.leaf (certNat% 2303))
 (.leaf (certNat% 2304))))
 (.branch 2306
 (.leaf (certNat% 2305))
 (.branch 2307
 (.leaf (certNat% 2306))
 (.leaf (certNat% 2307)))))
 (.branch 2311
 (.branch 2309
 (.leaf (certNat% 2308))
 (.branch 2310
 (.leaf (certNat% 2309))
 (.leaf (certNat% 2310))))
 (.branch 2313
 (.branch 2312
 (.leaf (certNat% 2311))
 (.leaf (certNat% 2312)))
 (.branch 2314
 (.leaf (certNat% 2313))
 (.leaf (certNat% 2314))))))
 (.branch 2322
 (.branch 2318
 (.branch 2316
 (.leaf (certNat% 2315))
 (.branch 2317
 (.leaf (certNat% 2316))
 (.leaf (certNat% 2317))))
 (.branch 2320
 (.branch 2319
 (.leaf (certNat% 2318))
 (.leaf (certNat% 2319)))
 (.branch 2321
 (.leaf (certNat% 2320))
 (.leaf (certNat% 2321)))))
 (.branch 2325
 (.branch 2323
 (.leaf (certNat% 2322))
 (.branch 2324
 (.leaf (certNat% 2323))
 (.leaf (certNat% 2324))))
 (.branch 2327
 (.branch 2326
 (.leaf (certNat% 2325))
 (.leaf (certNat% 2326)))
 (.branch 2328
 (.leaf (certNat% 2327))
 (.leaf (certNat% 2328)))))))
 (.branch 2342
 (.branch 2335
 (.branch 2332
 (.branch 2330
 (.leaf (certNat% 2329))
 (.branch 2331
 (.leaf (certNat% 2330))
 (.leaf (certNat% 2331))))
 (.branch 2333
 (.leaf (certNat% 2332))
 (.branch 2334
 (.leaf (certNat% 2333))
 (.leaf (certNat% 2334)))))
 (.branch 2338
 (.branch 2336
 (.leaf (certNat% 2335))
 (.branch 2337
 (.leaf (certNat% 2336))
 (.leaf (certNat% 2337))))
 (.branch 2340
 (.branch 2339
 (.leaf (certNat% 2338))
 (.leaf (certNat% 2339)))
 (.branch 2341
 (.leaf (certNat% 2340))
 (.leaf (certNat% 2341))))))
 (.branch 2349
 (.branch 2345
 (.branch 2343
 (.leaf (certNat% 2342))
 (.branch 2344
 (.leaf (certNat% 2343))
 (.leaf (certNat% 2344))))
 (.branch 2347
 (.branch 2346
 (.leaf (certNat% 2345))
 (.leaf (certNat% 2346)))
 (.branch 2348
 (.leaf (certNat% 2347))
 (.leaf (certNat% 2348)))))
 (.branch 2352
 (.branch 2350
 (.leaf (certNat% 2349))
 (.branch 2351
 (.leaf (certNat% 2350))
 (.leaf (certNat% 2351))))
 (.branch 2354
 (.branch 2353
 (.leaf (certNat% 2352))
 (.leaf (certNat% 2353)))
 (.branch 2355
 (.leaf (certNat% 2354))
 (.leaf (certNat% 2355))))))))))
 (.branch 2463
 (.branch 2409
 (.branch 2382
 (.branch 2369
 (.branch 2362
 (.branch 2359
 (.branch 2357
 (.leaf (certNat% 2356))
 (.branch 2358
 (.leaf (certNat% 2357))
 (.leaf (certNat% 2358))))
 (.branch 2360
 (.leaf (certNat% 2359))
 (.branch 2361
 (.leaf (certNat% 2360))
 (.leaf (certNat% 2361)))))
 (.branch 2365
 (.branch 2363
 (.leaf (certNat% 2362))
 (.branch 2364
 (.leaf (certNat% 2363))
 (.leaf (certNat% 2364))))
 (.branch 2367
 (.branch 2366
 (.leaf (certNat% 2365))
 (.leaf (certNat% 2366)))
 (.branch 2368
 (.leaf (certNat% 2367))
 (.leaf (certNat% 2368))))))
 (.branch 2375
 (.branch 2372
 (.branch 2370
 (.leaf (certNat% 2369))
 (.branch 2371
 (.leaf (certNat% 2370))
 (.leaf (certNat% 2371))))
 (.branch 2373
 (.leaf (certNat% 2372))
 (.branch 2374
 (.leaf (certNat% 2373))
 (.leaf (certNat% 2374)))))
 (.branch 2378
 (.branch 2376
 (.leaf (certNat% 2375))
 (.branch 2377
 (.leaf (certNat% 2376))
 (.leaf (certNat% 2377))))
 (.branch 2380
 (.branch 2379
 (.leaf (certNat% 2378))
 (.leaf (certNat% 2379)))
 (.branch 2381
 (.leaf (certNat% 2380))
 (.leaf (certNat% 2381)))))))
 (.branch 2395
 (.branch 2388
 (.branch 2385
 (.branch 2383
 (.leaf (certNat% 2382))
 (.branch 2384
 (.leaf (certNat% 2383))
 (.leaf (certNat% 2384))))
 (.branch 2386
 (.leaf (certNat% 2385))
 (.branch 2387
 (.leaf (certNat% 2386))
 (.leaf (certNat% 2387)))))
 (.branch 2391
 (.branch 2389
 (.leaf (certNat% 2388))
 (.branch 2390
 (.leaf (certNat% 2389))
 (.leaf (certNat% 2390))))
 (.branch 2393
 (.branch 2392
 (.leaf (certNat% 2391))
 (.leaf (certNat% 2392)))
 (.branch 2394
 (.leaf (certNat% 2393))
 (.leaf (certNat% 2394))))))
 (.branch 2402
 (.branch 2398
 (.branch 2396
 (.leaf (certNat% 2395))
 (.branch 2397
 (.leaf (certNat% 2396))
 (.leaf (certNat% 2397))))
 (.branch 2400
 (.branch 2399
 (.leaf (certNat% 2398))
 (.leaf (certNat% 2399)))
 (.branch 2401
 (.leaf (certNat% 2400))
 (.leaf (certNat% 2401)))))
 (.branch 2405
 (.branch 2403
 (.leaf (certNat% 2402))
 (.branch 2404
 (.leaf (certNat% 2403))
 (.leaf (certNat% 2404))))
 (.branch 2407
 (.branch 2406
 (.leaf (certNat% 2405))
 (.leaf (certNat% 2406)))
 (.branch 2408
 (.leaf (certNat% 2407))
 (.leaf (certNat% 2408))))))))
 (.branch 2436
 (.branch 2422
 (.branch 2415
 (.branch 2412
 (.branch 2410
 (.leaf (certNat% 2409))
 (.branch 2411
 (.leaf (certNat% 2410))
 (.leaf (certNat% 2411))))
 (.branch 2413
 (.leaf (certNat% 2412))
 (.branch 2414
 (.leaf (certNat% 2413))
 (.leaf (certNat% 2414)))))
 (.branch 2418
 (.branch 2416
 (.leaf (certNat% 2415))
 (.branch 2417
 (.leaf (certNat% 2416))
 (.leaf (certNat% 2417))))
 (.branch 2420
 (.branch 2419
 (.leaf (certNat% 2418))
 (.leaf (certNat% 2419)))
 (.branch 2421
 (.leaf (certNat% 2420))
 (.leaf (certNat% 2421))))))
 (.branch 2429
 (.branch 2425
 (.branch 2423
 (.leaf (certNat% 2422))
 (.branch 2424
 (.leaf (certNat% 2423))
 (.leaf (certNat% 2424))))
 (.branch 2427
 (.branch 2426
 (.leaf (certNat% 2425))
 (.leaf (certNat% 2426)))
 (.branch 2428
 (.leaf (certNat% 2427))
 (.leaf (certNat% 2428)))))
 (.branch 2432
 (.branch 2430
 (.leaf (certNat% 2429))
 (.branch 2431
 (.leaf (certNat% 2430))
 (.leaf (certNat% 2431))))
 (.branch 2434
 (.branch 2433
 (.leaf (certNat% 2432))
 (.leaf (certNat% 2433)))
 (.branch 2435
 (.leaf (certNat% 2434))
 (.leaf (certNat% 2435)))))))
 (.branch 2449
 (.branch 2442
 (.branch 2439
 (.branch 2437
 (.leaf (certNat% 2436))
 (.branch 2438
 (.leaf (certNat% 2437))
 (.leaf (certNat% 2438))))
 (.branch 2440
 (.leaf (certNat% 2439))
 (.branch 2441
 (.leaf (certNat% 2440))
 (.leaf (certNat% 2441)))))
 (.branch 2445
 (.branch 2443
 (.leaf (certNat% 2442))
 (.branch 2444
 (.leaf (certNat% 2443))
 (.leaf (certNat% 2444))))
 (.branch 2447
 (.branch 2446
 (.leaf (certNat% 2445))
 (.leaf (certNat% 2446)))
 (.branch 2448
 (.leaf (certNat% 2447))
 (.leaf (certNat% 2448))))))
 (.branch 2456
 (.branch 2452
 (.branch 2450
 (.leaf (certNat% 2449))
 (.branch 2451
 (.leaf (certNat% 2450))
 (.leaf (certNat% 2451))))
 (.branch 2454
 (.branch 2453
 (.leaf (certNat% 2452))
 (.leaf (certNat% 2453)))
 (.branch 2455
 (.leaf (certNat% 2454))
 (.leaf (certNat% 2455)))))
 (.branch 2459
 (.branch 2457
 (.leaf (certNat% 2456))
 (.branch 2458
 (.leaf (certNat% 2457))
 (.leaf (certNat% 2458))))
 (.branch 2461
 (.branch 2460
 (.leaf (certNat% 2459))
 (.leaf (certNat% 2460)))
 (.branch 2462
 (.leaf (certNat% 2461))
 (.leaf (certNat% 2462)))))))))
 (.branch 2517
 (.branch 2490
 (.branch 2476
 (.branch 2469
 (.branch 2466
 (.branch 2464
 (.leaf (certNat% 2463))
 (.branch 2465
 (.leaf (certNat% 2464))
 (.leaf (certNat% 2465))))
 (.branch 2467
 (.leaf (certNat% 2466))
 (.branch 2468
 (.leaf (certNat% 2467))
 (.leaf (certNat% 2468)))))
 (.branch 2472
 (.branch 2470
 (.leaf (certNat% 2469))
 (.branch 2471
 (.leaf (certNat% 2470))
 (.leaf (certNat% 2471))))
 (.branch 2474
 (.branch 2473
 (.leaf (certNat% 2472))
 (.leaf (certNat% 2473)))
 (.branch 2475
 (.leaf (certNat% 2474))
 (.leaf (certNat% 2475))))))
 (.branch 2483
 (.branch 2479
 (.branch 2477
 (.leaf (certNat% 2476))
 (.branch 2478
 (.leaf (certNat% 2477))
 (.leaf (certNat% 2478))))
 (.branch 2481
 (.branch 2480
 (.leaf (certNat% 2479))
 (.leaf (certNat% 2480)))
 (.branch 2482
 (.leaf (certNat% 2481))
 (.leaf (certNat% 2482)))))
 (.branch 2486
 (.branch 2484
 (.leaf (certNat% 2483))
 (.branch 2485
 (.leaf (certNat% 2484))
 (.leaf (certNat% 2485))))
 (.branch 2488
 (.branch 2487
 (.leaf (certNat% 2486))
 (.leaf (certNat% 2487)))
 (.branch 2489
 (.leaf (certNat% 2488))
 (.leaf (certNat% 2489)))))))
 (.branch 2503
 (.branch 2496
 (.branch 2493
 (.branch 2491
 (.leaf (certNat% 2490))
 (.branch 2492
 (.leaf (certNat% 2491))
 (.leaf (certNat% 2492))))
 (.branch 2494
 (.leaf (certNat% 2493))
 (.branch 2495
 (.leaf (certNat% 2494))
 (.leaf (certNat% 2495)))))
 (.branch 2499
 (.branch 2497
 (.leaf (certNat% 2496))
 (.branch 2498
 (.leaf (certNat% 2497))
 (.leaf (certNat% 2498))))
 (.branch 2501
 (.branch 2500
 (.leaf (certNat% 2499))
 (.leaf (certNat% 2500)))
 (.branch 2502
 (.leaf (certNat% 2501))
 (.leaf (certNat% 2502))))))
 (.branch 2510
 (.branch 2506
 (.branch 2504
 (.leaf (certNat% 2503))
 (.branch 2505
 (.leaf (certNat% 2504))
 (.leaf (certNat% 2505))))
 (.branch 2508
 (.branch 2507
 (.leaf (certNat% 2506))
 (.leaf (certNat% 2507)))
 (.branch 2509
 (.leaf (certNat% 2508))
 (.leaf (certNat% 2509)))))
 (.branch 2513
 (.branch 2511
 (.leaf (certNat% 2510))
 (.branch 2512
 (.leaf (certNat% 2511))
 (.leaf (certNat% 2512))))
 (.branch 2515
 (.branch 2514
 (.leaf (certNat% 2513))
 (.leaf (certNat% 2514)))
 (.branch 2516
 (.leaf (certNat% 2515))
 (.leaf (certNat% 2516))))))))
 (.branch 2544
 (.branch 2530
 (.branch 2523
 (.branch 2520
 (.branch 2518
 (.leaf (certNat% 2517))
 (.branch 2519
 (.leaf (certNat% 2518))
 (.leaf (certNat% 2519))))
 (.branch 2521
 (.leaf (certNat% 2520))
 (.branch 2522
 (.leaf (certNat% 2521))
 (.leaf (certNat% 2522)))))
 (.branch 2526
 (.branch 2524
 (.leaf (certNat% 2523))
 (.branch 2525
 (.leaf (certNat% 2524))
 (.leaf (certNat% 2525))))
 (.branch 2528
 (.branch 2527
 (.leaf (certNat% 2526))
 (.leaf (certNat% 2527)))
 (.branch 2529
 (.leaf (certNat% 2528))
 (.leaf (certNat% 2529))))))
 (.branch 2537
 (.branch 2533
 (.branch 2531
 (.leaf (certNat% 2530))
 (.branch 2532
 (.leaf (certNat% 2531))
 (.leaf (certNat% 2532))))
 (.branch 2535
 (.branch 2534
 (.leaf (certNat% 2533))
 (.leaf (certNat% 2534)))
 (.branch 2536
 (.leaf (certNat% 2535))
 (.leaf (certNat% 2536)))))
 (.branch 2540
 (.branch 2538
 (.leaf (certNat% 2537))
 (.branch 2539
 (.leaf (certNat% 2538))
 (.leaf (certNat% 2539))))
 (.branch 2542
 (.branch 2541
 (.leaf (certNat% 2540))
 (.leaf (certNat% 2541)))
 (.branch 2543
 (.leaf (certNat% 2542))
 (.leaf (certNat% 2543)))))))
 (.branch 2557
 (.branch 2550
 (.branch 2547
 (.branch 2545
 (.leaf (certNat% 2544))
 (.branch 2546
 (.leaf (certNat% 2545))
 (.leaf (certNat% 2546))))
 (.branch 2548
 (.leaf (certNat% 2547))
 (.branch 2549
 (.leaf (certNat% 2548))
 (.leaf (certNat% 2549)))))
 (.branch 2553
 (.branch 2551
 (.leaf (certNat% 2550))
 (.branch 2552
 (.leaf (certNat% 2551))
 (.leaf (certNat% 2552))))
 (.branch 2555
 (.branch 2554
 (.leaf (certNat% 2553))
 (.leaf (certNat% 2554)))
 (.branch 2556
 (.leaf (certNat% 2555))
 (.leaf (certNat% 2556))))))
 (.branch 2564
 (.branch 2560
 (.branch 2558
 (.leaf (certNat% 2557))
 (.branch 2559
 (.leaf (certNat% 2558))
 (.leaf (certNat% 2559))))
 (.branch 2562
 (.branch 2561
 (.leaf (certNat% 2560))
 (.leaf (certNat% 2561)))
 (.branch 2563
 (.leaf (certNat% 2562))
 (.leaf (certNat% 2563)))))
 (.branch 2567
 (.branch 2565
 (.leaf (certNat% 2564))
 (.branch 2566
 (.leaf (certNat% 2565))
 (.leaf (certNat% 2566))))
 (.branch 2569
 (.branch 2568
 (.leaf (certNat% 2567))
 (.leaf (certNat% 2568)))
 (.branch 2570
 (.leaf (certNat% 2569))
 (.leaf (certNat% 2570))))))))))))
 (.branch 2999
 (.branch 2785
 (.branch 2678
 (.branch 2624
 (.branch 2597
 (.branch 2584
 (.branch 2577
 (.branch 2574
 (.branch 2572
 (.leaf (certNat% 2571))
 (.branch 2573
 (.leaf (certNat% 2572))
 (.leaf (certNat% 2573))))
 (.branch 2575
 (.leaf (certNat% 2574))
 (.branch 2576
 (.leaf (certNat% 2575))
 (.leaf (certNat% 2576)))))
 (.branch 2580
 (.branch 2578
 (.leaf (certNat% 2577))
 (.branch 2579
 (.leaf (certNat% 2578))
 (.leaf (certNat% 2579))))
 (.branch 2582
 (.branch 2581
 (.leaf (certNat% 2580))
 (.leaf (certNat% 2581)))
 (.branch 2583
 (.leaf (certNat% 2582))
 (.leaf (certNat% 2583))))))
 (.branch 2590
 (.branch 2587
 (.branch 2585
 (.leaf (certNat% 2584))
 (.branch 2586
 (.leaf (certNat% 2585))
 (.leaf (certNat% 2586))))
 (.branch 2588
 (.leaf (certNat% 2587))
 (.branch 2589
 (.leaf (certNat% 2588))
 (.leaf (certNat% 2589)))))
 (.branch 2593
 (.branch 2591
 (.leaf (certNat% 2590))
 (.branch 2592
 (.leaf (certNat% 2591))
 (.leaf (certNat% 2592))))
 (.branch 2595
 (.branch 2594
 (.leaf (certNat% 2593))
 (.leaf (certNat% 2594)))
 (.branch 2596
 (.leaf (certNat% 2595))
 (.leaf (certNat% 2596)))))))
 (.branch 2610
 (.branch 2603
 (.branch 2600
 (.branch 2598
 (.leaf (certNat% 2597))
 (.branch 2599
 (.leaf (certNat% 2598))
 (.leaf (certNat% 2599))))
 (.branch 2601
 (.leaf (certNat% 2600))
 (.branch 2602
 (.leaf (certNat% 2601))
 (.leaf (certNat% 2602)))))
 (.branch 2606
 (.branch 2604
 (.leaf (certNat% 2603))
 (.branch 2605
 (.leaf (certNat% 2604))
 (.leaf (certNat% 2605))))
 (.branch 2608
 (.branch 2607
 (.leaf (certNat% 2606))
 (.leaf (certNat% 2607)))
 (.branch 2609
 (.leaf (certNat% 2608))
 (.leaf (certNat% 2609))))))
 (.branch 2617
 (.branch 2613
 (.branch 2611
 (.leaf (certNat% 2610))
 (.branch 2612
 (.leaf (certNat% 2611))
 (.leaf (certNat% 2612))))
 (.branch 2615
 (.branch 2614
 (.leaf (certNat% 2613))
 (.leaf (certNat% 2614)))
 (.branch 2616
 (.leaf (certNat% 2615))
 (.leaf (certNat% 2616)))))
 (.branch 2620
 (.branch 2618
 (.leaf (certNat% 2617))
 (.branch 2619
 (.leaf (certNat% 2618))
 (.leaf (certNat% 2619))))
 (.branch 2622
 (.branch 2621
 (.leaf (certNat% 2620))
 (.leaf (certNat% 2621)))
 (.branch 2623
 (.leaf (certNat% 2622))
 (.leaf (certNat% 2623))))))))
 (.branch 2651
 (.branch 2637
 (.branch 2630
 (.branch 2627
 (.branch 2625
 (.leaf (certNat% 2624))
 (.branch 2626
 (.leaf (certNat% 2625))
 (.leaf (certNat% 2626))))
 (.branch 2628
 (.leaf (certNat% 2627))
 (.branch 2629
 (.leaf (certNat% 2628))
 (.leaf (certNat% 2629)))))
 (.branch 2633
 (.branch 2631
 (.leaf (certNat% 2630))
 (.branch 2632
 (.leaf (certNat% 2631))
 (.leaf (certNat% 2632))))
 (.branch 2635
 (.branch 2634
 (.leaf (certNat% 2633))
 (.leaf (certNat% 2634)))
 (.branch 2636
 (.leaf (certNat% 2635))
 (.leaf (certNat% 2636))))))
 (.branch 2644
 (.branch 2640
 (.branch 2638
 (.leaf (certNat% 2637))
 (.branch 2639
 (.leaf (certNat% 2638))
 (.leaf (certNat% 2639))))
 (.branch 2642
 (.branch 2641
 (.leaf (certNat% 2640))
 (.leaf (certNat% 2641)))
 (.branch 2643
 (.leaf (certNat% 2642))
 (.leaf (certNat% 2643)))))
 (.branch 2647
 (.branch 2645
 (.leaf (certNat% 2644))
 (.branch 2646
 (.leaf (certNat% 2645))
 (.leaf (certNat% 2646))))
 (.branch 2649
 (.branch 2648
 (.leaf (certNat% 2647))
 (.leaf (certNat% 2648)))
 (.branch 2650
 (.leaf (certNat% 2649))
 (.leaf (certNat% 2650)))))))
 (.branch 2664
 (.branch 2657
 (.branch 2654
 (.branch 2652
 (.leaf (certNat% 2651))
 (.branch 2653
 (.leaf (certNat% 2652))
 (.leaf (certNat% 2653))))
 (.branch 2655
 (.leaf (certNat% 2654))
 (.branch 2656
 (.leaf (certNat% 2655))
 (.leaf (certNat% 2656)))))
 (.branch 2660
 (.branch 2658
 (.leaf (certNat% 2657))
 (.branch 2659
 (.leaf (certNat% 2658))
 (.leaf (certNat% 2659))))
 (.branch 2662
 (.branch 2661
 (.leaf (certNat% 2660))
 (.leaf (certNat% 2661)))
 (.branch 2663
 (.leaf (certNat% 2662))
 (.leaf (certNat% 2663))))))
 (.branch 2671
 (.branch 2667
 (.branch 2665
 (.leaf (certNat% 2664))
 (.branch 2666
 (.leaf (certNat% 2665))
 (.leaf (certNat% 2666))))
 (.branch 2669
 (.branch 2668
 (.leaf (certNat% 2667))
 (.leaf (certNat% 2668)))
 (.branch 2670
 (.leaf (certNat% 2669))
 (.leaf (certNat% 2670)))))
 (.branch 2674
 (.branch 2672
 (.leaf (certNat% 2671))
 (.branch 2673
 (.leaf (certNat% 2672))
 (.leaf (certNat% 2673))))
 (.branch 2676
 (.branch 2675
 (.leaf (certNat% 2674))
 (.leaf (certNat% 2675)))
 (.branch 2677
 (.leaf (certNat% 2676))
 (.leaf (certNat% 2677)))))))))
 (.branch 2731
 (.branch 2704
 (.branch 2691
 (.branch 2684
 (.branch 2681
 (.branch 2679
 (.leaf (certNat% 2678))
 (.branch 2680
 (.leaf (certNat% 2679))
 (.leaf (certNat% 2680))))
 (.branch 2682
 (.leaf (certNat% 2681))
 (.branch 2683
 (.leaf (certNat% 2682))
 (.leaf (certNat% 2683)))))
 (.branch 2687
 (.branch 2685
 (.leaf (certNat% 2684))
 (.branch 2686
 (.leaf (certNat% 2685))
 (.leaf (certNat% 2686))))
 (.branch 2689
 (.branch 2688
 (.leaf (certNat% 2687))
 (.leaf (certNat% 2688)))
 (.branch 2690
 (.leaf (certNat% 2689))
 (.leaf (certNat% 2690))))))
 (.branch 2697
 (.branch 2694
 (.branch 2692
 (.leaf (certNat% 2691))
 (.branch 2693
 (.leaf (certNat% 2692))
 (.leaf (certNat% 2693))))
 (.branch 2695
 (.leaf (certNat% 2694))
 (.branch 2696
 (.leaf (certNat% 2695))
 (.leaf (certNat% 2696)))))
 (.branch 2700
 (.branch 2698
 (.leaf (certNat% 2697))
 (.branch 2699
 (.leaf (certNat% 2698))
 (.leaf (certNat% 2699))))
 (.branch 2702
 (.branch 2701
 (.leaf (certNat% 2700))
 (.leaf (certNat% 2701)))
 (.branch 2703
 (.leaf (certNat% 2702))
 (.leaf (certNat% 2703)))))))
 (.branch 2717
 (.branch 2710
 (.branch 2707
 (.branch 2705
 (.leaf (certNat% 2704))
 (.branch 2706
 (.leaf (certNat% 2705))
 (.leaf (certNat% 2706))))
 (.branch 2708
 (.leaf (certNat% 2707))
 (.branch 2709
 (.leaf (certNat% 2708))
 (.leaf (certNat% 2709)))))
 (.branch 2713
 (.branch 2711
 (.leaf (certNat% 2710))
 (.branch 2712
 (.leaf (certNat% 2711))
 (.leaf (certNat% 2712))))
 (.branch 2715
 (.branch 2714
 (.leaf (certNat% 2713))
 (.leaf (certNat% 2714)))
 (.branch 2716
 (.leaf (certNat% 2715))
 (.leaf (certNat% 2716))))))
 (.branch 2724
 (.branch 2720
 (.branch 2718
 (.leaf (certNat% 2717))
 (.branch 2719
 (.leaf (certNat% 2718))
 (.leaf (certNat% 2719))))
 (.branch 2722
 (.branch 2721
 (.leaf (certNat% 2720))
 (.leaf (certNat% 2721)))
 (.branch 2723
 (.leaf (certNat% 2722))
 (.leaf (certNat% 2723)))))
 (.branch 2727
 (.branch 2725
 (.leaf (certNat% 2724))
 (.branch 2726
 (.leaf (certNat% 2725))
 (.leaf (certNat% 2726))))
 (.branch 2729
 (.branch 2728
 (.leaf (certNat% 2727))
 (.leaf (certNat% 2728)))
 (.branch 2730
 (.leaf (certNat% 2729))
 (.leaf (certNat% 2730))))))))
 (.branch 2758
 (.branch 2744
 (.branch 2737
 (.branch 2734
 (.branch 2732
 (.leaf (certNat% 2731))
 (.branch 2733
 (.leaf (certNat% 2732))
 (.leaf (certNat% 2733))))
 (.branch 2735
 (.leaf (certNat% 2734))
 (.branch 2736
 (.leaf (certNat% 2735))
 (.leaf (certNat% 2736)))))
 (.branch 2740
 (.branch 2738
 (.leaf (certNat% 2737))
 (.branch 2739
 (.leaf (certNat% 2738))
 (.leaf (certNat% 2739))))
 (.branch 2742
 (.branch 2741
 (.leaf (certNat% 2740))
 (.leaf (certNat% 2741)))
 (.branch 2743
 (.leaf (certNat% 2742))
 (.leaf (certNat% 2743))))))
 (.branch 2751
 (.branch 2747
 (.branch 2745
 (.leaf (certNat% 2744))
 (.branch 2746
 (.leaf (certNat% 2745))
 (.leaf (certNat% 2746))))
 (.branch 2749
 (.branch 2748
 (.leaf (certNat% 2747))
 (.leaf (certNat% 2748)))
 (.branch 2750
 (.leaf (certNat% 2749))
 (.leaf (certNat% 2750)))))
 (.branch 2754
 (.branch 2752
 (.leaf (certNat% 2751))
 (.branch 2753
 (.leaf (certNat% 2752))
 (.leaf (certNat% 2753))))
 (.branch 2756
 (.branch 2755
 (.leaf (certNat% 2754))
 (.leaf (certNat% 2755)))
 (.branch 2757
 (.leaf (certNat% 2756))
 (.leaf (certNat% 2757)))))))
 (.branch 2771
 (.branch 2764
 (.branch 2761
 (.branch 2759
 (.leaf (certNat% 2758))
 (.branch 2760
 (.leaf (certNat% 2759))
 (.leaf (certNat% 2760))))
 (.branch 2762
 (.leaf (certNat% 2761))
 (.branch 2763
 (.leaf (certNat% 2762))
 (.leaf (certNat% 2763)))))
 (.branch 2767
 (.branch 2765
 (.leaf (certNat% 2764))
 (.branch 2766
 (.leaf (certNat% 2765))
 (.leaf (certNat% 2766))))
 (.branch 2769
 (.branch 2768
 (.leaf (certNat% 2767))
 (.leaf (certNat% 2768)))
 (.branch 2770
 (.leaf (certNat% 2769))
 (.leaf (certNat% 2770))))))
 (.branch 2778
 (.branch 2774
 (.branch 2772
 (.leaf (certNat% 2771))
 (.branch 2773
 (.leaf (certNat% 2772))
 (.leaf (certNat% 2773))))
 (.branch 2776
 (.branch 2775
 (.leaf (certNat% 2774))
 (.leaf (certNat% 2775)))
 (.branch 2777
 (.leaf (certNat% 2776))
 (.leaf (certNat% 2777)))))
 (.branch 2781
 (.branch 2779
 (.leaf (certNat% 2778))
 (.branch 2780
 (.leaf (certNat% 2779))
 (.leaf (certNat% 2780))))
 (.branch 2783
 (.branch 2782
 (.leaf (certNat% 2781))
 (.leaf (certNat% 2782)))
 (.branch 2784
 (.leaf (certNat% 2783))
 (.leaf (certNat% 2784))))))))))
 (.branch 2892
 (.branch 2838
 (.branch 2811
 (.branch 2798
 (.branch 2791
 (.branch 2788
 (.branch 2786
 (.leaf (certNat% 2785))
 (.branch 2787
 (.leaf (certNat% 2786))
 (.leaf (certNat% 2787))))
 (.branch 2789
 (.leaf (certNat% 2788))
 (.branch 2790
 (.leaf (certNat% 2789))
 (.leaf (certNat% 2790)))))
 (.branch 2794
 (.branch 2792
 (.leaf (certNat% 2791))
 (.branch 2793
 (.leaf (certNat% 2792))
 (.leaf (certNat% 2793))))
 (.branch 2796
 (.branch 2795
 (.leaf (certNat% 2794))
 (.leaf (certNat% 2795)))
 (.branch 2797
 (.leaf (certNat% 2796))
 (.leaf (certNat% 2797))))))
 (.branch 2804
 (.branch 2801
 (.branch 2799
 (.leaf (certNat% 2798))
 (.branch 2800
 (.leaf (certNat% 2799))
 (.leaf (certNat% 2800))))
 (.branch 2802
 (.leaf (certNat% 2801))
 (.branch 2803
 (.leaf (certNat% 2802))
 (.leaf (certNat% 2803)))))
 (.branch 2807
 (.branch 2805
 (.leaf (certNat% 2804))
 (.branch 2806
 (.leaf (certNat% 2805))
 (.leaf (certNat% 2806))))
 (.branch 2809
 (.branch 2808
 (.leaf (certNat% 2807))
 (.leaf (certNat% 2808)))
 (.branch 2810
 (.leaf (certNat% 2809))
 (.leaf (certNat% 2810)))))))
 (.branch 2824
 (.branch 2817
 (.branch 2814
 (.branch 2812
 (.leaf (certNat% 2811))
 (.branch 2813
 (.leaf (certNat% 2812))
 (.leaf (certNat% 2813))))
 (.branch 2815
 (.leaf (certNat% 2814))
 (.branch 2816
 (.leaf (certNat% 2815))
 (.leaf (certNat% 2816)))))
 (.branch 2820
 (.branch 2818
 (.leaf (certNat% 2817))
 (.branch 2819
 (.leaf (certNat% 2818))
 (.leaf (certNat% 2819))))
 (.branch 2822
 (.branch 2821
 (.leaf (certNat% 2820))
 (.leaf (certNat% 2821)))
 (.branch 2823
 (.leaf (certNat% 2822))
 (.leaf (certNat% 2823))))))
 (.branch 2831
 (.branch 2827
 (.branch 2825
 (.leaf (certNat% 2824))
 (.branch 2826
 (.leaf (certNat% 2825))
 (.leaf (certNat% 2826))))
 (.branch 2829
 (.branch 2828
 (.leaf (certNat% 2827))
 (.leaf (certNat% 2828)))
 (.branch 2830
 (.leaf (certNat% 2829))
 (.leaf (certNat% 2830)))))
 (.branch 2834
 (.branch 2832
 (.leaf (certNat% 2831))
 (.branch 2833
 (.leaf (certNat% 2832))
 (.leaf (certNat% 2833))))
 (.branch 2836
 (.branch 2835
 (.leaf (certNat% 2834))
 (.leaf (certNat% 2835)))
 (.branch 2837
 (.leaf (certNat% 2836))
 (.leaf (certNat% 2837))))))))
 (.branch 2865
 (.branch 2851
 (.branch 2844
 (.branch 2841
 (.branch 2839
 (.leaf (certNat% 2838))
 (.branch 2840
 (.leaf (certNat% 2839))
 (.leaf (certNat% 2840))))
 (.branch 2842
 (.leaf (certNat% 2841))
 (.branch 2843
 (.leaf (certNat% 2842))
 (.leaf (certNat% 2843)))))
 (.branch 2847
 (.branch 2845
 (.leaf (certNat% 2844))
 (.branch 2846
 (.leaf (certNat% 2845))
 (.leaf (certNat% 2846))))
 (.branch 2849
 (.branch 2848
 (.leaf (certNat% 2847))
 (.leaf (certNat% 2848)))
 (.branch 2850
 (.leaf (certNat% 2849))
 (.leaf (certNat% 2850))))))
 (.branch 2858
 (.branch 2854
 (.branch 2852
 (.leaf (certNat% 2851))
 (.branch 2853
 (.leaf (certNat% 2852))
 (.leaf (certNat% 2853))))
 (.branch 2856
 (.branch 2855
 (.leaf (certNat% 2854))
 (.leaf (certNat% 2855)))
 (.branch 2857
 (.leaf (certNat% 2856))
 (.leaf (certNat% 2857)))))
 (.branch 2861
 (.branch 2859
 (.leaf (certNat% 2858))
 (.branch 2860
 (.leaf (certNat% 2859))
 (.leaf (certNat% 2860))))
 (.branch 2863
 (.branch 2862
 (.leaf (certNat% 2861))
 (.leaf (certNat% 2862)))
 (.branch 2864
 (.leaf (certNat% 2863))
 (.leaf (certNat% 2864)))))))
 (.branch 2878
 (.branch 2871
 (.branch 2868
 (.branch 2866
 (.leaf (certNat% 2865))
 (.branch 2867
 (.leaf (certNat% 2866))
 (.leaf (certNat% 2867))))
 (.branch 2869
 (.leaf (certNat% 2868))
 (.branch 2870
 (.leaf (certNat% 2869))
 (.leaf (certNat% 2870)))))
 (.branch 2874
 (.branch 2872
 (.leaf (certNat% 2871))
 (.branch 2873
 (.leaf (certNat% 2872))
 (.leaf (certNat% 2873))))
 (.branch 2876
 (.branch 2875
 (.leaf (certNat% 2874))
 (.leaf (certNat% 2875)))
 (.branch 2877
 (.leaf (certNat% 2876))
 (.leaf (certNat% 2877))))))
 (.branch 2885
 (.branch 2881
 (.branch 2879
 (.leaf (certNat% 2878))
 (.branch 2880
 (.leaf (certNat% 2879))
 (.leaf (certNat% 2880))))
 (.branch 2883
 (.branch 2882
 (.leaf (certNat% 2881))
 (.leaf (certNat% 2882)))
 (.branch 2884
 (.leaf (certNat% 2883))
 (.leaf (certNat% 2884)))))
 (.branch 2888
 (.branch 2886
 (.leaf (certNat% 2885))
 (.branch 2887
 (.leaf (certNat% 2886))
 (.leaf (certNat% 2887))))
 (.branch 2890
 (.branch 2889
 (.leaf (certNat% 2888))
 (.leaf (certNat% 2889)))
 (.branch 2891
 (.leaf (certNat% 2890))
 (.leaf (certNat% 2891)))))))))
 (.branch 2945
 (.branch 2918
 (.branch 2905
 (.branch 2898
 (.branch 2895
 (.branch 2893
 (.leaf (certNat% 2892))
 (.branch 2894
 (.leaf (certNat% 2893))
 (.leaf (certNat% 2894))))
 (.branch 2896
 (.leaf (certNat% 2895))
 (.branch 2897
 (.leaf (certNat% 2896))
 (.leaf (certNat% 2897)))))
 (.branch 2901
 (.branch 2899
 (.leaf (certNat% 2898))
 (.branch 2900
 (.leaf (certNat% 2899))
 (.leaf (certNat% 2900))))
 (.branch 2903
 (.branch 2902
 (.leaf (certNat% 2901))
 (.leaf (certNat% 2902)))
 (.branch 2904
 (.leaf (certNat% 2903))
 (.leaf (certNat% 2904))))))
 (.branch 2911
 (.branch 2908
 (.branch 2906
 (.leaf (certNat% 2905))
 (.branch 2907
 (.leaf (certNat% 2906))
 (.leaf (certNat% 2907))))
 (.branch 2909
 (.leaf (certNat% 2908))
 (.branch 2910
 (.leaf (certNat% 2909))
 (.leaf (certNat% 2910)))))
 (.branch 2914
 (.branch 2912
 (.leaf (certNat% 2911))
 (.branch 2913
 (.leaf (certNat% 2912))
 (.leaf (certNat% 2913))))
 (.branch 2916
 (.branch 2915
 (.leaf (certNat% 2914))
 (.leaf (certNat% 2915)))
 (.branch 2917
 (.leaf (certNat% 2916))
 (.leaf (certNat% 2917)))))))
 (.branch 2931
 (.branch 2924
 (.branch 2921
 (.branch 2919
 (.leaf (certNat% 2918))
 (.branch 2920
 (.leaf (certNat% 2919))
 (.leaf (certNat% 2920))))
 (.branch 2922
 (.leaf (certNat% 2921))
 (.branch 2923
 (.leaf (certNat% 2922))
 (.leaf (certNat% 2923)))))
 (.branch 2927
 (.branch 2925
 (.leaf (certNat% 2924))
 (.branch 2926
 (.leaf (certNat% 2925))
 (.leaf (certNat% 2926))))
 (.branch 2929
 (.branch 2928
 (.leaf (certNat% 2927))
 (.leaf (certNat% 2928)))
 (.branch 2930
 (.leaf (certNat% 2929))
 (.leaf (certNat% 2930))))))
 (.branch 2938
 (.branch 2934
 (.branch 2932
 (.leaf (certNat% 2931))
 (.branch 2933
 (.leaf (certNat% 2932))
 (.leaf (certNat% 2933))))
 (.branch 2936
 (.branch 2935
 (.leaf (certNat% 2934))
 (.leaf (certNat% 2935)))
 (.branch 2937
 (.leaf (certNat% 2936))
 (.leaf (certNat% 2937)))))
 (.branch 2941
 (.branch 2939
 (.leaf (certNat% 2938))
 (.branch 2940
 (.leaf (certNat% 2939))
 (.leaf (certNat% 2940))))
 (.branch 2943
 (.branch 2942
 (.leaf (certNat% 2941))
 (.leaf (certNat% 2942)))
 (.branch 2944
 (.leaf (certNat% 2943))
 (.leaf (certNat% 2944))))))))
 (.branch 2972
 (.branch 2958
 (.branch 2951
 (.branch 2948
 (.branch 2946
 (.leaf (certNat% 2945))
 (.branch 2947
 (.leaf (certNat% 2946))
 (.leaf (certNat% 2947))))
 (.branch 2949
 (.leaf (certNat% 2948))
 (.branch 2950
 (.leaf (certNat% 2949))
 (.leaf (certNat% 2950)))))
 (.branch 2954
 (.branch 2952
 (.leaf (certNat% 2951))
 (.branch 2953
 (.leaf (certNat% 2952))
 (.leaf (certNat% 2953))))
 (.branch 2956
 (.branch 2955
 (.leaf (certNat% 2954))
 (.leaf (certNat% 2955)))
 (.branch 2957
 (.leaf (certNat% 2956))
 (.leaf (certNat% 2957))))))
 (.branch 2965
 (.branch 2961
 (.branch 2959
 (.leaf (certNat% 2958))
 (.branch 2960
 (.leaf (certNat% 2959))
 (.leaf (certNat% 2960))))
 (.branch 2963
 (.branch 2962
 (.leaf (certNat% 2961))
 (.leaf (certNat% 2962)))
 (.branch 2964
 (.leaf (certNat% 2963))
 (.leaf (certNat% 2964)))))
 (.branch 2968
 (.branch 2966
 (.leaf (certNat% 2965))
 (.branch 2967
 (.leaf (certNat% 2966))
 (.leaf (certNat% 2967))))
 (.branch 2970
 (.branch 2969
 (.leaf (certNat% 2968))
 (.leaf (certNat% 2969)))
 (.branch 2971
 (.leaf (certNat% 2970))
 (.leaf (certNat% 2971)))))))
 (.branch 2985
 (.branch 2978
 (.branch 2975
 (.branch 2973
 (.leaf (certNat% 2972))
 (.branch 2974
 (.leaf (certNat% 2973))
 (.leaf (certNat% 2974))))
 (.branch 2976
 (.leaf (certNat% 2975))
 (.branch 2977
 (.leaf (certNat% 2976))
 (.leaf (certNat% 2977)))))
 (.branch 2981
 (.branch 2979
 (.leaf (certNat% 2978))
 (.branch 2980
 (.leaf (certNat% 2979))
 (.leaf (certNat% 2980))))
 (.branch 2983
 (.branch 2982
 (.leaf (certNat% 2981))
 (.leaf (certNat% 2982)))
 (.branch 2984
 (.leaf (certNat% 2983))
 (.leaf (certNat% 2984))))))
 (.branch 2992
 (.branch 2988
 (.branch 2986
 (.leaf (certNat% 2985))
 (.branch 2987
 (.leaf (certNat% 2986))
 (.leaf (certNat% 2987))))
 (.branch 2990
 (.branch 2989
 (.leaf (certNat% 2988))
 (.leaf (certNat% 2989)))
 (.branch 2991
 (.leaf (certNat% 2990))
 (.leaf (certNat% 2991)))))
 (.branch 2995
 (.branch 2993
 (.leaf (certNat% 2992))
 (.branch 2994
 (.leaf (certNat% 2993))
 (.leaf (certNat% 2994))))
 (.branch 2997
 (.branch 2996
 (.leaf (certNat% 2995))
 (.leaf (certNat% 2996)))
 (.branch 2998
 (.leaf (certNat% 2997))
 (.leaf (certNat% 2998)))))))))))
 (.branch 3213
 (.branch 3106
 (.branch 3052
 (.branch 3025
 (.branch 3012
 (.branch 3005
 (.branch 3002
 (.branch 3000
 (.leaf (certNat% 2999))
 (.branch 3001
 (.leaf (certNat% 3000))
 (.leaf (certNat% 3001))))
 (.branch 3003
 (.leaf (certNat% 3002))
 (.branch 3004
 (.leaf (certNat% 3003))
 (.leaf (certNat% 3004)))))
 (.branch 3008
 (.branch 3006
 (.leaf (certNat% 3005))
 (.branch 3007
 (.leaf (certNat% 3006))
 (.leaf (certNat% 3007))))
 (.branch 3010
 (.branch 3009
 (.leaf (certNat% 3008))
 (.leaf (certNat% 3009)))
 (.branch 3011
 (.leaf (certNat% 3010))
 (.leaf (certNat% 3011))))))
 (.branch 3018
 (.branch 3015
 (.branch 3013
 (.leaf (certNat% 3012))
 (.branch 3014
 (.leaf (certNat% 3013))
 (.leaf (certNat% 3014))))
 (.branch 3016
 (.leaf (certNat% 3015))
 (.branch 3017
 (.leaf (certNat% 3016))
 (.leaf (certNat% 3017)))))
 (.branch 3021
 (.branch 3019
 (.leaf (certNat% 3018))
 (.branch 3020
 (.leaf (certNat% 3019))
 (.leaf (certNat% 3020))))
 (.branch 3023
 (.branch 3022
 (.leaf (certNat% 3021))
 (.leaf (certNat% 3022)))
 (.branch 3024
 (.leaf (certNat% 3023))
 (.leaf (certNat% 3024)))))))
 (.branch 3038
 (.branch 3031
 (.branch 3028
 (.branch 3026
 (.leaf (certNat% 3025))
 (.branch 3027
 (.leaf (certNat% 3026))
 (.leaf (certNat% 3027))))
 (.branch 3029
 (.leaf (certNat% 3028))
 (.branch 3030
 (.leaf (certNat% 3029))
 (.leaf (certNat% 3030)))))
 (.branch 3034
 (.branch 3032
 (.leaf (certNat% 3031))
 (.branch 3033
 (.leaf (certNat% 3032))
 (.leaf (certNat% 3033))))
 (.branch 3036
 (.branch 3035
 (.leaf (certNat% 3034))
 (.leaf (certNat% 3035)))
 (.branch 3037
 (.leaf (certNat% 3036))
 (.leaf (certNat% 3037))))))
 (.branch 3045
 (.branch 3041
 (.branch 3039
 (.leaf (certNat% 3038))
 (.branch 3040
 (.leaf (certNat% 3039))
 (.leaf (certNat% 3040))))
 (.branch 3043
 (.branch 3042
 (.leaf (certNat% 3041))
 (.leaf (certNat% 3042)))
 (.branch 3044
 (.leaf (certNat% 3043))
 (.leaf (certNat% 3044)))))
 (.branch 3048
 (.branch 3046
 (.leaf (certNat% 3045))
 (.branch 3047
 (.leaf (certNat% 3046))
 (.leaf (certNat% 3047))))
 (.branch 3050
 (.branch 3049
 (.leaf (certNat% 3048))
 (.leaf (certNat% 3049)))
 (.branch 3051
 (.leaf (certNat% 3050))
 (.leaf (certNat% 3051))))))))
 (.branch 3079
 (.branch 3065
 (.branch 3058
 (.branch 3055
 (.branch 3053
 (.leaf (certNat% 3052))
 (.branch 3054
 (.leaf (certNat% 3053))
 (.leaf (certNat% 3054))))
 (.branch 3056
 (.leaf (certNat% 3055))
 (.branch 3057
 (.leaf (certNat% 3056))
 (.leaf (certNat% 3057)))))
 (.branch 3061
 (.branch 3059
 (.leaf (certNat% 3058))
 (.branch 3060
 (.leaf (certNat% 3059))
 (.leaf (certNat% 3060))))
 (.branch 3063
 (.branch 3062
 (.leaf (certNat% 3061))
 (.leaf (certNat% 3062)))
 (.branch 3064
 (.leaf (certNat% 3063))
 (.leaf (certNat% 3064))))))
 (.branch 3072
 (.branch 3068
 (.branch 3066
 (.leaf (certNat% 3065))
 (.branch 3067
 (.leaf (certNat% 3066))
 (.leaf (certNat% 3067))))
 (.branch 3070
 (.branch 3069
 (.leaf (certNat% 3068))
 (.leaf (certNat% 3069)))
 (.branch 3071
 (.leaf (certNat% 3070))
 (.leaf (certNat% 3071)))))
 (.branch 3075
 (.branch 3073
 (.leaf (certNat% 3072))
 (.branch 3074
 (.leaf (certNat% 3073))
 (.leaf (certNat% 3074))))
 (.branch 3077
 (.branch 3076
 (.leaf (certNat% 3075))
 (.leaf (certNat% 3076)))
 (.branch 3078
 (.leaf (certNat% 3077))
 (.leaf (certNat% 3078)))))))
 (.branch 3092
 (.branch 3085
 (.branch 3082
 (.branch 3080
 (.leaf (certNat% 3079))
 (.branch 3081
 (.leaf (certNat% 3080))
 (.leaf (certNat% 3081))))
 (.branch 3083
 (.leaf (certNat% 3082))
 (.branch 3084
 (.leaf (certNat% 3083))
 (.leaf (certNat% 3084)))))
 (.branch 3088
 (.branch 3086
 (.leaf (certNat% 3085))
 (.branch 3087
 (.leaf (certNat% 3086))
 (.leaf (certNat% 3087))))
 (.branch 3090
 (.branch 3089
 (.leaf (certNat% 3088))
 (.leaf (certNat% 3089)))
 (.branch 3091
 (.leaf (certNat% 3090))
 (.leaf (certNat% 3091))))))
 (.branch 3099
 (.branch 3095
 (.branch 3093
 (.leaf (certNat% 3092))
 (.branch 3094
 (.leaf (certNat% 3093))
 (.leaf (certNat% 3094))))
 (.branch 3097
 (.branch 3096
 (.leaf (certNat% 3095))
 (.leaf (certNat% 3096)))
 (.branch 3098
 (.leaf (certNat% 3097))
 (.leaf (certNat% 3098)))))
 (.branch 3102
 (.branch 3100
 (.leaf (certNat% 3099))
 (.branch 3101
 (.leaf (certNat% 3100))
 (.leaf (certNat% 3101))))
 (.branch 3104
 (.branch 3103
 (.leaf (certNat% 3102))
 (.leaf (certNat% 3103)))
 (.branch 3105
 (.leaf (certNat% 3104))
 (.leaf (certNat% 3105)))))))))
 (.branch 3159
 (.branch 3132
 (.branch 3119
 (.branch 3112
 (.branch 3109
 (.branch 3107
 (.leaf (certNat% 3106))
 (.branch 3108
 (.leaf (certNat% 3107))
 (.leaf (certNat% 3108))))
 (.branch 3110
 (.leaf (certNat% 3109))
 (.branch 3111
 (.leaf (certNat% 3110))
 (.leaf (certNat% 3111)))))
 (.branch 3115
 (.branch 3113
 (.leaf (certNat% 3112))
 (.branch 3114
 (.leaf (certNat% 3113))
 (.leaf (certNat% 3114))))
 (.branch 3117
 (.branch 3116
 (.leaf (certNat% 3115))
 (.leaf (certNat% 3116)))
 (.branch 3118
 (.leaf (certNat% 3117))
 (.leaf (certNat% 3118))))))
 (.branch 3125
 (.branch 3122
 (.branch 3120
 (.leaf (certNat% 3119))
 (.branch 3121
 (.leaf (certNat% 3120))
 (.leaf (certNat% 3121))))
 (.branch 3123
 (.leaf (certNat% 3122))
 (.branch 3124
 (.leaf (certNat% 3123))
 (.leaf (certNat% 3124)))))
 (.branch 3128
 (.branch 3126
 (.leaf (certNat% 3125))
 (.branch 3127
 (.leaf (certNat% 3126))
 (.leaf (certNat% 3127))))
 (.branch 3130
 (.branch 3129
 (.leaf (certNat% 3128))
 (.leaf (certNat% 3129)))
 (.branch 3131
 (.leaf (certNat% 3130))
 (.leaf (certNat% 3131)))))))
 (.branch 3145
 (.branch 3138
 (.branch 3135
 (.branch 3133
 (.leaf (certNat% 3132))
 (.branch 3134
 (.leaf (certNat% 3133))
 (.leaf (certNat% 3134))))
 (.branch 3136
 (.leaf (certNat% 3135))
 (.branch 3137
 (.leaf (certNat% 3136))
 (.leaf (certNat% 3137)))))
 (.branch 3141
 (.branch 3139
 (.leaf (certNat% 3138))
 (.branch 3140
 (.leaf (certNat% 3139))
 (.leaf (certNat% 3140))))
 (.branch 3143
 (.branch 3142
 (.leaf (certNat% 3141))
 (.leaf (certNat% 3142)))
 (.branch 3144
 (.leaf (certNat% 3143))
 (.leaf (certNat% 3144))))))
 (.branch 3152
 (.branch 3148
 (.branch 3146
 (.leaf (certNat% 3145))
 (.branch 3147
 (.leaf (certNat% 3146))
 (.leaf (certNat% 3147))))
 (.branch 3150
 (.branch 3149
 (.leaf (certNat% 3148))
 (.leaf (certNat% 3149)))
 (.branch 3151
 (.leaf (certNat% 3150))
 (.leaf (certNat% 3151)))))
 (.branch 3155
 (.branch 3153
 (.leaf (certNat% 3152))
 (.branch 3154
 (.leaf (certNat% 3153))
 (.leaf (certNat% 3154))))
 (.branch 3157
 (.branch 3156
 (.leaf (certNat% 3155))
 (.leaf (certNat% 3156)))
 (.branch 3158
 (.leaf (certNat% 3157))
 (.leaf (certNat% 3158))))))))
 (.branch 3186
 (.branch 3172
 (.branch 3165
 (.branch 3162
 (.branch 3160
 (.leaf (certNat% 3159))
 (.branch 3161
 (.leaf (certNat% 3160))
 (.leaf (certNat% 3161))))
 (.branch 3163
 (.leaf (certNat% 3162))
 (.branch 3164
 (.leaf (certNat% 3163))
 (.leaf (certNat% 3164)))))
 (.branch 3168
 (.branch 3166
 (.leaf (certNat% 3165))
 (.branch 3167
 (.leaf (certNat% 3166))
 (.leaf (certNat% 3167))))
 (.branch 3170
 (.branch 3169
 (.leaf (certNat% 3168))
 (.leaf (certNat% 3169)))
 (.branch 3171
 (.leaf (certNat% 3170))
 (.leaf (certNat% 3171))))))
 (.branch 3179
 (.branch 3175
 (.branch 3173
 (.leaf (certNat% 3172))
 (.branch 3174
 (.leaf (certNat% 3173))
 (.leaf (certNat% 3174))))
 (.branch 3177
 (.branch 3176
 (.leaf (certNat% 3175))
 (.leaf (certNat% 3176)))
 (.branch 3178
 (.leaf (certNat% 3177))
 (.leaf (certNat% 3178)))))
 (.branch 3182
 (.branch 3180
 (.leaf (certNat% 3179))
 (.branch 3181
 (.leaf (certNat% 3180))
 (.leaf (certNat% 3181))))
 (.branch 3184
 (.branch 3183
 (.leaf (certNat% 3182))
 (.leaf (certNat% 3183)))
 (.branch 3185
 (.leaf (certNat% 3184))
 (.leaf (certNat% 3185)))))))
 (.branch 3199
 (.branch 3192
 (.branch 3189
 (.branch 3187
 (.leaf (certNat% 3186))
 (.branch 3188
 (.leaf (certNat% 3187))
 (.leaf (certNat% 3188))))
 (.branch 3190
 (.leaf (certNat% 3189))
 (.branch 3191
 (.leaf (certNat% 3190))
 (.leaf (certNat% 3191)))))
 (.branch 3195
 (.branch 3193
 (.leaf (certNat% 3192))
 (.branch 3194
 (.leaf (certNat% 3193))
 (.leaf (certNat% 3194))))
 (.branch 3197
 (.branch 3196
 (.leaf (certNat% 3195))
 (.leaf (certNat% 3196)))
 (.branch 3198
 (.leaf (certNat% 3197))
 (.leaf (certNat% 3198))))))
 (.branch 3206
 (.branch 3202
 (.branch 3200
 (.leaf (certNat% 3199))
 (.branch 3201
 (.leaf (certNat% 3200))
 (.leaf (certNat% 3201))))
 (.branch 3204
 (.branch 3203
 (.leaf (certNat% 3202))
 (.leaf (certNat% 3203)))
 (.branch 3205
 (.leaf (certNat% 3204))
 (.leaf (certNat% 3205)))))
 (.branch 3209
 (.branch 3207
 (.leaf (certNat% 3206))
 (.branch 3208
 (.leaf (certNat% 3207))
 (.leaf (certNat% 3208))))
 (.branch 3211
 (.branch 3210
 (.leaf (certNat% 3209))
 (.leaf (certNat% 3210)))
 (.branch 3212
 (.leaf (certNat% 3211))
 (.leaf (certNat% 3212))))))))))
 (.branch 3320
 (.branch 3266
 (.branch 3239
 (.branch 3226
 (.branch 3219
 (.branch 3216
 (.branch 3214
 (.leaf (certNat% 3213))
 (.branch 3215
 (.leaf (certNat% 3214))
 (.leaf (certNat% 3215))))
 (.branch 3217
 (.leaf (certNat% 3216))
 (.branch 3218
 (.leaf (certNat% 3217))
 (.leaf (certNat% 3218)))))
 (.branch 3222
 (.branch 3220
 (.leaf (certNat% 3219))
 (.branch 3221
 (.leaf (certNat% 3220))
 (.leaf (certNat% 3221))))
 (.branch 3224
 (.branch 3223
 (.leaf (certNat% 3222))
 (.leaf (certNat% 3223)))
 (.branch 3225
 (.leaf (certNat% 3224))
 (.leaf (certNat% 3225))))))
 (.branch 3232
 (.branch 3229
 (.branch 3227
 (.leaf (certNat% 3226))
 (.branch 3228
 (.leaf (certNat% 3227))
 (.leaf (certNat% 3228))))
 (.branch 3230
 (.leaf (certNat% 3229))
 (.branch 3231
 (.leaf (certNat% 3230))
 (.leaf (certNat% 3231)))))
 (.branch 3235
 (.branch 3233
 (.leaf (certNat% 3232))
 (.branch 3234
 (.leaf (certNat% 3233))
 (.leaf (certNat% 3234))))
 (.branch 3237
 (.branch 3236
 (.leaf (certNat% 3235))
 (.leaf (certNat% 3236)))
 (.branch 3238
 (.leaf (certNat% 3237))
 (.leaf (certNat% 3238)))))))
 (.branch 3252
 (.branch 3245
 (.branch 3242
 (.branch 3240
 (.leaf (certNat% 3239))
 (.branch 3241
 (.leaf (certNat% 3240))
 (.leaf (certNat% 3241))))
 (.branch 3243
 (.leaf (certNat% 3242))
 (.branch 3244
 (.leaf (certNat% 3243))
 (.leaf (certNat% 3244)))))
 (.branch 3248
 (.branch 3246
 (.leaf (certNat% 3245))
 (.branch 3247
 (.leaf (certNat% 3246))
 (.leaf (certNat% 3247))))
 (.branch 3250
 (.branch 3249
 (.leaf (certNat% 3248))
 (.leaf (certNat% 3249)))
 (.branch 3251
 (.leaf (certNat% 3250))
 (.leaf (certNat% 3251))))))
 (.branch 3259
 (.branch 3255
 (.branch 3253
 (.leaf (certNat% 3252))
 (.branch 3254
 (.leaf (certNat% 3253))
 (.leaf (certNat% 3254))))
 (.branch 3257
 (.branch 3256
 (.leaf (certNat% 3255))
 (.leaf (certNat% 3256)))
 (.branch 3258
 (.leaf (certNat% 3257))
 (.leaf (certNat% 3258)))))
 (.branch 3262
 (.branch 3260
 (.leaf (certNat% 3259))
 (.branch 3261
 (.leaf (certNat% 3260))
 (.leaf (certNat% 3261))))
 (.branch 3264
 (.branch 3263
 (.leaf (certNat% 3262))
 (.leaf (certNat% 3263)))
 (.branch 3265
 (.leaf (certNat% 3264))
 (.leaf (certNat% 3265))))))))
 (.branch 3293
 (.branch 3279
 (.branch 3272
 (.branch 3269
 (.branch 3267
 (.leaf (certNat% 3266))
 (.branch 3268
 (.leaf (certNat% 3267))
 (.leaf (certNat% 3268))))
 (.branch 3270
 (.leaf (certNat% 3269))
 (.branch 3271
 (.leaf (certNat% 3270))
 (.leaf (certNat% 3271)))))
 (.branch 3275
 (.branch 3273
 (.leaf (certNat% 3272))
 (.branch 3274
 (.leaf (certNat% 3273))
 (.leaf (certNat% 3274))))
 (.branch 3277
 (.branch 3276
 (.leaf (certNat% 3275))
 (.leaf (certNat% 3276)))
 (.branch 3278
 (.leaf (certNat% 3277))
 (.leaf (certNat% 3278))))))
 (.branch 3286
 (.branch 3282
 (.branch 3280
 (.leaf (certNat% 3279))
 (.branch 3281
 (.leaf (certNat% 3280))
 (.leaf (certNat% 3281))))
 (.branch 3284
 (.branch 3283
 (.leaf (certNat% 3282))
 (.leaf (certNat% 3283)))
 (.branch 3285
 (.leaf (certNat% 3284))
 (.leaf (certNat% 3285)))))
 (.branch 3289
 (.branch 3287
 (.leaf (certNat% 3286))
 (.branch 3288
 (.leaf (certNat% 3287))
 (.leaf (certNat% 3288))))
 (.branch 3291
 (.branch 3290
 (.leaf (certNat% 3289))
 (.leaf (certNat% 3290)))
 (.branch 3292
 (.leaf (certNat% 3291))
 (.leaf (certNat% 3292)))))))
 (.branch 3306
 (.branch 3299
 (.branch 3296
 (.branch 3294
 (.leaf (certNat% 3293))
 (.branch 3295
 (.leaf (certNat% 3294))
 (.leaf (certNat% 3295))))
 (.branch 3297
 (.leaf (certNat% 3296))
 (.branch 3298
 (.leaf (certNat% 3297))
 (.leaf (certNat% 3298)))))
 (.branch 3302
 (.branch 3300
 (.leaf (certNat% 3299))
 (.branch 3301
 (.leaf (certNat% 3300))
 (.leaf (certNat% 3301))))
 (.branch 3304
 (.branch 3303
 (.leaf (certNat% 3302))
 (.leaf (certNat% 3303)))
 (.branch 3305
 (.leaf (certNat% 3304))
 (.leaf (certNat% 3305))))))
 (.branch 3313
 (.branch 3309
 (.branch 3307
 (.leaf (certNat% 3306))
 (.branch 3308
 (.leaf (certNat% 3307))
 (.leaf (certNat% 3308))))
 (.branch 3311
 (.branch 3310
 (.leaf (certNat% 3309))
 (.leaf (certNat% 3310)))
 (.branch 3312
 (.leaf (certNat% 3311))
 (.leaf (certNat% 3312)))))
 (.branch 3316
 (.branch 3314
 (.leaf (certNat% 3313))
 (.branch 3315
 (.leaf (certNat% 3314))
 (.leaf (certNat% 3315))))
 (.branch 3318
 (.branch 3317
 (.leaf (certNat% 3316))
 (.leaf (certNat% 3317)))
 (.branch 3319
 (.leaf (certNat% 3318))
 (.leaf (certNat% 3319)))))))))
 (.branch 3374
 (.branch 3347
 (.branch 3333
 (.branch 3326
 (.branch 3323
 (.branch 3321
 (.leaf (certNat% 3320))
 (.branch 3322
 (.leaf (certNat% 3321))
 (.leaf (certNat% 3322))))
 (.branch 3324
 (.leaf (certNat% 3323))
 (.branch 3325
 (.leaf (certNat% 3324))
 (.leaf (certNat% 3325)))))
 (.branch 3329
 (.branch 3327
 (.leaf (certNat% 3326))
 (.branch 3328
 (.leaf (certNat% 3327))
 (.leaf (certNat% 3328))))
 (.branch 3331
 (.branch 3330
 (.leaf (certNat% 3329))
 (.leaf (certNat% 3330)))
 (.branch 3332
 (.leaf (certNat% 3331))
 (.leaf (certNat% 3332))))))
 (.branch 3340
 (.branch 3336
 (.branch 3334
 (.leaf (certNat% 3333))
 (.branch 3335
 (.leaf (certNat% 3334))
 (.leaf (certNat% 3335))))
 (.branch 3338
 (.branch 3337
 (.leaf (certNat% 3336))
 (.leaf (certNat% 3337)))
 (.branch 3339
 (.leaf (certNat% 3338))
 (.leaf (certNat% 3339)))))
 (.branch 3343
 (.branch 3341
 (.leaf (certNat% 3340))
 (.branch 3342
 (.leaf (certNat% 3341))
 (.leaf (certNat% 3342))))
 (.branch 3345
 (.branch 3344
 (.leaf (certNat% 3343))
 (.leaf (certNat% 3344)))
 (.branch 3346
 (.leaf (certNat% 3345))
 (.leaf (certNat% 3346)))))))
 (.branch 3360
 (.branch 3353
 (.branch 3350
 (.branch 3348
 (.leaf (certNat% 3347))
 (.branch 3349
 (.leaf (certNat% 3348))
 (.leaf (certNat% 3349))))
 (.branch 3351
 (.leaf (certNat% 3350))
 (.branch 3352
 (.leaf (certNat% 3351))
 (.leaf (certNat% 3352)))))
 (.branch 3356
 (.branch 3354
 (.leaf (certNat% 3353))
 (.branch 3355
 (.leaf (certNat% 3354))
 (.leaf (certNat% 3355))))
 (.branch 3358
 (.branch 3357
 (.leaf (certNat% 3356))
 (.leaf (certNat% 3357)))
 (.branch 3359
 (.leaf (certNat% 3358))
 (.leaf (certNat% 3359))))))
 (.branch 3367
 (.branch 3363
 (.branch 3361
 (.leaf (certNat% 3360))
 (.branch 3362
 (.leaf (certNat% 3361))
 (.leaf (certNat% 3362))))
 (.branch 3365
 (.branch 3364
 (.leaf (certNat% 3363))
 (.leaf (certNat% 3364)))
 (.branch 3366
 (.leaf (certNat% 3365))
 (.leaf (certNat% 3366)))))
 (.branch 3370
 (.branch 3368
 (.leaf (certNat% 3367))
 (.branch 3369
 (.leaf (certNat% 3368))
 (.leaf (certNat% 3369))))
 (.branch 3372
 (.branch 3371
 (.leaf (certNat% 3370))
 (.leaf (certNat% 3371)))
 (.branch 3373
 (.leaf (certNat% 3372))
 (.leaf (certNat% 3373))))))))
 (.branch 3401
 (.branch 3387
 (.branch 3380
 (.branch 3377
 (.branch 3375
 (.leaf (certNat% 3374))
 (.branch 3376
 (.leaf (certNat% 3375))
 (.leaf (certNat% 3376))))
 (.branch 3378
 (.leaf (certNat% 3377))
 (.branch 3379
 (.leaf (certNat% 3378))
 (.leaf (certNat% 3379)))))
 (.branch 3383
 (.branch 3381
 (.leaf (certNat% 3380))
 (.branch 3382
 (.leaf (certNat% 3381))
 (.leaf (certNat% 3382))))
 (.branch 3385
 (.branch 3384
 (.leaf (certNat% 3383))
 (.leaf (certNat% 3384)))
 (.branch 3386
 (.leaf (certNat% 3385))
 (.leaf (certNat% 3386))))))
 (.branch 3394
 (.branch 3390
 (.branch 3388
 (.leaf (certNat% 3387))
 (.branch 3389
 (.leaf (certNat% 3388))
 (.leaf (certNat% 3389))))
 (.branch 3392
 (.branch 3391
 (.leaf (certNat% 3390))
 (.leaf (certNat% 3391)))
 (.branch 3393
 (.leaf (certNat% 3392))
 (.leaf (certNat% 3393)))))
 (.branch 3397
 (.branch 3395
 (.leaf (certNat% 3394))
 (.branch 3396
 (.leaf (certNat% 3395))
 (.leaf (certNat% 3396))))
 (.branch 3399
 (.branch 3398
 (.leaf (certNat% 3397))
 (.leaf (certNat% 3398)))
 (.branch 3400
 (.leaf (certNat% 3399))
 (.leaf (certNat% 3400)))))))
 (.branch 3414
 (.branch 3407
 (.branch 3404
 (.branch 3402
 (.leaf (certNat% 3401))
 (.branch 3403
 (.leaf (certNat% 3402))
 (.leaf (certNat% 3403))))
 (.branch 3405
 (.leaf (certNat% 3404))
 (.branch 3406
 (.leaf (certNat% 3405))
 (.leaf (certNat% 3406)))))
 (.branch 3410
 (.branch 3408
 (.leaf (certNat% 3407))
 (.branch 3409
 (.leaf (certNat% 3408))
 (.leaf (certNat% 3409))))
 (.branch 3412
 (.branch 3411
 (.leaf (certNat% 3410))
 (.leaf (certNat% 3411)))
 (.branch 3413
 (.leaf (certNat% 3412))
 (.leaf (certNat% 3413))))))
 (.branch 3421
 (.branch 3417
 (.branch 3415
 (.leaf (certNat% 3414))
 (.branch 3416
 (.leaf (certNat% 3415))
 (.leaf (certNat% 3416))))
 (.branch 3419
 (.branch 3418
 (.leaf (certNat% 3417))
 (.leaf (certNat% 3418)))
 (.branch 3420
 (.leaf (certNat% 3419))
 (.leaf (certNat% 3420)))))
 (.branch 3424
 (.branch 3422
 (.leaf (certNat% 3421))
 (.branch 3423
 (.leaf (certNat% 3422))
 (.leaf (certNat% 3423))))
 (.branch 3426
 (.branch 3425
 (.leaf (certNat% 3424))
 (.leaf (certNat% 3425)))
 (.branch 3427
 (.leaf (certNat% 3426))
 (.leaf (certNat% 3427))))))))))))))
cert_rawLeaves_4 13
cert_leaves_3
cert_quota_3 0 4 0 0 0 0 0 0 3 6
cert_nodeTest_5 96 03
cert_nodeTest_sound_4 96 03
cert_leafTest_4 03
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724

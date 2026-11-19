module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public meta import CertificateNumbers
public import RootedSixBase02GrowthCacheData
public import RootedSixBase02FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification
public import RootedSubsumedForest0708Packed000
public import RootedSubsumedForest0708Packed001
public import RootedSubsumedForest0708Packed002
public import RootedSubsumedForest0708Packed003
public import RootedSubsumedForest0708Packed004
public import RootedSubsumedForest0708Packed005
public import RootedSubsumedForest0708Packed006
public import RootedSubsumedForest0708Packed007
public import RootedSubsumedForest0708Packed008
public import RootedSubsumedForest0708Packed009

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 8084
abbrev nodeCount : Nat := 60366
abbrev leafCount : Nat := 1631
cert_widths_3 13 16 6 11
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
cert_codes_3
cert_counters_3 55
cert_rawNodes_3
def leafTable : Table Nat :=
(.branch 815
 (.branch 407
 (.branch 203
 (.branch 101
 (.branch 50
 (.branch 25
 (.branch 12
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
 (.branch 10
 (.leaf (certNat% 9))
 (.branch 11
 (.leaf (certNat% 10))
 (.leaf (certNat% 11))))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf (certNat% 12))
 (.branch 14
 (.leaf (certNat% 13))
 (.leaf (certNat% 14))))
 (.branch 16
 (.leaf (certNat% 15))
 (.branch 17
 (.leaf (certNat% 16))
 (.leaf (certNat% 17)))))
 (.branch 21
 (.branch 19
 (.leaf (certNat% 18))
 (.branch 20
 (.leaf (certNat% 19))
 (.leaf (certNat% 20))))
 (.branch 23
 (.branch 22
 (.leaf (certNat% 21))
 (.leaf (certNat% 22)))
 (.branch 24
 (.leaf (certNat% 23))
 (.leaf (certNat% 24)))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf (certNat% 25))
 (.branch 27
 (.leaf (certNat% 26))
 (.leaf (certNat% 27))))
 (.branch 29
 (.leaf (certNat% 28))
 (.branch 30
 (.leaf (certNat% 29))
 (.leaf (certNat% 30)))))
 (.branch 34
 (.branch 32
 (.leaf (certNat% 31))
 (.branch 33
 (.leaf (certNat% 32))
 (.leaf (certNat% 33))))
 (.branch 35
 (.leaf (certNat% 34))
 (.branch 36
 (.leaf (certNat% 35))
 (.leaf (certNat% 36))))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf (certNat% 37))
 (.branch 39
 (.leaf (certNat% 38))
 (.leaf (certNat% 39))))
 (.branch 41
 (.leaf (certNat% 40))
 (.branch 42
 (.leaf (certNat% 41))
 (.leaf (certNat% 42)))))
 (.branch 46
 (.branch 44
 (.leaf (certNat% 43))
 (.branch 45
 (.leaf (certNat% 44))
 (.leaf (certNat% 45))))
 (.branch 48
 (.branch 47
 (.leaf (certNat% 46))
 (.leaf (certNat% 47)))
 (.branch 49
 (.leaf (certNat% 48))
 (.leaf (certNat% 49))))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf (certNat% 50))
 (.branch 52
 (.leaf (certNat% 51))
 (.leaf (certNat% 52))))
 (.branch 54
 (.leaf (certNat% 53))
 (.branch 55
 (.leaf (certNat% 54))
 (.leaf (certNat% 55)))))
 (.branch 59
 (.branch 57
 (.leaf (certNat% 56))
 (.branch 58
 (.leaf (certNat% 57))
 (.leaf (certNat% 58))))
 (.branch 60
 (.leaf (certNat% 59))
 (.branch 61
 (.leaf (certNat% 60))
 (.leaf (certNat% 61))))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf (certNat% 62))
 (.branch 64
 (.leaf (certNat% 63))
 (.leaf (certNat% 64))))
 (.branch 66
 (.leaf (certNat% 65))
 (.branch 67
 (.leaf (certNat% 66))
 (.leaf (certNat% 67)))))
 (.branch 71
 (.branch 69
 (.leaf (certNat% 68))
 (.branch 70
 (.leaf (certNat% 69))
 (.leaf (certNat% 70))))
 (.branch 73
 (.branch 72
 (.leaf (certNat% 71))
 (.leaf (certNat% 72)))
 (.branch 74
 (.leaf (certNat% 73))
 (.leaf (certNat% 74)))))))
 (.branch 88
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf (certNat% 75))
 (.branch 77
 (.leaf (certNat% 76))
 (.leaf (certNat% 77))))
 (.branch 79
 (.leaf (certNat% 78))
 (.branch 80
 (.leaf (certNat% 79))
 (.leaf (certNat% 80)))))
 (.branch 84
 (.branch 82
 (.leaf (certNat% 81))
 (.branch 83
 (.leaf (certNat% 82))
 (.leaf (certNat% 83))))
 (.branch 86
 (.branch 85
 (.leaf (certNat% 84))
 (.leaf (certNat% 85)))
 (.branch 87
 (.leaf (certNat% 86))
 (.leaf (certNat% 87))))))
 (.branch 94
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
 (.leaf (certNat% 93)))))
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
 (.leaf (certNat% 100)))))))))
 (.branch 152
 (.branch 126
 (.branch 113
 (.branch 107
 (.branch 104
 (.branch 102
 (.leaf (certNat% 101))
 (.branch 103
 (.leaf (certNat% 102))
 (.leaf (certNat% 103))))
 (.branch 105
 (.leaf (certNat% 104))
 (.branch 106
 (.leaf (certNat% 105))
 (.leaf (certNat% 106)))))
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
 (.leaf (certNat% 112))))))
 (.branch 119
 (.branch 116
 (.branch 114
 (.leaf (certNat% 113))
 (.branch 115
 (.leaf (certNat% 114))
 (.leaf (certNat% 115))))
 (.branch 117
 (.leaf (certNat% 116))
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
 (.leaf (certNat% 125)))))))
 (.branch 139
 (.branch 132
 (.branch 129
 (.branch 127
 (.leaf (certNat% 126))
 (.branch 128
 (.leaf (certNat% 127))
 (.leaf (certNat% 128))))
 (.branch 130
 (.leaf (certNat% 129))
 (.branch 131
 (.leaf (certNat% 130))
 (.leaf (certNat% 131)))))
 (.branch 135
 (.branch 133
 (.leaf (certNat% 132))
 (.branch 134
 (.leaf (certNat% 133))
 (.leaf (certNat% 134))))
 (.branch 137
 (.branch 136
 (.leaf (certNat% 135))
 (.leaf (certNat% 136)))
 (.branch 138
 (.leaf (certNat% 137))
 (.leaf (certNat% 138))))))
 (.branch 145
 (.branch 142
 (.branch 140
 (.leaf (certNat% 139))
 (.branch 141
 (.leaf (certNat% 140))
 (.leaf (certNat% 141))))
 (.branch 143
 (.leaf (certNat% 142))
 (.branch 144
 (.leaf (certNat% 143))
 (.leaf (certNat% 144)))))
 (.branch 148
 (.branch 146
 (.leaf (certNat% 145))
 (.branch 147
 (.leaf (certNat% 146))
 (.leaf (certNat% 147))))
 (.branch 150
 (.branch 149
 (.leaf (certNat% 148))
 (.leaf (certNat% 149)))
 (.branch 151
 (.leaf (certNat% 150))
 (.leaf (certNat% 151))))))))
 (.branch 177
 (.branch 164
 (.branch 158
 (.branch 155
 (.branch 153
 (.leaf (certNat% 152))
 (.branch 154
 (.leaf (certNat% 153))
 (.leaf (certNat% 154))))
 (.branch 156
 (.leaf (certNat% 155))
 (.branch 157
 (.leaf (certNat% 156))
 (.leaf (certNat% 157)))))
 (.branch 161
 (.branch 159
 (.leaf (certNat% 158))
 (.branch 160
 (.leaf (certNat% 159))
 (.leaf (certNat% 160))))
 (.branch 162
 (.leaf (certNat% 161))
 (.branch 163
 (.leaf (certNat% 162))
 (.leaf (certNat% 163))))))
 (.branch 170
 (.branch 167
 (.branch 165
 (.leaf (certNat% 164))
 (.branch 166
 (.leaf (certNat% 165))
 (.leaf (certNat% 166))))
 (.branch 168
 (.leaf (certNat% 167))
 (.branch 169
 (.leaf (certNat% 168))
 (.leaf (certNat% 169)))))
 (.branch 173
 (.branch 171
 (.leaf (certNat% 170))
 (.branch 172
 (.leaf (certNat% 171))
 (.leaf (certNat% 172))))
 (.branch 175
 (.branch 174
 (.leaf (certNat% 173))
 (.leaf (certNat% 174)))
 (.branch 176
 (.leaf (certNat% 175))
 (.leaf (certNat% 176)))))))
 (.branch 190
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
 (.branch 188
 (.branch 187
 (.leaf (certNat% 186))
 (.leaf (certNat% 187)))
 (.branch 189
 (.leaf (certNat% 188))
 (.leaf (certNat% 189))))))
 (.branch 196
 (.branch 193
 (.branch 191
 (.leaf (certNat% 190))
 (.branch 192
 (.leaf (certNat% 191))
 (.leaf (certNat% 192))))
 (.branch 194
 (.leaf (certNat% 193))
 (.branch 195
 (.leaf (certNat% 194))
 (.leaf (certNat% 195)))))
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
 (.leaf (certNat% 202))))))))))
 (.branch 305
 (.branch 254
 (.branch 228
 (.branch 215
 (.branch 209
 (.branch 206
 (.branch 204
 (.leaf (certNat% 203))
 (.branch 205
 (.leaf (certNat% 204))
 (.leaf (certNat% 205))))
 (.branch 207
 (.leaf (certNat% 206))
 (.branch 208
 (.leaf (certNat% 207))
 (.leaf (certNat% 208)))))
 (.branch 212
 (.branch 210
 (.leaf (certNat% 209))
 (.branch 211
 (.leaf (certNat% 210))
 (.leaf (certNat% 211))))
 (.branch 213
 (.leaf (certNat% 212))
 (.branch 214
 (.leaf (certNat% 213))
 (.leaf (certNat% 214))))))
 (.branch 221
 (.branch 218
 (.branch 216
 (.leaf (certNat% 215))
 (.branch 217
 (.leaf (certNat% 216))
 (.leaf (certNat% 217))))
 (.branch 219
 (.leaf (certNat% 218))
 (.branch 220
 (.leaf (certNat% 219))
 (.leaf (certNat% 220)))))
 (.branch 224
 (.branch 222
 (.leaf (certNat% 221))
 (.branch 223
 (.leaf (certNat% 222))
 (.leaf (certNat% 223))))
 (.branch 226
 (.branch 225
 (.leaf (certNat% 224))
 (.leaf (certNat% 225)))
 (.branch 227
 (.leaf (certNat% 226))
 (.leaf (certNat% 227)))))))
 (.branch 241
 (.branch 234
 (.branch 231
 (.branch 229
 (.leaf (certNat% 228))
 (.branch 230
 (.leaf (certNat% 229))
 (.leaf (certNat% 230))))
 (.branch 232
 (.leaf (certNat% 231))
 (.branch 233
 (.leaf (certNat% 232))
 (.leaf (certNat% 233)))))
 (.branch 237
 (.branch 235
 (.leaf (certNat% 234))
 (.branch 236
 (.leaf (certNat% 235))
 (.leaf (certNat% 236))))
 (.branch 239
 (.branch 238
 (.leaf (certNat% 237))
 (.leaf (certNat% 238)))
 (.branch 240
 (.leaf (certNat% 239))
 (.leaf (certNat% 240))))))
 (.branch 247
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
 (.leaf (certNat% 246)))))
 (.branch 250
 (.branch 248
 (.leaf (certNat% 247))
 (.branch 249
 (.leaf (certNat% 248))
 (.leaf (certNat% 249))))
 (.branch 252
 (.branch 251
 (.leaf (certNat% 250))
 (.leaf (certNat% 251)))
 (.branch 253
 (.leaf (certNat% 252))
 (.leaf (certNat% 253))))))))
 (.branch 279
 (.branch 266
 (.branch 260
 (.branch 257
 (.branch 255
 (.leaf (certNat% 254))
 (.branch 256
 (.leaf (certNat% 255))
 (.leaf (certNat% 256))))
 (.branch 258
 (.leaf (certNat% 257))
 (.branch 259
 (.leaf (certNat% 258))
 (.leaf (certNat% 259)))))
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
 (.leaf (certNat% 265))))))
 (.branch 272
 (.branch 269
 (.branch 267
 (.leaf (certNat% 266))
 (.branch 268
 (.leaf (certNat% 267))
 (.leaf (certNat% 268))))
 (.branch 270
 (.leaf (certNat% 269))
 (.branch 271
 (.leaf (certNat% 270))
 (.leaf (certNat% 271)))))
 (.branch 275
 (.branch 273
 (.leaf (certNat% 272))
 (.branch 274
 (.leaf (certNat% 273))
 (.leaf (certNat% 274))))
 (.branch 277
 (.branch 276
 (.leaf (certNat% 275))
 (.leaf (certNat% 276)))
 (.branch 278
 (.leaf (certNat% 277))
 (.leaf (certNat% 278)))))))
 (.branch 292
 (.branch 285
 (.branch 282
 (.branch 280
 (.leaf (certNat% 279))
 (.branch 281
 (.leaf (certNat% 280))
 (.leaf (certNat% 281))))
 (.branch 283
 (.leaf (certNat% 282))
 (.branch 284
 (.leaf (certNat% 283))
 (.leaf (certNat% 284)))))
 (.branch 288
 (.branch 286
 (.leaf (certNat% 285))
 (.branch 287
 (.leaf (certNat% 286))
 (.leaf (certNat% 287))))
 (.branch 290
 (.branch 289
 (.leaf (certNat% 288))
 (.leaf (certNat% 289)))
 (.branch 291
 (.leaf (certNat% 290))
 (.leaf (certNat% 291))))))
 (.branch 298
 (.branch 295
 (.branch 293
 (.leaf (certNat% 292))
 (.branch 294
 (.leaf (certNat% 293))
 (.leaf (certNat% 294))))
 (.branch 296
 (.leaf (certNat% 295))
 (.branch 297
 (.leaf (certNat% 296))
 (.leaf (certNat% 297)))))
 (.branch 301
 (.branch 299
 (.leaf (certNat% 298))
 (.branch 300
 (.leaf (certNat% 299))
 (.leaf (certNat% 300))))
 (.branch 303
 (.branch 302
 (.leaf (certNat% 301))
 (.leaf (certNat% 302)))
 (.branch 304
 (.leaf (certNat% 303))
 (.leaf (certNat% 304)))))))))
 (.branch 356
 (.branch 330
 (.branch 317
 (.branch 311
 (.branch 308
 (.branch 306
 (.leaf (certNat% 305))
 (.branch 307
 (.leaf (certNat% 306))
 (.leaf (certNat% 307))))
 (.branch 309
 (.leaf (certNat% 308))
 (.branch 310
 (.leaf (certNat% 309))
 (.leaf (certNat% 310)))))
 (.branch 314
 (.branch 312
 (.leaf (certNat% 311))
 (.branch 313
 (.leaf (certNat% 312))
 (.leaf (certNat% 313))))
 (.branch 315
 (.leaf (certNat% 314))
 (.branch 316
 (.leaf (certNat% 315))
 (.leaf (certNat% 316))))))
 (.branch 323
 (.branch 320
 (.branch 318
 (.leaf (certNat% 317))
 (.branch 319
 (.leaf (certNat% 318))
 (.leaf (certNat% 319))))
 (.branch 321
 (.leaf (certNat% 320))
 (.branch 322
 (.leaf (certNat% 321))
 (.leaf (certNat% 322)))))
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
 (.leaf (certNat% 329)))))))
 (.branch 343
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
 (.branch 341
 (.branch 340
 (.leaf (certNat% 339))
 (.leaf (certNat% 340)))
 (.branch 342
 (.leaf (certNat% 341))
 (.leaf (certNat% 342))))))
 (.branch 349
 (.branch 346
 (.branch 344
 (.leaf (certNat% 343))
 (.branch 345
 (.leaf (certNat% 344))
 (.leaf (certNat% 345))))
 (.branch 347
 (.leaf (certNat% 346))
 (.branch 348
 (.leaf (certNat% 347))
 (.leaf (certNat% 348)))))
 (.branch 352
 (.branch 350
 (.leaf (certNat% 349))
 (.branch 351
 (.leaf (certNat% 350))
 (.leaf (certNat% 351))))
 (.branch 354
 (.branch 353
 (.leaf (certNat% 352))
 (.leaf (certNat% 353)))
 (.branch 355
 (.leaf (certNat% 354))
 (.leaf (certNat% 355))))))))
 (.branch 381
 (.branch 368
 (.branch 362
 (.branch 359
 (.branch 357
 (.leaf (certNat% 356))
 (.branch 358
 (.leaf (certNat% 357))
 (.leaf (certNat% 358))))
 (.branch 360
 (.leaf (certNat% 359))
 (.branch 361
 (.leaf (certNat% 360))
 (.leaf (certNat% 361)))))
 (.branch 365
 (.branch 363
 (.leaf (certNat% 362))
 (.branch 364
 (.leaf (certNat% 363))
 (.leaf (certNat% 364))))
 (.branch 366
 (.leaf (certNat% 365))
 (.branch 367
 (.leaf (certNat% 366))
 (.leaf (certNat% 367))))))
 (.branch 374
 (.branch 371
 (.branch 369
 (.leaf (certNat% 368))
 (.branch 370
 (.leaf (certNat% 369))
 (.leaf (certNat% 370))))
 (.branch 372
 (.leaf (certNat% 371))
 (.branch 373
 (.leaf (certNat% 372))
 (.leaf (certNat% 373)))))
 (.branch 377
 (.branch 375
 (.leaf (certNat% 374))
 (.branch 376
 (.leaf (certNat% 375))
 (.leaf (certNat% 376))))
 (.branch 379
 (.branch 378
 (.leaf (certNat% 377))
 (.leaf (certNat% 378)))
 (.branch 380
 (.leaf (certNat% 379))
 (.leaf (certNat% 380)))))))
 (.branch 394
 (.branch 387
 (.branch 384
 (.branch 382
 (.leaf (certNat% 381))
 (.branch 383
 (.leaf (certNat% 382))
 (.leaf (certNat% 383))))
 (.branch 385
 (.leaf (certNat% 384))
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
 (.leaf (certNat% 393))))))
 (.branch 400
 (.branch 397
 (.branch 395
 (.leaf (certNat% 394))
 (.branch 396
 (.leaf (certNat% 395))
 (.leaf (certNat% 396))))
 (.branch 398
 (.leaf (certNat% 397))
 (.branch 399
 (.leaf (certNat% 398))
 (.leaf (certNat% 399)))))
 (.branch 403
 (.branch 401
 (.leaf (certNat% 400))
 (.branch 402
 (.leaf (certNat% 401))
 (.leaf (certNat% 402))))
 (.branch 405
 (.branch 404
 (.leaf (certNat% 403))
 (.leaf (certNat% 404)))
 (.branch 406
 (.leaf (certNat% 405))
 (.leaf (certNat% 406)))))))))))
 (.branch 611
 (.branch 509
 (.branch 458
 (.branch 432
 (.branch 419
 (.branch 413
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
 (.leaf (certNat% 412)))))
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
 (.leaf (certNat% 418))))))
 (.branch 425
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
 (.leaf (certNat% 431)))))))
 (.branch 445
 (.branch 438
 (.branch 435
 (.branch 433
 (.leaf (certNat% 432))
 (.branch 434
 (.leaf (certNat% 433))
 (.leaf (certNat% 434))))
 (.branch 436
 (.leaf (certNat% 435))
 (.branch 437
 (.leaf (certNat% 436))
 (.leaf (certNat% 437)))))
 (.branch 441
 (.branch 439
 (.leaf (certNat% 438))
 (.branch 440
 (.leaf (certNat% 439))
 (.leaf (certNat% 440))))
 (.branch 443
 (.branch 442
 (.leaf (certNat% 441))
 (.leaf (certNat% 442)))
 (.branch 444
 (.leaf (certNat% 443))
 (.leaf (certNat% 444))))))
 (.branch 451
 (.branch 448
 (.branch 446
 (.leaf (certNat% 445))
 (.branch 447
 (.leaf (certNat% 446))
 (.leaf (certNat% 447))))
 (.branch 449
 (.leaf (certNat% 448))
 (.branch 450
 (.leaf (certNat% 449))
 (.leaf (certNat% 450)))))
 (.branch 454
 (.branch 452
 (.leaf (certNat% 451))
 (.branch 453
 (.leaf (certNat% 452))
 (.leaf (certNat% 453))))
 (.branch 456
 (.branch 455
 (.leaf (certNat% 454))
 (.leaf (certNat% 455)))
 (.branch 457
 (.leaf (certNat% 456))
 (.leaf (certNat% 457))))))))
 (.branch 483
 (.branch 470
 (.branch 464
 (.branch 461
 (.branch 459
 (.leaf (certNat% 458))
 (.branch 460
 (.leaf (certNat% 459))
 (.leaf (certNat% 460))))
 (.branch 462
 (.leaf (certNat% 461))
 (.branch 463
 (.leaf (certNat% 462))
 (.leaf (certNat% 463)))))
 (.branch 467
 (.branch 465
 (.leaf (certNat% 464))
 (.branch 466
 (.leaf (certNat% 465))
 (.leaf (certNat% 466))))
 (.branch 468
 (.leaf (certNat% 467))
 (.branch 469
 (.leaf (certNat% 468))
 (.leaf (certNat% 469))))))
 (.branch 476
 (.branch 473
 (.branch 471
 (.leaf (certNat% 470))
 (.branch 472
 (.leaf (certNat% 471))
 (.leaf (certNat% 472))))
 (.branch 474
 (.leaf (certNat% 473))
 (.branch 475
 (.leaf (certNat% 474))
 (.leaf (certNat% 475)))))
 (.branch 479
 (.branch 477
 (.leaf (certNat% 476))
 (.branch 478
 (.leaf (certNat% 477))
 (.leaf (certNat% 478))))
 (.branch 481
 (.branch 480
 (.leaf (certNat% 479))
 (.leaf (certNat% 480)))
 (.branch 482
 (.leaf (certNat% 481))
 (.leaf (certNat% 482)))))))
 (.branch 496
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
 (.branch 494
 (.branch 493
 (.leaf (certNat% 492))
 (.leaf (certNat% 493)))
 (.branch 495
 (.leaf (certNat% 494))
 (.leaf (certNat% 495))))))
 (.branch 502
 (.branch 499
 (.branch 497
 (.leaf (certNat% 496))
 (.branch 498
 (.leaf (certNat% 497))
 (.leaf (certNat% 498))))
 (.branch 500
 (.leaf (certNat% 499))
 (.branch 501
 (.leaf (certNat% 500))
 (.leaf (certNat% 501)))))
 (.branch 505
 (.branch 503
 (.leaf (certNat% 502))
 (.branch 504
 (.leaf (certNat% 503))
 (.leaf (certNat% 504))))
 (.branch 507
 (.branch 506
 (.leaf (certNat% 505))
 (.leaf (certNat% 506)))
 (.branch 508
 (.leaf (certNat% 507))
 (.leaf (certNat% 508)))))))))
 (.branch 560
 (.branch 534
 (.branch 521
 (.branch 515
 (.branch 512
 (.branch 510
 (.leaf (certNat% 509))
 (.branch 511
 (.leaf (certNat% 510))
 (.leaf (certNat% 511))))
 (.branch 513
 (.leaf (certNat% 512))
 (.branch 514
 (.leaf (certNat% 513))
 (.leaf (certNat% 514)))))
 (.branch 518
 (.branch 516
 (.leaf (certNat% 515))
 (.branch 517
 (.leaf (certNat% 516))
 (.leaf (certNat% 517))))
 (.branch 519
 (.leaf (certNat% 518))
 (.branch 520
 (.leaf (certNat% 519))
 (.leaf (certNat% 520))))))
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
 (.leaf (certNat% 533)))))))
 (.branch 547
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
 (.leaf (certNat% 546))))))
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
 (.leaf (certNat% 559))))))))
 (.branch 585
 (.branch 572
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
 (.branch 570
 (.leaf (certNat% 569))
 (.branch 571
 (.leaf (certNat% 570))
 (.leaf (certNat% 571))))))
 (.branch 578
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
 (.leaf (certNat% 577)))))
 (.branch 581
 (.branch 579
 (.leaf (certNat% 578))
 (.branch 580
 (.leaf (certNat% 579))
 (.leaf (certNat% 580))))
 (.branch 583
 (.branch 582
 (.leaf (certNat% 581))
 (.leaf (certNat% 582)))
 (.branch 584
 (.leaf (certNat% 583))
 (.leaf (certNat% 584)))))))
 (.branch 598
 (.branch 591
 (.branch 588
 (.branch 586
 (.leaf (certNat% 585))
 (.branch 587
 (.leaf (certNat% 586))
 (.leaf (certNat% 587))))
 (.branch 589
 (.leaf (certNat% 588))
 (.branch 590
 (.leaf (certNat% 589))
 (.leaf (certNat% 590)))))
 (.branch 594
 (.branch 592
 (.leaf (certNat% 591))
 (.branch 593
 (.leaf (certNat% 592))
 (.leaf (certNat% 593))))
 (.branch 596
 (.branch 595
 (.leaf (certNat% 594))
 (.leaf (certNat% 595)))
 (.branch 597
 (.leaf (certNat% 596))
 (.leaf (certNat% 597))))))
 (.branch 604
 (.branch 601
 (.branch 599
 (.leaf (certNat% 598))
 (.branch 600
 (.leaf (certNat% 599))
 (.leaf (certNat% 600))))
 (.branch 602
 (.leaf (certNat% 601))
 (.branch 603
 (.leaf (certNat% 602))
 (.leaf (certNat% 603)))))
 (.branch 607
 (.branch 605
 (.leaf (certNat% 604))
 (.branch 606
 (.leaf (certNat% 605))
 (.leaf (certNat% 606))))
 (.branch 609
 (.branch 608
 (.leaf (certNat% 607))
 (.leaf (certNat% 608)))
 (.branch 610
 (.leaf (certNat% 609))
 (.leaf (certNat% 610))))))))))
 (.branch 713
 (.branch 662
 (.branch 636
 (.branch 623
 (.branch 617
 (.branch 614
 (.branch 612
 (.leaf (certNat% 611))
 (.branch 613
 (.leaf (certNat% 612))
 (.leaf (certNat% 613))))
 (.branch 615
 (.leaf (certNat% 614))
 (.branch 616
 (.leaf (certNat% 615))
 (.leaf (certNat% 616)))))
 (.branch 620
 (.branch 618
 (.leaf (certNat% 617))
 (.branch 619
 (.leaf (certNat% 618))
 (.leaf (certNat% 619))))
 (.branch 621
 (.leaf (certNat% 620))
 (.branch 622
 (.leaf (certNat% 621))
 (.leaf (certNat% 622))))))
 (.branch 629
 (.branch 626
 (.branch 624
 (.leaf (certNat% 623))
 (.branch 625
 (.leaf (certNat% 624))
 (.leaf (certNat% 625))))
 (.branch 627
 (.leaf (certNat% 626))
 (.branch 628
 (.leaf (certNat% 627))
 (.leaf (certNat% 628)))))
 (.branch 632
 (.branch 630
 (.leaf (certNat% 629))
 (.branch 631
 (.leaf (certNat% 630))
 (.leaf (certNat% 631))))
 (.branch 634
 (.branch 633
 (.leaf (certNat% 632))
 (.leaf (certNat% 633)))
 (.branch 635
 (.leaf (certNat% 634))
 (.leaf (certNat% 635)))))))
 (.branch 649
 (.branch 642
 (.branch 639
 (.branch 637
 (.leaf (certNat% 636))
 (.branch 638
 (.leaf (certNat% 637))
 (.leaf (certNat% 638))))
 (.branch 640
 (.leaf (certNat% 639))
 (.branch 641
 (.leaf (certNat% 640))
 (.leaf (certNat% 641)))))
 (.branch 645
 (.branch 643
 (.leaf (certNat% 642))
 (.branch 644
 (.leaf (certNat% 643))
 (.leaf (certNat% 644))))
 (.branch 647
 (.branch 646
 (.leaf (certNat% 645))
 (.leaf (certNat% 646)))
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
 (.branch 660
 (.branch 659
 (.leaf (certNat% 658))
 (.leaf (certNat% 659)))
 (.branch 661
 (.leaf (certNat% 660))
 (.leaf (certNat% 661))))))))
 (.branch 687
 (.branch 674
 (.branch 668
 (.branch 665
 (.branch 663
 (.leaf (certNat% 662))
 (.branch 664
 (.leaf (certNat% 663))
 (.leaf (certNat% 664))))
 (.branch 666
 (.leaf (certNat% 665))
 (.branch 667
 (.leaf (certNat% 666))
 (.leaf (certNat% 667)))))
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
 (.leaf (certNat% 673))))))
 (.branch 680
 (.branch 677
 (.branch 675
 (.leaf (certNat% 674))
 (.branch 676
 (.leaf (certNat% 675))
 (.leaf (certNat% 676))))
 (.branch 678
 (.leaf (certNat% 677))
 (.branch 679
 (.leaf (certNat% 678))
 (.leaf (certNat% 679)))))
 (.branch 683
 (.branch 681
 (.leaf (certNat% 680))
 (.branch 682
 (.leaf (certNat% 681))
 (.leaf (certNat% 682))))
 (.branch 685
 (.branch 684
 (.leaf (certNat% 683))
 (.leaf (certNat% 684)))
 (.branch 686
 (.leaf (certNat% 685))
 (.leaf (certNat% 686)))))))
 (.branch 700
 (.branch 693
 (.branch 690
 (.branch 688
 (.leaf (certNat% 687))
 (.branch 689
 (.leaf (certNat% 688))
 (.leaf (certNat% 689))))
 (.branch 691
 (.leaf (certNat% 690))
 (.branch 692
 (.leaf (certNat% 691))
 (.leaf (certNat% 692)))))
 (.branch 696
 (.branch 694
 (.leaf (certNat% 693))
 (.branch 695
 (.leaf (certNat% 694))
 (.leaf (certNat% 695))))
 (.branch 698
 (.branch 697
 (.leaf (certNat% 696))
 (.leaf (certNat% 697)))
 (.branch 699
 (.leaf (certNat% 698))
 (.leaf (certNat% 699))))))
 (.branch 706
 (.branch 703
 (.branch 701
 (.leaf (certNat% 700))
 (.branch 702
 (.leaf (certNat% 701))
 (.leaf (certNat% 702))))
 (.branch 704
 (.leaf (certNat% 703))
 (.branch 705
 (.leaf (certNat% 704))
 (.leaf (certNat% 705)))))
 (.branch 709
 (.branch 707
 (.leaf (certNat% 706))
 (.branch 708
 (.leaf (certNat% 707))
 (.leaf (certNat% 708))))
 (.branch 711
 (.branch 710
 (.leaf (certNat% 709))
 (.leaf (certNat% 710)))
 (.branch 712
 (.leaf (certNat% 711))
 (.leaf (certNat% 712)))))))))
 (.branch 764
 (.branch 738
 (.branch 725
 (.branch 719
 (.branch 716
 (.branch 714
 (.leaf (certNat% 713))
 (.branch 715
 (.leaf (certNat% 714))
 (.leaf (certNat% 715))))
 (.branch 717
 (.leaf (certNat% 716))
 (.branch 718
 (.leaf (certNat% 717))
 (.leaf (certNat% 718)))))
 (.branch 722
 (.branch 720
 (.leaf (certNat% 719))
 (.branch 721
 (.leaf (certNat% 720))
 (.leaf (certNat% 721))))
 (.branch 723
 (.leaf (certNat% 722))
 (.branch 724
 (.leaf (certNat% 723))
 (.leaf (certNat% 724))))))
 (.branch 731
 (.branch 728
 (.branch 726
 (.leaf (certNat% 725))
 (.branch 727
 (.leaf (certNat% 726))
 (.leaf (certNat% 727))))
 (.branch 729
 (.leaf (certNat% 728))
 (.branch 730
 (.leaf (certNat% 729))
 (.leaf (certNat% 730)))))
 (.branch 734
 (.branch 732
 (.leaf (certNat% 731))
 (.branch 733
 (.leaf (certNat% 732))
 (.leaf (certNat% 733))))
 (.branch 736
 (.branch 735
 (.leaf (certNat% 734))
 (.leaf (certNat% 735)))
 (.branch 737
 (.leaf (certNat% 736))
 (.leaf (certNat% 737)))))))
 (.branch 751
 (.branch 744
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
 (.leaf (certNat% 743)))))
 (.branch 747
 (.branch 745
 (.leaf (certNat% 744))
 (.branch 746
 (.leaf (certNat% 745))
 (.leaf (certNat% 746))))
 (.branch 749
 (.branch 748
 (.leaf (certNat% 747))
 (.leaf (certNat% 748)))
 (.branch 750
 (.leaf (certNat% 749))
 (.leaf (certNat% 750))))))
 (.branch 757
 (.branch 754
 (.branch 752
 (.leaf (certNat% 751))
 (.branch 753
 (.leaf (certNat% 752))
 (.leaf (certNat% 753))))
 (.branch 755
 (.leaf (certNat% 754))
 (.branch 756
 (.leaf (certNat% 755))
 (.leaf (certNat% 756)))))
 (.branch 760
 (.branch 758
 (.leaf (certNat% 757))
 (.branch 759
 (.leaf (certNat% 758))
 (.leaf (certNat% 759))))
 (.branch 762
 (.branch 761
 (.leaf (certNat% 760))
 (.leaf (certNat% 761)))
 (.branch 763
 (.leaf (certNat% 762))
 (.leaf (certNat% 763))))))))
 (.branch 789
 (.branch 776
 (.branch 770
 (.branch 767
 (.branch 765
 (.leaf (certNat% 764))
 (.branch 766
 (.leaf (certNat% 765))
 (.leaf (certNat% 766))))
 (.branch 768
 (.leaf (certNat% 767))
 (.branch 769
 (.leaf (certNat% 768))
 (.leaf (certNat% 769)))))
 (.branch 773
 (.branch 771
 (.leaf (certNat% 770))
 (.branch 772
 (.leaf (certNat% 771))
 (.leaf (certNat% 772))))
 (.branch 774
 (.leaf (certNat% 773))
 (.branch 775
 (.leaf (certNat% 774))
 (.leaf (certNat% 775))))))
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
 (.leaf (certNat% 788)))))))
 (.branch 802
 (.branch 795
 (.branch 792
 (.branch 790
 (.leaf (certNat% 789))
 (.branch 791
 (.leaf (certNat% 790))
 (.leaf (certNat% 791))))
 (.branch 793
 (.leaf (certNat% 792))
 (.branch 794
 (.leaf (certNat% 793))
 (.leaf (certNat% 794)))))
 (.branch 798
 (.branch 796
 (.leaf (certNat% 795))
 (.branch 797
 (.leaf (certNat% 796))
 (.leaf (certNat% 797))))
 (.branch 800
 (.branch 799
 (.leaf (certNat% 798))
 (.leaf (certNat% 799)))
 (.branch 801
 (.leaf (certNat% 800))
 (.leaf (certNat% 801))))))
 (.branch 808
 (.branch 805
 (.branch 803
 (.leaf (certNat% 802))
 (.branch 804
 (.leaf (certNat% 803))
 (.leaf (certNat% 804))))
 (.branch 806
 (.leaf (certNat% 805))
 (.branch 807
 (.leaf (certNat% 806))
 (.leaf (certNat% 807)))))
 (.branch 811
 (.branch 809
 (.leaf (certNat% 808))
 (.branch 810
 (.leaf (certNat% 809))
 (.leaf (certNat% 810))))
 (.branch 813
 (.branch 812
 (.leaf (certNat% 811))
 (.leaf (certNat% 812)))
 (.branch 814
 (.leaf (certNat% 813))
 (.leaf (certNat% 814))))))))))))
 (.branch 1223
 (.branch 1019
 (.branch 917
 (.branch 866
 (.branch 840
 (.branch 827
 (.branch 821
 (.branch 818
 (.branch 816
 (.leaf (certNat% 815))
 (.branch 817
 (.leaf (certNat% 816))
 (.leaf (certNat% 817))))
 (.branch 819
 (.leaf (certNat% 818))
 (.branch 820
 (.leaf (certNat% 819))
 (.leaf (certNat% 820)))))
 (.branch 824
 (.branch 822
 (.leaf (certNat% 821))
 (.branch 823
 (.leaf (certNat% 822))
 (.leaf (certNat% 823))))
 (.branch 825
 (.leaf (certNat% 824))
 (.branch 826
 (.leaf (certNat% 825))
 (.leaf (certNat% 826))))))
 (.branch 833
 (.branch 830
 (.branch 828
 (.leaf (certNat% 827))
 (.branch 829
 (.leaf (certNat% 828))
 (.leaf (certNat% 829))))
 (.branch 831
 (.leaf (certNat% 830))
 (.branch 832
 (.leaf (certNat% 831))
 (.leaf (certNat% 832)))))
 (.branch 836
 (.branch 834
 (.leaf (certNat% 833))
 (.branch 835
 (.leaf (certNat% 834))
 (.leaf (certNat% 835))))
 (.branch 838
 (.branch 837
 (.leaf (certNat% 836))
 (.leaf (certNat% 837)))
 (.branch 839
 (.leaf (certNat% 838))
 (.leaf (certNat% 839)))))))
 (.branch 853
 (.branch 846
 (.branch 843
 (.branch 841
 (.leaf (certNat% 840))
 (.branch 842
 (.leaf (certNat% 841))
 (.leaf (certNat% 842))))
 (.branch 844
 (.leaf (certNat% 843))
 (.branch 845
 (.leaf (certNat% 844))
 (.leaf (certNat% 845)))))
 (.branch 849
 (.branch 847
 (.leaf (certNat% 846))
 (.branch 848
 (.leaf (certNat% 847))
 (.leaf (certNat% 848))))
 (.branch 851
 (.branch 850
 (.leaf (certNat% 849))
 (.leaf (certNat% 850)))
 (.branch 852
 (.leaf (certNat% 851))
 (.leaf (certNat% 852))))))
 (.branch 859
 (.branch 856
 (.branch 854
 (.leaf (certNat% 853))
 (.branch 855
 (.leaf (certNat% 854))
 (.leaf (certNat% 855))))
 (.branch 857
 (.leaf (certNat% 856))
 (.branch 858
 (.leaf (certNat% 857))
 (.leaf (certNat% 858)))))
 (.branch 862
 (.branch 860
 (.leaf (certNat% 859))
 (.branch 861
 (.leaf (certNat% 860))
 (.leaf (certNat% 861))))
 (.branch 864
 (.branch 863
 (.leaf (certNat% 862))
 (.leaf (certNat% 863)))
 (.branch 865
 (.leaf (certNat% 864))
 (.leaf (certNat% 865))))))))
 (.branch 891
 (.branch 878
 (.branch 872
 (.branch 869
 (.branch 867
 (.leaf (certNat% 866))
 (.branch 868
 (.leaf (certNat% 867))
 (.leaf (certNat% 868))))
 (.branch 870
 (.leaf (certNat% 869))
 (.branch 871
 (.leaf (certNat% 870))
 (.leaf (certNat% 871)))))
 (.branch 875
 (.branch 873
 (.leaf (certNat% 872))
 (.branch 874
 (.leaf (certNat% 873))
 (.leaf (certNat% 874))))
 (.branch 876
 (.leaf (certNat% 875))
 (.branch 877
 (.leaf (certNat% 876))
 (.leaf (certNat% 877))))))
 (.branch 884
 (.branch 881
 (.branch 879
 (.leaf (certNat% 878))
 (.branch 880
 (.leaf (certNat% 879))
 (.leaf (certNat% 880))))
 (.branch 882
 (.leaf (certNat% 881))
 (.branch 883
 (.leaf (certNat% 882))
 (.leaf (certNat% 883)))))
 (.branch 887
 (.branch 885
 (.leaf (certNat% 884))
 (.branch 886
 (.leaf (certNat% 885))
 (.leaf (certNat% 886))))
 (.branch 889
 (.branch 888
 (.leaf (certNat% 887))
 (.leaf (certNat% 888)))
 (.branch 890
 (.leaf (certNat% 889))
 (.leaf (certNat% 890)))))))
 (.branch 904
 (.branch 897
 (.branch 894
 (.branch 892
 (.leaf (certNat% 891))
 (.branch 893
 (.leaf (certNat% 892))
 (.leaf (certNat% 893))))
 (.branch 895
 (.leaf (certNat% 894))
 (.branch 896
 (.leaf (certNat% 895))
 (.leaf (certNat% 896)))))
 (.branch 900
 (.branch 898
 (.leaf (certNat% 897))
 (.branch 899
 (.leaf (certNat% 898))
 (.leaf (certNat% 899))))
 (.branch 902
 (.branch 901
 (.leaf (certNat% 900))
 (.leaf (certNat% 901)))
 (.branch 903
 (.leaf (certNat% 902))
 (.leaf (certNat% 903))))))
 (.branch 910
 (.branch 907
 (.branch 905
 (.leaf (certNat% 904))
 (.branch 906
 (.leaf (certNat% 905))
 (.leaf (certNat% 906))))
 (.branch 908
 (.leaf (certNat% 907))
 (.branch 909
 (.leaf (certNat% 908))
 (.leaf (certNat% 909)))))
 (.branch 913
 (.branch 911
 (.leaf (certNat% 910))
 (.branch 912
 (.leaf (certNat% 911))
 (.leaf (certNat% 912))))
 (.branch 915
 (.branch 914
 (.leaf (certNat% 913))
 (.leaf (certNat% 914)))
 (.branch 916
 (.leaf (certNat% 915))
 (.leaf (certNat% 916)))))))))
 (.branch 968
 (.branch 942
 (.branch 929
 (.branch 923
 (.branch 920
 (.branch 918
 (.leaf (certNat% 917))
 (.branch 919
 (.leaf (certNat% 918))
 (.leaf (certNat% 919))))
 (.branch 921
 (.leaf (certNat% 920))
 (.branch 922
 (.leaf (certNat% 921))
 (.leaf (certNat% 922)))))
 (.branch 926
 (.branch 924
 (.leaf (certNat% 923))
 (.branch 925
 (.leaf (certNat% 924))
 (.leaf (certNat% 925))))
 (.branch 927
 (.leaf (certNat% 926))
 (.branch 928
 (.leaf (certNat% 927))
 (.leaf (certNat% 928))))))
 (.branch 935
 (.branch 932
 (.branch 930
 (.leaf (certNat% 929))
 (.branch 931
 (.leaf (certNat% 930))
 (.leaf (certNat% 931))))
 (.branch 933
 (.leaf (certNat% 932))
 (.branch 934
 (.leaf (certNat% 933))
 (.leaf (certNat% 934)))))
 (.branch 938
 (.branch 936
 (.leaf (certNat% 935))
 (.branch 937
 (.leaf (certNat% 936))
 (.leaf (certNat% 937))))
 (.branch 940
 (.branch 939
 (.leaf (certNat% 938))
 (.leaf (certNat% 939)))
 (.branch 941
 (.leaf (certNat% 940))
 (.leaf (certNat% 941)))))))
 (.branch 955
 (.branch 948
 (.branch 945
 (.branch 943
 (.leaf (certNat% 942))
 (.branch 944
 (.leaf (certNat% 943))
 (.leaf (certNat% 944))))
 (.branch 946
 (.leaf (certNat% 945))
 (.branch 947
 (.leaf (certNat% 946))
 (.leaf (certNat% 947)))))
 (.branch 951
 (.branch 949
 (.leaf (certNat% 948))
 (.branch 950
 (.leaf (certNat% 949))
 (.leaf (certNat% 950))))
 (.branch 953
 (.branch 952
 (.leaf (certNat% 951))
 (.leaf (certNat% 952)))
 (.branch 954
 (.leaf (certNat% 953))
 (.leaf (certNat% 954))))))
 (.branch 961
 (.branch 958
 (.branch 956
 (.leaf (certNat% 955))
 (.branch 957
 (.leaf (certNat% 956))
 (.leaf (certNat% 957))))
 (.branch 959
 (.leaf (certNat% 958))
 (.branch 960
 (.leaf (certNat% 959))
 (.leaf (certNat% 960)))))
 (.branch 964
 (.branch 962
 (.leaf (certNat% 961))
 (.branch 963
 (.leaf (certNat% 962))
 (.leaf (certNat% 963))))
 (.branch 966
 (.branch 965
 (.leaf (certNat% 964))
 (.leaf (certNat% 965)))
 (.branch 967
 (.leaf (certNat% 966))
 (.leaf (certNat% 967))))))))
 (.branch 993
 (.branch 980
 (.branch 974
 (.branch 971
 (.branch 969
 (.leaf (certNat% 968))
 (.branch 970
 (.leaf (certNat% 969))
 (.leaf (certNat% 970))))
 (.branch 972
 (.leaf (certNat% 971))
 (.branch 973
 (.leaf (certNat% 972))
 (.leaf (certNat% 973)))))
 (.branch 977
 (.branch 975
 (.leaf (certNat% 974))
 (.branch 976
 (.leaf (certNat% 975))
 (.leaf (certNat% 976))))
 (.branch 978
 (.leaf (certNat% 977))
 (.branch 979
 (.leaf (certNat% 978))
 (.leaf (certNat% 979))))))
 (.branch 986
 (.branch 983
 (.branch 981
 (.leaf (certNat% 980))
 (.branch 982
 (.leaf (certNat% 981))
 (.leaf (certNat% 982))))
 (.branch 984
 (.leaf (certNat% 983))
 (.branch 985
 (.leaf (certNat% 984))
 (.leaf (certNat% 985)))))
 (.branch 989
 (.branch 987
 (.leaf (certNat% 986))
 (.branch 988
 (.leaf (certNat% 987))
 (.leaf (certNat% 988))))
 (.branch 991
 (.branch 990
 (.leaf (certNat% 989))
 (.leaf (certNat% 990)))
 (.branch 992
 (.leaf (certNat% 991))
 (.leaf (certNat% 992)))))))
 (.branch 1006
 (.branch 999
 (.branch 996
 (.branch 994
 (.leaf (certNat% 993))
 (.branch 995
 (.leaf (certNat% 994))
 (.leaf (certNat% 995))))
 (.branch 997
 (.leaf (certNat% 996))
 (.branch 998
 (.leaf (certNat% 997))
 (.leaf (certNat% 998)))))
 (.branch 1002
 (.branch 1000
 (.leaf (certNat% 999))
 (.branch 1001
 (.leaf (certNat% 1000))
 (.leaf (certNat% 1001))))
 (.branch 1004
 (.branch 1003
 (.leaf (certNat% 1002))
 (.leaf (certNat% 1003)))
 (.branch 1005
 (.leaf (certNat% 1004))
 (.leaf (certNat% 1005))))))
 (.branch 1012
 (.branch 1009
 (.branch 1007
 (.leaf (certNat% 1006))
 (.branch 1008
 (.leaf (certNat% 1007))
 (.leaf (certNat% 1008))))
 (.branch 1010
 (.leaf (certNat% 1009))
 (.branch 1011
 (.leaf (certNat% 1010))
 (.leaf (certNat% 1011)))))
 (.branch 1015
 (.branch 1013
 (.leaf (certNat% 1012))
 (.branch 1014
 (.leaf (certNat% 1013))
 (.leaf (certNat% 1014))))
 (.branch 1017
 (.branch 1016
 (.leaf (certNat% 1015))
 (.leaf (certNat% 1016)))
 (.branch 1018
 (.leaf (certNat% 1017))
 (.leaf (certNat% 1018))))))))))
 (.branch 1121
 (.branch 1070
 (.branch 1044
 (.branch 1031
 (.branch 1025
 (.branch 1022
 (.branch 1020
 (.leaf (certNat% 1019))
 (.branch 1021
 (.leaf (certNat% 1020))
 (.leaf (certNat% 1021))))
 (.branch 1023
 (.leaf (certNat% 1022))
 (.branch 1024
 (.leaf (certNat% 1023))
 (.leaf (certNat% 1024)))))
 (.branch 1028
 (.branch 1026
 (.leaf (certNat% 1025))
 (.branch 1027
 (.leaf (certNat% 1026))
 (.leaf (certNat% 1027))))
 (.branch 1029
 (.leaf (certNat% 1028))
 (.branch 1030
 (.leaf (certNat% 1029))
 (.leaf (certNat% 1030))))))
 (.branch 1037
 (.branch 1034
 (.branch 1032
 (.leaf (certNat% 1031))
 (.branch 1033
 (.leaf (certNat% 1032))
 (.leaf (certNat% 1033))))
 (.branch 1035
 (.leaf (certNat% 1034))
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
 (.branch 1063
 (.branch 1060
 (.branch 1058
 (.leaf (certNat% 1057))
 (.branch 1059
 (.leaf (certNat% 1058))
 (.leaf (certNat% 1059))))
 (.branch 1061
 (.leaf (certNat% 1060))
 (.branch 1062
 (.leaf (certNat% 1061))
 (.leaf (certNat% 1062)))))
 (.branch 1066
 (.branch 1064
 (.leaf (certNat% 1063))
 (.branch 1065
 (.leaf (certNat% 1064))
 (.leaf (certNat% 1065))))
 (.branch 1068
 (.branch 1067
 (.leaf (certNat% 1066))
 (.leaf (certNat% 1067)))
 (.branch 1069
 (.leaf (certNat% 1068))
 (.leaf (certNat% 1069))))))))
 (.branch 1095
 (.branch 1082
 (.branch 1076
 (.branch 1073
 (.branch 1071
 (.leaf (certNat% 1070))
 (.branch 1072
 (.leaf (certNat% 1071))
 (.leaf (certNat% 1072))))
 (.branch 1074
 (.leaf (certNat% 1073))
 (.branch 1075
 (.leaf (certNat% 1074))
 (.leaf (certNat% 1075)))))
 (.branch 1079
 (.branch 1077
 (.leaf (certNat% 1076))
 (.branch 1078
 (.leaf (certNat% 1077))
 (.leaf (certNat% 1078))))
 (.branch 1080
 (.leaf (certNat% 1079))
 (.branch 1081
 (.leaf (certNat% 1080))
 (.leaf (certNat% 1081))))))
 (.branch 1088
 (.branch 1085
 (.branch 1083
 (.leaf (certNat% 1082))
 (.branch 1084
 (.leaf (certNat% 1083))
 (.leaf (certNat% 1084))))
 (.branch 1086
 (.leaf (certNat% 1085))
 (.branch 1087
 (.leaf (certNat% 1086))
 (.leaf (certNat% 1087)))))
 (.branch 1091
 (.branch 1089
 (.leaf (certNat% 1088))
 (.branch 1090
 (.leaf (certNat% 1089))
 (.leaf (certNat% 1090))))
 (.branch 1093
 (.branch 1092
 (.leaf (certNat% 1091))
 (.leaf (certNat% 1092)))
 (.branch 1094
 (.leaf (certNat% 1093))
 (.leaf (certNat% 1094)))))))
 (.branch 1108
 (.branch 1101
 (.branch 1098
 (.branch 1096
 (.leaf (certNat% 1095))
 (.branch 1097
 (.leaf (certNat% 1096))
 (.leaf (certNat% 1097))))
 (.branch 1099
 (.leaf (certNat% 1098))
 (.branch 1100
 (.leaf (certNat% 1099))
 (.leaf (certNat% 1100)))))
 (.branch 1104
 (.branch 1102
 (.leaf (certNat% 1101))
 (.branch 1103
 (.leaf (certNat% 1102))
 (.leaf (certNat% 1103))))
 (.branch 1106
 (.branch 1105
 (.leaf (certNat% 1104))
 (.leaf (certNat% 1105)))
 (.branch 1107
 (.leaf (certNat% 1106))
 (.leaf (certNat% 1107))))))
 (.branch 1114
 (.branch 1111
 (.branch 1109
 (.leaf (certNat% 1108))
 (.branch 1110
 (.leaf (certNat% 1109))
 (.leaf (certNat% 1110))))
 (.branch 1112
 (.leaf (certNat% 1111))
 (.branch 1113
 (.leaf (certNat% 1112))
 (.leaf (certNat% 1113)))))
 (.branch 1117
 (.branch 1115
 (.leaf (certNat% 1114))
 (.branch 1116
 (.leaf (certNat% 1115))
 (.leaf (certNat% 1116))))
 (.branch 1119
 (.branch 1118
 (.leaf (certNat% 1117))
 (.leaf (certNat% 1118)))
 (.branch 1120
 (.leaf (certNat% 1119))
 (.leaf (certNat% 1120)))))))))
 (.branch 1172
 (.branch 1146
 (.branch 1133
 (.branch 1127
 (.branch 1124
 (.branch 1122
 (.leaf (certNat% 1121))
 (.branch 1123
 (.leaf (certNat% 1122))
 (.leaf (certNat% 1123))))
 (.branch 1125
 (.leaf (certNat% 1124))
 (.branch 1126
 (.leaf (certNat% 1125))
 (.leaf (certNat% 1126)))))
 (.branch 1130
 (.branch 1128
 (.leaf (certNat% 1127))
 (.branch 1129
 (.leaf (certNat% 1128))
 (.leaf (certNat% 1129))))
 (.branch 1131
 (.leaf (certNat% 1130))
 (.branch 1132
 (.leaf (certNat% 1131))
 (.leaf (certNat% 1132))))))
 (.branch 1139
 (.branch 1136
 (.branch 1134
 (.leaf (certNat% 1133))
 (.branch 1135
 (.leaf (certNat% 1134))
 (.leaf (certNat% 1135))))
 (.branch 1137
 (.leaf (certNat% 1136))
 (.branch 1138
 (.leaf (certNat% 1137))
 (.leaf (certNat% 1138)))))
 (.branch 1142
 (.branch 1140
 (.leaf (certNat% 1139))
 (.branch 1141
 (.leaf (certNat% 1140))
 (.leaf (certNat% 1141))))
 (.branch 1144
 (.branch 1143
 (.leaf (certNat% 1142))
 (.leaf (certNat% 1143)))
 (.branch 1145
 (.leaf (certNat% 1144))
 (.leaf (certNat% 1145)))))))
 (.branch 1159
 (.branch 1152
 (.branch 1149
 (.branch 1147
 (.leaf (certNat% 1146))
 (.branch 1148
 (.leaf (certNat% 1147))
 (.leaf (certNat% 1148))))
 (.branch 1150
 (.leaf (certNat% 1149))
 (.branch 1151
 (.leaf (certNat% 1150))
 (.leaf (certNat% 1151)))))
 (.branch 1155
 (.branch 1153
 (.leaf (certNat% 1152))
 (.branch 1154
 (.leaf (certNat% 1153))
 (.leaf (certNat% 1154))))
 (.branch 1157
 (.branch 1156
 (.leaf (certNat% 1155))
 (.leaf (certNat% 1156)))
 (.branch 1158
 (.leaf (certNat% 1157))
 (.leaf (certNat% 1158))))))
 (.branch 1165
 (.branch 1162
 (.branch 1160
 (.leaf (certNat% 1159))
 (.branch 1161
 (.leaf (certNat% 1160))
 (.leaf (certNat% 1161))))
 (.branch 1163
 (.leaf (certNat% 1162))
 (.branch 1164
 (.leaf (certNat% 1163))
 (.leaf (certNat% 1164)))))
 (.branch 1168
 (.branch 1166
 (.leaf (certNat% 1165))
 (.branch 1167
 (.leaf (certNat% 1166))
 (.leaf (certNat% 1167))))
 (.branch 1170
 (.branch 1169
 (.leaf (certNat% 1168))
 (.leaf (certNat% 1169)))
 (.branch 1171
 (.leaf (certNat% 1170))
 (.leaf (certNat% 1171))))))))
 (.branch 1197
 (.branch 1184
 (.branch 1178
 (.branch 1175
 (.branch 1173
 (.leaf (certNat% 1172))
 (.branch 1174
 (.leaf (certNat% 1173))
 (.leaf (certNat% 1174))))
 (.branch 1176
 (.leaf (certNat% 1175))
 (.branch 1177
 (.leaf (certNat% 1176))
 (.leaf (certNat% 1177)))))
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
 (.leaf (certNat% 1183))))))
 (.branch 1190
 (.branch 1187
 (.branch 1185
 (.leaf (certNat% 1184))
 (.branch 1186
 (.leaf (certNat% 1185))
 (.leaf (certNat% 1186))))
 (.branch 1188
 (.leaf (certNat% 1187))
 (.branch 1189
 (.leaf (certNat% 1188))
 (.leaf (certNat% 1189)))))
 (.branch 1193
 (.branch 1191
 (.leaf (certNat% 1190))
 (.branch 1192
 (.leaf (certNat% 1191))
 (.leaf (certNat% 1192))))
 (.branch 1195
 (.branch 1194
 (.leaf (certNat% 1193))
 (.leaf (certNat% 1194)))
 (.branch 1196
 (.leaf (certNat% 1195))
 (.leaf (certNat% 1196)))))))
 (.branch 1210
 (.branch 1203
 (.branch 1200
 (.branch 1198
 (.leaf (certNat% 1197))
 (.branch 1199
 (.leaf (certNat% 1198))
 (.leaf (certNat% 1199))))
 (.branch 1201
 (.leaf (certNat% 1200))
 (.branch 1202
 (.leaf (certNat% 1201))
 (.leaf (certNat% 1202)))))
 (.branch 1206
 (.branch 1204
 (.leaf (certNat% 1203))
 (.branch 1205
 (.leaf (certNat% 1204))
 (.leaf (certNat% 1205))))
 (.branch 1208
 (.branch 1207
 (.leaf (certNat% 1206))
 (.leaf (certNat% 1207)))
 (.branch 1209
 (.leaf (certNat% 1208))
 (.leaf (certNat% 1209))))))
 (.branch 1216
 (.branch 1213
 (.branch 1211
 (.leaf (certNat% 1210))
 (.branch 1212
 (.leaf (certNat% 1211))
 (.leaf (certNat% 1212))))
 (.branch 1214
 (.leaf (certNat% 1213))
 (.branch 1215
 (.leaf (certNat% 1214))
 (.leaf (certNat% 1215)))))
 (.branch 1219
 (.branch 1217
 (.leaf (certNat% 1216))
 (.branch 1218
 (.leaf (certNat% 1217))
 (.leaf (certNat% 1218))))
 (.branch 1221
 (.branch 1220
 (.leaf (certNat% 1219))
 (.leaf (certNat% 1220)))
 (.branch 1222
 (.leaf (certNat% 1221))
 (.leaf (certNat% 1222)))))))))))
 (.branch 1427
 (.branch 1325
 (.branch 1274
 (.branch 1248
 (.branch 1235
 (.branch 1229
 (.branch 1226
 (.branch 1224
 (.leaf (certNat% 1223))
 (.branch 1225
 (.leaf (certNat% 1224))
 (.leaf (certNat% 1225))))
 (.branch 1227
 (.leaf (certNat% 1226))
 (.branch 1228
 (.leaf (certNat% 1227))
 (.leaf (certNat% 1228)))))
 (.branch 1232
 (.branch 1230
 (.leaf (certNat% 1229))
 (.branch 1231
 (.leaf (certNat% 1230))
 (.leaf (certNat% 1231))))
 (.branch 1233
 (.leaf (certNat% 1232))
 (.branch 1234
 (.leaf (certNat% 1233))
 (.leaf (certNat% 1234))))))
 (.branch 1241
 (.branch 1238
 (.branch 1236
 (.leaf (certNat% 1235))
 (.branch 1237
 (.leaf (certNat% 1236))
 (.leaf (certNat% 1237))))
 (.branch 1239
 (.leaf (certNat% 1238))
 (.branch 1240
 (.leaf (certNat% 1239))
 (.leaf (certNat% 1240)))))
 (.branch 1244
 (.branch 1242
 (.leaf (certNat% 1241))
 (.branch 1243
 (.leaf (certNat% 1242))
 (.leaf (certNat% 1243))))
 (.branch 1246
 (.branch 1245
 (.leaf (certNat% 1244))
 (.leaf (certNat% 1245)))
 (.branch 1247
 (.leaf (certNat% 1246))
 (.leaf (certNat% 1247)))))))
 (.branch 1261
 (.branch 1254
 (.branch 1251
 (.branch 1249
 (.leaf (certNat% 1248))
 (.branch 1250
 (.leaf (certNat% 1249))
 (.leaf (certNat% 1250))))
 (.branch 1252
 (.leaf (certNat% 1251))
 (.branch 1253
 (.leaf (certNat% 1252))
 (.leaf (certNat% 1253)))))
 (.branch 1257
 (.branch 1255
 (.leaf (certNat% 1254))
 (.branch 1256
 (.leaf (certNat% 1255))
 (.leaf (certNat% 1256))))
 (.branch 1259
 (.branch 1258
 (.leaf (certNat% 1257))
 (.leaf (certNat% 1258)))
 (.branch 1260
 (.leaf (certNat% 1259))
 (.leaf (certNat% 1260))))))
 (.branch 1267
 (.branch 1264
 (.branch 1262
 (.leaf (certNat% 1261))
 (.branch 1263
 (.leaf (certNat% 1262))
 (.leaf (certNat% 1263))))
 (.branch 1265
 (.leaf (certNat% 1264))
 (.branch 1266
 (.leaf (certNat% 1265))
 (.leaf (certNat% 1266)))))
 (.branch 1270
 (.branch 1268
 (.leaf (certNat% 1267))
 (.branch 1269
 (.leaf (certNat% 1268))
 (.leaf (certNat% 1269))))
 (.branch 1272
 (.branch 1271
 (.leaf (certNat% 1270))
 (.leaf (certNat% 1271)))
 (.branch 1273
 (.leaf (certNat% 1272))
 (.leaf (certNat% 1273))))))))
 (.branch 1299
 (.branch 1286
 (.branch 1280
 (.branch 1277
 (.branch 1275
 (.leaf (certNat% 1274))
 (.branch 1276
 (.leaf (certNat% 1275))
 (.leaf (certNat% 1276))))
 (.branch 1278
 (.leaf (certNat% 1277))
 (.branch 1279
 (.leaf (certNat% 1278))
 (.leaf (certNat% 1279)))))
 (.branch 1283
 (.branch 1281
 (.leaf (certNat% 1280))
 (.branch 1282
 (.leaf (certNat% 1281))
 (.leaf (certNat% 1282))))
 (.branch 1284
 (.leaf (certNat% 1283))
 (.branch 1285
 (.leaf (certNat% 1284))
 (.leaf (certNat% 1285))))))
 (.branch 1292
 (.branch 1289
 (.branch 1287
 (.leaf (certNat% 1286))
 (.branch 1288
 (.leaf (certNat% 1287))
 (.leaf (certNat% 1288))))
 (.branch 1290
 (.leaf (certNat% 1289))
 (.branch 1291
 (.leaf (certNat% 1290))
 (.leaf (certNat% 1291)))))
 (.branch 1295
 (.branch 1293
 (.leaf (certNat% 1292))
 (.branch 1294
 (.leaf (certNat% 1293))
 (.leaf (certNat% 1294))))
 (.branch 1297
 (.branch 1296
 (.leaf (certNat% 1295))
 (.leaf (certNat% 1296)))
 (.branch 1298
 (.leaf (certNat% 1297))
 (.leaf (certNat% 1298)))))))
 (.branch 1312
 (.branch 1305
 (.branch 1302
 (.branch 1300
 (.leaf (certNat% 1299))
 (.branch 1301
 (.leaf (certNat% 1300))
 (.leaf (certNat% 1301))))
 (.branch 1303
 (.leaf (certNat% 1302))
 (.branch 1304
 (.leaf (certNat% 1303))
 (.leaf (certNat% 1304)))))
 (.branch 1308
 (.branch 1306
 (.leaf (certNat% 1305))
 (.branch 1307
 (.leaf (certNat% 1306))
 (.leaf (certNat% 1307))))
 (.branch 1310
 (.branch 1309
 (.leaf (certNat% 1308))
 (.leaf (certNat% 1309)))
 (.branch 1311
 (.leaf (certNat% 1310))
 (.leaf (certNat% 1311))))))
 (.branch 1318
 (.branch 1315
 (.branch 1313
 (.leaf (certNat% 1312))
 (.branch 1314
 (.leaf (certNat% 1313))
 (.leaf (certNat% 1314))))
 (.branch 1316
 (.leaf (certNat% 1315))
 (.branch 1317
 (.leaf (certNat% 1316))
 (.leaf (certNat% 1317)))))
 (.branch 1321
 (.branch 1319
 (.leaf (certNat% 1318))
 (.branch 1320
 (.leaf (certNat% 1319))
 (.leaf (certNat% 1320))))
 (.branch 1323
 (.branch 1322
 (.leaf (certNat% 1321))
 (.leaf (certNat% 1322)))
 (.branch 1324
 (.leaf (certNat% 1323))
 (.leaf (certNat% 1324)))))))))
 (.branch 1376
 (.branch 1350
 (.branch 1337
 (.branch 1331
 (.branch 1328
 (.branch 1326
 (.leaf (certNat% 1325))
 (.branch 1327
 (.leaf (certNat% 1326))
 (.leaf (certNat% 1327))))
 (.branch 1329
 (.leaf (certNat% 1328))
 (.branch 1330
 (.leaf (certNat% 1329))
 (.leaf (certNat% 1330)))))
 (.branch 1334
 (.branch 1332
 (.leaf (certNat% 1331))
 (.branch 1333
 (.leaf (certNat% 1332))
 (.leaf (certNat% 1333))))
 (.branch 1335
 (.leaf (certNat% 1334))
 (.branch 1336
 (.leaf (certNat% 1335))
 (.leaf (certNat% 1336))))))
 (.branch 1343
 (.branch 1340
 (.branch 1338
 (.leaf (certNat% 1337))
 (.branch 1339
 (.leaf (certNat% 1338))
 (.leaf (certNat% 1339))))
 (.branch 1341
 (.leaf (certNat% 1340))
 (.branch 1342
 (.leaf (certNat% 1341))
 (.leaf (certNat% 1342)))))
 (.branch 1346
 (.branch 1344
 (.leaf (certNat% 1343))
 (.branch 1345
 (.leaf (certNat% 1344))
 (.leaf (certNat% 1345))))
 (.branch 1348
 (.branch 1347
 (.leaf (certNat% 1346))
 (.leaf (certNat% 1347)))
 (.branch 1349
 (.leaf (certNat% 1348))
 (.leaf (certNat% 1349)))))))
 (.branch 1363
 (.branch 1356
 (.branch 1353
 (.branch 1351
 (.leaf (certNat% 1350))
 (.branch 1352
 (.leaf (certNat% 1351))
 (.leaf (certNat% 1352))))
 (.branch 1354
 (.leaf (certNat% 1353))
 (.branch 1355
 (.leaf (certNat% 1354))
 (.leaf (certNat% 1355)))))
 (.branch 1359
 (.branch 1357
 (.leaf (certNat% 1356))
 (.branch 1358
 (.leaf (certNat% 1357))
 (.leaf (certNat% 1358))))
 (.branch 1361
 (.branch 1360
 (.leaf (certNat% 1359))
 (.leaf (certNat% 1360)))
 (.branch 1362
 (.leaf (certNat% 1361))
 (.leaf (certNat% 1362))))))
 (.branch 1369
 (.branch 1366
 (.branch 1364
 (.leaf (certNat% 1363))
 (.branch 1365
 (.leaf (certNat% 1364))
 (.leaf (certNat% 1365))))
 (.branch 1367
 (.leaf (certNat% 1366))
 (.branch 1368
 (.leaf (certNat% 1367))
 (.leaf (certNat% 1368)))))
 (.branch 1372
 (.branch 1370
 (.leaf (certNat% 1369))
 (.branch 1371
 (.leaf (certNat% 1370))
 (.leaf (certNat% 1371))))
 (.branch 1374
 (.branch 1373
 (.leaf (certNat% 1372))
 (.leaf (certNat% 1373)))
 (.branch 1375
 (.leaf (certNat% 1374))
 (.leaf (certNat% 1375))))))))
 (.branch 1401
 (.branch 1388
 (.branch 1382
 (.branch 1379
 (.branch 1377
 (.leaf (certNat% 1376))
 (.branch 1378
 (.leaf (certNat% 1377))
 (.leaf (certNat% 1378))))
 (.branch 1380
 (.leaf (certNat% 1379))
 (.branch 1381
 (.leaf (certNat% 1380))
 (.leaf (certNat% 1381)))))
 (.branch 1385
 (.branch 1383
 (.leaf (certNat% 1382))
 (.branch 1384
 (.leaf (certNat% 1383))
 (.leaf (certNat% 1384))))
 (.branch 1386
 (.leaf (certNat% 1385))
 (.branch 1387
 (.leaf (certNat% 1386))
 (.leaf (certNat% 1387))))))
 (.branch 1394
 (.branch 1391
 (.branch 1389
 (.leaf (certNat% 1388))
 (.branch 1390
 (.leaf (certNat% 1389))
 (.leaf (certNat% 1390))))
 (.branch 1392
 (.leaf (certNat% 1391))
 (.branch 1393
 (.leaf (certNat% 1392))
 (.leaf (certNat% 1393)))))
 (.branch 1397
 (.branch 1395
 (.leaf (certNat% 1394))
 (.branch 1396
 (.leaf (certNat% 1395))
 (.leaf (certNat% 1396))))
 (.branch 1399
 (.branch 1398
 (.leaf (certNat% 1397))
 (.leaf (certNat% 1398)))
 (.branch 1400
 (.leaf (certNat% 1399))
 (.leaf (certNat% 1400)))))))
 (.branch 1414
 (.branch 1407
 (.branch 1404
 (.branch 1402
 (.leaf (certNat% 1401))
 (.branch 1403
 (.leaf (certNat% 1402))
 (.leaf (certNat% 1403))))
 (.branch 1405
 (.leaf (certNat% 1404))
 (.branch 1406
 (.leaf (certNat% 1405))
 (.leaf (certNat% 1406)))))
 (.branch 1410
 (.branch 1408
 (.leaf (certNat% 1407))
 (.branch 1409
 (.leaf (certNat% 1408))
 (.leaf (certNat% 1409))))
 (.branch 1412
 (.branch 1411
 (.leaf (certNat% 1410))
 (.leaf (certNat% 1411)))
 (.branch 1413
 (.leaf (certNat% 1412))
 (.leaf (certNat% 1413))))))
 (.branch 1420
 (.branch 1417
 (.branch 1415
 (.leaf (certNat% 1414))
 (.branch 1416
 (.leaf (certNat% 1415))
 (.leaf (certNat% 1416))))
 (.branch 1418
 (.leaf (certNat% 1417))
 (.branch 1419
 (.leaf (certNat% 1418))
 (.leaf (certNat% 1419)))))
 (.branch 1423
 (.branch 1421
 (.leaf (certNat% 1420))
 (.branch 1422
 (.leaf (certNat% 1421))
 (.leaf (certNat% 1422))))
 (.branch 1425
 (.branch 1424
 (.leaf (certNat% 1423))
 (.leaf (certNat% 1424)))
 (.branch 1426
 (.leaf (certNat% 1425))
 (.leaf (certNat% 1426))))))))))
 (.branch 1529
 (.branch 1478
 (.branch 1452
 (.branch 1439
 (.branch 1433
 (.branch 1430
 (.branch 1428
 (.leaf (certNat% 1427))
 (.branch 1429
 (.leaf (certNat% 1428))
 (.leaf (certNat% 1429))))
 (.branch 1431
 (.leaf (certNat% 1430))
 (.branch 1432
 (.leaf (certNat% 1431))
 (.leaf (certNat% 1432)))))
 (.branch 1436
 (.branch 1434
 (.leaf (certNat% 1433))
 (.branch 1435
 (.leaf (certNat% 1434))
 (.leaf (certNat% 1435))))
 (.branch 1437
 (.leaf (certNat% 1436))
 (.branch 1438
 (.leaf (certNat% 1437))
 (.leaf (certNat% 1438))))))
 (.branch 1445
 (.branch 1442
 (.branch 1440
 (.leaf (certNat% 1439))
 (.branch 1441
 (.leaf (certNat% 1440))
 (.leaf (certNat% 1441))))
 (.branch 1443
 (.leaf (certNat% 1442))
 (.branch 1444
 (.leaf (certNat% 1443))
 (.leaf (certNat% 1444)))))
 (.branch 1448
 (.branch 1446
 (.leaf (certNat% 1445))
 (.branch 1447
 (.leaf (certNat% 1446))
 (.leaf (certNat% 1447))))
 (.branch 1450
 (.branch 1449
 (.leaf (certNat% 1448))
 (.leaf (certNat% 1449)))
 (.branch 1451
 (.leaf (certNat% 1450))
 (.leaf (certNat% 1451)))))))
 (.branch 1465
 (.branch 1458
 (.branch 1455
 (.branch 1453
 (.leaf (certNat% 1452))
 (.branch 1454
 (.leaf (certNat% 1453))
 (.leaf (certNat% 1454))))
 (.branch 1456
 (.leaf (certNat% 1455))
 (.branch 1457
 (.leaf (certNat% 1456))
 (.leaf (certNat% 1457)))))
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
 (.leaf (certNat% 1464))))))
 (.branch 1471
 (.branch 1468
 (.branch 1466
 (.leaf (certNat% 1465))
 (.branch 1467
 (.leaf (certNat% 1466))
 (.leaf (certNat% 1467))))
 (.branch 1469
 (.leaf (certNat% 1468))
 (.branch 1470
 (.leaf (certNat% 1469))
 (.leaf (certNat% 1470)))))
 (.branch 1474
 (.branch 1472
 (.leaf (certNat% 1471))
 (.branch 1473
 (.leaf (certNat% 1472))
 (.leaf (certNat% 1473))))
 (.branch 1476
 (.branch 1475
 (.leaf (certNat% 1474))
 (.leaf (certNat% 1475)))
 (.branch 1477
 (.leaf (certNat% 1476))
 (.leaf (certNat% 1477))))))))
 (.branch 1503
 (.branch 1490
 (.branch 1484
 (.branch 1481
 (.branch 1479
 (.leaf (certNat% 1478))
 (.branch 1480
 (.leaf (certNat% 1479))
 (.leaf (certNat% 1480))))
 (.branch 1482
 (.leaf (certNat% 1481))
 (.branch 1483
 (.leaf (certNat% 1482))
 (.leaf (certNat% 1483)))))
 (.branch 1487
 (.branch 1485
 (.leaf (certNat% 1484))
 (.branch 1486
 (.leaf (certNat% 1485))
 (.leaf (certNat% 1486))))
 (.branch 1488
 (.leaf (certNat% 1487))
 (.branch 1489
 (.leaf (certNat% 1488))
 (.leaf (certNat% 1489))))))
 (.branch 1496
 (.branch 1493
 (.branch 1491
 (.leaf (certNat% 1490))
 (.branch 1492
 (.leaf (certNat% 1491))
 (.leaf (certNat% 1492))))
 (.branch 1494
 (.leaf (certNat% 1493))
 (.branch 1495
 (.leaf (certNat% 1494))
 (.leaf (certNat% 1495)))))
 (.branch 1499
 (.branch 1497
 (.leaf (certNat% 1496))
 (.branch 1498
 (.leaf (certNat% 1497))
 (.leaf (certNat% 1498))))
 (.branch 1501
 (.branch 1500
 (.leaf (certNat% 1499))
 (.leaf (certNat% 1500)))
 (.branch 1502
 (.leaf (certNat% 1501))
 (.leaf (certNat% 1502)))))))
 (.branch 1516
 (.branch 1509
 (.branch 1506
 (.branch 1504
 (.leaf (certNat% 1503))
 (.branch 1505
 (.leaf (certNat% 1504))
 (.leaf (certNat% 1505))))
 (.branch 1507
 (.leaf (certNat% 1506))
 (.branch 1508
 (.leaf (certNat% 1507))
 (.leaf (certNat% 1508)))))
 (.branch 1512
 (.branch 1510
 (.leaf (certNat% 1509))
 (.branch 1511
 (.leaf (certNat% 1510))
 (.leaf (certNat% 1511))))
 (.branch 1514
 (.branch 1513
 (.leaf (certNat% 1512))
 (.leaf (certNat% 1513)))
 (.branch 1515
 (.leaf (certNat% 1514))
 (.leaf (certNat% 1515))))))
 (.branch 1522
 (.branch 1519
 (.branch 1517
 (.leaf (certNat% 1516))
 (.branch 1518
 (.leaf (certNat% 1517))
 (.leaf (certNat% 1518))))
 (.branch 1520
 (.leaf (certNat% 1519))
 (.branch 1521
 (.leaf (certNat% 1520))
 (.leaf (certNat% 1521)))))
 (.branch 1525
 (.branch 1523
 (.leaf (certNat% 1522))
 (.branch 1524
 (.leaf (certNat% 1523))
 (.leaf (certNat% 1524))))
 (.branch 1527
 (.branch 1526
 (.leaf (certNat% 1525))
 (.leaf (certNat% 1526)))
 (.branch 1528
 (.leaf (certNat% 1527))
 (.leaf (certNat% 1528)))))))))
 (.branch 1580
 (.branch 1554
 (.branch 1541
 (.branch 1535
 (.branch 1532
 (.branch 1530
 (.leaf (certNat% 1529))
 (.branch 1531
 (.leaf (certNat% 1530))
 (.leaf (certNat% 1531))))
 (.branch 1533
 (.leaf (certNat% 1532))
 (.branch 1534
 (.leaf (certNat% 1533))
 (.leaf (certNat% 1534)))))
 (.branch 1538
 (.branch 1536
 (.leaf (certNat% 1535))
 (.branch 1537
 (.leaf (certNat% 1536))
 (.leaf (certNat% 1537))))
 (.branch 1539
 (.leaf (certNat% 1538))
 (.branch 1540
 (.leaf (certNat% 1539))
 (.leaf (certNat% 1540))))))
 (.branch 1547
 (.branch 1544
 (.branch 1542
 (.leaf (certNat% 1541))
 (.branch 1543
 (.leaf (certNat% 1542))
 (.leaf (certNat% 1543))))
 (.branch 1545
 (.leaf (certNat% 1544))
 (.branch 1546
 (.leaf (certNat% 1545))
 (.leaf (certNat% 1546)))))
 (.branch 1550
 (.branch 1548
 (.leaf (certNat% 1547))
 (.branch 1549
 (.leaf (certNat% 1548))
 (.leaf (certNat% 1549))))
 (.branch 1552
 (.branch 1551
 (.leaf (certNat% 1550))
 (.leaf (certNat% 1551)))
 (.branch 1553
 (.leaf (certNat% 1552))
 (.leaf (certNat% 1553)))))))
 (.branch 1567
 (.branch 1560
 (.branch 1557
 (.branch 1555
 (.leaf (certNat% 1554))
 (.branch 1556
 (.leaf (certNat% 1555))
 (.leaf (certNat% 1556))))
 (.branch 1558
 (.leaf (certNat% 1557))
 (.branch 1559
 (.leaf (certNat% 1558))
 (.leaf (certNat% 1559)))))
 (.branch 1563
 (.branch 1561
 (.leaf (certNat% 1560))
 (.branch 1562
 (.leaf (certNat% 1561))
 (.leaf (certNat% 1562))))
 (.branch 1565
 (.branch 1564
 (.leaf (certNat% 1563))
 (.leaf (certNat% 1564)))
 (.branch 1566
 (.leaf (certNat% 1565))
 (.leaf (certNat% 1566))))))
 (.branch 1573
 (.branch 1570
 (.branch 1568
 (.leaf (certNat% 1567))
 (.branch 1569
 (.leaf (certNat% 1568))
 (.leaf (certNat% 1569))))
 (.branch 1571
 (.leaf (certNat% 1570))
 (.branch 1572
 (.leaf (certNat% 1571))
 (.leaf (certNat% 1572)))))
 (.branch 1576
 (.branch 1574
 (.leaf (certNat% 1573))
 (.branch 1575
 (.leaf (certNat% 1574))
 (.leaf (certNat% 1575))))
 (.branch 1578
 (.branch 1577
 (.leaf (certNat% 1576))
 (.leaf (certNat% 1577)))
 (.branch 1579
 (.leaf (certNat% 1578))
 (.leaf (certNat% 1579))))))))
 (.branch 1605
 (.branch 1592
 (.branch 1586
 (.branch 1583
 (.branch 1581
 (.leaf (certNat% 1580))
 (.branch 1582
 (.leaf (certNat% 1581))
 (.leaf (certNat% 1582))))
 (.branch 1584
 (.leaf (certNat% 1583))
 (.branch 1585
 (.leaf (certNat% 1584))
 (.leaf (certNat% 1585)))))
 (.branch 1589
 (.branch 1587
 (.leaf (certNat% 1586))
 (.branch 1588
 (.leaf (certNat% 1587))
 (.leaf (certNat% 1588))))
 (.branch 1590
 (.leaf (certNat% 1589))
 (.branch 1591
 (.leaf (certNat% 1590))
 (.leaf (certNat% 1591))))))
 (.branch 1598
 (.branch 1595
 (.branch 1593
 (.leaf (certNat% 1592))
 (.branch 1594
 (.leaf (certNat% 1593))
 (.leaf (certNat% 1594))))
 (.branch 1596
 (.leaf (certNat% 1595))
 (.branch 1597
 (.leaf (certNat% 1596))
 (.leaf (certNat% 1597)))))
 (.branch 1601
 (.branch 1599
 (.leaf (certNat% 1598))
 (.branch 1600
 (.leaf (certNat% 1599))
 (.leaf (certNat% 1600))))
 (.branch 1603
 (.branch 1602
 (.leaf (certNat% 1601))
 (.leaf (certNat% 1602)))
 (.branch 1604
 (.leaf (certNat% 1603))
 (.leaf (certNat% 1604)))))))
 (.branch 1618
 (.branch 1611
 (.branch 1608
 (.branch 1606
 (.leaf (certNat% 1605))
 (.branch 1607
 (.leaf (certNat% 1606))
 (.leaf (certNat% 1607))))
 (.branch 1609
 (.leaf (certNat% 1608))
 (.branch 1610
 (.leaf (certNat% 1609))
 (.leaf (certNat% 1610)))))
 (.branch 1614
 (.branch 1612
 (.leaf (certNat% 1611))
 (.branch 1613
 (.leaf (certNat% 1612))
 (.leaf (certNat% 1613))))
 (.branch 1616
 (.branch 1615
 (.leaf (certNat% 1614))
 (.leaf (certNat% 1615)))
 (.branch 1617
 (.leaf (certNat% 1616))
 (.leaf (certNat% 1617))))))
 (.branch 1624
 (.branch 1621
 (.branch 1619
 (.leaf (certNat% 1618))
 (.branch 1620
 (.leaf (certNat% 1619))
 (.leaf (certNat% 1620))))
 (.branch 1622
 (.leaf (certNat% 1621))
 (.branch 1623
 (.leaf (certNat% 1622))
 (.leaf (certNat% 1623)))))
 (.branch 1627
 (.branch 1625
 (.leaf (certNat% 1624))
 (.branch 1626
 (.leaf (certNat% 1625))
 (.leaf (certNat% 1626))))
 (.branch 1629
 (.branch 1628
 (.leaf (certNat% 1627))
 (.leaf (certNat% 1628)))
 (.branch 1630
 (.leaf (certNat% 1629))
 (.leaf (certNat% 1630)))))))))))))
cert_rawLeaves_4 13
cert_leaves_3
cert_quota_3 0 4 0 0 0 0 0 0 2 7
cert_nodeTest_5 48 02
cert_nodeTest_sound_4 48 02
cert_leafTest_4 02
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0708

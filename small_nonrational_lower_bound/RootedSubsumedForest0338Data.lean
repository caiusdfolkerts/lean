module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public meta import CertificateNumbers
public import RootedSixBase00GrowthCacheData
public import RootedSixBase00FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification
public import RootedSubsumedForest0338Packed000
public import RootedSubsumedForest0338Packed001
public import RootedSubsumedForest0338Packed002
public import RootedSubsumedForest0338Packed003
public import RootedSubsumedForest0338Packed004
public import RootedSubsumedForest0338Packed005
public import RootedSubsumedForest0338Packed006
public import RootedSubsumedForest0338Packed007
public import RootedSubsumedForest0338Packed008
public import RootedSubsumedForest0338Packed009

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0338
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 21976
abbrev nodeCount : Nat := 58209
abbrev leafCount : Nat := 383
cert_widths_3 15 16 7 9
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
(.branch 191
 (.branch 95
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
 (.branch 71
 (.branch 59
 (.branch 53
 (.branch 50
 (.branch 48
 (.leaf (certNat% 47))
 (.branch 49
 (.leaf (certNat% 48))
 (.leaf (certNat% 49))))
 (.branch 51
 (.leaf (certNat% 50))
 (.branch 52
 (.leaf (certNat% 51))
 (.leaf (certNat% 52)))))
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
 (.leaf (certNat% 58))))))
 (.branch 65
 (.branch 62
 (.branch 60
 (.leaf (certNat% 59))
 (.branch 61
 (.leaf (certNat% 60))
 (.leaf (certNat% 61))))
 (.branch 63
 (.leaf (certNat% 62))
 (.branch 64
 (.leaf (certNat% 63))
 (.leaf (certNat% 64)))))
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
 (.leaf (certNat% 70)))))))
 (.branch 83
 (.branch 77
 (.branch 74
 (.branch 72
 (.leaf (certNat% 71))
 (.branch 73
 (.leaf (certNat% 72))
 (.leaf (certNat% 73))))
 (.branch 75
 (.leaf (certNat% 74))
 (.branch 76
 (.leaf (certNat% 75))
 (.leaf (certNat% 76)))))
 (.branch 80
 (.branch 78
 (.leaf (certNat% 77))
 (.branch 79
 (.leaf (certNat% 78))
 (.leaf (certNat% 79))))
 (.branch 81
 (.leaf (certNat% 80))
 (.branch 82
 (.leaf (certNat% 81))
 (.leaf (certNat% 82))))))
 (.branch 89
 (.branch 86
 (.branch 84
 (.leaf (certNat% 83))
 (.branch 85
 (.leaf (certNat% 84))
 (.leaf (certNat% 85))))
 (.branch 87
 (.leaf (certNat% 86))
 (.branch 88
 (.leaf (certNat% 87))
 (.leaf (certNat% 88)))))
 (.branch 92
 (.branch 90
 (.leaf (certNat% 89))
 (.branch 91
 (.leaf (certNat% 90))
 (.leaf (certNat% 91))))
 (.branch 93
 (.leaf (certNat% 92))
 (.branch 94
 (.leaf (certNat% 93))
 (.leaf (certNat% 94)))))))))
 (.branch 143
 (.branch 119
 (.branch 107
 (.branch 101
 (.branch 98
 (.branch 96
 (.leaf (certNat% 95))
 (.branch 97
 (.leaf (certNat% 96))
 (.leaf (certNat% 97))))
 (.branch 99
 (.leaf (certNat% 98))
 (.branch 100
 (.leaf (certNat% 99))
 (.leaf (certNat% 100)))))
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
 (.leaf (certNat% 106))))))
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
 (.branch 117
 (.leaf (certNat% 116))
 (.branch 118
 (.leaf (certNat% 117))
 (.leaf (certNat% 118)))))))
 (.branch 131
 (.branch 125
 (.branch 122
 (.branch 120
 (.leaf (certNat% 119))
 (.branch 121
 (.leaf (certNat% 120))
 (.leaf (certNat% 121))))
 (.branch 123
 (.leaf (certNat% 122))
 (.branch 124
 (.leaf (certNat% 123))
 (.leaf (certNat% 124)))))
 (.branch 128
 (.branch 126
 (.leaf (certNat% 125))
 (.branch 127
 (.leaf (certNat% 126))
 (.leaf (certNat% 127))))
 (.branch 129
 (.leaf (certNat% 128))
 (.branch 130
 (.leaf (certNat% 129))
 (.leaf (certNat% 130))))))
 (.branch 137
 (.branch 134
 (.branch 132
 (.leaf (certNat% 131))
 (.branch 133
 (.leaf (certNat% 132))
 (.leaf (certNat% 133))))
 (.branch 135
 (.leaf (certNat% 134))
 (.branch 136
 (.leaf (certNat% 135))
 (.leaf (certNat% 136)))))
 (.branch 140
 (.branch 138
 (.leaf (certNat% 137))
 (.branch 139
 (.leaf (certNat% 138))
 (.leaf (certNat% 139))))
 (.branch 141
 (.leaf (certNat% 140))
 (.branch 142
 (.leaf (certNat% 141))
 (.leaf (certNat% 142))))))))
 (.branch 167
 (.branch 155
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
 (.branch 153
 (.leaf (certNat% 152))
 (.branch 154
 (.leaf (certNat% 153))
 (.leaf (certNat% 154))))))
 (.branch 161
 (.branch 158
 (.branch 156
 (.leaf (certNat% 155))
 (.branch 157
 (.leaf (certNat% 156))
 (.leaf (certNat% 157))))
 (.branch 159
 (.leaf (certNat% 158))
 (.branch 160
 (.leaf (certNat% 159))
 (.leaf (certNat% 160)))))
 (.branch 164
 (.branch 162
 (.leaf (certNat% 161))
 (.branch 163
 (.leaf (certNat% 162))
 (.leaf (certNat% 163))))
 (.branch 165
 (.leaf (certNat% 164))
 (.branch 166
 (.leaf (certNat% 165))
 (.leaf (certNat% 166)))))))
 (.branch 179
 (.branch 173
 (.branch 170
 (.branch 168
 (.leaf (certNat% 167))
 (.branch 169
 (.leaf (certNat% 168))
 (.leaf (certNat% 169))))
 (.branch 171
 (.leaf (certNat% 170))
 (.branch 172
 (.leaf (certNat% 171))
 (.leaf (certNat% 172)))))
 (.branch 176
 (.branch 174
 (.leaf (certNat% 173))
 (.branch 175
 (.leaf (certNat% 174))
 (.leaf (certNat% 175))))
 (.branch 177
 (.leaf (certNat% 176))
 (.branch 178
 (.leaf (certNat% 177))
 (.leaf (certNat% 178))))))
 (.branch 185
 (.branch 182
 (.branch 180
 (.leaf (certNat% 179))
 (.branch 181
 (.leaf (certNat% 180))
 (.leaf (certNat% 181))))
 (.branch 183
 (.leaf (certNat% 182))
 (.branch 184
 (.leaf (certNat% 183))
 (.leaf (certNat% 184)))))
 (.branch 188
 (.branch 186
 (.leaf (certNat% 185))
 (.branch 187
 (.leaf (certNat% 186))
 (.leaf (certNat% 187))))
 (.branch 189
 (.leaf (certNat% 188))
 (.branch 190
 (.leaf (certNat% 189))
 (.leaf (certNat% 190))))))))))
 (.branch 287
 (.branch 239
 (.branch 215
 (.branch 203
 (.branch 197
 (.branch 194
 (.branch 192
 (.leaf (certNat% 191))
 (.branch 193
 (.leaf (certNat% 192))
 (.leaf (certNat% 193))))
 (.branch 195
 (.leaf (certNat% 194))
 (.branch 196
 (.leaf (certNat% 195))
 (.leaf (certNat% 196)))))
 (.branch 200
 (.branch 198
 (.leaf (certNat% 197))
 (.branch 199
 (.leaf (certNat% 198))
 (.leaf (certNat% 199))))
 (.branch 201
 (.leaf (certNat% 200))
 (.branch 202
 (.leaf (certNat% 201))
 (.leaf (certNat% 202))))))
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
 (.leaf (certNat% 214)))))))
 (.branch 227
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
 (.branch 225
 (.leaf (certNat% 224))
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
 (.branch 237
 (.leaf (certNat% 236))
 (.branch 238
 (.leaf (certNat% 237))
 (.leaf (certNat% 238))))))))
 (.branch 263
 (.branch 251
 (.branch 245
 (.branch 242
 (.branch 240
 (.leaf (certNat% 239))
 (.branch 241
 (.leaf (certNat% 240))
 (.leaf (certNat% 241))))
 (.branch 243
 (.leaf (certNat% 242))
 (.branch 244
 (.leaf (certNat% 243))
 (.leaf (certNat% 244)))))
 (.branch 248
 (.branch 246
 (.leaf (certNat% 245))
 (.branch 247
 (.leaf (certNat% 246))
 (.leaf (certNat% 247))))
 (.branch 249
 (.leaf (certNat% 248))
 (.branch 250
 (.leaf (certNat% 249))
 (.leaf (certNat% 250))))))
 (.branch 257
 (.branch 254
 (.branch 252
 (.leaf (certNat% 251))
 (.branch 253
 (.leaf (certNat% 252))
 (.leaf (certNat% 253))))
 (.branch 255
 (.leaf (certNat% 254))
 (.branch 256
 (.leaf (certNat% 255))
 (.leaf (certNat% 256)))))
 (.branch 260
 (.branch 258
 (.leaf (certNat% 257))
 (.branch 259
 (.leaf (certNat% 258))
 (.leaf (certNat% 259))))
 (.branch 261
 (.leaf (certNat% 260))
 (.branch 262
 (.leaf (certNat% 261))
 (.leaf (certNat% 262)))))))
 (.branch 275
 (.branch 269
 (.branch 266
 (.branch 264
 (.leaf (certNat% 263))
 (.branch 265
 (.leaf (certNat% 264))
 (.leaf (certNat% 265))))
 (.branch 267
 (.leaf (certNat% 266))
 (.branch 268
 (.leaf (certNat% 267))
 (.leaf (certNat% 268)))))
 (.branch 272
 (.branch 270
 (.leaf (certNat% 269))
 (.branch 271
 (.leaf (certNat% 270))
 (.leaf (certNat% 271))))
 (.branch 273
 (.leaf (certNat% 272))
 (.branch 274
 (.leaf (certNat% 273))
 (.leaf (certNat% 274))))))
 (.branch 281
 (.branch 278
 (.branch 276
 (.leaf (certNat% 275))
 (.branch 277
 (.leaf (certNat% 276))
 (.leaf (certNat% 277))))
 (.branch 279
 (.leaf (certNat% 278))
 (.branch 280
 (.leaf (certNat% 279))
 (.leaf (certNat% 280)))))
 (.branch 284
 (.branch 282
 (.leaf (certNat% 281))
 (.branch 283
 (.leaf (certNat% 282))
 (.leaf (certNat% 283))))
 (.branch 285
 (.leaf (certNat% 284))
 (.branch 286
 (.leaf (certNat% 285))
 (.leaf (certNat% 286)))))))))
 (.branch 335
 (.branch 311
 (.branch 299
 (.branch 293
 (.branch 290
 (.branch 288
 (.leaf (certNat% 287))
 (.branch 289
 (.leaf (certNat% 288))
 (.leaf (certNat% 289))))
 (.branch 291
 (.leaf (certNat% 290))
 (.branch 292
 (.leaf (certNat% 291))
 (.leaf (certNat% 292)))))
 (.branch 296
 (.branch 294
 (.leaf (certNat% 293))
 (.branch 295
 (.leaf (certNat% 294))
 (.leaf (certNat% 295))))
 (.branch 297
 (.leaf (certNat% 296))
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
 (.branch 309
 (.leaf (certNat% 308))
 (.branch 310
 (.leaf (certNat% 309))
 (.leaf (certNat% 310)))))))
 (.branch 323
 (.branch 317
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
 (.leaf (certNat% 316)))))
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
 (.leaf (certNat% 322))))))
 (.branch 329
 (.branch 326
 (.branch 324
 (.leaf (certNat% 323))
 (.branch 325
 (.leaf (certNat% 324))
 (.leaf (certNat% 325))))
 (.branch 327
 (.leaf (certNat% 326))
 (.branch 328
 (.leaf (certNat% 327))
 (.leaf (certNat% 328)))))
 (.branch 332
 (.branch 330
 (.leaf (certNat% 329))
 (.branch 331
 (.leaf (certNat% 330))
 (.leaf (certNat% 331))))
 (.branch 333
 (.leaf (certNat% 332))
 (.branch 334
 (.leaf (certNat% 333))
 (.leaf (certNat% 334))))))))
 (.branch 359
 (.branch 347
 (.branch 341
 (.branch 338
 (.branch 336
 (.leaf (certNat% 335))
 (.branch 337
 (.leaf (certNat% 336))
 (.leaf (certNat% 337))))
 (.branch 339
 (.leaf (certNat% 338))
 (.branch 340
 (.leaf (certNat% 339))
 (.leaf (certNat% 340)))))
 (.branch 344
 (.branch 342
 (.leaf (certNat% 341))
 (.branch 343
 (.leaf (certNat% 342))
 (.leaf (certNat% 343))))
 (.branch 345
 (.leaf (certNat% 344))
 (.branch 346
 (.leaf (certNat% 345))
 (.leaf (certNat% 346))))))
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
 (.branch 357
 (.leaf (certNat% 356))
 (.branch 358
 (.leaf (certNat% 357))
 (.leaf (certNat% 358)))))))
 (.branch 371
 (.branch 365
 (.branch 362
 (.branch 360
 (.leaf (certNat% 359))
 (.branch 361
 (.leaf (certNat% 360))
 (.leaf (certNat% 361))))
 (.branch 363
 (.leaf (certNat% 362))
 (.branch 364
 (.leaf (certNat% 363))
 (.leaf (certNat% 364)))))
 (.branch 368
 (.branch 366
 (.leaf (certNat% 365))
 (.branch 367
 (.leaf (certNat% 366))
 (.leaf (certNat% 367))))
 (.branch 369
 (.leaf (certNat% 368))
 (.branch 370
 (.leaf (certNat% 369))
 (.leaf (certNat% 370))))))
 (.branch 377
 (.branch 374
 (.branch 372
 (.leaf (certNat% 371))
 (.branch 373
 (.leaf (certNat% 372))
 (.leaf (certNat% 373))))
 (.branch 375
 (.leaf (certNat% 374))
 (.branch 376
 (.leaf (certNat% 375))
 (.leaf (certNat% 376)))))
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
 (.leaf (certNat% 382)))))))))))
cert_rawLeaves_4 15
cert_leaves_3
cert_quota_3 0 3 0 0 0 0 0 0 4 5
cert_nodeTest_5 96 00
cert_nodeTest_sound_4 96 00
cert_leafTest_4 00
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0338

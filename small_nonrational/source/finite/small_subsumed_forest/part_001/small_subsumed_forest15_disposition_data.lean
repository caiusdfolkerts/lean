module
prelude
public import SmallSubsumedForest15Data
public import RawLeafCertificate
public import OldTerminalMatches.M000
public import OldTerminalMatches.M001
public import OldTerminalMatches.M002

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest15
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 289
 (.branch 144
 (.branch 72
 (.branch 36
 (.branch 18
 (.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf (.matching Nonrational.OldTerminalMatches.M000.r0032))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 6
 (.branch 5
 (.leaf (.matching Nonrational.OldTerminalMatches.M000.r0033))
 (.leaf (.matching Nonrational.OldTerminalMatches.M000.r0034)))
 (.branch 7
 (.leaf (.matching Nonrational.OldTerminalMatches.M000.r0035))
 (.branch 8
 (.leaf (.quota 1))
 (.leaf (.matching Nonrational.OldTerminalMatches.M000.r0036))))))
 (.branch 13
 (.branch 11
 (.leaf (.quota 2))
 (.leaf (.incidence 7)))
 (.branch 15
 (.branch 14
 (.leaf (.matching Nonrational.OldTerminalMatches.M000.r0037))
 (.leaf (.incidence 9)))
 (.branch 16
 (.leaf (.incidence 9))
 (.branch 17
 (.leaf (.matching Nonrational.OldTerminalMatches.M000.r0038))
 (.leaf (.incidence 9)))))))
 (.branch 27
 (.branch 22
 (.branch 20
 (.branch 19
 (.leaf (.incidence 9))
 (.leaf (.incidence 7)))
 (.branch 21
 (.leaf (.incidence 7))
 (.leaf (.matching Nonrational.OldTerminalMatches.M000.r0039))))
 (.branch 24
 (.leaf (.quota 2))
 (.branch 25
 (.leaf (.matching Nonrational.OldTerminalMatches.M000.r0040))
 (.leaf (.quota 2)))))
 (.branch 31
 (.branch 29
 (.branch 28
 (.leaf (.incidence 7))
 (.leaf (.incidence 9)))
 (.branch 30
 (.leaf (.matching Nonrational.OldTerminalMatches.M000.r0041))
 (.leaf (.incidence 7))))
 (.branch 33
 (.leaf (.incidence 8))
 (.branch 34
 (.leaf (.matching Nonrational.OldTerminalMatches.M000.r0042))
 (.leaf (.incidence 7)))))))
 (.branch 54
 (.branch 45
 (.branch 40
 (.branch 38
 (.leaf (.incidence 9))
 (.branch 39
 (.leaf (.matching Nonrational.OldTerminalMatches.M000.r0043))
 (.leaf (.incidence 8))))
 (.branch 42
 (.branch 41
 (.leaf (.matching Nonrational.OldTerminalMatches.M000.r0044))
 (.leaf (.incidence 8)))
 (.leaf (.quota 1))))
 (.branch 49
 (.branch 47
 (.branch 46
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 48
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M000.r0045))))
 (.branch 51
 (.branch 50
 (.leaf (.matching Nonrational.OldTerminalMatches.M000.r0046))
 (.leaf (.quota 2)))
 (.branch 52
 (.leaf (.quota 2))
 (.branch 53
 (.leaf (.matching Nonrational.OldTerminalMatches.M000.r0047))
 (.leaf (.incidence 8)))))))
 (.branch 63
 (.branch 58
 (.branch 56
 (.branch 55
 (.leaf (.incidence 8))
 (.leaf (.matching Nonrational.OldTerminalMatches.M000.r0048)))
 (.branch 57
 (.leaf (.matching Nonrational.OldTerminalMatches.M000.r0049))
 (.leaf (.incidence 9))))
 (.branch 60
 (.branch 59
 (.leaf (.matching Nonrational.OldTerminalMatches.M000.r0050))
 (.leaf (.matching Nonrational.OldTerminalMatches.M000.r0051)))
 (.branch 61
 (.leaf (.matching Nonrational.OldTerminalMatches.M000.r0052))
 (.branch 62
 (.leaf (.matching Nonrational.OldTerminalMatches.M000.r0053))
 (.leaf (.quota 1))))))
 (.branch 67
 (.branch 65
 (.branch 64
 (.leaf (.matching Nonrational.OldTerminalMatches.M000.r0054))
 (.leaf (.quota 2)))
 (.leaf (.incidence 3)))
 (.branch 69
 (.branch 68
 (.leaf (.quota 2))
 (.leaf (.incidence 4)))
 (.branch 70
 (.leaf (.quota 2))
 (.branch 71
 (.leaf (.quota 2))
 (.leaf (.incidence 3)))))))))
 (.branch 108
 (.branch 90
 (.branch 81
 (.branch 76
 (.branch 74
 (.branch 73
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 78
 (.leaf (.quota 2))
 (.branch 79
 (.leaf (.incidence 8))
 (.branch 80
 (.leaf (.incidence 8))
 (.leaf (.matching Nonrational.OldTerminalMatches.M000.r0055))))))
 (.branch 85
 (.branch 83
 (.branch 82
 (.leaf (.incidence 5))
 (.leaf (.incidence 8)))
 (.leaf (.incidence 4)))
 (.branch 87
 (.branch 86
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 88
 (.leaf (.incidence 5))
 (.branch 89
 (.leaf (.incidence 7))
 (.leaf (.incidence 9)))))))
 (.branch 99
 (.branch 94
 (.branch 92
 (.branch 91
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 96
 (.leaf (.quota 2))
 (.branch 97
 (.leaf (.quota 2))
 (.branch 98
 (.leaf (.quota 2))
 (.leaf (.incidence 9))))))
 (.branch 103
 (.leaf (.quota 2))
 (.branch 105
 (.leaf (.quota 2))
 (.branch 106
 (.leaf (.matching Nonrational.OldTerminalMatches.M000.r0056))
 (.branch 107
 (.leaf (.matching Nonrational.OldTerminalMatches.M000.r0057))
 (.leaf (.incidence 4))))))))
 (.branch 126
 (.branch 117
 (.branch 112
 (.branch 110
 (.leaf (.quota 1))
 (.branch 111
 (.leaf (.matching Nonrational.OldTerminalMatches.M000.r0058))
 (.leaf (.matching Nonrational.OldTerminalMatches.M000.r0059))))
 (.branch 114
 (.branch 113
 (.leaf (.incidence 6))
 (.leaf (.matching Nonrational.OldTerminalMatches.M000.r0060)))
 (.branch 115
 (.leaf (.matching Nonrational.OldTerminalMatches.M000.r0061))
 (.leaf (.incidence 4)))))
 (.branch 121
 (.branch 119
 (.branch 118
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.incidence 4)))
 (.branch 123
 (.leaf (.incidence 4))
 (.leaf (.quota 2)))))
 (.branch 135
 (.branch 130
 (.branch 128
 (.leaf (.quota 2))
 (.branch 129
 (.leaf (.incidence 4))
 (.leaf (.quota 2))))
 (.branch 132
 (.branch 131
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 133
 (.leaf (.matching Nonrational.OldTerminalMatches.M000.r0062))
 (.branch 134
 (.leaf (.incidence 4))
 (.leaf (.quota 2))))))
 (.branch 139
 (.branch 137
 (.leaf (.incidence 4))
 (.branch 138
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 141
 (.leaf (.quota 2))
 (.branch 142
 (.leaf (.quota 2))
 (.branch 143
 (.leaf (.incidence 4))
 (.leaf (.quota 2))))))))))
 (.branch 216
 (.branch 180
 (.branch 162
 (.branch 153
 (.branch 148
 (.branch 146
 (.leaf (.incidence 4))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 157
 (.branch 155
 (.branch 154
 (.leaf (.matching Nonrational.OldTerminalMatches.M000.r0063))
 (.leaf (.incidence 8)))
 (.branch 156
 (.leaf (.matching Nonrational.OldTerminalMatches.M001.r0064))
 (.leaf (.matching Nonrational.OldTerminalMatches.M001.r0065))))
 (.branch 159
 (.branch 158
 (.leaf (.incidence 7))
 (.leaf (.quota 2)))
 (.branch 160
 (.leaf (.quota 1))
 (.branch 161
 (.leaf (.quota 1))
 (.leaf (.incidence 7)))))))
 (.branch 171
 (.branch 166
 (.branch 164
 (.branch 163
 (.leaf (.incidence 7))
 (.leaf (.incidence 9)))
 (.branch 165
 (.leaf (.incidence 9))
 (.leaf (.quota 1))))
 (.branch 168
 (.branch 167
 (.leaf (.matching Nonrational.OldTerminalMatches.M001.r0066))
 (.leaf (.incidence 9)))
 (.branch 169
 (.leaf (.matching Nonrational.OldTerminalMatches.M001.r0067))
 (.branch 170
 (.leaf (.incidence 8))
 (.leaf (.matching Nonrational.OldTerminalMatches.M001.r0068))))))
 (.branch 175
 (.branch 173
 (.branch 172
 (.leaf (.matching Nonrational.OldTerminalMatches.M001.r0069))
 (.leaf (.matching Nonrational.OldTerminalMatches.M001.r0070)))
 (.branch 174
 (.leaf (.incidence 9))
 (.leaf (.matching Nonrational.OldTerminalMatches.M001.r0071))))
 (.branch 177
 (.branch 176
 (.leaf (.incidence 8))
 (.leaf (.matching Nonrational.OldTerminalMatches.M001.r0072)))
 (.branch 178
 (.leaf (.matching Nonrational.OldTerminalMatches.M001.r0073))
 (.leaf (.incidence 8)))))))
 (.branch 198
 (.branch 189
 (.branch 184
 (.branch 182
 (.branch 181
 (.leaf (.matching Nonrational.OldTerminalMatches.M001.r0074))
 (.leaf (.quota 1)))
 (.branch 183
 (.leaf (.quota 1))
 (.leaf (.matching Nonrational.OldTerminalMatches.M001.r0075))))
 (.branch 186
 (.branch 185
 (.leaf (.incidence 9))
 (.leaf (.incidence 7)))
 (.branch 187
 (.leaf (.incidence 9))
 (.branch 188
 (.leaf (.quota 1))
 (.leaf (.incidence 6))))))
 (.branch 193
 (.branch 191
 (.branch 190
 (.leaf (.incidence 9))
 (.leaf (.incidence 7)))
 (.branch 192
 (.leaf (.matching Nonrational.OldTerminalMatches.M001.r0076))
 (.leaf (.matching Nonrational.OldTerminalMatches.M001.r0077))))
 (.branch 195
 (.branch 194
 (.leaf (.matching Nonrational.OldTerminalMatches.M001.r0078))
 (.leaf (.matching Nonrational.OldTerminalMatches.M001.r0079)))
 (.branch 196
 (.leaf (.incidence 5))
 (.branch 197
 (.leaf (.matching Nonrational.OldTerminalMatches.M001.r0080))
 (.leaf (.incidence 9)))))))
 (.branch 207
 (.branch 202
 (.branch 200
 (.branch 199
 (.leaf (.incidence 6))
 (.leaf (.incidence 8)))
 (.branch 201
 (.leaf (.incidence 7))
 (.leaf (.incidence 8))))
 (.branch 204
 (.branch 203
 (.leaf (.matching Nonrational.OldTerminalMatches.M001.r0081))
 (.leaf (.incidence 8)))
 (.branch 205
 (.leaf (.incidence 7))
 (.branch 206
 (.leaf (.incidence 9))
 (.leaf (.matching Nonrational.OldTerminalMatches.M001.r0082))))))
 (.branch 211
 (.branch 209
 (.branch 208
 (.leaf (.incidence 7))
 (.leaf (.incidence 8)))
 (.branch 210
 (.leaf (.incidence 7))
 (.leaf (.incidence 8))))
 (.branch 213
 (.branch 212
 (.leaf (.incidence 5))
 (.leaf (.incidence 8)))
 (.branch 214
 (.leaf (.matching Nonrational.OldTerminalMatches.M001.r0083))
 (.branch 215
 (.leaf (.matching Nonrational.OldTerminalMatches.M001.r0084))
 (.leaf (.incidence 6)))))))))
 (.branch 252
 (.branch 234
 (.branch 225
 (.branch 220
 (.branch 218
 (.branch 217
 (.leaf (.incidence 6))
 (.leaf (.quota 1)))
 (.branch 219
 (.leaf (.incidence 9))
 (.leaf (.incidence 8))))
 (.branch 222
 (.branch 221
 (.leaf (.matching Nonrational.OldTerminalMatches.M001.r0085))
 (.leaf (.incidence 6)))
 (.branch 223
 (.leaf (.incidence 9))
 (.branch 224
 (.leaf (.matching Nonrational.OldTerminalMatches.M001.r0086))
 (.leaf (.matching Nonrational.OldTerminalMatches.M001.r0087))))))
 (.branch 229
 (.branch 227
 (.branch 226
 (.leaf (.incidence 9))
 (.leaf (.incidence 8)))
 (.branch 228
 (.leaf (.incidence 9))
 (.leaf (.incidence 8))))
 (.branch 231
 (.branch 230
 (.leaf (.incidence 9))
 (.leaf (.quota 2)))
 (.branch 232
 (.leaf (.quota 2))
 (.branch 233
 (.leaf (.incidence 7))
 (.leaf (.matching Nonrational.OldTerminalMatches.M001.r0088)))))))
 (.branch 243
 (.branch 238
 (.branch 236
 (.branch 235
 (.leaf (.matching Nonrational.OldTerminalMatches.M001.r0089))
 (.leaf (.matching Nonrational.OldTerminalMatches.M001.r0090)))
 (.branch 237
 (.leaf (.matching Nonrational.OldTerminalMatches.M001.r0091))
 (.leaf (.matching Nonrational.OldTerminalMatches.M001.r0092))))
 (.branch 240
 (.branch 239
 (.leaf (.matching Nonrational.OldTerminalMatches.M001.r0093))
 (.leaf (.matching Nonrational.OldTerminalMatches.M001.r0094)))
 (.branch 241
 (.leaf (.quota 1))
 (.leaf (.incidence 8)))))
 (.branch 247
 (.branch 245
 (.branch 244
 (.leaf (.matching Nonrational.OldTerminalMatches.M001.r0095))
 (.leaf (.incidence 6)))
 (.branch 246
 (.leaf (.matching Nonrational.OldTerminalMatches.M001.r0096))
 (.leaf (.matching Nonrational.OldTerminalMatches.M001.r0097))))
 (.branch 249
 (.leaf (.quota 2))
 (.branch 250
 (.leaf (.quota 2))
 (.branch 251
 (.leaf (.matching Nonrational.OldTerminalMatches.M001.r0098))
 (.leaf (.matching Nonrational.OldTerminalMatches.M001.r0099))))))))
 (.branch 270
 (.branch 261
 (.branch 256
 (.branch 254
 (.branch 253
 (.leaf (.matching Nonrational.OldTerminalMatches.M001.r0100))
 (.leaf (.matching Nonrational.OldTerminalMatches.M001.r0101)))
 (.branch 255
 (.leaf (.matching Nonrational.OldTerminalMatches.M001.r0102))
 (.leaf (.matching Nonrational.OldTerminalMatches.M001.r0103))))
 (.branch 258
 (.leaf (.quota 1))
 (.branch 259
 (.leaf (.matching Nonrational.OldTerminalMatches.M001.r0104))
 (.branch 260
 (.leaf (.matching Nonrational.OldTerminalMatches.M001.r0105))
 (.leaf (.matching Nonrational.OldTerminalMatches.M001.r0106))))))
 (.branch 265
 (.branch 263
 (.leaf (.incidence 8))
 (.branch 264
 (.leaf (.matching Nonrational.OldTerminalMatches.M001.r0107))
 (.leaf (.incidence 9))))
 (.branch 267
 (.branch 266
 (.leaf (.matching Nonrational.OldTerminalMatches.M001.r0108))
 (.leaf (.matching Nonrational.OldTerminalMatches.M001.r0109)))
 (.branch 268
 (.leaf (.matching Nonrational.OldTerminalMatches.M001.r0110))
 (.branch 269
 (.leaf (.matching Nonrational.OldTerminalMatches.M001.r0111))
 (.leaf (.matching Nonrational.OldTerminalMatches.M001.r0112)))))))
 (.branch 279
 (.branch 274
 (.branch 272
 (.branch 271
 (.leaf (.quota 1))
 (.leaf (.matching Nonrational.OldTerminalMatches.M001.r0113)))
 (.branch 273
 (.leaf (.matching Nonrational.OldTerminalMatches.M001.r0114))
 (.leaf (.matching Nonrational.OldTerminalMatches.M001.r0115))))
 (.branch 276
 (.branch 275
 (.leaf (.incidence 9))
 (.leaf (.quota 1)))
 (.branch 277
 (.leaf (.quota 1))
 (.branch 278
 (.leaf (.matching Nonrational.OldTerminalMatches.M001.r0116))
 (.leaf (.quota 2))))))
 (.branch 284
 (.branch 281
 (.leaf (.quota 2))
 (.branch 282
 (.leaf (.quota 2))
 (.branch 283
 (.leaf (.incidence 9))
 (.leaf (.quota 1)))))
 (.branch 286
 (.branch 285
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M001.r0117)))
 (.branch 287
 (.leaf (.incidence 5))
 (.branch 288
 (.leaf (.matching Nonrational.OldTerminalMatches.M001.r0118))
 (.leaf (.matching Nonrational.OldTerminalMatches.M001.r0119)))))))))))
 (.branch 433
 (.branch 361
 (.branch 325
 (.branch 307
 (.branch 298
 (.branch 293
 (.branch 291
 (.branch 290
 (.leaf (.matching Nonrational.OldTerminalMatches.M001.r0120))
 (.leaf (.matching Nonrational.OldTerminalMatches.M001.r0121)))
 (.leaf (.quota 1)))
 (.branch 295
 (.branch 294
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.branch 316
 (.branch 311
 (.branch 309
 (.branch 308
 (.leaf (.incidence 3))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))
 (.branch 313
 (.branch 312
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M001.r0122)))
 (.branch 314
 (.leaf (.matching Nonrational.OldTerminalMatches.M001.r0123))
 (.leaf (.quota 2)))))
 (.branch 320
 (.branch 318
 (.branch 317
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 319
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M001.r0124))))
 (.branch 322
 (.branch 321
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M001.r0125)))
 (.branch 323
 (.leaf (.matching Nonrational.OldTerminalMatches.M001.r0126))
 (.branch 324
 (.leaf (.matching Nonrational.OldTerminalMatches.M001.r0127))
 (.leaf (.matching Nonrational.OldTerminalMatches.M002.r0128))))))))
 (.branch 343
 (.branch 334
 (.branch 329
 (.branch 327
 (.branch 326
 (.leaf (.matching Nonrational.OldTerminalMatches.M002.r0129))
 (.leaf (.incidence 3)))
 (.branch 328
 (.leaf (.matching Nonrational.OldTerminalMatches.M002.r0130))
 (.leaf (.incidence 7))))
 (.branch 331
 (.branch 330
 (.leaf (.incidence 9))
 (.leaf (.matching Nonrational.OldTerminalMatches.M002.r0131)))
 (.branch 332
 (.leaf (.incidence 3))
 (.branch 333
 (.leaf (.quota 1))
 (.leaf (.matching Nonrational.OldTerminalMatches.M002.r0132))))))
 (.branch 338
 (.branch 336
 (.leaf (.quota 2))
 (.branch 337
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M002.r0133))))
 (.branch 340
 (.branch 339
 (.leaf (.matching Nonrational.OldTerminalMatches.M002.r0134))
 (.leaf (.matching Nonrational.OldTerminalMatches.M002.r0135)))
 (.branch 341
 (.leaf (.matching Nonrational.OldTerminalMatches.M002.r0136))
 (.branch 342
 (.leaf (.quota 1))
 (.leaf (.matching Nonrational.OldTerminalMatches.M002.r0137)))))))
 (.branch 352
 (.branch 347
 (.branch 345
 (.leaf (.quota 2))
 (.branch 346
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M002.r0138))))
 (.branch 349
 (.branch 348
 (.leaf (.matching Nonrational.OldTerminalMatches.M002.r0139))
 (.leaf (.matching Nonrational.OldTerminalMatches.M002.r0140)))
 (.branch 350
 (.leaf (.matching Nonrational.OldTerminalMatches.M002.r0141))
 (.branch 351
 (.leaf (.matching Nonrational.OldTerminalMatches.M002.r0142))
 (.leaf (.matching Nonrational.OldTerminalMatches.M002.r0143))))))
 (.branch 356
 (.branch 354
 (.branch 353
 (.leaf (.matching Nonrational.OldTerminalMatches.M002.r0144))
 (.leaf (.incidence 9)))
 (.branch 355
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 358
 (.leaf (.quota 2))
 (.branch 359
 (.leaf (.quota 2))
 (.branch 360
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M002.r0145)))))))))
 (.branch 397
 (.branch 379
 (.branch 370
 (.branch 365
 (.branch 363
 (.branch 362
 (.leaf (.matching Nonrational.OldTerminalMatches.M002.r0146))
 (.leaf (.matching Nonrational.OldTerminalMatches.M002.r0147)))
 (.branch 364
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 367
 (.leaf (.quota 2))
 (.branch 368
 (.leaf (.quota 2))
 (.branch 369
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M002.r0148))))))
 (.branch 374
 (.branch 372
 (.leaf (.quota 2))
 (.branch 373
 (.leaf (.matching Nonrational.OldTerminalMatches.M002.r0149))
 (.leaf (.matching Nonrational.OldTerminalMatches.M002.r0150))))
 (.branch 376
 (.leaf (.quota 2))
 (.branch 377
 (.leaf (.matching Nonrational.OldTerminalMatches.M002.r0151))
 (.branch 378
 (.leaf (.matching Nonrational.OldTerminalMatches.M002.r0152))
 (.leaf (.quota 1)))))))
 (.branch 388
 (.branch 383
 (.branch 381
 (.branch 380
 (.leaf (.incidence 7))
 (.leaf (.matching Nonrational.OldTerminalMatches.M002.r0153)))
 (.branch 382
 (.leaf (.matching Nonrational.OldTerminalMatches.M002.r0154))
 (.leaf (.matching Nonrational.OldTerminalMatches.M002.r0155))))
 (.branch 385
 (.branch 384
 (.leaf (.quota 2))
 (.leaf (.incidence 3)))
 (.branch 386
 (.leaf (.quota 1))
 (.branch 387
 (.leaf (.matching Nonrational.OldTerminalMatches.M002.r0156))
 (.leaf (.matching Nonrational.OldTerminalMatches.M002.r0157))))))
 (.branch 392
 (.branch 390
 (.branch 389
 (.leaf (.matching Nonrational.OldTerminalMatches.M002.r0158))
 (.leaf (.matching Nonrational.OldTerminalMatches.M002.r0159)))
 (.branch 391
 (.leaf (.incidence 7))
 (.leaf (.quota 1))))
 (.branch 394
 (.branch 393
 (.leaf (.quota 1))
 (.leaf (.incidence 7)))
 (.branch 395
 (.leaf (.quota 2))
 (.branch 396
 (.leaf (.quota 2))
 (.leaf (.incidence 4))))))))
 (.branch 415
 (.branch 406
 (.branch 401
 (.branch 399
 (.branch 398
 (.leaf (.incidence 4))
 (.leaf (.quota 2)))
 (.branch 400
 (.leaf (.quota 2))
 (.leaf (.incidence 4))))
 (.branch 403
 (.leaf (.incidence 4))
 (.branch 404
 (.leaf (.quota 1))
 (.branch 405
 (.leaf (.incidence 4))
 (.leaf (.quota 2))))))
 (.branch 410
 (.branch 408
 (.branch 407
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 409
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 412
 (.leaf (.quota 2))
 (.branch 413
 (.leaf (.quota 2))
 (.branch 414
 (.leaf (.quota 2))
 (.leaf (.incidence 4)))))))
 (.branch 424
 (.branch 419
 (.branch 417
 (.leaf (.quota 1))
 (.leaf (.incidence 4)))
 (.branch 421
 (.leaf (.incidence 4))
 (.branch 422
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 428
 (.leaf (.incidence 4))
 (.branch 430
 (.branch 429
 (.leaf (.quota 1))
 (.leaf (.incidence 4)))
 (.branch 431
 (.leaf (.incidence 4))
 (.branch 432
 (.leaf (.incidence 4))
 (.leaf (.quota 2))))))))))
 (.branch 505
 (.branch 469
 (.branch 451
 (.branch 442
 (.branch 437
 (.branch 435
 (.leaf (.incidence 4))
 (.branch 436
 (.leaf (.incidence 4))
 (.leaf (.quota 1))))
 (.branch 439
 (.branch 438
 (.leaf (.quota 2))
 (.leaf (.incidence 4)))
 (.branch 440
 (.leaf (.quota 1))
 (.branch 441
 (.leaf (.quota 1))
 (.leaf (.incidence 4))))))
 (.branch 446
 (.branch 444
 (.leaf (.quota 2))
 (.leaf (.incidence 4)))
 (.branch 448
 (.branch 447
 (.leaf (.incidence 4))
 (.leaf (.quota 2)))
 (.leaf (.incidence 4)))))
 (.branch 460
 (.branch 455
 (.branch 453
 (.leaf (.quota 1))
 (.branch 454
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.branch 464
 (.branch 462
 (.branch 461
 (.leaf (.matching Nonrational.OldTerminalMatches.M002.r0160))
 (.leaf (.incidence 9)))
 (.branch 463
 (.leaf (.matching Nonrational.OldTerminalMatches.M002.r0161))
 (.leaf (.incidence 9))))
 (.branch 466
 (.branch 465
 (.leaf (.matching Nonrational.OldTerminalMatches.M002.r0162))
 (.leaf (.matching Nonrational.OldTerminalMatches.M002.r0163)))
 (.branch 467
 (.leaf (.incidence 9))
 (.branch 468
 (.leaf (.incidence 7))
 (.leaf (.matching Nonrational.OldTerminalMatches.M002.r0164))))))))
 (.branch 487
 (.branch 478
 (.branch 473
 (.branch 471
 (.branch 470
 (.leaf (.matching Nonrational.OldTerminalMatches.M002.r0165))
 (.leaf (.matching Nonrational.OldTerminalMatches.M002.r0166)))
 (.branch 472
 (.leaf (.matching Nonrational.OldTerminalMatches.M002.r0167))
 (.leaf (.quota 2))))
 (.branch 475
 (.branch 474
 (.leaf (.incidence 9))
 (.leaf (.matching Nonrational.OldTerminalMatches.M002.r0168)))
 (.branch 476
 (.leaf (.incidence 3))
 (.branch 477
 (.leaf (.quota 1))
 (.leaf (.incidence 3))))))
 (.branch 482
 (.branch 480
 (.branch 479
 (.leaf (.quota 2))
 (.leaf (.incidence 3)))
 (.branch 481
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 484
 (.branch 483
 (.leaf (.matching Nonrational.OldTerminalMatches.M002.r0169))
 (.leaf (.matching Nonrational.OldTerminalMatches.M002.r0170)))
 (.branch 485
 (.leaf (.incidence 8))
 (.branch 486
 (.leaf (.matching Nonrational.OldTerminalMatches.M002.r0171))
 (.leaf (.quota 1)))))))
 (.branch 496
 (.branch 491
 (.branch 489
 (.branch 488
 (.leaf (.quota 1))
 (.leaf (.incidence 9)))
 (.branch 490
 (.leaf (.incidence 8))
 (.leaf (.incidence 7))))
 (.branch 493
 (.branch 492
 (.leaf (.incidence 7))
 (.leaf (.quota 1)))
 (.branch 494
 (.leaf (.incidence 8))
 (.branch 495
 (.leaf (.matching Nonrational.OldTerminalMatches.M002.r0172))
 (.leaf (.quota 2))))))
 (.branch 500
 (.branch 498
 (.branch 497
 (.leaf (.matching Nonrational.OldTerminalMatches.M002.r0173))
 (.leaf (.matching Nonrational.OldTerminalMatches.M002.r0174)))
 (.branch 499
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M002.r0175))))
 (.branch 502
 (.branch 501
 (.leaf (.quota 1))
 (.leaf (.incidence 9)))
 (.branch 503
 (.leaf (.incidence 7))
 (.branch 504
 (.leaf (.incidence 8))
 (.leaf (.incidence 9)))))))))
 (.branch 541
 (.branch 523
 (.branch 514
 (.branch 509
 (.branch 507
 (.branch 506
 (.leaf (.quota 1))
 (.leaf (.incidence 9)))
 (.branch 508
 (.leaf (.incidence 9))
 (.leaf (.quota 1))))
 (.branch 511
 (.branch 510
 (.leaf (.quota 1))
 (.leaf (.incidence 9)))
 (.branch 512
 (.leaf (.incidence 9))
 (.branch 513
 (.leaf (.matching Nonrational.OldTerminalMatches.M002.r0176))
 (.leaf (.matching Nonrational.OldTerminalMatches.M002.r0177))))))
 (.branch 518
 (.branch 516
 (.branch 515
 (.leaf (.matching Nonrational.OldTerminalMatches.M002.r0178))
 (.leaf (.matching Nonrational.OldTerminalMatches.M002.r0179)))
 (.branch 517
 (.leaf (.quota 1))
 (.leaf (.matching Nonrational.OldTerminalMatches.M002.r0180))))
 (.branch 520
 (.branch 519
 (.leaf (.incidence 9))
 (.leaf (.incidence 8)))
 (.branch 521
 (.leaf (.incidence 9))
 (.leaf (.quota 1))))))
 (.branch 532
 (.branch 527
 (.branch 525
 (.branch 524
 (.leaf (.matching Nonrational.OldTerminalMatches.M002.r0181))
 (.leaf (.matching Nonrational.OldTerminalMatches.M002.r0182)))
 (.branch 526
 (.leaf (.matching Nonrational.OldTerminalMatches.M002.r0183))
 (.leaf (.incidence 9))))
 (.branch 529
 (.branch 528
 (.leaf (.matching Nonrational.OldTerminalMatches.M002.r0184))
 (.leaf (.matching Nonrational.OldTerminalMatches.M002.r0185)))
 (.branch 530
 (.leaf (.quota 1))
 (.branch 531
 (.leaf (.matching Nonrational.OldTerminalMatches.M002.r0186))
 (.leaf (.incidence 7))))))
 (.branch 536
 (.branch 534
 (.branch 533
 (.leaf (.matching Nonrational.OldTerminalMatches.M002.r0187))
 (.leaf (.matching Nonrational.OldTerminalMatches.M002.r0188)))
 (.branch 535
 (.leaf (.matching Nonrational.OldTerminalMatches.M002.r0189))
 (.leaf (.matching Nonrational.OldTerminalMatches.M002.r0190))))
 (.branch 538
 (.branch 537
 (.leaf (.quota 1))
 (.leaf (.matching Nonrational.OldTerminalMatches.M002.r0191)))
 (.leaf (.incidence 3))))))
 (.branch 559
 (.branch 550
 (.branch 545
 (.branch 543
 (.leaf (.incidence 3))
 (.leaf (.quota 1)))
 (.branch 547
 (.leaf (.quota 1))
 (.branch 548
 (.leaf (.incidence 4))
 (.branch 549
 (.leaf (.quota 1))
 (.leaf (.incidence 4))))))
 (.branch 554
 (.branch 552
 (.branch 551
 (.leaf (.incidence 4))
 (.leaf (.quota 1)))
 (.branch 553
 (.leaf (.incidence 3))
 (.leaf (.quota 2))))
 (.branch 556
 (.branch 555
 (.leaf (.quota 2))
 (.leaf (.incidence 3)))
 (.branch 557
 (.leaf (.incidence 4))
 (.branch 558
 (.leaf (.incidence 4))
 (.leaf (.quota 1)))))))
 (.branch 568
 (.branch 563
 (.branch 561
 (.branch 560
 (.leaf (.incidence 3))
 (.leaf (.incidence 4)))
 (.branch 562
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 565
 (.leaf (.quota 2))
 (.branch 566
 (.leaf (.quota 1))
 (.branch 567
 (.leaf (.incidence 4))
 (.leaf (.incidence 3))))))
 (.branch 573
 (.branch 570
 (.branch 569
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 571
 (.leaf (.incidence 4))
 (.branch 572
 (.leaf (.incidence 4))
 (.leaf (.quota 1)))))
 (.branch 575
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))))))
def disposition (j : Fin leafCount) := dispositionTable.get j.val
def dispositionTest (i : Nat) : Bool := RawLeafCertificate.check quota
  ((rawLeaves i).map RootedSmallCache.rawCells) (dispositionTable.get i)

end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest15

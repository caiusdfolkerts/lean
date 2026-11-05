module
prelude
public import RootedSubsumedForest0353Data
public import RawLeafCertificate
public import OldTerminalMatches.M011
public import OldTerminalMatches.M012
public import OldTerminalMatches.M013
public import OldTerminalMatches.M014

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0353
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 378
 (.branch 189
 (.branch 94
 (.branch 47
 (.branch 23
 (.branch 11
 (.branch 5
 (.branch 2
 (.leaf (.quota 2))
 (.branch 3
 (.leaf (.quota 2))
 (.branch 4
 (.leaf (.quota 2))
 (.leaf (.incidence 5)))))
 (.branch 8
 (.branch 6
 (.leaf (.incidence 5))
 (.branch 7
 (.leaf (.matching Nonrational.OldTerminalMatches.M011.r0751))
 (.leaf (.matching Nonrational.OldTerminalMatches.M011.r0752))))
 (.branch 9
 (.leaf (.quota 2))
 (.branch 10
 (.leaf (.quota 2))
 (.leaf (.incidence 0))))))
 (.branch 17
 (.branch 14
 (.leaf (.quota 2))
 (.branch 15
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 20
 (.branch 18
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 21
 (.leaf (.quota 2))
 (.branch 22
 (.leaf (.quota 3))
 (.leaf (.quota 2)))))))
 (.branch 35
 (.branch 29
 (.branch 26
 (.branch 24
 (.leaf (.matching Nonrational.OldTerminalMatches.M011.r0753))
 (.branch 25
 (.leaf (.matching Nonrational.OldTerminalMatches.M011.r0754))
 (.leaf (.matching Nonrational.OldTerminalMatches.M011.r0755))))
 (.branch 27
 (.leaf (.quota 2))
 (.branch 28
 (.leaf (.quota 1))
 (.leaf (.matching Nonrational.OldTerminalMatches.M011.r0756)))))
 (.branch 32
 (.branch 30
 (.leaf (.matching Nonrational.OldTerminalMatches.M011.r0757))
 (.branch 31
 (.leaf (.matching Nonrational.OldTerminalMatches.M011.r0758))
 (.leaf (.incidence 4))))
 (.branch 33
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 41
 (.leaf (.quota 2))
 (.branch 44
 (.leaf (.quota 2))
 (.branch 45
 (.leaf (.quota 2))
 (.branch 46
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))))
 (.branch 70
 (.branch 58
 (.leaf (.quota 2))
 (.branch 64
 (.leaf (.quota 2))
 (.branch 67
 (.leaf (.quota 2))
 (.branch 68
 (.leaf (.incidence 0))
 (.branch 69
 (.leaf (.incidence 0))
 (.leaf (.quota 3)))))))
 (.branch 82
 (.branch 76
 (.branch 73
 (.leaf (.quota 2))
 (.branch 74
 (.leaf (.incidence 5))
 (.branch 75
 (.leaf (.matching Nonrational.OldTerminalMatches.M011.r0759))
 (.leaf (.quota 2)))))
 (.branch 79
 (.branch 77
 (.leaf (.incidence 4))
 (.leaf (.quota 2)))
 (.branch 80
 (.leaf (.matching Nonrational.OldTerminalMatches.M011.r0760))
 (.branch 81
 (.leaf (.matching Nonrational.OldTerminalMatches.M011.r0761))
 (.leaf (.matching Nonrational.OldTerminalMatches.M011.r0762))))))
 (.branch 88
 (.branch 85
 (.branch 83
 (.leaf (.matching Nonrational.OldTerminalMatches.M011.r0763))
 (.branch 84
 (.leaf (.matching Nonrational.OldTerminalMatches.M011.r0764))
 (.leaf (.matching Nonrational.OldTerminalMatches.M011.r0765))))
 (.branch 86
 (.leaf (.matching Nonrational.OldTerminalMatches.M011.r0766))
 (.branch 87
 (.leaf (.matching Nonrational.OldTerminalMatches.M011.r0767))
 (.leaf (.matching Nonrational.OldTerminalMatches.M012.r0768)))))
 (.branch 91
 (.branch 89
 (.leaf (.matching Nonrational.OldTerminalMatches.M012.r0769))
 (.branch 90
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M012.r0770))))
 (.branch 92
 (.leaf (.quota 1))
 (.branch 93
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M012.r0771)))))))))
 (.branch 141
 (.branch 117
 (.branch 105
 (.branch 99
 (.branch 96
 (.branch 95
 (.leaf (.matching Nonrational.OldTerminalMatches.M012.r0772))
 (.leaf (.quota 3)))
 (.branch 97
 (.leaf (.quota 3))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.branch 111
 (.branch 108
 (.branch 106
 (.leaf (.quota 2))
 (.branch 107
 (.leaf (.matching Nonrational.OldTerminalMatches.M012.r0773))
 (.leaf (.quota 1))))
 (.branch 109
 (.leaf (.matching Nonrational.OldTerminalMatches.M012.r0774))
 (.branch 110
 (.leaf (.matching Nonrational.OldTerminalMatches.M012.r0775))
 (.leaf (.matching Nonrational.OldTerminalMatches.M012.r0776)))))
 (.branch 114
 (.branch 112
 (.leaf (.matching Nonrational.OldTerminalMatches.M012.r0777))
 (.leaf (.quota 1)))
 (.branch 115
 (.leaf (.quota 2))
 (.branch 116
 (.leaf (.matching Nonrational.OldTerminalMatches.M012.r0778))
 (.leaf (.quota 2)))))))
 (.branch 129
 (.branch 123
 (.branch 120
 (.leaf (.quota 2))
 (.branch 121
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 126
 (.branch 124
 (.leaf (.incidence 5))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.branch 135
 (.branch 132
 (.leaf (.quota 2))
 (.branch 133
 (.leaf (.quota 2))
 (.branch 134
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 138
 (.leaf (.quota 2))
 (.branch 139
 (.leaf (.quota 2))
 (.branch 140
 (.leaf (.quota 2))
 (.leaf (.incidence 5))))))))
 (.branch 165
 (.branch 153
 (.branch 147
 (.branch 144
 (.branch 142
 (.leaf (.quota 2))
 (.branch 143
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M012.r0779))))
 (.branch 145
 (.leaf (.matching Nonrational.OldTerminalMatches.M012.r0780))
 (.branch 146
 (.leaf (.matching Nonrational.OldTerminalMatches.M012.r0781))
 (.leaf (.matching Nonrational.OldTerminalMatches.M012.r0782)))))
 (.branch 150
 (.branch 148
 (.leaf (.matching Nonrational.OldTerminalMatches.M012.r0783))
 (.branch 149
 (.leaf (.matching Nonrational.OldTerminalMatches.M012.r0784))
 (.leaf (.matching Nonrational.OldTerminalMatches.M012.r0785))))
 (.branch 151
 (.leaf (.matching Nonrational.OldTerminalMatches.M012.r0786))
 (.branch 152
 (.leaf (.matching Nonrational.OldTerminalMatches.M012.r0787))
 (.leaf (.matching Nonrational.OldTerminalMatches.M012.r0788))))))
 (.branch 159
 (.leaf (.quota 2))
 (.branch 162
 (.branch 160
 (.leaf (.quota 2))
 (.branch 161
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M012.r0789))))
 (.branch 163
 (.leaf (.matching Nonrational.OldTerminalMatches.M012.r0790))
 (.branch 164
 (.leaf (.matching Nonrational.OldTerminalMatches.M012.r0791))
 (.leaf (.matching Nonrational.OldTerminalMatches.M012.r0792)))))))
 (.branch 177
 (.branch 171
 (.branch 168
 (.branch 166
 (.leaf (.quota 1))
 (.branch 167
 (.leaf (.matching Nonrational.OldTerminalMatches.M012.r0793))
 (.leaf (.matching Nonrational.OldTerminalMatches.M012.r0794))))
 (.branch 169
 (.leaf (.matching Nonrational.OldTerminalMatches.M012.r0795))
 (.branch 170
 (.leaf (.matching Nonrational.OldTerminalMatches.M012.r0796))
 (.leaf (.matching Nonrational.OldTerminalMatches.M012.r0797)))))
 (.branch 174
 (.branch 172
 (.leaf (.matching Nonrational.OldTerminalMatches.M012.r0798))
 (.branch 173
 (.leaf (.matching Nonrational.OldTerminalMatches.M012.r0799))
 (.leaf (.quota 1))))
 (.branch 175
 (.leaf (.matching Nonrational.OldTerminalMatches.M012.r0800))
 (.branch 176
 (.leaf (.matching Nonrational.OldTerminalMatches.M012.r0801))
 (.leaf (.quota 1))))))
 (.branch 183
 (.branch 180
 (.branch 178
 (.leaf (.quota 1))
 (.branch 179
 (.leaf (.matching Nonrational.OldTerminalMatches.M012.r0802))
 (.leaf (.matching Nonrational.OldTerminalMatches.M012.r0803))))
 (.branch 181
 (.leaf (.matching Nonrational.OldTerminalMatches.M012.r0804))
 (.branch 182
 (.leaf (.quota 1))
 (.leaf (.incidence 5)))))
 (.branch 186
 (.branch 184
 (.leaf (.matching Nonrational.OldTerminalMatches.M012.r0805))
 (.branch 185
 (.leaf (.matching Nonrational.OldTerminalMatches.M012.r0806))
 (.leaf (.matching Nonrational.OldTerminalMatches.M012.r0807))))
 (.branch 187
 (.leaf (.matching Nonrational.OldTerminalMatches.M012.r0808))
 (.branch 188
 (.leaf (.matching Nonrational.OldTerminalMatches.M012.r0809))
 (.leaf (.quota 1))))))))))
 (.branch 283
 (.branch 236
 (.branch 212
 (.branch 200
 (.branch 194
 (.branch 191
 (.branch 190
 (.leaf (.matching Nonrational.OldTerminalMatches.M012.r0810))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 197
 (.leaf (.quota 2))
 (.branch 198
 (.leaf (.quota 2))
 (.branch 199
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 206
 (.branch 203
 (.branch 201
 (.leaf (.quota 1))
 (.branch 202
 (.leaf (.matching Nonrational.OldTerminalMatches.M012.r0811))
 (.leaf (.matching Nonrational.OldTerminalMatches.M012.r0812))))
 (.branch 204
 (.leaf (.matching Nonrational.OldTerminalMatches.M012.r0813))
 (.branch 205
 (.leaf (.matching Nonrational.OldTerminalMatches.M012.r0814))
 (.leaf (.quota 1)))))
 (.branch 209
 (.branch 207
 (.leaf (.matching Nonrational.OldTerminalMatches.M012.r0815))
 (.branch 208
 (.leaf (.matching Nonrational.OldTerminalMatches.M012.r0816))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))))
 (.branch 224
 (.branch 218
 (.branch 215
 (.leaf (.quota 2))
 (.branch 216
 (.leaf (.quota 2))
 (.branch 217
 (.leaf (.matching Nonrational.OldTerminalMatches.M012.r0817))
 (.leaf (.quota 1)))))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.branch 259
 (.branch 247
 (.branch 241
 (.branch 238
 (.leaf (.quota 2))
 (.branch 239
 (.leaf (.quota 2))
 (.branch 240
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 271
 (.branch 265
 (.branch 262
 (.leaf (.quota 2))
 (.branch 263
 (.leaf (.quota 1))
 (.branch 264
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.leaf (.quota 2)))
 (.branch 277
 (.branch 274
 (.branch 272
 (.leaf (.quota 1))
 (.branch 273
 (.leaf (.incidence 0))
 (.leaf (.quota 1))))
 (.branch 275
 (.leaf (.incidence 0))
 (.leaf (.quota 2))))
 (.branch 280
 (.branch 278
 (.leaf (.incidence 0))
 (.branch 279
 (.leaf (.quota 2))
 (.leaf (.incidence 0))))
 (.branch 281
 (.leaf (.quota 2))
 (.branch 282
 (.leaf (.incidence 0))
 (.leaf (.quota 2)))))))))
 (.branch 330
 (.branch 306
 (.branch 294
 (.branch 288
 (.branch 285
 (.leaf (.quota 2))
 (.branch 286
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 2)))
 (.branch 300
 (.branch 297
 (.branch 295
 (.leaf (.quota 2))
 (.branch 296
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 303
 (.branch 301
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))))
 (.branch 318
 (.branch 312
 (.branch 309
 (.branch 307
 (.leaf (.quota 2))
 (.branch 308
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M012.r0818))))
 (.branch 310
 (.leaf (.matching Nonrational.OldTerminalMatches.M012.r0819))
 (.branch 311
 (.leaf (.matching Nonrational.OldTerminalMatches.M012.r0820))
 (.leaf (.quota 1)))))
 (.branch 315
 (.branch 313
 (.leaf (.matching Nonrational.OldTerminalMatches.M012.r0821))
 (.branch 314
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 316
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 324
 (.branch 321
 (.branch 319
 (.leaf (.quota 2))
 (.branch 320
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 322
 (.leaf (.quota 1))
 (.branch 323
 (.leaf (.matching Nonrational.OldTerminalMatches.M012.r0822))
 (.leaf (.matching Nonrational.OldTerminalMatches.M012.r0823)))))
 (.branch 327
 (.branch 325
 (.leaf (.matching Nonrational.OldTerminalMatches.M012.r0824))
 (.branch 326
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M012.r0825))))
 (.branch 328
 (.leaf (.matching Nonrational.OldTerminalMatches.M012.r0826))
 (.leaf (.quota 2)))))))
 (.branch 354
 (.branch 342
 (.branch 336
 (.branch 333
 (.branch 331
 (.leaf (.matching Nonrational.OldTerminalMatches.M012.r0827))
 (.leaf (.quota 2)))
 (.branch 334
 (.leaf (.quota 2))
 (.branch 335
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 339
 (.branch 337
 (.leaf (.quota 2))
 (.branch 338
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 340
 (.leaf (.matching Nonrational.OldTerminalMatches.M012.r0828))
 (.leaf (.quota 2)))))
 (.branch 348
 (.branch 345
 (.branch 343
 (.leaf (.quota 2))
 (.branch 344
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M012.r0829))))
 (.leaf (.quota 2)))
 (.branch 351
 (.branch 349
 (.leaf (.quota 1))
 (.branch 350
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M012.r0830))))
 (.branch 352
 (.leaf (.matching Nonrational.OldTerminalMatches.M012.r0831))
 (.branch 353
 (.leaf (.matching Nonrational.OldTerminalMatches.M013.r0832))
 (.leaf (.matching Nonrational.OldTerminalMatches.M013.r0833)))))))
 (.branch 366
 (.branch 360
 (.branch 357
 (.branch 355
 (.leaf (.matching Nonrational.OldTerminalMatches.M013.r0834))
 (.branch 356
 (.leaf (.matching Nonrational.OldTerminalMatches.M013.r0835))
 (.leaf (.matching Nonrational.OldTerminalMatches.M013.r0836))))
 (.leaf (.quota 1)))
 (.branch 363
 (.branch 361
 (.leaf (.matching Nonrational.OldTerminalMatches.M013.r0837))
 (.branch 362
 (.leaf (.matching Nonrational.OldTerminalMatches.M013.r0838))
 (.leaf (.matching Nonrational.OldTerminalMatches.M013.r0839))))
 (.branch 364
 (.leaf (.quota 1))
 (.branch 365
 (.leaf (.matching Nonrational.OldTerminalMatches.M013.r0840))
 (.leaf (.matching Nonrational.OldTerminalMatches.M013.r0841))))))
 (.branch 372
 (.branch 369
 (.branch 367
 (.leaf (.matching Nonrational.OldTerminalMatches.M013.r0842))
 (.branch 368
 (.leaf (.matching Nonrational.OldTerminalMatches.M013.r0843))
 (.leaf (.matching Nonrational.OldTerminalMatches.M013.r0844))))
 (.branch 370
 (.leaf (.matching Nonrational.OldTerminalMatches.M013.r0845))
 (.branch 371
 (.leaf (.matching Nonrational.OldTerminalMatches.M013.r0846))
 (.leaf (.quota 2)))))
 (.branch 375
 (.branch 373
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))))))))
 (.branch 567
 (.branch 472
 (.branch 425
 (.branch 401
 (.branch 389
 (.branch 383
 (.branch 380
 (.branch 379
 (.leaf (.quota 2))
 (.leaf (.incidence 0)))
 (.branch 381
 (.leaf (.quota 1))
 (.branch 382
 (.leaf (.quota 2))
 (.leaf (.incidence 0)))))
 (.branch 386
 (.branch 384
 (.leaf (.quota 2))
 (.branch 385
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 387
 (.leaf (.quota 2))
 (.branch 388
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 395
 (.branch 392
 (.branch 390
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 393
 (.leaf (.quota 3))
 (.leaf (.quota 2))))
 (.branch 398
 (.branch 396
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 399
 (.leaf (.quota 2))
 (.branch 400
 (.leaf (.incidence 0))
 (.leaf (.quota 2)))))))
 (.branch 413
 (.branch 407
 (.branch 404
 (.branch 402
 (.leaf (.quota 2))
 (.branch 403
 (.leaf (.incidence 0))
 (.leaf (.quota 1))))
 (.leaf (.quota 2)))
 (.branch 410
 (.branch 408
 (.leaf (.quota 1))
 (.branch 409
 (.leaf (.incidence 0))
 (.leaf (.quota 1))))
 (.branch 411
 (.leaf (.quota 1))
 (.leaf (.incidence 0)))))
 (.branch 419
 (.branch 416
 (.branch 414
 (.leaf (.incidence 0))
 (.branch 415
 (.leaf (.incidence 0))
 (.leaf (.quota 2))))
 (.branch 417
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 422
 (.branch 420
 (.leaf (.quota 1))
 (.branch 421
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 423
 (.leaf (.quota 2))
 (.branch 424
 (.leaf (.matching Nonrational.OldTerminalMatches.M013.r0847))
 (.leaf (.quota 2))))))))
 (.branch 448
 (.branch 436
 (.branch 430
 (.branch 427
 (.branch 426
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M013.r0848)))
 (.branch 428
 (.leaf (.matching Nonrational.OldTerminalMatches.M013.r0849))
 (.branch 429
 (.leaf (.matching Nonrational.OldTerminalMatches.M013.r0850))
 (.leaf (.matching Nonrational.OldTerminalMatches.M013.r0851)))))
 (.branch 433
 (.branch 431
 (.leaf (.matching Nonrational.OldTerminalMatches.M013.r0852))
 (.branch 432
 (.leaf (.matching Nonrational.OldTerminalMatches.M013.r0853))
 (.leaf (.incidence 4))))
 (.branch 434
 (.leaf (.incidence 4))
 (.branch 435
 (.leaf (.matching Nonrational.OldTerminalMatches.M013.r0854))
 (.leaf (.matching Nonrational.OldTerminalMatches.M013.r0855))))))
 (.branch 442
 (.branch 439
 (.branch 437
 (.leaf (.matching Nonrational.OldTerminalMatches.M013.r0856))
 (.branch 438
 (.leaf (.matching Nonrational.OldTerminalMatches.M013.r0857))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.branch 460
 (.branch 454
 (.branch 451
 (.branch 449
 (.leaf (.incidence 5))
 (.branch 450
 (.leaf (.incidence 5))
 (.leaf (.quota 2))))
 (.branch 452
 (.leaf (.matching Nonrational.OldTerminalMatches.M013.r0858))
 (.branch 453
 (.leaf (.matching Nonrational.OldTerminalMatches.M013.r0859))
 (.leaf (.quota 2)))))
 (.branch 457
 (.branch 455
 (.leaf (.quota 2))
 (.branch 456
 (.leaf (.matching Nonrational.OldTerminalMatches.M013.r0860))
 (.leaf (.matching Nonrational.OldTerminalMatches.M013.r0861))))
 (.branch 458
 (.leaf (.quota 2))
 (.branch 459
 (.leaf (.matching Nonrational.OldTerminalMatches.M013.r0862))
 (.leaf (.matching Nonrational.OldTerminalMatches.M013.r0863))))))
 (.branch 466
 (.branch 463
 (.branch 461
 (.leaf (.matching Nonrational.OldTerminalMatches.M013.r0864))
 (.leaf (.quota 2)))
 (.branch 464
 (.leaf (.incidence 4))
 (.branch 465
 (.leaf (.quota 2))
 (.leaf (.incidence 4)))))
 (.branch 469
 (.branch 467
 (.leaf (.matching Nonrational.OldTerminalMatches.M013.r0865))
 (.branch 468
 (.leaf (.quota 1))
 (.leaf (.matching Nonrational.OldTerminalMatches.M013.r0866))))
 (.branch 470
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))))
 (.branch 519
 (.branch 495
 (.branch 483
 (.branch 477
 (.branch 474
 (.branch 473
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 475
 (.leaf (.quota 2))
 (.branch 476
 (.leaf (.quota 1))
 (.leaf (.matching Nonrational.OldTerminalMatches.M013.r0867)))))
 (.branch 480
 (.branch 478
 (.leaf (.matching Nonrational.OldTerminalMatches.M013.r0868))
 (.branch 479
 (.leaf (.matching Nonrational.OldTerminalMatches.M013.r0869))
 (.leaf (.quota 2))))
 (.branch 481
 (.leaf (.quota 2))
 (.branch 482
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 489
 (.branch 486
 (.branch 484
 (.leaf (.quota 2))
 (.branch 485
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M013.r0870))))
 (.branch 487
 (.leaf (.matching Nonrational.OldTerminalMatches.M013.r0871))
 (.branch 488
 (.leaf (.quota 2))
 (.leaf (.incidence 5)))))
 (.branch 492
 (.leaf (.incidence 5))
 (.branch 493
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 507
 (.branch 501
 (.branch 498
 (.branch 496
 (.leaf (.quota 2))
 (.branch 497
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 499
 (.leaf (.quota 2))
 (.branch 500
 (.leaf (.incidence 4))
 (.leaf (.quota 2)))))
 (.branch 504
 (.leaf (.incidence 5))
 (.branch 505
 (.leaf (.incidence 5))
 (.leaf (.incidence 4)))))
 (.branch 513
 (.branch 510
 (.leaf (.incidence 4))
 (.branch 511
 (.leaf (.incidence 4))
 (.branch 512
 (.leaf (.incidence 4))
 (.leaf (.quota 2)))))
 (.branch 516
 (.leaf (.incidence 5))
 (.branch 517
 (.leaf (.incidence 5))
 (.leaf (.quota 2)))))))
 (.branch 543
 (.branch 531
 (.branch 525
 (.leaf (.quota 2))
 (.branch 528
 (.branch 526
 (.leaf (.quota 1))
 (.branch 527
 (.leaf (.matching Nonrational.OldTerminalMatches.M013.r0872))
 (.leaf (.matching Nonrational.OldTerminalMatches.M013.r0873))))
 (.leaf (.quota 2))))
 (.branch 537
 (.branch 534
 (.branch 532
 (.leaf .euler)
 (.branch 533
 (.leaf (.incidence 9))
 (.leaf (.quota 2))))
 (.branch 535
 (.leaf (.matching Nonrational.OldTerminalMatches.M013.r0874))
 (.branch 536
 (.leaf (.matching Nonrational.OldTerminalMatches.M013.r0875))
 (.leaf (.quota 2)))))
 (.branch 540
 (.branch 538
 (.leaf (.quota 2))
 (.branch 539
 (.leaf (.matching Nonrational.OldTerminalMatches.M013.r0876))
 (.leaf (.quota 2))))
 (.branch 541
 (.leaf (.quota 2))
 (.branch 542
 (.leaf (.matching Nonrational.OldTerminalMatches.M013.r0877))
 (.leaf (.quota 2)))))))
 (.branch 555
 (.branch 549
 (.branch 546
 (.leaf (.quota 2))
 (.branch 547
 (.leaf (.quota 2))
 (.leaf .euler)))
 (.leaf (.quota 2)))
 (.branch 561
 (.branch 558
 (.branch 556
 (.leaf (.quota 2))
 (.branch 557
 (.leaf .euler)
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.branch 564
 (.branch 562
 (.leaf .euler)
 (.branch 563
 (.leaf .euler)
 (.leaf (.matching Nonrational.OldTerminalMatches.M013.r0878))))
 (.branch 565
 (.leaf (.matching Nonrational.OldTerminalMatches.M013.r0879))
 (.leaf .euler))))))))
 (.branch 661
 (.branch 614
 (.branch 590
 (.branch 578
 (.branch 572
 (.branch 569
 (.branch 568
 (.leaf (.matching Nonrational.OldTerminalMatches.M013.r0880))
 (.leaf (.matching Nonrational.OldTerminalMatches.M013.r0881)))
 (.branch 570
 (.leaf (.incidence 7))
 (.branch 571
 (.leaf .euler)
 (.leaf (.incidence 8)))))
 (.branch 575
 (.branch 573
 (.leaf .euler)
 (.branch 574
 (.leaf .euler)
 (.leaf (.incidence 8))))
 (.branch 576
 (.leaf (.incidence 8))
 (.leaf (.incidence 9)))))
 (.branch 584
 (.branch 581
 (.branch 579
 (.leaf (.incidence 7))
 (.leaf .euler))
 (.branch 582
 (.leaf .euler)
 (.branch 583
 (.leaf .euler)
 (.leaf (.matching Nonrational.OldTerminalMatches.M013.r0882)))))
 (.branch 587
 (.branch 585
 (.leaf (.matching Nonrational.OldTerminalMatches.M013.r0883))
 (.branch 586
 (.leaf (.matching Nonrational.OldTerminalMatches.M013.r0884))
 (.leaf (.matching Nonrational.OldTerminalMatches.M013.r0885))))
 (.branch 588
 (.leaf (.matching Nonrational.OldTerminalMatches.M013.r0886))
 (.branch 589
 (.leaf (.matching Nonrational.OldTerminalMatches.M013.r0887))
 (.leaf (.matching Nonrational.OldTerminalMatches.M013.r0888)))))))
 (.branch 602
 (.branch 596
 (.branch 593
 (.branch 591
 (.leaf (.matching Nonrational.OldTerminalMatches.M013.r0889))
 (.branch 592
 (.leaf (.matching Nonrational.OldTerminalMatches.M013.r0890))
 (.leaf (.matching Nonrational.OldTerminalMatches.M013.r0891))))
 (.branch 594
 (.leaf (.matching Nonrational.OldTerminalMatches.M013.r0892))
 (.branch 595
 (.leaf (.matching Nonrational.OldTerminalMatches.M013.r0893))
 (.leaf (.matching Nonrational.OldTerminalMatches.M013.r0894)))))
 (.branch 599
 (.branch 597
 (.leaf (.matching Nonrational.OldTerminalMatches.M013.r0895))
 (.branch 598
 (.leaf (.matching Nonrational.OldTerminalMatches.M014.r0896))
 (.leaf (.matching Nonrational.OldTerminalMatches.M014.r0897))))
 (.branch 600
 (.leaf (.matching Nonrational.OldTerminalMatches.M014.r0898))
 (.branch 601
 (.leaf (.matching Nonrational.OldTerminalMatches.M014.r0899))
 (.leaf (.matching Nonrational.OldTerminalMatches.M014.r0900))))))
 (.branch 608
 (.branch 605
 (.branch 603
 (.leaf (.matching Nonrational.OldTerminalMatches.M014.r0901))
 (.branch 604
 (.leaf (.matching Nonrational.OldTerminalMatches.M014.r0902))
 (.leaf (.matching Nonrational.OldTerminalMatches.M014.r0903))))
 (.branch 606
 (.leaf (.matching Nonrational.OldTerminalMatches.M014.r0904))
 (.branch 607
 (.leaf (.matching Nonrational.OldTerminalMatches.M014.r0905))
 (.leaf (.matching Nonrational.OldTerminalMatches.M014.r0906)))))
 (.branch 611
 (.branch 609
 (.leaf (.quota 2))
 (.branch 610
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M014.r0907))))
 (.branch 612
 (.leaf (.quota 1))
 (.branch 613
 (.leaf (.matching Nonrational.OldTerminalMatches.M014.r0908))
 (.leaf (.matching Nonrational.OldTerminalMatches.M014.r0909))))))))
 (.branch 637
 (.branch 625
 (.branch 619
 (.branch 616
 (.branch 615
 (.leaf (.matching Nonrational.OldTerminalMatches.M014.r0910))
 (.leaf (.matching Nonrational.OldTerminalMatches.M014.r0911)))
 (.branch 617
 (.leaf (.matching Nonrational.OldTerminalMatches.M014.r0912))
 (.branch 618
 (.leaf (.matching Nonrational.OldTerminalMatches.M014.r0913))
 (.leaf (.matching Nonrational.OldTerminalMatches.M014.r0914)))))
 (.branch 622
 (.branch 620
 (.leaf (.matching Nonrational.OldTerminalMatches.M014.r0915))
 (.leaf (.quota 1)))
 (.branch 623
 (.leaf (.matching Nonrational.OldTerminalMatches.M014.r0916))
 (.branch 624
 (.leaf (.matching Nonrational.OldTerminalMatches.M014.r0917))
 (.leaf (.matching Nonrational.OldTerminalMatches.M014.r0918))))))
 (.branch 631
 (.branch 628
 (.branch 626
 (.leaf (.matching Nonrational.OldTerminalMatches.M014.r0919))
 (.branch 627
 (.leaf (.matching Nonrational.OldTerminalMatches.M014.r0920))
 (.leaf (.quota 1))))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.branch 649
 (.branch 643
 (.branch 640
 (.leaf (.quota 2))
 (.branch 641
 (.leaf (.quota 2))
 (.branch 642
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 646
 (.leaf (.quota 2))
 (.branch 647
 (.leaf (.quota 2))
 (.branch 648
 (.leaf (.quota 2))
 (.leaf (.incidence 0))))))
 (.branch 655
 (.branch 652
 (.branch 650
 (.leaf (.incidence 0))
 (.leaf (.quota 2)))
 (.branch 653
 (.leaf (.quota 2))
 (.branch 654
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 658
 (.branch 656
 (.leaf (.quota 2))
 (.branch 657
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 2)))))))
 (.branch 708
 (.branch 684
 (.branch 672
 (.branch 666
 (.branch 663
 (.branch 662
 (.leaf (.quota 1))
 (.leaf (.incidence 0)))
 (.leaf (.incidence 0)))
 (.branch 669
 (.branch 667
 (.leaf (.incidence 0))
 (.branch 668
 (.leaf (.incidence 0))
 (.leaf (.matching Nonrational.OldTerminalMatches.M014.r0921))))
 (.branch 670
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 678
 (.branch 675
 (.branch 673
 (.leaf (.matching Nonrational.OldTerminalMatches.M014.r0922))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 681
 (.leaf (.quota 2))
 (.branch 682
 (.leaf (.quota 2))
 (.branch 683
 (.leaf (.matching Nonrational.OldTerminalMatches.M014.r0923))
 (.leaf (.matching Nonrational.OldTerminalMatches.M014.r0924)))))))
 (.branch 696
 (.branch 690
 (.branch 687
 (.branch 685
 (.leaf (.quota 2))
 (.branch 686
 (.leaf (.matching Nonrational.OldTerminalMatches.M014.r0925))
 (.leaf (.matching Nonrational.OldTerminalMatches.M014.r0926))))
 (.leaf (.quota 2)))
 (.branch 693
 (.leaf (.quota 2))
 (.branch 694
 (.leaf (.quota 2))
 (.branch 695
 (.leaf (.matching Nonrational.OldTerminalMatches.M014.r0927))
 (.leaf (.quota 1))))))
 (.branch 702
 (.branch 699
 (.branch 697
 (.leaf (.quota 1))
 (.branch 698
 (.leaf (.matching Nonrational.OldTerminalMatches.M014.r0928))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.branch 705
 (.branch 703
 (.leaf (.quota 2))
 (.branch 704
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 2))))))
 (.branch 732
 (.branch 720
 (.branch 714
 (.branch 711
 (.branch 709
 (.leaf (.matching Nonrational.OldTerminalMatches.M014.r0929))
 (.branch 710
 (.leaf (.matching Nonrational.OldTerminalMatches.M014.r0930))
 (.leaf (.quota 2))))
 (.branch 712
 (.leaf (.matching Nonrational.OldTerminalMatches.M014.r0931))
 (.branch 713
 (.leaf (.matching Nonrational.OldTerminalMatches.M014.r0932))
 (.leaf (.matching Nonrational.OldTerminalMatches.M014.r0933)))))
 (.branch 717
 (.branch 715
 (.leaf (.matching Nonrational.OldTerminalMatches.M014.r0934))
 (.leaf (.quota 2)))
 (.branch 718
 (.leaf (.quota 1))
 (.branch 719
 (.leaf (.matching Nonrational.OldTerminalMatches.M014.r0935))
 (.leaf (.quota 1))))))
 (.branch 726
 (.branch 723
 (.branch 721
 (.leaf (.quota 1))
 (.branch 722
 (.leaf (.matching Nonrational.OldTerminalMatches.M014.r0936))
 (.leaf (.quota 2))))
 (.branch 724
 (.leaf (.quota 2))
 (.branch 725
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 729
 (.branch 727
 (.leaf (.quota 2))
 (.branch 728
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M014.r0937))))
 (.branch 730
 (.leaf (.matching Nonrational.OldTerminalMatches.M014.r0938))
 (.branch 731
 (.leaf (.matching Nonrational.OldTerminalMatches.M014.r0939))
 (.leaf (.matching Nonrational.OldTerminalMatches.M014.r0940)))))))
 (.branch 744
 (.branch 738
 (.branch 735
 (.branch 733
 (.leaf (.matching Nonrational.OldTerminalMatches.M014.r0941))
 (.branch 734
 (.leaf (.matching Nonrational.OldTerminalMatches.M014.r0942))
 (.leaf (.quota 2))))
 (.branch 736
 (.leaf (.quota 1))
 (.leaf (.incidence 5))))
 (.branch 741
 (.branch 739
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 742
 (.leaf (.quota 2))
 (.branch 743
 (.leaf (.matching Nonrational.OldTerminalMatches.M014.r0943))
 (.leaf (.matching Nonrational.OldTerminalMatches.M014.r0944))))))
 (.branch 750
 (.branch 747
 (.branch 745
 (.leaf (.matching Nonrational.OldTerminalMatches.M014.r0945))
 (.branch 746
 (.leaf (.matching Nonrational.OldTerminalMatches.M014.r0946))
 (.leaf (.matching Nonrational.OldTerminalMatches.M014.r0947))))
 (.leaf (.quota 2)))
 (.branch 753
 (.branch 751
 (.leaf (.quota 2))
 (.branch 752
 (.leaf (.quota 1))
 (.leaf (.matching Nonrational.OldTerminalMatches.M014.r0948))))
 (.branch 754
 (.leaf (.quota 2))
 (.branch 755
 (.leaf (.matching Nonrational.OldTerminalMatches.M014.r0949))
 (.leaf (.matching Nonrational.OldTerminalMatches.M014.r0950))))))))))))
def disposition (j : Fin leafCount) := dispositionTable.get j.val
def dispositionTest (i : Nat) : Bool := RawLeafCertificate.check quota
  ((rawLeaves i).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) (dispositionTable.get i)

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0353

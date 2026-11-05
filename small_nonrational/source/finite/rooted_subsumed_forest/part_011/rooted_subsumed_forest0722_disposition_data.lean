module
prelude
public import RootedSubsumedForest0722Data
public import RawLeafCertificate
public import OldTerminalMatches.M020
public import OldTerminalMatches.M021
public import OldTerminalMatches.M022

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0722
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 322
 (.branch 161
 (.branch 80
 (.branch 40
 (.branch 20
 (.branch 10
 (.branch 5
 (.leaf (.quota 2))
 (.branch 7
 (.leaf (.quota 2))
 (.branch 8
 (.leaf (.quota 2))
 (.branch 9
 (.leaf (.matching Nonrational.OldTerminalMatches.M020.r1318))
 (.leaf (.quota 2))))))
 (.branch 15
 (.leaf (.quota 2))
 (.branch 17
 (.branch 16
 (.leaf (.matching Nonrational.OldTerminalMatches.M020.r1319))
 (.leaf (.matching Nonrational.OldTerminalMatches.M020.r1320)))
 (.branch 18
 (.leaf (.matching Nonrational.OldTerminalMatches.M020.r1321))
 (.branch 19
 (.leaf (.matching Nonrational.OldTerminalMatches.M020.r1322))
 (.leaf (.quota 2)))))))
 (.branch 30
 (.branch 25
 (.branch 22
 (.leaf (.quota 2))
 (.branch 23
 (.leaf (.matching Nonrational.OldTerminalMatches.M020.r1323))
 (.leaf (.quota 2))))
 (.branch 27
 (.branch 26
 (.leaf (.matching Nonrational.OldTerminalMatches.M020.r1324))
 (.leaf (.matching Nonrational.OldTerminalMatches.M020.r1325)))
 (.branch 28
 (.leaf (.matching Nonrational.OldTerminalMatches.M020.r1326))
 (.branch 29
 (.leaf (.matching Nonrational.OldTerminalMatches.M020.r1327))
 (.leaf (.quota 2))))))
 (.branch 35
 (.branch 32
 (.branch 31
 (.leaf (.matching Nonrational.OldTerminalMatches.M020.r1328))
 (.leaf (.matching Nonrational.OldTerminalMatches.M020.r1329)))
 (.branch 33
 (.leaf (.quota 2))
 (.branch 34
 (.leaf (.matching Nonrational.OldTerminalMatches.M020.r1330))
 (.leaf (.quota 2)))))
 (.branch 37
 (.leaf (.quota 2))
 (.branch 38
 (.leaf (.matching Nonrational.OldTerminalMatches.M020.r1331))
 (.branch 39
 (.leaf (.matching Nonrational.OldTerminalMatches.M020.r1332))
 (.leaf (.quota 2))))))))
 (.branch 60
 (.branch 50
 (.branch 45
 (.branch 42
 (.branch 41
 (.leaf (.matching Nonrational.OldTerminalMatches.M020.r1333))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 70
 (.branch 65
 (.branch 62
 (.leaf (.quota 2))
 (.branch 63
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.branch 75
 (.branch 72
 (.branch 71
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M020.r1334)))
 (.branch 73
 (.leaf (.incidence 4))
 (.leaf (.quota 2))))
 (.branch 77
 (.branch 76
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 78
 (.leaf (.matching Nonrational.OldTerminalMatches.M020.r1335))
 (.branch 79
 (.leaf (.incidence 4))
 (.leaf (.matching Nonrational.OldTerminalMatches.M020.r1336)))))))))
 (.branch 120
 (.branch 100
 (.branch 90
 (.branch 85
 (.branch 82
 (.branch 81
 (.leaf (.matching Nonrational.OldTerminalMatches.M020.r1337))
 (.leaf (.quota 2)))
 (.branch 83
 (.leaf (.matching Nonrational.OldTerminalMatches.M020.r1338))
 (.branch 84
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M020.r1339)))))
 (.branch 87
 (.branch 86
 (.leaf (.matching Nonrational.OldTerminalMatches.M020.r1340))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.branch 95
 (.branch 92
 (.branch 91
 (.leaf (.matching Nonrational.OldTerminalMatches.M020.r1341))
 (.leaf (.matching Nonrational.OldTerminalMatches.M020.r1342)))
 (.branch 93
 (.leaf (.matching Nonrational.OldTerminalMatches.M020.r1343))
 (.branch 94
 (.leaf (.matching Nonrational.OldTerminalMatches.M021.r1344))
 (.leaf (.matching Nonrational.OldTerminalMatches.M021.r1345)))))
 (.branch 97
 (.branch 96
 (.leaf (.matching Nonrational.OldTerminalMatches.M021.r1346))
 (.leaf (.quota 2)))
 (.branch 98
 (.leaf (.matching Nonrational.OldTerminalMatches.M021.r1347))
 (.leaf (.quota 2))))))
 (.branch 110
 (.branch 105
 (.branch 102
 (.leaf (.quota 2))
 (.branch 103
 (.leaf (.matching Nonrational.OldTerminalMatches.M021.r1348))
 (.leaf (.quota 1))))
 (.branch 107
 (.branch 106
 (.leaf (.matching Nonrational.OldTerminalMatches.M021.r1349))
 (.leaf (.matching Nonrational.OldTerminalMatches.M021.r1350)))
 (.branch 108
 (.leaf (.matching Nonrational.OldTerminalMatches.M021.r1351))
 (.branch 109
 (.leaf (.matching Nonrational.OldTerminalMatches.M021.r1352))
 (.leaf (.quota 1))))))
 (.branch 115
 (.branch 112
 (.leaf (.quota 2))
 (.branch 113
 (.leaf (.quota 2))
 (.branch 114
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 117
 (.branch 116
 (.leaf (.matching Nonrational.OldTerminalMatches.M021.r1353))
 (.leaf (.quota 1)))
 (.branch 118
 (.leaf (.quota 1))
 (.branch 119
 (.leaf (.matching Nonrational.OldTerminalMatches.M021.r1354))
 (.leaf (.matching Nonrational.OldTerminalMatches.M021.r1355))))))))
 (.branch 140
 (.branch 130
 (.branch 125
 (.branch 122
 (.branch 121
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 123
 (.leaf (.quota 2))
 (.branch 124
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M021.r1356)))))
 (.branch 127
 (.branch 126
 (.leaf (.matching Nonrational.OldTerminalMatches.M021.r1357))
 (.leaf (.quota 2)))
 (.branch 128
 (.leaf (.matching Nonrational.OldTerminalMatches.M021.r1358))
 (.branch 129
 (.leaf (.matching Nonrational.OldTerminalMatches.M021.r1359))
 (.leaf (.quota 2))))))
 (.branch 135
 (.branch 132
 (.branch 131
 (.leaf (.matching Nonrational.OldTerminalMatches.M021.r1360))
 (.leaf (.matching Nonrational.OldTerminalMatches.M021.r1361)))
 (.branch 133
 (.leaf (.quota 2))
 (.branch 134
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 137
 (.branch 136
 (.leaf (.matching Nonrational.OldTerminalMatches.M021.r1362))
 (.leaf (.matching Nonrational.OldTerminalMatches.M021.r1363)))
 (.branch 138
 (.leaf (.quota 2))
 (.branch 139
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M021.r1364)))))))
 (.branch 150
 (.branch 145
 (.branch 142
 (.leaf (.quota 1))
 (.branch 143
 (.leaf (.matching Nonrational.OldTerminalMatches.M021.r1365))
 (.branch 144
 (.leaf (.matching Nonrational.OldTerminalMatches.M021.r1366))
 (.leaf (.matching Nonrational.OldTerminalMatches.M021.r1367)))))
 (.branch 147
 (.branch 146
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M021.r1368)))
 (.branch 148
 (.leaf (.matching Nonrational.OldTerminalMatches.M021.r1369))
 (.leaf (.quota 1)))))
 (.branch 155
 (.branch 152
 (.branch 151
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))
 (.branch 158
 (.branch 156
 (.leaf (.quota 2))
 (.branch 157
 (.leaf (.matching Nonrational.OldTerminalMatches.M021.r1370))
 (.leaf (.matching Nonrational.OldTerminalMatches.M021.r1371))))
 (.branch 159
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))))))
 (.branch 241
 (.branch 201
 (.branch 181
 (.branch 171
 (.branch 166
 (.leaf (.quota 2))
 (.branch 168
 (.leaf (.quota 2))
 (.branch 169
 (.leaf (.quota 2))
 (.branch 170
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 176
 (.branch 173
 (.leaf (.quota 2))
 (.branch 174
 (.leaf (.quota 1))
 (.branch 175
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 178
 (.branch 177
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 179
 (.leaf (.matching Nonrational.OldTerminalMatches.M021.r1372))
 (.leaf (.quota 1))))))
 (.branch 191
 (.branch 186
 (.branch 183
 (.branch 182
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M021.r1373)))
 (.branch 184
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 188
 (.leaf (.quota 2))
 (.branch 189
 (.leaf (.quota 2))
 (.branch 190
 (.leaf (.matching Nonrational.OldTerminalMatches.M021.r1374))
 (.leaf (.quota 2))))))
 (.branch 196
 (.branch 193
 (.branch 192
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M021.r1375)))
 (.branch 194
 (.leaf (.matching Nonrational.OldTerminalMatches.M021.r1376))
 (.leaf (.quota 2))))
 (.branch 198
 (.leaf (.quota 2))
 (.branch 199
 (.leaf (.quota 2))
 (.branch 200
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))))
 (.branch 221
 (.branch 211
 (.branch 206
 (.branch 203
 (.leaf (.quota 1))
 (.branch 204
 (.leaf (.matching Nonrational.OldTerminalMatches.M021.r1377))
 (.branch 205
 (.leaf (.matching Nonrational.OldTerminalMatches.M021.r1378))
 (.leaf (.matching Nonrational.OldTerminalMatches.M021.r1379)))))
 (.branch 208
 (.branch 207
 (.leaf (.matching Nonrational.OldTerminalMatches.M021.r1380))
 (.leaf (.quota 1)))
 (.branch 209
 (.leaf (.quota 1))
 (.branch 210
 (.leaf (.matching Nonrational.OldTerminalMatches.M021.r1381))
 (.leaf (.quota 2))))))
 (.branch 216
 (.branch 213
 (.branch 212
 (.leaf (.matching Nonrational.OldTerminalMatches.M021.r1382))
 (.leaf (.matching Nonrational.OldTerminalMatches.M021.r1383)))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.branch 231
 (.branch 226
 (.branch 223
 (.branch 222
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 236
 (.leaf (.quota 2))
 (.branch 238
 (.branch 237
 (.leaf (.quota 1))
 (.leaf (.matching Nonrational.OldTerminalMatches.M021.r1384)))
 (.leaf (.quota 2)))))))
 (.branch 281
 (.branch 261
 (.branch 251
 (.branch 246
 (.branch 243
 (.leaf (.quota 2))
 (.branch 244
 (.leaf (.quota 2))
 (.branch 245
 (.leaf (.matching Nonrational.OldTerminalMatches.M021.r1385))
 (.leaf (.quota 2)))))
 (.branch 248
 (.branch 247
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 249
 (.leaf (.incidence 4))
 (.leaf (.quota 2)))))
 (.branch 256
 (.branch 253
 (.leaf (.quota 2))
 (.branch 254
 (.leaf (.quota 2))
 (.branch 255
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 258
 (.branch 257
 (.leaf (.quota 1))
 (.leaf (.matching Nonrational.OldTerminalMatches.M021.r1386)))
 (.branch 259
 (.leaf (.matching Nonrational.OldTerminalMatches.M021.r1387))
 (.branch 260
 (.leaf (.matching Nonrational.OldTerminalMatches.M021.r1388))
 (.leaf (.quota 1)))))))
 (.branch 271
 (.branch 266
 (.branch 263
 (.branch 262
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M021.r1389)))
 (.leaf (.quota 2)))
 (.branch 268
 (.leaf (.quota 1))
 (.branch 269
 (.leaf (.quota 1))
 (.branch 270
 (.leaf (.matching Nonrational.OldTerminalMatches.M021.r1390))
 (.leaf (.matching Nonrational.OldTerminalMatches.M021.r1391))))))
 (.branch 276
 (.branch 273
 (.branch 272
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M021.r1392)))
 (.branch 274
 (.leaf (.matching Nonrational.OldTerminalMatches.M021.r1393))
 (.leaf (.quota 1))))
 (.branch 278
 (.branch 277
 (.leaf (.matching Nonrational.OldTerminalMatches.M021.r1394))
 (.leaf (.matching Nonrational.OldTerminalMatches.M021.r1395)))
 (.branch 279
 (.leaf (.matching Nonrational.OldTerminalMatches.M021.r1396))
 (.branch 280
 (.leaf (.matching Nonrational.OldTerminalMatches.M021.r1397))
 (.leaf (.quota 1))))))))
 (.branch 301
 (.branch 291
 (.branch 286
 (.branch 283
 (.branch 282
 (.leaf (.matching Nonrational.OldTerminalMatches.M021.r1398))
 (.leaf (.matching Nonrational.OldTerminalMatches.M021.r1399)))
 (.branch 284
 (.leaf (.matching Nonrational.OldTerminalMatches.M021.r1400))
 (.branch 285
 (.leaf (.quota 1))
 (.leaf (.matching Nonrational.OldTerminalMatches.M021.r1401)))))
 (.branch 288
 (.branch 287
 (.leaf (.matching Nonrational.OldTerminalMatches.M021.r1402))
 (.leaf (.quota 1)))
 (.branch 289
 (.leaf (.matching Nonrational.OldTerminalMatches.M021.r1403))
 (.branch 290
 (.leaf (.matching Nonrational.OldTerminalMatches.M021.r1404))
 (.leaf (.matching Nonrational.OldTerminalMatches.M021.r1405))))))
 (.branch 296
 (.branch 293
 (.branch 292
 (.leaf (.matching Nonrational.OldTerminalMatches.M021.r1406))
 (.leaf (.quota 2)))
 (.branch 294
 (.leaf (.quota 2))
 (.branch 295
 (.leaf (.quota 1))
 (.leaf (.matching Nonrational.OldTerminalMatches.M021.r1407)))))
 (.branch 298
 (.branch 297
 (.leaf (.quota 1))
 (.leaf (.matching Nonrational.OldTerminalMatches.M022.r1408)))
 (.branch 299
 (.leaf (.matching Nonrational.OldTerminalMatches.M022.r1409))
 (.leaf (.quota 2))))))
 (.branch 311
 (.leaf (.quota 2))
 (.branch 316
 (.leaf (.quota 2))
 (.branch 319
 (.branch 317
 (.leaf (.quota 2))
 (.branch 318
 (.leaf (.matching Nonrational.OldTerminalMatches.M022.r1410))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))))))))
 (.branch 483
 (.branch 402
 (.branch 362
 (.branch 342
 (.branch 332
 (.branch 327
 (.leaf (.quota 2))
 (.branch 329
 (.branch 328
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 330
 (.leaf (.matching Nonrational.OldTerminalMatches.M022.r1411))
 (.leaf (.quota 2)))))
 (.branch 337
 (.leaf (.quota 2))
 (.branch 339
 (.leaf (.quota 2))
 (.branch 340
 (.leaf (.quota 2))
 (.branch 341
 (.leaf (.quota 2))
 (.leaf (.incidence 4)))))))
 (.branch 352
 (.branch 347
 (.branch 344
 (.branch 343
 (.leaf (.matching Nonrational.OldTerminalMatches.M022.r1412))
 (.leaf (.matching Nonrational.OldTerminalMatches.M022.r1413)))
 (.branch 345
 (.leaf (.matching Nonrational.OldTerminalMatches.M022.r1414))
 (.leaf (.quota 1))))
 (.branch 349
 (.leaf (.quota 2))
 (.branch 350
 (.leaf (.quota 2))
 (.branch 351
 (.leaf (.matching Nonrational.OldTerminalMatches.M022.r1415))
 (.leaf (.quota 1))))))
 (.branch 357
 (.branch 354
 (.branch 353
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M022.r1416)))
 (.leaf (.quota 2)))
 (.branch 359
 (.branch 358
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 360
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))))
 (.branch 382
 (.branch 372
 (.branch 367
 (.branch 364
 (.leaf (.quota 2))
 (.branch 365
 (.leaf (.matching Nonrational.OldTerminalMatches.M022.r1417))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 392
 (.leaf (.quota 2))
 (.branch 397
 (.leaf (.quota 2))
 (.branch 399
 (.leaf (.quota 2))
 (.branch 400
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))))
 (.branch 442
 (.branch 422
 (.branch 412
 (.branch 407
 (.branch 404
 (.leaf (.quota 2))
 (.branch 405
 (.leaf (.quota 2))
 (.branch 406
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.leaf (.quota 2)))
 (.branch 417
 (.branch 414
 (.branch 413
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 415
 (.leaf (.quota 2))
 (.branch 416
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.branch 462
 (.branch 452
 (.branch 447
 (.branch 444
 (.branch 443
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 449
 (.branch 448
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 450
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 457
 (.leaf (.quota 2))
 (.branch 459
 (.leaf (.quota 2))
 (.branch 460
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 472
 (.branch 467
 (.branch 464
 (.leaf (.quota 2))
 (.branch 465
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.branch 477
 (.branch 474
 (.leaf (.quota 2))
 (.branch 475
 (.leaf (.quota 2))
 (.branch 476
 (.leaf (.matching Nonrational.OldTerminalMatches.M022.r1418))
 (.leaf (.matching Nonrational.OldTerminalMatches.M022.r1419)))))
 (.branch 480
 (.branch 478
 (.leaf (.matching Nonrational.OldTerminalMatches.M022.r1420))
 (.branch 479
 (.leaf (.matching Nonrational.OldTerminalMatches.M022.r1421))
 (.leaf (.matching Nonrational.OldTerminalMatches.M022.r1422))))
 (.branch 481
 (.leaf (.quota 2))
 (.branch 482
 (.leaf (.matching Nonrational.OldTerminalMatches.M022.r1423))
 (.leaf (.matching Nonrational.OldTerminalMatches.M022.r1424))))))))))
 (.branch 563
 (.branch 523
 (.branch 503
 (.branch 493
 (.branch 488
 (.leaf (.quota 2))
 (.branch 490
 (.leaf (.quota 2))
 (.branch 491
 (.leaf (.quota 2))
 (.branch 492
 (.leaf (.matching Nonrational.OldTerminalMatches.M022.r1425))
 (.leaf (.quota 1))))))
 (.branch 498
 (.branch 495
 (.branch 494
 (.leaf (.quota 1))
 (.leaf (.matching Nonrational.OldTerminalMatches.M022.r1426)))
 (.branch 496
 (.leaf (.matching Nonrational.OldTerminalMatches.M022.r1427))
 (.branch 497
 (.leaf (.quota 1))
 (.leaf (.matching Nonrational.OldTerminalMatches.M022.r1428)))))
 (.branch 500
 (.branch 499
 (.leaf (.quota 1))
 (.leaf (.matching Nonrational.OldTerminalMatches.M022.r1429)))
 (.branch 501
 (.leaf (.quota 2))
 (.branch 502
 (.leaf (.matching Nonrational.OldTerminalMatches.M022.r1430))
 (.leaf (.quota 2)))))))
 (.branch 513
 (.branch 508
 (.branch 505
 (.branch 504
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M022.r1431)))
 (.branch 506
 (.leaf (.quota 2))
 (.branch 507
 (.leaf (.matching Nonrational.OldTerminalMatches.M022.r1432))
 (.leaf (.matching Nonrational.OldTerminalMatches.M022.r1433)))))
 (.branch 510
 (.branch 509
 (.leaf (.matching Nonrational.OldTerminalMatches.M022.r1434))
 (.leaf (.matching Nonrational.OldTerminalMatches.M022.r1435)))
 (.leaf (.quota 2))))
 (.branch 518
 (.branch 515
 (.branch 514
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M022.r1436)))
 (.branch 516
 (.leaf (.quota 2))
 (.branch 517
 (.leaf (.matching Nonrational.OldTerminalMatches.M022.r1437))
 (.leaf (.quota 2)))))
 (.branch 520
 (.branch 519
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 521
 (.leaf (.quota 2))
 (.branch 522
 (.leaf (.quota 1))
 (.leaf (.matching Nonrational.OldTerminalMatches.M022.r1438))))))))
 (.branch 543
 (.branch 533
 (.branch 528
 (.branch 525
 (.branch 524
 (.leaf (.matching Nonrational.OldTerminalMatches.M022.r1439))
 (.leaf (.quota 1)))
 (.branch 526
 (.leaf (.matching Nonrational.OldTerminalMatches.M022.r1440))
 (.branch 527
 (.leaf (.matching Nonrational.OldTerminalMatches.M022.r1441))
 (.leaf (.quota 1)))))
 (.branch 530
 (.branch 529
 (.leaf (.matching Nonrational.OldTerminalMatches.M022.r1442))
 (.leaf (.matching Nonrational.OldTerminalMatches.M022.r1443)))
 (.leaf (.quota 2))))
 (.branch 538
 (.branch 535
 (.branch 534
 (.leaf (.matching Nonrational.OldTerminalMatches.M022.r1444))
 (.leaf (.quota 1)))
 (.branch 536
 (.leaf (.quota 2))
 (.branch 537
 (.leaf (.incidence 0))
 (.leaf (.matching Nonrational.OldTerminalMatches.M022.r1445)))))
 (.branch 540
 (.branch 539
 (.leaf (.quota 1))
 (.leaf (.matching Nonrational.OldTerminalMatches.M022.r1446)))
 (.leaf (.quota 2)))))
 (.branch 553
 (.branch 548
 (.branch 545
 (.leaf (.quota 2))
 (.branch 546
 (.leaf (.quota 2))
 (.branch 547
 (.leaf (.matching Nonrational.OldTerminalMatches.M022.r1447))
 (.leaf (.matching Nonrational.OldTerminalMatches.M022.r1448)))))
 (.branch 550
 (.branch 549
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M022.r1449)))
 (.branch 551
 (.leaf (.matching Nonrational.OldTerminalMatches.M022.r1450))
 (.branch 552
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M022.r1451))))))
 (.branch 558
 (.branch 555
 (.branch 554
 (.leaf (.matching Nonrational.OldTerminalMatches.M022.r1452))
 (.leaf (.matching Nonrational.OldTerminalMatches.M022.r1453)))
 (.branch 556
 (.leaf (.quota 2))
 (.branch 557
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 560
 (.leaf (.quota 2))
 (.branch 561
 (.leaf (.quota 1))
 (.branch 562
 (.leaf (.matching Nonrational.OldTerminalMatches.M022.r1454))
 (.leaf (.matching Nonrational.OldTerminalMatches.M022.r1455)))))))))
 (.branch 603
 (.branch 583
 (.branch 573
 (.branch 568
 (.branch 565
 (.branch 564
 (.leaf (.matching Nonrational.OldTerminalMatches.M022.r1456))
 (.leaf (.matching Nonrational.OldTerminalMatches.M022.r1457)))
 (.branch 566
 (.leaf (.matching Nonrational.OldTerminalMatches.M022.r1458))
 (.branch 567
 (.leaf (.matching Nonrational.OldTerminalMatches.M022.r1459))
 (.leaf (.matching Nonrational.OldTerminalMatches.M022.r1460)))))
 (.branch 570
 (.leaf (.quota 1))
 (.branch 571
 (.leaf (.matching Nonrational.OldTerminalMatches.M022.r1461))
 (.branch 572
 (.leaf (.quota 1))
 (.leaf (.matching Nonrational.OldTerminalMatches.M022.r1462))))))
 (.branch 578
 (.branch 575
 (.leaf (.quota 2))
 (.branch 576
 (.leaf (.quota 2))
 (.branch 577
 (.leaf (.incidence 4))
 (.leaf (.quota 2)))))
 (.branch 580
 (.branch 579
 (.leaf (.matching Nonrational.OldTerminalMatches.M022.r1463))
 (.leaf (.incidence 0)))
 (.branch 581
 (.leaf (.quota 1))
 (.branch 582
 (.leaf (.quota 1))
 (.leaf (.incidence 0)))))))
 (.branch 593
 (.branch 588
 (.branch 585
 (.branch 584
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 586
 (.leaf (.incidence 4))
 (.leaf (.quota 2))))
 (.branch 590
 (.leaf (.quota 1))
 (.branch 591
 (.leaf (.incidence 4))
 (.leaf (.quota 2)))))
 (.branch 598
 (.leaf (.quota 2))
 (.branch 600
 (.leaf (.quota 2))
 (.branch 601
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))))
 (.branch 623
 (.branch 613
 (.branch 608
 (.branch 605
 (.leaf (.quota 2))
 (.branch 606
 (.leaf (.quota 1))
 (.branch 607
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 610
 (.branch 609
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 611
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 618
 (.branch 615
 (.leaf (.quota 1))
 (.branch 616
 (.leaf (.incidence 0))
 (.leaf (.quota 2))))
 (.branch 620
 (.leaf (.quota 2))
 (.branch 621
 (.leaf (.quota 2))
 (.branch 622
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))))
 (.branch 633
 (.branch 628
 (.branch 625
 (.leaf (.quota 2))
 (.branch 626
 (.leaf (.quota 3))
 (.branch 627
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 630
 (.branch 629
 (.leaf (.quota 3))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.branch 638
 (.branch 635
 (.leaf (.quota 2))
 (.branch 636
 (.leaf (.quota 2))
 (.branch 637
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 641
 (.leaf (.quota 2))
 (.branch 642
 (.leaf (.quota 2))
 (.branch 643
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))))))))
def disposition (j : Fin leafCount) := dispositionTable.get j.val
def dispositionTest (i : Nat) : Bool := RawLeafCertificate.check quota
  ((rawLeaves i).map Papers.RationalityTen.RootedCaches.RootedSixBase03.rawCells) (dispositionTable.get i)

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0722

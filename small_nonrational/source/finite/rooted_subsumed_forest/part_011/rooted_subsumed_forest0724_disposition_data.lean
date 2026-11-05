module
prelude
public import RootedSubsumedForest0724Data
public import RawLeafCertificate
public import OldTerminalMatches.M022
public import OldTerminalMatches.M023
public import OldTerminalMatches.M024

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
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
 (.leaf (.quota 2))
 (.branch 4
 (.leaf (.quota 2))
 (.branch 5
 (.leaf (.quota 2))
 (.leaf (.quota 3)))))
 (.branch 9
 (.leaf (.quota 2))
 (.branch 11
 (.leaf (.quota 2))
 (.leaf (.quota 3)))))
 (.branch 19
 (.branch 16
 (.branch 14
 (.leaf (.quota 1))
 (.branch 15
 (.leaf (.matching Nonrational.OldTerminalMatches.M022.r1469))
 (.leaf (.matching Nonrational.OldTerminalMatches.M022.r1470))))
 (.leaf (.quota 2)))
 (.branch 22
 (.branch 20
 (.leaf (.matching Nonrational.OldTerminalMatches.M022.r1471))
 (.branch 21
 (.leaf (.matching Nonrational.OldTerminalMatches.M023.r1472))
 (.leaf (.quota 2))))
 (.branch 24
 (.branch 23
 (.leaf (.matching Nonrational.OldTerminalMatches.M023.r1473))
 (.leaf (.matching Nonrational.OldTerminalMatches.M023.r1474)))
 (.leaf (.quota 2))))))
 (.branch 39
 (.branch 32
 (.branch 29
 (.branch 27
 (.leaf (.matching Nonrational.OldTerminalMatches.M023.r1475))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 35
 (.leaf (.quota 2))
 (.branch 37
 (.leaf (.quota 2))
 (.branch 38
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M023.r1476))))))
 (.branch 46
 (.branch 42
 (.branch 40
 (.leaf (.matching Nonrational.OldTerminalMatches.M023.r1477))
 (.leaf (.quota 2)))
 (.branch 44
 (.leaf (.quota 2))
 (.branch 45
 (.leaf (.matching Nonrational.OldTerminalMatches.M023.r1478))
 (.leaf (.quota 2)))))
 (.branch 49
 (.branch 47
 (.leaf (.matching Nonrational.OldTerminalMatches.M023.r1479))
 (.branch 48
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 51
 (.leaf (.quota 3))
 (.leaf (.quota 2)))))))
 (.branch 80
 (.branch 66
 (.branch 59
 (.branch 56
 (.branch 54
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))
 (.branch 62
 (.branch 60
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 64
 (.branch 63
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 65
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 73
 (.branch 69
 (.branch 67
 (.leaf (.quota 1))
 (.branch 68
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M023.r1480))))
 (.branch 71
 (.branch 70
 (.leaf (.matching Nonrational.OldTerminalMatches.M023.r1481))
 (.leaf .euler))
 (.branch 72
 (.leaf .euler)
 (.leaf (.matching Nonrational.OldTerminalMatches.M023.r1482)))))
 (.leaf (.quota 2))))
 (.branch 93
 (.branch 86
 (.branch 83
 (.branch 81
 (.leaf (.quota 2))
 (.branch 82
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.branch 89
 (.leaf (.quota 2))
 (.branch 91
 (.branch 90
 (.leaf (.matching Nonrational.OldTerminalMatches.M023.r1483))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))))
 (.leaf (.quota 2)))))
 (.branch 160
 (.branch 133
 (.branch 120
 (.branch 113
 (.leaf (.quota 2))
 (.branch 116
 (.branch 114
 (.leaf (.quota 3))
 (.leaf (.quota 2)))
 (.branch 118
 (.leaf (.quota 2))
 (.branch 119
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 126
 (.leaf (.quota 2))
 (.branch 129
 (.leaf (.quota 2))
 (.branch 131
 (.leaf (.quota 2))
 (.branch 132
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))))
 (.branch 146
 (.branch 139
 (.branch 136
 (.leaf (.quota 2))
 (.branch 137
 (.leaf (.quota 2))
 (.branch 138
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 142
 (.branch 140
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.branch 153
 (.leaf (.quota 2))
 (.branch 156
 (.leaf (.quota 2))
 (.branch 158
 (.leaf (.quota 2))
 (.branch 159
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))))
 (.branch 187
 (.branch 173
 (.branch 166
 (.leaf (.quota 2))
 (.branch 169
 (.branch 167
 (.leaf (.quota 2))
 (.branch 168
 (.leaf (.quota 2))
 (.leaf (.quota 3))))
 (.branch 171
 (.branch 170
 (.leaf (.quota 3))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))))
 (.branch 180
 (.branch 176
 (.branch 174
 (.leaf (.quota 2))
 (.branch 175
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 178
 (.branch 177
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.leaf (.quota 2))))
 (.branch 200
 (.leaf (.quota 2))
 (.branch 207
 (.branch 203
 (.branch 201
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))))))
 (.branch 321
 (.branch 267
 (.branch 240
 (.branch 227
 (.branch 220
 (.branch 217
 (.branch 215
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 223
 (.leaf (.quota 2))
 (.branch 225
 (.leaf (.quota 2))
 (.branch 226
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 233
 (.leaf (.quota 2))
 (.branch 236
 (.leaf (.quota 2))
 (.branch 238
 (.leaf (.quota 2))
 (.branch 239
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))))
 (.branch 253
 (.branch 246
 (.branch 243
 (.leaf (.quota 2))
 (.branch 244
 (.leaf (.quota 2))
 (.branch 245
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 249
 (.branch 247
 (.leaf (.quota 2))
 (.branch 248
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 2))))
 (.branch 260
 (.branch 256
 (.leaf (.quota 2))
 (.branch 258
 (.branch 257
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2))))
 (.branch 263
 (.branch 261
 (.leaf (.quota 2))
 (.branch 262
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 2))))))
 (.branch 294
 (.branch 280
 (.branch 273
 (.leaf (.quota 2))
 (.branch 276
 (.leaf (.quota 2))
 (.branch 278
 (.leaf (.quota 2))
 (.branch 279
 (.leaf (.quota 2))
 (.leaf (.quota 3))))))
 (.branch 287
 (.branch 283
 (.branch 281
 (.leaf (.quota 3))
 (.leaf (.quota 2)))
 (.branch 285
 (.leaf (.quota 2))
 (.branch 286
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 290
 (.leaf (.quota 2))
 (.branch 292
 (.branch 291
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))))
 (.branch 307
 (.branch 300
 (.leaf (.quota 2))
 (.branch 303
 (.branch 301
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 305
 (.leaf (.quota 2))
 (.branch 306
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 314
 (.leaf (.quota 2))
 (.branch 317
 (.branch 315
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 319
 (.branch 318
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))))))
 (.branch 374
 (.branch 347
 (.branch 334
 (.branch 327
 (.branch 324
 (.branch 322
 (.leaf (.quota 2))
 (.branch 323
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 325
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 330
 (.branch 328
 (.leaf (.quota 2))
 (.branch 329
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 332
 (.branch 331
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))))
 (.branch 340
 (.branch 337
 (.branch 335
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.branch 360
 (.branch 353
 (.branch 350
 (.branch 348
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 351
 (.leaf (.quota 2))
 (.branch 352
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 356
 (.branch 354
 (.leaf (.quota 2))
 (.branch 355
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 358
 (.leaf (.quota 2))
 (.branch 359
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 367
 (.branch 363
 (.branch 361
 (.leaf (.quota 2))
 (.branch 362
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 2)))
 (.branch 370
 (.branch 368
 (.leaf (.quota 1))
 (.branch 369
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 2))))))
 (.branch 401
 (.branch 387
 (.branch 380
 (.leaf (.quota 2))
 (.branch 383
 (.leaf (.quota 2))
 (.branch 385
 (.leaf (.quota 2))
 (.branch 386
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 394
 (.branch 390
 (.leaf (.quota 2))
 (.branch 392
 (.leaf (.quota 2))
 (.branch 393
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 397
 (.branch 395
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))))
 (.branch 414
 (.branch 407
 (.leaf (.quota 2))
 (.branch 410
 (.leaf (.quota 2))
 (.branch 412
 (.leaf (.quota 2))
 (.branch 413
 (.leaf (.quota 2))
 (.leaf (.quota 3))))))
 (.branch 421
 (.branch 417
 (.leaf (.quota 2))
 (.branch 419
 (.branch 418
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.leaf (.quota 2))))
 (.leaf (.quota 2))))))))
 (.branch 642
 (.branch 535
 (.branch 481
 (.branch 454
 (.branch 441
 (.branch 434
 (.branch 431
 (.branch 429
 (.leaf (.quota 1))
 (.branch 430
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 432
 (.leaf (.quota 2))
 (.branch 433
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 437
 (.branch 435
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.branch 467
 (.branch 460
 (.leaf (.quota 2))
 (.branch 463
 (.branch 461
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.branch 465
 (.leaf (.quota 2))
 (.branch 466
 (.leaf (.quota 3))
 (.leaf (.quota 2))))))
 (.branch 474
 (.leaf (.quota 2))
 (.branch 477
 (.leaf (.quota 2))
 (.branch 479
 (.branch 478
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))))))
 (.branch 508
 (.branch 494
 (.branch 487
 (.branch 484
 (.leaf (.quota 2))
 (.branch 485
 (.leaf (.quota 2))
 (.branch 486
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.leaf (.quota 2)))
 (.branch 501
 (.branch 497
 (.branch 495
 (.leaf (.quota 2))
 (.branch 496
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.branch 521
 (.branch 514
 (.branch 511
 (.branch 509
 (.leaf (.quota 2))
 (.branch 510
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 512
 (.leaf (.quota 3))
 (.leaf (.quota 2))))
 (.branch 517
 (.leaf (.quota 2))
 (.branch 519
 (.leaf (.quota 2))
 (.branch 520
 (.leaf (.quota 3))
 (.leaf (.quota 2))))))
 (.leaf (.quota 2)))))
 (.branch 588
 (.branch 561
 (.branch 548
 (.branch 541
 (.branch 538
 (.branch 536
 (.leaf (.quota 1))
 (.branch 537
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.branch 544
 (.branch 542
 (.leaf (.quota 2))
 (.branch 543
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 546
 (.branch 545
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))))
 (.branch 554
 (.branch 551
 (.branch 549
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))
 (.branch 557
 (.leaf (.quota 2))
 (.branch 559
 (.leaf (.quota 2))
 (.branch 560
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M023.r1484)))))))
 (.branch 574
 (.branch 567
 (.branch 564
 (.branch 562
 (.leaf (.matching Nonrational.OldTerminalMatches.M023.r1485))
 (.branch 563
 (.leaf (.matching Nonrational.OldTerminalMatches.M023.r1486))
 (.leaf (.quota 2))))
 (.branch 565
 (.leaf (.quota 2))
 (.branch 566
 (.leaf (.matching Nonrational.OldTerminalMatches.M023.r1487))
 (.leaf (.quota 2)))))
 (.branch 570
 (.branch 568
 (.leaf (.quota 2))
 (.branch 569
 (.leaf (.matching Nonrational.OldTerminalMatches.M023.r1488))
 (.leaf (.quota 2))))
 (.leaf (.quota 2))))
 (.branch 581
 (.branch 577
 (.branch 575
 (.leaf (.quota 2))
 (.branch 576
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M023.r1489))))
 (.branch 579
 (.branch 578
 (.leaf (.matching Nonrational.OldTerminalMatches.M023.r1490))
 (.leaf (.quota 2)))
 (.branch 580
 (.leaf (.matching Nonrational.OldTerminalMatches.M023.r1491))
 (.leaf (.quota 2)))))
 (.branch 584
 (.branch 582
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))))
 (.branch 615
 (.branch 601
 (.branch 594
 (.branch 591
 (.branch 589
 (.leaf (.quota 2))
 (.branch 590
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 2)))
 (.branch 597
 (.leaf (.quota 2))
 (.branch 599
 (.branch 598
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 600
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 608
 (.branch 604
 (.branch 602
 (.leaf (.quota 3))
 (.branch 603
 (.leaf (.quota 3))
 (.leaf (.quota 2))))
 (.branch 606
 (.branch 605
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.branch 607
 (.leaf (.quota 3))
 (.leaf (.quota 1)))))
 (.branch 611
 (.branch 609
 (.leaf (.quota 1))
 (.branch 610
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 613
 (.branch 612
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2))))))
 (.branch 628
 (.branch 621
 (.branch 618
 (.branch 616
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 619
 (.leaf (.quota 2))
 (.branch 620
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M023.r1492)))))
 (.branch 624
 (.branch 622
 (.leaf (.quota 2))
 (.branch 623
 (.leaf .euler)
 (.leaf (.quota 2))))
 (.branch 626
 (.leaf (.quota 2))
 (.branch 627
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 635
 (.branch 631
 (.branch 629
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 638
 (.branch 636
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 640
 (.branch 639
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))))))))
 (.branch 749
 (.branch 695
 (.branch 668
 (.branch 655
 (.branch 648
 (.branch 645
 (.branch 643
 (.leaf (.quota 1))
 (.branch 644
 (.leaf (.matching Nonrational.OldTerminalMatches.M023.r1493))
 (.leaf (.matching Nonrational.OldTerminalMatches.M023.r1494))))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 661
 (.leaf (.quota 2))
 (.branch 664
 (.leaf (.quota 2))
 (.branch 666
 (.leaf (.quota 2))
 (.branch 667
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))))
 (.branch 681
 (.branch 674
 (.branch 671
 (.branch 669
 (.leaf (.quota 2))
 (.branch 670
 (.leaf (.matching Nonrational.OldTerminalMatches.M023.r1495))
 (.leaf (.matching Nonrational.OldTerminalMatches.M023.r1496))))
 (.branch 672
 (.leaf (.matching Nonrational.OldTerminalMatches.M023.r1497))
 (.branch 673
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.leaf (.quota 2)))
 (.branch 688
 (.branch 684
 (.branch 682
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 686
 (.branch 685
 (.leaf (.quota 1))
 (.leaf (.matching Nonrational.OldTerminalMatches.M023.r1498)))
 (.branch 687
 (.leaf (.matching Nonrational.OldTerminalMatches.M023.r1499))
 (.leaf (.matching Nonrational.OldTerminalMatches.M023.r1500)))))
 (.branch 691
 (.branch 689
 (.leaf (.matching Nonrational.OldTerminalMatches.M023.r1501))
 (.leaf (.quota 1)))
 (.leaf (.quota 2))))))
 (.branch 722
 (.branch 708
 (.branch 701
 (.branch 698
 (.branch 696
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))
 (.branch 704
 (.branch 702
 (.leaf (.quota 2))
 (.branch 703
 (.leaf (.quota 2))
 (.leaf (.quota 3))))
 (.branch 706
 (.branch 705
 (.leaf (.quota 3))
 (.leaf (.quota 1)))
 (.branch 707
 (.leaf (.quota 2))
 (.leaf (.quota 3))))))
 (.branch 715
 (.branch 711
 (.leaf (.quota 2))
 (.branch 713
 (.branch 712
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2))))
 (.branch 718
 (.leaf (.quota 2))
 (.branch 720
 (.branch 719
 (.leaf (.quota 3))
 (.leaf (.quota 2)))
 (.branch 721
 (.leaf (.quota 3))
 (.leaf (.quota 2)))))))
 (.branch 735
 (.branch 728
 (.branch 725
 (.branch 723
 (.leaf (.quota 2))
 (.branch 724
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 726
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 731
 (.leaf (.quota 2))
 (.branch 733
 (.leaf (.quota 2))
 (.branch 734
 (.leaf (.quota 2))
 (.leaf (.quota 3))))))
 (.branch 742
 (.branch 738
 (.leaf (.quota 2))
 (.branch 740
 (.branch 739
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.leaf (.quota 2))))
 (.branch 745
 (.leaf (.quota 2))
 (.branch 747
 (.leaf (.quota 2))
 (.branch 748
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))))))
 (.branch 803
 (.branch 776
 (.branch 762
 (.branch 755
 (.branch 752
 (.leaf (.quota 2))
 (.branch 753
 (.leaf (.quota 3))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.branch 769
 (.branch 765
 (.branch 763
 (.leaf (.quota 1))
 (.branch 764
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 767
 (.branch 766
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M023.r1502)))
 (.leaf (.quota 1))))
 (.branch 772
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 789
 (.branch 782
 (.leaf (.quota 2))
 (.branch 785
 (.branch 783
 (.leaf (.quota 1))
 (.branch 784
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M023.r1503))))
 (.branch 787
 (.branch 786
 (.leaf (.matching Nonrational.OldTerminalMatches.M023.r1504))
 (.leaf (.matching Nonrational.OldTerminalMatches.M023.r1505)))
 (.leaf (.quota 2)))))
 (.branch 796
 (.leaf (.quota 2))
 (.branch 799
 (.branch 797
 (.leaf (.quota 2))
 (.branch 798
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 2))))))
 (.branch 830
 (.branch 816
 (.branch 809
 (.branch 806
 (.branch 804
 (.leaf (.quota 2))
 (.branch 805
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 807
 (.leaf (.quota 2))
 (.branch 808
 (.leaf (.matching Nonrational.OldTerminalMatches.M023.r1506))
 (.leaf (.quota 2)))))
 (.leaf (.quota 2)))
 (.branch 823
 (.branch 819
 (.leaf (.quota 2))
 (.branch 821
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 826
 (.branch 824
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 828
 (.leaf (.quota 2))
 (.branch 829
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))))
 (.branch 843
 (.branch 836
 (.leaf (.quota 2))
 (.branch 839
 (.branch 837
 (.leaf (.quota 2))
 (.branch 838
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))
 (.branch 850
 (.branch 846
 (.branch 844
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 848
 (.branch 847
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1))))
 (.branch 853
 (.branch 851
 (.leaf (.quota 1))
 (.branch 852
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 855
 (.leaf (.quota 2))
 (.branch 856
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))))))))
 (.branch 1285
 (.branch 1071
 (.branch 964
 (.branch 910
 (.branch 883
 (.branch 870
 (.branch 863
 (.leaf (.quota 2))
 (.branch 866
 (.branch 864
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.branch 876
 (.branch 873
 (.branch 871
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 874
 (.leaf (.quota 2))
 (.branch 875
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 879
 (.branch 877
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))))
 (.branch 896
 (.branch 889
 (.branch 886
 (.branch 884
 (.leaf (.quota 2))
 (.branch 885
 (.leaf (.quota 2))
 (.leaf (.quota 3))))
 (.leaf (.quota 2)))
 (.branch 892
 (.branch 890
 (.leaf (.quota 2))
 (.branch 891
 (.leaf (.quota 3))
 (.leaf (.quota 2))))
 (.branch 894
 (.leaf (.quota 2))
 (.branch 895
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 903
 (.branch 899
 (.branch 897
 (.leaf (.quota 1))
 (.branch 898
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.branch 906
 (.leaf (.quota 2))
 (.branch 908
 (.leaf (.quota 2))
 (.branch 909
 (.leaf (.quota 2))
 (.leaf (.quota 3))))))))
 (.branch 937
 (.branch 923
 (.branch 916
 (.branch 913
 (.branch 911
 (.leaf (.quota 2))
 (.branch 912
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 914
 (.leaf (.quota 2))
 (.branch 915
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 919
 (.leaf (.quota 2))
 (.branch 921
 (.leaf (.quota 2))
 (.branch 922
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 930
 (.leaf (.quota 2))
 (.branch 933
 (.branch 931
 (.leaf (.matching Nonrational.OldTerminalMatches.M023.r1507))
 (.branch 932
 (.leaf (.matching Nonrational.OldTerminalMatches.M023.r1508))
 (.leaf (.quota 2))))
 (.branch 935
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 950
 (.branch 943
 (.branch 940
 (.branch 938
 (.leaf (.quota 1))
 (.branch 939
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1)))
 (.branch 946
 (.branch 944
 (.leaf (.quota 2))
 (.branch 945
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 948
 (.leaf (.quota 1))
 (.branch 949
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 957
 (.branch 953
 (.branch 951
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 955
 (.leaf (.quota 2))
 (.branch 956
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 960
 (.branch 958
 (.leaf (.quota 1))
 (.branch 959
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 962
 (.branch 961
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 963
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M023.r1509)))))))))
 (.branch 1017
 (.branch 990
 (.branch 977
 (.branch 970
 (.branch 967
 (.branch 965
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 968
 (.leaf (.quota 2))
 (.branch 969
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 973
 (.branch 971
 (.leaf (.quota 2))
 (.branch 972
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 2))))
 (.branch 983
 (.branch 980
 (.leaf (.quota 2))
 (.branch 981
 (.leaf (.quota 1))
 (.branch 982
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 986
 (.leaf (.quota 2))
 (.branch 988
 (.leaf (.quota 2))
 (.branch 989
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))))
 (.branch 1003
 (.branch 996
 (.branch 993
 (.branch 991
 (.leaf (.matching Nonrational.OldTerminalMatches.M023.r1510))
 (.leaf (.quota 2)))
 (.branch 994
 (.leaf (.quota 2))
 (.branch 995
 (.leaf (.matching Nonrational.OldTerminalMatches.M023.r1511))
 (.leaf (.quota 2)))))
 (.leaf (.quota 2)))
 (.branch 1010
 (.branch 1006
 (.leaf (.quota 2))
 (.branch 1008
 (.branch 1007
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.leaf (.quota 2))))
 (.branch 1013
 (.leaf (.quota 2))
 (.branch 1015
 (.leaf (.quota 2))
 (.branch 1016
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))))
 (.branch 1044
 (.branch 1030
 (.branch 1023
 (.branch 1020
 (.branch 1018
 (.leaf (.quota 2))
 (.branch 1019
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 1021
 (.leaf (.quota 2))
 (.branch 1022
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 1026
 (.branch 1024
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 1028
 (.branch 1027
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))))
 (.leaf (.quota 2)))
 (.branch 1057
 (.branch 1050
 (.branch 1047
 (.branch 1045
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.branch 1048
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 1053
 (.branch 1051
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.leaf (.quota 2))))))
 (.branch 1178
 (.branch 1124
 (.branch 1097
 (.branch 1084
 (.leaf (.quota 2))
 (.branch 1090
 (.branch 1087
 (.branch 1085
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 1093
 (.leaf (.quota 2))
 (.branch 1095
 (.leaf (.quota 2))
 (.branch 1096
 (.leaf (.quota 2))
 (.leaf (.quota 3)))))))
 (.branch 1110
 (.branch 1103
 (.branch 1100
 (.branch 1098
 (.leaf (.quota 3))
 (.branch 1099
 (.leaf (.quota 3))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 1117
 (.branch 1113
 (.branch 1111
 (.leaf (.quota 2))
 (.branch 1112
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 1115
 (.leaf (.quota 2))
 (.branch 1116
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 1120
 (.branch 1118
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))))
 (.branch 1151
 (.branch 1137
 (.branch 1130
 (.leaf (.quota 2))
 (.branch 1133
 (.branch 1131
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.branch 1144
 (.branch 1140
 (.leaf (.quota 2))
 (.branch 1142
 (.branch 1141
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.branch 1147
 (.branch 1145
 (.leaf (.quota 1))
 (.branch 1146
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 1149
 (.leaf (.quota 2))
 (.branch 1150
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))))
 (.branch 1164
 (.branch 1157
 (.branch 1154
 (.branch 1152
 (.leaf (.quota 3))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 1160
 (.leaf (.quota 2))
 (.branch 1162
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 1171
 (.branch 1167
 (.branch 1165
 (.leaf (.quota 1))
 (.branch 1166
 (.leaf (.quota 3))
 (.leaf (.quota 1))))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))))
 (.branch 1231
 (.branch 1204
 (.branch 1191
 (.branch 1184
 (.leaf (.quota 2))
 (.branch 1187
 (.branch 1185
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 1189
 (.branch 1188
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.branch 1190
 (.leaf (.quota 2))
 (.leaf (.quota 3))))))
 (.branch 1197
 (.branch 1194
 (.branch 1192
 (.leaf (.quota 3))
 (.leaf (.quota 2)))
 (.branch 1195
 (.leaf (.quota 1))
 (.branch 1196
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 1200
 (.branch 1198
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 1202
 (.branch 1201
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 1203
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))))
 (.branch 1217
 (.branch 1210
 (.branch 1207
 (.branch 1205
 (.leaf (.quota 2))
 (.branch 1206
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.branch 1213
 (.leaf (.quota 2))
 (.branch 1215
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 1224
 (.branch 1220
 (.branch 1218
 (.leaf (.quota 1))
 (.branch 1219
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 1222
 (.leaf (.quota 2))
 (.branch 1223
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.leaf (.quota 2)))))
 (.branch 1258
 (.branch 1244
 (.branch 1237
 (.branch 1234
 (.leaf (.quota 2))
 (.branch 1235
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 1240
 (.branch 1238
 (.leaf (.quota 2))
 (.branch 1239
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 1242
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 1251
 (.branch 1247
 (.branch 1245
 (.leaf (.quota 1))
 (.branch 1246
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 1249
 (.leaf (.quota 2))
 (.branch 1250
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 1254
 (.leaf (.quota 2))
 (.branch 1256
 (.leaf (.quota 2))
 (.branch 1257
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))))
 (.branch 1271
 (.branch 1264
 (.branch 1261
 (.leaf (.quota 2))
 (.branch 1262
 (.leaf (.quota 2))
 (.branch 1263
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 1267
 (.branch 1265
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.branch 1278
 (.branch 1274
 (.leaf (.quota 2))
 (.branch 1276
 (.branch 1275
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2))))
 (.branch 1281
 (.branch 1279
 (.leaf (.quota 2))
 (.branch 1280
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))))))))
 (.branch 1499
 (.branch 1392
 (.branch 1338
 (.branch 1311
 (.branch 1298
 (.branch 1291
 (.branch 1288
 (.branch 1286
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 1294
 (.branch 1292
 (.leaf (.quota 2))
 (.branch 1293
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 1296
 (.leaf (.quota 1))
 (.branch 1297
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 1304
 (.branch 1301
 (.branch 1299
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 1302
 (.leaf (.quota 2))
 (.branch 1303
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 1307
 (.leaf (.quota 2))
 (.branch 1309
 (.leaf (.quota 2))
 (.branch 1310
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))))
 (.branch 1324
 (.branch 1317
 (.branch 1314
 (.leaf (.quota 1))
 (.branch 1315
 (.leaf (.quota 1))
 (.branch 1316
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 1320
 (.branch 1318
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.branch 1331
 (.branch 1327
 (.branch 1325
 (.leaf (.quota 2))
 (.branch 1326
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.branch 1334
 (.leaf (.quota 2))
 (.branch 1336
 (.branch 1335
 (.leaf (.quota 3))
 (.leaf (.quota 2)))
 (.branch 1337
 (.leaf (.quota 2))
 (.leaf (.quota 3))))))))
 (.branch 1365
 (.branch 1351
 (.branch 1344
 (.branch 1341
 (.branch 1339
 (.leaf (.quota 3))
 (.branch 1340
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 1342
 (.leaf (.quota 2))
 (.branch 1343
 (.leaf (.quota 3))
 (.leaf (.quota 2)))))
 (.branch 1347
 (.branch 1345
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 1349
 (.branch 1348
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 1350
 (.leaf (.quota 2))
 (.leaf (.quota 3))))))
 (.branch 1358
 (.branch 1354
 (.branch 1352
 (.leaf (.quota 2))
 (.branch 1353
 (.leaf (.quota 3))
 (.leaf (.quota 1))))
 (.leaf (.quota 2)))
 (.branch 1361
 (.branch 1359
 (.leaf (.quota 2))
 (.branch 1360
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 1363
 (.branch 1362
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2))))))
 (.branch 1378
 (.branch 1371
 (.branch 1368
 (.branch 1366
 (.leaf (.quota 3))
 (.branch 1367
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 1369
 (.leaf (.quota 3))
 (.branch 1370
 (.leaf (.quota 3))
 (.leaf (.quota 2)))))
 (.branch 1374
 (.leaf (.quota 2))
 (.branch 1376
 (.branch 1375
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))))
 (.branch 1385
 (.branch 1381
 (.branch 1379
 (.leaf (.quota 1))
 (.branch 1380
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.branch 1388
 (.branch 1386
 (.leaf (.quota 1))
 (.branch 1387
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 1390
 (.leaf (.quota 2))
 (.branch 1391
 (.leaf (.quota 3))
 (.leaf (.quota 2)))))))))
 (.branch 1445
 (.branch 1418
 (.branch 1405
 (.branch 1398
 (.branch 1395
 (.branch 1393
 (.leaf (.quota 3))
 (.leaf (.quota 2)))
 (.branch 1396
 (.leaf (.quota 2))
 (.branch 1397
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 1401
 (.branch 1399
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 1403
 (.leaf (.quota 2))
 (.branch 1404
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 1411
 (.leaf (.quota 2))
 (.branch 1414
 (.leaf (.quota 2))
 (.branch 1416
 (.branch 1415
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 1417
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))))
 (.branch 1431
 (.branch 1424
 (.branch 1421
 (.branch 1419
 (.leaf (.quota 1))
 (.branch 1420
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 2)))
 (.branch 1427
 (.branch 1425
 (.leaf (.quota 2))
 (.branch 1426
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 1429
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 1438
 (.branch 1434
 (.branch 1432
 (.leaf (.quota 2))
 (.branch 1433
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 1436
 (.leaf (.quota 2))
 (.branch 1437
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 1441
 (.leaf (.quota 2))
 (.branch 1443
 (.branch 1442
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))))))
 (.branch 1472
 (.branch 1458
 (.branch 1451
 (.branch 1448
 (.leaf (.quota 2))
 (.branch 1449
 (.leaf (.quota 2))
 (.branch 1450
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 1454
 (.branch 1452
 (.leaf (.quota 2))
 (.branch 1453
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 1456
 (.branch 1455
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.branch 1465
 (.branch 1461
 (.branch 1459
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 1468
 (.branch 1466
 (.leaf (.quota 2))
 (.branch 1467
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 1470
 (.branch 1469
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 1471
 (.leaf (.matching Nonrational.OldTerminalMatches.M023.r1512))
 (.leaf (.quota 2)))))))
 (.leaf (.quota 2)))))
 (.branch 1606
 (.branch 1552
 (.branch 1525
 (.branch 1512
 (.leaf (.quota 2))
 (.branch 1518
 (.branch 1515
 (.branch 1513
 (.leaf (.quota 2))
 (.branch 1514
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.branch 1521
 (.branch 1519
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.leaf (.quota 2)))))
 (.branch 1538
 (.branch 1531
 (.branch 1528
 (.branch 1526
 (.leaf (.quota 3))
 (.leaf (.quota 2)))
 (.branch 1529
 (.leaf (.quota 2))
 (.branch 1530
 (.leaf (.quota 3))
 (.leaf (.quota 2)))))
 (.branch 1534
 (.branch 1532
 (.leaf (.quota 2))
 (.branch 1533
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 1536
 (.branch 1535
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))))
 (.branch 1545
 (.leaf (.quota 2))
 (.branch 1548
 (.branch 1546
 (.leaf (.quota 2))
 (.branch 1547
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 1550
 (.branch 1549
 (.leaf (.quota 1))
 (.leaf (.quota 3)))
 (.branch 1551
 (.leaf (.quota 3))
 (.leaf (.quota 1))))))))
 (.branch 1579
 (.branch 1565
 (.branch 1558
 (.branch 1555
 (.branch 1553
 (.leaf (.quota 3))
 (.branch 1554
 (.leaf (.quota 3))
 (.leaf (.quota 2))))
 (.branch 1556
 (.leaf (.quota 3))
 (.branch 1557
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 1561
 (.branch 1559
 (.leaf (.quota 2))
 (.branch 1560
 (.leaf (.quota 1))
 (.leaf .euler)))
 (.branch 1563
 (.branch 1562
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 1564
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.leaf (.quota 2)))
 (.branch 1592
 (.leaf (.quota 2))
 (.branch 1599
 (.branch 1595
 (.branch 1593
 (.leaf (.matching Nonrational.OldTerminalMatches.M023.r1513))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 1602
 (.leaf (.quota 2))
 (.branch 1604
 (.branch 1603
 (.leaf (.quota 3))
 (.leaf (.quota 1)))
 (.leaf (.quota 2))))))))
 (.branch 1660
 (.branch 1633
 (.branch 1619
 (.branch 1612
 (.branch 1609
 (.leaf (.quota 2))
 (.branch 1610
 (.leaf (.quota 2))
 (.branch 1611
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 1615
 (.branch 1613
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 1617
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 1626
 (.branch 1622
 (.leaf (.quota 2))
 (.branch 1624
 (.branch 1623
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 1625
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 1629
 (.branch 1627
 (.leaf (.quota 2))
 (.branch 1628
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 1631
 (.leaf (.quota 2))
 (.branch 1632
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))))
 (.branch 1646
 (.branch 1639
 (.leaf (.quota 2))
 (.branch 1642
 (.branch 1640
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2))))
 (.branch 1653
 (.branch 1649
 (.branch 1647
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 1656
 (.branch 1654
 (.leaf (.quota 2))
 (.branch 1655
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 1658
 (.leaf (.quota 2))
 (.branch 1659
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))))
 (.branch 1687
 (.branch 1673
 (.branch 1666
 (.branch 1663
 (.branch 1661
 (.leaf (.quota 2))
 (.branch 1662
 (.leaf (.matching Nonrational.OldTerminalMatches.M023.r1514))
 (.leaf (.matching Nonrational.OldTerminalMatches.M023.r1515))))
 (.branch 1664
 (.leaf (.quota 2))
 (.branch 1665
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 1669
 (.branch 1667
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 1671
 (.branch 1670
 (.leaf (.matching Nonrational.OldTerminalMatches.M023.r1516))
 (.leaf (.quota 1)))
 (.branch 1672
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M023.r1517))))))
 (.branch 1680
 (.branch 1676
 (.branch 1674
 (.leaf (.quota 2))
 (.branch 1675
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M023.r1518))))
 (.branch 1678
 (.leaf (.quota 2))
 (.branch 1679
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 1683
 (.branch 1681
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 1685
 (.branch 1684
 (.leaf (.matching Nonrational.OldTerminalMatches.M023.r1519))
 (.leaf (.quota 2)))
 (.branch 1686
 (.leaf (.matching Nonrational.OldTerminalMatches.M023.r1520))
 (.leaf (.quota 2)))))))
 (.branch 1700
 (.branch 1693
 (.branch 1690
 (.branch 1688
 (.leaf (.matching Nonrational.OldTerminalMatches.M023.r1521))
 (.branch 1689
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 1691
 (.leaf (.quota 2))
 (.branch 1692
 (.leaf (.matching Nonrational.OldTerminalMatches.M023.r1522))
 (.leaf (.quota 1)))))
 (.branch 1696
 (.leaf (.quota 1))
 (.branch 1698
 (.branch 1697
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1)))))
 (.branch 1707
 (.branch 1703
 (.branch 1701
 (.leaf (.matching Nonrational.OldTerminalMatches.M023.r1523))
 (.branch 1702
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 1705
 (.leaf (.quota 2))
 (.branch 1706
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 1710
 (.branch 1708
 (.leaf (.quota 2))
 (.branch 1709
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 1712
 (.leaf (.quota 1))
 (.branch 1713
 (.leaf (.matching Nonrational.OldTerminalMatches.M023.r1524))
 (.leaf (.quota 2)))))))))))))
 (.branch 2571
 (.branch 2142
 (.branch 1928
 (.branch 1821
 (.branch 1767
 (.branch 1740
 (.branch 1727
 (.branch 1720
 (.branch 1717
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 1723
 (.leaf (.quota 1))
 (.branch 1725
 (.branch 1724
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))))
 (.branch 1733
 (.branch 1730
 (.branch 1728
 (.leaf (.quota 2))
 (.branch 1729
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 1731
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 1736
 (.branch 1734
 (.leaf (.quota 2))
 (.branch 1735
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 1738
 (.branch 1737
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))))
 (.branch 1753
 (.branch 1746
 (.branch 1743
 (.branch 1741
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 1744
 (.leaf (.quota 2))
 (.branch 1745
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 1749
 (.branch 1747
 (.leaf (.quota 2))
 (.branch 1748
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 1751
 (.branch 1750
 (.leaf (.matching Nonrational.OldTerminalMatches.M023.r1525))
 (.leaf (.quota 2)))
 (.branch 1752
 (.leaf (.matching Nonrational.OldTerminalMatches.M023.r1526))
 (.leaf (.quota 2))))))
 (.branch 1760
 (.branch 1756
 (.branch 1754
 (.leaf (.quota 2))
 (.branch 1755
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 1758
 (.branch 1757
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2))))
 (.branch 1763
 (.leaf (.quota 2))
 (.branch 1765
 (.branch 1764
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))))))
 (.branch 1794
 (.branch 1780
 (.branch 1773
 (.branch 1770
 (.branch 1768
 (.leaf (.quota 2))
 (.branch 1769
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 1771
 (.leaf (.matching Nonrational.OldTerminalMatches.M023.r1527))
 (.branch 1772
 (.leaf (.matching Nonrational.OldTerminalMatches.M023.r1528))
 (.leaf (.quota 2)))))
 (.leaf (.quota 2)))
 (.branch 1787
 (.leaf (.quota 2))
 (.branch 1790
 (.leaf (.quota 2))
 (.branch 1792
 (.leaf (.quota 2))
 (.branch 1793
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))))
 (.branch 1807
 (.branch 1800
 (.branch 1797
 (.branch 1795
 (.leaf (.quota 3))
 (.leaf (.quota 2)))
 (.branch 1798
 (.leaf (.quota 1))
 (.branch 1799
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 1803
 (.branch 1801
 (.leaf (.quota 2))
 (.branch 1802
 (.leaf (.quota 1))
 (.leaf (.quota 3))))
 (.branch 1805
 (.leaf (.quota 3))
 (.branch 1806
 (.leaf (.quota 3))
 (.leaf (.quota 1))))))
 (.branch 1814
 (.branch 1810
 (.branch 1808
 (.leaf (.quota 3))
 (.leaf (.quota 1)))
 (.branch 1812
 (.branch 1811
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.branch 1813
 (.leaf (.quota 3))
 (.leaf (.quota 1)))))
 (.leaf (.quota 2))))))
 (.branch 1874
 (.branch 1847
 (.branch 1834
 (.leaf (.quota 2))
 (.branch 1840
 (.branch 1837
 (.branch 1835
 (.leaf (.quota 1))
 (.branch 1836
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.branch 1843
 (.leaf (.quota 2))
 (.branch 1845
 (.branch 1844
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))))
 (.branch 1860
 (.branch 1853
 (.branch 1850
 (.branch 1848
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 1851
 (.leaf (.quota 2))
 (.branch 1852
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 1856
 (.leaf (.quota 2))
 (.branch 1858
 (.branch 1857
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 3)))))
 (.branch 1867
 (.branch 1863
 (.branch 1861
 (.leaf (.quota 3))
 (.leaf (.quota 1)))
 (.branch 1865
 (.branch 1864
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 1866
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 1870
 (.leaf (.quota 3))
 (.branch 1872
 (.branch 1871
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.leaf (.quota 1)))))))
 (.branch 1901
 (.branch 1887
 (.branch 1880
 (.branch 1877
 (.leaf (.quota 3))
 (.branch 1878
 (.leaf (.quota 3))
 (.branch 1879
 (.leaf (.quota 3))
 (.leaf (.quota 1)))))
 (.branch 1883
 (.branch 1881
 (.leaf (.quota 3))
 (.branch 1882
 (.leaf (.quota 3))
 (.leaf (.quota 2))))
 (.branch 1885
 (.branch 1884
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1)))))
 (.branch 1894
 (.branch 1890
 (.branch 1888
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 1892
 (.leaf (.quota 1))
 (.branch 1893
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 1897
 (.branch 1895
 (.leaf (.quota 2))
 (.branch 1896
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 1899
 (.leaf (.quota 2))
 (.branch 1900
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M023.r1529)))))))
 (.branch 1914
 (.branch 1907
 (.branch 1904
 (.branch 1902
 (.leaf (.quota 2))
 (.branch 1903
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M023.r1530))))
 (.branch 1905
 (.leaf (.quota 1))
 (.branch 1906
 (.leaf (.matching Nonrational.OldTerminalMatches.M023.r1531))
 (.leaf (.quota 2)))))
 (.branch 1910
 (.branch 1908
 (.leaf (.quota 2))
 (.branch 1909
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 1912
 (.branch 1911
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 1913
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 1921
 (.branch 1917
 (.leaf (.quota 2))
 (.branch 1919
 (.branch 1918
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 1920
 (.leaf (.quota 1))
 (.leaf (.matching Nonrational.OldTerminalMatches.M023.r1532)))))
 (.branch 1924
 (.branch 1922
 (.leaf (.quota 2))
 (.branch 1923
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 1926
 (.branch 1925
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 1927
 (.leaf (.matching Nonrational.OldTerminalMatches.M023.r1533))
 (.leaf (.matching Nonrational.OldTerminalMatches.M023.r1534))))))))))
 (.branch 2035
 (.branch 1981
 (.branch 1954
 (.branch 1941
 (.branch 1934
 (.branch 1931
 (.branch 1929
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 1932
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 1937
 (.leaf (.quota 2))
 (.branch 1939
 (.leaf (.quota 2))
 (.branch 1940
 (.leaf (.quota 2))
 (.leaf (.quota 3))))))
 (.branch 1947
 (.branch 1944
 (.branch 1942
 (.leaf (.quota 2))
 (.branch 1943
 (.leaf (.quota 2))
 (.leaf (.quota 3))))
 (.branch 1945
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 1950
 (.branch 1948
 (.leaf (.quota 1))
 (.branch 1949
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 1952
 (.branch 1951
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 3))))))
 (.branch 1967
 (.branch 1960
 (.branch 1957
 (.branch 1955
 (.leaf (.matching Nonrational.OldTerminalMatches.M023.r1535))
 (.leaf (.quota 2)))
 (.branch 1958
 (.leaf (.quota 2))
 (.branch 1959
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 1963
 (.leaf (.quota 2))
 (.branch 1965
 (.branch 1964
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 1966
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 1974
 (.branch 1970
 (.branch 1968
 (.leaf (.quota 2))
 (.branch 1969
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))))
 (.branch 2008
 (.branch 1994
 (.branch 1987
 (.branch 1984
 (.branch 1982
 (.leaf (.quota 2))
 (.branch 1983
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.branch 1990
 (.branch 1988
 (.leaf (.quota 2))
 (.branch 1989
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 1992
 (.leaf (.quota 2))
 (.branch 1993
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 2001
 (.branch 1997
 (.branch 1995
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 2004
 (.branch 2002
 (.leaf (.quota 2))
 (.branch 2003
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 2006
 (.leaf (.quota 2))
 (.branch 2007
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))))
 (.branch 2021
 (.branch 2014
 (.branch 2011
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 2017
 (.leaf (.quota 2))
 (.branch 2019
 (.leaf (.quota 2))
 (.branch 2020
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 2028
 (.branch 2024
 (.leaf (.quota 2))
 (.branch 2026
 (.leaf (.quota 2))
 (.branch 2027
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 2031
 (.leaf (.quota 2))
 (.branch 2033
 (.leaf (.quota 2))
 (.branch 2034
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))))))
 (.branch 2088
 (.branch 2061
 (.branch 2048
 (.leaf (.quota 2))
 (.branch 2054
 (.branch 2051
 (.branch 2049
 (.leaf (.quota 3))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 2057
 (.branch 2055
 (.leaf (.quota 3))
 (.branch 2056
 (.leaf (.quota 3))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))))
 (.branch 2074
 (.branch 2067
 (.branch 2064
 (.branch 2062
 (.leaf (.quota 2))
 (.branch 2063
 (.leaf (.quota 3))
 (.leaf (.quota 2))))
 (.branch 2065
 (.leaf (.quota 3))
 (.branch 2066
 (.leaf (.quota 2))
 (.leaf (.quota 3)))))
 (.branch 2070
 (.leaf (.quota 2))
 (.branch 2072
 (.branch 2071
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.branch 2073
 (.leaf (.quota 2))
 (.leaf (.quota 3))))))
 (.branch 2081
 (.branch 2077
 (.branch 2075
 (.leaf (.quota 2))
 (.branch 2076
 (.leaf (.quota 3))
 (.leaf (.quota 2))))
 (.branch 2079
 (.branch 2078
 (.leaf (.quota 3))
 (.leaf (.quota 2)))
 (.branch 2080
 (.leaf (.quota 2))
 (.leaf (.quota 3)))))
 (.branch 2084
 (.branch 2082
 (.leaf (.quota 2))
 (.branch 2083
 (.leaf (.quota 2))
 (.leaf (.quota 3))))
 (.leaf (.quota 2))))))
 (.branch 2115
 (.branch 2101
 (.branch 2094
 (.branch 2091
 (.branch 2089
 (.leaf (.quota 2))
 (.branch 2090
 (.leaf (.quota 3))
 (.leaf (.quota 2))))
 (.branch 2092
 (.leaf (.quota 3))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.branch 2108
 (.branch 2104
 (.branch 2102
 (.leaf (.quota 2))
 (.branch 2103
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M024.r1536))))
 (.branch 2106
 (.branch 2105
 (.leaf (.matching Nonrational.OldTerminalMatches.M024.r1537))
 (.leaf (.quota 3)))
 (.leaf (.quota 2))))
 (.branch 2111
 (.branch 2109
 (.leaf (.quota 2))
 (.branch 2110
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M024.r1538))))
 (.branch 2113
 (.branch 2112
 (.leaf (.quota 3))
 (.leaf (.quota 2)))
 (.branch 2114
 (.leaf (.quota 3))
 (.leaf (.quota 2)))))))
 (.branch 2128
 (.branch 2121
 (.branch 2118
 (.branch 2116
 (.leaf (.quota 2))
 (.branch 2117
 (.leaf (.quota 2))
 (.leaf (.quota 3))))
 (.branch 2119
 (.leaf (.matching Nonrational.OldTerminalMatches.M024.r1539))
 (.branch 2120
 (.leaf (.quota 3))
 (.leaf (.quota 2)))))
 (.branch 2124
 (.branch 2122
 (.leaf (.matching Nonrational.OldTerminalMatches.M024.r1540))
 (.leaf (.quota 2)))
 (.branch 2126
 (.branch 2125
 (.leaf (.quota 3))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))))
 (.branch 2135
 (.branch 2131
 (.branch 2129
 (.leaf (.quota 2))
 (.branch 2130
 (.leaf (.quota 1))
 (.leaf (.matching Nonrational.OldTerminalMatches.M024.r1541))))
 (.branch 2133
 (.branch 2132
 (.leaf (.matching Nonrational.OldTerminalMatches.M024.r1542))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.leaf (.quota 2))))))))
 (.branch 2356
 (.branch 2249
 (.branch 2195
 (.branch 2168
 (.branch 2155
 (.branch 2148
 (.branch 2145
 (.leaf (.quota 2))
 (.branch 2146
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.branch 2161
 (.branch 2158
 (.leaf (.quota 2))
 (.branch 2159
 (.leaf (.quota 1))
 (.branch 2160
 (.leaf (.quota 3))
 (.leaf (.quota 2)))))
 (.leaf (.quota 2))))
 (.branch 2181
 (.branch 2174
 (.branch 2171
 (.branch 2169
 (.leaf (.quota 3))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 2177
 (.branch 2175
 (.leaf (.quota 2))
 (.branch 2176
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 2179
 (.leaf (.quota 2))
 (.branch 2180
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 2188
 (.branch 2184
 (.branch 2182
 (.leaf (.quota 1))
 (.branch 2183
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 2186
 (.leaf (.quota 2))
 (.branch 2187
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 2191
 (.leaf (.quota 2))
 (.branch 2193
 (.leaf (.quota 1))
 (.branch 2194
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))))
 (.branch 2222
 (.branch 2208
 (.branch 2201
 (.branch 2198
 (.branch 2196
 (.leaf (.quota 2))
 (.branch 2197
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 2)))
 (.branch 2204
 (.branch 2202
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.branch 2206
 (.branch 2205
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.leaf (.quota 3)))))
 (.branch 2215
 (.branch 2211
 (.branch 2209
 (.leaf (.quota 3))
 (.branch 2210
 (.leaf (.quota 2))
 (.leaf (.quota 3))))
 (.leaf (.quota 1)))
 (.branch 2218
 (.branch 2216
 (.leaf (.quota 1))
 (.branch 2217
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))))
 (.branch 2235
 (.leaf (.quota 2))
 (.branch 2242
 (.leaf (.quota 2))
 (.branch 2245
 (.branch 2243
 (.leaf (.quota 2))
 (.branch 2244
 (.leaf (.quota 1))
 (.leaf (.quota 3))))
 (.branch 2247
 (.branch 2246
 (.leaf (.quota 3))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))))))
 (.branch 2302
 (.branch 2275
 (.branch 2262
 (.branch 2255
 (.branch 2252
 (.leaf (.quota 2))
 (.branch 2253
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.branch 2268
 (.branch 2265
 (.branch 2263
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.leaf (.quota 2)))
 (.branch 2271
 (.leaf (.quota 2))
 (.branch 2273
 (.leaf (.quota 3))
 (.leaf (.quota 2))))))
 (.branch 2288
 (.branch 2281
 (.leaf (.quota 2))
 (.branch 2284
 (.branch 2282
 (.leaf (.quota 1))
 (.branch 2283
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 2))))
 (.branch 2295
 (.leaf (.quota 2))
 (.branch 2298
 (.leaf (.quota 1))
 (.leaf (.quota 3))))))
 (.branch 2329
 (.branch 2315
 (.branch 2308
 (.branch 2305
 (.branch 2303
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.leaf (.quota 2)))
 (.branch 2311
 (.branch 2309
 (.leaf (.quota 2))
 (.branch 2310
 (.leaf (.quota 2))
 (.leaf (.quota 3))))
 (.branch 2313
 (.branch 2312
 (.leaf (.quota 3))
 (.leaf (.quota 1)))
 (.branch 2314
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 2322
 (.branch 2318
 (.leaf (.quota 2))
 (.branch 2320
 (.branch 2319
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.branch 2325
 (.leaf (.quota 2))
 (.branch 2327
 (.branch 2326
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))))
 (.branch 2342
 (.branch 2335
 (.branch 2332
 (.branch 2330
 (.leaf (.quota 1))
 (.branch 2331
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.branch 2338
 (.branch 2336
 (.leaf (.quota 2))
 (.branch 2337
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 2340
 (.leaf (.quota 2))
 (.branch 2341
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 2349
 (.branch 2345
 (.leaf (.quota 2))
 (.branch 2347
 (.branch 2346
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.branch 2352
 (.branch 2350
 (.leaf (.quota 2))
 (.branch 2351
 (.leaf (.quota 2))
 (.leaf (.quota 3))))
 (.branch 2354
 (.leaf (.quota 2))
 (.branch 2355
 (.leaf (.quota 3))
 (.leaf (.quota 2))))))))))
 (.branch 2463
 (.branch 2409
 (.branch 2382
 (.branch 2369
 (.branch 2362
 (.branch 2359
 (.branch 2357
 (.leaf (.quota 3))
 (.leaf (.quota 2)))
 (.branch 2360
 (.leaf (.quota 1))
 (.leaf (.quota 3))))
 (.leaf (.quota 2)))
 (.branch 2375
 (.branch 2372
 (.branch 2370
 (.leaf (.quota 3))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 2378
 (.branch 2376
 (.leaf (.quota 2))
 (.branch 2377
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 2380
 (.branch 2379
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2))))))
 (.branch 2395
 (.branch 2388
 (.branch 2385
 (.leaf (.quota 1))
 (.branch 2386
 (.leaf (.quota 2))
 (.branch 2387
 (.leaf (.quota 2))
 (.leaf (.quota 3)))))
 (.branch 2391
 (.leaf (.quota 2))
 (.branch 2393
 (.branch 2392
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.leaf (.quota 2)))))
 (.branch 2402
 (.branch 2398
 (.leaf (.quota 2))
 (.branch 2400
 (.branch 2399
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2))))
 (.branch 2405
 (.branch 2403
 (.leaf (.quota 2))
 (.branch 2404
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 2407
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))))
 (.branch 2436
 (.branch 2422
 (.branch 2415
 (.branch 2412
 (.branch 2410
 (.leaf (.quota 1))
 (.branch 2411
 (.leaf (.quota 1))
 (.leaf (.quota 3))))
 (.branch 2413
 (.leaf (.quota 3))
 (.branch 2414
 (.leaf (.quota 1))
 (.leaf (.quota 3)))))
 (.branch 2418
 (.leaf (.quota 3))
 (.branch 2420
 (.branch 2419
 (.leaf (.quota 1))
 (.leaf (.quota 3)))
 (.branch 2421
 (.leaf (.quota 1))
 (.leaf (.quota 3))))))
 (.branch 2429
 (.branch 2425
 (.branch 2423
 (.leaf (.quota 1))
 (.branch 2424
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 2427
 (.branch 2426
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.branch 2428
 (.leaf (.quota 2))
 (.leaf (.quota 3)))))
 (.branch 2432
 (.branch 2430
 (.leaf (.quota 1))
 (.branch 2431
 (.leaf (.quota 1))
 (.leaf (.quota 3))))
 (.branch 2434
 (.leaf (.quota 2))
 (.branch 2435
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))))
 (.branch 2449
 (.branch 2442
 (.leaf (.quota 2))
 (.branch 2445
 (.leaf (.quota 2))
 (.branch 2447
 (.leaf (.quota 3))
 (.leaf (.quota 2)))))
 (.branch 2456
 (.branch 2452
 (.branch 2450
 (.leaf (.quota 2))
 (.branch 2451
 (.leaf (.quota 1))
 (.leaf (.quota 3))))
 (.branch 2454
 (.branch 2453
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.branch 2459
 (.leaf (.quota 2))
 (.branch 2461
 (.leaf (.quota 2))
 (.branch 2462
 (.leaf (.quota 2))
 (.leaf (.quota 3)))))))))
 (.branch 2517
 (.branch 2490
 (.branch 2476
 (.branch 2469
 (.branch 2466
 (.branch 2464
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 2467
 (.leaf (.quota 2))
 (.branch 2468
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 2472
 (.leaf (.quota 2))
 (.branch 2474
 (.leaf (.quota 1))
 (.branch 2475
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 2483
 (.branch 2479
 (.branch 2477
 (.leaf (.quota 1))
 (.branch 2478
 (.leaf (.quota 1))
 (.leaf (.quota 3))))
 (.branch 2481
 (.branch 2480
 (.leaf (.quota 3))
 (.leaf (.quota 1)))
 (.leaf (.quota 3))))
 (.branch 2486
 (.branch 2484
 (.leaf (.quota 1))
 (.branch 2485
 (.leaf (.quota 1))
 (.leaf (.quota 3))))
 (.leaf (.quota 2)))))
 (.branch 2503
 (.branch 2496
 (.branch 2493
 (.leaf (.quota 2))
 (.branch 2494
 (.leaf (.quota 1))
 (.branch 2495
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 2499
 (.branch 2497
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 2501
 (.branch 2500
 (.leaf (.quota 3))
 (.leaf (.quota 2)))
 (.branch 2502
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 2510
 (.branch 2506
 (.branch 2504
 (.leaf (.quota 1))
 (.branch 2505
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 2508
 (.branch 2507
 (.leaf (.quota 3))
 (.leaf (.quota 2)))
 (.branch 2509
 (.leaf (.quota 2))
 (.leaf (.quota 3)))))
 (.branch 2513
 (.branch 2511
 (.leaf (.quota 3))
 (.branch 2512
 (.leaf (.quota 3))
 (.leaf (.quota 2))))
 (.branch 2515
 (.branch 2514
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.branch 2516
 (.leaf (.quota 2))
 (.leaf (.quota 3))))))))
 (.branch 2544
 (.branch 2530
 (.branch 2523
 (.branch 2520
 (.branch 2518
 (.leaf (.quota 1))
 (.branch 2519
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 2521
 (.leaf (.quota 2))
 (.leaf (.quota 3))))
 (.branch 2526
 (.branch 2524
 (.leaf (.quota 3))
 (.branch 2525
 (.leaf (.quota 3))
 (.leaf (.quota 1))))
 (.branch 2528
 (.branch 2527
 (.leaf (.quota 1))
 (.leaf (.quota 3)))
 (.branch 2529
 (.leaf (.quota 3))
 (.leaf (.quota 2))))))
 (.branch 2537
 (.branch 2533
 (.branch 2531
 (.leaf (.quota 2))
 (.branch 2532
 (.leaf (.quota 1))
 (.leaf (.quota 3))))
 (.branch 2535
 (.branch 2534
 (.leaf (.quota 3))
 (.leaf (.quota 1)))
 (.branch 2536
 (.leaf (.quota 2))
 (.leaf (.quota 3)))))
 (.branch 2540
 (.branch 2538
 (.leaf (.quota 2))
 (.branch 2539
 (.leaf (.quota 1))
 (.leaf (.quota 3))))
 (.branch 2542
 (.leaf (.quota 2))
 (.branch 2543
 (.leaf (.quota 1))
 (.leaf (.quota 3)))))))
 (.branch 2557
 (.branch 2550
 (.branch 2547
 (.branch 2545
 (.leaf (.quota 2))
 (.branch 2546
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.branch 2553
 (.branch 2551
 (.leaf (.quota 2))
 (.branch 2552
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 2555
 (.leaf (.quota 2))
 (.branch 2556
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 2564
 (.branch 2560
 (.branch 2558
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.branch 2562
 (.branch 2561
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 2563
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.leaf (.quota 2)))))))))
 (.branch 2999
 (.branch 2785
 (.branch 2678
 (.branch 2624
 (.branch 2597
 (.branch 2584
 (.branch 2577
 (.branch 2574
 (.branch 2572
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.branch 2575
 (.leaf (.quota 2))
 (.branch 2576
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 2580
 (.leaf (.quota 2))
 (.branch 2582
 (.branch 2581
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))))
 (.branch 2590
 (.branch 2587
 (.leaf (.quota 2))
 (.branch 2588
 (.leaf (.quota 2))
 (.branch 2589
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 2593
 (.branch 2591
 (.leaf (.quota 1))
 (.branch 2592
 (.leaf (.quota 2))
 (.leaf (.quota 3))))
 (.branch 2595
 (.branch 2594
 (.leaf (.quota 1))
 (.leaf (.quota 3)))
 (.branch 2596
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))))
 (.branch 2610
 (.branch 2603
 (.branch 2600
 (.branch 2598
 (.leaf (.quota 1))
 (.branch 2599
 (.leaf (.quota 1))
 (.leaf (.quota 3))))
 (.branch 2601
 (.leaf (.quota 3))
 (.leaf (.quota 2))))
 (.branch 2606
 (.branch 2604
 (.leaf (.quota 1))
 (.branch 2605
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 2608
 (.branch 2607
 (.leaf (.quota 1))
 (.leaf (.quota 3)))
 (.leaf (.quota 2)))))
 (.branch 2617
 (.branch 2613
 (.branch 2611
 (.leaf (.quota 1))
 (.branch 2612
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 2615
 (.branch 2614
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 2616
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 2620
 (.branch 2618
 (.leaf (.quota 2))
 (.branch 2619
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 2))))))
 (.branch 2651
 (.branch 2637
 (.branch 2630
 (.branch 2627
 (.leaf (.quota 2))
 (.branch 2628
 (.leaf (.quota 1))
 (.branch 2629
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 2633
 (.branch 2631
 (.leaf (.quota 3))
 (.branch 2632
 (.leaf (.quota 3))
 (.leaf (.quota 2))))
 (.leaf (.quota 2))))
 (.branch 2644
 (.branch 2640
 (.branch 2638
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.branch 2664
 (.branch 2657
 (.leaf (.quota 2))
 (.branch 2660
 (.leaf (.quota 2))
 (.branch 2662
 (.branch 2661
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))))
 (.branch 2671
 (.branch 2667
 (.leaf (.quota 2))
 (.branch 2669
 (.branch 2668
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.branch 2674
 (.branch 2672
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 2676
 (.leaf (.quota 2))
 (.branch 2677
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))))))
 (.branch 2731
 (.branch 2704
 (.branch 2691
 (.branch 2684
 (.leaf (.quota 2))
 (.branch 2687
 (.branch 2685
 (.leaf (.quota 2))
 (.branch 2686
 (.leaf (.quota 3))
 (.leaf (.quota 2))))
 (.branch 2689
 (.branch 2688
 (.leaf (.matching Nonrational.OldTerminalMatches.M024.r1543))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))))
 (.branch 2697
 (.branch 2694
 (.leaf (.quota 2))
 (.branch 2695
 (.leaf (.quota 2))
 (.branch 2696
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M024.r1544)))))
 (.branch 2700
 (.branch 2698
 (.leaf (.matching Nonrational.OldTerminalMatches.M024.r1545))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))))
 (.branch 2717
 (.branch 2710
 (.branch 2707
 (.branch 2705
 (.leaf (.quota 2))
 (.branch 2706
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 2708
 (.leaf (.quota 1))
 (.branch 2709
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.branch 2758
 (.branch 2744
 (.branch 2737
 (.branch 2734
 (.branch 2732
 (.leaf (.matching Nonrational.OldTerminalMatches.M024.r1546))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 2740
 (.leaf (.quota 2))
 (.branch 2742
 (.branch 2741
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))))
 (.branch 2751
 (.branch 2747
 (.leaf (.quota 2))
 (.branch 2749
 (.leaf (.quota 2))
 (.branch 2750
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.leaf (.quota 2))))
 (.branch 2771
 (.branch 2764
 (.branch 2761
 (.branch 2759
 (.leaf (.quota 2))
 (.branch 2760
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 2)))
 (.branch 2767
 (.leaf (.quota 2))
 (.branch 2769
 (.branch 2768
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 2770
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 2778
 (.branch 2774
 (.leaf (.quota 2))
 (.branch 2776
 (.branch 2775
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 2777
 (.leaf (.quota 2))
 (.leaf (.quota 3)))))
 (.branch 2781
 (.branch 2779
 (.leaf (.quota 2))
 (.branch 2780
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 2783
 (.branch 2782
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))))))))
 (.branch 2892
 (.branch 2838
 (.branch 2811
 (.branch 2798
 (.branch 2791
 (.branch 2788
 (.branch 2786
 (.leaf (.quota 1))
 (.branch 2787
 (.leaf (.quota 3))
 (.leaf (.quota 2))))
 (.branch 2789
 (.leaf (.quota 2))
 (.branch 2790
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 2794
 (.branch 2792
 (.leaf (.quota 1))
 (.branch 2793
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.branch 2824
 (.branch 2817
 (.branch 2814
 (.branch 2812
 (.leaf (.quota 2))
 (.branch 2813
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 2815
 (.leaf (.quota 2))
 (.branch 2816
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 2820
 (.leaf (.quota 2))
 (.branch 2822
 (.branch 2821
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 2823
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 2831
 (.branch 2827
 (.branch 2825
 (.leaf (.quota 3))
 (.leaf (.quota 1)))
 (.branch 2829
 (.leaf (.quota 1))
 (.branch 2830
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 2834
 (.leaf (.quota 2))
 (.branch 2836
 (.branch 2835
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 2837
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))))
 (.branch 2865
 (.branch 2851
 (.branch 2844
 (.branch 2841
 (.branch 2839
 (.leaf (.quota 2))
 (.branch 2840
 (.leaf (.quota 2))
 (.leaf (.quota 3))))
 (.branch 2842
 (.leaf (.quota 2))
 (.branch 2843
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 2847
 (.branch 2845
 (.leaf (.quota 2))
 (.branch 2846
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 2849
 (.branch 2848
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))))
 (.branch 2858
 (.branch 2854
 (.branch 2852
 (.leaf (.quota 2))
 (.branch 2853
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 2856
 (.branch 2855
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2))))
 (.branch 2861
 (.leaf (.quota 2))
 (.branch 2863
 (.leaf (.quota 2))
 (.branch 2864
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))))
 (.branch 2878
 (.branch 2871
 (.leaf (.quota 2))
 (.branch 2874
 (.leaf (.quota 2))
 (.branch 2876
 (.branch 2875
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))))
 (.branch 2885
 (.branch 2881
 (.leaf (.quota 2))
 (.branch 2883
 (.leaf (.quota 1))
 (.branch 2884
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.leaf (.quota 2))))))
 (.branch 2945
 (.branch 2918
 (.branch 2905
 (.leaf (.quota 2))
 (.branch 2911
 (.branch 2908
 (.branch 2906
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 2909
 (.leaf (.quota 2))
 (.branch 2910
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.leaf (.quota 2))))
 (.branch 2931
 (.branch 2924
 (.branch 2921
 (.branch 2919
 (.leaf (.quota 3))
 (.branch 2920
 (.leaf (.matching Nonrational.OldTerminalMatches.M024.r1547))
 (.leaf (.matching Nonrational.OldTerminalMatches.M024.r1548))))
 (.branch 2922
 (.leaf (.quota 2))
 (.branch 2923
 (.leaf (.quota 1))
 (.leaf (.quota 3)))))
 (.branch 2927
 (.branch 2925
 (.leaf (.quota 3))
 (.leaf (.quota 2)))
 (.branch 2929
 (.branch 2928
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1)))))
 (.branch 2938
 (.branch 2934
 (.branch 2932
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))
 (.branch 2941
 (.branch 2939
 (.leaf (.quota 1))
 (.branch 2940
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 2943
 (.leaf (.quota 2))
 (.branch 2944
 (.leaf (.quota 1))
 (.leaf .euler)))))))
 (.branch 2972
 (.branch 2958
 (.branch 2951
 (.branch 2948
 (.branch 2946
 (.leaf (.matching Nonrational.OldTerminalMatches.M024.r1549))
 (.leaf (.quota 2)))
 (.branch 2949
 (.leaf (.quota 1))
 (.branch 2950
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 2954
 (.branch 2952
 (.leaf (.quota 2))
 (.branch 2953
 (.leaf (.matching Nonrational.OldTerminalMatches.M024.r1550))
 (.leaf (.quota 2))))
 (.branch 2956
 (.branch 2955
 (.leaf (.matching Nonrational.OldTerminalMatches.M024.r1551))
 (.leaf (.quota 2)))
 (.branch 2957
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 2965
 (.branch 2961
 (.branch 2959
 (.leaf (.quota 1))
 (.branch 2960
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 2963
 (.leaf (.quota 1))
 (.branch 2964
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 2968
 (.branch 2966
 (.leaf (.quota 2))
 (.branch 2967
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 2970
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 2985
 (.branch 2978
 (.branch 2975
 (.leaf (.quota 2))
 (.branch 2976
 (.leaf (.matching Nonrational.OldTerminalMatches.M024.r1552))
 (.branch 2977
 (.leaf (.matching Nonrational.OldTerminalMatches.M024.r1553))
 (.leaf (.quota 1)))))
 (.branch 2981
 (.branch 2979
 (.leaf (.quota 2))
 (.branch 2980
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 2983
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 2992
 (.branch 2988
 (.leaf (.quota 2))
 (.branch 2990
 (.leaf (.quota 2))
 (.branch 2991
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 2995
 (.branch 2993
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))))))))
 (.branch 3213
 (.branch 3106
 (.branch 3052
 (.branch 3025
 (.branch 3012
 (.branch 3005
 (.branch 3002
 (.branch 3000
 (.leaf (.matching Nonrational.OldTerminalMatches.M024.r1554))
 (.leaf (.quota 2)))
 (.branch 3003
 (.leaf (.quota 2))
 (.branch 3004
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 3008
 (.leaf (.quota 2))
 (.branch 3010
 (.leaf (.quota 2))
 (.branch 3011
 (.leaf (.matching Nonrational.OldTerminalMatches.M024.r1555))
 (.leaf (.matching Nonrational.OldTerminalMatches.M024.r1556))))))
 (.branch 3018
 (.branch 3015
 (.branch 3013
 (.leaf (.matching Nonrational.OldTerminalMatches.M024.r1557))
 (.leaf (.quota 2)))
 (.branch 3016
 (.leaf (.quota 2))
 (.branch 3017
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 3021
 (.branch 3019
 (.leaf (.quota 1))
 (.branch 3020
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 3023
 (.branch 3022
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))))
 (.branch 3038
 (.branch 3031
 (.branch 3028
 (.branch 3026
 (.leaf (.quota 2))
 (.branch 3027
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 2)))
 (.branch 3034
 (.leaf (.quota 2))
 (.branch 3036
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 3045
 (.leaf (.quota 2))
 (.branch 3048
 (.branch 3046
 (.leaf (.matching Nonrational.OldTerminalMatches.M024.r1558))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))))
 (.branch 3079
 (.branch 3065
 (.branch 3058
 (.branch 3055
 (.branch 3053
 (.leaf (.quota 2))
 (.branch 3054
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.branch 3061
 (.leaf (.quota 2))
 (.branch 3063
 (.branch 3062
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 3064
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 3072
 (.branch 3068
 (.branch 3066
 (.leaf (.quota 2))
 (.branch 3067
 (.leaf (.quota 3))
 (.leaf (.quota 1))))
 (.branch 3070
 (.branch 3069
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 3071
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 3075
 (.branch 3073
 (.leaf (.quota 2))
 (.branch 3074
 (.leaf (.matching Nonrational.OldTerminalMatches.M024.r1559))
 (.leaf (.matching Nonrational.OldTerminalMatches.M024.r1560))))
 (.branch 3077
 (.branch 3076
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 3078
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))))
 (.branch 3092
 (.branch 3085
 (.branch 3082
 (.branch 3080
 (.leaf (.quota 2))
 (.branch 3081
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M024.r1561))))
 (.branch 3083
 (.leaf (.quota 2))
 (.branch 3084
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 3088
 (.branch 3086
 (.leaf (.matching Nonrational.OldTerminalMatches.M024.r1562))
 (.branch 3087
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M024.r1563))))
 (.branch 3090
 (.leaf (.quota 2))
 (.branch 3091
 (.leaf (.matching Nonrational.OldTerminalMatches.M024.r1564))
 (.leaf (.quota 2))))))
 (.branch 3099
 (.branch 3095
 (.branch 3093
 (.leaf (.quota 2))
 (.branch 3094
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M024.r1565))))
 (.leaf (.quota 2)))
 (.branch 3102
 (.branch 3100
 (.leaf (.quota 2))
 (.branch 3101
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 3104
 (.branch 3103
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2))))))))
 (.branch 3159
 (.branch 3132
 (.branch 3119
 (.branch 3112
 (.branch 3109
 (.branch 3107
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 3110
 (.leaf (.matching Nonrational.OldTerminalMatches.M024.r1566))
 (.branch 3111
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 3115
 (.branch 3113
 (.leaf (.quota 1))
 (.branch 3114
 (.leaf (.matching Nonrational.OldTerminalMatches.M024.r1567))
 (.leaf (.matching Nonrational.OldTerminalMatches.M024.r1568))))
 (.branch 3117
 (.branch 3116
 (.leaf (.matching Nonrational.OldTerminalMatches.M024.r1569))
 (.leaf (.quota 1)))
 (.branch 3118
 (.leaf (.matching Nonrational.OldTerminalMatches.M024.r1570))
 (.leaf (.quota 2))))))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 3186
 (.branch 3172
 (.branch 3165
 (.branch 3162
 (.leaf (.quota 2))
 (.branch 3163
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 3168
 (.leaf (.quota 2))
 (.branch 3170
 (.branch 3169
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 3171
 (.leaf (.matching Nonrational.OldTerminalMatches.M024.r1571))
 (.leaf (.quota 1))))))
 (.branch 3179
 (.branch 3175
 (.branch 3173
 (.leaf (.matching Nonrational.OldTerminalMatches.M024.r1572))
 (.branch 3174
 (.leaf (.matching Nonrational.OldTerminalMatches.M024.r1573))
 (.leaf (.quota 1))))
 (.branch 3177
 (.branch 3176
 (.leaf (.matching Nonrational.OldTerminalMatches.M024.r1574))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.leaf (.quota 2))))
 (.branch 3199
 (.branch 3192
 (.leaf (.quota 2))
 (.branch 3195
 (.branch 3193
 (.leaf (.quota 2))
 (.branch 3194
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M024.r1575))))
 (.branch 3197
 (.branch 3196
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M024.r1576)))
 (.branch 3198
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 3206
 (.branch 3202
 (.branch 3200
 (.leaf (.matching Nonrational.OldTerminalMatches.M024.r1577))
 (.branch 3201
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 3204
 (.leaf (.quota 1))
 (.branch 3205
 (.leaf (.matching Nonrational.OldTerminalMatches.M024.r1578))
 (.leaf (.quota 2)))))
 (.branch 3209
 (.leaf (.quota 2))
 (.branch 3211
 (.branch 3210
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 3212
 (.leaf (.quota 1))
 (.leaf (.matching Nonrational.OldTerminalMatches.M024.r1579))))))))))
 (.branch 3320
 (.branch 3266
 (.branch 3239
 (.branch 3226
 (.branch 3219
 (.branch 3216
 (.branch 3214
 (.leaf (.quota 2))
 (.branch 3215
 (.leaf (.matching Nonrational.OldTerminalMatches.M024.r1580))
 (.leaf (.quota 2))))
 (.branch 3217
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 3222
 (.branch 3220
 (.leaf (.quota 2))
 (.branch 3221
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 3224
 (.branch 3223
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 3225
 (.leaf (.matching Nonrational.OldTerminalMatches.M024.r1581))
 (.leaf (.quota 2))))))
 (.branch 3232
 (.branch 3229
 (.branch 3227
 (.leaf (.quota 1))
 (.branch 3228
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M024.r1582))))
 (.branch 3230
 (.leaf (.quota 1))
 (.branch 3231
 (.leaf (.matching Nonrational.OldTerminalMatches.M024.r1583))
 (.leaf (.matching Nonrational.OldTerminalMatches.M024.r1584)))))
 (.leaf (.quota 2))))
 (.branch 3252
 (.branch 3245
 (.branch 3242
 (.branch 3240
 (.leaf (.quota 2))
 (.branch 3241
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 3243
 (.leaf (.quota 1))
 (.branch 3244
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 3248
 (.branch 3246
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.branch 3259
 (.branch 3255
 (.branch 3253
 (.leaf (.quota 2))
 (.branch 3254
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 2)))
 (.branch 3262
 (.leaf (.quota 1))
 (.branch 3264
 (.branch 3263
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))))))
 (.branch 3293
 (.branch 3279
 (.branch 3272
 (.branch 3269
 (.leaf (.quota 2))
 (.branch 3270
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 3275
 (.leaf (.quota 2))
 (.branch 3277
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 3286
 (.branch 3282
 (.leaf (.quota 2))
 (.branch 3284
 (.branch 3283
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 3285
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 3289
 (.leaf (.quota 2))
 (.branch 3291
 (.leaf (.quota 2))
 (.branch 3292
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))))
 (.branch 3306
 (.branch 3299
 (.branch 3296
 (.branch 3294
 (.leaf (.quota 1))
 (.branch 3295
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 3313
 (.branch 3309
 (.branch 3307
 (.leaf (.quota 2))
 (.branch 3308
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 3311
 (.branch 3310
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 3312
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 3316
 (.branch 3314
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 3318
 (.leaf (.quota 1))
 (.branch 3319
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))))))
 (.branch 3374
 (.branch 3347
 (.branch 3333
 (.branch 3326
 (.branch 3323
 (.branch 3321
 (.leaf (.quota 1))
 (.branch 3322
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 3324
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 3329
 (.leaf (.quota 2))
 (.branch 3331
 (.leaf (.quota 2))
 (.branch 3332
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 3340
 (.branch 3336
 (.branch 3334
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 3338
 (.leaf (.quota 1))
 (.branch 3339
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 3343
 (.branch 3341
 (.leaf (.quota 2))
 (.branch 3342
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))))
 (.branch 3360
 (.branch 3353
 (.leaf (.quota 2))
 (.branch 3356
 (.leaf (.quota 2))
 (.branch 3358
 (.leaf (.quota 2))
 (.branch 3359
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 3367
 (.branch 3363
 (.branch 3361
 (.leaf (.quota 2))
 (.branch 3362
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 3365
 (.branch 3364
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.branch 3370
 (.branch 3368
 (.leaf (.quota 2))
 (.branch 3369
 (.leaf (.quota 1))
 (.leaf (.quota 3))))
 (.branch 3372
 (.branch 3371
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 3373
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))))
 (.branch 3401
 (.branch 3387
 (.branch 3380
 (.branch 3377
 (.branch 3375
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))
 (.branch 3383
 (.branch 3381
 (.leaf (.quota 1))
 (.leaf (.quota 3)))
 (.branch 3385
 (.branch 3384
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))))
 (.branch 3394
 (.branch 3390
 (.branch 3388
 (.leaf (.quota 2))
 (.branch 3389
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 3392
 (.branch 3391
 (.leaf (.quota 1))
 (.leaf (.quota 3)))
 (.branch 3393
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 3397
 (.branch 3395
 (.leaf (.quota 3))
 (.branch 3396
 (.leaf (.quota 3))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))))
 (.branch 3414
 (.branch 3407
 (.branch 3404
 (.branch 3402
 (.leaf (.quota 3))
 (.branch 3403
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 3405
 (.leaf (.quota 2))
 (.branch 3406
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 3410
 (.branch 3408
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 3412
 (.branch 3411
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.branch 3413
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 3421
 (.branch 3417
 (.branch 3415
 (.leaf (.quota 3))
 (.branch 3416
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 3419
 (.leaf (.quota 3))
 (.leaf (.quota 1))))
 (.branch 3424
 (.leaf (.quota 1))
 (.branch 3426
 (.leaf (.quota 1))
 (.branch 3427
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))))))))))
def disposition (j : Fin leafCount) := dispositionTable.get j.val
def dispositionTest (i : Nat) : Bool := RawLeafCertificate.check quota
  ((rawLeaves i).map Papers.RationalityTen.RootedCaches.RootedSixBase03.rawCells) (dispositionTable.get i)

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724

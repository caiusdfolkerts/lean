module
prelude
public import RootedSubsumedForest0870Data
public import RawLeafCertificate
public import OldTerminalMatches.M025
public import OldTerminalMatches.M026

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0870
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 417
 (.branch 208
 (.branch 104
 (.branch 52
 (.branch 26
 (.leaf (.quota 2))
 (.branch 39
 (.branch 32
 (.branch 29
 (.branch 27
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))
 (.branch 35
 (.branch 33
 (.leaf (.quota 2))
 (.branch 34
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 2))))
 (.branch 45
 (.branch 42
 (.leaf (.quota 2))
 (.branch 43
 (.leaf (.quota 1))
 (.branch 44
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 48
 (.branch 46
 (.leaf (.quota 1))
 (.branch 47
 (.leaf (.quota 2))
 (.leaf .euler)))
 (.branch 50
 (.branch 49
 (.leaf (.quota 2))
 (.leaf .euler))
 (.leaf (.quota 2)))))))
 (.branch 78
 (.leaf (.quota 2))
 (.branch 91
 (.branch 84
 (.branch 81
 (.branch 79
 (.leaf (.quota 2))
 (.branch 80
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M025.r1663))))
 (.leaf (.quota 2)))
 (.branch 87
 (.leaf (.quota 2))
 (.branch 89
 (.branch 88
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 90
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 97
 (.branch 94
 (.branch 92
 (.leaf (.quota 1))
 (.branch 93
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 95
 (.leaf (.quota 2))
 (.branch 96
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 100
 (.branch 98
 (.leaf .euler)
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))))))
 (.branch 156
 (.branch 130
 (.branch 117
 (.branch 110
 (.branch 107
 (.leaf (.quota 2))
 (.branch 108
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 113
 (.branch 111
 (.leaf (.quota 2))
 (.branch 112
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 2))))
 (.branch 123
 (.branch 120
 (.branch 118
 (.leaf (.matching Nonrational.OldTerminalMatches.M026.r1664))
 (.branch 119
 (.leaf (.matching Nonrational.OldTerminalMatches.M026.r1665))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.branch 143
 (.branch 136
 (.branch 133
 (.branch 131
 (.leaf (.quota 2))
 (.branch 132
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 2)))
 (.branch 139
 (.leaf (.quota 2))
 (.branch 141
 (.branch 140
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 142
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 149
 (.branch 146
 (.leaf (.quota 2))
 (.branch 147
 (.leaf (.quota 2))
 (.branch 148
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 152
 (.branch 150
 (.leaf (.quota 2))
 (.branch 151
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 154
 (.branch 153
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))))))
 (.branch 182
 (.branch 169
 (.leaf (.quota 2))
 (.branch 175
 (.branch 172
 (.branch 170
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 173
 (.leaf (.quota 2))
 (.branch 174
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 178
 (.branch 176
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 180
 (.branch 179
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))))
 (.branch 195
 (.branch 188
 (.branch 185
 (.branch 183
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))))
 (.branch 312
 (.branch 260
 (.branch 234
 (.branch 221
 (.branch 214
 (.leaf (.quota 2))
 (.branch 217
 (.branch 215
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 219
 (.branch 218
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))))
 (.branch 227
 (.leaf (.quota 2))
 (.branch 230
 (.branch 228
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))))
 (.branch 247
 (.branch 240
 (.branch 237
 (.branch 235
 (.leaf (.quota 2))
 (.branch 236
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 238
 (.leaf (.quota 2))
 (.branch 239
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 243
 (.branch 241
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 245
 (.branch 244
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 246
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 253
 (.leaf (.quota 2))
 (.branch 256
 (.branch 254
 (.leaf (.quota 2))
 (.branch 255
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 2))))))
 (.branch 286
 (.branch 273
 (.branch 266
 (.leaf (.quota 2))
 (.branch 269
 (.branch 267
 (.leaf (.quota 2))
 (.branch 268
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 271
 (.branch 270
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))))
 (.leaf (.quota 2)))
 (.branch 299
 (.branch 292
 (.branch 289
 (.branch 287
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 305
 (.branch 302
 (.leaf (.quota 2))
 (.branch 303
 (.leaf (.quota 2))
 (.branch 304
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 308
 (.branch 306
 (.leaf (.quota 1))
 (.branch 307
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 2)))))))
 (.branch 364
 (.branch 338
 (.branch 325
 (.branch 318
 (.branch 315
 (.branch 313
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 316
 (.leaf .euler)
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 351
 (.leaf (.quota 2))
 (.branch 357
 (.branch 354
 (.branch 352
 (.leaf (.quota 1))
 (.branch 353
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 355
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 360
 (.leaf (.quota 2))
 (.branch 362
 (.leaf (.quota 2))
 (.branch 363
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))))
 (.branch 390
 (.branch 377
 (.branch 370
 (.leaf (.quota 2))
 (.branch 373
 (.branch 371
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 375
 (.branch 374
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))))
 (.branch 383
 (.branch 380
 (.branch 378
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))
 (.branch 386
 (.branch 384
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))))
 (.branch 403
 (.branch 396
 (.branch 393
 (.leaf (.quota 2))
 (.branch 394
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 399
 (.branch 397
 (.leaf (.matching Nonrational.OldTerminalMatches.M026.r1666))
 (.branch 398
 (.leaf (.matching Nonrational.OldTerminalMatches.M026.r1667))
 (.leaf (.matching Nonrational.OldTerminalMatches.M026.r1668))))
 (.leaf (.quota 2))))
 (.branch 410
 (.leaf (.quota 2))
 (.branch 413
 (.branch 411
 (.leaf (.quota 2))
 (.branch 412
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))))))))
 (.branch 626
 (.branch 521
 (.branch 469
 (.branch 443
 (.branch 430
 (.branch 423
 (.branch 420
 (.branch 418
 (.leaf (.quota 2))
 (.branch 419
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.branch 426
 (.leaf (.quota 2))
 (.branch 428
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 436
 (.branch 433
 (.branch 431
 (.leaf (.quota 2))
 (.branch 432
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 434
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 439
 (.branch 437
 (.leaf (.quota 2))
 (.branch 438
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 441
 (.branch 440
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))))
 (.branch 456
 (.branch 449
 (.branch 446
 (.branch 444
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 447
 (.leaf (.quota 2))
 (.branch 448
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 452
 (.leaf (.quota 2))
 (.branch 454
 (.branch 453
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))))
 (.branch 462
 (.branch 459
 (.branch 457
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 465
 (.leaf (.quota 2))
 (.branch 467
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))))
 (.branch 495
 (.branch 482
 (.branch 475
 (.leaf (.quota 2))
 (.branch 478
 (.leaf (.quota 2))
 (.branch 480
 (.branch 479
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))))
 (.branch 488
 (.branch 485
 (.branch 483
 (.leaf (.quota 2))
 (.branch 484
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.branch 491
 (.branch 489
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 493
 (.leaf (.quota 2))
 (.branch 494
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))))
 (.branch 508
 (.branch 501
 (.branch 498
 (.branch 496
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 499
 (.leaf (.quota 2))
 (.branch 500
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 504
 (.branch 502
 (.leaf (.quota 2))
 (.branch 503
 (.leaf (.matching Nonrational.OldTerminalMatches.M026.r1669))
 (.leaf (.quota 2))))
 (.leaf (.quota 2))))
 (.branch 514
 (.branch 511
 (.leaf (.quota 2))
 (.branch 512
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 2))))))
 (.branch 573
 (.branch 547
 (.branch 534
 (.branch 527
 (.branch 524
 (.leaf (.quota 1))
 (.branch 525
 (.leaf (.quota 1))
 (.branch 526
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 530
 (.branch 528
 (.leaf (.quota 2))
 (.branch 529
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 532
 (.branch 531
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))))
 (.branch 540
 (.branch 537
 (.leaf (.quota 2))
 (.branch 538
 (.leaf (.quota 1))
 (.branch 539
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 543
 (.branch 541
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 545
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 560
 (.branch 553
 (.branch 550
 (.leaf (.quota 2))
 (.branch 551
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 556
 (.branch 554
 (.leaf (.quota 2))
 (.branch 555
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 558
 (.branch 557
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 559
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 566
 (.branch 563
 (.branch 561
 (.leaf (.quota 1))
 (.branch 562
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 564
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 569
 (.leaf (.quota 2))
 (.branch 571
 (.branch 570
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))))))
 (.branch 599
 (.branch 586
 (.branch 579
 (.leaf (.quota 2))
 (.branch 582
 (.branch 580
 (.leaf (.quota 2))
 (.branch 581
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 584
 (.branch 583
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 585
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 592
 (.leaf (.quota 2))
 (.branch 595
 (.leaf (.quota 2))
 (.branch 597
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 612
 (.leaf (.quota 2))
 (.branch 619
 (.leaf (.quota 2))
 (.branch 622
 (.branch 620
 (.leaf (.quota 2))
 (.branch 621
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 624
 (.branch 623
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))))))))
 (.branch 730
 (.branch 678
 (.branch 652
 (.branch 639
 (.branch 632
 (.leaf (.quota 2))
 (.branch 635
 (.branch 633
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 637
 (.branch 636
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1)))))
 (.branch 645
 (.branch 642
 (.leaf (.quota 1))
 (.branch 643
 (.leaf (.quota 1))
 (.branch 644
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 648
 (.branch 646
 (.leaf (.quota 2))
 (.branch 647
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 650
 (.branch 649
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2))))))
 (.branch 665
 (.branch 658
 (.branch 655
 (.leaf (.quota 2))
 (.branch 656
 (.leaf (.quota 2))
 (.branch 657
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 661
 (.branch 659
 (.leaf (.quota 2))
 (.branch 660
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 663
 (.leaf (.quota 2))
 (.branch 664
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 671
 (.branch 668
 (.branch 666
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 669
 (.leaf (.quota 2))
 (.branch 670
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 674
 (.leaf (.quota 2))
 (.branch 676
 (.leaf (.quota 2))
 (.branch 677
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M026.r1670))))))))
 (.branch 704
 (.leaf (.quota 2))
 (.branch 717
 (.branch 710
 (.branch 707
 (.branch 705
 (.leaf (.quota 2))
 (.branch 706
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M026.r1671))))
 (.branch 708
 (.leaf (.quota 1))
 (.branch 709
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 713
 (.branch 711
 (.leaf (.quota 2))
 (.branch 712
 (.leaf (.matching Nonrational.OldTerminalMatches.M026.r1672))
 (.leaf (.quota 1))))
 (.leaf (.quota 2))))
 (.branch 723
 (.leaf (.quota 2))
 (.branch 726
 (.branch 724
 (.leaf (.quota 2))
 (.branch 725
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))))))
 (.branch 782
 (.branch 756
 (.branch 743
 (.branch 736
 (.branch 733
 (.branch 731
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 739
 (.branch 737
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 741
 (.leaf (.quota 2))
 (.branch 742
 (.leaf (.matching Nonrational.OldTerminalMatches.M026.r1673))
 (.leaf (.quota 1))))))
 (.branch 749
 (.branch 746
 (.branch 744
 (.leaf (.quota 2))
 (.branch 745
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 747
 (.leaf (.quota 2))
 (.branch 748
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 752
 (.leaf (.quota 2))
 (.branch 754
 (.leaf (.quota 2))
 (.branch 755
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))))
 (.branch 769
 (.branch 762
 (.leaf (.quota 2))
 (.branch 765
 (.branch 763
 (.leaf (.quota 1))
 (.branch 764
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 767
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 775
 (.branch 772
 (.branch 770
 (.leaf (.quota 2))
 (.branch 771
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 773
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 778
 (.leaf (.quota 1))
 (.branch 780
 (.branch 779
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))))))
 (.branch 808
 (.branch 795
 (.branch 788
 (.branch 785
 (.leaf (.quota 2))
 (.branch 786
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 791
 (.branch 789
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 793
 (.branch 792
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1)))))
 (.branch 801
 (.branch 798
 (.branch 796
 (.leaf (.quota 2))
 (.branch 797
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1)))
 (.branch 804
 (.leaf (.quota 1))
 (.branch 806
 (.branch 805
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2))))))
 (.branch 821
 (.branch 814
 (.branch 811
 (.branch 809
 (.leaf (.quota 1))
 (.branch 810
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 817
 (.branch 815
 (.leaf (.quota 1))
 (.branch 816
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 819
 (.branch 818
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1)))))
 (.branch 828
 (.branch 824
 (.branch 822
 (.leaf (.quota 1))
 (.branch 823
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.branch 831
 (.branch 829
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))))))))
def disposition (j : Fin leafCount) := dispositionTable.get j.val
def dispositionTest (i : Nat) : Bool := RawLeafCertificate.check quota
  ((rawLeaves i).map Papers.RationalityTen.RootedCaches.RootedSixExtra05.rawCells) (dispositionTable.get i)

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0870

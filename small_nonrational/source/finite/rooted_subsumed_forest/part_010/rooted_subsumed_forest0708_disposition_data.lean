module
prelude
public import RootedSubsumedForest0708Data
public import RawLeafCertificate
public import OldTerminalMatches.M019

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
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
 (.leaf (.quota 2))
 (.branch 2
 (.leaf (.matching Nonrational.OldTerminalMatches.M019.r1230))
 (.leaf (.quota 2))))
 (.branch 4
 (.leaf (.matching Nonrational.OldTerminalMatches.M019.r1231))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 37
 (.leaf (.quota 2))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf (.quota 2))
 (.branch 39
 (.leaf (.matching Nonrational.OldTerminalMatches.M019.r1232))
 (.leaf (.matching Nonrational.OldTerminalMatches.M019.r1233))))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf (.quota 2))
 (.branch 52
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 54
 (.leaf (.quota 2))
 (.branch 55
 (.leaf (.matching Nonrational.OldTerminalMatches.M019.r1234))
 (.leaf (.quota 2)))))
 (.leaf (.quota 2)))
 (.branch 68
 (.branch 65
 (.leaf (.quota 2))
 (.branch 66
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 71
 (.branch 69
 (.leaf (.quota 2))
 (.branch 70
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M019.r1235))))
 (.branch 73
 (.branch 72
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))))
 (.branch 88
 (.leaf (.quota 2))
 (.branch 94
 (.branch 91
 (.branch 89
 (.leaf (.quota 2))
 (.branch 90
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 2)))
 (.branch 97
 (.branch 95
 (.leaf (.quota 2))
 (.branch 96
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 99
 (.branch 98
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))))))
 (.branch 152
 (.branch 126
 (.branch 113
 (.branch 107
 (.leaf (.quota 2))
 (.branch 110
 (.branch 108
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.branch 119
 (.leaf (.quota 2))
 (.branch 122
 (.leaf (.quota 2))
 (.branch 124
 (.branch 123
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))))
 (.branch 139
 (.branch 132
 (.branch 129
 (.branch 127
 (.leaf (.matching Nonrational.OldTerminalMatches.M019.r1236))
 (.branch 128
 (.leaf (.matching Nonrational.OldTerminalMatches.M019.r1237))
 (.leaf (.matching Nonrational.OldTerminalMatches.M019.r1238))))
 (.branch 130
 (.leaf (.matching Nonrational.OldTerminalMatches.M019.r1239))
 (.leaf (.quota 1))))
 (.branch 135
 (.branch 133
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.branch 145
 (.branch 142
 (.leaf (.quota 2))
 (.branch 143
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 148
 (.branch 146
 (.leaf (.quota 2))
 (.branch 147
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M019.r1240))))
 (.branch 150
 (.leaf (.quota 2))
 (.branch 151
 (.leaf (.matching Nonrational.OldTerminalMatches.M019.r1241))
 (.leaf (.quota 2))))))))
 (.branch 177
 (.branch 164
 (.branch 158
 (.leaf (.quota 2))
 (.branch 161
 (.branch 159
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 162
 (.leaf (.quota 1))
 (.branch 163
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 170
 (.leaf (.quota 2))
 (.branch 173
 (.branch 171
 (.leaf (.quota 2))
 (.branch 172
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 175
 (.leaf (.quota 1))
 (.branch 176
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))))
 (.branch 190
 (.branch 183
 (.leaf (.quota 2))
 (.branch 186
 (.branch 184
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 188
 (.leaf (.quota 2))
 (.branch 189
 (.leaf (.quota 1))
 (.leaf (.matching Nonrational.OldTerminalMatches.M019.r1242))))))
 (.branch 196
 (.branch 193
 (.branch 191
 (.leaf (.matching Nonrational.OldTerminalMatches.M019.r1243))
 (.branch 192
 (.leaf (.matching Nonrational.OldTerminalMatches.M019.r1244))
 (.leaf (.matching Nonrational.OldTerminalMatches.M019.r1245))))
 (.branch 194
 (.leaf (.quota 1))
 (.branch 195
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.leaf (.quota 2)))))))
 (.branch 305
 (.branch 254
 (.branch 228
 (.branch 215
 (.branch 209
 (.branch 206
 (.branch 204
 (.leaf (.quota 1))
 (.branch 205
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M019.r1246))))
 (.branch 207
 (.leaf (.quota 2))
 (.branch 208
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M019.r1247)))))
 (.branch 212
 (.branch 210
 (.leaf (.matching Nonrational.OldTerminalMatches.M019.r1248))
 (.leaf (.quota 2)))
 (.branch 213
 (.leaf (.quota 2))
 (.branch 214
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 221
 (.branch 218
 (.branch 216
 (.leaf (.quota 1))
 (.branch 217
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 219
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 224
 (.branch 222
 (.leaf (.quota 1))
 (.branch 223
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 226
 (.leaf (.quota 2))
 (.branch 227
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))))
 (.branch 241
 (.branch 234
 (.leaf (.quota 2))
 (.branch 237
 (.branch 235
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 239
 (.leaf (.quota 2))
 (.branch 240
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 247
 (.branch 244
 (.leaf (.quota 2))
 (.branch 245
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 2)))))
 (.branch 279
 (.branch 266
 (.branch 260
 (.branch 257
 (.leaf (.quota 2))
 (.branch 258
 (.leaf (.quota 2))
 (.branch 259
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 263
 (.branch 261
 (.leaf (.quota 2))
 (.branch 262
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 2))))
 (.branch 272
 (.branch 269
 (.branch 267
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.branch 292
 (.branch 285
 (.branch 282
 (.branch 280
 (.leaf (.quota 2))
 (.branch 281
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 283
 (.leaf (.quota 2))
 (.branch 284
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.leaf (.quota 2)))
 (.branch 298
 (.leaf (.quota 2))
 (.branch 301
 (.leaf (.quota 2))
 (.branch 303
 (.branch 302
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))))))
 (.branch 356
 (.branch 330
 (.branch 317
 (.branch 311
 (.branch 308
 (.leaf (.quota 2))
 (.branch 309
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.branch 323
 (.leaf (.quota 2))
 (.branch 326
 (.leaf (.quota 2))
 (.branch 328
 (.branch 327
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))))
 (.branch 343
 (.branch 336
 (.leaf (.quota 2))
 (.branch 339
 (.branch 337
 (.leaf (.quota 2))
 (.branch 338
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 341
 (.branch 340
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))))
 (.branch 349
 (.branch 346
 (.branch 344
 (.leaf (.quota 1))
 (.branch 345
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 347
 (.leaf (.quota 1))
 (.branch 348
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.leaf (.quota 2)))))
 (.branch 381
 (.branch 368
 (.branch 362
 (.branch 359
 (.leaf (.quota 2))
 (.branch 360
 (.leaf (.quota 1))
 (.branch 361
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.leaf (.quota 2)))
 (.branch 374
 (.branch 371
 (.branch 369
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.branch 394
 (.branch 387
 (.branch 384
 (.leaf (.quota 2))
 (.branch 385
 (.leaf (.quota 2))
 (.branch 386
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 390
 (.branch 388
 (.leaf (.quota 2))
 (.branch 389
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 2))))
 (.branch 400
 (.branch 397
 (.leaf (.quota 2))
 (.branch 398
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 403
 (.leaf (.quota 2))
 (.branch 405
 (.branch 404
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2))))))))))
 (.branch 611
 (.branch 509
 (.branch 458
 (.branch 432
 (.branch 419
 (.branch 413
 (.branch 410
 (.branch 408
 (.leaf (.matching Nonrational.OldTerminalMatches.M019.r1249))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 425
 (.branch 422
 (.branch 420
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 423
 (.leaf (.quota 2))
 (.branch 424
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 428
 (.leaf (.quota 2))
 (.branch 430
 (.branch 429
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))))
 (.branch 445
 (.branch 438
 (.branch 435
 (.leaf (.quota 2))
 (.branch 436
 (.leaf (.quota 1))
 (.branch 437
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 441
 (.branch 439
 (.leaf (.quota 2))
 (.branch 440
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 443
 (.leaf (.quota 2))
 (.branch 444
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 451
 (.branch 448
 (.branch 446
 (.leaf (.quota 2))
 (.branch 447
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.branch 454
 (.branch 452
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 456
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))))
 (.branch 483
 (.branch 470
 (.branch 464
 (.leaf (.quota 2))
 (.branch 467
 (.leaf (.quota 2))
 (.branch 468
 (.leaf (.matching Nonrational.OldTerminalMatches.M019.r1250))
 (.leaf (.quota 2)))))
 (.branch 476
 (.leaf (.quota 2))
 (.branch 479
 (.branch 477
 (.leaf (.quota 2))
 (.branch 478
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 481
 (.branch 480
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2))))))
 (.branch 496
 (.branch 489
 (.branch 486
 (.leaf (.quota 2))
 (.branch 487
 (.leaf (.quota 1))
 (.branch 488
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 492
 (.branch 490
 (.leaf (.quota 2))
 (.branch 491
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 494
 (.leaf (.quota 1))
 (.branch 495
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 502
 (.branch 499
 (.leaf (.quota 2))
 (.branch 500
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 505
 (.leaf (.quota 2))
 (.branch 507
 (.branch 506
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))))))
 (.branch 560
 (.branch 534
 (.branch 521
 (.leaf (.quota 2))
 (.branch 527
 (.branch 524
 (.leaf (.quota 2))
 (.branch 525
 (.leaf (.quota 2))
 (.branch 526
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 530
 (.leaf (.quota 2))
 (.branch 532
 (.branch 531
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))))
 (.branch 547
 (.branch 540
 (.leaf (.quota 2))
 (.branch 543
 (.leaf (.quota 2))
 (.branch 545
 (.branch 544
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 546
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 553
 (.branch 550
 (.branch 548
 (.leaf (.quota 2))
 (.branch 549
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 551
 (.leaf (.quota 2))
 (.branch 552
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 556
 (.leaf (.quota 2))
 (.branch 558
 (.branch 557
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))))
 (.branch 585
 (.branch 572
 (.branch 566
 (.branch 563
 (.branch 561
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 564
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 569
 (.branch 567
 (.leaf (.matching Nonrational.OldTerminalMatches.M019.r1251))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.branch 578
 (.leaf (.quota 2))
 (.branch 581
 (.branch 579
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 583
 (.leaf (.quota 2))
 (.branch 584
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M019.r1252)))))))
 (.branch 598
 (.branch 591
 (.branch 588
 (.branch 586
 (.leaf (.quota 1))
 (.branch 587
 (.leaf (.matching Nonrational.OldTerminalMatches.M019.r1253))
 (.leaf (.quota 2))))
 (.branch 589
 (.leaf (.quota 2))
 (.branch 590
 (.leaf (.incidence 5))
 (.leaf (.quota 2)))))
 (.leaf (.quota 2)))
 (.branch 604
 (.branch 601
 (.branch 599
 (.leaf (.quota 2))
 (.branch 600
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.branch 607
 (.branch 605
 (.leaf (.quota 2))
 (.branch 606
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 609
 (.leaf (.quota 2))
 (.branch 610
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))))))
 (.branch 713
 (.branch 662
 (.branch 636
 (.branch 623
 (.branch 617
 (.branch 614
 (.leaf (.quota 2))
 (.branch 615
 (.leaf (.quota 2))
 (.branch 616
 (.leaf (.incidence 5))
 (.leaf (.quota 2)))))
 (.leaf (.quota 2)))
 (.branch 629
 (.branch 626
 (.branch 624
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 627
 (.leaf (.quota 2))
 (.branch 628
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.leaf (.quota 2))))
 (.branch 649
 (.branch 642
 (.branch 639
 (.branch 637
 (.leaf (.matching Nonrational.OldTerminalMatches.M019.r1254))
 (.branch 638
 (.leaf (.matching Nonrational.OldTerminalMatches.M019.r1255))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.branch 645
 (.branch 643
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 647
 (.branch 646
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 648
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 655
 (.branch 652
 (.branch 650
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 653
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 658
 (.branch 656
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 660
 (.leaf (.quota 2))
 (.branch 661
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))))
 (.branch 687
 (.branch 674
 (.branch 668
 (.branch 665
 (.branch 663
 (.leaf (.quota 2))
 (.branch 664
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 671
 (.branch 669
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 672
 (.leaf (.quota 1))
 (.branch 673
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 680
 (.branch 677
 (.leaf (.quota 2))
 (.branch 678
 (.leaf (.quota 2))
 (.branch 679
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 683
 (.leaf (.quota 2))
 (.branch 685
 (.branch 684
 (.leaf (.matching Nonrational.OldTerminalMatches.M019.r1256))
 (.leaf (.quota 1)))
 (.leaf (.quota 2))))))
 (.branch 700
 (.leaf (.quota 2))
 (.branch 706
 (.branch 703
 (.branch 701
 (.leaf (.quota 1))
 (.branch 702
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 2)))
 (.branch 709
 (.leaf (.quota 2))
 (.branch 711
 (.branch 710
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 712
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))))))
 (.branch 764
 (.branch 738
 (.branch 725
 (.branch 719
 (.branch 716
 (.leaf (.quota 2))
 (.branch 717
 (.leaf (.quota 1))
 (.branch 718
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 722
 (.leaf (.quota 2))
 (.branch 723
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 731
 (.leaf (.quota 2))
 (.branch 734
 (.branch 732
 (.leaf (.quota 1))
 (.branch 733
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 736
 (.leaf (.quota 2))
 (.branch 737
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))))
 (.branch 751
 (.branch 744
 (.branch 741
 (.leaf (.quota 1))
 (.branch 742
 (.leaf (.quota 1))
 (.branch 743
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 747
 (.branch 745
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.branch 757
 (.branch 754
 (.leaf (.quota 2))
 (.branch 755
 (.leaf (.quota 2))
 (.branch 756
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 760
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 789
 (.branch 776
 (.branch 770
 (.branch 767
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 773
 (.branch 771
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.branch 802
 (.branch 795
 (.branch 792
 (.leaf (.quota 2))
 (.branch 793
 (.leaf (.quota 2))
 (.branch 794
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 798
 (.leaf (.quota 2))
 (.branch 800
 (.leaf (.quota 2))
 (.branch 801
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 808
 (.leaf (.quota 2))
 (.branch 811
 (.branch 809
 (.leaf (.quota 2))
 (.branch 810
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 813
 (.leaf (.quota 2))
 (.branch 814
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))))))))
 (.branch 1223
 (.branch 1019
 (.branch 917
 (.branch 866
 (.branch 840
 (.branch 827
 (.branch 821
 (.branch 818
 (.branch 816
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 833
 (.leaf (.quota 2))
 (.branch 836
 (.branch 834
 (.leaf (.quota 2))
 (.branch 835
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 838
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 853
 (.branch 846
 (.branch 843
 (.branch 841
 (.leaf (.quota 2))
 (.branch 842
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 844
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 849
 (.branch 847
 (.leaf (.quota 1))
 (.branch 848
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 2))))
 (.branch 859
 (.branch 856
 (.branch 854
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))
 (.branch 862
 (.branch 860
 (.leaf (.quota 1))
 (.branch 861
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 2))))))
 (.branch 891
 (.branch 878
 (.branch 872
 (.branch 869
 (.branch 867
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 870
 (.leaf (.quota 1))
 (.branch 871
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 875
 (.branch 873
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2))))
 (.branch 884
 (.branch 881
 (.branch 879
 (.leaf (.quota 2))
 (.branch 880
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 882
 (.leaf (.quota 2))
 (.branch 883
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 887
 (.leaf (.quota 2))
 (.branch 889
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 904
 (.branch 897
 (.branch 894
 (.branch 892
 (.leaf (.quota 2))
 (.branch 893
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 895
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 900
 (.branch 898
 (.leaf (.quota 2))
 (.branch 899
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 902
 (.leaf (.quota 1))
 (.branch 903
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 910
 (.branch 907
 (.leaf (.quota 2))
 (.branch 908
 (.leaf (.quota 1))
 (.branch 909
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 913
 (.branch 911
 (.leaf (.quota 2))
 (.branch 912
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 915
 (.leaf (.quota 2))
 (.branch 916
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))))))
 (.branch 968
 (.branch 942
 (.branch 929
 (.branch 923
 (.branch 920
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 926
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 935
 (.leaf (.quota 2))
 (.branch 938
 (.branch 936
 (.leaf (.quota 1))
 (.branch 937
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))))
 (.branch 955
 (.branch 948
 (.leaf (.quota 2))
 (.branch 951
 (.leaf (.quota 2))
 (.branch 953
 (.branch 952
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 954
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 961
 (.branch 958
 (.branch 956
 (.leaf (.quota 2))
 (.branch 957
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1)))
 (.branch 964
 (.branch 962
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 966
 (.branch 965
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))))))
 (.branch 993
 (.branch 980
 (.branch 974
 (.branch 971
 (.leaf (.quota 1))
 (.branch 972
 (.leaf (.quota 1))
 (.branch 973
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 977
 (.branch 975
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.branch 986
 (.leaf (.quota 2))
 (.branch 989
 (.leaf (.quota 2))
 (.branch 991
 (.branch 990
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))))
 (.branch 1006
 (.branch 999
 (.branch 996
 (.branch 994
 (.leaf (.quota 2))
 (.branch 995
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.branch 1002
 (.leaf (.quota 1))
 (.branch 1004
 (.branch 1003
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))))
 (.branch 1012
 (.leaf (.quota 2))
 (.branch 1015
 (.branch 1013
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 1017
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))))))
 (.branch 1121
 (.branch 1070
 (.branch 1044
 (.branch 1031
 (.branch 1025
 (.branch 1022
 (.leaf (.quota 2))
 (.branch 1023
 (.leaf (.quota 2))
 (.branch 1024
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 1028
 (.branch 1026
 (.leaf (.quota 1))
 (.branch 1027
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 2))))
 (.branch 1037
 (.branch 1034
 (.branch 1032
 (.leaf (.quota 2))
 (.branch 1033
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 1035
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 1040
 (.branch 1038
 (.leaf (.quota 2))
 (.branch 1039
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 1042
 (.branch 1041
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))))
 (.branch 1057
 (.branch 1050
 (.branch 1047
 (.branch 1045
 (.leaf (.quota 2))
 (.branch 1046
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 1048
 (.leaf (.quota 1))
 (.branch 1049
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 1053
 (.branch 1051
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 1055
 (.leaf (.quota 2))
 (.branch 1056
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.leaf (.quota 2))))
 (.branch 1095
 (.branch 1082
 (.branch 1076
 (.leaf (.quota 2))
 (.branch 1079
 (.branch 1077
 (.leaf .euler)
 (.branch 1078
 (.leaf (.quota 2))
 (.leaf .euler)))
 (.leaf (.quota 2))))
 (.branch 1088
 (.branch 1085
 (.branch 1083
 (.leaf (.quota 2))
 (.branch 1084
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.branch 1091
 (.branch 1089
 (.leaf (.quota 2))
 (.branch 1090
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 1093
 (.leaf (.quota 2))
 (.branch 1094
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))))
 (.branch 1108
 (.branch 1101
 (.branch 1098
 (.branch 1096
 (.leaf (.quota 2))
 (.branch 1097
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 1099
 (.leaf (.quota 1))
 (.branch 1100
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 1104
 (.branch 1102
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2))))
 (.branch 1114
 (.branch 1111
 (.branch 1109
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))))
 (.branch 1172
 (.branch 1146
 (.branch 1133
 (.branch 1127
 (.leaf (.quota 2))
 (.branch 1130
 (.leaf (.quota 2))
 (.branch 1131
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 1139
 (.branch 1136
 (.branch 1134
 (.leaf (.quota 2))
 (.branch 1135
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 2)))
 (.branch 1142
 (.branch 1140
 (.leaf (.quota 2))
 (.branch 1141
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 1144
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 1159
 (.branch 1152
 (.branch 1149
 (.branch 1147
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 1155
 (.branch 1153
 (.leaf (.quota 2))
 (.branch 1154
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 1157
 (.branch 1156
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.branch 1165
 (.branch 1162
 (.branch 1160
 (.leaf (.quota 1))
 (.branch 1161
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 1163
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 1168
 (.leaf (.quota 2))
 (.branch 1170
 (.branch 1169
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 1171
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))))
 (.branch 1197
 (.branch 1184
 (.branch 1178
 (.branch 1175
 (.leaf (.quota 2))
 (.branch 1176
 (.leaf (.quota 2))
 (.branch 1177
 (.leaf .euler)
 (.leaf (.quota 2)))))
 (.branch 1181
 (.branch 1179
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2))))
 (.branch 1190
 (.branch 1187
 (.branch 1185
 (.leaf (.quota 2))
 (.branch 1186
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 1188
 (.leaf (.quota 2))
 (.branch 1189
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.leaf (.quota 2))))
 (.branch 1210
 (.branch 1203
 (.branch 1200
 (.leaf (.quota 2))
 (.branch 1201
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.branch 1216
 (.branch 1213
 (.leaf (.quota 2))
 (.branch 1214
 (.leaf (.quota 2))
 (.branch 1215
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 1219
 (.leaf (.quota 2))
 (.branch 1221
 (.leaf (.quota 2))
 (.branch 1222
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))))))))
 (.branch 1427
 (.branch 1325
 (.branch 1274
 (.branch 1248
 (.branch 1235
 (.leaf (.quota 2))
 (.branch 1241
 (.branch 1238
 (.branch 1236
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 1244
 (.leaf (.quota 2))
 (.branch 1246
 (.branch 1245
 (.leaf (.quota 1))
 (.leaf (.matching Nonrational.OldTerminalMatches.M019.r1257)))
 (.leaf (.quota 2))))))
 (.branch 1261
 (.branch 1254
 (.leaf (.quota 2))
 (.branch 1257
 (.branch 1255
 (.leaf (.quota 1))
 (.branch 1256
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 2))))
 (.branch 1267
 (.leaf (.quota 2))
 (.branch 1270
 (.leaf (.quota 2))
 (.branch 1272
 (.leaf (.quota 2))
 (.branch 1273
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))))
 (.branch 1299
 (.branch 1286
 (.branch 1280
 (.branch 1277
 (.leaf (.quota 2))
 (.branch 1278
 (.leaf (.quota 2))
 (.branch 1279
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 1283
 (.leaf (.quota 2))
 (.branch 1284
 (.leaf (.quota 1))
 (.branch 1285
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 1292
 (.branch 1289
 (.leaf (.quota 2))
 (.branch 1290
 (.leaf (.quota 1))
 (.branch 1291
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.leaf (.quota 2))))
 (.branch 1312
 (.branch 1305
 (.leaf (.quota 2))
 (.branch 1308
 (.leaf (.quota 2))
 (.branch 1310
 (.leaf (.quota 2))
 (.branch 1311
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 1318
 (.branch 1315
 (.branch 1313
 (.leaf (.matching Nonrational.OldTerminalMatches.M019.r1258))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 1321
 (.leaf (.quota 2))
 (.branch 1323
 (.branch 1322
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 1324
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))))))
 (.branch 1376
 (.branch 1350
 (.branch 1337
 (.branch 1331
 (.leaf (.quota 2))
 (.branch 1334
 (.branch 1332
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 1335
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 1343
 (.branch 1340
 (.leaf (.quota 2))
 (.branch 1341
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 1346
 (.branch 1344
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 1348
 (.branch 1347
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))))
 (.branch 1363
 (.branch 1356
 (.branch 1353
 (.branch 1351
 (.leaf (.quota 1))
 (.branch 1352
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 1354
 (.leaf (.quota 1))
 (.branch 1355
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 1359
 (.leaf (.quota 2))
 (.branch 1361
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 1369
 (.branch 1366
 (.branch 1364
 (.leaf (.quota 1))
 (.branch 1365
 (.leaf (.matching Nonrational.OldTerminalMatches.M019.r1259))
 (.leaf (.matching Nonrational.OldTerminalMatches.M019.r1260))))
 (.branch 1367
 (.leaf (.quota 2))
 (.branch 1368
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 1372
 (.branch 1370
 (.leaf (.quota 1))
 (.branch 1371
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 1374
 (.branch 1373
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 1375
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))))
 (.branch 1401
 (.branch 1388
 (.branch 1382
 (.branch 1379
 (.branch 1377
 (.leaf (.quota 1))
 (.branch 1378
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 1380
 (.leaf (.quota 1))
 (.branch 1381
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 1385
 (.leaf (.quota 2))
 (.branch 1386
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 1394
 (.branch 1391
 (.leaf (.quota 1))
 (.branch 1392
 (.leaf (.quota 1))
 (.branch 1393
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M019.r1261)))))
 (.leaf (.quota 1))))
 (.branch 1414
 (.branch 1407
 (.branch 1404
 (.branch 1402
 (.leaf (.matching Nonrational.OldTerminalMatches.M019.r1262))
 (.branch 1403
 (.leaf (.matching Nonrational.OldTerminalMatches.M019.r1263))
 (.leaf (.matching Nonrational.OldTerminalMatches.M019.r1264))))
 (.branch 1405
 (.leaf (.matching Nonrational.OldTerminalMatches.M019.r1265))
 (.branch 1406
 (.leaf (.matching Nonrational.OldTerminalMatches.M019.r1266))
 (.leaf (.matching Nonrational.OldTerminalMatches.M019.r1267)))))
 (.branch 1410
 (.branch 1408
 (.leaf (.matching Nonrational.OldTerminalMatches.M019.r1268))
 (.leaf (.quota 1)))
 (.branch 1412
 (.branch 1411
 (.leaf (.matching Nonrational.OldTerminalMatches.M019.r1269))
 (.leaf (.matching Nonrational.OldTerminalMatches.M019.r1270)))
 (.branch 1413
 (.leaf (.matching Nonrational.OldTerminalMatches.M019.r1271))
 (.leaf (.matching Nonrational.OldTerminalMatches.M019.r1272))))))
 (.branch 1420
 (.branch 1417
 (.branch 1415
 (.leaf (.matching Nonrational.OldTerminalMatches.M019.r1273))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))))))
 (.branch 1529
 (.branch 1478
 (.branch 1452
 (.branch 1439
 (.branch 1433
 (.leaf (.quota 2))
 (.branch 1436
 (.leaf (.quota 2))
 (.branch 1437
 (.leaf (.quota 2))
 (.branch 1438
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 1445
 (.branch 1442
 (.branch 1440
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 1443
 (.leaf (.quota 2))
 (.branch 1444
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 1448
 (.leaf (.quota 2))
 (.branch 1450
 (.branch 1449
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))))
 (.branch 1465
 (.branch 1458
 (.leaf (.quota 2))
 (.branch 1461
 (.branch 1459
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.leaf (.quota 2))))
 (.branch 1503
 (.branch 1490
 (.leaf (.quota 2))
 (.branch 1496
 (.branch 1493
 (.leaf (.quota 2))
 (.branch 1494
 (.leaf (.quota 2))
 (.branch 1495
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 1499
 (.leaf (.quota 2))
 (.branch 1501
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 1516
 (.branch 1509
 (.leaf (.quota 2))
 (.branch 1512
 (.leaf (.quota 2))
 (.branch 1514
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 1522
 (.branch 1519
 (.branch 1517
 (.leaf (.quota 2))
 (.branch 1518
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 1520
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 2))))))
 (.branch 1580
 (.branch 1554
 (.branch 1541
 (.branch 1535
 (.branch 1532
 (.leaf (.quota 2))
 (.branch 1533
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.branch 1547
 (.leaf (.quota 2))
 (.branch 1550
 (.branch 1548
 (.leaf (.quota 2))
 (.branch 1549
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 1552
 (.branch 1551
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2))))))
 (.branch 1567
 (.branch 1560
 (.branch 1557
 (.branch 1555
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 1558
 (.leaf (.quota 1))
 (.branch 1559
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 1563
 (.leaf (.quota 1))
 (.branch 1565
 (.leaf (.quota 1))
 (.branch 1566
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 1573
 (.branch 1570
 (.branch 1568
 (.leaf (.quota 1))
 (.branch 1569
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 1571
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 1576
 (.branch 1574
 (.leaf (.quota 2))
 (.branch 1575
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 2))))))
 (.branch 1605
 (.branch 1592
 (.branch 1586
 (.branch 1583
 (.branch 1581
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 1598
 (.branch 1595
 (.leaf (.quota 2))
 (.branch 1596
 (.leaf (.quota 2))
 (.branch 1597
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.leaf (.quota 2))))
 (.branch 1618
 (.branch 1611
 (.branch 1608
 (.branch 1606
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 1609
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 1614
 (.leaf (.quota 2))
 (.branch 1616
 (.branch 1615
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))))
 (.branch 1624
 (.branch 1621
 (.branch 1619
 (.leaf (.quota 2))
 (.branch 1620
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 1627
 (.branch 1625
 (.leaf (.quota 1))
 (.branch 1626
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 1629
 (.leaf (.quota 1))
 (.branch 1630
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))))))))))
def disposition (j : Fin leafCount) := dispositionTable.get j.val
def dispositionTest (i : Nat) : Bool := RawLeafCertificate.check quota
  ((rawLeaves i).map Papers.RationalityTen.RootedCaches.RootedSixBase02.rawCells) (dispositionTable.get i)

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0708

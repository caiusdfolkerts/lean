module
prelude
public import RootedSubsumedForest0355Data
public import RawLeafCertificate
public import OldTerminalMatches.M014
public import OldTerminalMatches.M015
public import OldTerminalMatches.M016
public import OldTerminalMatches.M017

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 2042
 (.branch 1021
 (.branch 510
 (.branch 255
 (.branch 127
 (.branch 63
 (.branch 31
 (.branch 15
 (.branch 7
 (.branch 3
 (.leaf (.quota 2))
 (.branch 5
 (.branch 4
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.branch 6
 (.leaf (.quota 2))
 (.leaf (.quota 3)))))
 (.branch 11
 (.branch 9
 (.leaf (.quota 2))
 (.branch 10
 (.leaf .euler)
 (.leaf (.quota 2))))
 (.branch 13
 (.leaf (.quota 2))
 (.branch 14
 (.leaf .euler)
 (.leaf (.quota 2))))))
 (.branch 23
 (.branch 19
 (.branch 17
 (.leaf (.quota 2))
 (.branch 18
 (.leaf (.quota 3))
 (.leaf (.quota 2))))
 (.branch 21
 (.leaf (.quota 2))
 (.branch 22
 (.leaf (.quota 3))
 (.leaf (.quota 2)))))
 (.branch 27
 (.leaf (.quota 2))
 (.branch 29
 (.leaf (.quota 2))
 (.leaf .euler)))))
 (.branch 47
 (.branch 39
 (.leaf (.quota 2))
 (.branch 43
 (.branch 41
 (.branch 40
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.leaf (.quota 2)))
 (.branch 45
 (.branch 44
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 46
 (.leaf (.quota 2))
 (.leaf (.quota 3))))))
 (.branch 55
 (.branch 51
 (.branch 49
 (.branch 48
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 59
 (.branch 57
 (.branch 56
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))
 (.branch 61
 (.branch 60
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.leaf (.quota 2)))))))
 (.branch 95
 (.branch 79
 (.branch 71
 (.branch 67
 (.branch 65
 (.branch 64
 (.leaf (.quota 3))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 69
 (.branch 68
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.branch 87
 (.branch 83
 (.leaf (.quota 2))
 (.branch 85
 (.leaf (.quota 2))
 (.branch 86
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 91
 (.branch 89
 (.leaf (.quota 2))
 (.branch 90
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))))
 (.branch 111
 (.branch 103
 (.leaf (.quota 2))
 (.branch 107
 (.leaf (.quota 2))
 (.branch 109
 (.branch 108
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))))
 (.branch 119
 (.leaf (.quota 2))
 (.branch 123
 (.branch 121
 (.branch 120
 (.leaf (.matching Nonrational.OldTerminalMatches.M014.r0957))
 (.leaf (.matching Nonrational.OldTerminalMatches.M014.r0958)))
 (.branch 122
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))))))
 (.branch 191
 (.branch 159
 (.branch 143
 (.branch 135
 (.branch 131
 (.branch 129
 (.branch 128
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 130
 (.leaf (.quota 3))
 (.leaf (.quota 1))))
 (.branch 133
 (.branch 132
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.leaf (.quota 3))))
 (.branch 139
 (.branch 137
 (.branch 136
 (.leaf (.quota 2))
 (.leaf (.incidence 5)))
 (.branch 138
 (.leaf (.quota 2))
 (.leaf (.incidence 4))))
 (.leaf (.quota 2))))
 (.branch 151
 (.branch 147
 (.branch 145
 (.branch 144
 (.leaf (.quota 2))
 (.leaf (.incidence 5)))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 155
 (.branch 153
 (.branch 152
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 157
 (.branch 156
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))))
 (.branch 175
 (.branch 167
 (.branch 163
 (.branch 161
 (.branch 160
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 165
 (.branch 164
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.branch 171
 (.branch 169
 (.leaf (.quota 2))
 (.branch 170
 (.leaf (.quota 3))
 (.leaf (.quota 2))))
 (.branch 173
 (.branch 172
 (.leaf (.quota 3))
 (.leaf (.quota 2)))
 (.branch 174
 (.leaf (.quota 2))
 (.leaf (.quota 3))))))
 (.branch 183
 (.branch 179
 (.branch 177
 (.leaf (.quota 2))
 (.branch 178
 (.leaf (.quota 2))
 (.leaf (.quota 3))))
 (.branch 181
 (.leaf (.quota 3))
 (.branch 182
 (.leaf (.quota 2))
 (.leaf (.quota 3)))))
 (.branch 187
 (.leaf (.quota 2))
 (.branch 189
 (.branch 188
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.leaf (.quota 2)))))))
 (.branch 223
 (.branch 207
 (.branch 199
 (.branch 195
 (.branch 193
 (.leaf (.quota 2))
 (.branch 194
 (.leaf (.quota 3))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.branch 203
 (.branch 201
 (.leaf (.quota 2))
 (.branch 202
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 2))))
 (.branch 215
 (.branch 211
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.branch 219
 (.branch 217
 (.leaf (.quota 2))
 (.branch 218
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))))
 (.branch 239
 (.branch 231
 (.branch 227
 (.branch 225
 (.leaf (.quota 2))
 (.branch 226
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M014.r0959))))
 (.branch 229
 (.branch 228
 (.leaf (.matching Nonrational.OldTerminalMatches.M015.r0960))
 (.leaf (.quota 3)))
 (.leaf (.quota 2))))
 (.branch 235
 (.branch 233
 (.leaf (.quota 2))
 (.branch 234
 (.leaf (.quota 3))
 (.leaf (.quota 2))))
 (.branch 237
 (.leaf (.quota 3))
 (.leaf (.quota 2)))))
 (.branch 247
 (.branch 243
 (.branch 241
 (.branch 240
 (.leaf (.quota 3))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 245
 (.branch 244
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.branch 246
 (.leaf (.quota 3))
 (.leaf (.quota 1)))))
 (.branch 251
 (.branch 249
 (.leaf (.quota 3))
 (.leaf (.quota 1)))
 (.branch 253
 (.leaf (.quota 2))
 (.branch 254
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))))))
 (.branch 382
 (.branch 318
 (.branch 286
 (.branch 270
 (.branch 262
 (.branch 258
 (.branch 256
 (.leaf (.quota 3))
 (.leaf (.quota 2)))
 (.branch 260
 (.leaf (.quota 2))
 (.branch 261
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 266
 (.branch 264
 (.branch 263
 (.leaf (.quota 1))
 (.leaf (.matching Nonrational.OldTerminalMatches.M015.r0961)))
 (.branch 265
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 268
 (.branch 267
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))))
 (.branch 278
 (.branch 274
 (.branch 272
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.branch 276
 (.leaf (.quota 2))
 (.leaf (.quota 3))))
 (.branch 282
 (.branch 280
 (.branch 279
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.leaf (.quota 3)))
 (.branch 284
 (.branch 283
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 285
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))))
 (.branch 302
 (.branch 294
 (.branch 290
 (.branch 288
 (.leaf (.quota 2))
 (.branch 289
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 292
 (.leaf (.quota 2))
 (.branch 293
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 298
 (.branch 296
 (.branch 295
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 300
 (.leaf (.quota 2))
 (.branch 301
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M015.r0962))))))
 (.branch 310
 (.branch 306
 (.branch 304
 (.leaf (.quota 2))
 (.branch 305
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 308
 (.branch 307
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.branch 309
 (.leaf (.quota 2))
 (.leaf (.quota 3)))))
 (.branch 314
 (.branch 312
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.leaf (.quota 3))))))
 (.branch 350
 (.branch 334
 (.branch 326
 (.branch 322
 (.branch 320
 (.leaf (.quota 2))
 (.branch 321
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 324
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 330
 (.branch 328
 (.branch 327
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))
 (.branch 332
 (.leaf (.quota 2))
 (.branch 333
 (.leaf (.quota 1))
 (.leaf (.quota 3))))))
 (.branch 342
 (.branch 338
 (.branch 336
 (.branch 335
 (.leaf (.quota 3))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 340
 (.branch 339
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.leaf (.quota 2))))
 (.branch 346
 (.branch 344
 (.leaf (.quota 2))
 (.branch 345
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 2)))))
 (.branch 366
 (.branch 358
 (.branch 354
 (.branch 352
 (.branch 351
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 362
 (.leaf (.quota 2))
 (.branch 364
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 374
 (.branch 370
 (.leaf (.quota 3))
 (.branch 372
 (.leaf (.quota 1))
 (.leaf (.quota 3))))
 (.branch 378
 (.branch 376
 (.branch 375
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))))))
 (.branch 446
 (.branch 414
 (.branch 398
 (.branch 390
 (.branch 386
 (.leaf (.quota 2))
 (.branch 388
 (.branch 387
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 3))))
 (.branch 394
 (.branch 392
 (.branch 391
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.branch 406
 (.branch 402
 (.branch 400
 (.branch 399
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.branch 430
 (.branch 422
 (.branch 418
 (.leaf (.quota 2))
 (.branch 420
 (.branch 419
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.leaf (.quota 2))))
 (.branch 426
 (.branch 424
 (.leaf (.quota 2))
 (.branch 425
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 2))))
 (.branch 438
 (.leaf (.quota 2))
 (.branch 442
 (.branch 440
 (.branch 439
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))))
 (.branch 478
 (.branch 462
 (.leaf (.quota 2))
 (.branch 470
 (.leaf (.quota 2))
 (.branch 474
 (.leaf (.quota 2))
 (.branch 476
 (.leaf (.quota 2))
 (.branch 477
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))))
 (.branch 494
 (.branch 486
 (.branch 482
 (.branch 480
 (.leaf (.quota 2))
 (.branch 481
 (.leaf (.matching Nonrational.OldTerminalMatches.M015.r0963))
 (.leaf (.matching Nonrational.OldTerminalMatches.M015.r0964))))
 (.branch 484
 (.branch 483
 (.leaf (.matching Nonrational.OldTerminalMatches.M015.r0965))
 (.leaf (.matching Nonrational.OldTerminalMatches.M015.r0966)))
 (.branch 485
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.leaf (.quota 2)))
 (.branch 502
 (.branch 498
 (.branch 496
 (.branch 495
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))
 (.branch 500
 (.leaf (.quota 2))
 (.branch 501
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 506
 (.branch 504
 (.branch 503
 (.leaf (.quota 3))
 (.leaf (.quota 2)))
 (.branch 505
 (.leaf (.quota 3))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))))))))
 (.branch 765
 (.branch 637
 (.branch 573
 (.branch 541
 (.branch 525
 (.branch 517
 (.leaf (.quota 2))
 (.branch 521
 (.leaf (.quota 2))
 (.branch 523
 (.branch 522
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))))
 (.branch 533
 (.branch 529
 (.branch 527
 (.leaf (.quota 2))
 (.branch 528
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 531
 (.branch 530
 (.leaf (.quota 3))
 (.leaf (.quota 2)))
 (.branch 532
 (.leaf (.quota 3))
 (.leaf (.quota 2)))))
 (.leaf (.quota 2))))
 (.branch 557
 (.branch 549
 (.leaf (.quota 2))
 (.branch 553
 (.leaf (.quota 2))
 (.branch 555
 (.leaf (.quota 2))
 (.branch 556
 (.leaf (.matching Nonrational.OldTerminalMatches.M015.r0967))
 (.leaf (.quota 2))))))
 (.branch 565
 (.branch 561
 (.leaf (.quota 2))
 (.branch 563
 (.branch 562
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.branch 564
 (.leaf (.quota 2))
 (.leaf (.quota 3)))))
 (.branch 569
 (.branch 567
 (.leaf (.quota 2))
 (.branch 568
 (.leaf (.quota 3))
 (.leaf (.quota 2))))
 (.branch 571
 (.branch 570
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.branch 572
 (.leaf (.quota 2))
 (.leaf (.quota 3))))))))
 (.branch 605
 (.branch 589
 (.branch 581
 (.branch 577
 (.branch 575
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.branch 579
 (.branch 578
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.leaf (.quota 2))))
 (.branch 585
 (.leaf (.quota 2))
 (.branch 587
 (.branch 586
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))))
 (.branch 597
 (.branch 593
 (.branch 591
 (.leaf (.quota 2))
 (.branch 592
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 595
 (.branch 594
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.branch 596
 (.leaf (.quota 2))
 (.leaf (.quota 3)))))
 (.leaf (.quota 2))))
 (.branch 621
 (.branch 613
 (.branch 609
 (.branch 607
 (.leaf (.quota 2))
 (.branch 608
 (.leaf (.matching Nonrational.OldTerminalMatches.M015.r0968))
 (.leaf (.matching Nonrational.OldTerminalMatches.M015.r0969))))
 (.branch 611
 (.leaf (.quota 3))
 (.branch 612
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.leaf (.quota 2)))
 (.branch 629
 (.branch 625
 (.branch 623
 (.branch 622
 (.leaf (.quota 3))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 633
 (.branch 631
 (.leaf (.quota 2))
 (.branch 632
 (.leaf (.quota 3))
 (.leaf (.quota 2))))
 (.branch 635
 (.leaf (.quota 2))
 (.branch 636
 (.leaf (.matching Nonrational.OldTerminalMatches.M015.r0970))
 (.leaf (.quota 2)))))))))
 (.branch 701
 (.branch 669
 (.branch 653
 (.branch 645
 (.branch 641
 (.leaf (.quota 2))
 (.branch 643
 (.branch 642
 (.leaf (.quota 3))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.branch 649
 (.leaf (.quota 2))
 (.branch 651
 (.branch 650
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.leaf (.quota 2)))))
 (.branch 661
 (.branch 657
 (.branch 655
 (.leaf (.quota 2))
 (.branch 656
 (.leaf (.matching Nonrational.OldTerminalMatches.M015.r0971))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.branch 665
 (.branch 663
 (.leaf (.quota 2))
 (.branch 664
 (.leaf (.matching Nonrational.OldTerminalMatches.M015.r0972))
 (.leaf (.quota 2))))
 (.branch 667
 (.branch 666
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 668
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))))
 (.branch 685
 (.branch 677
 (.leaf (.quota 2))
 (.branch 681
 (.branch 679
 (.branch 678
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))
 (.branch 683
 (.branch 682
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))))
 (.branch 693
 (.leaf (.quota 2))
 (.branch 697
 (.leaf (.quota 2))
 (.branch 699
 (.branch 698
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))))))
 (.branch 733
 (.branch 717
 (.branch 709
 (.branch 705
 (.branch 703
 (.branch 702
 (.leaf (.quota 2))
 (.leaf .euler))
 (.branch 704
 (.leaf (.quota 3))
 (.leaf (.incidence 0))))
 (.branch 707
 (.branch 706
 (.leaf (.incidence 0))
 (.leaf (.quota 2)))
 (.branch 708
 (.leaf (.quota 2))
 (.leaf (.quota 3)))))
 (.branch 713
 (.branch 711
 (.branch 710
 (.leaf (.quota 3))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 715
 (.branch 714
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.leaf (.quota 2)))))
 (.branch 725
 (.branch 721
 (.branch 719
 (.leaf (.quota 2))
 (.branch 720
 (.leaf (.quota 3))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.branch 729
 (.branch 727
 (.branch 726
 (.leaf (.quota 3))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))))
 (.branch 749
 (.branch 741
 (.branch 737
 (.branch 735
 (.leaf (.quota 2))
 (.branch 736
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 2)))
 (.branch 745
 (.leaf (.quota 2))
 (.branch 747
 (.leaf (.quota 3))
 (.leaf (.quota 2)))))
 (.branch 757
 (.branch 753
 (.branch 751
 (.leaf (.quota 3))
 (.leaf (.quota 2)))
 (.branch 755
 (.branch 754
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 756
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 761
 (.branch 759
 (.leaf (.quota 2))
 (.branch 760
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 763
 (.branch 762
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 764
 (.leaf (.incidence 0))
 (.leaf (.quota 2))))))))))
 (.branch 893
 (.branch 829
 (.branch 797
 (.branch 781
 (.branch 773
 (.leaf (.quota 2))
 (.branch 777
 (.leaf (.quota 2))
 (.branch 779
 (.leaf (.quota 2))
 (.branch 780
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 789
 (.branch 785
 (.leaf (.quota 2))
 (.branch 787
 (.branch 786
 (.leaf (.quota 1))
 (.leaf (.quota 3)))
 (.branch 788
 (.leaf (.quota 3))
 (.leaf (.quota 2)))))
 (.branch 793
 (.branch 791
 (.branch 790
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 792
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 2)))))
 (.branch 813
 (.branch 805
 (.branch 801
 (.branch 799
 (.branch 798
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.branch 800
 (.leaf (.quota 3))
 (.leaf (.quota 2))))
 (.branch 803
 (.branch 802
 (.leaf (.quota 2))
 (.leaf (.incidence 0)))
 (.branch 804
 (.leaf (.quota 2))
 (.leaf (.quota 3)))))
 (.branch 809
 (.branch 807
 (.branch 806
 (.leaf (.incidence 0))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 811
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 821
 (.branch 817
 (.branch 815
 (.branch 814
 (.leaf (.quota 1))
 (.leaf (.incidence 0)))
 (.leaf (.quota 2)))
 (.branch 819
 (.branch 818
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2))))
 (.branch 825
 (.branch 823
 (.leaf (.quota 2))
 (.branch 824
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 2))))))
 (.branch 861
 (.branch 845
 (.branch 837
 (.leaf (.quota 2))
 (.branch 841
 (.branch 839
 (.leaf (.quota 2))
 (.branch 840
 (.leaf (.quota 3))
 (.leaf (.quota 2))))
 (.branch 843
 (.leaf (.quota 2))
 (.branch 844
 (.leaf (.quota 2))
 (.leaf .euler)))))
 (.branch 853
 (.branch 849
 (.leaf (.quota 2))
 (.branch 851
 (.branch 850
 (.leaf (.quota 3))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.branch 857
 (.branch 855
 (.branch 854
 (.leaf (.matching Nonrational.OldTerminalMatches.M015.r0973))
 (.leaf (.matching Nonrational.OldTerminalMatches.M015.r0974)))
 (.branch 856
 (.leaf (.matching Nonrational.OldTerminalMatches.M015.r0975))
 (.leaf (.quota 2))))
 (.branch 859
 (.branch 858
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M015.r0976)))
 (.branch 860
 (.leaf (.matching Nonrational.OldTerminalMatches.M015.r0977))
 (.leaf (.matching Nonrational.OldTerminalMatches.M015.r0978)))))))
 (.branch 877
 (.branch 869
 (.branch 865
 (.branch 863
 (.branch 862
 (.leaf (.matching Nonrational.OldTerminalMatches.M015.r0979))
 (.leaf (.quota 2)))
 (.branch 864
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 867
 (.branch 866
 (.leaf (.matching Nonrational.OldTerminalMatches.M015.r0980))
 (.leaf (.quota 2)))
 (.branch 868
 (.leaf (.matching Nonrational.OldTerminalMatches.M015.r0981))
 (.leaf (.matching Nonrational.OldTerminalMatches.M015.r0982)))))
 (.branch 873
 (.branch 871
 (.leaf (.quota 3))
 (.branch 872
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 875
 (.leaf (.incidence 5))
 (.branch 876
 (.leaf (.matching Nonrational.OldTerminalMatches.M015.r0983))
 (.leaf (.matching Nonrational.OldTerminalMatches.M015.r0984))))))
 (.branch 885
 (.branch 881
 (.branch 879
 (.branch 878
 (.leaf (.quota 1))
 (.leaf (.incidence 5)))
 (.leaf (.quota 2)))
 (.branch 883
 (.branch 882
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 884
 (.leaf (.matching Nonrational.OldTerminalMatches.M015.r0985))
 (.leaf (.matching Nonrational.OldTerminalMatches.M015.r0986)))))
 (.branch 889
 (.branch 887
 (.branch 886
 (.leaf (.matching Nonrational.OldTerminalMatches.M015.r0987))
 (.leaf (.matching Nonrational.OldTerminalMatches.M015.r0988)))
 (.branch 888
 (.leaf (.matching Nonrational.OldTerminalMatches.M015.r0989))
 (.leaf (.matching Nonrational.OldTerminalMatches.M015.r0990))))
 (.branch 891
 (.branch 890
 (.leaf (.matching Nonrational.OldTerminalMatches.M015.r0991))
 (.leaf (.quota 2)))
 (.branch 892
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))))))
 (.branch 957
 (.branch 925
 (.branch 909
 (.branch 901
 (.branch 897
 (.branch 895
 (.branch 894
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 896
 (.leaf (.matching Nonrational.OldTerminalMatches.M015.r0992))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 905
 (.branch 903
 (.branch 902
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 904
 (.leaf (.quota 1))
 (.leaf (.quota 3))))
 (.leaf (.quota 2))))
 (.branch 917
 (.branch 913
 (.branch 911
 (.leaf (.quota 2))
 (.branch 912
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M015.r0993))))
 (.leaf (.quota 2)))
 (.branch 921
 (.branch 919
 (.leaf (.quota 2))
 (.branch 920
 (.leaf .euler)
 (.leaf (.quota 2))))
 (.branch 923
 (.branch 922
 (.leaf (.incidence 9))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))))
 (.branch 941
 (.branch 933
 (.branch 929
 (.branch 927
 (.branch 926
 (.leaf (.quota 2))
 (.leaf .euler))
 (.branch 928
 (.leaf .euler)
 (.leaf (.quota 2))))
 (.branch 931
 (.leaf (.quota 2))
 (.branch 932
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 937
 (.branch 935
 (.branch 934
 (.leaf (.matching Nonrational.OldTerminalMatches.M015.r0994))
 (.leaf (.quota 2)))
 (.branch 936
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 939
 (.branch 938
 (.leaf (.matching Nonrational.OldTerminalMatches.M015.r0995))
 (.leaf (.matching Nonrational.OldTerminalMatches.M015.r0996)))
 (.leaf (.quota 2)))))
 (.branch 949
 (.branch 945
 (.leaf (.quota 2))
 (.branch 947
 (.leaf (.quota 2))
 (.branch 948
 (.leaf (.quota 3))
 (.leaf (.matching Nonrational.OldTerminalMatches.M015.r0997)))))
 (.branch 953
 (.branch 951
 (.branch 950
 (.leaf (.matching Nonrational.OldTerminalMatches.M015.r0998))
 (.leaf (.matching Nonrational.OldTerminalMatches.M015.r0999)))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))))
 (.branch 989
 (.branch 973
 (.branch 965
 (.branch 961
 (.branch 959
 (.leaf (.quota 2))
 (.branch 960
 (.leaf (.quota 2))
 (.leaf (.incidence 5))))
 (.branch 963
 (.branch 962
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.branch 964
 (.leaf (.quota 3))
 (.leaf (.quota 2)))))
 (.branch 969
 (.branch 967
 (.branch 966
 (.leaf (.quota 3))
 (.leaf (.quota 2)))
 (.branch 968
 (.leaf (.quota 3))
 (.leaf (.quota 2))))
 (.leaf (.quota 2))))
 (.branch 981
 (.branch 977
 (.leaf (.quota 2))
 (.branch 979
 (.branch 978
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 3))))
 (.branch 985
 (.branch 983
 (.branch 982
 (.leaf (.quota 3))
 (.leaf (.quota 2)))
 (.branch 984
 (.leaf (.quota 2))
 (.leaf (.quota 3))))
 (.branch 987
 (.branch 986
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2))))))
 (.branch 1005
 (.branch 997
 (.branch 993
 (.branch 991
 (.branch 990
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 992
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 995
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 1001
 (.branch 999
 (.branch 998
 (.leaf (.quota 3))
 (.leaf (.incidence 9)))
 (.branch 1000
 (.leaf (.quota 2))
 (.leaf (.quota 3))))
 (.leaf (.quota 2))))
 (.branch 1013
 (.branch 1009
 (.branch 1007
 (.leaf (.quota 2))
 (.branch 1008
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 1011
 (.leaf (.quota 2))
 (.branch 1012
 (.leaf (.incidence 5))
 (.leaf (.quota 2)))))
 (.branch 1017
 (.branch 1015
 (.branch 1014
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))))))))
 (.branch 1531
 (.branch 1276
 (.branch 1148
 (.branch 1084
 (.branch 1052
 (.branch 1036
 (.branch 1028
 (.branch 1024
 (.branch 1022
 (.leaf (.incidence 5))
 (.leaf (.quota 2)))
 (.branch 1026
 (.branch 1025
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 1027
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 1032
 (.leaf (.quota 2))
 (.branch 1034
 (.branch 1033
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))))
 (.branch 1044
 (.branch 1040
 (.branch 1038
 (.leaf (.quota 2))
 (.branch 1039
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M015.r1000))))
 (.branch 1042
 (.leaf (.quota 2))
 (.leaf .euler)))
 (.branch 1048
 (.branch 1046
 (.branch 1045
 (.leaf (.matching Nonrational.OldTerminalMatches.M015.r1001))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))))
 (.branch 1068
 (.branch 1060
 (.branch 1056
 (.branch 1054
 (.leaf (.quota 2))
 (.branch 1055
 (.leaf (.quota 2))
 (.leaf .euler)))
 (.leaf (.quota 2)))
 (.branch 1064
 (.branch 1062
 (.branch 1061
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 1066
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 1076
 (.branch 1072
 (.branch 1070
 (.leaf (.quota 2))
 (.branch 1071
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 2)))
 (.branch 1080
 (.branch 1078
 (.branch 1077
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M015.r1002)))
 (.branch 1079
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 1082
 (.leaf (.quota 2))
 (.branch 1083
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))))
 (.branch 1116
 (.branch 1100
 (.branch 1092
 (.branch 1088
 (.branch 1086
 (.leaf (.quota 2))
 (.branch 1087
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M015.r1003))))
 (.leaf (.quota 2)))
 (.branch 1096
 (.branch 1094
 (.leaf (.quota 2))
 (.branch 1095
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 1098
 (.leaf (.quota 2))
 (.branch 1099
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 1108
 (.branch 1104
 (.branch 1102
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 1106
 (.leaf (.quota 1))
 (.branch 1107
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 1112
 (.branch 1110
 (.leaf (.quota 1))
 (.branch 1111
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 1114
 (.branch 1113
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 1115
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))))
 (.branch 1132
 (.branch 1124
 (.branch 1120
 (.branch 1118
 (.leaf (.quota 2))
 (.branch 1119
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 1122
 (.branch 1121
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M015.r1004)))
 (.branch 1123
 (.leaf (.matching Nonrational.OldTerminalMatches.M015.r1005))
 (.leaf (.quota 2)))))
 (.branch 1128
 (.branch 1126
 (.leaf (.quota 2))
 (.branch 1127
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 1130
 (.branch 1129
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 1131
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 1140
 (.branch 1136
 (.branch 1134
 (.leaf (.quota 2))
 (.branch 1135
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 1138
 (.leaf (.quota 2))
 (.branch 1139
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.leaf (.quota 2))))))
 (.branch 1212
 (.branch 1180
 (.branch 1164
 (.branch 1156
 (.leaf (.quota 2))
 (.branch 1160
 (.leaf (.quota 2))
 (.branch 1162
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 1172
 (.branch 1168
 (.leaf (.quota 2))
 (.branch 1170
 (.leaf (.quota 2))
 (.branch 1171
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 1176
 (.branch 1174
 (.leaf (.quota 2))
 (.branch 1175
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 2)))))
 (.branch 1196
 (.branch 1188
 (.leaf (.quota 2))
 (.branch 1192
 (.leaf (.quota 2))
 (.branch 1194
 (.leaf (.quota 2))
 (.branch 1195
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 1204
 (.branch 1200
 (.branch 1198
 (.leaf (.quota 2))
 (.branch 1199
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))))
 (.branch 1244
 (.branch 1228
 (.branch 1220
 (.branch 1216
 (.branch 1214
 (.leaf (.quota 2))
 (.branch 1215
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.branch 1224
 (.branch 1222
 (.branch 1221
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 1223
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 1226
 (.branch 1225
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 1227
 (.leaf (.incidence 5))
 (.leaf (.quota 1))))))
 (.branch 1236
 (.branch 1232
 (.branch 1230
 (.leaf (.quota 2))
 (.branch 1231
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 2)))
 (.branch 1240
 (.branch 1238
 (.branch 1237
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))))
 (.branch 1260
 (.branch 1252
 (.branch 1248
 (.branch 1246
 (.leaf (.quota 2))
 (.branch 1247
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 1250
 (.leaf (.quota 2))
 (.branch 1251
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 1256
 (.branch 1254
 (.branch 1253
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 1255
 (.leaf (.quota 2))
 (.leaf (.incidence 5))))
 (.leaf (.quota 2))))
 (.branch 1268
 (.branch 1264
 (.branch 1262
 (.leaf (.quota 2))
 (.branch 1263
 (.leaf (.incidence 5))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))))))
 (.branch 1403
 (.branch 1339
 (.branch 1307
 (.branch 1291
 (.branch 1283
 (.branch 1279
 (.leaf (.quota 2))
 (.branch 1281
 (.leaf (.quota 2))
 (.branch 1282
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 1287
 (.branch 1285
 (.branch 1284
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 1289
 (.leaf (.quota 2))
 (.branch 1290
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 1299
 (.branch 1295
 (.leaf (.quota 2))
 (.branch 1297
 (.leaf (.quota 2))
 (.branch 1298
 (.leaf (.matching Nonrational.OldTerminalMatches.M015.r1006))
 (.leaf (.quota 2)))))
 (.branch 1303
 (.branch 1301
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))))
 (.leaf (.quota 2)))
 (.branch 1371
 (.branch 1355
 (.branch 1347
 (.branch 1343
 (.branch 1341
 (.leaf (.quota 2))
 (.branch 1342
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M015.r1007))))
 (.branch 1345
 (.branch 1344
 (.leaf (.matching Nonrational.OldTerminalMatches.M015.r1008))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.branch 1351
 (.leaf (.quota 2))
 (.branch 1353
 (.branch 1352
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))))
 (.branch 1363
 (.branch 1359
 (.branch 1357
 (.branch 1356
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 1367
 (.leaf (.quota 2))
 (.branch 1369
 (.branch 1368
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2))))))
 (.branch 1387
 (.branch 1379
 (.branch 1375
 (.leaf (.quota 2))
 (.branch 1377
 (.branch 1376
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.branch 1395
 (.branch 1391
 (.leaf (.quota 2))
 (.branch 1393
 (.branch 1392
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.branch 1394
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 1399
 (.branch 1397
 (.branch 1396
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 1401
 (.leaf (.quota 2))
 (.branch 1402
 (.leaf (.quota 3))
 (.leaf (.quota 2)))))))))
 (.branch 1467
 (.branch 1435
 (.branch 1419
 (.branch 1411
 (.branch 1407
 (.branch 1405
 (.branch 1404
 (.leaf (.quota 3))
 (.leaf (.quota 2)))
 (.leaf (.quota 1)))
 (.branch 1409
 (.leaf (.quota 2))
 (.branch 1410
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 1415
 (.branch 1413
 (.leaf (.quota 2))
 (.branch 1414
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 1417
 (.leaf (.quota 2))
 (.branch 1418
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 1427
 (.branch 1423
 (.leaf (.quota 2))
 (.branch 1425
 (.branch 1424
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.leaf (.quota 2))))
 (.branch 1451
 (.branch 1443
 (.branch 1439
 (.branch 1437
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.leaf (.quota 2)))
 (.branch 1447
 (.leaf (.quota 2))
 (.branch 1449
 (.branch 1448
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.branch 1450
 (.leaf (.quota 3))
 (.leaf (.quota 2))))))
 (.branch 1459
 (.branch 1455
 (.branch 1453
 (.leaf (.quota 2))
 (.branch 1454
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 1457
 (.branch 1456
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.branch 1463
 (.branch 1461
 (.branch 1460
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))))
 (.branch 1499
 (.branch 1483
 (.branch 1475
 (.branch 1471
 (.leaf (.quota 2))
 (.branch 1473
 (.branch 1472
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M015.r1009)))
 (.branch 1474
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M015.r1010)))))
 (.branch 1479
 (.branch 1477
 (.branch 1476
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M015.r1011)))
 (.leaf (.quota 2)))
 (.branch 1481
 (.leaf (.quota 2))
 (.branch 1482
 (.leaf (.matching Nonrational.OldTerminalMatches.M015.r1012))
 (.leaf (.matching Nonrational.OldTerminalMatches.M015.r1013))))))
 (.branch 1491
 (.branch 1487
 (.branch 1485
 (.branch 1484
 (.leaf (.matching Nonrational.OldTerminalMatches.M015.r1014))
 (.leaf (.quota 3)))
 (.branch 1486
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 1489
 (.leaf (.quota 2))
 (.branch 1490
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 1495
 (.branch 1493
 (.leaf (.quota 2))
 (.branch 1494
 (.leaf (.quota 2))
 (.leaf (.quota 3))))
 (.branch 1497
 (.branch 1496
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M015.r1015)))
 (.leaf (.quota 1))))))
 (.branch 1515
 (.branch 1507
 (.branch 1503
 (.branch 1501
 (.leaf (.quota 2))
 (.branch 1502
 (.leaf (.quota 1))
 (.leaf (.matching Nonrational.OldTerminalMatches.M015.r1016))))
 (.branch 1505
 (.branch 1504
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 1511
 (.branch 1509
 (.branch 1508
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M015.r1017)))
 (.branch 1510
 (.leaf (.matching Nonrational.OldTerminalMatches.M015.r1018))
 (.leaf (.quota 1))))
 (.branch 1513
 (.leaf (.quota 1))
 (.branch 1514
 (.leaf (.matching Nonrational.OldTerminalMatches.M015.r1019))
 (.leaf (.quota 1))))))
 (.branch 1523
 (.branch 1519
 (.leaf (.quota 1))
 (.branch 1521
 (.branch 1520
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2))))
 (.branch 1527
 (.branch 1525
 (.leaf (.quota 1))
 (.branch 1526
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 1529
 (.branch 1528
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2))))))))))
 (.branch 1786
 (.branch 1658
 (.branch 1594
 (.branch 1562
 (.branch 1546
 (.branch 1538
 (.branch 1534
 (.leaf (.quota 2))
 (.branch 1536
 (.branch 1535
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 1537
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 1542
 (.branch 1540
 (.branch 1539
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 1541
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 1544
 (.leaf (.quota 2))
 (.branch 1545
 (.leaf (.quota 3))
 (.leaf (.quota 2))))))
 (.branch 1554
 (.branch 1550
 (.branch 1548
 (.branch 1547
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 1552
 (.leaf (.quota 2))
 (.branch 1553
 (.leaf (.matching Nonrational.OldTerminalMatches.M015.r1020))
 (.leaf (.matching Nonrational.OldTerminalMatches.M015.r1021)))))
 (.branch 1558
 (.branch 1556
 (.branch 1555
 (.leaf (.quota 3))
 (.leaf (.quota 2)))
 (.branch 1557
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M015.r1022))))
 (.branch 1560
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 1578
 (.branch 1570
 (.branch 1566
 (.branch 1564
 (.leaf (.quota 2))
 (.branch 1565
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 1568
 (.leaf (.quota 2))
 (.branch 1569
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.leaf (.quota 1)))
 (.branch 1586
 (.branch 1582
 (.branch 1580
 (.branch 1579
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 1584
 (.branch 1583
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2))))
 (.branch 1590
 (.branch 1588
 (.branch 1587
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))
 (.branch 1592
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))))
 (.branch 1626
 (.branch 1610
 (.branch 1602
 (.branch 1598
 (.branch 1596
 (.branch 1595
 (.leaf (.quota 1))
 (.leaf (.matching Nonrational.OldTerminalMatches.M015.r1023)))
 (.branch 1597
 (.leaf (.matching Nonrational.OldTerminalMatches.M016.r1024))
 (.leaf (.quota 1))))
 (.leaf (.quota 2)))
 (.branch 1606
 (.branch 1604
 (.leaf (.quota 2))
 (.branch 1605
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 2))))
 (.branch 1618
 (.branch 1614
 (.branch 1612
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))
 (.branch 1622
 (.branch 1620
 (.branch 1619
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 1621
 (.leaf (.quota 2))
 (.leaf (.quota 3))))
 (.branch 1624
 (.leaf (.quota 2))
 (.branch 1625
 (.leaf (.quota 2))
 (.leaf (.quota 3)))))))
 (.branch 1642
 (.branch 1634
 (.branch 1630
 (.branch 1628
 (.branch 1627
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.branch 1629
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 1632
 (.branch 1631
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M016.r1025)))
 (.branch 1633
 (.leaf (.matching Nonrational.OldTerminalMatches.M016.r1026))
 (.leaf (.quota 2)))))
 (.branch 1638
 (.branch 1636
 (.branch 1635
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M016.r1027)))
 (.branch 1637
 (.leaf (.matching Nonrational.OldTerminalMatches.M016.r1028))
 (.leaf (.matching Nonrational.OldTerminalMatches.M016.r1029))))
 (.branch 1640
 (.branch 1639
 (.leaf (.matching Nonrational.OldTerminalMatches.M016.r1030))
 (.leaf (.quota 2)))
 (.branch 1641
 (.leaf (.matching Nonrational.OldTerminalMatches.M016.r1031))
 (.leaf (.quota 2))))))
 (.branch 1650
 (.branch 1646
 (.leaf (.quota 2))
 (.branch 1648
 (.branch 1647
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.branch 1654
 (.branch 1652
 (.branch 1651
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 1653
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 1656
 (.branch 1655
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 1657
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))))))
 (.branch 1722
 (.branch 1690
 (.branch 1674
 (.branch 1666
 (.branch 1662
 (.branch 1660
 (.leaf (.quota 2))
 (.branch 1661
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 2)))
 (.branch 1670
 (.branch 1668
 (.leaf (.quota 2))
 (.branch 1669
 (.leaf (.quota 1))
 (.leaf (.matching Nonrational.OldTerminalMatches.M016.r1032))))
 (.leaf (.quota 2))))
 (.branch 1682
 (.branch 1678
 (.branch 1676
 (.leaf (.quota 2))
 (.branch 1677
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.branch 1686
 (.branch 1684
 (.leaf (.quota 1))
 (.branch 1685
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))))
 (.branch 1706
 (.leaf (.quota 2))
 (.branch 1714
 (.branch 1710
 (.leaf (.quota 2))
 (.branch 1712
 (.branch 1711
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2))))
 (.branch 1718
 (.branch 1716
 (.branch 1715
 (.leaf (.quota 3))
 (.leaf (.quota 2)))
 (.branch 1717
 (.leaf (.quota 3))
 (.leaf (.quota 2))))
 (.branch 1720
 (.leaf (.quota 2))
 (.branch 1721
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))))
 (.branch 1754
 (.branch 1738
 (.leaf (.quota 2))
 (.branch 1746
 (.branch 1742
 (.branch 1740
 (.branch 1739
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.leaf (.quota 3)))
 (.leaf (.quota 2)))
 (.branch 1750
 (.leaf (.quota 2))
 (.branch 1752
 (.branch 1751
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.branch 1753
 (.leaf (.quota 3))
 (.leaf (.quota 2)))))))
 (.branch 1770
 (.branch 1762
 (.branch 1758
 (.leaf (.quota 2))
 (.branch 1760
 (.branch 1759
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 1761
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 1766
 (.leaf (.quota 2))
 (.branch 1768
 (.leaf (.quota 2))
 (.branch 1769
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 1778
 (.branch 1774
 (.leaf (.quota 2))
 (.branch 1776
 (.leaf (.quota 2))
 (.branch 1777
 (.leaf (.quota 2))
 (.leaf (.quota 3)))))
 (.branch 1782
 (.branch 1780
 (.branch 1779
 (.leaf (.quota 3))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 1784
 (.branch 1783
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 3)))))))))
 (.branch 1914
 (.branch 1850
 (.branch 1818
 (.branch 1802
 (.leaf (.quota 2))
 (.branch 1810
 (.branch 1806
 (.branch 1804
 (.leaf (.quota 2))
 (.branch 1805
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 1808
 (.branch 1807
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.leaf (.quota 2))))
 (.leaf (.quota 2))))
 (.branch 1834
 (.branch 1826
 (.branch 1822
 (.branch 1820
 (.branch 1819
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 1830
 (.branch 1828
 (.leaf (.quota 2))
 (.branch 1829
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 1832
 (.branch 1831
 (.leaf (.quota 3))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))))
 (.branch 1842
 (.branch 1838
 (.branch 1836
 (.leaf (.quota 2))
 (.branch 1837
 (.leaf (.quota 2))
 (.leaf (.quota 3))))
 (.leaf (.quota 2)))
 (.branch 1846
 (.branch 1844
 (.leaf (.quota 2))
 (.branch 1845
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 2))))))
 (.branch 1882
 (.branch 1866
 (.branch 1858
 (.branch 1854
 (.branch 1852
 (.leaf (.quota 2))
 (.branch 1853
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 2)))
 (.branch 1862
 (.branch 1860
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 1864
 (.branch 1863
 (.leaf (.quota 3))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))))
 (.branch 1874
 (.branch 1870
 (.leaf (.quota 2))
 (.branch 1872
 (.leaf (.quota 2))
 (.branch 1873
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.leaf (.quota 2))))
 (.branch 1898
 (.branch 1890
 (.branch 1886
 (.branch 1884
 (.leaf (.quota 2))
 (.branch 1885
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.branch 1894
 (.branch 1892
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 1896
 (.branch 1895
 (.leaf (.quota 1))
 (.leaf (.quota 3)))
 (.leaf (.quota 2)))))
 (.leaf (.quota 2)))))
 (.branch 1978
 (.branch 1946
 (.branch 1930
 (.branch 1922
 (.leaf (.quota 2))
 (.branch 1926
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 1938
 (.branch 1934
 (.branch 1932
 (.branch 1931
 (.leaf (.quota 3))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 1942
 (.branch 1940
 (.branch 1939
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 1944
 (.leaf (.quota 1))
 (.branch 1945
 (.leaf (.quota 1))
 (.leaf (.quota 3)))))))
 (.branch 1962
 (.branch 1954
 (.branch 1950
 (.branch 1948
 (.branch 1947
 (.leaf (.quota 1))
 (.leaf (.quota 3)))
 (.branch 1949
 (.leaf (.quota 3))
 (.leaf (.quota 1))))
 (.branch 1952
 (.leaf (.quota 3))
 (.branch 1953
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.leaf (.quota 2)))
 (.branch 1970
 (.branch 1966
 (.leaf (.quota 2))
 (.branch 1968
 (.leaf (.quota 2))
 (.branch 1969
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 1974
 (.branch 1972
 (.branch 1971
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 1976
 (.branch 1975
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 3)))))))
 (.branch 2010
 (.branch 1994
 (.branch 1986
 (.branch 1982
 (.branch 1980
 (.branch 1979
 (.leaf (.quota 1))
 (.leaf (.quota 3)))
 (.leaf (.quota 1)))
 (.branch 1984
 (.branch 1983
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.branch 1990
 (.branch 1988
 (.leaf (.quota 2))
 (.branch 1989
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 2))))
 (.branch 2002
 (.branch 1998
 (.leaf (.quota 2))
 (.branch 2000
 (.branch 1999
 (.leaf (.quota 3))
 (.leaf (.quota 2)))
 (.branch 2001
 (.leaf (.quota 3))
 (.leaf (.quota 2)))))
 (.branch 2006
 (.branch 2004
 (.leaf (.quota 2))
 (.branch 2005
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 2008
 (.branch 2007
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 2009
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))))
 (.branch 2026
 (.branch 2018
 (.branch 2014
 (.branch 2012
 (.branch 2011
 (.leaf (.quota 3))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 2034
 (.branch 2030
 (.branch 2028
 (.branch 2027
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 2029
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 2032
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 2038
 (.branch 2036
 (.branch 2035
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 2037
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 2040
 (.branch 2039
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))))))))))
 (.branch 3063
 (.branch 2552
 (.branch 2297
 (.branch 2169
 (.branch 2105
 (.branch 2073
 (.branch 2057
 (.branch 2049
 (.branch 2045
 (.branch 2043
 (.leaf (.quota 3))
 (.branch 2044
 (.leaf (.quota 2))
 (.leaf (.incidence 0))))
 (.leaf (.quota 2)))
 (.branch 2053
 (.branch 2051
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.branch 2055
 (.branch 2054
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.leaf (.quota 2)))))
 (.branch 2065
 (.leaf (.quota 2))
 (.branch 2069
 (.branch 2067
 (.branch 2066
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.leaf (.quota 2)))
 (.branch 2071
 (.branch 2070
 (.leaf (.quota 3))
 (.leaf (.quota 1)))
 (.branch 2072
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))))
 (.branch 2089
 (.branch 2081
 (.leaf (.quota 2))
 (.branch 2085
 (.branch 2083
 (.branch 2082
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 2084
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1))))
 (.branch 2097
 (.branch 2093
 (.branch 2091
 (.branch 2090
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.leaf (.quota 3)))
 (.branch 2095
 (.leaf (.quota 1))
 (.branch 2096
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 2101
 (.branch 2099
 (.leaf (.quota 3))
 (.branch 2100
 (.leaf (.quota 3))
 (.leaf (.quota 2))))
 (.branch 2103
 (.leaf (.quota 1))
 (.branch 2104
 (.leaf (.quota 2))
 (.leaf (.quota 3))))))))
 (.branch 2137
 (.branch 2121
 (.branch 2113
 (.branch 2109
 (.branch 2107
 (.branch 2106
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 2111
 (.leaf (.quota 2))
 (.branch 2112
 (.leaf (.quota 2))
 (.leaf (.quota 3)))))
 (.branch 2117
 (.branch 2115
 (.branch 2114
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.leaf (.quota 2)))
 (.branch 2119
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 2129
 (.branch 2125
 (.branch 2123
 (.leaf (.quota 3))
 (.branch 2124
 (.leaf (.quota 3))
 (.leaf (.quota 1))))
 (.branch 2127
 (.leaf (.quota 2))
 (.branch 2128
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.leaf (.quota 2))))
 (.branch 2153
 (.branch 2145
 (.leaf (.quota 2))
 (.branch 2149
 (.branch 2147
 (.leaf (.quota 2))
 (.branch 2148
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 2151
 (.leaf (.quota 2))
 (.branch 2152
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 2161
 (.branch 2157
 (.branch 2155
 (.leaf (.quota 2))
 (.branch 2156
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))))
 (.branch 2233
 (.branch 2201
 (.branch 2185
 (.branch 2177
 (.branch 2173
 (.branch 2171
 (.branch 2170
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 2181
 (.leaf (.quota 2))
 (.branch 2183
 (.branch 2182
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.leaf (.quota 1)))))
 (.branch 2193
 (.branch 2189
 (.branch 2187
 (.branch 2186
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 2188
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 2191
 (.branch 2190
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.branch 2265
 (.branch 2249
 (.branch 2241
 (.branch 2237
 (.leaf (.quota 2))
 (.branch 2239
 (.leaf (.quota 2))
 (.branch 2240
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 2245
 (.branch 2243
 (.leaf (.quota 2))
 (.branch 2244
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 2247
 (.branch 2246
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))))
 (.branch 2257
 (.branch 2253
 (.branch 2251
 (.leaf (.quota 2))
 (.branch 2252
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 2)))
 (.branch 2261
 (.branch 2259
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.branch 2263
 (.leaf (.quota 3))
 (.branch 2264
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))))
 (.branch 2281
 (.branch 2273
 (.branch 2269
 (.branch 2267
 (.branch 2266
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.branch 2268
 (.leaf (.quota 3))
 (.leaf (.quota 2))))
 (.branch 2271
 (.branch 2270
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.branch 2277
 (.branch 2275
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.branch 2289
 (.branch 2285
 (.branch 2283
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 2287
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 2293
 (.leaf (.quota 2))
 (.branch 2295
 (.leaf (.quota 2))
 (.branch 2296
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M016.r1033))))))))))
 (.branch 2424
 (.branch 2360
 (.branch 2328
 (.branch 2312
 (.branch 2304
 (.branch 2300
 (.leaf (.quota 2))
 (.branch 2302
 (.leaf (.quota 2))
 (.branch 2303
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M016.r1034)))))
 (.branch 2308
 (.branch 2306
 (.branch 2305
 (.leaf (.matching Nonrational.OldTerminalMatches.M016.r1035))
 (.leaf (.quota 2)))
 (.branch 2307
 (.leaf (.matching Nonrational.OldTerminalMatches.M016.r1036))
 (.leaf (.quota 1))))
 (.branch 2310
 (.branch 2309
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))))
 (.branch 2320
 (.branch 2316
 (.leaf (.quota 2))
 (.branch 2318
 (.branch 2317
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2))))
 (.branch 2324
 (.branch 2322
 (.branch 2321
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 2323
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 2326
 (.branch 2325
 (.leaf (.quota 3))
 (.leaf (.quota 2)))
 (.branch 2327
 (.leaf (.quota 3))
 (.leaf (.quota 2)))))))
 (.branch 2344
 (.branch 2336
 (.branch 2332
 (.branch 2330
 (.branch 2329
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 2340
 (.branch 2338
 (.branch 2337
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 2342
 (.leaf (.quota 2))
 (.branch 2343
 (.leaf (.quota 1))
 (.leaf (.matching Nonrational.OldTerminalMatches.M016.r1037))))))
 (.branch 2352
 (.branch 2348
 (.branch 2346
 (.branch 2345
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 2347
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M016.r1038))))
 (.branch 2350
 (.leaf (.quota 2))
 (.branch 2351
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 2356
 (.leaf (.quota 2))
 (.branch 2358
 (.branch 2357
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 2359
 (.leaf (.quota 2))
 (.leaf .euler)))))))
 (.branch 2392
 (.branch 2376
 (.branch 2368
 (.branch 2364
 (.branch 2362
 (.branch 2361
 (.leaf .euler)
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 2366
 (.branch 2365
 (.leaf (.matching Nonrational.OldTerminalMatches.M016.r1039))
 (.leaf (.quota 2)))
 (.leaf (.quota 3))))
 (.branch 2372
 (.branch 2370
 (.branch 2369
 (.leaf (.quota 3))
 (.leaf (.quota 2)))
 (.branch 2371
 (.leaf (.quota 3))
 (.leaf (.incidence 9))))
 (.branch 2374
 (.branch 2373
 (.leaf (.quota 3))
 (.leaf (.quota 1)))
 (.branch 2375
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 2384
 (.branch 2380
 (.branch 2378
 (.leaf (.quota 2))
 (.branch 2379
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 2)))
 (.branch 2388
 (.branch 2386
 (.branch 2385
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 2387
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 2390
 (.branch 2389
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 2391
 (.leaf (.matching Nonrational.OldTerminalMatches.M016.r1040))
 (.leaf (.quota 2)))))))
 (.branch 2408
 (.branch 2400
 (.branch 2396
 (.leaf (.quota 2))
 (.branch 2398
 (.branch 2397
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1))))
 (.branch 2404
 (.leaf (.quota 2))
 (.branch 2406
 (.branch 2405
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))))
 (.branch 2416
 (.branch 2412
 (.branch 2410
 (.branch 2409
 (.leaf (.quota 3))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 2414
 (.branch 2413
 (.leaf (.quota 3))
 (.leaf (.quota 1)))
 (.leaf (.quota 2))))
 (.branch 2420
 (.branch 2418
 (.branch 2417
 (.leaf (.quota 3))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 2422
 (.branch 2421
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 2423
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))))))
 (.branch 2488
 (.branch 2456
 (.branch 2440
 (.branch 2432
 (.branch 2428
 (.branch 2426
 (.leaf (.quota 2))
 (.branch 2427
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 2)))
 (.branch 2436
 (.branch 2434
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2))))
 (.branch 2448
 (.branch 2444
 (.branch 2442
 (.branch 2441
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))
 (.branch 2446
 (.leaf (.quota 1))
 (.branch 2447
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 2452
 (.leaf (.quota 1))
 (.branch 2454
 (.branch 2453
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 2455
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))))
 (.branch 2472
 (.branch 2464
 (.branch 2460
 (.branch 2458
 (.branch 2457
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 2462
 (.leaf .euler)
 (.branch 2463
 (.leaf (.quota 1))
 (.leaf (.incidence 5)))))
 (.branch 2468
 (.branch 2466
 (.branch 2465
 (.leaf (.incidence 5))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 2470
 (.branch 2469
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M016.r1041)))
 (.branch 2471
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 2480
 (.branch 2476
 (.branch 2474
 (.leaf (.quota 2))
 (.branch 2475
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 2)))
 (.branch 2484
 (.branch 2482
 (.leaf (.quota 2))
 (.branch 2483
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 2486
 (.branch 2485
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M016.r1042)))
 (.branch 2487
 (.leaf (.matching Nonrational.OldTerminalMatches.M016.r1043))
 (.leaf (.quota 2))))))))
 (.branch 2520
 (.branch 2504
 (.branch 2496
 (.branch 2492
 (.leaf (.quota 2))
 (.branch 2494
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 2500
 (.branch 2498
 (.leaf (.quota 2))
 (.branch 2499
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 2502
 (.branch 2501
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.branch 2512
 (.branch 2508
 (.branch 2506
 (.branch 2505
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))
 (.branch 2516
 (.branch 2514
 (.branch 2513
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 2518
 (.branch 2517
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 2519
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))))
 (.branch 2536
 (.branch 2528
 (.branch 2524
 (.leaf (.quota 1))
 (.branch 2526
 (.branch 2525
 (.leaf (.quota 1))
 (.leaf (.matching Nonrational.OldTerminalMatches.M016.r1044)))
 (.branch 2527
 (.leaf (.quota 1))
 (.leaf (.matching Nonrational.OldTerminalMatches.M016.r1045)))))
 (.branch 2532
 (.branch 2530
 (.branch 2529
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 2534
 (.branch 2533
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 2535
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 2544
 (.branch 2540
 (.leaf (.quota 2))
 (.branch 2542
 (.leaf (.quota 2))
 (.branch 2543
 (.leaf (.incidence 0))
 (.leaf (.quota 2)))))
 (.leaf (.quota 2))))))))
 (.branch 2807
 (.branch 2679
 (.branch 2615
 (.branch 2583
 (.branch 2567
 (.branch 2559
 (.branch 2555
 (.branch 2553
 (.leaf (.quota 2))
 (.branch 2554
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 2557
 (.leaf (.quota 2))
 (.branch 2558
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 2563
 (.branch 2561
 (.leaf (.quota 1))
 (.branch 2562
 (.leaf (.quota 2))
 (.leaf (.quota 3))))
 (.branch 2565
 (.branch 2564
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.branch 2566
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 2575
 (.branch 2571
 (.branch 2569
 (.branch 2568
 (.leaf (.quota 3))
 (.leaf (.quota 2)))
 (.leaf (.quota 1)))
 (.branch 2573
 (.branch 2572
 (.leaf (.incidence 0))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.branch 2579
 (.branch 2577
 (.branch 2576
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 2581
 (.branch 2580
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 2582
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))))
 (.branch 2599
 (.branch 2591
 (.branch 2587
 (.leaf (.quota 2))
 (.branch 2589
 (.leaf (.quota 2))
 (.branch 2590
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 2595
 (.branch 2593
 (.branch 2592
 (.leaf (.quota 2))
 (.leaf (.incidence 0)))
 (.branch 2594
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 2597
 (.branch 2596
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.branch 2598
 (.leaf (.quota 2))
 (.leaf (.quota 3))))))
 (.branch 2607
 (.branch 2603
 (.branch 2601
 (.leaf (.quota 3))
 (.branch 2602
 (.leaf (.quota 3))
 (.leaf (.quota 2))))
 (.branch 2605
 (.leaf (.quota 2))
 (.branch 2606
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 2611
 (.branch 2609
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 2613
 (.branch 2612
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))))))
 (.branch 2647
 (.branch 2631
 (.branch 2623
 (.branch 2619
 (.branch 2617
 (.leaf (.quota 2))
 (.branch 2618
 (.leaf (.quota 3))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.branch 2627
 (.branch 2625
 (.branch 2624
 (.leaf (.quota 1))
 (.leaf (.incidence 0)))
 (.leaf (.quota 2)))
 (.branch 2629
 (.branch 2628
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 2630
 (.leaf (.incidence 0))
 (.leaf (.quota 2))))))
 (.branch 2639
 (.branch 2635
 (.branch 2633
 (.branch 2632
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 2634
 (.leaf (.quota 2))
 (.leaf (.incidence 0))))
 (.branch 2637
 (.branch 2636
 (.leaf (.incidence 0))
 (.leaf (.quota 2)))
 (.leaf (.quota 3))))
 (.branch 2643
 (.branch 2641
 (.branch 2640
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))))
 (.branch 2663
 (.branch 2655
 (.leaf (.quota 2))
 (.branch 2659
 (.leaf (.quota 2))
 (.branch 2661
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 2671
 (.branch 2667
 (.leaf (.quota 2))
 (.branch 2669
 (.leaf (.quota 2))
 (.branch 2670
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 2675
 (.branch 2673
 (.branch 2672
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))))))
 (.branch 2743
 (.branch 2711
 (.branch 2695
 (.branch 2687
 (.branch 2683
 (.branch 2681
 (.branch 2680
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 2682
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 2703
 (.branch 2699
 (.branch 2697
 (.branch 2696
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 2698
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 2701
 (.branch 2700
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.branch 2707
 (.branch 2705
 (.leaf (.quota 2))
 (.branch 2706
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))))
 (.branch 2727
 (.branch 2719
 (.branch 2715
 (.leaf (.quota 2))
 (.branch 2717
 (.branch 2716
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.branch 2723
 (.branch 2721
 (.branch 2720
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))
 (.branch 2725
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 2735
 (.branch 2731
 (.branch 2729
 (.branch 2728
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1)))
 (.branch 2733
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 2739
 (.branch 2737
 (.leaf (.quota 1))
 (.branch 2738
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 2741
 (.branch 2740
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 2742
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))))
 (.branch 2775
 (.branch 2759
 (.branch 2751
 (.branch 2747
 (.branch 2745
 (.leaf (.quota 2))
 (.branch 2746
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.branch 2755
 (.branch 2753
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 2757
 (.branch 2756
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 2758
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 2767
 (.branch 2763
 (.branch 2761
 (.branch 2760
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.branch 2791
 (.branch 2783
 (.branch 2779
 (.leaf (.quota 2))
 (.branch 2781
 (.leaf (.quota 3))
 (.leaf (.quota 2))))
 (.branch 2787
 (.branch 2785
 (.leaf (.quota 2))
 (.branch 2786
 (.leaf (.quota 2))
 (.leaf (.quota 3))))
 (.leaf (.quota 2))))
 (.branch 2799
 (.branch 2795
 (.leaf (.quota 2))
 (.branch 2797
 (.branch 2796
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M016.r1046)))
 (.branch 2798
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 2803
 (.branch 2801
 (.leaf (.quota 2))
 (.branch 2802
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 2805
 (.leaf (.quota 1))
 (.branch 2806
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))))))
 (.branch 2935
 (.branch 2871
 (.branch 2839
 (.branch 2823
 (.branch 2815
 (.branch 2811
 (.leaf (.quota 2))
 (.branch 2813
 (.branch 2812
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 2814
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 2819
 (.branch 2817
 (.leaf (.quota 2))
 (.branch 2818
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 2821
 (.branch 2820
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))))
 (.branch 2831
 (.branch 2827
 (.branch 2825
 (.leaf (.quota 2))
 (.branch 2826
 (.leaf (.quota 2))
 (.leaf (.quota 3))))
 (.branch 2829
 (.branch 2828
 (.leaf (.quota 3))
 (.leaf (.quota 2)))
 (.branch 2830
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 2835
 (.leaf (.quota 2))
 (.branch 2837
 (.branch 2836
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.leaf (.quota 2))))))
 (.branch 2855
 (.branch 2847
 (.branch 2843
 (.branch 2841
 (.leaf (.quota 2))
 (.branch 2842
 (.leaf (.matching Nonrational.OldTerminalMatches.M016.r1047))
 (.leaf (.matching Nonrational.OldTerminalMatches.M016.r1048))))
 (.leaf (.quota 2)))
 (.branch 2851
 (.branch 2849
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.branch 2853
 (.leaf (.quota 3))
 (.branch 2854
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 2863
 (.leaf (.quota 2))
 (.branch 2867
 (.branch 2865
 (.leaf (.quota 2))
 (.branch 2866
 (.leaf (.quota 3))
 (.leaf (.quota 2))))
 (.branch 2869
 (.branch 2868
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M016.r1049)))
 (.leaf (.quota 1)))))))
 (.branch 2903
 (.branch 2887
 (.branch 2879
 (.branch 2875
 (.branch 2873
 (.leaf (.quota 2))
 (.branch 2874
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 2877
 (.branch 2876
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 2878
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 2883
 (.branch 2881
 (.leaf (.quota 1))
 (.leaf (.quota 3)))
 (.branch 2885
 (.leaf (.quota 1))
 (.branch 2886
 (.leaf (.quota 2))
 (.leaf (.quota 3))))))
 (.branch 2895
 (.branch 2891
 (.branch 2889
 (.branch 2888
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.leaf (.quota 2)))
 (.branch 2893
 (.branch 2892
 (.leaf (.quota 1))
 (.leaf (.quota 3)))
 (.branch 2894
 (.leaf (.quota 3))
 (.leaf (.quota 1)))))
 (.branch 2899
 (.leaf (.quota 3))
 (.branch 2901
 (.branch 2900
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 2902
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))))
 (.branch 2919
 (.branch 2911
 (.branch 2907
 (.branch 2905
 (.leaf (.quota 2))
 (.branch 2906
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 2909
 (.leaf (.quota 2))
 (.branch 2910
 (.leaf (.incidence 5))
 (.leaf (.quota 1)))))
 (.branch 2915
 (.branch 2913
 (.branch 2912
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 2914
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 2917
 (.leaf (.quota 2))
 (.branch 2918
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 2927
 (.branch 2923
 (.branch 2921
 (.branch 2920
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 2931
 (.branch 2929
 (.branch 2928
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 2930
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 2933
 (.leaf (.quota 2))
 (.branch 2934
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))))))
 (.branch 2999
 (.branch 2967
 (.branch 2951
 (.leaf (.quota 2))
 (.branch 2959
 (.leaf (.quota 2))
 (.branch 2963
 (.leaf (.quota 2))
 (.branch 2965
 (.branch 2964
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))))
 (.branch 2983
 (.branch 2975
 (.branch 2971
 (.leaf (.quota 2))
 (.branch 2973
 (.branch 2972
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2))))
 (.branch 2979
 (.branch 2977
 (.branch 2976
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 2978
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 2981
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 2991
 (.branch 2987
 (.branch 2985
 (.branch 2984
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))
 (.branch 2989
 (.leaf (.quota 3))
 (.branch 2990
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.leaf (.quota 2)))))
 (.branch 3031
 (.branch 3015
 (.branch 3007
 (.branch 3003
 (.branch 3001
 (.leaf (.quota 2))
 (.branch 3002
 (.leaf (.quota 3))
 (.leaf (.quota 2))))
 (.branch 3005
 (.branch 3004
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M016.r1050)))
 (.branch 3006
 (.leaf (.matching Nonrational.OldTerminalMatches.M016.r1051))
 (.leaf (.quota 2)))))
 (.branch 3011
 (.branch 3009
 (.leaf (.quota 2))
 (.branch 3010
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 3013
 (.leaf (.quota 2))
 (.branch 3014
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 3023
 (.leaf (.quota 2))
 (.branch 3027
 (.branch 3025
 (.leaf (.quota 2))
 (.branch 3026
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 3029
 (.branch 3028
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 3030
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))))
 (.branch 3047
 (.branch 3039
 (.branch 3035
 (.branch 3033
 (.branch 3032
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.branch 3034
 (.leaf (.quota 2))
 (.leaf (.quota 3))))
 (.branch 3037
 (.branch 3036
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2))))
 (.branch 3043
 (.leaf (.quota 2))
 (.branch 3045
 (.branch 3044
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))))
 (.branch 3055
 (.branch 3051
 (.branch 3049
 (.leaf (.quota 2))
 (.branch 3050
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 3053
 (.leaf (.quota 2))
 (.branch 3054
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 3059
 (.branch 3057
 (.branch 3056
 (.leaf (.quota 2))
 (.leaf .euler))
 (.branch 3058
 (.leaf .euler)
 (.leaf (.quota 2))))
 (.branch 3061
 (.branch 3060
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M016.r1052)))
 (.branch 3062
 (.leaf (.quota 2))
 (.leaf (.quota 3))))))))))))
 (.branch 3573
 (.branch 3318
 (.branch 3190
 (.branch 3126
 (.branch 3094
 (.branch 3078
 (.branch 3070
 (.branch 3066
 (.branch 3064
 (.leaf (.quota 3))
 (.branch 3065
 (.leaf (.quota 3))
 (.leaf .euler)))
 (.branch 3068
 (.branch 3067
 (.leaf (.quota 3))
 (.leaf (.quota 2)))
 (.branch 3069
 (.leaf (.quota 3))
 (.leaf (.quota 2)))))
 (.branch 3074
 (.branch 3072
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 3076
 (.leaf (.quota 2))
 (.branch 3077
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 3086
 (.branch 3082
 (.branch 3080
 (.branch 3079
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 3081
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 3084
 (.branch 3083
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M016.r1053)))
 (.leaf (.quota 1))))
 (.branch 3090
 (.leaf (.quota 2))
 (.branch 3092
 (.leaf (.quota 2))
 (.branch 3093
 (.leaf (.quota 2))
 (.leaf (.quota 3)))))))
 (.branch 3110
 (.branch 3102
 (.branch 3098
 (.branch 3096
 (.branch 3095
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 3097
 (.leaf (.quota 3))
 (.leaf (.quota 1))))
 (.leaf (.quota 2)))
 (.branch 3106
 (.branch 3104
 (.branch 3103
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))
 (.branch 3108
 (.branch 3107
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.branch 3109
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 3118
 (.branch 3114
 (.branch 3112
 (.leaf (.quota 2))
 (.branch 3113
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 2)))
 (.branch 3122
 (.branch 3120
 (.branch 3119
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 3121
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 2))))))
 (.branch 3158
 (.branch 3142
 (.branch 3134
 (.branch 3130
 (.branch 3128
 (.branch 3127
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 3129
 (.leaf (.quota 2))
 (.leaf (.incidence 5))))
 (.branch 3132
 (.branch 3131
 (.leaf (.incidence 5))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 3138
 (.branch 3136
 (.branch 3135
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.branch 3150
 (.branch 3146
 (.leaf (.quota 2))
 (.branch 3148
 (.branch 3147
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M016.r1054)))
 (.leaf (.quota 2))))
 (.branch 3154
 (.branch 3152
 (.branch 3151
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 3156
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 3174
 (.branch 3166
 (.branch 3162
 (.branch 3160
 (.branch 3159
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 3161
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 3164
 (.branch 3163
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.leaf (.quota 2)))
 (.branch 3182
 (.branch 3178
 (.branch 3176
 (.branch 3175
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 3177
 (.leaf (.quota 2))
 (.leaf .euler)))
 (.branch 3180
 (.branch 3179
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 3181
 (.leaf (.quota 1))
 (.leaf .euler))))
 (.branch 3186
 (.branch 3184
 (.branch 3183
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 3185
 (.leaf (.quota 1))
 (.leaf .euler)))
 (.branch 3188
 (.branch 3187
 (.leaf .euler)
 (.leaf (.quota 2)))
 (.branch 3189
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))))))
 (.branch 3254
 (.branch 3222
 (.branch 3206
 (.branch 3198
 (.branch 3194
 (.branch 3192
 (.leaf (.quota 1))
 (.branch 3193
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 3196
 (.branch 3195
 (.leaf (.quota 2))
 (.leaf (.incidence 5)))
 (.branch 3197
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 3202
 (.branch 3200
 (.branch 3199
 (.leaf (.incidence 4))
 (.leaf (.quota 1)))
 (.leaf .euler))
 (.branch 3204
 (.branch 3203
 (.leaf .euler)
 (.leaf (.quota 1)))
 (.branch 3205
 (.leaf (.incidence 5))
 (.leaf (.quota 2))))))
 (.branch 3214
 (.branch 3210
 (.branch 3208
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 3212
 (.branch 3211
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 3213
 (.leaf (.quota 2))
 (.leaf (.incidence 4)))))
 (.branch 3218
 (.branch 3216
 (.leaf (.quota 1))
 (.branch 3217
 (.leaf (.quota 3))
 (.leaf (.quota 2))))
 (.branch 3220
 (.branch 3219
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))))
 (.branch 3238
 (.branch 3230
 (.branch 3226
 (.branch 3224
 (.leaf (.quota 2))
 (.branch 3225
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.branch 3234
 (.branch 3232
 (.branch 3231
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 3233
 (.leaf (.quota 3))
 (.leaf (.quota 2))))
 (.leaf (.quota 2))))
 (.branch 3246
 (.branch 3242
 (.leaf (.quota 2))
 (.branch 3244
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 3250
 (.branch 3248
 (.leaf (.quota 3))
 (.branch 3249
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 3252
 (.branch 3251
 (.leaf (.quota 1))
 (.leaf (.quota 3)))
 (.branch 3253
 (.leaf (.quota 1))
 (.leaf (.quota 3))))))))
 (.branch 3286
 (.branch 3270
 (.branch 3262
 (.branch 3258
 (.branch 3256
 (.leaf (.quota 3))
 (.branch 3257
 (.leaf (.quota 3))
 (.leaf (.quota 2))))
 (.branch 3260
 (.branch 3259
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2))))
 (.branch 3266
 (.branch 3264
 (.branch 3263
 (.leaf (.quota 2))
 (.leaf .euler))
 (.leaf (.quota 2)))
 (.branch 3268
 (.branch 3267
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 3269
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 3278
 (.branch 3274
 (.branch 3272
 (.branch 3271
 (.leaf (.quota 3))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))
 (.branch 3282
 (.branch 3280
 (.branch 3279
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 3284
 (.leaf (.quota 1))
 (.branch 3285
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))))
 (.branch 3302
 (.branch 3294
 (.branch 3290
 (.branch 3288
 (.branch 3287
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 3292
 (.branch 3291
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 3293
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 3298
 (.branch 3296
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.branch 3310
 (.branch 3306
 (.branch 3304
 (.branch 3303
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 3305
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 3308
 (.branch 3307
 (.leaf (.quota 3))
 (.leaf (.quota 2)))
 (.branch 3309
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 3314
 (.branch 3312
 (.branch 3311
 (.leaf (.quota 3))
 (.leaf (.quota 2)))
 (.branch 3313
 (.leaf (.quota 3))
 (.leaf (.quota 2))))
 (.branch 3316
 (.leaf (.quota 1))
 (.branch 3317
 (.leaf (.quota 2))
 (.leaf (.quota 3))))))))))
 (.branch 3445
 (.branch 3381
 (.branch 3349
 (.branch 3333
 (.branch 3325
 (.branch 3321
 (.branch 3319
 (.leaf .euler)
 (.branch 3320
 (.leaf (.quota 2))
 (.leaf (.quota 3))))
 (.branch 3323
 (.branch 3322
 (.leaf (.quota 3))
 (.leaf (.quota 2)))
 (.leaf (.quota 1))))
 (.branch 3329
 (.leaf (.quota 2))
 (.branch 3331
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 3341
 (.branch 3337
 (.branch 3335
 (.branch 3334
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 3336
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 3339
 (.branch 3338
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2))))
 (.branch 3345
 (.branch 3343
 (.leaf (.quota 2))
 (.branch 3344
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 3347
 (.branch 3346
 (.leaf (.quota 3))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))))
 (.branch 3365
 (.branch 3357
 (.branch 3353
 (.branch 3351
 (.leaf (.quota 2))
 (.branch 3352
 (.leaf (.quota 1))
 (.leaf .euler)))
 (.branch 3355
 (.branch 3354
 (.leaf .euler)
 (.leaf (.quota 2)))
 (.leaf .euler)))
 (.branch 3361
 (.branch 3359
 (.leaf .euler)
 (.branch 3360
 (.leaf (.quota 1))
 (.leaf .euler)))
 (.leaf (.quota 1))))
 (.branch 3373
 (.branch 3369
 (.branch 3367
 (.branch 3366
 (.leaf (.quota 1))
 (.leaf (.matching Nonrational.OldTerminalMatches.M016.r1055)))
 (.leaf (.quota 2)))
 (.branch 3371
 (.branch 3370
 (.leaf (.quota 1))
 (.leaf (.matching Nonrational.OldTerminalMatches.M016.r1056)))
 (.branch 3372
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 3377
 (.branch 3375
 (.leaf (.quota 1))
 (.branch 3376
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 3379
 (.leaf (.quota 1))
 (.branch 3380
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))))
 (.branch 3413
 (.branch 3397
 (.branch 3389
 (.branch 3385
 (.leaf (.quota 1))
 (.branch 3387
 (.branch 3386
 (.leaf .euler)
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.branch 3393
 (.leaf (.quota 1))
 (.branch 3395
 (.branch 3394
 (.leaf (.matching Nonrational.OldTerminalMatches.M016.r1057))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))))
 (.branch 3405
 (.branch 3401
 (.branch 3399
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 3409
 (.branch 3407
 (.branch 3406
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M016.r1058)))
 (.leaf (.quota 1)))
 (.branch 3411
 (.branch 3410
 (.leaf (.matching Nonrational.OldTerminalMatches.M016.r1059))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))))
 (.branch 3429
 (.branch 3421
 (.branch 3417
 (.leaf (.quota 1))
 (.branch 3419
 (.branch 3418
 (.leaf (.quota 1))
 (.leaf (.matching Nonrational.OldTerminalMatches.M016.r1060)))
 (.branch 3420
 (.leaf (.quota 1))
 (.leaf (.matching Nonrational.OldTerminalMatches.M016.r1061)))))
 (.branch 3425
 (.branch 3423
 (.branch 3422
 (.leaf (.matching Nonrational.OldTerminalMatches.M016.r1062))
 (.leaf (.matching Nonrational.OldTerminalMatches.M016.r1063)))
 (.branch 3424
 (.leaf (.quota 1))
 (.leaf (.matching Nonrational.OldTerminalMatches.M016.r1064))))
 (.branch 3427
 (.leaf (.quota 1))
 (.branch 3428
 (.leaf (.matching Nonrational.OldTerminalMatches.M016.r1065))
 (.leaf (.matching Nonrational.OldTerminalMatches.M016.r1066))))))
 (.branch 3437
 (.branch 3433
 (.branch 3431
 (.leaf (.quota 1))
 (.branch 3432
 (.leaf (.matching Nonrational.OldTerminalMatches.M016.r1067))
 (.leaf (.matching Nonrational.OldTerminalMatches.M016.r1068))))
 (.branch 3435
 (.branch 3434
 (.leaf (.matching Nonrational.OldTerminalMatches.M016.r1069))
 (.leaf (.quota 1)))
 (.branch 3436
 (.leaf (.matching Nonrational.OldTerminalMatches.M016.r1070))
 (.leaf (.matching Nonrational.OldTerminalMatches.M016.r1071)))))
 (.branch 3441
 (.branch 3439
 (.branch 3438
 (.leaf (.matching Nonrational.OldTerminalMatches.M016.r1072))
 (.leaf (.matching Nonrational.OldTerminalMatches.M016.r1073)))
 (.branch 3440
 (.leaf (.matching Nonrational.OldTerminalMatches.M016.r1074))
 (.leaf (.matching Nonrational.OldTerminalMatches.M016.r1075))))
 (.branch 3443
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))))
 (.branch 3509
 (.branch 3477
 (.branch 3461
 (.branch 3453
 (.branch 3449
 (.branch 3447
 (.leaf (.quota 2))
 (.branch 3448
 (.leaf (.quota 1))
 (.leaf (.matching Nonrational.OldTerminalMatches.M016.r1076))))
 (.branch 3451
 (.leaf (.quota 1))
 (.branch 3452
 (.leaf (.matching Nonrational.OldTerminalMatches.M016.r1077))
 (.leaf (.matching Nonrational.OldTerminalMatches.M016.r1078)))))
 (.branch 3457
 (.branch 3455
 (.branch 3454
 (.leaf (.matching Nonrational.OldTerminalMatches.M016.r1079))
 (.leaf (.matching Nonrational.OldTerminalMatches.M016.r1080)))
 (.branch 3456
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 3459
 (.branch 3458
 (.leaf (.matching Nonrational.OldTerminalMatches.M016.r1081))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))))
 (.branch 3469
 (.leaf (.quota 2))
 (.branch 3473
 (.leaf (.quota 2))
 (.branch 3475
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 3493
 (.leaf (.quota 2))
 (.branch 3501
 (.branch 3497
 (.branch 3495
 (.branch 3494
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 3499
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 3505
 (.branch 3503
 (.branch 3502
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 3507
 (.branch 3506
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 3508
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))))
 (.branch 3541
 (.branch 3525
 (.branch 3517
 (.branch 3513
 (.branch 3511
 (.branch 3510
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 3515
 (.branch 3514
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1))))
 (.branch 3521
 (.branch 3519
 (.leaf (.quota 1))
 (.branch 3520
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 3523
 (.branch 3522
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))))
 (.branch 3533
 (.branch 3529
 (.leaf (.quota 2))
 (.branch 3531
 (.branch 3530
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.leaf (.quota 2))))
 (.branch 3557
 (.branch 3549
 (.branch 3545
 (.branch 3543
 (.leaf (.quota 2))
 (.branch 3544
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 3565
 (.branch 3561
 (.branch 3559
 (.branch 3558
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 3569
 (.branch 3567
 (.leaf (.quota 2))
 (.branch 3568
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 2)))))))))
 (.branch 3828
 (.branch 3700
 (.branch 3636
 (.branch 3604
 (.branch 3588
 (.branch 3580
 (.leaf (.quota 2))
 (.branch 3584
 (.branch 3582
 (.leaf (.quota 1))
 (.branch 3583
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 3586
 (.leaf (.quota 2))
 (.branch 3587
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 3596
 (.branch 3592
 (.branch 3590
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 3594
 (.branch 3593
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2))))
 (.branch 3600
 (.branch 3598
 (.branch 3597
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))))
 (.branch 3620
 (.branch 3612
 (.leaf (.quota 2))
 (.branch 3616
 (.leaf (.quota 2))
 (.branch 3618
 (.branch 3617
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 3619
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 3628
 (.branch 3624
 (.leaf (.quota 2))
 (.branch 3626
 (.leaf (.quota 2))
 (.branch 3627
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 3632
 (.branch 3630
 (.leaf (.quota 2))
 (.branch 3631
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 2))))))
 (.branch 3668
 (.branch 3652
 (.branch 3644
 (.branch 3640
 (.branch 3638
 (.leaf (.quota 2))
 (.branch 3639
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 3642
 (.branch 3641
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 3648
 (.branch 3646
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 3650
 (.leaf (.quota 2))
 (.branch 3651
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 3660
 (.branch 3656
 (.branch 3654
 (.branch 3653
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 3658
 (.branch 3657
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 3659
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 3664
 (.branch 3662
 (.branch 3661
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))
 (.branch 3666
 (.leaf (.quota 1))
 (.branch 3667
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))))
 (.branch 3684
 (.branch 3676
 (.branch 3672
 (.branch 3670
 (.branch 3669
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))
 (.branch 3674
 (.branch 3673
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.branch 3680
 (.leaf (.quota 2))
 (.branch 3682
 (.branch 3681
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))))
 (.branch 3692
 (.branch 3688
 (.leaf (.quota 2))
 (.branch 3690
 (.branch 3689
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2))))
 (.branch 3696
 (.leaf (.quota 2))
 (.branch 3698
 (.branch 3697
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2))))))))
 (.branch 3764
 (.branch 3732
 (.branch 3716
 (.branch 3708
 (.branch 3704
 (.branch 3702
 (.branch 3701
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 3703
 (.leaf (.quota 2))
 (.leaf (.incidence 0))))
 (.branch 3706
 (.leaf (.quota 1))
 (.branch 3707
 (.leaf (.incidence 0))
 (.leaf (.quota 1)))))
 (.branch 3712
 (.branch 3710
 (.branch 3709
 (.leaf (.quota 1))
 (.leaf (.incidence 0)))
 (.leaf (.quota 1)))
 (.leaf (.quota 2))))
 (.branch 3724
 (.leaf (.quota 2))
 (.branch 3728
 (.leaf (.quota 2))
 (.branch 3730
 (.branch 3729
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2))))))
 (.branch 3748
 (.branch 3740
 (.branch 3736
 (.branch 3734
 (.branch 3733
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 3744
 (.leaf (.quota 2))
 (.branch 3746
 (.leaf (.quota 2))
 (.branch 3747
 (.leaf (.quota 2))
 (.leaf .euler)))))
 (.branch 3756
 (.branch 3752
 (.branch 3750
 (.branch 3749
 (.leaf .euler)
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 3760
 (.leaf (.quota 2))
 (.branch 3762
 (.branch 3761
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))))))
 (.branch 3796
 (.branch 3780
 (.branch 3772
 (.branch 3768
 (.leaf (.quota 2))
 (.branch 3770
 (.branch 3769
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.branch 3776
 (.branch 3774
 (.branch 3773
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.branch 3788
 (.branch 3784
 (.branch 3782
 (.leaf (.quota 2))
 (.branch 3783
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 3786
 (.branch 3785
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.branch 3792
 (.branch 3790
 (.branch 3789
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 3791
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 3794
 (.leaf (.quota 2))
 (.branch 3795
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))))
 (.branch 3812
 (.branch 3804
 (.branch 3800
 (.leaf (.quota 2))
 (.branch 3802
 (.leaf (.quota 1))
 (.branch 3803
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 3808
 (.leaf (.quota 2))
 (.branch 3810
 (.branch 3809
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))))
 (.branch 3820
 (.branch 3816
 (.branch 3814
 (.branch 3813
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 3818
 (.leaf (.quota 2))
 (.branch 3819
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 3824
 (.branch 3822
 (.branch 3821
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))
 (.branch 3826
 (.branch 3825
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))))))))
 (.branch 3956
 (.branch 3892
 (.branch 3860
 (.branch 3844
 (.branch 3836
 (.branch 3832
 (.branch 3830
 (.leaf (.quota 2))
 (.branch 3831
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 3834
 (.leaf (.quota 2))
 (.branch 3835
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.leaf (.quota 2)))
 (.branch 3852
 (.branch 3848
 (.leaf (.quota 2))
 (.branch 3850
 (.leaf (.quota 2))
 (.branch 3851
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 3856
 (.branch 3854
 (.leaf (.quota 2))
 (.branch 3855
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 3858
 (.leaf (.quota 2))
 (.branch 3859
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))))
 (.branch 3876
 (.branch 3868
 (.branch 3864
 (.branch 3862
 (.branch 3861
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 3863
 (.leaf (.quota 1))
 (.leaf (.matching Nonrational.OldTerminalMatches.M016.r1082))))
 (.branch 3866
 (.branch 3865
 (.leaf (.matching Nonrational.OldTerminalMatches.M016.r1083))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.branch 3872
 (.branch 3870
 (.branch 3869
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M016.r1084)))
 (.leaf (.quota 2)))
 (.branch 3874
 (.branch 3873
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))))
 (.branch 3884
 (.branch 3880
 (.branch 3878
 (.leaf (.quota 2))
 (.branch 3879
 (.leaf (.matching Nonrational.OldTerminalMatches.M016.r1085))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))))
 (.branch 3924
 (.branch 3908
 (.branch 3900
 (.branch 3896
 (.branch 3894
 (.branch 3893
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 3895
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 3898
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 3904
 (.branch 3902
 (.leaf (.quota 1))
 (.branch 3903
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 3906
 (.branch 3905
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 3907
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 3916
 (.branch 3912
 (.leaf (.quota 2))
 (.branch 3914
 (.branch 3913
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M016.r1086)))
 (.leaf (.quota 2))))
 (.branch 3920
 (.branch 3918
 (.branch 3917
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))
 (.branch 3922
 (.leaf (.quota 2))
 (.branch 3923
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))))
 (.branch 3940
 (.branch 3932
 (.branch 3928
 (.branch 3926
 (.leaf (.quota 1))
 (.branch 3927
 (.leaf (.matching Nonrational.OldTerminalMatches.M016.r1087))
 (.leaf (.matching Nonrational.OldTerminalMatches.M017.r1088))))
 (.branch 3930
 (.leaf (.quota 2))
 (.branch 3931
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 3936
 (.branch 3934
 (.leaf (.quota 2))
 (.branch 3935
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 3938
 (.leaf (.quota 1))
 (.branch 3939
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 3948
 (.branch 3944
 (.branch 3942
 (.branch 3941
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1)))
 (.branch 3946
 (.leaf (.quota 2))
 (.branch 3947
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 3952
 (.branch 3950
 (.branch 3949
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 3951
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))))))
 (.branch 4020
 (.branch 3988
 (.branch 3972
 (.branch 3964
 (.branch 3960
 (.leaf (.quota 2))
 (.branch 3962
 (.branch 3961
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 3963
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 3968
 (.branch 3966
 (.branch 3965
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 3970
 (.leaf (.quota 2))
 (.branch 3971
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 3980
 (.branch 3976
 (.branch 3974
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 3978
 (.leaf (.quota 2))
 (.branch 3979
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 3984
 (.branch 3982
 (.branch 3981
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 3983
 (.leaf (.quota 1))
 (.leaf (.matching Nonrational.OldTerminalMatches.M017.r1089))))
 (.branch 3986
 (.branch 3985
 (.leaf (.matching Nonrational.OldTerminalMatches.M017.r1090))
 (.leaf (.matching Nonrational.OldTerminalMatches.M017.r1091)))
 (.branch 3987
 (.leaf (.matching Nonrational.OldTerminalMatches.M017.r1092))
 (.leaf (.quota 1)))))))
 (.branch 4004
 (.branch 3996
 (.branch 3992
 (.branch 3990
 (.branch 3989
 (.leaf (.quota 1))
 (.leaf (.matching Nonrational.OldTerminalMatches.M017.r1093)))
 (.branch 3991
 (.leaf (.matching Nonrational.OldTerminalMatches.M017.r1094))
 (.leaf (.matching Nonrational.OldTerminalMatches.M017.r1095))))
 (.branch 3994
 (.branch 3993
 (.leaf (.matching Nonrational.OldTerminalMatches.M017.r1096))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 4000
 (.leaf (.quota 2))
 (.branch 4002
 (.branch 4001
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))))
 (.branch 4012
 (.branch 4008
 (.branch 4006
 (.leaf (.quota 2))
 (.branch 4007
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 4010
 (.branch 4009
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 4011
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 4016
 (.branch 4014
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 4018
 (.branch 4017
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))))))
 (.branch 4052
 (.branch 4036
 (.branch 4028
 (.branch 4024
 (.branch 4022
 (.branch 4021
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 4032
 (.leaf (.quota 2))
 (.branch 4034
 (.leaf (.quota 1))
 (.branch 4035
 (.leaf (.quota 1))
 (.leaf (.matching Nonrational.OldTerminalMatches.M017.r1097))))))
 (.branch 4044
 (.branch 4040
 (.branch 4038
 (.leaf (.quota 1))
 (.branch 4039
 (.leaf (.matching Nonrational.OldTerminalMatches.M017.r1098))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.branch 4048
 (.branch 4046
 (.branch 4045
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 4047
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))))
 (.branch 4068
 (.branch 4060
 (.branch 4056
 (.branch 4054
 (.branch 4053
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 4058
 (.leaf (.quota 2))
 (.branch 4059
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M017.r1099)))))
 (.branch 4064
 (.leaf (.quota 2))
 (.branch 4066
 (.branch 4065
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 4067
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 4076
 (.branch 4072
 (.branch 4070
 (.branch 4069
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M017.r1100)))
 (.branch 4071
 (.leaf (.quota 1))
 (.leaf (.matching Nonrational.OldTerminalMatches.M017.r1101))))
 (.leaf (.quota 2)))
 (.branch 4080
 (.branch 4078
 (.leaf (.quota 2))
 (.branch 4079
 (.leaf (.quota 1))
 (.leaf (.matching Nonrational.OldTerminalMatches.M017.r1102))))
 (.branch 4082
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))))))))))
def disposition (j : Fin leafCount) := dispositionTable.get j.val
def dispositionTest (i : Nat) : Bool := RawLeafCertificate.check quota
  ((rawLeaves i).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) (dispositionTable.get i)

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355

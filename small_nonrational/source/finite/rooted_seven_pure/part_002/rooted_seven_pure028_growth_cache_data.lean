module
prelude
public import RootedSevenPure028
public import SignatureCompatibility
public import PackedRawNatGrowth
public import FiniteChecks
public import RawFacetEmbedding
public import RootedSevenPure028GrowthCachecandidateMasksData000
public import RootedSevenPure028GrowthCachebadMasksData000
public import RootedSevenPure028GrowthCachesignatureMasksData000

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure028
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def rawCells := Papers.RationalityTen.FacetUniverses.RootedSevenPure028.rawCells
def cells (c : Fin 406) := rawCells c.val
def ridgeList := ConcreteGrowth.ridgeList cells
def literalCompatible (a b : Fin 406) := ConcreteGrowth.compatible (cells a) (cells b)
def kind (c : Fin 406) := (cells c).kind
def rawKindCode : Nat := 1934451890825525049150978233838538086977273788348546147093311168793656235678577529795951031152097889435534180275942640164890390605583980187704968008084548970976949623315067989688570181031324554131459374082704775587615183146696381547310234949955536263648571727201590808533854580356954813281813176144522260144694215070692168438985637239729490900017601686719343555585168
def rawKind (i : Nat) := PackedRawNatGrowth.take 3
  (PackedRawNatGrowth.drop (3*i) rawKindCode)
def candidateRowTable : Table Nat :=
(.branch 512
 (.branch 256
 (.branch 128
 (.branch 64
 (.branch 32
 (.branch 16
 (.branch 8
 (.branch 4
 (.leaf 0x0)
 (.branch 6
 (.leaf 0x0)
 (.branch 7
 (.leaf 0x0)
 (.leaf 0x241188842200f8783a1c0d86832180b8582a14098482210078381a0c058281208038180a040180802000025))))
 (.leaf 0x0))
 (.branch 24
 (.leaf 0x0)
 (.branch 28
 (.branch 26
 (.leaf 0x0)
 (.branch 27
 (.leaf 0x0)
 (.leaf 0x138984a000004)))
 (.leaf 0x0))))
 (.branch 48
 (.branch 40
 (.leaf 0x0)
 (.branch 44
 (.leaf 0x0)
 (.branch 46
 (.leaf 0x0)
 (.branch 47
 (.leaf 0x361acd4000004)
 (.leaf 0x0)))))
 (.branch 56
 (.branch 52
 (.leaf 0x0)
 (.branch 54
 (.branch 53
 (.leaf 0x0)
 (.leaf 0x1f8f87a000004))
 (.leaf 0x0)))
 (.leaf 0x0))))
 (.branch 96
 (.branch 80
 (.leaf 0x0)
 (.branch 88
 (.leaf 0x0)
 (.branch 92
 (.branch 90
 (.branch 89
 (.leaf 0xcf6733598cb6532590c76331588c36130580bf5f2f578bb5d2e570b75b2d568b3592c560af572b558000025)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 112
 (.branch 104
 (.leaf 0x0)
 (.branch 108
 (.branch 106
 (.branch 105
 (.leaf 0x10883c1a0b0481c0a03007fbf9fafc7dbe9f2f87bbd9eaf479bc9e2f077bb9daec75ba9d2e873b99ca000025)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 120
 (.branch 116
 (.branch 114
 (.branch 113
 (.leaf 0x156aad52a752a8d429f4ea6d32974aa4d228f46a2d128742a0d027f3e9ecf2773a9cce26f369acd266000025)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))))
 (.branch 192
 (.branch 160
 (.branch 144
 (.branch 136
 (.branch 132
 (.branch 130
 (.leaf 0x0)
 (.branch 131
 (.leaf 0x0)
 (.leaf 0xe06e351a0c8622f170b4582a148942c14088401c0a0401408020017)))
 (.branch 134
 (.branch 133
 (.leaf 0x0)
 (.leaf 0x1409e4d261289247231148842208f430130903c1c0c0381806020017))
 (.branch 135
 (.leaf 0x1f4f87a3c9dcec74399c8e26f371a82e15090401a0b0481808010017)
 (.leaf 0x0))))
 (.branch 140
 (.branch 138
 (.leaf 0x0)
 (.branch 139
 (.leaf 0x1249147a39188b44a210e864220cd425000e)
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 152
 (.branch 148
 (.branch 146
 (.branch 145
 (.leaf 0x0)
 (.leaf 0xca6431184be5e2e16cb4592b9587a25000e))
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 156
 (.branch 154
 (.branch 153
 (.leaf 0x381bedd6e369b2d76b355a8d268b057ebc5dae56ab3582bd5a250017)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 176
 (.branch 168
 (.branch 164
 (.leaf 0x0)
 (.branch 166
 (.branch 165
 (.leaf 0x14ea65228d42a04f275389b4ca60d43d000e)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 172
 (.branch 170
 (.branch 169
 (.leaf 0x46631168ac4e251087c3a1b0b853e9f0f57a3c9dcec74ba1cc6a0017)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 184
 (.branch 180
 (.branch 178
 (.branch 177
 (.leaf 0x59ecd64b1d86c15eaed72b759ac5228d43a1502793a9bcda683d0017)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 224
 (.branch 208
 (.branch 200
 (.leaf 0x0)
 (.branch 204
 (.branch 202
 (.branch 201
 (.leaf 0x974b6572a9449e4b2491c8a411f7e3ddecf3793c1d6ea73b9986be5eae972b7592c55cad0020)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 216
 (.branch 212
 (.branch 210
 (.branch 209
 (.leaf 0xbe5eef378bb5d6e772b8dc2dd6da55168941a04fa73389acd184c05eaed70b65a2c55eac0020)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 240
 (.branch 232
 (.branch 228
 (.branch 226
 (.branch 225
 (.leaf 0xc8e431d8dc5e2b1187c36170782a4d1e89429fcf677389b4cdf6f97b3d1e2ef76ba9d0e50020)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))))
 (.branch 384
 (.branch 320
 (.branch 288
 (.branch 272
 (.branch 264
 (.branch 260
 (.branch 258
 (.leaf 0x0)
 (.branch 259
 (.leaf 0x0)
 (.leaf 0xe872361a8cc6430170b4562a1409844200e87034090381806010017)))
 (.branch 262
 (.branch 261
 (.leaf 0x0)
 (.leaf 0x148a24e2692c9448231148642200f8481f0f06c340b0401408010017))
 (.branch 263
 (.leaf 0x1fcfc7b3d1e0ee75399c8e06f369ac46210f070320c0501406020017)
 (.leaf 0x0))))
 (.branch 268
 (.branch 266
 (.leaf 0x0)
 (.branch 267
 (.leaf 0x128934823d1a8c452210e8542208d626000e)
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 280
 (.branch 276
 (.branch 274
 (.branch 273
 (.leaf 0x0)
 (.leaf 0xce6631988c05f2e96cb4582b9547c26000e))
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 284
 (.branch 282
 (.branch 281
 (.leaf 0x389c2de6eb6db4d86b355a6d26833596c863b1568b258ab958260017)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 304
 (.branch 296
 (.branch 292
 (.leaf 0x0)
 (.branch 294
 (.branch 293
 (.leaf 0x152a852a9144a14fa75389a4ca5cd63e000e)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 300
 (.branch 298
 (.branch 297
 (.leaf 0x46e35178b452271187c3a190b84c1a0901803f9daeb7539dca6b0017)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 312
 (.branch 308
 (.branch 306
 (.branch 305
 (.leaf 0x5a6d165b258ac35faed72b559abd52a54fa753277399c4d6663e0017)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 352
 (.branch 336
 (.branch 328
 (.leaf 0x0)
 (.branch 332
 (.branch 330
 (.branch 329
 (.leaf 0x984be592b94ca24d2491c86411e8440e04ff7f3bdd8e9743959eca64b198ab659ac15eac0020)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 344
 (.branch 340
 (.branch 338
 (.branch 337
 (.leaf 0xbf5f6f579bbddae972b8dbedd6cab546a14da64f675379b4cd9ccc64b1d88b75aac15cad0020)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 368
 (.branch 360
 (.branch 356
 (.branch 354
 (.branch 353
 (.leaf 0xc9e4b1f8ec662f1387c36130781aad4ea14ea5cfa79379acd20f0581401faf0773a5cee60020)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 448
 (.branch 416
 (.branch 400
 (.branch 392
 (.branch 388
 (.branch 386
 (.branch 385
 (.leaf 0x0)
 (.leaf 0x6732980bc5d2e164b0572914096492411c8843210e87033188c05e2c158a810070301408030021))
 (.branch 387
 (.leaf 0x9449235168a44a190a843f9f4f0763a9d0e270378e46e361a0c05e2d148a014090301404010021)
 (.leaf 0x1e0ec180b0004)))
 (.branch 390
 (.branch 389
 (.leaf 0xa953a89409f4f26d34993f1f0f6793a9d0e46e369449e4e261208e4520900180b0200c04010021)
 (.leaf 0x2a14c14090004))
 (.branch 391
 (.leaf 0x40a0010070004)
 (.leaf 0x0))))
 (.branch 396
 (.branch 394
 (.branch 393
 (.leaf 0x984ba53279349645219046e331489446210d8642dd8eb753a5d0e771381b6d96c35da8d3692cd64b1582bd5c9348a411c8a44a1d06820030)
 (.leaf 0x0))
 (.branch 395
 (.leaf 0x12c950002)
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 408
 (.branch 404
 (.branch 402
 (.branch 401
 (.leaf 0xbf5f2ef75ba5cee16fb75a6cf62b057ebd5bad56675399c4de6d3570b7dbcdc6c35daad1682d568b1582b558663218cc25d2e168ac550030)
 (.leaf 0xd2680002))
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 412
 (.branch 410
 (.branch 409
 (.leaf 0x7238d6eb60004)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 432
 (.branch 424
 (.branch 420
 (.branch 418
 (.branch 417
 (.leaf 0xc9e47198ac4e230b84c1da2cd65b1d7ebd5cac55e793b9c4de69338d4622f1588c421d0a84bb9daea74b99caa853295469f4f27130970030)
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 422
 (.branch 421
 (.leaf 0x156aa0002)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 428
 (.branch 426
 (.branch 425
 (.leaf 0x8ec71e0ef0004)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 440
 (.branch 436
 (.branch 434
 (.branch 433
 (.leaf 0xb5daa7d3d0004)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 480
 (.branch 464
 (.branch 456
 (.branch 452
 (.branch 450
 (.branch 449
 (.leaf 0x192c863f1b89c461b0581bedeef578ba5cee36db64fa7b369acd2672f96cb2552692c8e3f1e783bdd0e7733956eb657ab95aac002d)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 460
 (.branch 458
 (.branch 457
 (.leaf 0x26531773b56ab40006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 472
 (.branch 468
 (.branch 466
 (.branch 465
 (.leaf 0x3017f9e4ed66b20006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 496
 (.branch 488
 (.branch 484
 (.branch 482
 (.branch 481
 (.leaf 0x32b949d4e5d8eb0006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))))
 (.branch 768
 (.branch 640
 (.branch 576
 (.branch 544
 (.branch 528
 (.branch 520
 (.branch 516
 (.branch 514
 (.leaf 0x0)
 (.branch 515
 (.leaf 0x0)
 (.leaf 0xf076361a0cc6230178b056291409c421f0f06c3215098481e0d0017)))
 (.branch 518
 (.branch 517
 (.leaf 0x0)
 (.leaf 0x150a64e2612c9248239108641200fc46200e87032170a044200d0017))
 (.branch 519
 (.leaf 0x205007b3c9e0ec753a1c4e06e369b048220e86c34180b0441e0e0017)
 (.leaf 0x0))))
 (.branch 524
 (.branch 522
 (.leaf 0x0)
 (.branch 523
 (.leaf 0x12c95482391a8b452250c8541a08d827000e)
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 536
 (.branch 532
 (.branch 530
 (.branch 529
 (.leaf 0x0)
 (.leaf 0xd26831984c05e2e970b2582b1547e27000e))
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 540
 (.branch 538
 (.branch 537
 (.leaf 0x391c6de6e36db2d86bb51a6d16833194c96331180be5eae970270017)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 560
 (.branch 552
 (.branch 548
 (.leaf 0x0)
 (.branch 550
 (.branch 549
 (.leaf 0x156aa52a8d44a04fa79369a4c25cd83f000e)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 556
 (.branch 554
 (.branch 553
 (.leaf 0x47639178ac52251188436190a84c1607027fbf5f2f77b3cde26c0017)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 568
 (.branch 564
 (.branch 562
 (.branch 561
 (.leaf 0x5aed565b1d8ac15faf56eb558abd4ea350a6d2e8f45a25067e3f0017)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 608
 (.branch 592
 (.branch 584
 (.leaf 0x0)
 (.branch 588
 (.branch 586
 (.branch 585
 (.leaf 0x994c6592a94c9e4d25914863f1e83c1203007ebedf0f57a3c59ccb6431d88c25faf176b80020)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 600
 (.branch 596
 (.branch 594
 (.branch 593
 (.leaf 0xc05fef578bbdd6e973b85bedb6caad4a9f4ea5d268d43a14fd9ecd643198ac360af174b90020)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 624
 (.branch 616
 (.branch 612
 (.branch 610
 (.branch 609
 (.leaf 0xcae531f8dc662b1388c2e130581ab5529f4da652a9143a0d02110680bfdfcfc7d3d5e6f20020)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 704
 (.branch 672
 (.branch 656
 (.branch 648
 (.branch 644
 (.branch 642
 (.branch 641
 (.leaf 0x0)
 (.leaf 0x6932180be5d2d968b0562a13c964a241188a43208f06e33190c05c2d158a4281309044200f0021))
 (.branch 643
 (.leaf 0x9648a35188a4421d0a83409f0f0773a9cce470370ec70361a8c05c2c150a02c15090441c0d0021)
 (.leaf 0x1d0e430170004)))
 (.branch 646
 (.branch 645
 (.leaf 0xab53289429f4ea713498401f4f67a3a9cce26f3694ca04e269208c442110030170803c1c0d0021)
 (.leaf 0x291442c150004))
 (.branch 647
 (.leaf 0x3f9f828130004)
 (.leaf 0x0))))
 (.branch 652
 (.branch 650
 (.branch 649
 (.leaf 0x994b653289349247218fc76311489c461f0e86429f0f77b3d5e8f37237db6da6c359aad368afd7cbd5e2ed7495492411e8a4421908820030)
 (.leaf 0x0))
 (.branch 651
 (.leaf 0x128930002)
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 664
 (.branch 660
 (.branch 658
 (.branch 657
 (.leaf 0xc05eeef76ba5cae36fb6daecd62b0d7ebb5cad5628d45a250e854171b81bcdd6c359a8d26830580bd5e2e570683298cc45d2d964ae550030)
 (.leaf 0xce660002))
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 668
 (.branch 666
 (.branch 665
 (.leaf 0x7138586c20004)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 688
 (.branch 680
 (.branch 676
 (.branch 674
 (.branch 673
 (.leaf 0xcae43198bc4e1f0d84c15aacf65b257ebb5bacd5e9147a250e813f8e4662f1688c3e1b0b84be9f2f67abc9e2aa53a95489f4ea6d32970030)
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 678
 (.branch 677
 (.leaf 0x152a80002)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 684
 (.branch 682
 (.branch 681
 (.leaf 0x8dc69f8fb0004)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 696
 (.branch 692
 (.branch 690
 (.branch 689
 (.leaf 0xb4da295490004)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 736
 (.branch 720
 (.branch 712
 (.branch 708
 (.branch 706
 (.branch 705
 (.leaf 0x194c8e3f1d89c3e170781bfdf2f579ba5cae16eb652a9342a0d027f31974b257269248a411e7e3ede8f3793c586c25dae972b8002d)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 716
 (.branch 714
 (.branch 713
 (.leaf 0x2612f7d3e582c00006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 728
 (.branch 724
 (.branch 722
 (.branch 721
 (.leaf 0x2fd7da451d7ebe0006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 752
 (.branch 744
 (.branch 740
 (.branch 738
 (.branch 737
 (.leaf 0x32792a3515f0f70006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))))
 (.branch 896
 (.branch 832
 (.branch 800
 (.branch 784
 (.branch 776
 (.branch 772
 (.branch 770
 (.branch 769
 (.leaf 0x0)
 (.leaf 0x683317cbc5c2d968b255299449449239188a44200ec7232188bc5c2d160a0401f0f074381b0021))
 (.branch 771
 (.leaf 0x9549a3116894421d0c82401f8ee763a1cce471368f074351a0bc5c2b150a444210f07434190021)
 (.leaf 0x1c0dc48230004)))
 (.branch 774
 (.branch 773
 (.leaf 0xaa54285409e4ea713697409fcf4793a1cce06f37150a44d2611c8c432110448230e06c34190021)
 (.leaf 0x2813c44210004))
 (.branch 775
 (.leaf 0x3e9f0401f0004)
 (.leaf 0x0))))
 (.branch 780
 (.branch 778
 (.branch 777
 (.leaf 0x98cbe512792c9247228f4723513894421f0e86c2609038140600ff71b85b4d96bb59aad46832d94c96431d8c964a23d1c894421508830030)
 (.leaf 0x0))
 (.branch 779
 (.leaf 0x124910002)
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 792
 (.branch 788
 (.branch 786
 (.branch 785
 (.leaf 0xbfdf6ed75b9dcae370b65aad161b057abb5cadd5ea551a853e9d4d72389badc6bb59a6d268b3598c964315886933988c25c2d960ae560030)
 (.leaf 0xca640002))
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 796
 (.branch 794
 (.branch 793
 (.leaf 0x7037d9ece0004)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 816
 (.branch 808
 (.branch 804
 (.branch 802
 (.branch 801
 (.leaf 0xca64b178ac461f0d85c0daed364b1d7abb5aacd62a953a853e994b8ec6e2d158843e190b8541a0b0280bf9faab54a91469e4ea6932980030)
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 806
 (.branch 805
 (.leaf 0x14ea60002)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 812
 (.branch 810
 (.branch 809
 (.leaf 0x8cc6211070004)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 824
 (.branch 820
 (.branch 818
 (.branch 817
 (.leaf 0xb3d9aad550004)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 864
 (.branch 848
 (.branch 840
 (.branch 836
 (.branch 834
 (.branch 833
 (.leaf 0x195c9e3b1b88c3e130782c05faf378b9dcadf6eb6d5aab4ea6d329732984ae552592486411f8441e00ff7f3f59ece63b198ac4002d)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 844
 (.branch 842
 (.branch 841
 (.leaf 0x25d2d834159acc0006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 856
 (.branch 852
 (.branch 850
 (.branch 849
 (.leaf 0x2f97baa54d96ca0006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 880
 (.branch 872
 (.branch 868
 (.branch 866
 (.branch 865
 (.leaf 0x32390a954609030006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 960
 (.branch 928
 (.branch 912
 (.branch 904
 (.branch 900
 (.branch 898
 (.branch 897
 (.leaf 0xcae532792c8e430d85c260f0581c05fefd7dbe5eee370b7dbadb6cb5daad368b3d9ab95bad566b157994c6612f974b6472290c823f1e8ec72371a8cc621d0d8642e15097238dc4e17037daad469b49a2d055aa952a853a99389b4d26530974b2552893492450e8642a11068240a00fe7e3e9f0e471381bcdc6d349a0ce6632990b4592c15cac552a14ca4512813c8a442190882401e0ec74391c0dc5a2c158a852280090)
 (.leaf 0x63311849c4d260d86a340009))
 (.branch 899
 (.leaf 0x9047a38f67a3c8cc64310009)
 (.leaf 0x0)))
 (.branch 902
 (.branch 901
 (.leaf 0xa55228cf0773b12c94490009)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 908
 (.branch 906
 (.branch 905
 (.leaf 0x964ae55178b455bcdd6e235188b000c)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 920
 (.branch 916
 (.branch 914
 (.branch 913
 (.leaf 0xbd5e6f165b258db6da6c980be5e000c)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 944
 (.branch 936
 (.branch 932
 (.branch 930
 (.branch 929
 (.leaf 0xc7e3b1b62b0d8229138928942a0000c)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 992
 (.branch 976
 (.branch 968
 (.branch 964
 (.branch 962
 (.branch 961
 (.leaf 0x18cc5e2aef76baca651270009)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))))
def kindRowTable : Table Nat :=
(.branch 2
 (.branch 1
 (.leaf 0x1)
 (.leaf 0x0))
 (.branch 3
 (.leaf 0xc4e230f86c2e130782c0dd2e772b8dc2df6eb6db2bf5eaed72b75aacd62af50a7d3a9b4ca5d128742a0d027f389bcda6b3499c9a4b2491c8a43208fc7a231087c3a1b0c85c2a130280c01fefe7ebd9eaf479bc9e2ea74ba1cee672b61aed66ab51a6d268b4192c863b198ac45eaf176ba5cae162b057ab95aac4fa793a9c4da6932984ba29128843a190a8441a08ea74399c8e270379b8da5d2e16cb4592c15cac552411c8c452210c8441200c05e2e168b0562a148a03c1d0e06c341909044200f070340c050200c040100b4)
 (.branch 4
 (.leaf 0x195ca64f2591c863f1d8dc662f1580bfdfafb7cbddeaf378bbddaeb6bb55a6d167b3596c963b1586c156aad52a752a8d2a9348a3d1a8b3e9ecf2773a9ccca633097cba5b2c95caa532893c76391b8d46631178b4562913894220f0682c1206fc7dbe9f2f87bbc1deee76bb1d6e471b89c2e06fb79badc6db69b2cf6733598cb6530d84c1602fd7cb75b2d568b3592ad54a95429d4ca55228d44a1502592a9449a49229047a391a8c45a05007f3f1f4f87b3d1e4f0773b1b0d66a349a0ce6632990c66230980be5e2a14ca4512813c9c4d2612c94491f8f87a3c1d8e872381b8d86a34198c8622713094482311084401f0c05c2c150a04c180b05024100700e1)
 (.leaf 0x0))))
def decodeRow (table : Table Nat) (i : Nat) : List Nat :=
  let code := table.get i
  (PackedRawNatGrowth.readList 9 (PackedRawNatGrowth.take 16 code)
    (PackedRawNatGrowth.drop 16 code)).1
def candidateRows := decodeRow candidateRowTable
def kindRows := decodeRow kindRowTable
def kindMaskTable : Table Nat :=
(.branch 2
 (.branch 1
 (.leaf 0x1)
 (.leaf 0x0))
 (.branch 3
 (.leaf 0x3fe001ff000ff81f81f81f8007fc003fe07e07e07e001ff03f03f03f000ff8007fc003fe0003fe001ff0001ff007e07e07e)
 (.branch 4
 (.leaf 0x3ffc01ffe00fff007e07e07e07ff803ffc01f81f81f81ffe00fc0fc0fc0fff007ff803ffc01fffc01ffe00fffe00ff81f81f80)
 (.leaf 0x0))))
def kindMasks := kindMaskTable.get
def keys := List.range 5
def vertexMaskTable : Table Nat :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf 81129638414606681695789005144063)
 (.leaf 2854495385411838632478157334523137492974043135))
 (.branch 3
 (.leaf 5986307852013354070429085112358827088079626814095359)
 (.branch 4
 (.leaf 260740604970814219042361048116400404614581968081387826727356035210117620806631019722580164609)
 (.leaf 78804012392788958424557819459682256795940436180745495228840792687980088079431589625526240295407861240329162320773121))))
 (.branch 7
 (.branch 6
 (.leaf 165263913393587333630344783781498050878782184857434073439062264323216110600866975892898176953140169657881787743689173368833)
 (.leaf 165263992197524573074572403613968961827681329776282876229681442537505292741683366544790128111072032926736644940519830454273))
 (.branch 8
 (.leaf 165263992197562149720065243572219892296490318229901307487691797463482384097304296276303377768640801189363769518611157221374)
 (.branch 9
 (.leaf 165263992197562149737974453574736711893707466919656445202672582021395608193913829244339295875092516299610951222648343896062)
 (.leaf 165263992197562149737978825940459982601616943762598279953091278502000567477140540556099070431400944026459697344016998719488)))))
def vertexMasks := vertexMaskTable.get
def signatureIndexTable : Table (Table Nat) :=
(.branch 512
 (.branch 256
 (.branch 128
 (.branch 64
 (.branch 32
 (.branch 16
 (.branch 8
 (.branch 4
 (.leaf (.leaf 0))
 (.branch 6
 (.branch 5
 (.leaf (.leaf 0))
 (.leaf (.leaf 1)))
 (.branch 7
 (.leaf (.leaf 2))
 (.leaf (.leaf 3)))))
 (.branch 12
 (.branch 10
 (.leaf (.leaf 0))
 (.branch 11
 (.leaf (.leaf 4))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0))))
 (.branch 24
 (.branch 20
 (.branch 18
 (.branch 17
 (.leaf (.leaf 0))
 (.leaf (.leaf 5)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 28
 (.branch 26
 (.branch 25
 (.leaf (.leaf 6))
 (.leaf (.leaf 0)))
 (.branch 27
 (.leaf (.leaf 0))
 (.leaf (.leaf 7))))
 (.leaf (.leaf 0)))))
 (.branch 48
 (.branch 40
 (.branch 36
 (.leaf (.leaf 0))
 (.branch 38
 (.branch 37
 (.leaf (.leaf 8))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 44
 (.branch 42
 (.branch 41
 (.leaf (.leaf 9))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 46
 (.leaf (.leaf 0))
 (.branch 47
 (.leaf (.leaf 10))
 (.leaf (.leaf 0))))))
 (.branch 56
 (.branch 52
 (.branch 50
 (.branch 49
 (.leaf (.leaf 11))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 54
 (.branch 53
 (.leaf (.leaf 0))
 (.leaf (.leaf 12)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))))
 (.branch 96
 (.branch 80
 (.branch 72
 (.leaf (.leaf 0))
 (.branch 76
 (.branch 74
 (.branch 73
 (.leaf (.leaf 13))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 88
 (.branch 84
 (.branch 82
 (.branch 81
 (.leaf (.leaf 14))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 92
 (.branch 90
 (.branch 89
 (.leaf (.leaf 15))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 112
 (.branch 104
 (.branch 100
 (.branch 98
 (.branch 97
 (.leaf (.leaf 16))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 108
 (.branch 106
 (.branch 105
 (.leaf (.leaf 17))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 120
 (.branch 116
 (.branch 114
 (.branch 113
 (.leaf (.leaf 18))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))))
 (.branch 192
 (.branch 160
 (.branch 144
 (.branch 136
 (.branch 132
 (.branch 130
 (.branch 129
 (.leaf (.leaf 0))
 (.leaf (.leaf 19)))
 (.branch 131
 (.leaf (.leaf 20))
 (.leaf (.leaf 21))))
 (.branch 134
 (.branch 133
 (.leaf (.leaf 22))
 (.leaf (.leaf 23)))
 (.branch 135
 (.leaf (.leaf 24))
 (.leaf (.leaf 0)))))
 (.branch 140
 (.branch 138
 (.branch 137
 (.leaf (.leaf 25))
 (.leaf (.leaf 0)))
 (.branch 139
 (.leaf (.leaf 26))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0))))
 (.branch 152
 (.branch 148
 (.branch 146
 (.branch 145
 (.leaf (.leaf 27))
 (.leaf (.leaf 28)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 156
 (.branch 154
 (.branch 153
 (.leaf (.leaf 29))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 176
 (.branch 168
 (.branch 164
 (.branch 162
 (.branch 161
 (.leaf (.leaf 30))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 166
 (.branch 165
 (.leaf (.leaf 31))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 172
 (.branch 170
 (.branch 169
 (.leaf (.leaf 32))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 184
 (.branch 180
 (.branch 178
 (.branch 177
 (.leaf (.leaf 33))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 224
 (.branch 208
 (.branch 200
 (.branch 196
 (.branch 194
 (.branch 193
 (.leaf (.leaf 34))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 204
 (.branch 202
 (.branch 201
 (.leaf (.leaf 35))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 216
 (.branch 212
 (.branch 210
 (.branch 209
 (.leaf (.leaf 36))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 240
 (.branch 232
 (.branch 228
 (.branch 226
 (.branch 225
 (.leaf (.leaf 37))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))))
 (.branch 384
 (.branch 320
 (.branch 288
 (.branch 272
 (.branch 264
 (.branch 260
 (.branch 258
 (.branch 257
 (.leaf (.leaf 0))
 (.leaf (.leaf 38)))
 (.branch 259
 (.leaf (.leaf 39))
 (.leaf (.leaf 40))))
 (.branch 262
 (.branch 261
 (.leaf (.leaf 41))
 (.leaf (.leaf 42)))
 (.branch 263
 (.leaf (.leaf 43))
 (.leaf (.leaf 0)))))
 (.branch 268
 (.branch 266
 (.branch 265
 (.leaf (.leaf 44))
 (.leaf (.leaf 0)))
 (.branch 267
 (.leaf (.leaf 45))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0))))
 (.branch 280
 (.branch 276
 (.branch 274
 (.branch 273
 (.leaf (.leaf 46))
 (.leaf (.leaf 47)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 284
 (.branch 282
 (.branch 281
 (.leaf (.leaf 48))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 304
 (.branch 296
 (.branch 292
 (.branch 290
 (.branch 289
 (.leaf (.leaf 49))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 294
 (.branch 293
 (.leaf (.leaf 50))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 300
 (.branch 298
 (.branch 297
 (.leaf (.leaf 51))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 312
 (.branch 308
 (.branch 306
 (.branch 305
 (.leaf (.leaf 52))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 352
 (.branch 336
 (.branch 328
 (.branch 324
 (.branch 322
 (.branch 321
 (.leaf (.leaf 53))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 332
 (.branch 330
 (.branch 329
 (.leaf (.leaf 54))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 344
 (.branch 340
 (.branch 338
 (.branch 337
 (.leaf (.leaf 55))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 368
 (.branch 360
 (.branch 356
 (.branch 354
 (.branch 353
 (.leaf (.leaf 56))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 448
 (.branch 416
 (.branch 400
 (.branch 392
 (.branch 388
 (.branch 386
 (.branch 385
 (.leaf (.leaf 57))
 (.leaf (.leaf 58)))
 (.branch 387
 (.leaf (.leaf 59))
 (.leaf (.branch 0x1000000000000000000000000000000040000000000000000000000000000000200000000000000000000000000000008 (.leaf 60) (.leaf 61)))))
 (.branch 390
 (.branch 389
 (.leaf (.leaf 62))
 (.leaf (.branch 0x1000000000000000000000000000000100000000000000000000000000000000200000000000000000000000000000020 (.leaf 63) (.leaf 64))))
 (.branch 391
 (.leaf (.branch 0x1000000000000000000000000000000100000000000000000000000000000000400000000000000000000000000000040 (.leaf 65) (.leaf 66)))
 (.leaf (.leaf 0)))))
 (.branch 396
 (.branch 394
 (.branch 393
 (.leaf (.leaf 67))
 (.leaf (.leaf 0)))
 (.branch 395
 (.leaf (.branch 0x1000000000000000000000000000001000000000000000000000000000000000400000000000000000000000000000400 (.leaf 68) (.leaf 69)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0))))
 (.branch 408
 (.branch 404
 (.branch 402
 (.branch 401
 (.leaf (.leaf 70))
 (.leaf (.branch 0x1000000000000000000000000000100000000000000000000000000000000000200000000000000000000000000020000 (.leaf 71) (.leaf 72))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 412
 (.branch 410
 (.branch 409
 (.leaf (.branch 0x1000000000000000000000000000100000000000000000000000000000000010000000000000000000000000001000000 (.leaf 73) (.leaf 74)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 432
 (.branch 424
 (.branch 420
 (.branch 418
 (.branch 417
 (.leaf (.leaf 75))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 422
 (.branch 421
 (.leaf (.branch 0x1000000000000000000000001000000000000000000000000000000000000001000000000000000000000001000000000 (.leaf 76) (.leaf 77)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 428
 (.branch 426
 (.branch 425
 (.leaf (.branch 0x1000000000000000000000001000000000000000000000000000000000000010000000000000000000000010000000000 (.leaf 78) (.leaf 79)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 440
 (.branch 436
 (.branch 434
 (.branch 433
 (.leaf (.branch 0x1000000000000000000000001000000000000000000000000000000000001000000000000000000000001000000000000 (.leaf 80) (.leaf 81)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 480
 (.branch 464
 (.branch 456
 (.branch 452
 (.branch 450
 (.branch 449
 (.leaf (.leaf 82))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 460
 (.branch 458
 (.branch 457
 (.leaf (.branch 0x1000000000000000100000000000000000000000000000000000000000000010000000000000001000000000000000000 (.leaf 83) (.leaf 84)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 472
 (.branch 468
 (.branch 466
 (.branch 465
 (.leaf (.branch 0x1000000000000000100000000000000000000000000000000000000000001000000000000000100000000000000000000 (.leaf 85) (.leaf 86)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 496
 (.branch 488
 (.branch 484
 (.branch 482
 (.branch 481
 (.leaf (.branch 0x1000000000000000100000000000000000000000000000000000000010000000000000001000000000000000000000000 (.leaf 87) (.leaf 88)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))))
 (.branch 768
 (.branch 640
 (.branch 576
 (.branch 544
 (.branch 528
 (.branch 520
 (.branch 516
 (.branch 514
 (.branch 513
 (.leaf (.leaf 0))
 (.leaf (.leaf 89)))
 (.branch 515
 (.leaf (.leaf 90))
 (.leaf (.leaf 91))))
 (.branch 518
 (.branch 517
 (.leaf (.leaf 92))
 (.leaf (.leaf 93)))
 (.branch 519
 (.leaf (.leaf 94))
 (.leaf (.leaf 0)))))
 (.branch 524
 (.branch 522
 (.branch 521
 (.leaf (.leaf 95))
 (.leaf (.leaf 0)))
 (.branch 523
 (.leaf (.leaf 96))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0))))
 (.branch 536
 (.branch 532
 (.branch 530
 (.branch 529
 (.leaf (.leaf 97))
 (.leaf (.leaf 98)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 540
 (.branch 538
 (.branch 537
 (.leaf (.leaf 99))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 560
 (.branch 552
 (.branch 548
 (.branch 546
 (.branch 545
 (.leaf (.leaf 100))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 550
 (.branch 549
 (.leaf (.leaf 101))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 556
 (.branch 554
 (.branch 553
 (.leaf (.leaf 102))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 568
 (.branch 564
 (.branch 562
 (.branch 561
 (.leaf (.leaf 103))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 608
 (.branch 592
 (.branch 584
 (.branch 580
 (.branch 578
 (.branch 577
 (.leaf (.leaf 104))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 588
 (.branch 586
 (.branch 585
 (.leaf (.leaf 105))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 600
 (.branch 596
 (.branch 594
 (.branch 593
 (.leaf (.leaf 106))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 624
 (.branch 616
 (.branch 612
 (.branch 610
 (.branch 609
 (.leaf (.leaf 107))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 704
 (.branch 672
 (.branch 656
 (.branch 648
 (.branch 644
 (.branch 642
 (.branch 641
 (.leaf (.leaf 108))
 (.leaf (.leaf 109)))
 (.branch 643
 (.leaf (.leaf 110))
 (.leaf (.branch 0x10000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000008 (.leaf 111) (.leaf 112)))))
 (.branch 646
 (.branch 645
 (.leaf (.leaf 113))
 (.leaf (.branch 0x10000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000020 (.leaf 114) (.leaf 115))))
 (.branch 647
 (.leaf (.branch 0x10000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000040 (.leaf 116) (.leaf 117)))
 (.leaf (.leaf 0)))))
 (.branch 652
 (.branch 650
 (.branch 649
 (.leaf (.leaf 118))
 (.leaf (.leaf 0)))
 (.branch 651
 (.leaf (.branch 0x10000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000400 (.leaf 119) (.leaf 120)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0))))
 (.branch 664
 (.branch 660
 (.branch 658
 (.branch 657
 (.leaf (.leaf 121))
 (.leaf (.branch 0x10000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000020000 (.leaf 122) (.leaf 123))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 668
 (.branch 666
 (.branch 665
 (.leaf (.branch 0x10000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000001000000 (.leaf 124) (.leaf 125)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 688
 (.branch 680
 (.branch 676
 (.branch 674
 (.branch 673
 (.leaf (.leaf 126))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 678
 (.branch 677
 (.leaf (.branch 0x10000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000001000000000 (.leaf 127) (.leaf 128)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 684
 (.branch 682
 (.branch 681
 (.leaf (.branch 0x10000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000010000000000 (.leaf 129) (.leaf 130)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 696
 (.branch 692
 (.branch 690
 (.branch 689
 (.leaf (.branch 0x10000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000001000000000000 (.leaf 131) (.leaf 132)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 736
 (.branch 720
 (.branch 712
 (.branch 708
 (.branch 706
 (.branch 705
 (.leaf (.leaf 133))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 716
 (.branch 714
 (.branch 713
 (.leaf (.branch 0x10000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000001000000000000000000 (.leaf 134) (.leaf 135)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 728
 (.branch 724
 (.branch 722
 (.branch 721
 (.leaf (.branch 0x10000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000100000000000000000000 (.leaf 136) (.leaf 137)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 752
 (.branch 744
 (.branch 740
 (.branch 738
 (.branch 737
 (.leaf (.branch 0x10000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000001000000000000000000000000 (.leaf 138) (.leaf 139)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))))
 (.branch 896
 (.branch 832
 (.branch 800
 (.branch 784
 (.branch 776
 (.branch 772
 (.branch 770
 (.branch 769
 (.leaf (.leaf 140))
 (.leaf (.leaf 141)))
 (.branch 771
 (.leaf (.leaf 142))
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000008 (.leaf 143) (.leaf 144)))))
 (.branch 774
 (.branch 773
 (.leaf (.leaf 145))
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000020 (.leaf 146) (.leaf 147))))
 (.branch 775
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000040 (.leaf 148) (.leaf 149)))
 (.leaf (.leaf 0)))))
 (.branch 780
 (.branch 778
 (.branch 777
 (.leaf (.leaf 150))
 (.leaf (.leaf 0)))
 (.branch 779
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000400 (.leaf 151) (.leaf 152)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0))))
 (.branch 792
 (.branch 788
 (.branch 786
 (.branch 785
 (.leaf (.leaf 153))
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000020000 (.leaf 154) (.leaf 155))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 796
 (.branch 794
 (.branch 793
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000001000000 (.leaf 156) (.leaf 157)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 816
 (.branch 808
 (.branch 804
 (.branch 802
 (.branch 801
 (.leaf (.leaf 158))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 806
 (.branch 805
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000001000000000 (.leaf 159) (.leaf 160)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 812
 (.branch 810
 (.branch 809
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000010000000000 (.leaf 161) (.leaf 162)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 824
 (.branch 820
 (.branch 818
 (.branch 817
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000001000000000000 (.leaf 163) (.leaf 164)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 864
 (.branch 848
 (.branch 840
 (.branch 836
 (.branch 834
 (.branch 833
 (.leaf (.leaf 165))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 844
 (.branch 842
 (.branch 841
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000001000000000000000000 (.leaf 166) (.leaf 167)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 856
 (.branch 852
 (.branch 850
 (.branch 849
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000100000000000000000000 (.leaf 168) (.leaf 169)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 880
 (.branch 872
 (.branch 868
 (.branch 866
 (.branch 865
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000001000000000000000000000000 (.leaf 170) (.leaf 171)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 960
 (.branch 928
 (.branch 912
 (.branch 904
 (.branch 900
 (.branch 898
 (.branch 897
 (.leaf (.leaf 172))
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000 (.leaf 173) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000200000000000000000000000000000000 (.leaf 174) (.leaf 175)))))
 (.branch 899
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000 (.leaf 176) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000400000000000000000000000000000000 (.leaf 177) (.leaf 178))))
 (.leaf (.leaf 0))))
 (.branch 902
 (.branch 901
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000 (.leaf 179) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000000 (.leaf 180) (.leaf 181))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 908
 (.branch 906
 (.branch 905
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000 (.leaf 182) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000000000000000000 (.leaf 183) (.leaf 184))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 920
 (.branch 916
 (.branch 914
 (.branch 913
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000 (.leaf 185) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000000000 (.leaf 186) (.leaf 187))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 944
 (.branch 936
 (.branch 932
 (.branch 930
 (.branch 929
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000 (.leaf 188) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000000000000000000000000 (.leaf 189) (.leaf 190))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 992
 (.branch 976
 (.branch 968
 (.branch 964
 (.branch 962
 (.branch 961
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000 (.leaf 191) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000000000000000000000 (.leaf 192) (.leaf 193))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))))
def signatureIndex (q signature : Nat) : Nat := (signatureIndexTable.get q).get signature
def candidateMasksBlocks : Table Nat :=
(.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf candidateMasksBlock0000)
 (.leaf candidateMasksBlock0001))
 (.branch 3
 (.leaf candidateMasksBlock0002)
 (.leaf candidateMasksBlock0003)))
 (.branch 6
 (.branch 5
 (.leaf candidateMasksBlock0004)
 (.leaf candidateMasksBlock0005))
 (.branch 7
 (.leaf candidateMasksBlock0006)
 (.leaf candidateMasksBlock0007))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf candidateMasksBlock0008)
 (.leaf candidateMasksBlock0009))
 (.branch 11
 (.leaf candidateMasksBlock0010)
 (.leaf candidateMasksBlock0011)))
 (.branch 14
 (.branch 13
 (.leaf candidateMasksBlock0012)
 (.leaf candidateMasksBlock0013))
 (.branch 15
 (.leaf candidateMasksBlock0014)
 (.leaf candidateMasksBlock0015)))))
def candidateMasks (i : Nat) := PackedRawNatGrowth.take 406
  (PackedRawNatGrowth.drop (406*(i%64)) (candidateMasksBlocks.get (i/64)))

def badMasksBlocks : Table Nat :=
(.branch 3
 (.branch 1
 (.leaf badMasksBlock0000)
 (.branch 2
 (.leaf badMasksBlock0001)
 (.leaf badMasksBlock0002)))
 (.branch 5
 (.branch 4
 (.leaf badMasksBlock0003)
 (.leaf badMasksBlock0004))
 (.branch 6
 (.leaf badMasksBlock0005)
 (.leaf badMasksBlock0006))))
def badMasks (i : Nat) := PackedRawNatGrowth.take 406
  (PackedRawNatGrowth.drop (406*(i%64)) (badMasksBlocks.get (i/64)))

def signatureMasksBlocks : Table Nat :=
(.branch 2
 (.branch 1
 (.leaf signatureMasksBlock0000)
 (.leaf signatureMasksBlock0001))
 (.branch 3
 (.leaf signatureMasksBlock0002)
 (.leaf signatureMasksBlock0003)))
def signatureMasks (i : Nat) := PackedRawNatGrowth.take 406
  (PackedRawNatGrowth.drop (406*(i%64)) (signatureMasksBlocks.get (i/64)))

def fastKind := rawKind
def candidateSupports := candidateRows
def kindSupports := kindRows
def wellFormedTest (i : Nat) : Bool := RawFacetEmbedding.wellFormedCheck (rawCells i)

def cellTest (i : Nat) := (listBounds 1024 (rawCells i).ridgeMasks && ((rawCells i).ridgeMasks.all (fun q => (candidateMasks q).testBit i) && (decide (rawKind i = (rawCells i).kind) && (decide ((rawCells i).vertices < 1024) && ((List.range 10).all (fun v => decide ((vertexMasks v).testBit i = (rawCells i).vertices.testBit v)) && (SignatureCompatibility.faces (rawCells i)).all (fun q => (SignatureCompatibility.profileMask (SignatureCompatibility.allMask 406) signatureIndex signatureMasks (rawCells i) q).testBit i))))))
def ridgeTest (i : Nat) := decide (candidateMasks i = RawNatGrowthCheck.mask (candidateRows i)) &&
  (candidateRows i).all (fun c => hasNat (rawCells c).ridgeMasks i)
def kindTest (i : Nat) := decide (kindMasks i = RawNatGrowthCheck.mask (kindRows i)) &&
  (kindRows i).all (fun c => decide ((rawCells c).kind = i))
def badTest (i : Nat) := if badMasks i = 0 then true else
  decide (Nat.land (badMasks i) (SignatureCompatibility.cover (SignatureCompatibility.allMask 406)
    vertexMasks signatureIndex signatureMasks (rawCells i)) = 0)

end Papers.RationalityTen.RootedCaches.RootedSevenPure028

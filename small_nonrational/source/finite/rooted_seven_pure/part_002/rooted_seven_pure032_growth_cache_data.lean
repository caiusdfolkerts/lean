module
prelude
public import RootedSevenPure032
public import SignatureCompatibility
public import PackedRawNatGrowth
public import FiniteChecks
public import RawFacetEmbedding
public import RootedSevenPure032GrowthCachecandidateMasksData000
public import RootedSevenPure032GrowthCachebadMasksData000
public import RootedSevenPure032GrowthCachesignatureMasksData000

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure032
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def rawCells := Papers.RationalityTen.FacetUniverses.RootedSevenPure032.rawCells
def cells (c : Fin 461) := rawCells c.val
def ridgeList := ConcreteGrowth.ridgeList cells
def literalCompatible (a b : Fin 461) := ConcreteGrowth.compatible (cells a) (cells b)
def kind (c : Fin 461) := (cells c).kind
def rawKindCode : Nat := 90470547384939709328558794442657240979953177407311136247202475124391253817579384040149161859668028626879754223752317989554763828702634312670429539757815507353923793035388578877358487992855624441174878584847358679501846064695088457847216079611562820454730981548134257258530718252768673653949970945212126177140326131566901287850923415019882296143927970220170389995191540454106244054879941423742464884434922173154759240
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
 (.leaf 0x2d968b2582b958aa5429948a250279389a4c259289248239188a442190882401f8f87a3c1d8e872380180802000028))))
 (.leaf 0x0))
 (.branch 24
 (.leaf 0x0)
 (.branch 28
 (.branch 26
 (.leaf 0x0)
 (.branch 27
 (.leaf 0x0)
 (.leaf 0x2f174b8000004)))
 (.leaf 0x0))))
 (.branch 48
 (.branch 40
 (.leaf 0x0)
 (.branch 44
 (.leaf 0x0)
 (.branch 46
 (.leaf 0x0)
 (.branch 47
 (.leaf 0x51a8942000004)
 (.leaf 0x0)))))
 (.branch 56
 (.branch 52
 (.leaf 0x0)
 (.branch 54
 (.branch 53
 (.leaf 0x0)
 (.leaf 0x3b1d4e8000004))
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
 (.leaf 0x8341609038140600ff7f3f5f8fb7d3e5f0f77b3d5e8f3793c5e0ef773b5d8eb753a5d0e773395c8e30d86832000028)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 112
 (.branch 104
 (.leaf 0x0)
 (.branch 108
 (.branch 106
 (.branch 105
 (.leaf 0x9fcfa7b3c9dcea73389bcda6b3499cca633097cba5b2c95caa532893c9a4b2491c8a43208fc7a3b1c108803e000028)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 120
 (.branch 116
 (.branch 114
 (.branch 113
 (.leaf 0xc6e33178ac4e230f86c2e130782c0e02ff7ebedf2f77abcde2ef76badd2e772b8dc2df6eb6db2d76a158a852000028)
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
 (.leaf 0xde6e361acd26833194c86330980b84d259208e45208fc783b1c8140801001a)))
 (.branch 134
 (.branch 133
 (.leaf 0x0)
 (.leaf 0x10e864220d02803f1f4f87b3c9e0e84f251248c45218f87a3a1c8200e01001a))
 (.branch 135
 (.leaf 0x168b358ac15cad55aa952a853295424e261248e44211007a3b1c03c1c01001a)
 (.leaf 0x0))))
 (.branch 140
 (.branch 138
 (.leaf 0x0)
 (.branch 139
 (.leaf 0x64b218cc561b0980bf5f2f576ba5097024110010)
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 152
 (.branch 148
 (.branch 146
 (.branch 145
 (.leaf 0x0)
 (.leaf 0x4e26d32984b255269248a411c8d3a170160a0010))
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 156
 (.branch 154
 (.branch 153
 (.leaf 0x22f168a44e231087436190b84c21f0f679bc9e0ec7539dcce42e0743819001a)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 176
 (.branch 168
 (.branch 164
 (.leaf 0x0)
 (.branch 166
 (.branch 165
 (.leaf 0x6f375b6da6c35daad469b49a0cf509d02c150010)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 172
 (.branch 170
 (.branch 169
 (.leaf 0x2a14fa6d329549a3d1a8b44a1506632f964ae532591c823f1d5088c441f001a)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 184
 (.branch 180
 (.branch 178
 (.branch 177
 (.leaf 0x33d9dcde6b3197cae532792c863eff7dbd5e6ef73b8dbadb6b3a0b45829001a)
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
 (.leaf 0xb2d92c561afd7ab95bad566af5699cba5b2a94c9e45218f475f4f57a3c5e0ee74ba1cae4130943e190024)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 216
 (.branch 212
 (.branch 210
 (.branch 209
 (.leaf 0xd9ecb61afd6eb355a9d469f4ba4c0df2f778bbdd6e16fb65adf2f77a3c9deed75ba1cce3180bc52190024)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 240
 (.branch 232
 (.branch 228
 (.branch 226
 (.branch 225
 (.leaf 0xe471f8bc4e17077fbedeef375b9c05faf779bb5d2e56fb6daa653096cae5126924863f1c1a0cc521f0024)
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
 (.leaf 0xe270369b0d46933994c8623097cba592b950a651200f87a3a1c0180802001a)))
 (.branch 262
 (.branch 261
 (.leaf 0x0)
 (.leaf 0x1128842a1104813f9f4f87a3c9dcea5b2b154a451210fc783b1c0240e02001a))
 (.branch 263
 (.leaf 0x16cb5592c55eae562a952a753291445a2c154a65021904783a1c8401c02001a)
 (.leaf 0x0))))
 (.branch 268
 (.branch 266
 (.leaf 0x0)
 (.branch 267
 (.leaf 0x65b298ec66230d82bf5f2f176b95117426110010)
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 280
 (.branch 276
 (.branch 274
 (.branch 273
 (.leaf 0x0)
 (.leaf 0x4f27534994ba59289248a3d1c8c3a974180a0010))
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 284
 (.branch 282
 (.branch 281
 (.leaf 0x233188ac52251187c36190a84c1e09027fbf9f8eb74ba1cae32e878381a001a)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 304
 (.branch 296
 (.branch 292
 (.leaf 0x0)
 (.branch 294
 (.branch 293
 (.leaf 0x7037db8db6cb61acd469b45a0ce511d42e150010)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 300
 (.branch 298
 (.branch 297
 (.leaf 0x2a551a7536974aa451a8b43a15027b3b9c4de6b24914863d1c510904420001a)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 312
 (.branch 308
 (.branch 306
 (.branch 305
 (.leaf 0x3419fce66f3398cb6532791c863b1789c36170772b85bed96a3a8b8582a001a)
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
 (.leaf 0xb3d9ac762b057ebb5bad562af559fcea73369ac9a47208fc720d01803f5f8ed7539dcce313894401a0024)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 344
 (.branch 340
 (.branch 338
 (.branch 337
 (.leaf 0xdaed363b0d76b757a9d469b4ba3c6e230f84c1dd2e36eb6daa0b03803f9f6ee7639dcae4188bc541a0024)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 368
 (.branch 360
 (.branch 356
 (.branch 354
 (.branch 353
 (.leaf 0xe57278dc5e1f0b81bedeeef75b8c662b0f85c15d6e76eb65ae7d3c9ccde692792c823d1d1a8cc54200024)
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
 (.leaf 0x9e4e25d2a9449a411e8e44a1d04803f9f8f67a3c9c4de6a3419ccc63311847e3e1e8f0763a068280e040025))
 (.branch 387
 (.leaf 0xcb64b1184c1602f578bb5b2d15ead562ad50a7531c0dc6d3599ccc643017c82401e8f072380a0441c040025)
 (.leaf 0x399c886420004)))
 (.branch 390
 (.branch 389
 (.leaf 0xe06f365aed66ab49a2d05aacd64b0562ad52a5522210c85419fcfc7c3c1dc86421d8e872380c0541c070025)
 (.leaf 0x45a2882400004))
 (.branch 391
 (.leaf 0x5c2dc7e3e0004)
 (.leaf 0x0))))
 (.branch 396
 (.branch 394
 (.branch 393
 (.leaf 0x167b2d82bd5dae566b157a95429749a451e8943a148e45219047e3d198bc4a210f8742e1509753a5d0e77339594c863b1582c05f2e972281288838110035)
 (.leaf 0x0))
 (.branch 395
 (.leaf 0x19acc0002)
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 408
 (.branch 404
 (.branch 402
 (.branch 401
 (.leaf 0x1b5d9ebb59abd569f4da5d067b3397cb6572591c85c6e16fb75b6d9188b456270f874321107763add0e77238d3a9b4d261289348a351832178b0380a0035)
 (.leaf 0x1409f0002))
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 412
 (.branch 410
 (.branch 409
 (.leaf 0x8dc69dced0004)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 432
 (.branch 424
 (.branch 420
 (.branch 418
 (.branch 417
 (.leaf 0x1cae470f83c0dfef377bacfe77399acb657278fc75cee56fb75aed551a7d3a9948a3d16834092c9243208ec71bedd6e369acd569b3d9c36198b044150035)
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 422
 (.branch 421
 (.leaf 0x1c4e10002)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 428
 (.branch 426
 (.branch 425
 (.leaf 0xaa54e4f260004)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 440
 (.branch 436
 (.branch 434
 (.branch 433
 (.leaf 0xd1686eb740004)
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
 (.leaf 0x1c9e3f1b89c0dfef773b8da6cb63afd5eab51a4d1dd6e96db65aed566b258ec35dae56aad5593c9a3f1e8ec71dced73395c8e31b8cc5e250031)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 460
 (.branch 458
 (.branch 457
 (.leaf 0x2d36892c91d8eb0006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 472
 (.branch 468
 (.branch 466
 (.branch 465
 (.leaf 0x36fb6b9dc9d4e90006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 496
 (.branch 488
 (.branch 484
 (.branch 482
 (.branch 481
 (.leaf 0x399cbb8dc247220006)
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
 (.leaf 0xe672369acd46833998c6623017cbc582b154a450261289246220180a03001a)))
 (.branch 518
 (.branch 517
 (.leaf 0x0)
 (.leaf 0x1168a42a0d04803f9f8f67a3c1dcec5a2b950a6502712c9047220241003001a))
 (.branch 519
 (.leaf 0x170b7592c15ead562ad50a752a91465b2c950a451279349046228401e03001a)
 (.leaf 0x0))))
 (.branch 524
 (.branch 522
 (.leaf 0x0)
 (.branch 523
 (.leaf 0x66b318ec56230982c05eaf174b95197826120010)
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 536
 (.branch 532
 (.branch 530
 (.branch 529
 (.leaf 0x0)
 (.leaf 0x5027d34984ba5528934823d1a8c3b178180b0010))
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 540
 (.branch 538
 (.branch 537
 (.leaf 0x2371a8ac4e251087c3a170a8441e0701803f5f6f77abd1e2ef2f0783a1b001a)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 560
 (.branch 552
 (.branch 548
 (.leaf 0x0)
 (.branch 550
 (.branch 549
 (.leaf 0x71385b8da6cb5dacd5693459ece519d82e160010)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 556
 (.branch 554
 (.branch 553
 (.leaf 0x2a953a75329749a451e8943a0d02793a9ccda6930974b65528518904621001a)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 568
 (.branch 564
 (.branch 562
 (.branch 561
 (.leaf 0x345a1ce66b3397cb6572591c7e3b1588c3e13057ebe5eef1763b0b85a2b001a)
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
 (.leaf 0xb4da2c761b057abb5cacd62ad559f4ee71379a4ca5f2c95ca20b027fbf9f6f97b3cde4ef13898421b0024)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 600
 (.branch 596
 (.branch 594
 (.branch 593
 (.leaf 0xdbedb63afd76b357aad3e9b49a3c66270d85c1602fb7abcdda0d047fbf5f8fa7c3cde2f0188c0561b0024)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 624
 (.branch 616
 (.branch 612
 (.branch 610
 (.branch 609
 (.leaf 0xe672f8dc4e1f0781bfde6ef73b8c6e2f0d84c1e06ff7abc5de7f3d9c4da6b3398cb255291a8d056210024)
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
 (.leaf 0xa04da5d2c94492451e8d45a1904813f9f4f87a3c1ccdc6a3499cca6431180964a249208e460682c10050025))
 (.branch 643
 (.leaf 0xcd6431186c15faf978ba5c2cd5eae562a952a7529c8de6d3619cca633097c9a4c249208a440a0481e050025)
 (.leaf 0x389c09e4e0004)))
 (.branch 646
 (.branch 645
 (.leaf 0xe26eb65b0d66a34da2cf5bad164b1562a950a6522290e85421fcfa7b3c9dc9e4e239188a440c0581e080025)
 (.leaf 0x44a209a4c0004))
 (.branch 647
 (.leaf 0x5b2d4964a0004)
 (.leaf 0x0))))
 (.branch 652
 (.branch 650
 (.branch 649
 (.leaf 0x169b2582bf5dadd6ab156aa53e974aa451a8b43a0cbe5d2d964ae551b8b44a230f86c3215087b3d5e8f3793c598c963b1982bf5eaed72281308c3a120035)
 (.leaf 0x0))
 (.branch 651
 (.leaf 0x196ca0002)
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 664
 (.branch 660
 (.branch 658
 (.branch 657
 (.leaf 0x1b7d96bb5babd4ea34da4d16773398cb6532791c7df6f97bbd5e6f11a8bc56290f86c2e13077c3dde8f3783bd3e9c4d2652892482391832180b43a0b0035)
 (.leaf 0x13c9d0002))
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 668
 (.branch 666
 (.branch 665
 (.leaf 0x8cc61f4f90004)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 688
 (.branch 680
 (.branch 676
 (.branch 674
 (.branch 673
 (.leaf 0x1cce3f0f85c0df6f777b9d0e7b399bcb6532590c75fefd7bbd5deed53a853a9b48a3512854098cc25b2c94ca1c2de6e36dacd4693419c361a0b446160035)
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 678
 (.branch 677
 (.leaf 0x1c0df0002)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 684
 (.branch 682
 (.branch 681
 (.leaf 0xa954667320004)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 696
 (.branch 692
 (.branch 690
 (.branch 689
 (.leaf 0xd067f03800004)
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
 (.leaf 0x1cbe471b8bc0df6f375b8db6cf63b0d5ea74fa5d1e070179bc5deed68b2d8ec55dadd66af5599cca572a94ca1f4f9793c5e0ef1b8d060260031)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 716
 (.branch 714
 (.branch 713
 (.leaf 0x2cf6698cc1f0f70006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 728
 (.branch 724
 (.branch 722
 (.branch 721
 (.leaf 0x36bb4bfdf9ecf50006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 752
 (.branch 744
 (.branch 740
 (.branch 738
 (.branch 737
 (.leaf 0x395c9bedf25f2e0006)
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
 (.leaf 0x9f4ea592a9349245208c4522102803f1f4f87b3b9c8e06934198ca643197cae562a950a6520683012060025))
 (.branch 771
 (.leaf 0xcc6530d84c05faf97ab95bad55cad55aa952a8521cce26c35998ca6230980b2582a950a2500a04c20060025)
 (.leaf 0x379b8b65a0004)))
 (.branch 774
 (.branch 773
 (.leaf 0xe16fb61aed56a34da4ce5c2d962b055aa94ea652a2d1284419f8fa7a3c9e0b65a29948a2500c05c20090025)
 (.leaf 0x43a18b2580004))
 (.branch 775
 (.leaf 0x5a2ccae560004)
 (.leaf 0x0))))
 (.branch 780
 (.branch 778
 (.branch 777
 (.leaf 0x168b357ebd5cadd6ab355a9d469549a3d1a8b44a04ee75399c4de6d1a8c446210e86c3217078140600ff7f3f59acb6331580bf5e2ed7428138903c130035)
 (.leaf 0x0))
 (.branch 779
 (.leaf 0x192c80002)
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 792
 (.branch 788
 (.branch 786
 (.branch 785
 (.leaf 0x1b6da6b759aad4ea34fa3d0e7f3197cae532792c76271187c3617091b8cc52270e86c2a13088240e00ff7e3ed409e4ca61269247a391a32188b83c0c0035)
 (.leaf 0x1389b0002))
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 796
 (.branch 794
 (.branch 793
 (.leaf 0x8bc5a0d050004)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 816
 (.branch 808
 (.branch 804
 (.branch 802
 (.branch 801
 (.leaf 0x1cbe4f0b83bfdf6f779b8d1683379acae532390c7e2f1587c360f0554a95369947a350e85419ecf273389acd1c4e06db69aad468b419e361a8b848170035)
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 806
 (.branch 805
 (.leaf 0x1bcdd0002)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 812
 (.branch 810
 (.branch 809
 (.leaf 0xa853e7f3e0004)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 824
 (.branch 820
 (.branch 818
 (.branch 817
 (.leaf 0xcf6771b8c0004)
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
 (.leaf 0x1cce571789bfdf6ef75b9dbed761afd56a74da5d26371985c260f0569b3d8ac35cadd62af569fcfa6f369acd20d057f3f5f8fb1b8d462270031)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 844
 (.branch 842
 (.branch 841
 (.leaf 0x2cb649ecf209030006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 856
 (.branch 852
 (.branch 850
 (.branch 849
 (.leaf 0x367b2c5e2a05010006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 880
 (.branch 872
 (.branch 868
 (.branch 866
 (.branch 865
 (.leaf 0x391c7c4e22773a0006)
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
 (.leaf 0x73397cae4f238fbdde6ef75b9dc6df6db5da6cf65a8d3e9b4ba4d1e8b43a0cfe7b3b93c9647218fc75a6d167b3596c95aacd62af56aad52a752a8d429f45a250e8541a046e35198c45e2d0c85c2a130883b89c2e06fb79bad369345a0cf6733598cb6532590be5eaf176ba5cae16eb65aad166a95429d4ca5522813e9e4ea7136914823d1c8d4622d14894421d0c7c3d9e8f2783b9cce471381bcdc6431988c2602f8dc6c3214060280d0097)
 (.leaf 0x9a4ca610a84419b4d86b0009))
 (.branch 899
 (.leaf 0xc76331564b1581a8d2680009)
 (.leaf 0x0)))
 (.branch 902
 (.branch 901
 (.leaf 0xdc6db695eae56a0902800009)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 908
 (.branch 906
 (.branch 905
 (.leaf 0xb1d8ac34ea6d322b1489b1186c2000c)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 920
 (.branch 916
 (.branch 914
 (.branch 913
 (.leaf 0xd8ec35f9ccde6a25118825d2c95000c)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 944
 (.branch 936
 (.branch 932
 (.branch 930
 (.branch 929
 (.leaf 0xe37178999cc65e974aa4b65b0d7000c)
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
 (.leaf 0x1c3e17075dadd6582bf5e0009)
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
 (.leaf 0xdc6c351a0cc6431180bc5c2d160ac54291409c4c251208c44211007c3c1d0e06c34190c05c2c150a04c24110803c1c0d0602c14090401c0c050200c04010037))
 (.branch 3
 (.leaf 0xe06ff7dbdde6ef75b9dc6af55a9d469f4da5d268f2d95ca64f2591c863f1d87c36170983c15eef579bc5deed6fb75b6d96bb5576b95bad566b157ab5569147a35168943a150681399c4de6d359a4b6592b954a651219047e3d1d8e43e1d0d8642e15098441e00ff7f3f5f8fb7a3cde4f1783bdd0e773395c8e36b355a8d369345a0cf6730580bf5f2f578bb5d2e558ab552a550a753295489449a49229047a391a8c3f9f8fa7c3d9e8f2783b99ccc653218cc4613017caa5429948a250249208e46229107a3c1d8e8723800b4)
 (.branch 4
 (.leaf 0x1cce5f2b93c8e3f1b8bc4e1f0b83b7db6d769b3d96c761afd76b759a2d0e833f9ecee73379acce632f8dc662f1589c4607017fbf5f6f975ba5cee571b85a6d167b3596c963b1586c15faf552a752a8d429f4ea6d32974aa4cfe7d3d9e4ee7533994c6612f9749e4d259248e451b8d46631178b456291389446210682c12070280be9f2f87bbd9eaee76bb1d6ea74b89c2e06fb79badc6db69b2d86bb3598cb6532590c76331588c3612e16eb65aad166b258ac15eae56a8d44a15027d3c9d4e26d34994c25d2c9545a29128843a190a8441a0902803b1d4e873391c4e06f371b4d86b351a4d05e2e970b65a2c960ae56279389a4c259288642209007e3e00e1)
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
 (.leaf 0xfffffffffffffe))
 (.branch 3
 (.leaf 0x1ff000ff8007fc0fc0fc0fc003fe001ff03f03f03f000ff81f81f81f8007fc003fe001ff0001ff000ff8000ff803f03f03f00000000000000)
 (.branch 4
 (.leaf 0x1ffe00fff007ff803f03f03f03ffc01ffe00fc0fc0fc0fff007e07e07e07ff803ffc01ffe00fffe00fff007fff007fc0fc0fc000000000000000)
 (.leaf 0x0))))
def kindMasks := kindMaskTable.get
def keys := List.range 5
def vertexMaskTable : Table Nat :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf 2923003274661805836407369665432493981717827174399)
 (.leaf 102844034832572454631410912187074748928312801020489776825876607))
 (.branch 3
 (.leaf 215679470493219325636343192573185288654571195736673616378772349633423)
 (.branch 4
 (.leaf 9394170331095332911557922387157348109502514516162786263503545080957304682496629100700921912714597894051463169)
 (.leaf 2839213766779714416208286730392186616986000007293531717902073252738208403085448992980913053624081468954412829945226169504190087306241))))
 (.branch 7
 (.branch 6
 (.leaf 5954259990217198710289726855043667939606562974372563405425530522469522366601196276968424262204458140147070057521106428957601856487958773761)
 (.leaf 5954262829428257805401540674609606765808671356293121414330193691618582605090772622902750562605478282908980931140646124990816431812875649025))
 (.branch 8
 (.leaf 5954262829429611646734655772721591575927897214444602444730292807731669370677765838351777868887008806265361368390285570974347700316407262642)
 (.branch 9
 (.leaf 5954262829429611647379903064672269243674664515810005177974137712931948384241179618466883542753760214095660616722999476053338192331176376020)
 (.leaf 5954262829429611647380060595749405639589641753920690090750808573504507046109725373784294463070212014428512761976600465135386091814458866536)))))
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
def candidateMasks (i : Nat) := PackedRawNatGrowth.take 461
  (PackedRawNatGrowth.drop (461*(i%64)) (candidateMasksBlocks.get (i/64)))

def badMasksBlocks : Table Nat :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf badMasksBlock0000)
 (.leaf badMasksBlock0001))
 (.branch 3
 (.leaf badMasksBlock0002)
 (.leaf badMasksBlock0003)))
 (.branch 6
 (.branch 5
 (.leaf badMasksBlock0004)
 (.leaf badMasksBlock0005))
 (.branch 7
 (.leaf badMasksBlock0006)
 (.leaf badMasksBlock0007))))
def badMasks (i : Nat) := PackedRawNatGrowth.take 461
  (PackedRawNatGrowth.drop (461*(i%64)) (badMasksBlocks.get (i/64)))

def signatureMasksBlocks : Table Nat :=
(.branch 2
 (.branch 1
 (.leaf signatureMasksBlock0000)
 (.leaf signatureMasksBlock0001))
 (.branch 3
 (.leaf signatureMasksBlock0002)
 (.leaf signatureMasksBlock0003)))
def signatureMasks (i : Nat) := PackedRawNatGrowth.take 461
  (PackedRawNatGrowth.drop (461*(i%64)) (signatureMasksBlocks.get (i/64)))

def fastKind := rawKind
def candidateSupports := candidateRows
def kindSupports := kindRows
def wellFormedTest (i : Nat) : Bool := RawFacetEmbedding.wellFormedCheck (rawCells i)

def cellTest (i : Nat) := (listBounds 1024 (rawCells i).ridgeMasks && ((rawCells i).ridgeMasks.all (fun q => (candidateMasks q).testBit i) && (decide (rawKind i = (rawCells i).kind) && (decide ((rawCells i).vertices < 1024) && ((List.range 10).all (fun v => decide ((vertexMasks v).testBit i = (rawCells i).vertices.testBit v)) && (SignatureCompatibility.faces (rawCells i)).all (fun q => (SignatureCompatibility.profileMask (SignatureCompatibility.allMask 461) signatureIndex signatureMasks (rawCells i) q).testBit i))))))
def ridgeTest (i : Nat) := decide (candidateMasks i = RawNatGrowthCheck.mask (candidateRows i)) &&
  (candidateRows i).all (fun c => hasNat (rawCells c).ridgeMasks i)
def kindTest (i : Nat) := decide (kindMasks i = RawNatGrowthCheck.mask (kindRows i)) &&
  (kindRows i).all (fun c => decide ((rawCells c).kind = i))
def badTest (i : Nat) := if badMasks i = 0 then true else
  decide (Nat.land (badMasks i) (SignatureCompatibility.cover (SignatureCompatibility.allMask 461)
    vertexMasks signatureIndex signatureMasks (rawCells i)) = 0)

end Papers.RationalityTen.RootedCaches.RootedSevenPure032

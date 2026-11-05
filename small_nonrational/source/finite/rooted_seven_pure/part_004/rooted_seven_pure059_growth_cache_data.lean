module
prelude
public import RootedSevenPure059
public import SignatureCompatibility
public import PackedRawNatGrowth
public import FiniteChecks
public import RawFacetEmbedding
public import RootedSevenPure059GrowthCachecandidateMasksData000
public import RootedSevenPure059GrowthCachebadMasksData000
public import RootedSevenPure059GrowthCachesignatureMasksData000

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure059
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def rawCells := Papers.RationalityTen.FacetUniverses.RootedSevenPure059.rawCells
def cells (c : Fin 461) := rawCells c.val
def ridgeList := ConcreteGrowth.ridgeList cells
def literalCompatible (a b : Fin 461) := ConcreteGrowth.compatible (cells a) (cells b)
def kind (c : Fin 461) := (cells c).kind
def rawKindCode : Nat := 90470547384939709328558794442657240979953177407311136247202475271004614035762015127157665457676004571042561456340649839308664002750208220719772445437074313008316183256255011853307944474273804814674917636479357028653558019578211218892557998164126820125928083504928208491595010068251894026328070933484713506204087358219001418488651683031667550657928302384436097123402893878629920464466231677104062097594738368982585928
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
 (.branch 20
 (.leaf 0x0)
 (.branch 22
 (.branch 21
 (.leaf 0x0)
 (.leaf 0x4ba592a9449a49229047a391a8c45a29128843a190a8441a0902803f9f8fa7c3d9e8f2783b9d8ea74048200e000028))
 (.leaf 0x0)))
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
 (.leaf 0x6230d84000004)
 (.leaf 0x0)))))
 (.leaf 0x0)))
 (.branch 96
 (.branch 80
 (.leaf 0x0)
 (.branch 88
 (.branch 84
 (.leaf 0x0)
 (.branch 86
 (.branch 85
 (.leaf 0x89446210f87436190b8542611078341609038140600ff7f3f5f8fb7d3e5f0f77b3d5e8f3793c5e0ef0d06430000028)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 112
 (.branch 104
 (.branch 100
 (.leaf 0x0)
 (.branch 102
 (.branch 101
 (.leaf 0xa5d2a9348a3d1a8b44a1d0a83409fcfa7b3c9dcea73389bcda6b3499cca633097cba5b2c95caa53281007c3c000028)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 120
 (.leaf 0x0)
 (.branch 124
 (.branch 122
 (.branch 121
 (.leaf 0xbc5deec000004)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))))
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
 (.leaf 0x5429d4aa4512853e9e4ea71349944a1d0883409f4f6783b9d49e4a249188a431f0f47439058280e010024))
 (.branch 135
 (.leaf 0x1aad4693459ece6632d94c963b19844e261248e44211007a3b1c0482201001a)
 (.leaf 0x0))))
 (.branch 140
 (.branch 138
 (.leaf 0x0)
 (.branch 139
 (.leaf 0x753a5cee67238dc2e06fb79b8db611702a140010)
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 152
 (.branch 148
 (.branch 146
 (.branch 145
 (.leaf 0x0)
 (.leaf 0x17abc5d2e56eb65a2cd64b157ab9168642a09027f3d1e4ec752e0381a07001a))
 (.leaf 0x0))
 (.branch 150
 (.branch 149
 (.leaf 0x91c8a411f8ec7235198c45e2b1482409fefe7e3e1ecf3793c1148842a0d007e3e1e4ee740e06c30070024)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 156
 (.branch 154
 (.branch 153
 (.leaf 0xc4e230d85c1e0b017fbf5f6f77abb17052280010)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 176
 (.branch 168
 (.branch 164
 (.leaf 0x0)
 (.branch 166
 (.branch 165
 (.leaf 0x2b95bacd62ad55a9d4aa350a75367b3b9c4de6b3197cb2572961088421e001a)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 172
 (.branch 170
 (.branch 169
 (.leaf 0xcf677379acc65f2b94c9e4b218fbb308582b0010)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 224
 (.branch 208
 (.branch 200
 (.branch 196
 (.leaf 0x0)
 (.branch 198
 (.branch 197
 (.leaf 0xb8dc2dd6db5daad167b3596c7629fcea73369acce5d2d954a60d01803f5f8fa7abd1e2f0128903c180024)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 216
 (.branch 212
 (.branch 210
 (.branch 209
 (.leaf 0x367b2d86bf5bacd56a751a7d2e92ed0581c01fcfb7cbdde8f2778c05e18001a)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 240
 (.branch 232
 (.branch 228
 (.branch 226
 (.branch 225
 (.leaf 0x391c7e2f1385c1dfefb7bbcdd6e6ed3e9e4e66f34994c25b2b940d0661e001a)
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
 (.leaf 0x552a54ca551a89409e4ea6d34984aa4d208f469f0f4793b1d0b6562a948a2421f8f076380602810020024))
 (.branch 263
 (.leaf 0x1aed669b49a0cf66b2d94c863b15865a2c154a65021904783a1c84c2202001a)
 (.leaf 0x0))))
 (.branch 268
 (.branch 266
 (.leaf 0x0)
 (.branch 267
 (.leaf 0x763add0e772b91c4e06fb75b8da619742c140010)
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 280
 (.branch 276
 (.branch 274
 (.branch 273
 (.leaf 0x0)
 (.leaf 0x17ebe5dae970b75aacd64b057ab52e9248a391a7e3d9e0ee742e83c1a08001a))
 (.leaf 0x0))
 (.branch 278
 (.branch 277
 (.leaf 0x92c9243208f47637198c45a2b138843a170a843ddeaf478bbd2c9448a3d187f3e9e0ec750e86c32080024)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 284
 (.branch 282
 (.branch 281
 (.leaf 0xc5e2b0f86c260f037fbf5f2f779bb97454280010)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 304
 (.branch 296
 (.branch 292
 (.leaf 0x0)
 (.branch 294
 (.branch 293
 (.leaf 0x2bd5dad566af56aa54aa34fa75329347a250e8330974b655286188c421f001a)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 300
 (.branch 298
 (.branch 297
 (.leaf 0xd067f399bcce632d94c9e47218ebbb0c5a2b0010)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 352
 (.branch 336
 (.branch 328
 (.branch 324
 (.leaf 0x0)
 (.branch 326
 (.branch 325
 (.leaf 0xb9dcadf6eb65aed367b3592c761a5d1a8b42a0cca5f2c95ca2250d8642610f97b3cde4ef130903e190024)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 344
 (.branch 340
 (.branch 338
 (.branch 337
 (.leaf 0x36bb4d8ec35dadd5ea751a6d2e8eef1187c3215077d3e1e6f1780c45e19001a)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 368
 (.branch 360
 (.branch 356
 (.branch 354
 (.branch 353
 (.leaf 0x395c9e371787c2e06fb7bbbdd6e2ef4aa4516874099cc6592a948d4661f001a)
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
 (.leaf 0x2fd7ab85b2d568b1582bd54a851a85409f4e26d347b3d1e4f0773b1c4de6a3419ccc63311847e3e1e8f0763a080341404002b))
 (.branch 387
 (.leaf 0xec75395c6e270b79badc6bb55a0ce66b3192c8639c0dc6d3599ccc643017c82401e8f072380b85022040025)
 (.leaf 0x399c886420004)))
 (.branch 390
 (.branch 389
 (.leaf 0x5cee36cb55a6d165b258ebd5cabd56a953a853e9d2f974b6592b95496471e8e46e35178b455ecf57a3cde4f16b351a6d166b3194c662aa54ea6522813e9d4ca60fa7c3c9e0ea7421908763a1c8e04e241086c220a004b)
 (.leaf 0x158ab3f9f882400006))
 (.branch 391
 (.leaf 0x6cb607e3e0004)
 (.leaf 0x0))))
 (.branch 396
 (.branch 394
 (.branch 393
 (.leaf 0x6833d99cbe5b2b92c8e431789c260b0380bedf2f6eb74ba1cce270b7db6da170ac5014001f)
 (.leaf 0x0))
 (.branch 395
 (.leaf 0x1dced0002)
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 408
 (.branch 404
 (.branch 402
 (.branch 401
 (.leaf 0x1b5d9ebb59abd569f4da5c56230f85c0e02fd7abcc9245218fc6e35188a44df0f77a3cde0ef5f2f176b95aad164ae569fcfc773b1d4e832178a0360d0035)
 (.leaf 0x60b00fa7c0004))
 (.leaf 0x0))
 (.branch 406
 (.branch 405
 (.leaf 0x24f267d3e4f67a0006)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 412
 (.branch 410
 (.branch 409
 (.leaf 0x31b8c0002)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 432
 (.branch 424
 (.branch 420
 (.branch 418
 (.branch 417
 (.leaf 0x1cae470f83c0dfef377bacfe77399acb657278fc7576b75aac552a751a6d32633096cb253281b0cc56210025)
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 422
 (.branch 421
 (.leaf 0xb057e67320004)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 428
 (.branch 426
 (.branch 425
 (.leaf 0x345a10002)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 480
 (.branch 464
 (.branch 456
 (.branch 452
 (.branch 450
 (.branch 449
 (.leaf 0x7278fc6e27037fbddcee369b2d8ebf57aad46934772b85bedb69b459ac56199cca572a94ca1f4f9793c5e0ef1b8cc5e24002b)
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 454
 (.branch 453
 (.leaf 0x2eb7498cc1f0f70006)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 472
 (.branch 468
 (.branch 466
 (.branch 465
 (.leaf 0xdbed9ecf50004)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 496
 (.branch 488
 (.branch 484
 (.branch 482
 (.branch 481
 (.leaf 0xe672e5f2e0004)
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
 (.leaf 0x562ad4ca451a85409f4e26d32984a249228e462210c8541200b4572a14ca04e259208e440602c12030024))
 (.branch 519
 (.leaf 0x1b2d869b45a0ce66b3192c863315885b2c950a4512793490462284c2403001a)
 (.leaf 0x0))))
 (.branch 524
 (.branch 522
 (.leaf 0x0)
 (.branch 523
 (.leaf 0x773b5d0e672b8dc4e16f375b6da621782c150010)
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 536
 (.branch 532
 (.branch 530
 (.branch 529
 (.leaf 0x0)
 (.leaf 0x182c05dae570b65aad162b0572b52c934823d188a43a1106802f03c1c09001a))
 (.leaf 0x0))
 (.branch 534
 (.branch 533
 (.leaf 0x93c9a431f8f472371a8bc5a291387c36190983c0e03007ebed2e95482391a8b44a1104810e87034090024)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 540
 (.branch 538
 (.branch 537
 (.leaf 0xc6e330f85c260b0380bedf2f579bc17854290010)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 560
 (.branch 552
 (.branch 548
 (.leaf 0x0)
 (.branch 550
 (.branch 549
 (.leaf 0x2c15fad562af55aa54ea14fa6d329146a2d0a813c9d4e66d346208c4420001a)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 556
 (.branch 554
 (.branch 553
 (.leaf 0xd1687399acce5f2d95c96471f8ebc3105a2c0010)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 608
 (.branch 592
 (.branch 584
 (.branch 580
 (.leaf 0x0)
 (.branch 582
 (.branch 581
 (.leaf 0xbadd2df6db65aad368b2d92c561a551e8943a04fa77389bcd2230e85c2a0f05813fdfcfb13094401a0024)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 600
 (.branch 596
 (.branch 594
 (.branch 593
 (.leaf 0x36fb6d8ebf5dacd5eab4fa6d268ef1128842e130883411fefd7e0c4601a001a)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 624
 (.branch 616
 (.branch 612
 (.branch 610
 (.branch 609
 (.leaf 0x399cbe371387c1e06ff79bbdcee2f14ba4d1285419fcf671369a8d46820001a)
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
 (.leaf 0x30578b85bad566b2582b958a751a89409e4ea6d3287432150883411ccdc6a3499cca6431180964a249208e46080381605002b))
 (.branch 643
 (.leaf 0xee74b95c8e27037dbadb6cb51a0cf66b2d94c8631c8de6d3619cca633097c9a4c249208a440b85424050025)
 (.leaf 0x389c09e4e0004)))
 (.branch 646
 (.branch 645
 (.leaf 0x5d6e16cb5da6cf66b258ac15babd5aa952a8d3e9b3b9d4e671379b49e451e8ec6e33188b4520501803fdfcfd6c355a6d266b2d92c762aad50a652a813c9c4d261128842a110280279388e46229104e2511070240b004b)
 (.leaf 0x154a945a289a4c0006))
 (.branch 647
 (.leaf 0x6bb58964a0004)
 (.leaf 0x0))))
 (.branch 652
 (.branch 650
 (.branch 649
 (.leaf 0x68b3b99cc65b2993c8e3f1b88c260f037fbf5f2f4ed753a1cee270379b8da170b05215001f)
 (.leaf 0x0))
 (.branch 651
 (.leaf 0x1d8eb0002)
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 664
 (.branch 660
 (.branch 658
 (.branch 657
 (.leaf 0x1b7d96bb5babd4ea34da4c66270f86c0dfefb7bbcc9a47219046e33178ac4e0903803fdf8fb602f576ba5aacd62af56a2d1483412050032180a4380e0035)
 (.leaf 0x5faf912880004))
 (.leaf 0x0))
 (.branch 662
 (.branch 661
 (.leaf 0x24b24834150e860006)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 668
 (.branch 666
 (.branch 665
 (.leaf 0x3178a0002)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 688
 (.branch 680
 (.branch 676
 (.branch 674
 (.branch 673
 (.leaf 0x1cce3f0f85c0df6f777b9d0e7b399bcb6532590c757eb95aacd52a550a75327b3c9cce26b341b0d058220025)
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 678
 (.branch 677
 (.leaf 0xaf5767f3e0004)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 684
 (.branch 682
 (.branch 681
 (.leaf 0x3419f0002)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 736
 (.branch 720
 (.branch 712
 (.branch 708
 (.branch 706
 (.branch 705
 (.leaf 0x72f91c6e2f037dbcdd6e36db3d8ec357a9d3e974774b8dbedd69b3d96c7619fcfa6f369acd20d057f3f5f8fb1b8d06025002b)
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 710
 (.branch 709
 (.leaf 0x2e7729ecf209030006)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 728
 (.branch 724
 (.branch 722
 (.branch 721
 (.leaf 0xdaed205010004)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 752
 (.branch 744
 (.branch 740
 (.branch 738
 (.branch 737
 (.leaf 0xe5726773a0004)
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
 (.leaf 0x3017cb75b2d166b258ab556a9512853e9e4ea71309349245208f471c8e06934198ca643197cae562a950a6520803c1806002b))
 (.branch 771
 (.leaf 0xed75b91c6e17037dbcda6c3599ece6632d94c9629cce26c35998ca6230980b2582a950a2500b85826060025)
 (.leaf 0x379b8b65a0004)))
 (.branch 774
 (.branch 773
 (.leaf 0x5d2e56bb55a2cf66b2d86bf5dab556a752a8d429947a35168943a149a491d8e46a33188bc4e1d0d8642e15096cb5da4d16632d90c7632b154a55227d3c9b4d2652a9448a411a8c2d968a652289404e2611874260c004b)
 (.leaf 0x150a74ba58b2580006))
 (.branch 775
 (.leaf 0x6ab50ae560004)
 (.leaf 0x0))))
 (.branch 780
 (.branch 778
 (.branch 777
 (.leaf 0x6873f98cbe572993c963b198ac1e0b017fbf5f6f2ee7639dcce170375b8db170b45416001f)
 (.leaf 0x0))
 (.branch 779
 (.leaf 0x1d4e90002)
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 792
 (.branch 788
 (.branch 786
 (.branch 785
 (.leaf 0x1b6da6b759aad4ea34fa3c6e2f0d85c05fef97bbd49e4b208fc6a33168ac52210f8642e110760afd74b95a2cd60af5725d2c8f472351832188a83a0f0035)
 (.leaf 0x5eaf12a940004))
 (.leaf 0x0))
 (.branch 790
 (.branch 789
 (.leaf 0x247228944526920006)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 796
 (.branch 794
 (.branch 793
 (.leaf 0x313880002)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 816
 (.branch 808
 (.branch 804
 (.branch 802
 (.branch 801
 (.leaf 0x1cbe4f0b83bfdf6f779b8d1683379acae532390c7d82bd59ac54ea54fa75369348a2d1283401b0d45a230025)
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 806
 (.branch 805
 (.leaf 0xae56e974a0004)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 812
 (.branch 810
 (.branch 809
 (.leaf 0x33d9d0002)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 864
 (.branch 848
 (.branch 840
 (.branch 836
 (.branch 834
 (.branch 833
 (.leaf 0x73395c5e26ff7dbbdd6e76fb5d86bf55a9d36974975b9dbadb68b3d92c762a5d2a8742a0d0225118542611071b8d46226002b)
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 838
 (.branch 837
 (.leaf 0x2e370a4d22210f0006)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 856
 (.branch 852
 (.branch 850
 (.branch 849
 (.leaf 0xd9eca1d0d0004)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 880
 (.branch 872
 (.branch 868
 (.branch 866
 (.branch 865
 (.leaf 0xe471e8f460004)
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
 (.leaf 0x73397cae4f238fbdde6ef75b9dc6df6db5da6cf65a8d3e9b4ba4d1e8b43a0cfe7b3b93c9647218fc7637198bc5627117ebedf2f77abcdd6e973b95c6e166b2d92c762b0d82bf5eaed72b751a853e9d4da649e4d259248e45188bc5a2b1489bb9daec75ba9d2df6f375b8db6d365b0d76b355a8ca64b218ec662b0580bf5f2f578b258ac15eae56ab156aa54aa14e9d4e26d34994c1cce471381bcdc6431988c2602f8dc6c321709c2e100097)
 (.leaf 0xbb5d2e54ca5521b4d86b0009))
 (.branch 899
 (.leaf 0xe873b99a6d2689a8d2680009)
 (.leaf 0x0)))
 (.branch 902
 (.branch 901
 (.leaf 0x5bedd6dad566b1219047da0cf6728d44a1000f)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 908
 (.branch 906
 (.branch 905
 (.leaf 0x19ccde6b0f86c2b95c8e30009)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 920
 (.branch 916
 (.branch 914
 (.branch 913
 (.leaf 0xd8ec35f84c1e0a3d1d8e2e16eb6000c)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 944
 (.branch 936
 (.branch 932
 (.branch 930
 (.branch 929
 (.leaf 0x1c6e2f133398cbd5ead550009)
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
 (.leaf 0x1c3e17075dadd65b2d76a0009)
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
 (.leaf 0xe06ff7dbdde6ef75b9dc6af55a9d469f4da5d268f2d95ca64f2591c863f1d81c05fefd7dbe5eef579b4da2cf66b2d92c762b0d52a752a8d429f4ea6d328b44a1d0a83409cce26f369acd25b2c95caa53288dc6a33188bc5a2b1489c32170a84c220f007fbf9fafc7dbd1e6f278bc1dee270b81bede6eb71b6da66b3196ca64b218ec662ad568b3592c560af572b5409f4f275389b4d26530914823d1c8d4621508834120500793c1dcec753a19ccc653218cc4613017caa5429948a250249208e46229107a3c1d8e8723800b4)
 (.branch 4
 (.leaf 0x1cce5f2b93c8e3f1b8bc4e1f0b83b7db6d769b3d96c761afd76b759a2d0e833f9ecee73379acce632f8dc662f1589c461f0d85c260f0578bbddaeb74b9dcae370b7dbadb6cb5daac15faf576b95bad566b157ab556974aa4d228f469fcfa7b3c9dcea673298cc25f2e93c9a4b2491c8a43208fc7a3b1c89446210f874360d058240e05017d3e5f0f77b3d5dced763add4e97439dcce57238db2d86bb59aad469b49a2d067b3988c36130580bf5f2f578bb5d2e570b75b2b156aa54aa14ea652a9146a250a5d2c954a24d248b452251087431fcfc7d3e1ecf473391c4e06f371b4d86b351a4d05e2e970b65a2c960ae56279389a4c259288642209007e3e00e1)
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
 (.leaf 0x1ff000ff8007fc003fe0003fe001ff03f03f03f000ff81f81f81f8007fc003fe0003fe001ff03f03f03f000ff803f03f03f00000000000000)
 (.branch 4
 (.leaf 0x1ffe00fff007ff803ffc01fffc01ffe00fc0fc0fc0fff007e07e07e07ff803ffc01fffc01ffe00fc0fc0fc0fff007fc0fc0fc000000000000000)
 (.leaf 0x0))))
def kindMasks := kindMaskTable.get
def keys := List.range 5
def vertexMaskTable : Table Nat :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf 25108406941546723055343157692830665664409349720262100254719)
 (.leaf 883423532389167056384707203648403914839125867508702311623455591754498175))
 (.branch 3
 (.leaf 38478521676166483605741250097796497856522299458202772711069297406699703278367977880047086111955274292598861078415)
 (.branch 4
 (.leaf 1353842624082390652131846384367509348318474994212991414795502529949422641608180838298055950571661716302877108984407774112776193)
 (.leaf 2839212412937735896210208676511214357391081626797579911623697626939856385706445761692173291187430557583319344025704789088511333557121))))
 (.branch 7
 (.branch 6
 (.leaf 5954259990217198709644164654881005039198502190688476225592205643823910345239571006403368872494560001394068766733016203033038327935076925441)
 (.leaf 5954262829428257804755978512916034684225868839917853605849754805649888083023353635936707891823190101882175905200049402156258348522868310017))
 (.branch 8
 (.leaf 5954262829429611647380060403347403088417381525390912836198879377167303787438962024706979425785526064627728914540130485603163847636486155442)
 (.branch 9
 (.leaf 5954262829429611647380060441825924764592609862578704349875009654365978980529194950430011713389972756490855834655280775729913523007576061268)
 (.leaf 5954262829429611647380060518782968116925579209005405361243366605796298720772200289642258605280842739966899520083278400145110213273848765032)))))
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
 (.branch 22
 (.branch 21
 (.leaf (.leaf 6))
 (.leaf (.leaf 7)))
 (.leaf (.leaf 0))))
 (.branch 28
 (.branch 26
 (.branch 25
 (.leaf (.leaf 8))
 (.leaf (.leaf 0)))
 (.branch 27
 (.leaf (.leaf 0))
 (.leaf (.leaf 9))))
 (.leaf (.leaf 0)))))
 (.branch 48
 (.branch 40
 (.branch 36
 (.leaf (.leaf 0))
 (.branch 38
 (.branch 37
 (.leaf (.leaf 10))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 44
 (.branch 42
 (.branch 41
 (.leaf (.leaf 11))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 46
 (.leaf (.leaf 0))
 (.branch 47
 (.leaf (.leaf 12))
 (.leaf (.leaf 0))))))
 (.leaf (.leaf 0))))
 (.branch 96
 (.branch 80
 (.branch 72
 (.branch 68
 (.leaf (.leaf 0))
 (.branch 70
 (.branch 69
 (.leaf (.leaf 13))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
 (.branch 88
 (.branch 84
 (.branch 82
 (.branch 81
 (.leaf (.leaf 14))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 86
 (.branch 85
 (.leaf (.leaf 15))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0))))
 (.branch 112
 (.branch 104
 (.branch 100
 (.branch 98
 (.branch 97
 (.leaf (.leaf 16))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 102
 (.branch 101
 (.leaf (.leaf 17))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
 (.branch 120
 (.leaf (.leaf 0))
 (.branch 124
 (.branch 122
 (.branch 121
 (.leaf (.leaf 18))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))))
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
 (.branch 150
 (.branch 149
 (.leaf (.leaf 29))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 156
 (.branch 154
 (.branch 153
 (.leaf (.leaf 30))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 176
 (.branch 168
 (.branch 164
 (.branch 162
 (.branch 161
 (.leaf (.leaf 31))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 166
 (.branch 165
 (.leaf (.leaf 32))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 172
 (.branch 170
 (.branch 169
 (.leaf (.leaf 33))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0))))
 (.branch 224
 (.branch 208
 (.branch 200
 (.branch 196
 (.branch 194
 (.branch 193
 (.leaf (.leaf 34))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 198
 (.branch 197
 (.leaf (.leaf 35))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
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
 (.branch 278
 (.branch 277
 (.leaf (.leaf 48))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 284
 (.branch 282
 (.branch 281
 (.leaf (.leaf 49))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 304
 (.branch 296
 (.branch 292
 (.branch 290
 (.branch 289
 (.leaf (.leaf 50))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 294
 (.branch 293
 (.leaf (.leaf 51))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 300
 (.branch 298
 (.branch 297
 (.leaf (.leaf 52))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0))))
 (.branch 352
 (.branch 336
 (.branch 328
 (.branch 324
 (.branch 322
 (.branch 321
 (.leaf (.leaf 53))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 326
 (.branch 325
 (.leaf (.leaf 54))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
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
 (.branch 406
 (.branch 405
 (.leaf (.branch 0x1000000000000000000000000000100000000000000000000000000000000001000000000000000000000000000100000 (.leaf 73) (.leaf 74)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 412
 (.branch 410
 (.branch 409
 (.leaf (.branch 0x1000000000000000000000000000100000000000000000000000000000000010000000000000000000000000001000000 (.leaf 75) (.leaf 76)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 432
 (.branch 424
 (.branch 420
 (.branch 418
 (.branch 417
 (.leaf (.leaf 77))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 422
 (.branch 421
 (.leaf (.branch 0x1000000000000000000000001000000000000000000000000000000000000001000000000000000000000001000000000 (.leaf 78) (.leaf 79)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 428
 (.branch 426
 (.branch 425
 (.leaf (.branch 0x1000000000000000000000001000000000000000000000000000000000000010000000000000000000000010000000000 (.leaf 80) (.leaf 81)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0))))
 (.branch 480
 (.branch 464
 (.branch 456
 (.branch 452
 (.branch 450
 (.branch 449
 (.leaf (.leaf 82))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 454
 (.branch 453
 (.leaf (.branch 0x1000000000000000100000000000000000000000000000000000000000000001000000000000000100000000000000000 (.leaf 83) (.leaf 84)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
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
 (.branch 534
 (.branch 533
 (.leaf (.leaf 99))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 540
 (.branch 538
 (.branch 537
 (.leaf (.leaf 100))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 560
 (.branch 552
 (.branch 548
 (.branch 546
 (.branch 545
 (.leaf (.leaf 101))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 550
 (.branch 549
 (.leaf (.leaf 102))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 556
 (.branch 554
 (.branch 553
 (.leaf (.leaf 103))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0))))
 (.branch 608
 (.branch 592
 (.branch 584
 (.branch 580
 (.branch 578
 (.branch 577
 (.leaf (.leaf 104))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 582
 (.branch 581
 (.leaf (.leaf 105))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
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
 (.branch 662
 (.branch 661
 (.leaf (.branch 0x10000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000100000 (.leaf 124) (.leaf 125)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 668
 (.branch 666
 (.branch 665
 (.leaf (.branch 0x10000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000001000000 (.leaf 126) (.leaf 127)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 688
 (.branch 680
 (.branch 676
 (.branch 674
 (.branch 673
 (.leaf (.leaf 128))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 678
 (.branch 677
 (.leaf (.branch 0x10000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000001000000000 (.leaf 129) (.leaf 130)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 684
 (.branch 682
 (.branch 681
 (.leaf (.branch 0x10000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000010000000000 (.leaf 131) (.leaf 132)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0))))
 (.branch 736
 (.branch 720
 (.branch 712
 (.branch 708
 (.branch 706
 (.branch 705
 (.leaf (.leaf 133))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 710
 (.branch 709
 (.leaf (.branch 0x10000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000100000000000000000 (.leaf 134) (.leaf 135)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
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
 (.branch 790
 (.branch 789
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000100000 (.leaf 156) (.leaf 157)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 796
 (.branch 794
 (.branch 793
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000001000000 (.leaf 158) (.leaf 159)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 816
 (.branch 808
 (.branch 804
 (.branch 802
 (.branch 801
 (.leaf (.leaf 160))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 806
 (.branch 805
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000001000000000 (.leaf 161) (.leaf 162)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 812
 (.branch 810
 (.branch 809
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000010000000000 (.leaf 163) (.leaf 164)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0))))
 (.branch 864
 (.branch 848
 (.branch 840
 (.branch 836
 (.branch 834
 (.branch 833
 (.leaf (.leaf 165))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 838
 (.branch 837
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000100000000000000000 (.leaf 166) (.leaf 167)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
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

end Papers.RationalityTen.RootedCaches.RootedSevenPure059

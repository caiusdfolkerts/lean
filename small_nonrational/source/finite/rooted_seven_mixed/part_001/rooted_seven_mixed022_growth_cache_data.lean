module
prelude
public import RootedSevenMixed022
public import SignatureCompatibility
public import PackedRawNatGrowth
public import FiniteChecks
public import RawFacetEmbedding
public import RootedSevenMixed022GrowthCachecandidateMasksData000
public import RootedSevenMixed022GrowthCachebadMasksData000
public import RootedSevenMixed022GrowthCachesignatureMasksData000

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenMixed022
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def rawCells := Papers.RationalityTen.FacetUniverses.RootedSevenMixed022.rawCells
def cells (c : Fin 556) := rawCells c.val
def ridgeList := ConcreteGrowth.ridgeList cells
def literalCompatible (a b : Fin 556) := ConcreteGrowth.compatible (cells a) (cells b)
def kind (c : Fin 556) := (cells c).kind
def rawKindCode : Nat := 7498850904243570169787243962217458379325984366651666341510177083605883086760363045704266961050950714751410458433117145587946101835850263864406492369641185989778366288870007447811905817305057207618250441954558188653761296376733146509760088353422863509015962971263965178432776886749801072584105132780226372293729978855910004866663063900547663628825394315103719676322662635118461373488133814483807643018416664192734882744294283004138523801529993886828692618965851888717350819630737124396085495352273740944
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
 (.leaf 0x1f57d1f37c9f17c02408c220842007c1e0741c06c1a0641805c160541404c120441003c0e0340c02c0a0240801c060140400c0200400002b))))
 (.branch 12
 (.leaf 0x0)
 (.branch 14
 (.leaf 0x0)
 (.branch 15
 (.leaf 0x1fb7e9f97e1f77d8ae2b4ac2acaa2a4a829ca6294a428ca2284a027c9e2749c26c9a2649825c962549424c922449023c8e2348c22c00002b)
 (.leaf 0x0)))))
 (.branch 24
 (.branch 20
 (.leaf 0x0)
 (.branch 22
 (.branch 21
 (.leaf 0x0)
 (.leaf 0x201801ff7f9fd7f06017c5e1745c16c5a1645815c561545414c521445013c4e1344c12c4a1244811c461144410c42104400fc3e0f400002b))
 (.leaf 0x0)))
 (.branch 28
 (.branch 26
 (.leaf 0x0)
 (.branch 27
 (.leaf 0x0)
 (.leaf 0x8360c82e0a8260881e068160480e0209c26094000010)))
 (.leaf 0x0))))
 (.branch 48
 (.leaf 0x0)
 (.branch 56
 (.leaf 0x0)
 (.branch 60
 (.branch 58
 (.branch 57
 (.leaf 0x21384a118420f839625856057d5e5755c56d5a5655855d565555454d525455053d4e5354c52d4a5254851d465154450d42505404fc00002b)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))))
 (.branch 96
 (.branch 80
 (.leaf 0x0)
 (.branch 88
 (.branch 84
 (.leaf 0x0)
 (.branch 86
 (.branch 85
 (.leaf 0x2198621785a158511444d124451043d0e4350c42d0a4250841d064150440d02405003fcfe3f4fc3ecfa3e4f83dcf63d4f43ccf23c400002b)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 112
 (.branch 104
 (.leaf 0x0)
 (.branch 108
 (.leaf 0x0)
 (.branch 110
 (.branch 109
 (.leaf 0x8962488e228862087e1e8761c86e1a36cda364000010)
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 120
 (.branch 116
 (.branch 114
 (.branch 113
 (.leaf 0x22b8aa298a227899b06bdae6b5ac6adaa6a5a869da6695a468da2685a067d9e6759c66d9a6659865d966559464d926459063d8e63400002b)
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
 (.leaf 0x206808380dc350d0320c42f0b82d0b02a0a42505814044100380a02005010020019)))
 (.branch 134
 (.branch 133
 (.leaf 0x0)
 (.leaf 0x1c4701b86d1ac6a1a0671986518c62148501344c12846110411003e060130480f0380c01c0600c020020))
 (.branch 135
 (.leaf 0x2fcbe2f0bb2e4b82d8b52d0b32c4b02809e26c9a260942488f2388c05c15048100340b02406010010020)
 (.leaf 0x0))))
 (.branch 140
 (.branch 138
 (.leaf 0x0)
 (.branch 139
 (.leaf 0x209814d434cd1340ce334cb328c9320c6314a22749c26498258912408d230250019)
 (.leaf 0x0)))
 (.branch 142
 (.branch 141
 (.leaf 0x21e868ec3ace93a0e6394e3388e1380de374d92849f2709a25c9524c902388b0019)
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 152
 (.branch 148
 (.branch 146
 (.branch 145
 (.leaf 0x0)
 (.leaf 0x2088108621483208801fc7d1f07b1e8781dc5413c4e12c4a120431083f0f8250019))
 (.leaf 0x0))
 (.branch 150
 (.branch 149
 (.leaf 0x495244892147d1e4711b4691945d1641904405003f8fa3e0f53d0f214c511384c12447114421003d0020)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 156
 (.branch 154
 (.branch 153
 (.leaf 0x20780d735c9705bd6d5b16a5a56859d65591545494f5394c5214650d42500250019)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 176
 (.branch 168
 (.leaf 0x0)
 (.branch 172
 (.branch 170
 (.branch 169
 (.leaf 0x2218758861d85611826057f5f97d5f17a5e556545505354c5294551141500d90019)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 184
 (.branch 180
 (.branch 178
 (.branch 177
 (.leaf 0x705c06f9bd6edba6e1b76d9b56cdb2689a06759c66996651916418e555535414e52d4951d445093f0020)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 224
 (.branch 208
 (.branch 200
 (.branch 196
 (.leaf 0x0)
 (.branch 198
 (.branch 197
 (.leaf 0x2208713a4e5374d9344cd314c12f4b92c4ad0840d023fcfe3f0f73d8f33c8d90019)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 216
 (.branch 212
 (.branch 210
 (.branch 209
 (.leaf 0x759d574dd2741cf735cc72dca721c76919f6799b6699864d9263d8e41d05409003f4fb3e4f63d0f10020)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 240
 (.branch 232
 (.branch 228
 (.branch 226
 (.branch 225
 (.leaf 0x21f86deb7a9e879de5791e2785e077ddd771a36859e6719965d9564990634d90019)
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
 (.leaf 0x20a80c3a0e4360d4330c8300b82d0ac2a0a026088200741c0680901c0600c010019)))
 (.branch 262
 (.branch 261
 (.leaf 0x0)
 (.leaf 0x1cc721bc6e1b06b1a4671986418c611785c164581584510c420fc3d0901f0781b0680b02005010010020))
 (.branch 263
 (.leaf 0x304c02f4bc2e8b92dcb52d0b22c4af2b0aa29ca629093244902348b08c210781c0640c0280500c020020)
 (.leaf 0x0))))
 (.branch 268
 (.branch 266
 (.leaf 0x0)
 (.branch 267
 (.leaf 0x20d810d6354d2344cf338cc328c931cc6310ae2a4a8294a42549223c8e22c260019)
 (.leaf 0x0)))
 (.branch 270
 (.branch 269
 (.leaf 0x22286cee3b4ea3a4e7398e4388e137cde370da2b4ab2a0a628c962508f2348c0019)
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 280
 (.branch 276
 (.branch 274
 (.branch 273
 (.leaf 0x0)
 (.leaf 0x20c8148821c8420c812007e1f07b1e4781d86016c5a15c5611c44104400f4260019))
 (.leaf 0x0))
 (.branch 278
 (.branch 277
 (.leaf 0x49d2648d224811f4751b4691845d15449104350c428f93dcf63ccf117c5d1685815448118410fc3e0020)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 284
 (.branch 282
 (.branch 281
 (.leaf 0x20b809755d1715c16e5b56b5a5685996558d605795b5695851d45511414fc260019)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 304
 (.branch 296
 (.leaf 0x0)
 (.branch 300
 (.branch 298
 (.branch 297
 (.leaf 0x2258718a6258661583609805f97d5ed7a5e1625755c565585254650d424fcda0019)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 312
 (.branch 308
 (.branch 306
 (.branch 305
 (.leaf 0x70dc26fdbe6f1bb6e5b76d9b46cdb16b9ac6a5a86999564d9263d8d5855f5715a55d4a52143505400020)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 352
 (.branch 336
 (.branch 328
 (.branch 324
 (.leaf 0x0)
 (.branch 326
 (.branch 325
 (.leaf 0x2248753c4ed384dd354d1324c12f4b52c4a91443d0e42d0a3ecf83d4f43c4da0019)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 344
 (.branch 340
 (.branch 338
 (.branch 337
 (.leaf 0x761d7751d3745d0739cc72dc9721c66c1ab6a9a769997651916418d44d114390c424fc3e8f53ccf20020)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 368
 (.branch 360
 (.branch 356
 (.branch 354
 (.branch 353
 (.leaf 0x223869ed7b1e97a1e6795e3785e0779dd76daf6b5aa6a1a5661966458f638da0019)
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
 (.leaf 0x88218811fc7e1f47a1e4781cc711b06a1a4681946418c4410c42104400fc3a0e0330c4300bc2c0ac2a0200701805010030027))
 (.branch 387
 (.leaf 0xd6350cf334cc32cc831cc6304bf2e8b82dcb62ccb22c4922449023c8e234390dc360d0300bc2d0a4280280901805008010027)
 (.leaf 0x816047c9f00f03b0300b0008)))
 (.branch 390
 (.branch 389
 (.leaf 0x13c4e9354cd324c52e4b52c49d254811e4751c4651845cf83dcf63d4f43ccee3b0e7394e438ce037cde300be2f4bb2dcb62d0b02bc9424c9023c8c22c721c06f1b4691a0661886111845108410f83d0300b01003008010045)
 (.leaf 0x7f9fc7d5f41d4741204702809000a))
 (.branch 391
 (.leaf 0x7e1f67cdf130cc22589502007000a)
 (.leaf 0x0))))
 (.branch 396
 (.branch 394
 (.branch 393
 (.leaf 0x6298860d816017f5f17b5e9755cd6e5b16b5a967599655194551143509413b4eb3a8e8390e3384dd370d534cd2340cc32cc9314c4258952388d2308b0030)
 (.leaf 0x0))
 (.branch 395
 (.leaf 0x80e027edfa360d7250930008)
 (.leaf 0x0)))
 (.branch 398
 (.branch 397
 (.leaf 0x8761c7e5f73c0ef248910008)
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 408
 (.branch 404
 (.branch 402
 (.branch 401
 (.leaf 0x1d8759d173dce735ca725c870dc16f1ba6e5b86d5b46cd9464d926459063d745c9715bd6b5a9685916352147511435013f4992448d214751c46916454fa3e4f63d4f23c487214842087e1f47b1dc76120471003f0f83d0045)
 (.leaf 0x80e028060022889118450008))
 (.leaf 0x0))
 (.branch 406
 (.branch 405
 (.leaf 0x85a147fdfd4a5283f0fb11043000a)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 412
 (.branch 410
 (.branch 409
 (.leaf 0x8420e816045dd76529490008)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 432
 (.branch 424
 (.branch 420
 (.branch 418
 (.branch 417
 (.leaf 0x1ed7ade6791e3789df779dd709c06fdbd6e5b86d9b26c596655926458e6358961d86611805fd7d5e57852949509415013f0027)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 428
 (.branch 426
 (.branch 425
 (.leaf 0x86e1a84e126318b521470008)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 440
 (.branch 436
 (.branch 434
 (.branch 433
 (.leaf 0x8a2268460f715c46619751945000a)
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
 (.leaf 0x1ec7a9e979de3789e0771db75dd5751d2739cd72dc77199865d9063d8e6353b4e5384d9324c52f4ad2a3f0fb3d0f33c8f10027)
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 454
 (.branch 453
 (.leaf 0x86e1a866184f93d3e8f90008)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 472
 (.branch 468
 (.branch 466
 (.branch 465
 (.leaf 0x8ae2a85e15769d9659953e0f7000a)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 496
 (.branch 488
 (.branch 484
 (.branch 482
 (.branch 481
 (.leaf 0x8a6278761c7bdee651930008)
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
 (.leaf 0x20b81c3c0ec360d0330c4300bc2c0ac290a0270841f0781b0641504c1203c0d0019)))
 (.branch 518
 (.branch 517
 (.leaf 0x0)
 (.leaf 0x1d4741bc6d1b06a1a46819464188611745b168571545113c4e12c4908c200741c06417050110400d0020))
 (.branch 519
 (.leaf 0x30cc22f4bb2e8b82dcb62ccb22c0af2aca92a0a528c9f2749c26497090220741b068180581103c0e0020)
 (.leaf 0x0))))
 (.branch 524
 (.branch 522
 (.leaf 0x0)
 (.branch 523
 (.leaf 0x20c820d835cd2340cf334cc32cc831cc5310ad2a8a7298a32849e26c9a25c270019)
 (.leaf 0x0)))
 (.branch 526
 (.branch 525
 (.leaf 0x22387cf03bcea3a0e7394e438ce037cdd370db2b8ac29ca5290a22809b264980019)
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 536
 (.branch 532
 (.branch 530
 (.branch 529
 (.leaf 0x0)
 (.leaf 0x20d8248a22484208811fc7e1f47a1e4771d85f170591605514c501344c124270019))
 (.leaf 0x0))
 (.branch 534
 (.branch 533
 (.leaf 0x4a52848d214811e4751c46518459154450f4390b4250540d023fcfd1805e16457158541484d12c4a0020)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 540
 (.branch 538
 (.branch 537
 (.leaf 0x20a819775d9715bd6e5b16b5a9675996458d5f5755c5655754d515414d52c270019)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 560
 (.branch 552
 (.leaf 0x0)
 (.branch 556
 (.branch 554
 (.branch 553
 (.leaf 0x2248818c62d8661183605805fd7c5ed795e1615795b569575555253d4e52cdb0019)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 568
 (.branch 564
 (.branch 562
 (.branch 561
 (.leaf 0x715c46fdbd6f1ba6e5b86d5b46c9b16b5ab6a9a7695a167d9e66d995896056d59561565514f5354c0020)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 608
 (.branch 592
 (.branch 584
 (.branch 580
 (.leaf 0x0)
 (.branch 582
 (.branch 581
 (.leaf 0x2258853e4f5384d9354cd324c52e4b52b4a9134410d4310941d04405003f4db0019)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 600
 (.branch 596
 (.branch 594
 (.branch 593
 (.leaf 0x769d9751d2745cf739cd729c971dc66bdac6a5a8695a36819d67199451124350b42908419013fcfe0020)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 624
 (.branch 616
 (.branch 612
 (.branch 610
 (.branch 609
 (.leaf 0x222879ef7b9e979de6791e3789df779dc76db06b9a969da6691a26759b668db0019)
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
 (.leaf 0x8a214812007e1f07b1e4771d4701b06b1a467198641885013c4e1344c12c3c0dc330c8300b82d0ac2905013048110400f0027))
 (.branch 643
 (.leaf 0xd834ccf338cc328c931cc530cbe2e8b92dcb52d0b22c09e2749c26c9a2643b0e0360d4300b82c0a82805815048110380d0027)
 (.leaf 0x826087d1f10e839060170008)))
 (.branch 646
 (.branch 645
 (.leaf 0x13e4e5354d1324c12f4b52b4a5244811f4751b469184590440d02405003fcf03ace7398e4388e137cdd308bf2f4bc2dcb52ccb12bca027c9c26c9825c741c46f1b86919c6518c61148511384d12849060170400f0380d0045)
 (.leaf 0x801fd7cdf21cc721505305815000a))
 (.branch 647
 (.leaf 0x7e9f77d5f0304c0288a105013000a)
 (.leaf 0x0))))
 (.branch 652
 (.branch 650
 (.branch 649
 (.leaf 0x6318760d826017e5f57b5e5775c96e5b56b5a56859964549515414f5394d3bcec3a8e9390e2380de370d7350d2344cc328c8318c4288a126899260970030)
 (.leaf 0x0))
 (.branch 651
 (.leaf 0x81e067e5f8358d52809f0008)
 (.leaf 0x0)))
 (.branch 654
 (.branch 653
 (.leaf 0x886207edf63b8ed2789d0008)
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 664
 (.branch 660
 (.branch 658
 (.branch 657
 (.leaf 0x1da755d1741ce731cb725c7715c06f1bb6e5b76d9b46c9a067d9e6759c66d765cd715c16b5a56759563551535414f5314b4a12548d224751b465174550641502404fe3f4892188420c7e1f07a1e076150531304b128490045)
 (.leaf 0x81e067fdfe22087148510008))
 (.leaf 0x0))
 (.branch 662
 (.branch 661
 (.leaf 0x86215805fc49d26421071404f000a)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 668
 (.branch 666
 (.branch 665
 (.leaf 0x84a0f826085d574559550008)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 688
 (.branch 680
 (.branch 676
 (.branch 674
 (.branch 673
 (.leaf 0x1ef7a9e6795e3785e0779dc711c16fdbe6e5b76d5b36c5a26859e6759a6658b62186615805f97c5e978559555394d5314b0027)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 684
 (.branch 682
 (.branch 681
 (.leaf 0x87e1e8461062989551530008)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 696
 (.branch 692
 (.branch 690
 (.branch 689
 (.leaf 0x8aa2784e0e70dc2691a354951000a)
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
 (.leaf 0x1ee7ade97a1e3785df775db765d6751d3739cc729c8719a468d9c66d9a6653d4e9384dd324c12e4b12a42107400ff3f8fd0027)
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 710
 (.branch 709
 (.leaf 0x87e1e85e164f13b419050008)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 728
 (.branch 724
 (.branch 722
 (.branch 721
 (.leaf 0x8a62886614761d7689a141103000a)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 752
 (.branch 744
 (.branch 740
 (.branch 738
 (.branch 737
 (.leaf 0x8ae26886207b5ec6819f0008)
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
 (.leaf 0x8921c801fc7d1f07b1e8761d0721ac6a1a067198651845c16c5a1645815c3b0e4320c42f0b82d0b0280801f0781d0701b0027))
 (.branch 771
 (.leaf 0xd7354ce334cb328c9320c4308c02e4b82d8b52d0b32bcaa2a4a829ca62943c0e8350d02f0b82b0a829088210781d068190027)
 (.leaf 0x8360c7d5f30e037090230008)))
 (.branch 774
 (.branch 773
 (.leaf 0x13d4ed344cd314c12f4b92a4a12647d1e4711b469194551043d0e4350c42cef3b4e6394e3388e1380dc30cc12f0bb2d8b52c8b12c0ac2aca829ca428c751cc6e1b46819c6418c621785d1685915855090230701b068190045)
 (.leaf 0x805ff7c5f01c4701805f08821000a))
 (.branch 775
 (.leaf 0x7edf97d1f22fcbe2b8ad0801f000a)
 (.leaf 0x0))))
 (.branch 780
 (.branch 778
 (.branch 777
 (.leaf 0x62d89609815fd7e5f57c5e1765d16d5b16a5a56859d635795d5715b569593c0ee3a4e838ce237cde374d8358d1340cb328c7318c52b8ad298a5290a30030)
 (.leaf 0x0))
 (.branch 779
 (.leaf 0x82e0a7ddf6350d32b0ab0008)
 (.leaf 0x0)))
 (.branch 782
 (.branch 781
 (.leaf 0x896247e9f83b0eb2a8a90008)
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 792
 (.branch 788
 (.branch 786
 (.branch 785
 (.leaf 0x1d975dd073dcd731cb729c6711c26edba6e1b76d9b56c5ac6adaa6a5a869d775d5705bd6a5a566595645815f5715b561574a527489214711b46117459124450e4350a4248a220832087d1f0791e0771805f16057158550045)
 (.leaf 0x82e0a7f5fc218851785d0008))
 (.leaf 0x0))
 (.branch 790
 (.branch 789
 (.leaf 0x86617801fe49524451131705b000a)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 796
 (.branch 794
 (.branch 793
 (.leaf 0x84e118360c5cd72589610008)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 816
 (.branch 808
 (.branch 804
 (.branch 802
 (.branch 801
 (.leaf 0x1ee7b1e5791e2785e077ddb715c36f9bd6e1b76d1b36c9ae6b5aa6a5a66958c629856117f5f97b5e9795896156959561570027)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 812
 (.branch 810
 (.branch 809
 (.leaf 0x88e2283e0e621875815f0008)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 824
 (.branch 820
 (.branch 818
 (.branch 817
 (.leaf 0x8ae2984a10705c06c1af5795d000a)
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
 (.leaf 0x1ef7b5e879de2785de775dc769d874dd2735cc725c871db06bda869da66953e4f1374d9314c12d4b12b451134310b429090027)
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 838
 (.branch 837
 (.leaf 0x88e22856144e939449110008)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 856
 (.branch 852
 (.branch 850
 (.branch 849
 (.leaf 0x89e2686216759d56b9ad4410f000a)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 880
 (.branch 872
 (.branch 868
 (.branch 866
 (.branch 865
 (.leaf 0x8aa28896247adea6b1ab0008)
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
 (.leaf 0x8ae2a8a62889e268661885e168561484e128461083e0e806007fdfe7f5fc7edfa7e5f87ddf67d5f47cdf27c5f07bdee7b5ec7adea781df779dd771db769d9761d7759d572dca725c871dc6715c470dc2705c06d9b56d1b36c9b16318b62989621875f57c5ed7a5e5785dd765d5745cd725a16759965591634f93d4f13b4e9394bd2e4b52c4ad2a4a52849d26495244691946117459153c0ef3b8ed3b0eb384e037cde374dc360d7358d5350d3324c831cc6314c430cc2304c02fcbe2d0b32c8b12c0af2288922087218851ec7a1e4781dc761d4741cc721c4701986519063188610f03b0e8390e0370b42c0ac2a0a42800c0)
 (.leaf 0x8420c821bc6e1b4360d4340009))
 (.branch 899
 (.leaf 0xd2344d02f4bc2ec330c8310009)
 (.leaf 0x0)))
 (.branch 902
 (.branch 901
 (.leaf 0x1384dd3648d22484ea3a4e82e8b92e06c1ac6a000f)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 908
 (.branch 906
 (.branch 905
 (.leaf 0x61985611715c16f39ce6394cf338cd000c)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 920
 (.branch 916
 (.branch 914
 (.branch 913
 (.leaf 0x1d474dd26fdbe6f56e5b56c4811f478812007f000f)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 944
 (.branch 936
 (.branch 932
 (.branch 930
 (.branch 929
 (.leaf 0x1e97a1e76f1bb6e983609810009)
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
 (.leaf 0x1e6795e4745d073d354d1330009)
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
 (.leaf 0x1e3789e1781df779dd771db739cd731cb729c9721c7719b96e1b76d9b56d1b36c9b16a9a96a1a7699a56799d6719b66999649916418f6398d6017f5f97d5f17b5e9795e16b5a9695a16759965591635715b56959561575414f5394d5314b51143509415013f4c9314c12f4b92d4b12b4a91d4711b4691946117459154390d4310b4290940901400ff3f8fd3d8f53d0f33c8f1390e3388e1380df378dd370cc32cca324c831cc6314c42dcb62d4b42ccb22c4b02bca829ca6294a428c9c26c9a2649825c9023c8e2348c22c7e1f47c1ec7a1e4781dc761a46819c661946418c621845a1645815c561544e1344c12c4a12442104400fc3e0f4300bc2e0b42c0ac2a0a4280781d0701b06819048110400f0380d01805010030080100e1)
 (.branch 4
 (.leaf 0x7bdee7b5ec7adea7a5e879de6795e4769d9761d7759d5751d3749d1741cf715c470dc2705c06fdbe6f5bc6edba6c1af6b9ad6b1ab691a3689a16819f6619765995651936318b62989621876198561183609815dd765d5745cd725c5705bd6e5b56c589615815f5795d5595555153549515294952147519454f93d4f13b4e9394e1374d9354d1334a52849d264952448d224852047d1e45113449114410f4210741905411033f0fb3e8f93e0f73c0ef3b8ed3b0eb3a8e93a0e7398e536cda364d835cd6354d434cd2344d033cce334c3308c1300bf2f8bd2f0bb2e8b92e0ae2b4ac2acaa2a4a2284a027c9e274962549424c922448a2248821c862148420c82204801fc751d0731c8711c06f1b86d1b06b1a86017c5e1745c16c5414c521445013c4811c461144410c3c0ec3a0e4380dc360d4340cc320c4270982509023088210801f0601705815050130300b0280902007010e)
 (.leaf 0x8ae2a8a62889e268962488e228862087e1e8761c86e1a8661885e168561484e128461083e0e8360c82e0a8260881e068160480e02806007fdfe7f5fc7edfa7e5f87ddf67d5f47cdf27c5f0003c))))
def decodeRow (table : Table Nat) (i : Nat) : List Nat :=
  let code := table.get i
  (PackedRawNatGrowth.readList 10 (PackedRawNatGrowth.take 16 code)
    (PackedRawNatGrowth.drop 16 code)).1
def candidateRows := decodeRow candidateRowTable
def kindRows := decodeRow kindRowTable
def kindMaskTable : Table Nat :=
(.branch 2
 (.branch 1
 (.leaf 0x1)
 (.leaf 0x0))
 (.branch 3
 (.leaf 0xff8007fc003fe07e07e07e001ff000ff81f81f81f8007fc003fe07e07e07e001ff0001ff000ff81f81f81f8007fc003fe07e07e07e001ff007e07e07e)
 (.branch 4
 (.leaf 0xfff007ff803ffc01f81f81f81ffe00fff007e07e07e07ff803ffc01f81f81f81ffe00fffe00fff007e07e07e07ff803ffc01f81f81f81ffe00ff81f81f80)
 (.leaf 0xfffffffffffffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))))
def kindMasks := kindMaskTable.get
def keys := List.range 5
def vertexMaskTable : Table Nat :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf 219672700025159408058160715370976626345910623997250042370604331561806911136999937414641918236898898861056870119152570250975792309248177677756678420954993393663)
 (.leaf 219620731675868448909832385971349791381770032588127062674006494828047016916848216801408591441123757389995057015551195768859215932557099046077575802246225985535))
 (.branch 3
 (.leaf 3685496121437809556442554257452949044261214244294405862088902221041798905156337775532736493180064217072006278278659464151903580385878755052426912778091459818452680703)
 (.branch 4
 (.leaf 3684624456783679447723946760080602884918368078491986781273094106353303762719119857623460885598187321992644119889447732596324184455222760866254471982563265885847420929)
 (.leaf 232188041153614618689579806416295460538088137145345939546239865701447209187169201633428555323861633278536288443349652051616007949674697477556249468222362596519972962305))))
 (.branch 7
 (.branch 6
 (.leaf 235871765608019508903716600046490466613446572569592104025973871164963321800819314395322463992898091125153052887696620610286523707803449965637368979654002015362009268225)
 (.leaf 235872637492240726772195378022296318383265062071597560011725160812420942832122714627552783043920279782824809201939024396062927163504888109252574013958906650101368750081))
 (.branch 8
 (.leaf 232417485551193229889180376288406947620077910188618406634887578446772696199988144895152640555170560876877802223383996937328733704050111765256235970074453791478562947070)
 (.branch 9
 (.leaf 235656703676336765475977362247806814554798804483584451451329943650965151128875116073772671298585948275801939565600742274370180094977099280204688524281062777561309782014)
 (.leaf 235859154809158236450152173870269306236838615095234702728641713565842261347646231714055693857064603591565060894977361414367185073562936443503384245383727170606747082752)))))
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
 (.branch 14
 (.branch 13
 (.leaf (.leaf 5))
 (.leaf (.leaf 0)))
 (.branch 15
 (.leaf (.leaf 6))
 (.leaf (.leaf 0))))))
 (.branch 24
 (.branch 20
 (.branch 18
 (.branch 17
 (.leaf (.leaf 0))
 (.leaf (.leaf 7)))
 (.leaf (.leaf 0)))
 (.branch 22
 (.branch 21
 (.leaf (.leaf 8))
 (.leaf (.leaf 9)))
 (.leaf (.leaf 0))))
 (.branch 28
 (.branch 26
 (.branch 25
 (.leaf (.leaf 10))
 (.leaf (.leaf 0)))
 (.branch 27
 (.leaf (.leaf 0))
 (.leaf (.leaf 11))))
 (.leaf (.leaf 0)))))
 (.branch 48
 (.branch 40
 (.leaf (.leaf 0))
 (.branch 44
 (.branch 42
 (.branch 41
 (.leaf (.leaf 12))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 56
 (.branch 52
 (.branch 50
 (.branch 49
 (.leaf (.leaf 13))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 60
 (.branch 58
 (.branch 57
 (.leaf (.leaf 14))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))))
 (.branch 96
 (.branch 80
 (.branch 72
 (.branch 68
 (.leaf (.leaf 0))
 (.branch 70
 (.branch 69
 (.leaf (.leaf 15))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
 (.branch 88
 (.branch 84
 (.branch 82
 (.branch 81
 (.leaf (.leaf 16))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 86
 (.branch 85
 (.leaf (.leaf 17))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0))))
 (.branch 112
 (.branch 104
 (.branch 100
 (.branch 98
 (.branch 97
 (.leaf (.leaf 18))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 108
 (.leaf (.leaf 0))
 (.branch 110
 (.branch 109
 (.leaf (.leaf 19))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 120
 (.branch 116
 (.branch 114
 (.branch 113
 (.leaf (.leaf 20))
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
 (.leaf (.leaf 21)))
 (.branch 131
 (.leaf (.leaf 22))
 (.leaf (.leaf 23))))
 (.branch 134
 (.branch 133
 (.leaf (.leaf 24))
 (.leaf (.leaf 25)))
 (.branch 135
 (.leaf (.leaf 26))
 (.leaf (.leaf 0)))))
 (.branch 140
 (.branch 138
 (.branch 137
 (.leaf (.leaf 27))
 (.leaf (.leaf 0)))
 (.branch 139
 (.leaf (.leaf 28))
 (.leaf (.leaf 0))))
 (.branch 142
 (.branch 141
 (.leaf (.leaf 29))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 152
 (.branch 148
 (.branch 146
 (.branch 145
 (.leaf (.leaf 30))
 (.leaf (.leaf 31)))
 (.leaf (.leaf 0)))
 (.branch 150
 (.branch 149
 (.leaf (.leaf 32))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 156
 (.branch 154
 (.branch 153
 (.leaf (.leaf 33))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 176
 (.branch 168
 (.branch 164
 (.branch 162
 (.branch 161
 (.leaf (.leaf 34))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 172
 (.branch 170
 (.branch 169
 (.leaf (.leaf 35))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 184
 (.branch 180
 (.branch 178
 (.branch 177
 (.leaf (.leaf 36))
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
 (.leaf (.leaf 37))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 198
 (.branch 197
 (.leaf (.leaf 38))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
 (.branch 216
 (.branch 212
 (.branch 210
 (.branch 209
 (.leaf (.leaf 39))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 240
 (.branch 232
 (.branch 228
 (.branch 226
 (.branch 225
 (.leaf (.leaf 40))
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
 (.leaf (.leaf 41)))
 (.branch 259
 (.leaf (.leaf 42))
 (.leaf (.leaf 43))))
 (.branch 262
 (.branch 261
 (.leaf (.leaf 44))
 (.leaf (.leaf 45)))
 (.branch 263
 (.leaf (.leaf 46))
 (.leaf (.leaf 0)))))
 (.branch 268
 (.branch 266
 (.branch 265
 (.leaf (.leaf 47))
 (.leaf (.leaf 0)))
 (.branch 267
 (.leaf (.leaf 48))
 (.leaf (.leaf 0))))
 (.branch 270
 (.branch 269
 (.leaf (.leaf 49))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 280
 (.branch 276
 (.branch 274
 (.branch 273
 (.leaf (.leaf 50))
 (.leaf (.leaf 51)))
 (.leaf (.leaf 0)))
 (.branch 278
 (.branch 277
 (.leaf (.leaf 52))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 284
 (.branch 282
 (.branch 281
 (.leaf (.leaf 53))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 304
 (.branch 296
 (.branch 292
 (.branch 290
 (.branch 289
 (.leaf (.leaf 54))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 300
 (.branch 298
 (.branch 297
 (.leaf (.leaf 55))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 312
 (.branch 308
 (.branch 306
 (.branch 305
 (.leaf (.leaf 56))
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
 (.leaf (.leaf 57))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 326
 (.branch 325
 (.leaf (.leaf 58))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
 (.branch 344
 (.branch 340
 (.branch 338
 (.branch 337
 (.leaf (.leaf 59))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 368
 (.branch 360
 (.branch 356
 (.branch 354
 (.branch 353
 (.leaf (.leaf 60))
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
 (.leaf (.leaf 61))
 (.leaf (.leaf 62)))
 (.branch 387
 (.leaf (.leaf 63))
 (.leaf (.branch 0x1000000000000000000000000000000040000000000000000000000000000000200000000000000000000000000000008 (.leaf 64) (.leaf 65)))))
 (.branch 390
 (.branch 389
 (.leaf (.leaf 66))
 (.leaf (.branch 0x1000000000000000000000000000000100000000000000000000000000000000200000000000000000000000000000020 (.leaf 67) (.leaf 68))))
 (.branch 391
 (.leaf (.branch 0x1000000000000000000000000000000100000000000000000000000000000000400000000000000000000000000000040 (.leaf 69) (.leaf 70)))
 (.leaf (.leaf 0)))))
 (.branch 396
 (.branch 394
 (.branch 393
 (.leaf (.leaf 71))
 (.leaf (.leaf 0)))
 (.branch 395
 (.leaf (.branch 0x1000000000000000000000000000001000000000000000000000000000000000400000000000000000000000000000400 (.leaf 72) (.leaf 73)))
 (.leaf (.leaf 0))))
 (.branch 398
 (.branch 397
 (.leaf (.branch 0x1000000000000000000000000000001000000000000000000000000000000001000000000000000000000000000001000 (.leaf 74) (.leaf 75)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 408
 (.branch 404
 (.branch 402
 (.branch 401
 (.leaf (.leaf 76))
 (.leaf (.branch 0x1000000000000000000000000000100000000000000000000000000000000000200000000000000000000000000020000 (.leaf 77) (.leaf 78))))
 (.leaf (.leaf 0)))
 (.branch 406
 (.branch 405
 (.leaf (.branch 0x1000000000000000000000000000100000000000000000000000000000000001000000000000000000000000000100000 (.leaf 79) (.leaf 80)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 412
 (.branch 410
 (.branch 409
 (.leaf (.branch 0x1000000000000000000000000000100000000000000000000000000000000010000000000000000000000000001000000 (.leaf 81) (.leaf 82)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 432
 (.branch 424
 (.branch 420
 (.branch 418
 (.branch 417
 (.leaf (.leaf 83))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 428
 (.branch 426
 (.branch 425
 (.leaf (.branch 0x1000000000000000000000001000000000000000000000000000000000000010000000000000000000000010000000000 (.leaf 84) (.leaf 85)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 440
 (.branch 436
 (.branch 434
 (.branch 433
 (.leaf (.branch 0x1000000000000000000000001000000000000000000000000000000000001000000000000000000000001000000000000 (.leaf 86) (.leaf 87)))
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
 (.leaf (.leaf 88))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 454
 (.branch 453
 (.leaf (.branch 0x1000000000000000100000000000000000000000000000000000000000000001000000000000000100000000000000000 (.leaf 89) (.leaf 90)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
 (.branch 472
 (.branch 468
 (.branch 466
 (.branch 465
 (.leaf (.branch 0x1000000000000000100000000000000000000000000000000000000000001000000000000000100000000000000000000 (.leaf 91) (.leaf 92)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 496
 (.branch 488
 (.branch 484
 (.branch 482
 (.branch 481
 (.leaf (.branch 0x1000000000000000100000000000000000000000000000000000000010000000000000001000000000000000000000000 (.leaf 93) (.leaf 94)))
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
 (.leaf (.leaf 95)))
 (.branch 515
 (.leaf (.leaf 96))
 (.leaf (.leaf 97))))
 (.branch 518
 (.branch 517
 (.leaf (.leaf 98))
 (.leaf (.leaf 99)))
 (.branch 519
 (.leaf (.leaf 100))
 (.leaf (.leaf 0)))))
 (.branch 524
 (.branch 522
 (.branch 521
 (.leaf (.leaf 101))
 (.leaf (.leaf 0)))
 (.branch 523
 (.leaf (.leaf 102))
 (.leaf (.leaf 0))))
 (.branch 526
 (.branch 525
 (.leaf (.leaf 103))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 536
 (.branch 532
 (.branch 530
 (.branch 529
 (.leaf (.leaf 104))
 (.leaf (.leaf 105)))
 (.leaf (.leaf 0)))
 (.branch 534
 (.branch 533
 (.leaf (.leaf 106))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 540
 (.branch 538
 (.branch 537
 (.leaf (.leaf 107))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 560
 (.branch 552
 (.branch 548
 (.branch 546
 (.branch 545
 (.leaf (.leaf 108))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 556
 (.branch 554
 (.branch 553
 (.leaf (.leaf 109))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 568
 (.branch 564
 (.branch 562
 (.branch 561
 (.leaf (.leaf 110))
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
 (.leaf (.leaf 111))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 582
 (.branch 581
 (.leaf (.leaf 112))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
 (.branch 600
 (.branch 596
 (.branch 594
 (.branch 593
 (.leaf (.leaf 113))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 624
 (.branch 616
 (.branch 612
 (.branch 610
 (.branch 609
 (.leaf (.leaf 114))
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
 (.leaf (.leaf 115))
 (.leaf (.leaf 116)))
 (.branch 643
 (.leaf (.leaf 117))
 (.leaf (.branch 0x10000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000008 (.leaf 118) (.leaf 119)))))
 (.branch 646
 (.branch 645
 (.leaf (.leaf 120))
 (.leaf (.branch 0x10000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000020 (.leaf 121) (.leaf 122))))
 (.branch 647
 (.leaf (.branch 0x10000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000040 (.leaf 123) (.leaf 124)))
 (.leaf (.leaf 0)))))
 (.branch 652
 (.branch 650
 (.branch 649
 (.leaf (.leaf 125))
 (.leaf (.leaf 0)))
 (.branch 651
 (.leaf (.branch 0x10000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000400 (.leaf 126) (.leaf 127)))
 (.leaf (.leaf 0))))
 (.branch 654
 (.branch 653
 (.leaf (.branch 0x10000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000001000 (.leaf 128) (.leaf 129)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 664
 (.branch 660
 (.branch 658
 (.branch 657
 (.leaf (.leaf 130))
 (.leaf (.branch 0x10000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000020000 (.leaf 131) (.leaf 132))))
 (.leaf (.leaf 0)))
 (.branch 662
 (.branch 661
 (.leaf (.branch 0x10000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000100000 (.leaf 133) (.leaf 134)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 668
 (.branch 666
 (.branch 665
 (.leaf (.branch 0x10000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000001000000 (.leaf 135) (.leaf 136)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 688
 (.branch 680
 (.branch 676
 (.branch 674
 (.branch 673
 (.leaf (.leaf 137))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 684
 (.branch 682
 (.branch 681
 (.leaf (.branch 0x10000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000010000000000 (.leaf 138) (.leaf 139)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 696
 (.branch 692
 (.branch 690
 (.branch 689
 (.leaf (.branch 0x10000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000001000000000000 (.leaf 140) (.leaf 141)))
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
 (.leaf (.leaf 142))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 710
 (.branch 709
 (.leaf (.branch 0x10000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000100000000000000000 (.leaf 143) (.leaf 144)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
 (.branch 728
 (.branch 724
 (.branch 722
 (.branch 721
 (.leaf (.branch 0x10000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000100000000000000000000 (.leaf 145) (.leaf 146)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 752
 (.branch 744
 (.branch 740
 (.branch 738
 (.branch 737
 (.leaf (.branch 0x10000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000001000000000000000000000000 (.leaf 147) (.leaf 148)))
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
 (.leaf (.leaf 149))
 (.leaf (.leaf 150)))
 (.branch 771
 (.leaf (.leaf 151))
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000008 (.leaf 152) (.leaf 153)))))
 (.branch 774
 (.branch 773
 (.leaf (.leaf 154))
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000020 (.leaf 155) (.leaf 156))))
 (.branch 775
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000040 (.leaf 157) (.leaf 158)))
 (.leaf (.leaf 0)))))
 (.branch 780
 (.branch 778
 (.branch 777
 (.leaf (.leaf 159))
 (.leaf (.leaf 0)))
 (.branch 779
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000400 (.leaf 160) (.leaf 161)))
 (.leaf (.leaf 0))))
 (.branch 782
 (.branch 781
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000001000 (.leaf 162) (.leaf 163)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 792
 (.branch 788
 (.branch 786
 (.branch 785
 (.leaf (.leaf 164))
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000020000 (.leaf 165) (.leaf 166))))
 (.leaf (.leaf 0)))
 (.branch 790
 (.branch 789
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000100000 (.leaf 167) (.leaf 168)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 796
 (.branch 794
 (.branch 793
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000001000000 (.leaf 169) (.leaf 170)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 816
 (.branch 808
 (.branch 804
 (.branch 802
 (.branch 801
 (.leaf (.leaf 171))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 812
 (.branch 810
 (.branch 809
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000010000000000 (.leaf 172) (.leaf 173)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 824
 (.branch 820
 (.branch 818
 (.branch 817
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000001000000000000 (.leaf 174) (.leaf 175)))
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
 (.leaf (.leaf 176))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 838
 (.branch 837
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000100000000000000000 (.leaf 177) (.leaf 178)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
 (.branch 856
 (.branch 852
 (.branch 850
 (.branch 849
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000100000000000000000000 (.leaf 179) (.leaf 180)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 880
 (.branch 872
 (.branch 868
 (.branch 866
 (.branch 865
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000001000000000000000000000000 (.leaf 181) (.leaf 182)))
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
 (.leaf (.leaf 183))
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000 (.leaf 184) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000200000000000000000000000000000000 (.leaf 185) (.leaf 186)))))
 (.branch 899
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000 (.leaf 187) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000400000000000000000000000000000000 (.leaf 188) (.leaf 189))))
 (.leaf (.leaf 0))))
 (.branch 902
 (.branch 901
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000 (.leaf 190) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000000 (.leaf 191) (.leaf 192))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 908
 (.branch 906
 (.branch 905
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000 (.leaf 193) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000000000000000000 (.leaf 194) (.leaf 195))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 920
 (.branch 916
 (.branch 914
 (.branch 913
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000 (.leaf 196) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000000000 (.leaf 197) (.leaf 198))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 944
 (.branch 936
 (.branch 932
 (.branch 930
 (.branch 929
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000 (.leaf 199) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000000000000000000000000 (.leaf 200) (.leaf 201))))
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
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000 (.leaf 202) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000000000000000000000 (.leaf 203) (.leaf 204))))
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
def candidateMasks (i : Nat) := PackedRawNatGrowth.take 556
  (PackedRawNatGrowth.drop (556*(i%64)) (candidateMasksBlocks.get (i/64)))

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
 (.branch 8
 (.leaf badMasksBlock0007)
 (.leaf badMasksBlock0008)))))
def badMasks (i : Nat) := PackedRawNatGrowth.take 556
  (PackedRawNatGrowth.drop (556*(i%64)) (badMasksBlocks.get (i/64)))

def signatureMasksBlocks : Table Nat :=
(.branch 2
 (.branch 1
 (.leaf signatureMasksBlock0000)
 (.leaf signatureMasksBlock0001))
 (.branch 3
 (.leaf signatureMasksBlock0002)
 (.leaf signatureMasksBlock0003)))
def signatureMasks (i : Nat) := PackedRawNatGrowth.take 556
  (PackedRawNatGrowth.drop (556*(i%64)) (signatureMasksBlocks.get (i/64)))

def fastKind := rawKind
def candidateSupports := candidateRows
def kindSupports := kindRows
def wellFormedTest (i : Nat) : Bool := RawFacetEmbedding.wellFormedCheck (rawCells i)

def cellTest (i : Nat) := (listBounds 1024 (rawCells i).ridgeMasks && ((rawCells i).ridgeMasks.all (fun q => (candidateMasks q).testBit i) && (decide (rawKind i = (rawCells i).kind) && (decide ((rawCells i).vertices < 1024) && ((List.range 10).all (fun v => decide ((vertexMasks v).testBit i = (rawCells i).vertices.testBit v)) && (SignatureCompatibility.faces (rawCells i)).all (fun q => (SignatureCompatibility.profileMask (SignatureCompatibility.allMask 556) signatureIndex signatureMasks (rawCells i) q).testBit i))))))
def ridgeTest (i : Nat) := decide (candidateMasks i = RawNatGrowthCheck.mask (candidateRows i)) &&
  (candidateRows i).all (fun c => hasNat (rawCells c).ridgeMasks i)
def kindTest (i : Nat) := decide (kindMasks i = RawNatGrowthCheck.mask (kindRows i)) &&
  (kindRows i).all (fun c => decide ((rawCells c).kind = i))
def badTest (i : Nat) := if badMasks i = 0 then true else
  decide (Nat.land (badMasks i) (SignatureCompatibility.cover (SignatureCompatibility.allMask 556)
    vertexMasks signatureIndex signatureMasks (rawCells i)) = 0)

end Papers.RationalityTen.RootedCaches.RootedSevenMixed022

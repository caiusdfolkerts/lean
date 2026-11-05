module
prelude
public import RootedSevenPure062
public import SignatureCompatibility
public import PackedRawNatGrowth
public import FiniteChecks
public import RawFacetEmbedding
public import RootedSevenPure062GrowthCachecandidateMasksData000
public import RootedSevenPure062GrowthCachebadMasksData000
public import RootedSevenPure062GrowthCachesignatureMasksData000

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure062
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def rawCells := Papers.RationalityTen.FacetUniverses.RootedSevenPure062.rawCells
def cells (c : Fin 496) := rawCells c.val
def ridgeList := ConcreteGrowth.ridgeList cells
def literalCompatible (a b : Fin 496) := ConcreteGrowth.compatible (cells a) (cells b)
def kind (c : Fin 496) := (cells c).kind
def rawKindCode : Nat := 3669921398255849356061346242236897636592412998643005438713744842294719902507102867923441624154133364549201257411391109259529887948207242235172841881789613671693943967038556535238890950458902885513005819166197206322478069861570843152641783590744459864895411346657425263198657535121473397371640274626314065855154745958941931806624706627734505514503510753933351363626713233082972299552791464713990459394067841693489589477726932217379566922630678783120
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
 (.branch 20
 (.leaf 0x0)
 (.branch 22
 (.branch 21
 (.leaf 0x0)
 (.leaf 0x602f978ba5c2d968b2582b958aa5429948a250279389a4c259289248239188a442190882401f8f87a000025))
 (.leaf 0x0)))
 (.branch 28
 (.branch 26
 (.leaf 0x0)
 (.branch 27
 (.leaf 0x0)
 (.leaf 0x138984a000004)))
 (.leaf 0x0))))
 (.branch 48
 (.leaf 0x0)
 (.branch 56
 (.branch 52
 (.leaf 0x0)
 (.branch 54
 (.branch 53
 (.leaf 0x11489c4a231087c3a1b0c85c2a130883c1a0b0481c0a03007fbf9fafc7dbe9f2f87bbd9eaf479bc9e2000025)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 60
 (.branch 58
 (.branch 57
 (.leaf 0x162b0d82bf5eaed72b75aacd62af56aad52a752a8d429f4ea6d32974aa4d228f46a2d128742a0d027e000025)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))))
 (.branch 96
 (.branch 80
 (.branch 72
 (.leaf 0x0)
 (.branch 76
 (.branch 74
 (.leaf 0x0)
 (.branch 75
 (.leaf 0xc662b1186c260b017ebe5eaf176ba5cae16eb65aad166b258ac15eae56ab156aa54aa14ea652a9146000025)
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 112
 (.branch 104
 (.branch 100
 (.leaf 0x0)
 (.branch 102
 (.leaf 0x0)
 (.branch 103
 (.leaf 0x46a3116000004)
 (.leaf 0x0))))
 (.branch 108
 (.branch 106
 (.branch 105
 (.leaf 0x19bcd6673197cb6572993c9647218fc7637198bc56271187c36170983c1607017fbf5f6f97bbd5e6f0000025)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))))
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
 (.leaf 0x389c0dc6d359a8d06733194c662291409a4c251188841200f830130903c1c0c0381806020020))
 (.branch 135
 (.leaf 0x2793a9b4d2612e954a24d249047a2c2e15090401a0b0481808010017)
 (.leaf 0x0))))
 (.branch 140
 (.branch 138
 (.leaf 0x0)
 (.branch 139
 (.leaf 0x35dacd469b45a0ce66b3196c9642e16cb3592c158aa53a9948250017)
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 152
 (.branch 148
 (.branch 146
 (.branch 145
 (.leaf 0x0)
 (.leaf 0x2190a8341200fe7d3e1ecf4783b9509e4e259289043210fc7c250017))
 (.leaf 0x0))
 (.branch 150
 (.branch 149
 (.leaf 0x92c9245218fc7a391b8d4662f168341203007f3e9f0f57a3c8a65127130924722908803d0020)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 156
 (.branch 154
 (.branch 153
 (.leaf 0x5cee570b7db6d96ab4da2cf65b2552a54fa75329146a1d0a80250017)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 176
 (.branch 168
 (.branch 164
 (.leaf 0x0)
 (.branch 166
 (.branch 165
 (.leaf 0x4ea73379b4d26731984be5d2c95c2207027fbf9f8f77b3cde48b0017)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 172
 (.branch 170
 (.branch 169
 (.leaf 0xd66af53a8d369747a2d0e833d9dc6e2f1187c2e06ff7cbdde6ad51a8536994aa2d1283400020)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 184
 (.branch 180
 (.branch 178
 (.branch 177
 (.leaf 0xeb757a7d2e873f9bcce5f2b91c7aad4ea14ea5d268f44a14fe0f0581401fafb7cbd9e8f10020)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 224
 (.branch 208
 (.branch 200
 (.branch 196
 (.branch 194
 (.leaf 0x0)
 (.branch 195
 (.leaf 0x3b1d6e974399cae371385c0de6eae96ab458ac15ca954295488b0017)
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 204
 (.branch 202
 (.branch 201
 (.leaf 0xe0f037dbdddeeb71b7db6d767b2c7e2b1386c2e0efd7dbd5e572b75a2c95ead55aa14ca30020)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 240
 (.branch 232
 (.branch 228
 (.branch 226
 (.branch 225
 (.leaf 0x7afd5e8f3f97c9e2f0f83bfddee63b1989c3e130580bedeef08b0017)
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
 (.leaf 0x399c8de6e361acd26733190c6612f170b2582b11486421f8f4481f0f06c340b0401408010020))
 (.branch 263
 (.leaf 0x2813e9c4da6530964a24d22904723046210f070320c0501406020017)
 (.leaf 0x0))))
 (.branch 268
 (.branch 266
 (.leaf 0x0)
 (.branch 267
 (.leaf 0x365b0d56a349a2cf66b3194c963b1184bf5f2f156a95429546260017)
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 280
 (.branch 276
 (.branch 274
 (.branch 273
 (.leaf 0x0)
 (.leaf 0x2210e8441a05007e3e1ecf2783b180b65a2b9588e44209007a260017))
 (.leaf 0x0))
 (.branch 278
 (.branch 277
 (.leaf 0x93c9a47229047e3b1b8d4622f15894421b0c853e5eef679bc4be5d2d160aa48231047e3e0020)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 284
 (.branch 282
 (.branch 281
 (.leaf 0x5d6e971b85badb6bb4da2cd65b1d82bd5bad5628f45a25067e260017)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 304
 (.branch 296
 (.branch 292
 (.leaf 0x0)
 (.branch 294
 (.branch 293
 (.leaf 0x4f277389bcd66932984be5b2c954521f0e85c29f6f87abd1e28c0017)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 300
 (.branch 298
 (.branch 297
 (.leaf 0xd76b755a9d3e9b49a2d0e7f3d9ccce5f2993c8e02fd7dbd5e2c55dae566b149a350e853f0020)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 312
 (.branch 308
 (.branch 306
 (.branch 305
 (.leaf 0xec75fa9d3e8f439dcce5f2791c6b0d7eb95aabd2a9143a0d0227118743212fc7d3d5e6f20020)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 352
 (.branch 336
 (.branch 328
 (.branch 324
 (.branch 322
 (.leaf 0x0)
 (.branch 323
 (.leaf 0x3b9daea74b9dcce471385bede6e31982c05eaf15aaa53a99468c0017)
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 332
 (.branch 330
 (.branch 329
 (.leaf 0xe1f0b7fbede6ef73b7db6d367b1cde5b2b92c8e0aff7cbdde18ac3602f976ae5629d4aa40020)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 368
 (.branch 360
 (.branch 356
 (.branch 354
 (.branch 353
 (.leaf 0x7b7d9e9f479bcbe3f0f83bdddede6b3195c9e430781be5eaf28c0017)
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
 (.leaf 0x2210c813f9f8fa7a3c9e0e671361a8d26832990c6442190882401f8e87033188c05e2c158a810070301408030027))
 (.branch 387
 (.leaf 0x773b1cee57238dc0df6f365aed26833d9ccb6532554a95429d4ca55027932974b2552491480e46e361a0c05e2d148a014090301404010030)
 (.leaf 0x1e0ec180b0004)))
 (.branch 390
 (.branch 389
 (.leaf 0x2793a9acce6531974b6592792c823d1d8e46631177c3ddecf57a3cd3e9d4e2692c9549a3d1c72381bcda6934198c4612311484411f0f4180b0200c04010036)
 (.leaf 0xea742411c14090006))
 (.branch 391
 (.leaf 0x5128410070004)
 (.leaf 0x0))))
 (.branch 396
 (.branch 394
 (.branch 393
 (.leaf 0x387c1de6eb73b8daed367aed669f4ba4d1e833f9ebfdfafb7cbddeaeb73b75b2d76ab3d9acb46a2d128742a0b61acd569b3d9ccc6431d58ab5429d48a30036)
 (.leaf 0x0))
 (.branch 395
 (.leaf 0x6db695cad0004)
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 408
 (.branch 404
 (.branch 402
 (.branch 401
 (.leaf 0x3b1d6e8f3f9dcde57279174b95c6df6bb55a2c963a451e8943a04fe4d2491c863b1c8d45a2afa7cbd9eaf278a1d0a84411f8fa7b3b9d89047200fc7c3d0036)
 (.leaf 0x452248c450004))
 (.leaf 0x0))
 (.branch 406
 (.branch 405
 (.leaf 0x253287e3ec88430006)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 412
 (.branch 410
 (.branch 409
 (.leaf 0xbbdda95490004)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 432
 (.branch 424
 (.branch 420
 (.branch 418
 (.branch 417
 (.leaf 0x3dbebf3793c7e2eff7bbbd7eaf53a5cee6f2f8fc6d6eaf55a8d268f439dce607017dbe5e6f14aa4d0a83409fcee73389b4ca632f95ca9f8fb7a3cde4f10036)
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 422
 (.branch 421
 (.leaf 0x9f4f5f4f90004)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 428
 (.branch 426
 (.branch 425
 (.leaf 0x361afc1e0a91470006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 440
 (.branch 436
 (.branch 434
 (.branch 433
 (.leaf 0x3b5d9a3515f0f70006)
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
 (.leaf 0x7b3d5e9f3f8fc5e0ee76f85c0dfef773b8db6cb6383c15eef579bc3b5d6ea74391c6e16eb715cad5329548a30027)
 (.leaf 0x0))
 (.branch 451
 (.leaf 0x783bd58ab0004)
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 460
 (.branch 458
 (.branch 457
 (.leaf 0x38bc4c0e0154a90006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 496
 (.branch 488
 (.branch 484
 (.branch 482
 (.branch 481
 (.leaf 0xf7fbaff7e0004)
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
 (.leaf 0x3a9d0de6d361a8d26832990c4612e96cb4572a9449e4e2592446200e87032170a044200d0020))
 (.branch 519
 (.leaf 0x289429c4d2652e964aa49228f4723448220e86c34180b0441e0e0017)
 (.leaf 0x0))))
 (.branch 524
 (.branch 522
 (.leaf 0x0)
 (.branch 523
 (.leaf 0x36db4d569b49a0cf6732d94c863b0d82c05eaed6eb55a2c55e270017)
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 536
 (.branch 532
 (.branch 530
 (.branch 529
 (.leaf 0x0)
 (.leaf 0x229128441204fe7e3e9e8f2773b17cb8592c154a6502693092270017))
 (.leaf 0x0))
 (.branch 534
 (.branch 533
 (.leaf 0x94ca247219047a3b1c8cc622d1588c3e1d0b84c1607027fbf4c05e2c95cac5429134964a0020)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 540
 (.branch 538
 (.branch 537
 (.leaf 0x5deed71b7dbad96bb559ecd64b1d7ebb5cacd5ea751a853696270017)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 560
 (.branch 552
 (.branch 548
 (.leaf 0x0)
 (.branch 550
 (.branch 549
 (.leaf 0x4fa7b389b4d6673298cba5b2b9544e210d864260f0480c01fa8d0017)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 556
 (.branch 554
 (.branch 553
 (.leaf 0xd86bf55a8d3e9749a3d067f3b9ccc65b2b92c86331589c3612c35eadd6aaf55a953e9d4b0020)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 568
 (.branch 564
 (.branch 562
 (.branch 561
 (.leaf 0xed767a9d2e8f3f9dcde57278fc6b1582b759ac55aa94fa6d32291286c2e150883405fefe0020)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 608
 (.branch 592
 (.branch 584
 (.branch 580
 (.branch 578
 (.leaf 0x0)
 (.branch 579
 (.leaf 0x3c1deea7439dcae471b81bedd6e31584bf5f2ed72b659ac95e8d0017)
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 588
 (.branch 586
 (.branch 585
 (.leaf 0xe2f137fbdde6eb73b8daed365b1cd65f2993c863b1788c3e118cc45faf578ba5c2cd62b00020)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 624
 (.branch 616
 (.branch 612
 (.branch 610
 (.branch 609
 (.leaf 0x7bfdde9f3f9bc9e3f177fbddcede6f3394c96471f8dc461b0a8d0017)
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
 (.leaf 0x2290a81401f8f87b3c9dcea70361acd26733190c450279389a4c258f06e33190c05c2d158a4281309044200f0027))
 (.branch 643
 (.leaf 0x783adcee672389c2df6eb6dacd268b3d9acc653216cb55a2cd64b15127532984b2512691478ec70361a8c05c2c150a02c15090441c0d0030)
 (.leaf 0x1d0e430170004)))
 (.branch 646
 (.branch 645
 (.leaf 0x27d399acd2653097cb65729924823f1d8dc6a31168240e0501803fd429e4e26d2c94492411c74389bcdc6933994c661291449c4d2512430170803c1c0d0036)
 (.leaf 0xe6722a14c2c150006))
 (.branch 647
 (.leaf 0x5027c28130004)
 (.leaf 0x0))))
 (.branch 652
 (.branch 650
 (.branch 649
 (.leaf 0x38bc0de6ef73b7db6d365b0d5e9f4da4d16873f9dc5e2b1388c3e1aef72b75b6d769b459ac952a8d429f4ea6b69aed56a33d9acb64b1d70b75a2cd60af0036)
 (.leaf 0x0))
 (.branch 651
 (.leaf 0x6cb6174b90004)
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 664
 (.branch 660
 (.branch 658
 (.branch 657
 (.leaf 0x3b5d5e8f439dcce5f278f76b9dc6e16bb4d9ecb63aa54ea14fa652e512591c8a3b1b8cc5e2b0682c0a02fe7ea250c84419f8f87a3c1d8a8532612c94490036)
 (.leaf 0x4421ca4510004))
 (.leaf 0x0))
 (.branch 662
 (.branch 661
 (.leaf 0x24f268441ca04f0006)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 668
 (.branch 666
 (.branch 665
 (.leaf 0xbadd2ad550004)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 688
 (.branch 680
 (.branch 676
 (.branch 674
 (.branch 673
 (.leaf 0x3dfeaf3797c7e1f077bb9d9eb753a7cee672b91c6d7eb355a9d268b419ece6371989c46170956aad3a9b4ca5cf675389bcca612e964aa1107803fdfcfd0036)
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 678
 (.branch 677
 (.leaf 0x9e4ee0d050004)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 684
 (.branch 682
 (.branch 681
 (.leaf 0x35dadc7e3aa9530006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 696
 (.branch 692
 (.branch 690
 (.branch 689
 (.leaf 0x3b1d7a954609030006)
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
 (.leaf 0x7bbd7e9f478fc3dfeef6f89c1dfefb73b7daecf638fc761f0d85c23bdd8ea74b91c4e06f37174b9592c560af0027)
 (.leaf 0x0))
 (.branch 707
 (.leaf 0x773b570b70004)
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 716
 (.branch 714
 (.branch 713
 (.leaf 0x387c2c6e316cb50006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 752
 (.branch 744
 (.branch 740
 (.branch 738
 (.branch 737
 (.leaf 0xf6fb3178a0004)
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
 (.leaf 0x2250e803f9f4f87b3d1d8e872359a8d06733194c25c2d968b2582b8ec7232188bc5c2d160a0401f0f074381b0027))
 (.branch 771
 (.leaf 0x77bb5cce571b89c2e06e369b0d1683399acc65b1d84c1602fd7cbd50a7d30974aa512692470f074351a0bc5c2b150a444210f07434190030)
 (.leaf 0x1c0dc48230004)))
 (.branch 774
 (.branch 773
 (.leaf 0x27b3b9a4ce633097cba55289347e3d1c8dc6a33158843e1d0d8642d44a04da692a9448a411e75399b8da6833990c6622f174b4592b15448230e06c34190036)
 (.leaf 0xe2703017c44210006))
 (.branch 775
 (.leaf 0x4f274401f0004)
 (.leaf 0x0))))
 (.branch 780
 (.branch 778
 (.branch 777
 (.leaf 0x389c2ddeeb71b7db6d763afd6e9b4ba3d1687419ccbe5b2b94c9e4aed74b6db2d569b459ec75eaed72b75aacb6db2d469b399aca64b2188c3602fd78bb0036)
 (.leaf 0x0))
 (.branch 779
 (.leaf 0x6bb598cc50004)
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 792
 (.branch 788
 (.branch 786
 (.branch 785
 (.leaf 0x3b3d7e873f9bcce5f2b8d77badc2df6ab4d9acb64b057eb95bac55e532791486391b8c45e2d1288c3a1b0a84a291083411f4f8793c1dcc05f2c15cac550036)
 (.leaf 0x43214bc5d0004))
 (.leaf 0x0))
 (.branch 790
 (.branch 789
 (.leaf 0x24b248a44cb85b0006)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 796
 (.branch 794
 (.branch 793
 (.leaf 0xb9dcac5610004)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 816
 (.branch 808
 (.branch 804
 (.branch 802
 (.branch 801
 (.leaf 0x3ddecf2f93c5e1f077fb7daec74fa5cde672791c7d86bb53a8d1e8b3f9ecee673195ca6472162b0d6ab358abcfa79379b4c6612d964ae29138642e15090036)
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 806
 (.branch 805
 (.leaf 0x9d4e625110004)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 812
 (.branch 810
 (.branch 809
 (.leaf 0x359abcde6ac15f0006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 824
 (.branch 820
 (.branch 818
 (.branch 817
 (.leaf 0x3add5af576210f0006)
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
 (.leaf 0x7bfdbe8f3f8bc3deeef738bc3df6f771b7da6cf659bcd64f2591c83c1dce97438dc4df6f3758cc55f2f578bb0027)
 (.leaf 0x0))
 (.branch 835
 (.leaf 0x763ad88c30004)
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 844
 (.branch 842
 (.branch 841
 (.leaf 0x383c0cce6184c10006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 880
 (.branch 872
 (.branch 868
 (.branch 866
 (.branch 865
 (.leaf 0xf5fab2f960004)
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
 (.leaf 0xf7fbbdbecf5fabc1dfef777b9dbed767b1d7eb75797cae4f238fc6e2f1387c2e0f036db5da6cf65b1d86bf5dadd66af43a0cfe7b3b9cbbddaeb74b9dcad167b3596c9639f4f6793b9d4e65f2e96cb2572a94ca24f2692c9235198c45e2d15783bddced763adc2e06fb79badc6db69b2d86bb5998cb6532590c751285409f4f275269248a411e8e45225108743214f67a3c9e0ee763a9d0e672389c0cc653218cc4611e0ec74391c0dc5a2c158a85228009c)
 (.leaf 0x8441a08de6e368d86a340009))
 (.branch 899
 (.leaf 0x753a5d0d56a34d389b4d0cc6431000c)
 (.leaf 0x0)))
 (.branch 902
 (.branch 901
 (.leaf 0x9c4de6d239148532984b9b0d66a000c)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 908
 (.branch 906
 (.branch 905
 (.leaf 0xdfefb7baad4ea2e370b7b49a2d0000c)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 920
 (.branch 916
 (.branch 914
 (.branch 913
 (.leaf 0xea74fa56eb6db2411f8f205007f000c)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 944
 (.branch 936
 (.branch 932
 (.branch 930
 (.branch 929
 (.leaf 0xf4fa3cfd1e873f4fa6d2cd66933000c)
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
 (.leaf 0x1e6f2f9379bbdd39dcce50009)
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
 (.leaf 0x1e3f1787c1dfef777b9dbe773799cbe572791c7e36e771b7db6d769b3d96c749a3d1687419fcf6773995ca64f2591c86271187c3617097dbe5eef579bc5aed569b459ecd65b258eb95bad566b157a853e9d4da652e8943a1506813f994c6612f974b6592b95476391b8d46631178b4561d0d8642e15098140600ff7f3f5ecf57a3cde4f17238dc4e17037dbcdd6e33d9ccd6632d94c96431d80bf5f2f578bb5a2cd64b1582bd50a75329548a34b255289349245208f471f8fa7c3d9e8f2783b9d8d26833998ca6431988c25a2c960ae562a9389a4c259289242209007e3e1e8c05e2e168b0562a148a03c1d0e06c341909044200f070340c050200c040100e1)
 (.branch 4
 (.leaf 0x3dfeef6fb3d7eaf4fa3cfe6f2f93b5d9ec75fadd5ea74fa5d1e873f8bc4e1f0b83c0dfefb7bbcddeeb61afd76b759abd56a751a7d3697379acce632f96c7e3b1b8cc5e2b0782c0e02ff7ebbddaeb74b9dcae370b7dbadb6cb1586c15faf576ad55aa54ea551a55269147a35167d3d9e4ee75399c4de6d359a4ce532893c9a4b2491c8a43208fc7a291389446210f8441e0d058240df8fb7d3e5f0f7783bddced763add4e97439dcce56db69b2d86bb59aad469b49a2d06331588c36130574b95c2dd6cb5572b558ab552a544a15027d3c9d4e26d34994c25d1a8c45a29128843a190a8441a0902803f9d4e873391c4e06f371b4d86b35180be5e2e970b65429948a250279208e4622910863c1d8e872381b8d86a34198c8622713094482311084401f0c05c2c150a04c180b050241007010e)
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
 (.leaf 0xff8007fc003fe001ff03f03f03f000ff81f81f81f8007fc003fe07e07e07e001ff000ff81f81f81f8007fc0007fc003fe07e07e07e001ff007e07e07e)
 (.branch 4
 (.leaf 0xfff007ff803ffc01ffe00fc0fc0fc0fff007e07e07e07ff803ffc01f81f81f81ffe00fff007e07e07e07ff803fff803ffc01f81f81f81ffe00ff81f81f80)
 (.leaf 0x0))))
def kindMasks := kindMaskTable.get
def keys := List.range 5
def vertexMaskTable : Table Nat :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf 696898287454081973172991196020261297061887)
 (.leaf 3533694129556768659166595001485140133367513711778064927353035150501871615))
 (.branch 3
 (.leaf 1067993517960455041197507319390646500532693094595016911538238417141862563370109020044957916856319)
 (.branch 4
 (.leaf 46517678354918840995156723704832290198631979090470395402974175236707831348196832437530024393971238966588461745781009745992826806775840769)
 (.leaf 97554595679696402311833918274466656309058159258588236467682522006770219189061008510613674700710983814916714842996861349741643310997084666068993))))
 (.branch 7
 (.branch 6
 (.leaf 204586912993462349219650794763696309012548595747927363182436080649488287734600924703819369729197587472742945262306003757973486797785368358982273466369)
 (.leaf 204586815438913187157240697241735654314234088577032548583321374773493792756219356553620673264702072727016814110574830209547428924197367714731043848193))
 (.branch 8
 (.leaf 204586912993508866875824345477411696247649379862664786245506147263811254891408796745574949656016756223936990016602811785895081414665541862114423996414)
 (.branch 9
 (.leaf 204586912993508866875824356049143327567552361581789443199371433268888685247122266281050418506913357416266841660307243933308866683302114503126138494974)
 (.leaf 204586912993508866875824356051724316735355072270685713867573060535979768604142704139823727947550783344292314209120128935392083491221919965950127366144)))))
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
 (.leaf (.leaf 0))))
 (.branch 56
 (.branch 52
 (.branch 50
 (.branch 49
 (.leaf (.leaf 12))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 54
 (.branch 53
 (.leaf (.leaf 13))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
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
 (.branch 66
 (.leaf (.leaf 0))
 (.branch 67
 (.leaf (.leaf 15))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
 (.branch 76
 (.branch 74
 (.branch 73
 (.leaf (.leaf 16))
 (.leaf (.leaf 0)))
 (.branch 75
 (.leaf (.leaf 17))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
 (.branch 112
 (.branch 104
 (.branch 100
 (.branch 98
 (.branch 97
 (.leaf (.leaf 18))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 102
 (.leaf (.leaf 0))
 (.branch 103
 (.leaf (.leaf 19))
 (.leaf (.leaf 0)))))
 (.branch 108
 (.branch 106
 (.branch 105
 (.leaf (.leaf 20))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))))
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
 (.leaf (.leaf 0))))
 (.branch 152
 (.branch 148
 (.branch 146
 (.branch 145
 (.leaf (.leaf 29))
 (.leaf (.leaf 30)))
 (.leaf (.leaf 0)))
 (.branch 150
 (.branch 149
 (.leaf (.leaf 31))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 156
 (.branch 154
 (.branch 153
 (.leaf (.leaf 32))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 176
 (.branch 168
 (.branch 164
 (.branch 162
 (.branch 161
 (.leaf (.leaf 33))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 166
 (.branch 165
 (.leaf (.leaf 34))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
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
 (.branch 195
 (.leaf (.leaf 38))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
 (.branch 204
 (.branch 202
 (.branch 201
 (.leaf (.leaf 39))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
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
 (.leaf (.leaf 0))))
 (.branch 280
 (.branch 276
 (.branch 274
 (.branch 273
 (.leaf (.leaf 49))
 (.leaf (.leaf 50)))
 (.leaf (.leaf 0)))
 (.branch 278
 (.branch 277
 (.leaf (.leaf 51))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 284
 (.branch 282
 (.branch 281
 (.leaf (.leaf 52))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 304
 (.branch 296
 (.branch 292
 (.branch 290
 (.branch 289
 (.leaf (.leaf 53))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 294
 (.branch 293
 (.leaf (.leaf 54))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
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
 (.branch 323
 (.leaf (.leaf 58))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
 (.branch 332
 (.branch 330
 (.branch 329
 (.leaf (.leaf 59))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
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
 (.leaf (.leaf 0))))
 (.branch 408
 (.branch 404
 (.branch 402
 (.branch 401
 (.leaf (.leaf 74))
 (.leaf (.branch 0x1000000000000000000000000000100000000000000000000000000000000000200000000000000000000000000020000 (.leaf 75) (.leaf 76))))
 (.leaf (.leaf 0)))
 (.branch 406
 (.branch 405
 (.leaf (.branch 0x1000000000000000000000000000100000000000000000000000000000000001000000000000000000000000000100000 (.leaf 77) (.leaf 78)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 412
 (.branch 410
 (.branch 409
 (.leaf (.branch 0x1000000000000000000000000000100000000000000000000000000000000010000000000000000000000000001000000 (.leaf 79) (.leaf 80)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 432
 (.branch 424
 (.branch 420
 (.branch 418
 (.branch 417
 (.leaf (.leaf 81))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 422
 (.branch 421
 (.leaf (.branch 0x1000000000000000000000001000000000000000000000000000000000000001000000000000000000000001000000000 (.leaf 82) (.leaf 83)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
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
 (.branch 451
 (.leaf (.branch 0x1000000000000000100000000000000000000000000000000000000000000000400000000000000040000000000000000 (.leaf 89) (.leaf 90)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
 (.branch 460
 (.branch 458
 (.branch 457
 (.leaf (.branch 0x1000000000000000100000000000000000000000000000000000000000000010000000000000001000000000000000000 (.leaf 91) (.leaf 92)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
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
 (.leaf (.leaf 0))))
 (.branch 536
 (.branch 532
 (.branch 530
 (.branch 529
 (.leaf (.leaf 103))
 (.leaf (.leaf 104)))
 (.leaf (.leaf 0)))
 (.branch 534
 (.branch 533
 (.leaf (.leaf 105))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 540
 (.branch 538
 (.branch 537
 (.leaf (.leaf 106))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 560
 (.branch 552
 (.branch 548
 (.branch 546
 (.branch 545
 (.leaf (.leaf 107))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 550
 (.branch 549
 (.leaf (.leaf 108))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
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
 (.branch 579
 (.leaf (.leaf 112))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
 (.branch 588
 (.branch 586
 (.branch 585
 (.leaf (.leaf 113))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
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
 (.leaf (.leaf 0))))
 (.branch 664
 (.branch 660
 (.branch 658
 (.branch 657
 (.leaf (.leaf 128))
 (.leaf (.branch 0x10000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000020000 (.leaf 129) (.leaf 130))))
 (.leaf (.leaf 0)))
 (.branch 662
 (.branch 661
 (.leaf (.branch 0x10000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000100000 (.leaf 131) (.leaf 132)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 668
 (.branch 666
 (.branch 665
 (.leaf (.branch 0x10000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000001000000 (.leaf 133) (.leaf 134)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 688
 (.branch 680
 (.branch 676
 (.branch 674
 (.branch 673
 (.leaf (.leaf 135))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 678
 (.branch 677
 (.leaf (.branch 0x10000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000001000000000 (.leaf 136) (.leaf 137)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
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
 (.branch 707
 (.leaf (.branch 0x10000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000040000000000000000 (.leaf 143) (.leaf 144)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
 (.branch 716
 (.branch 714
 (.branch 713
 (.leaf (.branch 0x10000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000001000000000000000000 (.leaf 145) (.leaf 146)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
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
 (.leaf (.leaf 0))))
 (.branch 792
 (.branch 788
 (.branch 786
 (.branch 785
 (.leaf (.leaf 162))
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000020000 (.leaf 163) (.leaf 164))))
 (.leaf (.leaf 0)))
 (.branch 790
 (.branch 789
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000100000 (.leaf 165) (.leaf 166)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 796
 (.branch 794
 (.branch 793
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000001000000 (.leaf 167) (.leaf 168)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 816
 (.branch 808
 (.branch 804
 (.branch 802
 (.branch 801
 (.leaf (.leaf 169))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 806
 (.branch 805
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000001000000000 (.leaf 170) (.leaf 171)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
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
 (.branch 835
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000040000000000000000 (.leaf 177) (.leaf 178)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
 (.branch 844
 (.branch 842
 (.branch 841
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000001000000000000000000 (.leaf 179) (.leaf 180)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
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
def candidateMasks (i : Nat) := PackedRawNatGrowth.take 496
  (PackedRawNatGrowth.drop (496*(i%64)) (candidateMasksBlocks.get (i/64)))

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
def badMasks (i : Nat) := PackedRawNatGrowth.take 496
  (PackedRawNatGrowth.drop (496*(i%64)) (badMasksBlocks.get (i/64)))

def signatureMasksBlocks : Table Nat :=
(.branch 2
 (.branch 1
 (.leaf signatureMasksBlock0000)
 (.leaf signatureMasksBlock0001))
 (.branch 3
 (.leaf signatureMasksBlock0002)
 (.leaf signatureMasksBlock0003)))
def signatureMasks (i : Nat) := PackedRawNatGrowth.take 496
  (PackedRawNatGrowth.drop (496*(i%64)) (signatureMasksBlocks.get (i/64)))

def fastKind := rawKind
def candidateSupports := candidateRows
def kindSupports := kindRows
def wellFormedTest (i : Nat) : Bool := RawFacetEmbedding.wellFormedCheck (rawCells i)

def cellTest (i : Nat) := (listBounds 1024 (rawCells i).ridgeMasks && ((rawCells i).ridgeMasks.all (fun q => (candidateMasks q).testBit i) && (decide (rawKind i = (rawCells i).kind) && (decide ((rawCells i).vertices < 1024) && ((List.range 10).all (fun v => decide ((vertexMasks v).testBit i = (rawCells i).vertices.testBit v)) && (SignatureCompatibility.faces (rawCells i)).all (fun q => (SignatureCompatibility.profileMask (SignatureCompatibility.allMask 496) signatureIndex signatureMasks (rawCells i) q).testBit i))))))
def ridgeTest (i : Nat) := decide (candidateMasks i = RawNatGrowthCheck.mask (candidateRows i)) &&
  (candidateRows i).all (fun c => hasNat (rawCells c).ridgeMasks i)
def kindTest (i : Nat) := decide (kindMasks i = RawNatGrowthCheck.mask (kindRows i)) &&
  (kindRows i).all (fun c => decide ((rawCells c).kind = i))
def badTest (i : Nat) := if badMasks i = 0 then true else
  decide (Nat.land (badMasks i) (SignatureCompatibility.cover (SignatureCompatibility.allMask 496)
    vertexMasks signatureIndex signatureMasks (rawCells i)) = 0)

end Papers.RationalityTen.RootedCaches.RootedSevenPure062

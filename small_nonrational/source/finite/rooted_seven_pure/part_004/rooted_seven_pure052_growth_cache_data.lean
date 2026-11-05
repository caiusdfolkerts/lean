module
prelude
public import RootedSevenPure052
public import SignatureCompatibility
public import PackedRawNatGrowth
public import FiniteChecks
public import RawFacetEmbedding
public import RootedSevenPure052GrowthCachecandidateMasksData000
public import RootedSevenPure052GrowthCachebadMasksData000
public import RootedSevenPure052GrowthCachesignatureMasksData000

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure052
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def rawCells := Papers.RationalityTen.FacetUniverses.RootedSevenPure052.rawCells
def cells (c : Fin 496) := rawCells c.val
def ridgeList := ConcreteGrowth.ridgeList cells
def literalCompatible (a b : Fin 496) := ConcreteGrowth.compatible (cells a) (cells b)
def kind (c : Fin 496) := (cells c).kind
def rawKindCode : Nat := 3669921398255849356061346242236897636592412998643005438713744836347375451881284543414932969672600713012581202394007483859270510198004821538572983214137541807894489267070293401007333407117303147039338188005250255188652815381776368285702440499929723862293775141146343152050622580720933950666871139738785252679654057119048116187911425474088341731234853440042199585049147932278240380952824162296332255058427307293988677204525942174712485389736513971344
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
 (.branch 12
 (.leaf 0x0)
 (.branch 14
 (.leaf 0x0)
 (.branch 15
 (.leaf 0xae56ab156aa54aa14ea652a9146a250a813e9e4ea71369a4ca612e964aa51269248a411e8e46a3116000025)
 (.leaf 0x0)))))
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
 (.leaf 0x0)
 (.branch 60
 (.branch 58
 (.branch 57
 (.leaf 0x162b0d82bf5eaed72b75aacd62af56aad52a752a8d429f4ea6d32974aa4d228f46a2d128742a0d027e000025)
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
 (.leaf 0x11489c4a231087c3a1b0c85c2a130883c1a0b0481c0a03007fbf9fafc7dbe9f2f87bbd9eaf479bc9e2000025)
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
 (.leaf 0x6db69b2000004)
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 120
 (.branch 116
 (.branch 114
 (.branch 113
 (.leaf 0x1b0d7ebb5bacd5eab53a8d3e9b4ba4d1e8b43a0cfe7b3b9ccde6b3398cbe5b2b94c9e4b2390c7e3b1a000025)
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
 (.leaf 0x389c0dc6d359a8d06733194c662291409a4c251188841200f830130903c1c0c0381806020020))
 (.branch 135
 (.leaf 0x5faf978bb5cae16cb55a2cd62b050279369a4c251248f472302e15090401a0b0481808010020)
 (.leaf 0x0))))
 (.branch 140
 (.branch 138
 (.leaf 0x0)
 (.branch 139
 (.leaf 0x351a6d1683399acb6532590c662a893a9c4ca612c914823518250017)
 (.leaf 0x0)))
 (.branch 142
 (.branch 141
 (.leaf 0x3b1d6e974399cae371385c0de6eb65429f4e2692e9549a411c8b0017)
 (.leaf 0x0))
 (.leaf 0x0))))
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
 (.leaf 0x0)
 (.branch 172
 (.branch 170
 (.branch 169
 (.leaf 0x6230f85c260b037fbf5f6f97abcd5aa350a6d329545a250680d90017)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 184
 (.branch 180
 (.branch 178
 (.branch 177
 (.leaf 0xe0f037dbdddeeb71b7db6d767b2d16833b9ccd65b2991c863aab53a853a9749a3d12853f0020)
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
 (.leaf 0x4ea73379b4d26731984be5d2c95c2207027fbf9f8f77b3cde4d90017)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 216
 (.branch 212
 (.branch 210
 (.branch 209
 (.leaf 0xeb757a7d2e873f9bcce5f2b91c7d267f3d9bcd6632792c7e3a0f0581401fafb7cbd9e8f10020)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 240
 (.branch 232
 (.branch 228
 (.branch 226
 (.branch 225
 (.leaf 0x7afd5e8f3f97c9e2f0f83bfddee68f439ece6672f95c96431ad90017)
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
 (.leaf 0x60b017abc5d2e56eb55a2c962af562a94ea65224d229046a2c46210f070320c0501406020020)
 (.leaf 0x0))))
 (.branch 268
 (.branch 266
 (.leaf 0x0)
 (.branch 267
 (.leaf 0x359aad268b3d9ccc653258ec6622b952a852a912a9247a3916260017)
 (.leaf 0x0)))
 (.branch 270
 (.branch 269
 (.leaf 0x3b9daea74b9dcce471385bede6e3695aab5429946964a23d1a8c0017)
 (.leaf 0x0))
 (.leaf 0x0))))
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
 (.leaf 0x0)
 (.branch 300
 (.branch 298
 (.branch 297
 (.leaf 0x62b1386c2e0f0580bf5f6f77abc58abb5cacd629346a1d0a7eda0017)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 312
 (.branch 308
 (.branch 306
 (.branch 305
 (.leaf 0xe1f0b7fbede6ef73b7db6d367b1d76b353a8d36572792c7e36c35fae56aaf4aa450e83400020)
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
 (.leaf 0x4f277389bcd66932984be5b2c954521f0e85c29f6f87abd1e2da0017)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 344
 (.branch 340
 (.branch 338
 (.branch 337
 (.leaf 0xec75fa9d3e8f439dcce5f2791c6d86af55a7d365f2991c863627118743212fc7d3d5e6f20020)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 368
 (.branch 360
 (.branch 356
 (.branch 354
 (.branch 353
 (.leaf 0x7b7d9e9f479bcbe3f0f83bdddedebf5baad46973196c8e3f1cda0017)
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
 (.leaf 0x359a8cf66b3196c863b1982bf5d2e16eb659ac9629248a411e8e468e46e361a0c05e2d148a014090301404010027)
 (.leaf 0x1e0ec180b0004)))
 (.branch 390
 (.branch 389
 (.leaf 0x13c9d4d6673298cba5b2c93c96411e8ec7233188bbe1eef67abd1e6ee7639dcae471b81bede602f97abb5bad968b057a51269047a311672381bcda6934198c4612311484411f0f4180b0200c04010045)
 (.leaf 0xea742411c14090006))
 (.branch 391
 (.leaf 0x186c24b25410070006)
 (.leaf 0x0))))
 (.branch 396
 (.branch 394
 (.branch 393
 (.leaf 0xc56230781c05fef97bbd5d6e76eb65aed567b35968d45a250e854176badd4e87238dc2dd6e355a6d26833196c962b112c9547235188b0030)
 (.leaf 0x0))
 (.branch 395
 (.leaf 0x6c35d28930004)
 (.leaf 0x0)))
 (.branch 398
 (.branch 397
 (.leaf 0x783bd24910004)
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 408
 (.branch 404
 (.branch 402
 (.branch 401
 (.leaf 0x1d8eb7479fcee6f2b93c8e1f0779badcee36bb4d9e532792c8e431f74b95c6df6bb55a2c963a451e8943a04fe4d2491c863b1c8d45a2afa7cbd9eaf278a1d0a84411f8fa7b3b9d89047200fc7c3d0045)
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
 (.leaf 0x7b7d7e6f278fc5dfef77785c0dfef773b8db6cb6396cae4b238ec6e270f86c2602ff7dbcde29549a1506813f0027)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 428
 (.branch 426
 (.branch 425
 (.leaf 0xc662e91470004)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 440
 (.branch 436
 (.branch 434
 (.branch 433
 (.leaf 0x38bc4cc65e8d450006)
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
 (.leaf 0x7b3d5e9f3f8fc5e0ee76fafd5ea74b9dcde5f1f8d98cbe431f8ec6cee73389b4ca632f95ca9f8fb7a3cde4f10027)
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 454
 (.branch 453
 (.leaf 0x9f4f5f4f90004)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 472
 (.branch 468
 (.branch 466
 (.branch 465
 (.leaf 0x3b5d9cb655f0f70006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 496
 (.branch 488
 (.branch 484
 (.branch 482
 (.branch 481
 (.leaf 0xf7fbb29930004)
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
 (.leaf 0x61b097abb5d2e16eb659ac960af55aa550a551a7d3a9c4ca5c48220e86c34180b0441e0e0020)
 (.leaf 0x0))))
 (.branch 524
 (.branch 522
 (.leaf 0x0)
 (.branch 523
 (.leaf 0x361aed26833d9acc65b218ec5622b554a75328d429e4da692e270017)
 (.leaf 0x0)))
 (.branch 526
 (.branch 525
 (.leaf 0x3c1deea7439dcae471b81bedd6e36d5cac53a9548a25026d32980017)
 (.leaf 0x0))
 (.leaf 0x0))))
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
 (.leaf 0x0)
 (.branch 556
 (.branch 554
 (.branch 553
 (.leaf 0x6331786c260f0380bfdf2f779bc586bd5bad55eab52a7d3a96db0017)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 568
 (.branch 564
 (.branch 562
 (.branch 561
 (.leaf 0xe2f137fbdde6eb73b8daed365b1d6eaf55a7d2e873f9ecde66c560add66b156aa53e9b4c0020)
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
 (.leaf 0x4fa7b389b4d6673298cba5b2b9544e210d864260f0480c01fadb0017)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 600
 (.branch 596
 (.branch 594
 (.branch 593
 (.leaf 0xed767a9d2e8f3f9dcde57278fc6d7eb353a8d2e8f419dce666291286c2e150883405fefe0020)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 624
 (.branch 616
 (.branch 612
 (.branch 610
 (.branch 609
 (.leaf 0x7bfdde9f3f9bc9e3f177fbddcedec35da9d3e9b49a2cee6f34db0017)
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
 (.leaf 0x361a6cf6733194c963b1586be5d2e56eb55a2c9609e4ea71369a4c8ec70361a8c05c2c150a02c15090441c0d0027)
 (.leaf 0x1d0e430170004)))
 (.branch 646
 (.branch 645
 (.leaf 0x13e9ccd66932984be5b2b94c92411f8ec6e35188b412070280c01fef075b9dcce471385bedd612fd7abc5bad566b157a813e9c4da612e74389bcdc6933994c661291449c4d2512430170803c1c0d0045)
 (.leaf 0xe6722a14c2c150006))
 (.branch 647
 (.leaf 0x182c05128428130006)
 (.leaf 0x0))))
 (.branch 652
 (.branch 650
 (.branch 649
 (.leaf 0xc661f0782c05fafb7bbcddee56eb6daed368b3592a551a853e9d4d77bb1d4e972389c0de6e35da8d268b3194c86331144a14d26530970030)
 (.leaf 0x0))
 (.branch 651
 (.leaf 0x6b355409f0004)
 (.leaf 0x0)))
 (.branch 654
 (.branch 653
 (.leaf 0x773b53c9d0004)
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 664
 (.branch 660
 (.branch 658
 (.branch 657
 (.leaf 0x1daeaf47a1cee672f93c7e2f0379bbdcedf6db4d96833f9ecee733776b9dc6e16bb4d9ecb63aa54ea14fa652e512591c8a3b1b8cc5e2b0682c0a02fe7ea250c84419f8f87a3c1d8a8532612c94490045)
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
 (.leaf 0x7bfd5e6f2f8fc3e0ef77389c1dfefb73b7daecf63a2d0e7b3b9acce2f1186c2e02fd7cbd5e2ad55a7536994b0027)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 684
 (.branch 682
 (.branch 681
 (.leaf 0xc5626a9530004)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 696
 (.branch 692
 (.branch 690
 (.branch 689
 (.leaf 0x387c2d268ea5510006)
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
 (.leaf 0x7bbd7e9f478fc3dfeef6fb3d6ea74f9dcce57238da4d1e73379acccf675389bcca612e964aa1107803fdfcfd0027)
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 710
 (.branch 709
 (.leaf 0x9e4ee0d050004)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 728
 (.branch 724
 (.branch 722
 (.branch 721
 (.leaf 0x3b1d7d168609030006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 752
 (.branch 744
 (.branch 740
 (.branch 738
 (.branch 737
 (.leaf 0xf6fb3419f0004)
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
 (.leaf 0x35daace66b2d94c96431184c05cae16cb55a2cd5eaa54aa14ea6528f074351a0bc5c2b150a444210f07434190027)
 (.leaf 0x1c0dc48230004)))
 (.branch 774
 (.branch 773
 (.leaf 0x13d9dcd26731984be5d2a9449a3f1e8e46e35198ac421f0e86c3216ef76b99cae371385c0dc61b0578bb5b2d564b1582b156a853a914675399b8da6833990c6622f174b4592b15448230e06c34190045)
 (.leaf 0xe2703017c44210006))
 (.branch 775
 (.leaf 0x17ebe572b4401f0006)
 (.leaf 0x0))))
 (.branch 780
 (.branch 778
 (.branch 777
 (.leaf 0xc5e270581bfdfafb7cbc5dae96db65aad368b3d8ebd5dae56eb559783b9d2e871b89bede6eb61acd16832d94c7633155cad5329548a30030)
 (.leaf 0x0))
 (.branch 779
 (.leaf 0x6a34d58ab0004)
 (.leaf 0x0)))
 (.branch 782
 (.branch 781
 (.leaf 0x763ad54a90004)
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 792
 (.branch 788
 (.branch 786
 (.branch 785
 (.leaf 0x1d9ebf439fcde672f95c6e270b77badc6df6db5d8eb357aad4ea34f77badc2df6ab4d9acb64b057eb95bac55e532791486391b8c45e2d1288c3a1b0a84a291083411f4f8793c1dcc05f2c15cac550045)
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
 (.leaf 0x7bbd9e5f278bc3e0eff6f8bc3df6f771b7da6cf65aed6eab53a6d2e331585c25fefd7bbd5e6c561ad566b1570027)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 812
 (.branch 810
 (.branch 809
 (.leaf 0xc461ec15f0004)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 824
 (.branch 820
 (.branch 818
 (.branch 817
 (.leaf 0x383c0d86bebd5d0006)
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
 (.leaf 0x7bfdbe8f3f8bc3deeef73b5d8e9f4b9bcce4f238fb0d7ea34fa6d2cfa79379b4c6612d964ae29138642e15090027)
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 838
 (.branch 837
 (.leaf 0x9d4e625110004)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 856
 (.branch 852
 (.branch 850
 (.branch 849
 (.leaf 0x3add5d76b6210f0006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 880
 (.branch 872
 (.branch 868
 (.branch 866
 (.branch 865
 (.leaf 0xf5fab59ab0004)
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
 (.leaf 0xf7fbbdbecf5fabc1dfef777b9dbed767b1d7eb75797cae4f238fc6e2f1387c2e0f036db5da6cf65b1c662f1589c461efb7cbddeaf378bbddaeb74b9dcad167b3596c9639f4f6793b9d4e65f2e96cb2572a94ca24f2692c9235198c45e2d15783bddced763adc2e06fb79badc6c35dacd56a34d92c863b198ac461b0982c05faf968b3592c560af45225108743214f67a3c9e0ee763a9d0e672389c0cc653218cc4611e0ec74391c0dc5a2c158a85228009c)
 (.leaf 0x8441a08de6e368d86a340009))
 (.branch 899
 (.leaf 0xd268b417abc5d8cc64310009)
 (.leaf 0x0)))
 (.branch 902
 (.branch 901
 (.leaf 0x4e26f3691c8a42ea74ba174b95c1b0d66a000f)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 908
 (.branch 906
 (.branch 905
 (.leaf 0xc36170971b85bdcee672b3d9ccd000c)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 920
 (.branch 916
 (.branch 914
 (.branch 913
 (.leaf 0x753a7d2dfefb7b6eb6db2411f8f205007f000f)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 944
 (.branch 936
 (.branch 932
 (.branch 930
 (.branch 929
 (.leaf 0x1e9f479f79bbdd60f05810009)
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
 (.leaf 0x1e6f2f93a3d0e7cd669330009)
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
 (.leaf 0x1e3f1787c1dfef777b9dbe773799cbe572791c7e36e771b7db6d769b3d96c755a9d469f4da5cf677399bcd6672591c863f1d8dc05fefd7dbe5eef579bc5aed569b459ecd65b258eb95bad566b157a853e9d4da652e8943a1506813f994c6612f974b6592b95476391b8d46631178b4561d0d8642e15098140600ff7f3f5ecf57a3cde4f17238dc4e17037dbcdd6e33196ca64b218ec662b116eb65aad166b258ac15ea853a994aa451a71369a4ca612e9047a391a8c459f8fa7c3d9e8f2783b9d8d26833998ca6431988c25a2c960ae562a9389a4c259289242209007e3e1e8c05e2e168b0562a148a03c1d0e06c341909044200f070340c050200c040100e1)
 (.branch 4
 (.leaf 0x3dfeef6fb3d7eaf4fa3cfe6f2f93b5d9ec75fadd5ea74fa5d1e873f8bc4e1f0b83c0dfefb7bbcddeeb61afd76b759abd268f45a1d067f3197cb6572993c662f1589c461f0d85c260f0581bbddaeb74b9dcae370b7dbadb6cb1586c15faf576ad55aa54ea551a55269147a35167d3d9e4ee75399c4de6d359a4ce532893c9a4b2491c8a43208fc7a291389446210f8441e0d058240df8fb7d3e5f0f7783bddced763add4e97439dcce56db69b2d86bb59aad469b49a2d067b399ac36130580bf5f2f578bb5d2e570ae56ab156aa54a8942a04fa793a964aa51269248a29128843a190a8441a0902803f9d4e873391c4e06f371b4d86b35180be5e2e970b65429948a250279208e4622910863c1d8e872381b8d86a34198c8622713094482311084401f0c05c2c150a04c180b050241007010e)
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
 (.leaf 0xff8007fc003fe07e07e07e001ff000ff81f81f81f8007fc003fe07e07e07e001ff0001ff000ff81f81f81f8007fc003fe07e07e07e001ff007e07e07e)
 (.branch 4
 (.leaf 0xfff007ff803ffc01f81f81f81ffe00fff007e07e07e07ff803ffc01f81f81f81ffe00fffe00fff007e07e07e07ff803ffc01f81f81f81ffe00ff81f81f80)
 (.leaf 0x0))))
def kindMasks := kindMaskTable.get
def keys := List.range 5
def vertexMaskTable : Table Nat :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf 696898287454081973172991196020261297061887)
 (.leaf 210624583337114373395835358469053410555817017812208045256538587135))
 (.branch 3
 (.leaf 1067993517960455041197510853084565432818448774571117440442628138670711708413131587989028972003327)
 (.branch 4
 (.leaf 322781234760863573706988828506858523836172026596333548457331786440906493725965153595462198783868193058561052291926851585)
 (.leaf 97554642197374757230674590649955600277774650901738820079554088808918863097036343935661199995985477390635582026129084133548101569315092303970305))))
 (.branch 7
 (.branch 6
 (.leaf 204586815438913187179422044217806672546883892211488000300771087707839006398351403358490326598226643243004477007248433717533463214493253650778737868801)
 (.leaf 204586912993462349219650794763373527931701745486930597094605850970569457467318750886141964356019129819580062884160419993137170901395973087576918589441))
 (.branch 8
 (.leaf 204586912993508866853648413869254757853435355120712530430706550332112787317463624983875185463015699842222539612096595925949882717513872649157703892990)
 (.branch 9
 (.leaf 204586912993508866875818942003340554877514711673405177511916648211044032300937221072047970390839851376889876919169571632630218533561614171577142747134)
 (.leaf 204586912993508866875824354729935790667803793547563549740207959270096505749419514430889132194316933404238500080014533057912156958529349348143623299072)))))
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

end Papers.RationalityTen.RootedCaches.RootedSevenPure052

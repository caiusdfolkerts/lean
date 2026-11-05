module
prelude
public import RootedSevenMixed024
public import SignatureCompatibility
public import PackedRawNatGrowth
public import FiniteChecks
public import RawFacetEmbedding
public import RootedSevenMixed024GrowthCachecandidateMasksData000
public import RootedSevenMixed024GrowthCachebadMasksData000
public import RootedSevenMixed024GrowthCachesignatureMasksData000

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenMixed024
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def rawCells := Papers.RationalityTen.FacetUniverses.RootedSevenMixed024.rawCells
def cells (c : Fin 466) := rawCells c.val
def ridgeList := ConcreteGrowth.ridgeList cells
def literalCompatible (a b : Fin 466) := ConcreteGrowth.compatible (cells a) (cells b)
def kind (c : Fin 466) := (cells c).kind
def rawKindCode : Nat := 3952718528965445735213134598124983447118885085241084845489633178566306505861063985618090918416996379112230725492546709910512139476907924484146307522322796379861308264888678936669952004101333422363957243903208200387471237486361452980918615001335278486474400922745026346202287579581491531735655212056785222315744603193118710246107308286340092847930983572541585902908371677096459322167443711792729933391147831388769320772752
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
 (.leaf 0x66f3599cc65f2c241188842200f8783a1c0d86832180b8582a14098482210078381a0c058281208038180a04018080200002b))))
 (.leaf 0x0))
 (.branch 24
 (.branch 20
 (.leaf 0x0)
 (.branch 22
 (.branch 21
 (.leaf 0x0)
 (.leaf 0x687419fcf67738602f978ba5c2d968b2582b958aa5429948a250279389a4c259289248239188a442190882401f8f87a00002b))
 (.leaf 0x0)))
 (.branch 28
 (.branch 26
 (.leaf 0x0)
 (.branch 27
 (.leaf 0x0)
 (.leaf 0xd6eb357aad4ea34fa6d2e9347a2138984a000010)))
 (.leaf 0x0))))
 (.branch 48
 (.branch 40
 (.leaf 0x0)
 (.branch 44
 (.leaf 0x0)
 (.branch 46
 (.leaf 0x0)
 (.branch 47
 (.leaf 0xdcee36fb6daed367b2d8ec35fae46a3116000010)
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
 (.leaf 0x6ff7dbdde6ef74db6d365b0d76b355a8d369345a0cf6733598cb6532590c76331588c36130580bf5f2f578bb5d2e57000002b)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 112
 (.branch 104
 (.branch 100
 (.leaf 0x0)
 (.branch 102
 (.branch 101
 (.leaf 0x71789c3e1707811489c4a231087c3a1b0c85c2a130883c1a0b0481c0a03007fbf9fafc7dbe9f2f87bbd9eaf479bc9e200002b)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 120
 (.leaf 0x0)
 (.branch 124
 (.branch 122
 (.branch 121
 (.leaf 0xe8f439fcee6f3397cae4f238fc6a0d027e000010)
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
 (.leaf 0x1a6d10e06e351a0c8622f170b4582a148942c14088401c0a0401408020019)))
 (.branch 134
 (.branch 133
 (.leaf 0x0)
 (.leaf 0x389c0dc6d359a8d06733194c662291409a4c251188841200f830130903c1c0c0381806020020))
 (.branch 135
 (.leaf 0x1b2d72793a9b4d2612e954a24d249047a2c2e15090401a0b0481808010019)
 (.leaf 0x0))))
 (.branch 140
 (.branch 138
 (.leaf 0x0)
 (.branch 139
 (.leaf 0x369b0d4e9566b2582bd5aac552a550a752a9116250012)
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 152
 (.branch 148
 (.branch 146
 (.branch 145
 (.leaf 0x0)
 (.leaf 0x1a8d22190a8341200fe7d3e1ecf4783b9509e4e259289043210fc7c250019))
 (.leaf 0x0))
 (.branch 150
 (.branch 149
 (.leaf 0x763add2e873395c6e270b81bcdd66b2d90c762b057ebc5dae4a65127130924722908803d0020)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 156
 (.branch 154
 (.branch 153
 (.leaf 0x395c6d3e8ea551a7d3a994ba4d228f46a250e7e250012)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 176
 (.branch 168
 (.branch 164
 (.leaf 0x0)
 (.branch 166
 (.branch 165
 (.leaf 0x1b5d8c96492290c7e3d1c8dc6a33178b41a0901803f9f4f87abd1e48b0019)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 172
 (.branch 170
 (.branch 169
 (.leaf 0x399c8d9ebecf66b258ec360af576b95bacd627e8b0012)
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
 (.leaf 0x9d4e66f369a4ce633097cba592b8440e04ff7f3f1eef679bc99eca64b198ac35f2f574b90020)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 216
 (.branch 212
 (.branch 210
 (.branch 209
 (.leaf 0x1cde4df2f779bc5daeb73b95c6e16eb6cfd9ccc64b1d88c2602f576b80019)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 240
 (.branch 232
 (.branch 228
 (.branch 226
 (.branch 225
 (.leaf 0x1cbe3e47218ec6e2f1588c3e1b0b83c14fe0f0581401fafb7cbd9e8f10019)
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
 (.leaf 0x1aad18e872361a8cc6430170b4562a1409844200e87034090381806010019)))
 (.branch 262
 (.branch 261
 (.leaf 0x0)
 (.leaf 0x399c8de6e361acd26733190c6612f170b2582b11486421f8f4481f0f06c340b0401408010020))
 (.branch 263
 (.leaf 0x1b6d7a813e9c4da6530964a24d22904723046210f070320c0501406020019)
 (.leaf 0x0))))
 (.branch 268
 (.branch 266
 (.leaf 0x0)
 (.branch 267
 (.leaf 0x371b1d6e916ab458ac15cad55aa550a652a8d18260012)
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 280
 (.branch 276
 (.branch 274
 (.branch 273
 (.leaf 0x0)
 (.leaf 0x1acd2a210e8441a05007e3e1ecf2783b180b65a2b9588e44209007a260019))
 (.leaf 0x0))
 (.branch 278
 (.branch 277
 (.leaf 0x773b5d4e973b99c8e270b7dbcdc6cb5da8d368b017cbd5d2e0be5d2d160aa48231047e3e0020)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 284
 (.branch 282
 (.branch 281
 (.leaf 0x39dc7d5e8aa953a853e9b4ca55228f45a250a80260012)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 304
 (.branch 296
 (.branch 292
 (.leaf 0x0)
 (.branch 294
 (.branch 293
 (.leaf 0x1b9d849e4d23914823f1d8dc6a31178ac4a210d86429f2f77b3cde28c0019)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 300
 (.branch 298
 (.branch 297
 (.leaf 0x3a1c9dbebad368b2d92c561afd76b95aacd5e808c0012)
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
 (.leaf 0x9e4ee71379acd2653097cb6592a8a43e1d0b853edf0f57a3c5b6d66ab49a2c25faf176b80020)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 344
 (.branch 340
 (.branch 338
 (.branch 337
 (.leaf 0x1d1e45fafb7abcddeed74b95c6df6eb6501b4d86ab4da0c360af174b90019)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 368
 (.branch 360
 (.branch 356
 (.branch 354
 (.branch 353
 (.leaf 0x1cfe364f258fc76331789c3e1b0983c0d0227118743212fc7d3d5e6f20019)
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
 (.leaf 0xb559ab958ab5529d4ca55027932974b2552491480e46e361a0c05e2d148a014090301404010021)
 (.leaf 0xd2e9331961e0ec180b0008)))
 (.branch 390
 (.branch 389
 (.leaf 0x13c9d4d6673298cba5b2c93c96411e8ec7233188bbe1eef67abd1e6ee7639dcae471b81bede5faf97abc5dae93e9d4e2692c9549a3d1c72381bcda6934198c4612311484411f0f4180b0200c04010045)
 (.leaf 0x33d9ccde68ea742411c1409000a))
 (.branch 391
 (.leaf 0xd8ec333975128410070008)
 (.leaf 0x0))))
 (.branch 396
 (.branch 394
 (.branch 393
 (.leaf 0x5a6cf62b057ebd5bad566a952a6d2e9549a351688b4592c55eab552a148a3001b)
 (.leaf 0x0))
 (.branch 395
 (.leaf 0x35faed1e896eb60006)
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 408
 (.branch 404
 (.branch 402
 (.branch 401
 (.leaf 0xbf5f2ef75ba5cee16fb754ea350a752a9347a1d09daeb753a1c8e370b75b8c1602f578b95c21d0a84411f8fa7b3b9d89047200fc7c3d0030)
 (.leaf 0xd1e8b43a0452248c450008))
 (.leaf 0x0))
 (.branch 406
 (.branch 405
 (.leaf 0x379bacfe75e0ef61b088843000a)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 412
 (.branch 410
 (.branch 409
 (.leaf 0x393c8d2e92ad550006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 432
 (.branch 424
 (.branch 420
 (.branch 418
 (.branch 417
 (.leaf 0x193c8e331589c46170983b459acb63afd7ab958abc9a492390c76391a8b455f4f97b3d5e4f10021)
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 422
 (.branch 421
 (.leaf 0xe17035fae94ca1f8fb0008)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 428
 (.branch 426
 (.branch 425
 (.leaf 0x38fc6d8ec2d76a0006)
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
 (.leaf 0x64b218fc6e271186c1606fb7bbd5e2e973b8db6d93b9cce26d3298cbe572a7e3ede8f3793c586c25dae972b80027)
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 454
 (.branch 453
 (.leaf 0x38bc4dfefa7d3d7d3e582c0000a)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 472
 (.branch 468
 (.branch 466
 (.branch 465
 (.leaf 0xe3f1b7bbbc05fd7ebe0008)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 496
 (.branch 488
 (.branch 484
 (.branch 482
 (.branch 481
 (.leaf 0xe4f2387c1cae51f0f70008)
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
 (.leaf 0x1abd38f076361a0cc6230178b056291409c421f0f06c3215098481e0d0019)))
 (.branch 518
 (.branch 517
 (.leaf 0x0)
 (.leaf 0x3a9d0de6d361a8d26832990c4612e96cb4572a9449e4e2592446200e87032170a044200d0020))
 (.branch 519
 (.leaf 0x1b7d9a89429c4d2652e964aa49228f4723448220e86c34180b0441e0e0019)
 (.leaf 0x0))))
 (.branch 524
 (.branch 522
 (.leaf 0x0)
 (.branch 523
 (.leaf 0x373b5d66a16eb658abd5cac55aa94ea65228d1a270012)
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 536
 (.branch 532
 (.branch 530
 (.branch 529
 (.leaf 0x0)
 (.leaf 0x1add4a29128441204fe7e3e9e8f2773b17cb8592c154a6502693092270019))
 (.leaf 0x0))
 (.branch 534
 (.branch 533
 (.leaf 0x783bdd4e873b95c8e37037dbadc6c359aad26833194c963310c05e2c95cac5429134964a0020)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 540
 (.branch 538
 (.branch 537
 (.leaf 0x39fcbd569aad55a853a9b4ba55268d45a1d0a82270012)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 560
 (.branch 552
 (.branch 548
 (.leaf 0x0)
 (.branch 550
 (.branch 549
 (.leaf 0x1b8da4a6512390c823d1d8e46631168ac461f0e85c260b03813fdfa8d0019)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 556
 (.branch 554
 (.branch 553
 (.leaf 0x3a3cddb6cad76ab2d8ec560afd7ab75aac55e828d0012)
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
 (.leaf 0x9f4f671369acce6531974b6572a89c421b0c84c1e0901803f5b4d76a34da0ce65b218ec40020)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 600
 (.branch 596
 (.branch 594
 (.branch 593
 (.leaf 0x1d0e6602ff7abc5deeb74b9dc2df6db6505b6d96a349a2cf66b218cc50019)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 624
 (.branch 616
 (.branch 612
 (.branch 610
 (.branch 609
 (.leaf 0x1cee5657298fc6e331589c46170982c0d06291286c2e150883405fefe0019)
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
 (.leaf 0xb7592b95aab54aa14ca45127532984b2512691478ec70361a8c05c2c150a02c15090441c0d0021)
 (.leaf 0xd4ea335971d0e430170008)))
 (.branch 646
 (.branch 645
 (.leaf 0x13e9ccd66932984be5b2b94c92411f8ec6e35188b412070280c01fef075b9dcce471385bedd65b2992c863b19429e4e26d2c94492411c74389bcdc6933994c661291449c4d2512430170803c1c0d0045)
 (.leaf 0x3419dcce60e6722a14c2c15000a))
 (.branch 647
 (.leaf 0xdaed337965027c28130008)
 (.leaf 0x0))))
 (.branch 652
 (.branch 650
 (.branch 649
 (.leaf 0x5aecd62b0d7ebb5cad562ad51a6d329548a3d1686b659ac560ab54a9d4aa3001b)
 (.leaf 0x0))
 (.branch 651
 (.leaf 0x367b2d3e996ab40006)
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 664
 (.branch 660
 (.branch 658
 (.branch 657
 (.leaf 0xc05eeef76ba5cae36fb6d56a550a7d2a9146a2509deec753a5c8e270379b8cd6632590c5622250c84419f8f87a3c1d8a8532612c94490030)
 (.leaf 0xd3e9b3f9e4421ca4510008))
 (.leaf 0x0))
 (.branch 662
 (.branch 661
 (.leaf 0x37dbbd0e71dced67b38a04f000a)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 668
 (.branch 666
 (.branch 665
 (.leaf 0x39bccd4ea2a9530006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 688
 (.branch 680
 (.branch 676
 (.branch 674
 (.branch 673
 (.leaf 0x195c86331789c3e1b0982b559ecb64afd76b759abca24b239147637198bc560d0581405fcfd0021)
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 678
 (.branch 677
 (.leaf 0xe270767b293c9a11070008)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 684
 (.branch 682
 (.branch 681
 (.leaf 0x397cadaed2d3680006)
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
 (.leaf 0x653238fc76270f85c1e06ff7cbd5e6e972b85bad93d9d4e26f32984ba592a8441e00ff7f3f59ece63b198ac40027)
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 710
 (.branch 709
 (.leaf 0x387c2deef2793b834159acc000a)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 728
 (.branch 724
 (.branch 722
 (.branch 721
 (.leaf 0xe5f2b7fbabf5f596ca0008)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 752
 (.branch 744
 (.branch 740
 (.branch 738
 (.branch 737
 (.leaf 0xe6f338bc0c9e4a09030008)
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
 (.leaf 0xb65a2b558aa54aa14ea350a7d30974aa512692470f074351a0bc5c2b150a444210f07434190021)
 (.leaf 0xd6eb337991c0dc48230008)))
 (.branch 774
 (.branch 773
 (.leaf 0x13d9dcd26731984be5d2a9449a3f1e8e46e35198ac421f0e86c3216ef76b99cae371385c0dc6bb59aad469b4944a04da692a9448a411e75399b8da6833990c6622f174b4592b15448230e06c34190045)
 (.leaf 0x3439fcbe58e2703017c4421000a))
 (.branch 775
 (.leaf 0xdcee335984f274401f0008)
 (.leaf 0x0))))
 (.branch 780
 (.branch 778
 (.branch 777
 (.leaf 0x5aad161b057abb5cadd5eab53a652e9348a3d1a84b75aac15eaa54a994aa4001b)
 (.leaf 0x0))
 (.branch 779
 (.leaf 0x36fb6d5ea966b20006)
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 792
 (.branch 788
 (.branch 786
 (.branch 785
 (.leaf 0xbfdf6ed75b9dcae370b655aa94fa75269145a250de0ee74ba1c6e26fb79bad96c355a8d1682291083411f4f8793c1dcc05f2c15cac550030)
 (.leaf 0xd5eab3b9c43214bc5d0008))
 (.leaf 0x0))
 (.branch 790
 (.branch 789
 (.leaf 0x37fbdd0679d8eb6db68b85b000a)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 796
 (.branch 794
 (.branch 793
 (.leaf 0x3a3d0d6eb2a5510006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 816
 (.branch 808
 (.branch 804
 (.branch 802
 (.branch 801
 (.leaf 0x194c962f1588c3e1b0b81b5da6c963af576b559ac4a64f2290c7237188bc5a25118743615090021)
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 806
 (.branch 805
 (.leaf 0xe2f0f6fb692c9229130008)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 812
 (.branch 810
 (.branch 809
 (.leaf 0x39fcedcee2cf660006)
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
 (.leaf 0x657278ec6e230f84c1e0b017ebcde2e772b7dbadb3e9e4de6d31984b6592b8a44e190b85425b6da69b49a2d00027)
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 838
 (.branch 837
 (.leaf 0x383c0ddeea753989445b2d8000a)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 856
 (.branch 852
 (.branch 850
 (.branch 849
 (.leaf 0xe7f3b7dbcbe5edaed60008)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 880
 (.branch 872
 (.branch 868
 (.branch 866
 (.branch 865
 (.leaf 0xe8f4389c2c8e42210f0008)
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
 (.leaf 0xe2f1387c2e0f037fbedeef377bad0e833f9ecee73379acce632f96cae532792c8e430d85c260f0581c05fefd7dbe5eee370b7dbadb6cb5daad368b3d9ab95bad566b157ab556a953a95468f46a2d1287429f4f6793b9d4e65f2e96cb2572a94ca24f2692c9235198c45e2d15783bddced763adc2e06fb79badc5bad96ab459ac950a75329548a351285409f4f275269248a411e8e45225108743214f67a3c9e0ee763a9d0e672389c0cc653218cc4611e0ec74391c0dc5a2c158a8522800a8)
 (.leaf 0x8441a08de6e368d86a340009))
 (.branch 899
 (.leaf 0xb1582bd389b4d0cc64310009)
 (.leaf 0x0)))
 (.branch 902
 (.branch 901
 (.leaf 0x4e26f3691c8a42ea74ba132984b9b0d66a000f)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 908
 (.branch 906
 (.branch 905
 (.leaf 0x165b258ea14fa72b95aac0009)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 920
 (.branch 916
 (.branch 914
 (.branch 913
 (.leaf 0xbd5e6f14da652dcee672a05007f000c)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 944
 (.branch 936
 (.branch 932
 (.branch 930
 (.branch 929
 (.leaf 0x18fc7636c561b04823f1e0009)
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
 (.leaf 0x18cc5e2aef76bacd669330009)
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
 (.leaf 0xc4e230f86c2e130782c0dd2e772b8dc2df6eb6db2bf5eaed72b75aacd62af4aa4d228f46a2d128742994c6612f974b6592b95476391b8d46631178b4561d0d8642e15098140600ff7f3f5ecf57a3cde4f17238dc4e17037dbcdd6e355a8d369345a0c96431d8cc5622f578bb5d2e570ab552a550a75329548a34b255289349245208f471f8fa7c3d9e8f2783b9d8d26833998ca6431988c25a2c960ae562a9389a4c259289242209007e3e1e8c05e2e168b0562a148a03c1d0e06c341909044200f070340c050200c040100b4)
 (.branch 4
 (.leaf 0x195ca64f2591c863f1d8dc662f1580bfdfafb7cbddeaf378bbddaeb6bb55a6d167b3596c963b1586c156aad52a752a8d429f4ea6d329741a04fe7d3d9e4ee75399c4de6d359a4ce532893c9a4b2491c8a43208fc7a291389446210f8441e0d058240df8fb7d3e5f0f7783bddced763add4e97439dcce56db69b2d86bb599ece66b3196ca61b0982c05faf96eb65aad166b258ac15eae56ab144a15027d3c9d4e26d34994c25d1a8c45a29128843a190a8441a0902803f9d4e873391c4e06f371b4d86b35180be5e2e970b65429948a250279208e4622910863c1d8e872381b8d86a34198c8622713094482311084401f0c05c2c150a04c180b05024100700e1)
 (.leaf 0xe8f439fcee6f3397cae4f238fc6e2f1387c2e0f037fbedeef377badcee36fb6daed367b2d8ec35faed6eb357aad4ea34fa6d2e9347a2d0e833f9ecee73379acce632f96003c))))
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
 (.leaf 0x3fe001ff000ff8007fc0007fc003fe07e07e07e001ff03f03f03f000ff8007fc0007fc003fe07e07e07e001ff007e07e07e)
 (.branch 4
 (.leaf 0x3ffc01ffe00fff007ff803fff803ffc01f81f81f81ffe00fc0fc0fc0fff007ff803fff803ffc01f81f81f81ffe00ff81f81f80)
 (.leaf 0x3ffffffffffffffc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))))
def kindMasks := kindMaskTable.get
def keys := List.range 5
def vertexMaskTable : Table Nat :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf 2772669528856822662016264446164256695243677118274645834100174759452422489204177813962138646705124422250543172054796585834431643647)
 (.leaf 11356854400609177132065034604981461525234245353750323093161745018450341041352228057889474592680369732142330884288018515630379994447871))
 (.branch 3
 (.leaf 46517675582925902922390881129595129352148960993093570231424677986177077804855633543770039310538153082275439030182207017016691743885623295)
 (.branch 4
 (.leaf 190489904220247044072712407189944976533522131790686507420615876070504917181888319342244051954160174043224415490397250867128554081652672823297)
 (.leaf 190490608348034541480425061081487265196915987449609427959872907953928498941229927512536964235557330622656059795199624549203069426189153075201))))
 (.branch 7
 (.branch 6
 (.leaf 190535695057105674699272154338378590327421206107156934597481584340500433117587906025950311170313841701778764180960326432560840304424965373953)
 (.leaf 190536399184892505762568267659333135460184565800864207547527895794447377254296102843892600866461302382858915542669249298232376139894644277249))
 (.branch 8
 (.leaf 11908515009208220032592796556471835883774491477649882135378437218468034791164077157426380509056663108721918002575312496549143673531799699454)
 (.branch 9
 (.leaf 179372167070963863173438868811335484105486801580398383561150732262598447667232811046661387104323164532404188843276238091726890952957636911102)
 (.leaf 189838645324823590869741748327264462119343823031057605948628032588707649197031849052237011398155434454064486315099813074861961163124338843648)))))
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
def candidateMasks (i : Nat) := PackedRawNatGrowth.take 466
  (PackedRawNatGrowth.drop (466*(i%64)) (candidateMasksBlocks.get (i/64)))

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
def badMasks (i : Nat) := PackedRawNatGrowth.take 466
  (PackedRawNatGrowth.drop (466*(i%64)) (badMasksBlocks.get (i/64)))

def signatureMasksBlocks : Table Nat :=
(.branch 2
 (.branch 1
 (.leaf signatureMasksBlock0000)
 (.leaf signatureMasksBlock0001))
 (.branch 3
 (.leaf signatureMasksBlock0002)
 (.leaf signatureMasksBlock0003)))
def signatureMasks (i : Nat) := PackedRawNatGrowth.take 466
  (PackedRawNatGrowth.drop (466*(i%64)) (signatureMasksBlocks.get (i/64)))

def fastKind := rawKind
def candidateSupports := candidateRows
def kindSupports := kindRows
def wellFormedTest (i : Nat) : Bool := RawFacetEmbedding.wellFormedCheck (rawCells i)

def cellTest (i : Nat) := (listBounds 1024 (rawCells i).ridgeMasks && ((rawCells i).ridgeMasks.all (fun q => (candidateMasks q).testBit i) && (decide (rawKind i = (rawCells i).kind) && (decide ((rawCells i).vertices < 1024) && ((List.range 10).all (fun v => decide ((vertexMasks v).testBit i = (rawCells i).vertices.testBit v)) && (SignatureCompatibility.faces (rawCells i)).all (fun q => (SignatureCompatibility.profileMask (SignatureCompatibility.allMask 466) signatureIndex signatureMasks (rawCells i) q).testBit i))))))
def ridgeTest (i : Nat) := decide (candidateMasks i = RawNatGrowthCheck.mask (candidateRows i)) &&
  (candidateRows i).all (fun c => hasNat (rawCells c).ridgeMasks i)
def kindTest (i : Nat) := decide (kindMasks i = RawNatGrowthCheck.mask (kindRows i)) &&
  (kindRows i).all (fun c => decide ((rawCells c).kind = i))
def badTest (i : Nat) := if badMasks i = 0 then true else
  decide (Nat.land (badMasks i) (SignatureCompatibility.cover (SignatureCompatibility.allMask 466)
    vertexMasks signatureIndex signatureMasks (rawCells i)) = 0)

end Papers.RationalityTen.RootedCaches.RootedSevenMixed024

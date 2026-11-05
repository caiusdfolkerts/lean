module
prelude
public import RootedSevenMixed025
public import SignatureCompatibility
public import PackedRawNatGrowth
public import FiniteChecks
public import RawFacetEmbedding
public import RootedSevenMixed025GrowthCachecandidateMasksData000
public import RootedSevenMixed025GrowthCachebadMasksData000
public import RootedSevenMixed025GrowthCachesignatureMasksData000

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenMixed025
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def rawCells := Papers.RationalityTen.FacetUniverses.RootedSevenMixed025.rawCells
def cells (c : Fin 466) := rawCells c.val
def ridgeList := ConcreteGrowth.ridgeList cells
def literalCompatible (a b : Fin 466) := ConcreteGrowth.compatible (cells a) (cells b)
def kind (c : Fin 466) := (cells c).kind
def rawKindCode : Nat := 3952718528965445735213134598124983447118885085241084845489633178566306505861063985618090918416996379112230725492546709910512139476907924484146307522322796379861308264888678936669952004101333422363957243903208200387471237486361455588007648732317933741440920624313657835911823328174594433947805279958912489732082594937204320465147289162731475534951227111226266013261860999040167007177878006000666287921929091101064243520656
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
 (.leaf 0x0)
 (.branch 28
 (.branch 26
 (.leaf 0x0)
 (.branch 27
 (.leaf 0x0)
 (.leaf 0xd3e9b4ba4d1e8b43a0cfe7b3b9c138984a000010)))
 (.leaf 0x0))))
 (.branch 48
 (.leaf 0x0)
 (.branch 56
 (.branch 52
 (.leaf 0x0)
 (.branch 54
 (.branch 53
 (.leaf 0x0)
 (.leaf 0xd9ecb63b0d7ebb5bacd5eab53a81f8f87a000010))
 (.leaf 0x0)))
 (.leaf 0x0))))
 (.branch 96
 (.branch 80
 (.branch 72
 (.branch 68
 (.leaf 0x0)
 (.branch 70
 (.leaf 0x0)
 (.branch 71
 (.leaf 0x6e771b7db6d7688d4622d14894421d0c854220d0481401fcfc7d3e1ecf4793c1dcec753a1cce471381bcdc6d361acd400002b)
 (.leaf 0x0))))
 (.branch 76
 (.branch 74
 (.leaf 0x0)
 (.branch 75
 (.leaf 0x6ff7dbdde6ef74c662b1186c260b017ebe5eaf176ba5cae16eb65aad166b258ac15eae56ab156aa54aa14ea652a914600002b)
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.leaf 0x0))
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
 (.leaf 0x1a0ce0e06e351a0c8622f170b4582a148942c14088401c0a0401408020019)))
 (.branch 134
 (.branch 133
 (.leaf 0x0)
 (.leaf 0x1acd41409e4d261289247231148842208f430130903c1c0c0381806020019))
 (.branch 135
 (.leaf 0x4f275369a4c25d2a9449a49208f3f9f4f4793b9cce26e369ac2e15090401a0b0481808010020)
 (.leaf 0x0))))
 (.branch 140
 (.branch 138
 (.leaf 0x0)
 (.branch 139
 (.leaf 0x1a3cfb5dacd469b45a0ce66b3196c9642e16cb3592c158aa53a9948250019)
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 152
 (.branch 148
 (.branch 146
 (.branch 145
 (.leaf 0x0)
 (.leaf 0x35daad1678ca6431184be5e2e16cb4592b9587a250012))
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 156
 (.branch 154
 (.branch 153
 (.leaf 0x395c6d0e76a551a7d3a994ba4d228f46a250e7e250012)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 176
 (.branch 168
 (.branch 164
 (.leaf 0x0)
 (.branch 166
 (.branch 165
 (.leaf 0x1afd5c96492290c7e3d1c8dc6a33178b41a0901803f9f4f87abd1e43d0019)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 184
 (.branch 180
 (.branch 178
 (.branch 177
 (.leaf 0x39bc9d6ea6f97bbcde2ed75b9dcae370b75b67e3d0012)
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
 (.leaf 0x763add2e873395c6e270b81bcdd5d2d568b1582b952a852a91027c3d9e0ee75381bcd86b0020)
 (.leaf 0x0)))
 (.branch 198
 (.branch 197
 (.leaf 0x9d4e66f369a4ce633097cba592b8440e04ff7f3f1eef679bc9007e3d9e4ec74391bcda6a0020)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 204
 (.branch 202
 (.branch 201
 (.leaf 0x1cce459ecd64b1d86c15eaed72b759ac4fd72b75a2c95ead55aa14ca30019)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
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
 (.leaf 0x1a4ce8e872361a8cc6430170b4562a1409844200e87034090381806010019)))
 (.branch 262
 (.branch 261
 (.leaf 0x0)
 (.leaf 0x1b0d4948a24e2692c9448231148642200f8481f0f06c340b0401408010019))
 (.branch 263
 (.leaf 0x5027d389b4ca612c9449a45208e45a250c85419c8e06f361a846210f070320c0501406020020)
 (.leaf 0x0))))
 (.branch 268
 (.branch 266
 (.leaf 0x0)
 (.branch 267
 (.leaf 0x1a7cf365b0d56a349a2cf66b3194c963b1184bf5f2f156a95429546260019)
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 280
 (.branch 276
 (.branch 274
 (.branch 273
 (.leaf 0x0)
 (.leaf 0x365abd367cce6631988c05f2e96cb4582b9547c260012))
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 284
 (.branch 282
 (.branch 281
 (.leaf 0x39dc7d2e72a953a853e9b4ca55228f45a250a80260012)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 304
 (.branch 296
 (.branch 292
 (.leaf 0x0)
 (.branch 294
 (.branch 293
 (.leaf 0x1b3d549e4d23914823f1d8dc6a31178ac4a210d86429f2f77b3cde23e0019)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 312
 (.branch 308
 (.branch 306
 (.branch 305
 (.leaf 0x3a3c8d8ea2fd7dbd5e6ef76ba5cae36fb75b2803e0012)
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
 (.leaf 0x773b5d4e973b99c8e270b7dbcdc6330580bd5e2b554a75328d1a8843a110674389b8da6a0020)
 (.leaf 0x0)))
 (.branch 326
 (.branch 325
 (.leaf 0x9e4ee71379acd2653097cb6592a8a43e1d0b853edf0f57a3c5188a43a150475399b8d86b0020)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 332
 (.branch 330
 (.branch 329
 (.leaf 0x1d0e4da6d165b258ac35faed72b559abd018ac3602f976ae5629d4aa40019)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
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
 (.leaf 0x6732980bc5d2e164b0572914096492411c8843210e87033188c05e2c158a810070301408030021))
 (.branch 387
 (.leaf 0x1dcec73b95c8e37037dbcd96bb49a0cf6732d94c9552a550a753295409e4ca5d2c95492452071381bcdc6d360e46e361a0c05e2d148a014090301404010036)
 (.leaf 0xcfe7b31961e0ec180b0008)))
 (.branch 390
 (.branch 389
 (.leaf 0x2793a9acce6531974b6592792c823d1d8e46631177c3ddecf57a3cd3e9d4e2692c9549a3d1c73391bcdc6b351449e4e261208e4520900180b0200c04010036)
 (.leaf 0xd5eab379a2a14c14090008))
 (.branch 391
 (.leaf 0x36db4cce5d44a13a9d01007000a)
 (.leaf 0x0))))
 (.branch 396
 (.branch 394
 (.branch 393
 (.leaf 0x169b3d8ac15faf56eb559aa54a9b4ba55268d45a2361acd569b3d9ccc6431d58ab5429d48a30021)
 (.leaf 0x0))
 (.branch 395
 (.leaf 0xde6eb3b9c6db695cad0008)
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 408
 (.branch 404
 (.branch 402
 (.branch 401
 (.leaf 0x5faf977badd2e770b7dbaa751a853a9549a3d0e84663218cc25d2e168ac55001b)
 (.leaf 0x353a8cee70d2680006))
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 412
 (.branch 410
 (.branch 409
 (.leaf 0x393c8cfe7aad550006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 432
 (.branch 424
 (.branch 420
 (.branch 418
 (.branch 417
 (.leaf 0x193c8e331589c46170983bedeef578ba5cee36db649a492390c76391a8b455f4f97b3d5e4f10021)
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 422
 (.branch 421
 (.leaf 0xe170353a894ca1f8fb0008)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 440
 (.branch 436
 (.branch 434
 (.branch 433
 (.leaf 0x38fc6d5eab017f0006)
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
 (.leaf 0x32590c7e371388c360b0368b3596c75faf572b1579dce67136994c65f2b953f1f6f479bc9e2ed75ba9d0e471b85badc572b54ca55228cea74369b0d66a0036)
 (.leaf 0x0))
 (.branch 451
 (.leaf 0x37fbedcee1e0ef562ace672000a)
 (.leaf 0x0)))
 (.branch 454
 (.branch 453
 (.leaf 0x38bc4dbed67d3d7d3e4e270000a)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 460
 (.branch 458
 (.branch 457
 (.leaf 0xe3f1b7bbbb5da954a90008)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
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
 (.leaf 0x1a5d08f076361a0cc6230178b056291409c421f0f06c3215098481e0d0019)))
 (.branch 518
 (.branch 517
 (.leaf 0x0)
 (.leaf 0x1b1d6950a64e2612c9248239108641200fc46200e87032170a044200d0019))
 (.branch 519
 (.leaf 0x51285389a4ca5d2c95492451e8e452210e84411f8f87b3c1d848220e86c34180b0441e0e0020)
 (.leaf 0x0))))
 (.branch 524
 (.branch 522
 (.leaf 0x0)
 (.branch 523
 (.leaf 0x1a6d136db4d569b49a0cf6732d94c863b0d82c05eaed6eb55a2c55e270019)
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 536
 (.branch 532
 (.branch 530
 (.branch 529
 (.leaf 0x0)
 (.leaf 0x367afd3e8cd26831984c05e2e970b2582b1547e270012))
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 540
 (.branch 538
 (.branch 537
 (.leaf 0x39fcbd2682ad55a853a9b4ba55268d45a1d0a82270012)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 560
 (.branch 552
 (.branch 548
 (.leaf 0x0)
 (.branch 550
 (.branch 549
 (.leaf 0x1b2d74a6512390c823d1d8e46631168ac461f0e85c260b03813fdfa3f0019)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 568
 (.branch 564
 (.branch 562
 (.branch 561
 (.leaf 0x3a1ccd86b3017fbd5e2ef75ba5cee16fb6db2823f0012)
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
 (.leaf 0x783bdd4e873b95c8e37037dbadc62b097ebe5dae56cb3592bd18894321504803e9e8f2760020)
 (.leaf 0x0)))
 (.branch 582
 (.branch 581
 (.leaf 0x9f4f671369acce6531974b6572a89c421b0c84c1e0901803f51a8b4321106813f9e8f0770020)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 588
 (.branch 586
 (.branch 585
 (.leaf 0x1d1e6daed565b1d8ac15faf56eb558abd058cc45faf578ba5c2cd62b00019)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
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
 (.leaf 0x6932180be5d2d968b0562a13c964a241188a43208f06e33190c05c2d158a4281309044200f0021))
 (.branch 643
 (.leaf 0x1e0eb73b99c8e270b7dbadb6b349a2cf66b3194c85b2d568b3592c5449d4ca612c9449a451e7d3e1ecf4793c0ec70361a8c05c2c150a02c15090441c0d0036)
 (.leaf 0xd1e8b35971d0e430170008)))
 (.branch 646
 (.branch 645
 (.leaf 0x27d399acd2653097cb65729924823f1d8dc6a31168240e0501803fd429e4e26d2c94492411c7f3f1ecf4773b14ca04e269208c442110030170803c1c0d0036)
 (.leaf 0xd7ebb3398291442c150008))
 (.branch 647
 (.leaf 0x371b5cde59409f40a002813000a)
 (.leaf 0x0))))
 (.branch 652
 (.branch 650
 (.branch 649
 (.leaf 0x16bb358ac35faed72b558ab5469b4ca55228f45a1b69aed56a33d9acb64b1d70b75a2cd60af0021)
 (.leaf 0x0))
 (.branch 651
 (.leaf 0xdf6ef43a06cb6174b90008)
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 664
 (.branch 660
 (.branch 658
 (.branch 657
 (.leaf 0x602f777bb5d2e571b7db6ab52a853e9548a351284683298cc45d2d964ae55001b)
 (.leaf 0x35bacd0e80ce660006))
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 668
 (.branch 666
 (.branch 665
 (.leaf 0x39bccd1e8aa9530006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 688
 (.branch 680
 (.branch 676
 (.branch 674
 (.branch 673
 (.leaf 0x195c86331789c3e1b0982bfdf2f579ba5cae16eb64a24b239147637198bc560d0581405fcfd0021)
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 678
 (.branch 677
 (.leaf 0xe27075bac93c9a11070008)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 696
 (.branch 692
 (.branch 690
 (.branch 689
 (.leaf 0x397cad7ebafd7d0006)
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
 (.leaf 0x32991c7e3b1387c2e0f036ab3d96c95faed6eb3579ecea7137994c25d2c954220f007fbf9faef763a9d2e471381bcdc5d2e564b1582bd02803c9e0ee760036)
 (.leaf 0x0))
 (.branch 707
 (.leaf 0x37bbcdbed9dced5c2dcfe7e000a)
 (.leaf 0x0)))
 (.branch 710
 (.branch 709
 (.leaf 0x387c2dced2793b83414fa7c000a)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 716
 (.branch 714
 (.branch 713
 (.leaf 0xe5f2b7fbab4da16cb50008)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
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
 (.leaf 0x683317cbc5c2d968b255299449449239188a44200ec7232188bc5c2d160a0401f0f074381b0021))
 (.branch 771
 (.leaf 0x1deed73395c6e270b81b8da6c345a0ce66b3196c76130580bf5f2f5429f4c25d2a9449a491c894421d0c85420f074351a0bc5c2b150a444210f07434190036)
 (.leaf 0xd3e9b37991c0dc48230008)))
 (.branch 774
 (.branch 773
 (.leaf 0x27b3b9a4ce633097cba55289347e3d1c8dc6a33158843e1d0d8642d44a04da692a9448a411e8b4521d0c8341150a44d2611c8c432110448230e06c34190036)
 (.leaf 0xd9ecb2f962813c44210008))
 (.branch 775
 (.leaf 0x373b7cd6613c9d46a30401f000a)
 (.leaf 0x0))))
 (.branch 780
 (.branch 778
 (.branch 777
 (.leaf 0x16ab4586c15eaed72b757aad4e994ba4d228f46a136db2d469b399aca64b2188c3602fd78bb0021)
 (.leaf 0x0))
 (.branch 779
 (.leaf 0xdfef74ba46bb598cc50008)
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 792
 (.branch 788
 (.branch 786
 (.branch 785
 (.leaf 0x5fefb76badcee571b85b2ad54a7d3a9348a2d12866933988c25c2d960ae56001b)
 (.leaf 0x363b0d2e90ca640006))
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 796
 (.branch 794
 (.branch 793
 (.leaf 0x3a3d0d3e9aa5510006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 816
 (.branch 808
 (.branch 804
 (.branch 802
 (.branch 801
 (.leaf 0x194c962f1588c3e1b0b81c05faf378b9dcadf6eb6ca64f2290c7237188bc5a25118743615090021)
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 806
 (.branch 805
 (.leaf 0xe2f0f63b092c9229130008)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 824
 (.branch 820
 (.branch 818
 (.branch 817
 (.leaf 0x39fced9ecaf97b0006)
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
 (.leaf 0x32b93c76371187c260f056bb4d92c75eaed6ab3589f4f26f3698cc25b2c95c52270c85c2a12f0773a5d0e37137dbcdd633157cbd5e2ed1a8c42a1106820036)
 (.leaf 0x0))
 (.branch 835
 (.leaf 0x377badaed1d8eb6230d168a000a)
 (.leaf 0x0)))
 (.branch 838
 (.branch 837
 (.leaf 0x383c0dc6da7539894451288000a)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 844
 (.branch 842
 (.branch 841
 (.leaf 0xe7f3b7dbcb3d9984c10008)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
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
 (.leaf 0xe2f1387c2e0f037fbedeef377badcee36fb6daed3379acce632f96cae532792c8e430d85c260f0581c05fefd7dbe5eee370b7dbadb6cb5daad368b3d9ab95bad566b157ab556a953a95468f46a2d1287429f4f6793b9d4e65f2e96cb2572a94ca24f2692c9235198c45e2d15783bddced763adc2e06fb79badc6db69b2d86bb5998cb6532590c751285409f4f275269248a411e8e349a0ce6632990b4592c15cac552a14ca4512813c8a442190882401e0ec74391c0dc5a2c158a8522800a8)
 (.leaf 0x63311849c4d260d86a340009))
 (.branch 899
 (.leaf 0x753a5d0d56a34d389b4d0cc6431000c)
 (.leaf 0x0)))
 (.branch 902
 (.branch 901
 (.leaf 0x9c4de6d239148532984b92c9449000c)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 908
 (.branch 906
 (.branch 905
 (.leaf 0x165b258ea14fa7349a2d00009)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 920
 (.branch 916
 (.branch 914
 (.branch 913
 (.leaf 0x17abcde29b4ca5980be5e0009)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 944
 (.branch 936
 (.branch 932
 (.branch 930
 (.branch 929
 (.leaf 0x18fc7636ef76bac823f1e0009)
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
 (.leaf 0xc662f1562b0d826b3499b9dcce5000c)
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
 (.leaf 0xc4e230f86c2e130782c0dd2e772b8dc2df6eb6db2bf5eaed72b75aacd62af4aa4d228f46a2d128742994c6612f974b6592b95476391b8d46631178b4561d0d8642e15098140600ff7f3f5ecf57a3cde4f17238dc4e17037dbcdd6e33d9ccd6632d94c96431d80bf5f2f578bb5a2cd64b1582bd50a75329548a34b255289349245208f4721d0c854220d047b3d1e4f0773b1bcdc6d361acd45d2e16cb4592c15cac552411c8c452210c8441200c05e2e168b0562a148a03c1d0e06c341909044200f070340c050200c040100b4)
 (.branch 4
 (.leaf 0x195ca64f2591c863f1d8dc662f1580bfdfafb7cbddeaf378bbddaeb6bb55a6d167b3596c963b1586c156aad52a752a8d429f4ea6d329741a04fe7d3d9e4ee75399c4de6d359a4ce532893c9a4b2491c8a43208fc7a291389446210f8441e0d058240df8fb7d3e5f0f7783bddced763add4e97439dcce56db69b2d86bb59aad469b49a2d06331588c36130574b95c2dd6cb5572b558ab552a544a15027d3c9d4e26d34994c25d1a8c45a29128840a00fe7e3e9f0ea74399c8e270349a0ce6632990c66230980be5e2a14ca4512813c9c4d2612c94491f8f87a3c1d8e872381b8d86a34198c8622713094482311084401f0c05c2c150a04c180b05024100700e1)
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
 (.leaf 0x3fe001ff000ff8007fc0007fc003fe07e07e07e001ff000ff81f81f81f8007fc0fc0fc0fc003fe001ff0001ff007e07e07e)
 (.branch 4
 (.leaf 0x3ffc01ffe00fff007ff803fff803ffc01f81f81f81ffe00fff007e07e07e07ff803f03f03f03ffc01ffe00fffe00ff81f81f80)
 (.leaf 0x3ffffffffffffffc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))))
def kindMasks := kindMaskTable.get
def keys := List.range 5
def vertexMaskTable : Table Nat :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf 177450860258468158815456358047178530011739212866951090069840388338173564880958592065480525534367630469433854704238707286587511668735)
 (.leaf 726661316757981865043845408143203025405296102148866209597072208755096366811106355468002776000753730357221931632113733441221724064448511))
 (.branch 3
 (.leaf 45802196442377800623142947315963306773995582640762705668476531782226853057943487661945674490743888957099378199550064160696440487548026879)
 (.branch 4
 (.leaf 190490608345305194750274805150152524290172519596829014621209948893591451097316415922126698362449973735415034079099059415633934159937957527553)
 (.leaf 190489893040843503722003512744303969043466756400390537129833762597750360384022276509575957601412539534011127858256834840471649769889208467457))))
 (.branch 7
 (.branch 6
 (.leaf 190535683880430814734296896449547340769251181704223060020852112313460278230903744442140333255371431330936625838677730063479528051187539509249)
 (.leaf 190536410364296712457693702675561886480870438224368324870230437262674506668907346516332620171208776101829861166069135630412279472056533254145))
 (.branch 8
 (.leaf 11908525492458426368788756819812609565739497986666629630408593963990325300961753134230172638064238874099202346127597490967795040058481836030)
 (.branch 9
 (.leaf 179372167726167001069451116327794282460609614487211930279590117059193590823990290540265919984877616037507344045393279761599762320585813663742)
 (.leaf 189838645365773786988242513797043137016538998837733452618530494138494845644329165916277005224643334535011597770600750392655370887218864316416)))))
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
 (.leaf (.leaf 0)))
 (.branch 56
 (.branch 52
 (.branch 50
 (.branch 49
 (.leaf (.leaf 9))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 54
 (.branch 53
 (.leaf (.leaf 0))
 (.leaf (.leaf 10)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))))
 (.branch 96
 (.branch 80
 (.branch 72
 (.branch 68
 (.branch 66
 (.leaf (.leaf 0))
 (.branch 67
 (.leaf (.leaf 11))
 (.leaf (.leaf 0))))
 (.branch 70
 (.branch 69
 (.leaf (.leaf 12))
 (.leaf (.leaf 0)))
 (.branch 71
 (.leaf (.leaf 13))
 (.leaf (.leaf 0)))))
 (.branch 76
 (.branch 74
 (.branch 73
 (.leaf (.leaf 14))
 (.leaf (.leaf 0)))
 (.branch 75
 (.leaf (.leaf 15))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
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
 (.leaf (.leaf 0)))
 (.branch 184
 (.branch 180
 (.branch 178
 (.branch 177
 (.leaf (.leaf 32))
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
 (.leaf (.leaf 33))
 (.leaf (.leaf 0)))
 (.branch 195
 (.leaf (.leaf 34))
 (.leaf (.leaf 0))))
 (.branch 198
 (.branch 197
 (.leaf (.leaf 35))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 204
 (.branch 202
 (.branch 201
 (.leaf (.leaf 36))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
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
 (.leaf (.leaf 0)))
 (.branch 312
 (.branch 308
 (.branch 306
 (.branch 305
 (.leaf (.leaf 51))
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
 (.leaf (.leaf 52))
 (.leaf (.leaf 0)))
 (.branch 323
 (.leaf (.leaf 53))
 (.leaf (.leaf 0))))
 (.branch 326
 (.branch 325
 (.leaf (.leaf 54))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 332
 (.branch 330
 (.branch 329
 (.leaf (.leaf 55))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
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
 (.leaf (.leaf 0)))
 (.branch 440
 (.branch 436
 (.branch 434
 (.branch 433
 (.leaf (.branch 0x1000000000000000000000001000000000000000000000000000000000001000000000000000000000001000000000000 (.leaf 78) (.leaf 79)))
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
 (.leaf (.leaf 80))
 (.leaf (.leaf 0)))
 (.branch 451
 (.leaf (.branch 0x1000000000000000100000000000000000000000000000000000000000000000400000000000000040000000000000000 (.leaf 81) (.leaf 82)))
 (.leaf (.leaf 0))))
 (.branch 454
 (.branch 453
 (.leaf (.branch 0x1000000000000000100000000000000000000000000000000000000000000001000000000000000100000000000000000 (.leaf 83) (.leaf 84)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 460
 (.branch 458
 (.branch 457
 (.leaf (.branch 0x1000000000000000100000000000000000000000000000000000000000000010000000000000001000000000000000000 (.leaf 85) (.leaf 86)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
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
 (.leaf (.leaf 0)))
 (.branch 568
 (.branch 564
 (.branch 562
 (.branch 561
 (.leaf (.leaf 102))
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
 (.leaf (.leaf 103))
 (.leaf (.leaf 0)))
 (.branch 579
 (.leaf (.leaf 104))
 (.leaf (.leaf 0))))
 (.branch 582
 (.branch 581
 (.leaf (.leaf 105))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 588
 (.branch 586
 (.branch 585
 (.leaf (.leaf 106))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
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
 (.leaf (.leaf 0)))
 (.branch 696
 (.branch 692
 (.branch 690
 (.branch 689
 (.leaf (.branch 0x10000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000001000000000000 (.leaf 129) (.leaf 130)))
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
 (.leaf (.leaf 131))
 (.leaf (.leaf 0)))
 (.branch 707
 (.leaf (.branch 0x10000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000040000000000000000 (.leaf 132) (.leaf 133)))
 (.leaf (.leaf 0))))
 (.branch 710
 (.branch 709
 (.leaf (.branch 0x10000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000100000000000000000 (.leaf 134) (.leaf 135)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 716
 (.branch 714
 (.branch 713
 (.leaf (.branch 0x10000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000001000000000000000000 (.leaf 136) (.leaf 137)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
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
 (.leaf (.leaf 0)))
 (.branch 824
 (.branch 820
 (.branch 818
 (.branch 817
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000001000000000000 (.leaf 161) (.leaf 162)))
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
 (.leaf (.leaf 163))
 (.leaf (.leaf 0)))
 (.branch 835
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000040000000000000000 (.leaf 164) (.leaf 165)))
 (.leaf (.leaf 0))))
 (.branch 838
 (.branch 837
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000100000000000000000 (.leaf 166) (.leaf 167)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 844
 (.branch 842
 (.branch 841
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000001000000000000000000 (.leaf 168) (.leaf 169)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
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

end Papers.RationalityTen.RootedCaches.RootedSevenMixed025

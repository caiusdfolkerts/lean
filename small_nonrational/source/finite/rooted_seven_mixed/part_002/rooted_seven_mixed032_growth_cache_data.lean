module
prelude
public import RootedSevenMixed032
public import SignatureCompatibility
public import PackedRawNatGrowth
public import FiniteChecks
public import RawFacetEmbedding
public import RootedSevenMixed032GrowthCachecandidateMasksData000
public import RootedSevenMixed032GrowthCachebadMasksData000
public import RootedSevenMixed032GrowthCachesignatureMasksData000

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenMixed032
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def rawCells := Papers.RationalityTen.FacetUniverses.RootedSevenMixed032.rawCells
def cells (c : Fin 529) := rawCells c.val
def ridgeList := ConcreteGrowth.ridgeList cells
def literalCompatible (a b : Fin 529) := ConcreteGrowth.compatible (cells a) (cells b)
def kind (c : Fin 529) := (cells c).kind
def rawKindCode : Nat := 3101452042208010924945369284704057220690515800232829193597811320713845080201531266669457235888997293599014726003491844776924231607248088895924777307045941114705748446964361189622509924982894188575294322270319853732730146240045813350722288232804425541568390966205462197348460364799035393233255386473711856331049378195393314942468505879960957241489615412955165999551871539096199185424054452116263593797184706416210921879511676012895942518469758437506113059845399344218032717767824
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
 (.leaf 0x1c5711c3709c1701bf6f9bd6f1bb6e9b96e1b76d9b56d02408c220842007c1e0741c06c1a0641805c160541404c120441003c0e0340c02c0a0240801c060140400c02004000037))))
 (.branch 12
 (.leaf 0x0)
 (.branch 14
 (.leaf 0x0)
 (.branch 15
 (.leaf 0x1d7759d5751d3749d1741cf739cd731cb729c9721c7718ab2a8a92a0a7298a5290a3288a12809f2789d2709b26899260972589525093248912408f2388d2308b22889220000037)
 (.leaf 0x0)))))
 (.leaf 0x0))
 (.branch 48
 (.branch 40
 (.branch 36
 (.leaf 0x0)
 (.branch 38
 (.branch 37
 (.leaf 0x0)
 (.leaf 0x1e97a1e7799e5791e3789e1781df779dd771db769d97605d1705b16859160571585515053148511404f1384d1304b12849120471184511043108411003f0f83d0f03b0e8000037))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 56
 (.leaf 0x0)
 (.branch 60
 (.branch 58
 (.leaf 0x0)
 (.branch 59
 (.leaf 0x0)
 (.leaf 0x7b1eb7a8000004)))
 (.leaf 0x0)))))
 (.branch 96
 (.branch 80
 (.leaf 0x0)
 (.branch 88
 (.leaf 0x0)
 (.branch 92
 (.leaf 0x0)
 (.branch 94
 (.branch 93
 (.leaf 0x360d7358000004)
 (.leaf 0x0))
 (.leaf 0x0)))))
 (.branch 112
 (.branch 104
 (.branch 100
 (.leaf 0x0)
 (.branch 102
 (.branch 101
 (.leaf 0x1fe7f5fc7edfa7e5f87ddf67d5f47cdf27c5f07bdee7b5114410f4390d4310b4290942107419054110340901400ff3f8fd3f0fb3e8f93e0f73d8f53d0f33c8f13c0ef3b8000037)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 120
 (.branch 116
 (.branch 114
 (.branch 113
 (.leaf 0x21083e0e8360c82e0a8260881e068160480e02806007fd745cd725c5705bd6e5b56c5ad6a5a56859d665956458d625856057d5e5755c56d5a5655855d565555454d52544000037)
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
 (.leaf 0x1ea715c36fdbd0d4340c8310bc2e0b02b0a82909c2605814044100380a0200501002001b)))
 (.branch 134
 (.branch 133
 (.leaf 0x0)
 (.leaf 0x7a5e778de1705c06e5b71b86d1ac6a1a0671946418c621805f13c4d1284911c431043e0f43b060130480f0380c01c0600c020028))
 (.branch 135
 (.leaf 0x75dd5745cf6edba6d5b42f0bb2e4b82d8b52ccb22c4b02b8ad2749b260972549123c8c22c8905c15048100340b02406010010028)
 (.leaf 0x0))))
 (.branch 140
 (.branch 138
 (.leaf 0x0)
 (.branch 139
 (.leaf 0x1ea74dd272dc9344d0338cd32cca320c7318c530cc227c9a26496254932388d22889001b)
 (.leaf 0x0)))
 (.branch 142
 (.branch 141
 (.leaf 0x1cd731c7718e93a0e6394e3388e037cde374db368d62789c26497250922408d22c88001b)
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 152
 (.leaf 0x0)
 (.branch 156
 (.branch 154
 (.branch 153
 (.leaf 0x7a94c52d495214651543509415013e4f4d6000e)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 176
 (.branch 168
 (.branch 164
 (.branch 162
 (.branch 161
 (.leaf 0x0)
 (.leaf 0x1ea795e4775db20c822007f1f47c1e8791e0771d4741444c12c4811c451003f0f03b001b))
 (.leaf 0x0))
 (.branch 166
 (.branch 165
 (.leaf 0x7f9fc7e1f677dde765d84892147d1e4711b4651845d164511340d013f8fd3ecf73d4f23c4ef1404e12c49118441083f0f43a0028)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 184
 (.branch 180
 (.branch 178
 (.branch 177
 (.leaf 0x21083a0a821ea61584609815fd7e5f17b5e9795dd7659964585605795a5615555152001b)
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
 (.leaf 0x1fa7e5f27c1374d9344cd314c12e4b52c4ad294a105400ff3f0fb3e4f43ccf03bcd6001b)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 216
 (.branch 212
 (.branch 210
 (.branch 209
 (.leaf 0x20c82e048099a665976599464d916418f6398c62d6858d6257d5e5715755953548d6001b)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 240
 (.branch 232
 (.branch 228
 (.branch 226
 (.branch 225
 (.leaf 0x81a05801ff7d1f37b9ed6bdae6b1ab6a5a8699a5691a3685a059d65589605755b5655655151411023fcfd3e8f83d8f33c4ee0028)
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
 (.leaf 0x1eb711c16f9bb0dc360cc320c02f0b42b0a82809c25088200741c0680901c0600c01001b)))
 (.branch 262
 (.branch 261
 (.leaf 0x0)
 (.leaf 0x7a1e5789df70dc26e1b51c06f1b06b1a4681986418c611805e16c591585514c421003f0f03a0901f0781b0680b02005010010028))
 (.branch 263
 (.leaf 0x759d3741cd6f5bc6ddb62f8bd2e8b92dcb62d0b22c4af2b8ac2a4a7290a3284902388d2288808c210781c0640c0280500c020028)
 (.leaf 0x0))))
 (.branch 268
 (.branch 266
 (.leaf 0x0)
 (.branch 267
 (.leaf 0x1eb755d4729c734cd233cce330cb324c7318c430cc12aca6294a22849223c8c22c88001b)
 (.leaf 0x0)))
 (.branch 270
 (.branch 269
 (.leaf 0x1cf739c9720eb3a8e7398e438ce137cde370db364d72a8a8294a3280932448c22889001b)
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 280
 (.leaf 0x0)
 (.branch 284
 (.branch 282
 (.branch 281
 (.leaf 0x7ad4e5354a5254751944509414fd3e4f0d7000e)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 304
 (.branch 296
 (.branch 292
 (.branch 290
 (.branch 289
 (.leaf 0x0)
 (.leaf 0x1eb79de6771d921484204801f87d1ec791e0761d4731745815c5414c441043e0f43a001b))
 (.leaf 0x0))
 (.branch 294
 (.branch 293
 (.leaf 0x7f5fa7ddf4785e076dda491234811f4751c4691845d154511243d0d4290941cf63d0f33c0ee1705a15c551484510c3e0f03b0028)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 312
 (.branch 308
 (.branch 306
 (.branch 305
 (.leaf 0x20f83209819eb61d8660d826017f5f57b5e9785dd755c9705b56c5a95955d5654d51001b)
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
 (.leaf 0x1fc7edf17b9394e1354d1324c52f4b52c4a92949d114310b421073e0f53c8f13b8d7001b)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 344
 (.branch 340
 (.branch 338
 (.branch 337
 (.leaf 0x20e836038019c66d9865d95651926418f6358c629745bd6e5ad6a56d5855554544d7001b)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 368
 (.branch 360
 (.branch 356
 (.branch 354
 (.branch 353
 (.leaf 0x8220780a017d9f57c1ef6c5b06b5ac6a9a969da5691a26859f5cd715b96c5a55c5695554d524410e42d09418f93dcf23c0ef0028)
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
 (.leaf 0x1e97a1e6791c5711c27008520c7e1f07b1e8771d8751c06e1a4671986518861180411003f0f83d0f0370d4300b82d0b0290a027020070180501003002f))
 (.branch 387
 (.leaf 0x1d7759d4749bf6f9bc6e8d3344cc328c9320c5310c32f8bc2dcb52d0b32c0af2b88f2388d2308b228360d0330c42d0b02a09825028090180500801002f)
 (.leaf 0xe4380300b0004)))
 (.branch 390
 (.branch 389
 (.leaf 0x1fe7f5fb7e5e3789e0779d1741ce731b96e1b66d1394dd324c12f4b92b4a929491224751b4691945915450f53d0f33c8f13c0eb3a4e4388e1380dd370db2f4bb2e8b82d0b32c4ad2b0912408d230892206f1b46c1a8661946317c5e10c420fc3e0ec3a0300b01003008010055)
 (.leaf 0x1c87111444028090006))
 (.branch 391
 (.leaf 0x300bf24c92020070006)
 (.leaf 0x0))))
 (.branch 396
 (.branch 394
 (.branch 393
 (.leaf 0x1cb729c87194e531475154450d404fd3e3a8e839ce5384e0378da364d2340cf334c9320c6308c124c9222c8a224880025)
 (.leaf 0x0))
 (.branch 395
 (.leaf 0x354d4244900004)
 (.leaf 0x0)))
 (.branch 398
 (.branch 397
 (.leaf 0x3b4ec23c8e0004)
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 408
 (.branch 404
 (.branch 402
 (.branch 401
 (.leaf 0x21083e0d82d9c6699564d926458e6358c61d856017e5f57c5e5785dd5855d565555454d4d52d4a5214450d414f53c0025)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 412
 (.branch 410
 (.branch 409
 (.leaf 0x5414f0002)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 432
 (.branch 424
 (.branch 420
 (.branch 418
 (.branch 417
 (.leaf 0x82a0981e057e1f77d5f3775dc769d86c5af6a9a869da668da268586611836057d5f17a5d97556959559555495148d214811e4691945d13448f73d8f33c8ef3b884208811fc7b1e8781d073114440f43c0ec3a0042)
 (.leaf 0x21c8610c420004))
 (.leaf 0x0))
 (.branch 422
 (.branch 421
 (.leaf 0x499253e4f8104400006)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 440
 (.branch 436
 (.branch 434
 (.branch 433
 (.leaf 0x625885715b0004)
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
 (.leaf 0x20480e017fdf27c5ef7b5b06b9ad6ada7699a46819f66d99661966499163d8b6295c56d5454d52545384d9354cd2f4b92c4a1273e4f83c4f03bcee002f)
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 454
 (.branch 453
 (.leaf 0x4ed3a3dcf60004)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 472
 (.branch 468
 (.branch 466
 (.branch 465
 (.leaf 0x6799d569590004)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 496
 (.branch 488
 (.branch 484
 (.branch 482
 (.branch 481
 (.leaf 0x6cdb2561573d4f40006)
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
 (.leaf 0x1ec709c06f1ba0e4380cc310c02e0b42c0a428098250841f0781b0641504c1203c0d001b)))
 (.branch 518
 (.branch 517
 (.leaf 0x0)
 (.leaf 0x799e4781de715c46d9b41c8711b06a1a467198651886117c5e1685815c541484e1304b1204608c200741c06417050110400d0028))
 (.branch 519
 (.leaf 0x751d2739cc6fdbe6e5b8300bf2e8b82dcb52d0b32c0af2b4ac2a0a6294a22809c2689925894090220741b068180581103c0e0028)
 (.leaf 0x0))))
 (.branch 524
 (.branch 522
 (.leaf 0x0)
 (.branch 523
 (.leaf 0x1ec75dd6721c6354d433ccd330ca324c8314c4308c12a8a7290a32809e26c9825c94001b)
 (.leaf 0x0)))
 (.branch 526
 (.branch 525
 (.leaf 0x1d1741cb728ed3b0e7394e4388e1380dd370da364d82aca9290a22849f2749825895001b)
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 536
 (.leaf 0x0)
 (.branch 540
 (.branch 538
 (.branch 537
 (.leaf 0x7b15053d4a521475154450d404fd3d4f0d8000e)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 560
 (.branch 552
 (.branch 548
 (.branch 546
 (.branch 545
 (.leaf 0x0)
 (.leaf 0x1ec7a5e8769d821c862047f1f87c1ec7a1dc761d0731705915855148501344a12446001b))
 (.leaf 0x0))
 (.branch 550
 (.branch 549
 (.leaf 0x7edf97d5f378de2775dc499254811e4751b469194591544d124390c42d0841902400ff3f0fa1745b1585414c5113c4a120470028)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 568
 (.branch 564
 (.branch 562
 (.branch 561
 (.leaf 0x20d82e07815ec6258860d816017e5f57c5e5785d9755c56f5b96b5a56558d6257d5d001b)
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
 (.leaf 0x1fe7f5ef7b53b4e9354cd324c12f4b92b4a92849d104350a42506411013f8fd3e8d8001b)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 600
 (.branch 596
 (.branch 594
 (.branch 593
 (.leaf 0x21083e017fd9e675986599564d926458e6358b629735c16d5b16959d6458560574d8001b)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 624
 (.branch 616
 (.branch 612
 (.branch 610
 (.branch 609
 (.leaf 0x82a09812037e1f77c9f16cdb26b5ab6a9a869da668da26819f5d1725b56b5a9685996157d5e4450f4290841d0540cfe3f0fb0028)
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
 (.leaf 0x1e879de6795c470dc2704872087e1f47b1e4781d8741c86d1a4681986418c6117c4d1304b12849120390d0300bc2d0ac2a0a02605013048110400f002f))
 (.branch 643
 (.leaf 0x1d6755d474dbe6f5bc6ecd5340cc32cc931cc6310c2300bb2dcb62d0b22c4af2b49b2689926097258380d4330c82d0ac2909c2505815048110380d002f)
 (.leaf 0xdc36060170004)))
 (.branch 646
 (.branch 645
 (.leaf 0x1fd7f1fb7e9e2785e077dd073dce735b86ddb66d53b4d9324c52f4b52c4a928499214751c4691845d1544d01400ff3f8fd3f0ed3a0e438ce137cde370da2fcbc2e8b92d0b22c0ae2b09d2709926095250711b86c1ac66190621805e13c4e12c4a11c46060170400f0380d0055)
 (.leaf 0x1c06f14450058150006))
 (.branch 647
 (.leaf 0x2f8bd27c9e050130006)
 (.leaf 0x0))))
 (.branch 652
 (.branch 650
 (.branch 649
 (.leaf 0x1ca725c871d5052d4751944509414fd3d3b0e939ce6384df374db364d4344cf338c931cc530cc127c9e25c96254940025)
 (.leaf 0x0))
 (.branch 651
 (.leaf 0x34cd22749c0004)
 (.leaf 0x0)))
 (.branch 654
 (.branch 653
 (.leaf 0x3acea26c9a0004)
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 664
 (.branch 660
 (.branch 658
 (.branch 657
 (.leaf 0x20f83a0d8319e66595651926418f6358b625846017f5f57b5e9785d96458d625856057d4f5314a52544509404f93c0025)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 668
 (.branch 666
 (.branch 665
 (.leaf 0x5394d0002)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 688
 (.branch 680
 (.branch 676
 (.branch 674
 (.branch 673
 (.leaf 0x8260881e067ddf67d5f4771db769d96cdae6a9a969da5691a268188615836097d5ed795dd7559965589615795d495224811f469184591444903408ff3f8fb3e88620c812007b1e4771d473144501244811c460042)
 (.leaf 0x2148413c4e0004))
 (.leaf 0x0))
 (.branch 678
 (.branch 677
 (.leaf 0x49123415041344c0006)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 696
 (.branch 692
 (.branch 690
 (.branch 689
 (.leaf 0x61d865a1670004)
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
 (.leaf 0x20380a01801f17c1ef7b9b26bdad6b1a7695a36859f6759a66197649906398c6296859d6057d5e5753a4dd354d12f4b52b4a527415043f4fc3ecfa002f)
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 710
 (.branch 709
 (.leaf 0x4e53840d020004)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 728
 (.branch 724
 (.branch 722
 (.branch 721
 (.leaf 0x6719b599650004)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 752
 (.branch 744
 (.branch 740
 (.branch 738
 (.branch 737
 (.leaf 0x6c5b059163405000006)
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
 (.leaf 0x1e979de5791c570dc1700862107d1f07a1e4781dc731c46f1a0671946418c62178591605715855150380d82f0b82c0ac2a0a4250801f0781d0701b002f))
 (.branch 771
 (.leaf 0x1d7755d3749bf6f5bb6e8d4348cb328c831cc6314c12fcbd2d8b52ccb22c4b02b0a7298a5290a3288390dc320c42c0ac2809c26088210781d06819002f)
 (.leaf 0xd434090230004)))
 (.branch 774
 (.branch 773
 (.leaf 0x1fe7f1fa7e5e3785df779d173dcd731b96ddb56d13a4e1314c12e4b52c4ad27495234711b4651845d164490d4310b42909420ec3a8e3388e037cde374d9300be2e4b82ccb22bcae2b4a92a0a5290a1280721c06b1a865190611805f16c5a15c5614c52090230701b068190055)
 (.leaf 0x1b86d1745c088210006))
 (.branch 775
 (.leaf 0x2f0bb2acaa0801f0006)
 (.leaf 0x0))))
 (.branch 780
 (.branch 778
 (.branch 777
 (.leaf 0x1cb725c77194f5354651543509415013c3b4eb398e5380df370db368d534cce334c831cc430cc22acaa28ca2284a00025)
 (.leaf 0x0))
 (.branch 779
 (.leaf 0x344d02a4a80004)
 (.leaf 0x0)))
 (.branch 782
 (.branch 781
 (.leaf 0x3a4e829ca60004)
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 792
 (.branch 788
 (.branch 786
 (.branch 785
 (.leaf 0x21083a0c82d9d66d9464d916418f6398a621865fd7e5f17b5e9795d5705bd6e5b56c5ad5053949521435093f4f93d0025)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 796
 (.branch 794
 (.branch 793
 (.leaf 0x5314b0002)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 816
 (.branch 808
 (.branch 804
 (.branch 802
 (.branch 801
 (.leaf 0x82a0881a057e1f67d1f3775db765d86c9b06a5a8699a5691a367d8961d826057c5ed785dd765c9715b96d5a9694992447d1e465184551444d0f4390b4290741887214801fc7a1e4761d4741745c1545414c520042)
 (.leaf 0x20c8216c5a0004))
 (.leaf 0x0))
 (.branch 806
 (.branch 805
 (.leaf 0x4892144510164580006)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 824
 (.branch 820
 (.branch 818
 (.branch 817
 (.leaf 0x615845d1730004)
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
 (.leaf 0x20480a007fdf27c1ee7b5b36c5ac6ada6695a2685a06799c65d96645906358c62d745cd6c5ad6a5a53b4e5344cd2e4b52a4a528445104250841d06002f)
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 838
 (.branch 837
 (.leaf 0x4dd3643d0e0004)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 856
 (.branch 852
 (.branch 850
 (.branch 849
 (.leaf 0x669995c9710004)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 880
 (.branch 872
 (.branch 868
 (.branch 866
 (.branch 865
 (.leaf 0x6bdae5c16f4350c0006)
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
 (.leaf 0x6cdb26c5b06bdae691a3689a16819f6799d6719b6699963d8e6358c62d8a6258861d86615845e9795e1775d9755414f5394d5314b505404fd3e4f53c4ed3a4e5384dd364b12b4a9294a12749925491234892145d164551444d123b4ec3acea3a4e8378dd370db368d9354d434cd2344d0318c5310c3308c1300bf2f8bd2f0bb2c4b02bcae2b4ac21c862148420c821e0771d8751d0731c8711c06f1b86d18c621846017c5e0e4380dc360d4340a8290a027098250090)
 (.leaf 0x812007f1b06b1a8330c8310009))
 (.branch 899
 (.leaf 0xcf338cd2e8b92e0300bc2e0009)
 (.leaf 0x6e5b86ddb66d5b40006)))
 (.branch 902
 (.branch 901
 (.leaf 0x1354d1334811f478e7398e52dcb62d4691a067000f)
 (.leaf 0x775dc76dda765d86fdbe6f5bc6edba000c))
 (.branch 903
 (.leaf 0x72dca725c871dc6715c470dc2705c0000c)
 (.leaf 0x0))))
 (.branch 908
 (.branch 906
 (.branch 905
 (.leaf 0x14a52548390e3388cc32cca0009)
 (.leaf 0x0))
 (.branch 907
 (.leaf 0x745d073dce735cc0006)
 (.leaf 0x0)))
 (.branch 910
 (.branch 909
 (.leaf 0x75dd6755d474dd20006)
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 920
 (.branch 916
 (.branch 914
 (.branch 913
 (.leaf 0x19865d9660d8260547519450009)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 944
 (.branch 936
 (.branch 932
 (.branch 930
 (.branch 929
 (.leaf 0x6b5ac6ad805fd7e4751c46c7e1f47c000c)
 (.leaf 0x78de2785e077dde0006))
 (.leaf 0x0))
 (.branch 934
 (.branch 933
 (.leaf 0x7c9f17c1ef7b9ed7a5e879de6795e4000c)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 952
 (.branch 948
 (.branch 946
 (.branch 945
 (.leaf 0x8120380a01801ff0006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 992
 (.branch 976
 (.branch 968
 (.branch 964
 (.branch 962
 (.branch 961
 (.leaf 0x1aa6a5a86559464d324c5300009)
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 966
 (.branch 965
 (.leaf 0x7e1f77d9f57d1f30006)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 984
 (.branch 980
 (.branch 978
 (.branch 977
 (.leaf 0x82a098220781a050006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 1008
 (.branch 1000
 (.branch 996
 (.branch 994
 (.branch 993
 (.leaf 0x8420f83a0d8320b7f9fd7f1fb7e9f9000c)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))))))
def kindRowTable : Table Nat :=
(.branch 2
 (.branch 1
 (.leaf 0x1)
 (.leaf 0x0))
 (.branch 3
 (.leaf 0x69da6695a468da2685a067d926459063d8e6358c62d8a5f57c5ed7a5e5785dd765d56e5b56c5ad6a5a5625856057d5e575565555454d525454450d42505404fd3e4f53c4bd2e4b52c4ad2a4a52849d1a4651845d164551444d1242d0a4250841d063fcfe3f4fc3ecfa3ccf23c4f03bcee384e037cde374dc36cda364c9320c7318c5310c3308c12d0b32c8b12c0af2b8ad2b0a5290a3288a12809926097258952508d2308b228892207b1e8791e0771d8751d0731986519063188611805f1785715855150531484b12849120471183f0f83d0f03b0e82d0b02b0a8290a027098250781d0701b06819048110400f0380d01805010030080100c6)
 (.branch 4
 (.leaf 0x1b36c9b16c1af6b9ad6b1ab6a9a96a19e6759c66d9a6659865d966559464d89621876198561183609816017f5f9745cd725c5705bd6859d665956458d5c56d5a5655855d5053d4e5354c52d4a5254851d465153b4e9394e1374d9354d1334c9314c1264952448d224852047d1e4751c46d114410f4390d431054110340901400f93e0f73d8f53d0ed3b0eb3a8e93a0e7398e5390e3388d835cd6354d434cd2344d033cce334cc32cca300bf2f8bd2f0bb2e8b92e0b72d8b52acaa2a4a829ca627c9e2749c26c9a24c922449023c8e21c862148420c82204801fc7e1f47c1c8711c06f1b86d1b06b1a8691a0671745c16c5a164581445013c4e1344c1144410c42104400e4380dc360d4340cc320c4300bc2e09023088210801f0601705815050130300b028090200700ed)
 (.leaf 0x21083e0e8360c82e0a8260881e068160480e02806007fdfe7f5fc7edfa7e5f87ddf67d5f47cdf27c5f07bdee7b5ec7adea7a5e879de6795e478de2785e077dde775dc76dda765d875dd6755d474dd2745d073dce735cc72dca725c871dc6715c470dc2705c06fdbe6f5bc6edba6e5b86ddb66d5b4005d))))
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
 (.leaf 0xff8007fc003fe07e07e07e001ff000ff8007fc0fc0fc0fc003fe0003fe001ff03f03f03f000ff8007fc0fc0fc0fc003fe07e07e07e)
 (.branch 4
 (.leaf 0xfff007ff803ffc01f81f81f81ffe00fff007ff803f03f03f03ffc01fffc01ffe00fc0fc0fc0fff007ff803f03f03f03ffc01f81f81f80)
 (.leaf 0x1fffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))))
def kindMasks := kindMaskTable.get
def keys := List.range 5
def vertexMaskTable : Table Nat :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf 25573351929904851188537449089364445207822958659291224909946671301474926309640032950419587768883247488663108841315855096674899311902891755991812014079)
 (.leaf 22376705802995306808937082353789443946143325531926650974470022306124277349557741570422372115061924963155269214495891043995631400709490834898073681919))
 (.branch 3
 (.leaf 6703881588277689884754520504953556174172590285836924908991684930640716424991488406484448361644707700791513486771865410768539632760933727454689443549544447)
 (.branch 4
 (.leaf 22376705802948789308033023936526438235457001027165342906591042555581322923103514426226943382625446198277702055310122114626892228313791042804229603329)
 (.leaf 1757381497111847809345481849866880934256233118385202505940075725041329539445122116472054158836838721240925341826846469907731303775126419979739182226026216292353))))
 (.branch 7
 (.branch 6
 (.leaf 1757388200993436074841036330070442785595219751472673252860952485235984756886061899010313193228697222617137655712403314604912010076176908004280798255079204323329)
 (.leaf 1757388200967862722911177996382809479538201621837906329496518459010127792510356305758491266548966816694918814715037458467733833222816186041751297442631372505089))
 (.branch 8
 (.leaf 1757388200974256063942225148295228130241126223034932234063531368664205548502126648335112472135099487714619129296778064167850536713279137791852277682811703394302)
 (.branch 9
 (.leaf 1757388200977452734457748724340162885804434425351248666376121753587680148160734907608722327273465994851266483710633244636488846286830735140387356610358327386110)
 (.leaf 1757388200983846075488795876430032396931050829945426490164246514273796194490740039993939723478159641652428258997474832193105273700172156561919338318053892939776)))))
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
 (.leaf (.leaf 0))
 (.branch 28
 (.branch 26
 (.branch 25
 (.leaf (.leaf 7))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 48
 (.branch 40
 (.branch 36
 (.branch 34
 (.branch 33
 (.leaf (.leaf 0))
 (.leaf (.leaf 8)))
 (.leaf (.leaf 0)))
 (.branch 38
 (.branch 37
 (.leaf (.leaf 9))
 (.leaf (.leaf 10)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
 (.branch 56
 (.branch 52
 (.branch 50
 (.branch 49
 (.leaf (.leaf 11))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 60
 (.branch 58
 (.leaf (.leaf 0))
 (.branch 59
 (.leaf (.leaf 0))
 (.leaf (.leaf 12))))
 (.leaf (.leaf 0))))))
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
 (.leaf (.leaf 0)))
 (.branch 92
 (.leaf (.leaf 0))
 (.branch 94
 (.branch 93
 (.leaf (.leaf 15))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))))
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
 (.branch 142
 (.branch 141
 (.leaf (.leaf 27))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 152
 (.branch 148
 (.branch 146
 (.branch 145
 (.leaf (.leaf 28))
 (.leaf (.leaf 0)))
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
 (.leaf (.leaf 31)))
 (.leaf (.leaf 0)))
 (.branch 166
 (.branch 165
 (.leaf (.leaf 32))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
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
 (.branch 270
 (.branch 269
 (.leaf (.leaf 46))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 280
 (.branch 276
 (.branch 274
 (.branch 273
 (.leaf (.leaf 47))
 (.leaf (.leaf 0)))
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
 (.leaf (.leaf 50)))
 (.leaf (.leaf 0)))
 (.branch 294
 (.branch 293
 (.leaf (.leaf 51))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
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
 (.branch 398
 (.branch 397
 (.leaf (.branch 0x1000000000000000000000000000001000000000000000000000000000000001000000000000000000000000000001000 (.leaf 70) (.leaf 71)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 408
 (.branch 404
 (.branch 402
 (.branch 401
 (.leaf (.leaf 72))
 (.leaf (.leaf 0)))
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
 (.leaf (.branch 0x1000000000000000000000001000000000000000000000000000000000000000200000000000000000000000200000000 (.leaf 76) (.leaf 77))))
 (.leaf (.leaf 0)))
 (.branch 422
 (.branch 421
 (.leaf (.branch 0x1000000000000000000000001000000000000000000000000000000000000001000000000000000000000001000000000 (.leaf 78) (.leaf 79)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
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
 (.branch 526
 (.branch 525
 (.leaf (.leaf 97))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 536
 (.branch 532
 (.branch 530
 (.branch 529
 (.leaf (.leaf 98))
 (.leaf (.leaf 0)))
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
 (.leaf (.leaf 101)))
 (.leaf (.leaf 0)))
 (.branch 550
 (.branch 549
 (.leaf (.leaf 102))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
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
 (.branch 654
 (.branch 653
 (.leaf (.branch 0x10000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000001000 (.leaf 121) (.leaf 122)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 664
 (.branch 660
 (.branch 658
 (.branch 657
 (.leaf (.leaf 123))
 (.leaf (.leaf 0)))
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
 (.leaf (.branch 0x10000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000200000000 (.leaf 127) (.leaf 128))))
 (.leaf (.leaf 0)))
 (.branch 678
 (.branch 677
 (.leaf (.branch 0x10000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000001000000000 (.leaf 129) (.leaf 130)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
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
 (.branch 782
 (.branch 781
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000001000 (.leaf 153) (.leaf 154)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 792
 (.branch 788
 (.branch 786
 (.branch 785
 (.leaf (.leaf 155))
 (.leaf (.leaf 0)))
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
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000200000000 (.leaf 159) (.leaf 160))))
 (.leaf (.leaf 0)))
 (.branch 806
 (.branch 805
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000001000000000 (.leaf 161) (.leaf 162)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
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
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000008 (.branch 0x10000000000000000000000000000000400000000000000000000000000000001000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000008 (.leaf 179) (.branch 0x1000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000008 (.leaf 180) (.leaf 181))) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000400000000000000000000000000000008 (.leaf 182) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000200000000000000000000000000000008 (.leaf 183) (.leaf 184)))))))
 (.branch 902
 (.branch 901
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000 (.leaf 185) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000000 (.leaf 186) (.leaf 187))))
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000020 (.branch 0x10000000000000000000000000000001000000000000000000000000000000001000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000020 (.leaf 188) (.branch 0x1000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000020 (.leaf 189) (.leaf 190))) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000001000000000000000000000000000000020 (.leaf 191) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000200000000000000000000000000000020 (.leaf 192) (.leaf 193))))))
 (.branch 903
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000040 (.branch 0x10000000000000000000000000000001000000000000000000000000000000001000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000040 (.leaf 194) (.branch 0x1000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000040 (.leaf 195) (.leaf 196))) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000001000000000000000000000000000000040 (.leaf 197) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000400000000000000000000000000000040 (.leaf 198) (.leaf 199)))))
 (.leaf (.leaf 0)))))
 (.branch 908
 (.branch 906
 (.branch 905
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000 (.leaf 200) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000000000000000000 (.leaf 201) (.leaf 202))))
 (.leaf (.leaf 0)))
 (.branch 907
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000400 (.branch 0x10000000000000000000000000000010000000000000000000000000000000001000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000400 (.leaf 203) (.branch 0x1000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000400 (.leaf 204) (.leaf 205))) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000010000000000000000000000000000000400 (.leaf 206) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000400000000000000000000000000000400 (.leaf 207) (.leaf 208)))))
 (.leaf (.leaf 0))))
 (.branch 910
 (.branch 909
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000001000 (.branch 0x10000000000000000000000000000010000000000000000000000000000000001000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000001000 (.leaf 209) (.branch 0x1000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000001000 (.leaf 210) (.leaf 211))) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000010000000000000000000000000000001000 (.leaf 212) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000001000000000000000000000000000001000 (.leaf 213) (.leaf 214)))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 920
 (.branch 916
 (.branch 914
 (.branch 913
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000 (.leaf 215) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000000000 (.leaf 216) (.leaf 217))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 944
 (.branch 936
 (.branch 932
 (.branch 930
 (.branch 929
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000 (.leaf 218) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000000000000000000000000 (.leaf 219) (.leaf 220))))
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000200000000000000000000000200000000 (.branch 0x10000000000000000000000010000000000000000000000000000000000000001000000000000000000000000000000020000000000000000000000000000000000000000000000000000000200000000 (.leaf 221) (.branch 0x1000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000001000000000000000000000000000000000000000000000000000000010000000000000000000000000000000200000000 (.leaf 222) (.leaf 223))) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000010000000000000000000000000000000200000000 (.leaf 224) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000200000000000000000000000200000000 (.leaf 225) (.leaf 226))))))
 (.leaf (.leaf 0)))
 (.branch 934
 (.branch 933
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000001000000000000000000000001000000000 (.branch 0x10000000000000000000000010000000000000000000000000000000000000001000000000000000000000000000000100000000000000000000000000000000000000000000000000000001000000000 (.leaf 227) (.branch 0x1000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000001000000000000000000000000000000000000000000000000000000010000000000000000000000000000001000000000 (.leaf 228) (.leaf 229))) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000010000000000000000000000000000001000000000 (.leaf 230) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000001000000000000000000000001000000000 (.leaf 231) (.leaf 232)))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
 (.branch 952
 (.branch 948
 (.branch 946
 (.branch 945
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000001000000000000000000000001000000000000 (.branch 0x10000000000000000000000010000000000000000000000000000000000000001000000000000000000000000000100000000000000000000000000000000000000000000000000000001000000000000 (.leaf 233) (.branch 0x1000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000010000000000000000000000000001000000000000 (.leaf 234) (.leaf 235))) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000010000000000000000000000000001000000000000 (.leaf 236) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000001000000000000000000000001000000000000 (.leaf 237) (.leaf 238)))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 992
 (.branch 976
 (.branch 968
 (.branch 964
 (.branch 962
 (.branch 961
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000 (.leaf 239) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000000000000000000000 (.leaf 240) (.leaf 241))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 966
 (.branch 965
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000001000000000000000100000000000000000 (.branch 0x10000000000000001000000000000000000000000000000000000000000000001000000000000000000000000000000100000000000000000000000000000000000000000000000100000000000000000 (.leaf 242) (.branch 0x1000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000001000000000000000000000000000000000000000000000001000000000000000000000000000000100000000000000000 (.leaf 243) (.leaf 244))) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000001000000000000000000000000000000100000000000000000 (.leaf 245) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000001000000000000000100000000000000000 (.leaf 246) (.leaf 247)))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
 (.branch 984
 (.branch 980
 (.branch 978
 (.branch 977
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000001000000000000000100000000000000000000 (.branch 0x10000000000000001000000000000000000000000000000000000000000000001000000000000000000000000000100000000000000000000000000000000000000000000000100000000000000000000 (.leaf 248) (.branch 0x1000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000001000000000000000000000000000000000000000000000001000000000000000000000000000100000000000000000000 (.leaf 249) (.leaf 250))) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000001000000000000000000000000000100000000000000000000 (.leaf 251) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000001000000000000000100000000000000000000 (.leaf 252) (.leaf 253)))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 1008
 (.branch 1000
 (.branch 996
 (.branch 994
 (.branch 993
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000010000000000000001000000000000000000000000 (.branch 0x10000000000000001000000000000000000000000000000000000000000000001000000000000000000000001000000000000000000000000000000000000000000000001000000000000000000000000 (.leaf 254) (.branch 0x1000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000001000000000000000000000000000000000000000000000001000000000000000000000001000000000000000000000000 (.leaf 255) (.leaf 256))) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000001000000000000000000000001000000000000000000000000 (.leaf 257) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000010000000000000001000000000000000000000000 (.leaf 258) (.leaf 259)))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))))))
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
def candidateMasks (i : Nat) := PackedRawNatGrowth.take 529
  (PackedRawNatGrowth.drop (529*(i%64)) (candidateMasksBlocks.get (i/64)))

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
def badMasks (i : Nat) := PackedRawNatGrowth.take 529
  (PackedRawNatGrowth.drop (529*(i%64)) (badMasksBlocks.get (i/64)))

def signatureMasksBlocks : Table Nat :=
(.branch 2
 (.branch 1
 (.leaf signatureMasksBlock0000)
 (.leaf signatureMasksBlock0001))
 (.branch 3
 (.leaf signatureMasksBlock0002)
 (.branch 4
 (.leaf signatureMasksBlock0003)
 (.leaf signatureMasksBlock0004))))
def signatureMasks (i : Nat) := PackedRawNatGrowth.take 529
  (PackedRawNatGrowth.drop (529*(i%64)) (signatureMasksBlocks.get (i/64)))

def fastKind := rawKind
def candidateSupports := candidateRows
def kindSupports := kindRows
def wellFormedTest (i : Nat) : Bool := RawFacetEmbedding.wellFormedCheck (rawCells i)

def cellTest (i : Nat) := (listBounds 1024 (rawCells i).ridgeMasks && ((rawCells i).ridgeMasks.all (fun q => (candidateMasks q).testBit i) && (decide (rawKind i = (rawCells i).kind) && (decide ((rawCells i).vertices < 1024) && ((List.range 10).all (fun v => decide ((vertexMasks v).testBit i = (rawCells i).vertices.testBit v)) && (SignatureCompatibility.faces (rawCells i)).all (fun q => (SignatureCompatibility.profileMask (SignatureCompatibility.allMask 529) signatureIndex signatureMasks (rawCells i) q).testBit i))))))
def ridgeTest (i : Nat) := decide (candidateMasks i = RawNatGrowthCheck.mask (candidateRows i)) &&
  (candidateRows i).all (fun c => hasNat (rawCells c).ridgeMasks i)
def kindTest (i : Nat) := decide (kindMasks i = RawNatGrowthCheck.mask (kindRows i)) &&
  (kindRows i).all (fun c => decide ((rawCells c).kind = i))
def badTest (i : Nat) := if badMasks i = 0 then true else
  decide (Nat.land (badMasks i) (SignatureCompatibility.cover (SignatureCompatibility.allMask 529)
    vertexMasks signatureIndex signatureMasks (rawCells i)) = 0)

end Papers.RationalityTen.RootedCaches.RootedSevenMixed032

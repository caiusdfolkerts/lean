module
prelude
public import RootedSevenMixed033
public import SignatureCompatibility
public import PackedRawNatGrowth
public import FiniteChecks
public import RawFacetEmbedding
public import RootedSevenMixed033GrowthCachecandidateMasksData000
public import RootedSevenMixed033GrowthCachebadMasksData000
public import RootedSevenMixed033GrowthCachesignatureMasksData000

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenMixed033
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def rawCells := Papers.RationalityTen.FacetUniverses.RootedSevenMixed033.rawCells
def cells (c : Fin 529) := rawCells c.val
def ridgeList := ConcreteGrowth.ridgeList cells
def literalCompatible (a b : Fin 529) := ConcreteGrowth.compatible (cells a) (cells b)
def kind (c : Fin 529) := (cells c).kind
def rawKindCode : Nat := 3101452042208010924945369284704057220690515800232829193597811320713845080201531266669457235888997293599014726003491844776924231607248088895924777307045941114705748446964361189622509924982894188575294322270319853732730005666083201549546752441191114877423431842164040335210938259004413789460091207176583547935396475241412295023593334568807886238939666112412689810376119533728762333347916991930088593843241052357169783611656147632999101242441083840898278418038252494060764126586000
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
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 48
 (.branch 40
 (.branch 36
 (.leaf 0x0)
 (.branch 38
 (.branch 37
 (.leaf 0x0)
 (.leaf 0x1d7759d5751d3749d1741cf739cd731cb729c9721c77185d1705b16859160571585515053148511404f1384d1304b12849120471184511043108411003f0f83d0f03b0e8000037))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 56
 (.leaf 0x0)
 (.branch 60
 (.branch 58
 (.leaf 0x0)
 (.branch 59
 (.leaf 0x0)
 (.leaf 0x769d9760000004)))
 (.leaf 0x0)))))
 (.branch 96
 (.branch 80
 (.branch 72
 (.leaf 0x0)
 (.branch 76
 (.leaf 0x0)
 (.branch 78
 (.leaf 0x0)
 (.branch 79
 (.leaf 0x22889220000004)
 (.leaf 0x0)))))
 (.branch 88
 (.leaf 0x0)
 (.branch 92
 (.branch 90
 (.branch 89
 (.leaf 0x1ec7adea7a5e879de6795e478de2785e077dde775dc76d264952448d224852047d1e4751c46d1a4651845d164551444d124451043d0e4350c42d0a4250841d064150440c000037)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 112
 (.branch 104
 (.branch 100
 (.leaf 0x0)
 (.branch 102
 (.branch 101
 (.leaf 0x1fe7f5fc7edfa7e5f87ddf67d5f47cdf27c5f07bdee7b4d835cd6354d434cd2344d033cce334cc32cca324c831cc6314c430cc2304c02fcbe2f4bc2ecba2e4b82dcb62d4000037)
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
 (.leaf 0x1d8715c36fdbd0d4340c8310bc2e0b02b0a82909c2605814044100380a0200501002001b)))
 (.branch 134
 (.branch 133
 (.leaf 0x0)
 (.leaf 0x75dd5745cf705c06e5b71b86d1ac6a1a0671946418c621805f13c4d1284911c431043e0f43b060130480f0380c01c0600c020028))
 (.branch 135
 (.leaf 0x1bb6e9b56d09b2689825c95250922449023c8d2308805c15048100340b0240601001001b)
 (.leaf 0x0))))
 (.branch 140
 (.branch 138
 (.leaf 0x0)
 (.branch 139
 (.leaf 0x760b02bcad2b0aa2a4a7298a5290a228488000e)
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 152
 (.leaf 0x0)
 (.branch 156
 (.branch 154
 (.branch 153
 (.leaf 0x1ec7a9e6791d84dd364d1334c5304b92d4b12b4a5284611644d124410c4290741904001b)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 176
 (.branch 168
 (.branch 164
 (.branch 162
 (.branch 161
 (.leaf 0x0)
 (.leaf 0x1d874dd272dc920c822007f1f47c1e8791e0771d4741444c12c4811c451003f0f03b001b))
 (.leaf 0x0))
 (.branch 166
 (.branch 165
 (.leaf 0x7f9fc7e1f6735cc71dc63a4e8398e538ce2380df378dd36cda328c8314c4308be2f0b92e0b61404e12c49118441083f0f43a0028)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 184
 (.branch 180
 (.branch 178
 (.branch 177
 (.leaf 0x21083a0a821d861584609815fd7e5f17b5e9795dd7659964585605795a5615555152001b)
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
 (.leaf 0x1fa7e5f27c0fe3f4fb3e8f83dcf53d0f33c8f03bccc31cc630cc2300bb2e8b72d888001b)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 204
 (.branch 202
 (.branch 201
 (.leaf 0x1e879de07794c52d495214651543509415013e4f51a4551444510439094210541088001b)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 216
 (.branch 212
 (.branch 210
 (.branch 209
 (.leaf 0x8320b81202789e1771db6699965d96651936459063d8e6318b5a1635895f5795c55d5654d52465174511243d0d42d08419030028)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 240
 (.branch 232
 (.branch 228
 (.branch 226
 (.branch 225
 (.leaf 0x81a05801ff7d1f37b9ed6bdae6b1ab6a5a8699a5691a3685a059d65589605755b565565515132cc9318c4304bf2f4ba2e0b50028)
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
 (.leaf 0x1d9711c16f9bb0dc360cc320c02f0b42b0a82809c25088200741c0680901c0600c01001b)))
 (.branch 262
 (.branch 261
 (.leaf 0x0)
 (.leaf 0x759d3741cd70dc26e1b51c06f1b06b1a4681986418c611805e16c591585514c421003f0f03a0901f0781b0680b02005010010028))
 (.branch 263
 (.leaf 0x1bd6f1b76d89d270992609625493244902388d22c8908c210781c0640c0280500c02001b)
 (.leaf 0x0))))
 (.branch 268
 (.branch 266
 (.leaf 0x0)
 (.branch 267
 (.leaf 0x764b22c4ae2b4ab2a8a8298a528ca228089000e)
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 280
 (.leaf 0x0)
 (.branch 284
 (.branch 282
 (.branch 281
 (.leaf 0x1eb7a1e5789d94e5384d5344c9314bd2d4b12a4a5274912247d1e4710b4250841503001b)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 304
 (.branch 296
 (.branch 292
 (.branch 290
 (.branch 289
 (.leaf 0x0)
 (.leaf 0x1d9755d4729c721484204801f87d1ec791e0761d4731745815c5414c441043e0f43a001b))
 (.leaf 0x0))
 (.branch 294
 (.branch 293
 (.leaf 0x7f5fa7ddf473dce725c83acea39ce6390e3384df378dc36cd9358d4344d0338bd2ecba2dcb51705a15c551484510c3e0f03b0028)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 312
 (.branch 308
 (.branch 306
 (.branch 305
 (.leaf 0x20f83209819d961d8660d826017f5f57b5e9785dd755c9705b56c5a95955d5654d51001b)
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
 (.leaf 0x1fc7edf17b9003fcfc3ecf93e0f63d0f33c4f03b8d834cd233cce2fcbc2e4b82d489001b)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 332
 (.branch 330
 (.branch 329
 (.leaf 0x1ea7a5df7714e5354a5254751944509414fd3e4f126485204751c4350a41d0640c89001b)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 344
 (.branch 340
 (.branch 338
 (.branch 337
 (.leaf 0x83a0d80e00791e3779dd6719b66197655946499063d8d6318a5d16f5b96b5a95b5615555151495234811e46d0e43107415040028)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 368
 (.branch 360
 (.branch 356
 (.branch 354
 (.branch 353
 (.leaf 0x8220780a017d9f57c1ef6c5b06b5ac6a9a969da5691a26859f5cd715b96c5a55c5695554d5235cd5348d0334c02f8b92dcb60028)
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
 (.leaf 0x1d7759d4749c5711c27008520c7e1f07b1e8771d8751c06e1a4671986518861180411003f0f83d0f0370d4300b82d0b0290a027020070180501003002f))
 (.branch 387
 (.leaf 0x1bf6f9bc6e8b22c0ab2a4a829ca428ca22749b2589424c9223c8e234360d0330c42d0b02a098250280901805008010025)
 (.leaf 0xe4380300b0004)))
 (.branch 390
 (.branch 389
 (.leaf 0x7f9fd7edf9745d0739cc6e5b86d9b4400fe3e4f73d8f53c8f13c0eb3a4e4388e1380dd370db2f0bb2e8b92e0b72709a2649724c922408c22c6f1b46c1a8661946317c5e10c420fc3e0ec3a0300b01003008010042)
 (.leaf 0x1c87111444028090006))
 (.branch 391
 (.leaf 0x27c9e020070004)
 (.leaf 0x0))))
 (.branch 396
 (.branch 394
 (.branch 393
 (.leaf 0x1ec7ade979d4e531475154450d404fd3e4e5374c9304bd2e4ad2a4a50a4250841d06414b12bcae2b0a829ca5284a00025)
 (.leaf 0x0))
 (.branch 395
 (.leaf 0x2d0b30002)
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 408
 (.branch 404
 (.branch 402
 (.branch 401
 (.leaf 0x21083e0d82de6795e37859c6699564d926458e6358c61d856017e5f57c5e5785dd5855d565555454d384d9354cd2f4b92c4a1274310b4210741103002f)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 412
 (.branch 410
 (.branch 409
 (.leaf 0x4ed3a4390d0004)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 432
 (.branch 424
 (.branch 420
 (.branch 418
 (.branch 417
 (.leaf 0x82a0981e057e1f77d5f372dca721c66c5af6a9a869da668da268586611836057d5f17a5d9755695955955549513a8e839ce5384e0378da364be2f4ba2e4b62d484208811fc7b1e8781d073114440f43c0ec3a0042)
 (.leaf 0x21c8610c420004))
 (.leaf 0x0))
 (.branch 422
 (.branch 421
 (.leaf 0x3b4ec300bf104400006)
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
 (.leaf 0x81203805ff7c9f17bded781df775db6c1ae6b5ab69da6691a067d9b66598659926458f62d8a5715b55153549515354b52948511435053d4f10e435064150440cff3f4fc3e8f63d4f33bcee300bf2e0b72d8b50042)
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 454
 (.branch 453
 (.leaf 0x409012f8bd0004)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 460
 (.branch 458
 (.branch 457
 (.leaf 0x5414f4310b0004)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 472
 (.branch 468
 (.branch 466
 (.branch 465
 (.leaf 0x6799d56959429090006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 496
 (.branch 488
 (.branch 484
 (.branch 482
 (.branch 481
 (.leaf 0x6cdb2561572f0bb0006)
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
 (.leaf 0x1da709c06f1ba0e4380cc310c02e0b42c0a428098250841f0781b0641504c1203c0d001b)))
 (.branch 518
 (.branch 517
 (.leaf 0x0)
 (.leaf 0x751d2739cc715c46d9b41c8711b06a1a467198651886117c5e1685815c541484e1304b1204608c200741c06417050110400d0028))
 (.branch 519
 (.leaf 0x1bf6f9b96e09f2789925c96250932488f2388c22c8a090220741b068180581103c0e001b)
 (.leaf 0x0))))
 (.branch 524
 (.branch 522
 (.leaf 0x0)
 (.branch 523
 (.leaf 0x768b42ccae2b0ab2a4a829ca428ca12808a000e)
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 536
 (.leaf 0x0)
 (.branch 540
 (.branch 538
 (.branch 537
 (.leaf 0x1e979de3785da4ed3a4d5334c9304bd2e4ad2a4a12748d214811d46d17455144450f001b)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 560
 (.branch 552
 (.branch 548
 (.branch 546
 (.branch 545
 (.leaf 0x0)
 (.leaf 0x1da75dd6721c621c862047f1f87c1ec7a1dc761d0731705915855148501344a12446001b))
 (.leaf 0x0))
 (.branch 550
 (.branch 549
 (.leaf 0x7edf97d5f3745d072dca3b4ec39ce5390e2384e0374dc368d9354d3348cf334c931cc630cc11745b1585414c5113c4a120470028)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 568
 (.branch 564
 (.branch 562
 (.branch 561
 (.leaf 0x20d82e07815da6258860d816017e5f57c5e5785d9755c56f5b96b5a56558d6257d5d001b)
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
 (.leaf 0x1fe7f5ef7b502404fc3e8f93dcf63d4f23c4ef3b8d7350d1340cd32cc8314c43048a001b)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 588
 (.branch 586
 (.branch 585
 (.leaf 0x1ec7addd76d5053d4a521475154450d404fd3d4f1254891f4791b4651644d1243c8a001b)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 600
 (.branch 596
 (.branch 594
 (.branch 593
 (.leaf 0x8420f805ff799e5781df6799d6619665593649916398d62d8a5cd705b56c5a567591615815d4992447d1d4711a46113445100028)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 624
 (.branch 616
 (.branch 612
 (.branch 610
 (.branch 609
 (.leaf 0x82a09812037e1f77c9f16cdb26b5ab6a9a869da668da26819f5d1725b56b5a9685996157d5e360d6344cf338cc328c530cc20028)
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
 (.leaf 0x1d6755d474dc470dc2704872087e1f47b1e4781d8741c86d1a4681986418c6117c4d1304b12849120390d0300bc2d0ac2a0a02605013048110400f002f))
 (.branch 643
 (.leaf 0x1be6f5bc6ecb42bcab2a8a8298a528ca127c9a2589524c912408e230380d4330c82d0ac2909c2505815048110380d0025)
 (.leaf 0xdc36060170004)))
 (.branch 646
 (.branch 645
 (.leaf 0x7f5fc7edfa741cf739cd6e1b76d9b5408fd3e4f83d8f43ccf13bced3a0e438ce137cde370da320c7318c5310c32789b2649824c9123c8d22c711b86c1ac66190621805e13c4e12c4a11c46060170400f0380d0042)
 (.leaf 0x1c06f14450058150006))
 (.branch 647
 (.leaf 0x2749c050130004)
 (.leaf 0x0))))
 (.branch 652
 (.branch 650
 (.branch 649
 (.leaf 0x1eb7a9e97a15052d4751944509414fd3d4ed364c9314bd2d4b12a4a1164551444d12444b32c0ae2b4a8298a4288a00025)
 (.leaf 0x0))
 (.branch 651
 (.leaf 0x2c8b10002)
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 664
 (.branch 660
 (.branch 658
 (.branch 657
 (.leaf 0x20f83a0d831e5791e37899e66595651926418f6358b625846017f5f57b5e9785d96458d625856057d3a4dd354d12f4b52b4a52746117451134410f002f)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 668
 (.branch 666
 (.branch 665
 (.leaf 0x4e538469190004)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 688
 (.branch 680
 (.branch 676
 (.branch 674
 (.branch 673
 (.leaf 0x8260881e067ddf67d5f4729c9721c76cdae6a9a969da5691a268188615836097d5ed795dd7559965589615795d3b0e939ce6384df374db364ca324c6314c23048620c812007b1e4771d473144501244811c460042)
 (.leaf 0x2148413c4e0004))
 (.leaf 0x0))
 (.branch 678
 (.branch 677
 (.leaf 0x3acea330cb1344c0006)
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
 (.leaf 0x80e02806007c5f07bdee77dde775dc6c9af6b5ac69da568da167d9d6699865d926418e6318a5a1675815f5795d53d4c52949511425013e4f11a465124451043d013f8fc3ecf63d0f23c0ee330cb310c3308c10042)
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 710
 (.branch 709
 (.leaf 0x400ff328c90004)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 716
 (.branch 714
 (.branch 713
 (.leaf 0x5394d461170004)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 728
 (.branch 724
 (.branch 722
 (.branch 721
 (.leaf 0x6719b59965459150006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 752
 (.branch 744
 (.branch 740
 (.branch 738
 (.branch 737
 (.leaf 0x6c5b059163320c70006)
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
 (.leaf 0x1d7755d3749c570dc1700862107d1f07a1e4781dc731c46f1a0671946418c62178591605715855150380d82f0b82c0ac2a0a4250801f0781d0701b002f))
 (.branch 771
 (.leaf 0x1bf6f5bb6e8b32c4aa2a4a7298a5290a02789c25494248912408f22c390dc320c42c0ac2809c26088210781d068190025)
 (.leaf 0xd434090230004)))
 (.branch 774
 (.branch 773
 (.leaf 0x7f9fc7e9f9745cf735cc6e5b76d5b4404ff3e0f73d4f43ccf23b8ec3a8e3388e037cde374d9350d3348d1340cf27c9d26097248912388d230721c06b1a865190611805f16c5a15c5614c52090230701b068190042)
 (.leaf 0x1b86d1745c088210006))
 (.branch 775
 (.leaf 0x26c9a0801f0004)
 (.leaf 0x0))))
 (.branch 780
 (.branch 778
 (.branch 777
 (.leaf 0x1ec7a9e879d4f5354651543509415013c4e9384c5304b92d4b12b49d224852047d1e474b42c8ad2b0a7298a3288a10025)
 (.leaf 0x0))
 (.branch 779
 (.leaf 0x2c0af0002)
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 792
 (.branch 788
 (.branch 786
 (.branch 785
 (.leaf 0x21083a0c82de6791e27859d66d9464d916418f6398a621865fd7e5f17b5e9795d5705bd6e5b56c5ad3b4e5344cd2e4b52a4a528491234811f4711b002f)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 796
 (.branch 794
 (.branch 793
 (.leaf 0x4dd36499250004)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 816
 (.branch 808
 (.branch 804
 (.branch 802
 (.branch 801
 (.leaf 0x82a0881a057e1f67d1f372dc971dc66c9b06a5a8699a5691a367d8961d826057c5ed785dd765c9715b96d5a9693b4eb398e5380df370db368d6354d2344ce33487214801fc7a1e4761d4741745c1545414c520042)
 (.leaf 0x20c8216c5a0004))
 (.leaf 0x0))
 (.branch 806
 (.branch 805
 (.leaf 0x3a4e8360d7164580006)
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
 (.leaf 0x81202801ff7c9f07b9ed781de771db6cdb16b1ab699a5689a16819e67197659916418d6318b5d1735b16b5a9695414e5254850d424fd3e4f5264951e4751c46d02400fb3e8f53d0f13c0ef360d7340cf338cd0042)
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 838
 (.branch 837
 (.leaf 0x3f8fd358d50004)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 844
 (.branch 842
 (.branch 841
 (.leaf 0x5314b491230004)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 856
 (.branch 852
 (.branch 850
 (.branch 849
 (.leaf 0x669995c971489210006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 880
 (.branch 872
 (.branch 868
 (.branch 866
 (.branch 865
 (.leaf 0x6bdae5c16f350d30006)
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
 (.leaf 0x6cdb26c5b06bdae691a3689a16819f6799d6719b6699963d8e6358c62d8a6258861d86615845e9795e1775d9755414f5394d5314b505404fd3e4f53c4ed3a4e5384dd364b12b4a9294a12740901400ff3f8fd3ccf23c4f03bcee3b4ec3acea3a4e8378dd370db368d92d0b32c8b12c0af294a428ca2284a027c9e2749c26c9a2408f2388d2308b21c862148420c821e0771d8751d0731c8711c06f1b86d18c621846017c5e0e4380dc360d4340a8290a027098250090)
 (.leaf 0x812007f1b06b1a8330c8310009))
 (.branch 899
 (.leaf 0xae2b4ac2649825c300bc2e0009)
 (.leaf 0x6e5b86ddb66d5b40006)))
 (.branch 902
 (.branch 901
 (.leaf 0x3f0fb3e8e7398e525895250691a067000c)
 (.leaf 0x72dca725c871dc66fdbe6f5bc6edba000c))
 (.branch 903
 (.leaf 0x715c470dc2705c00006)
 (.leaf 0x0))))
 (.branch 908
 (.branch 906
 (.branch 905
 (.leaf 0x14a525484d5344ccab2a8a90009)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 920
 (.branch 916
 (.branch 914
 (.branch 913
 (.leaf 0x19865d9660d82605324c5300009)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 924
 (.branch 922
 (.branch 921
 (.leaf 0x781df779dd771db0006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 944
 (.branch 936
 (.branch 932
 (.branch 930
 (.branch 929
 (.leaf 0x6b5ac6ad805fd7e390e33887e1f47c000c)
 (.leaf 0x745d073dce735cc0006))
 (.leaf 0x0))
 (.branch 934
 (.branch 933
 (.leaf 0x7c9f17c1ef7b9ed75dd6755d474dd2000c)
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
 (.leaf 0x6a9a96a1956519351d46514f93e0f7000c)
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 966
 (.branch 965
 (.leaf 0x7e1f77d9f57d1f30006)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 972
 (.branch 970
 (.branch 969
 (.leaf 0x799e5791e3789e10006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 984
 (.branch 980
 (.branch 978
 (.branch 977
 (.leaf 0x82a098220781a057b1eb7a9e97a1e7000c)
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
 (.leaf 0x69da6695a468da2685a067d926459063d8e6358c62d8a5f57c5ed7a5e5785dd765d56e5b56c5ad6a5a5625856057d5e575565555454d525454450d42505404fd3e4f53c4bd2e4b52c4ad2a4a52849d2047d1e4751c46d1444d124451043d0841d064150440cf63d4f43ccf23c4f03bcee384e037cde374dc36cda364d2344d033cce334c6314c430cc2304ba2e4b82dcb62d4a829ca6294a428ca2284a024c922449023c8e2348c22c7b1e8791e0771d8751d0731986519063188611805f1785715855150531484b12849120471183f0f83d0f03b0e82d0b02b0a8290a027098250781d0701b06819048110400f0380d01805010030080100c6)
 (.branch 4
 (.leaf 0x1b36c9b16c1af6b9ad6b1ab6a9a96a19e6759c66d9a6659865d966559464d89621876198561183609816017f5f9745cd725c5705bd6859d665956458d5c56d5a5655855d5053d4e5354c52d4a5254851d465153b4e9394e1374d9354d1334c9314c1264952448d224851a4651845d164550e4350c42d0a42502405003fcfe3f4fc3ecfa3e4f83dced3b0eb3a8e93a0e7398e5390e3388d835cd6354d434ccc32cca324c831cc02fcbe2f4bc2ecb42ccb22c4b02bcae2b4ac2acaa2a49f2789d2709b2689926097258952508a2248821c862148420c82204801fc7e1f47c1c8711c06f1b86d1b06b1a8691a0671745c16c5a164581445013c4e1344c1144410c42104400e4380dc360d4340cc320c4300bc2e09023088210801f0601705815050130300b028090200700ed)
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
 (.leaf 0xff8007fc003fe07e07e07e001ff000ff81f81f81f8007fc003fe07e07e07e001ff000ff8000ff8007fc0fc0fc0fc003fe07e07e07e)
 (.branch 4
 (.leaf 0xfff007ff803ffc01f81f81f81ffe00fff007e07e07e07ff803ffc01f81f81f81ffe00fff007fff007ff803f03f03f03ffc01f81f81f80)
 (.leaf 0x1fffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))))
def kindMasks := kindMaskTable.get
def keys := List.range 5
def vertexMaskTable : Table Nat :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf 97554642197197306370251181280023428546858534601260416491524602727481956144958339865060005680859565736841038950477484174627843310883237231853567)
 (.leaf 85360358440203816635257812257867577497318271739522456921836878869318095351108069668932155906986127636969653034416406162303007128804076793364479))
 (.branch 3
 (.leaf 6703878391619368691453147414851827230149172755154257281555877995232288293605141111256481026789139368209085277973974349699672831997502340628099676753625087)
 (.branch 4
 (.leaf 25573351929858333687633390672101439497136634154529916975566881295988851106537506831551736299939927247955256438305025318710239245951263235680248004609)
 (.leaf 1757381497115044467666675151239971035985177141802733188607423192888991912091990702683967187904847409834712521470043098573279100876174104893286944491171221602305))))
 (.branch 7
 (.branch 6
 (.leaf 1757388200967862820465773676079211706757036586288278841060195861586454513451815439729939992771222126307354282882587280225668470125491278186917423102908835037185)
 (.leaf 1757388200993435989480724407367530293369753809178151790837817912223391515325876449439668655416036663960220508645386629190274749254844459533138589178275926376449))
 (.branch 8
 (.leaf 1757388200993436013869384956533768740614790363540116330069295982704822796958771128554633936023733864063621772417822167100026069870601707295707400444391362396158)
 (.branch 9
 (.leaf 1757388200993436026063715231205613394449154542438902079714258931954861241560569893774696509028705668953843828159552718205308291100708593748581445778967992737790)
 (.leaf 1757388200993436050452375780549302702117882900198018538167128821294104850539959768018734374373124640194344456668437738436451049456079010057809744839712016687104)))))
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
 (.leaf (.leaf 0))
 (.branch 28
 (.branch 26
 (.branch 25
 (.leaf (.leaf 5))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 48
 (.branch 40
 (.branch 36
 (.branch 34
 (.branch 33
 (.leaf (.leaf 0))
 (.leaf (.leaf 6)))
 (.leaf (.leaf 0)))
 (.branch 38
 (.branch 37
 (.leaf (.leaf 7))
 (.leaf (.leaf 8)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
 (.branch 56
 (.branch 52
 (.branch 50
 (.branch 49
 (.leaf (.leaf 9))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 60
 (.branch 58
 (.leaf (.leaf 0))
 (.branch 59
 (.leaf (.leaf 0))
 (.leaf (.leaf 10))))
 (.leaf (.leaf 0))))))
 (.branch 96
 (.branch 80
 (.branch 72
 (.branch 68
 (.leaf (.leaf 0))
 (.branch 70
 (.branch 69
 (.leaf (.leaf 11))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 76
 (.branch 74
 (.branch 73
 (.leaf (.leaf 12))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 78
 (.leaf (.leaf 0))
 (.branch 79
 (.leaf (.leaf 13))
 (.leaf (.leaf 0))))))
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
 (.leaf (.leaf 0))))
 (.branch 152
 (.branch 148
 (.branch 146
 (.branch 145
 (.leaf (.leaf 27))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 156
 (.branch 154
 (.branch 153
 (.leaf (.leaf 28))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 176
 (.branch 168
 (.branch 164
 (.branch 162
 (.branch 161
 (.leaf (.leaf 29))
 (.leaf (.leaf 30)))
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
 (.leaf (.leaf 0)))
 (.branch 198
 (.branch 197
 (.leaf (.leaf 34))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
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
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 284
 (.branch 282
 (.branch 281
 (.leaf (.leaf 47))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 304
 (.branch 296
 (.branch 292
 (.branch 290
 (.branch 289
 (.leaf (.leaf 48))
 (.leaf (.leaf 49)))
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
 (.leaf (.leaf 0)))
 (.branch 326
 (.branch 325
 (.leaf (.leaf 53))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
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
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 412
 (.branch 410
 (.branch 409
 (.leaf (.branch 0x1000000000000000000000000000100000000000000000000000000000000010000000000000000000000000001000000 (.leaf 71) (.leaf 72)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 432
 (.branch 424
 (.branch 420
 (.branch 418
 (.branch 417
 (.leaf (.leaf 73))
 (.leaf (.branch 0x1000000000000000000000001000000000000000000000000000000000000000200000000000000000000000200000000 (.leaf 74) (.leaf 75))))
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
 (.leaf (.leaf 0)))
 (.branch 454
 (.branch 453
 (.leaf (.branch 0x1000000000000000100000000000000000000000000000000000000000000001000000000000000100000000000000000 (.leaf 81) (.leaf 82)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
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
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 540
 (.branch 538
 (.branch 537
 (.leaf (.leaf 98))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 560
 (.branch 552
 (.branch 548
 (.branch 546
 (.branch 545
 (.leaf (.leaf 99))
 (.leaf (.leaf 100)))
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
 (.leaf (.leaf 0)))
 (.branch 582
 (.branch 581
 (.leaf (.leaf 104))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
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
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 668
 (.branch 666
 (.branch 665
 (.leaf (.branch 0x10000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000001000000 (.leaf 122) (.leaf 123)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 688
 (.branch 680
 (.branch 676
 (.branch 674
 (.branch 673
 (.leaf (.leaf 124))
 (.leaf (.branch 0x10000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000200000000 (.leaf 125) (.leaf 126))))
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
 (.leaf (.leaf 0)))
 (.branch 710
 (.branch 709
 (.leaf (.branch 0x10000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000100000000000000000 (.leaf 132) (.leaf 133)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
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
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 796
 (.branch 794
 (.branch 793
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000001000000 (.leaf 154) (.leaf 155)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 816
 (.branch 808
 (.branch 804
 (.branch 802
 (.branch 801
 (.leaf (.leaf 156))
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000200000000 (.leaf 157) (.leaf 158))))
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
 (.leaf (.leaf 0)))
 (.branch 838
 (.branch 837
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000100000000000000000 (.leaf 164) (.leaf 165)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
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
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 920
 (.branch 916
 (.branch 914
 (.branch 913
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000 (.leaf 203) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000000000 (.leaf 204) (.leaf 205))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 924
 (.branch 922
 (.branch 921
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000010000000000000000000000000001000000 (.branch 0x10000000000000000000000000001000000000000000000000000000000000001000000000000000000000000000001000000000000000000000000000000000000000000000000000000000001000000 (.leaf 206) (.branch 0x1000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000001000000000000000000000000000001000000 (.leaf 207) (.leaf 208))) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000001000000000000000000000000000001000000 (.leaf 209) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000010000000000000000000000000001000000 (.leaf 210) (.leaf 211)))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 944
 (.branch 936
 (.branch 932
 (.branch 930
 (.branch 929
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000 (.leaf 212) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000000000000000000000000 (.leaf 213) (.leaf 214))))
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000200000000000000000000000200000000 (.branch 0x10000000000000000000000010000000000000000000000000000000000000001000000000000000000000000000000020000000000000000000000000000000000000000000000000000000200000000 (.leaf 215) (.branch 0x1000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000001000000000000000000000000000000000000000000000000000000010000000000000000000000000000000200000000 (.leaf 216) (.leaf 217))) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000010000000000000000000000000000000200000000 (.leaf 218) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000200000000000000000000000200000000 (.leaf 219) (.leaf 220))))))
 (.leaf (.leaf 0)))
 (.branch 934
 (.branch 933
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000001000000000000000000000001000000000 (.branch 0x10000000000000000000000010000000000000000000000000000000000000001000000000000000000000000000000100000000000000000000000000000000000000000000000000000001000000000 (.leaf 221) (.branch 0x1000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000001000000000000000000000000000000000000000000000000000000010000000000000000000000000000001000000000 (.leaf 222) (.leaf 223))) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000010000000000000000000000000000001000000000 (.leaf 224) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000001000000000000000000000001000000000 (.leaf 225) (.leaf 226)))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
 (.branch 952
 (.branch 948
 (.branch 946
 (.branch 945
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000001000000000000000000000001000000000000 (.branch 0x10000000000000000000000010000000000000000000000000000000000000001000000000000000000000000000100000000000000000000000000000000000000000000000000000001000000000000 (.leaf 227) (.branch 0x1000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000010000000000000000000000000001000000000000 (.leaf 228) (.leaf 229))) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000010000000000000000000000000001000000000000 (.leaf 230) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000001000000000000000000000001000000000000 (.leaf 231) (.leaf 232)))))
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
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000 (.leaf 233) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000000000000000000000 (.leaf 234) (.leaf 235))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 966
 (.branch 965
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000001000000000000000100000000000000000 (.branch 0x10000000000000001000000000000000000000000000000000000000000000001000000000000000000000000000000100000000000000000000000000000000000000000000000100000000000000000 (.leaf 236) (.branch 0x1000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000001000000000000000000000000000000000000000000000001000000000000000000000000000000100000000000000000 (.leaf 237) (.leaf 238))) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000001000000000000000000000000000000100000000000000000 (.leaf 239) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000001000000000000000100000000000000000 (.leaf 240) (.leaf 241)))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 972
 (.branch 970
 (.branch 969
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000010000000000000001000000000000000000 (.branch 0x10000000000000001000000000000000000000000000000000000000000000001000000000000000000000000000001000000000000000000000000000000000000000000000001000000000000000000 (.leaf 242) (.branch 0x1000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000001000000000000000000000000000000000000000000000001000000000000000000000000000001000000000000000000 (.leaf 243) (.leaf 244))) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000001000000000000000000000000000001000000000000000000 (.leaf 245) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000010000000000000001000000000000000000 (.leaf 246) (.leaf 247)))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
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

end Papers.RationalityTen.RootedCaches.RootedSevenMixed033

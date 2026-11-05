module
prelude
public import RootedSevenMixed030
public import SignatureCompatibility
public import PackedRawNatGrowth
public import FiniteChecks
public import RawFacetEmbedding
public import RootedSevenMixed030GrowthCachecandidateMasksData000
public import RootedSevenMixed030GrowthCachebadMasksData000
public import RootedSevenMixed030GrowthCachesignatureMasksData000

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenMixed030
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def rawCells := Papers.RationalityTen.FacetUniverses.RootedSevenMixed030.rawCells
def cells (c : Fin 655) := rawCells c.val
def ridgeList := ConcreteGrowth.ridgeList cells
def literalCompatible (a b : Fin 655) := ConcreteGrowth.compatible (cells a) (cells b)
def kind (c : Fin 655) := (cells c).kind
def rawKindCode : Nat := 1909428634139068099126008873369148905825265187784589029578563119992890297755150513352060368411818835083471685380188385461817677626263531377846122940898364153532829746001544458165185895199024075248929190416153128539086400594876359743783162238689494449595931795102907770309987104920687077603326638695474950973691940035336460336909683228167033866850304789207144243175328882530271002457615093207954399356001788987357197027245329532161576479349130659008345551024449678569916090861907208291373253432618739413547886304448578149291690535004177138389925507155995339835615574193098482135807768494941328
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
 (.leaf 0x21f87a1d8721b86a198621785a158521384a118420f8382408c220842007c1e0741c06c1a0641805c160541404c120441003c0e0340c02c0a0240801c060140400c02004000037))))
 (.branch 12
 (.leaf 0x0)
 (.branch 14
 (.leaf 0x0)
 (.branch 15
 (.leaf 0x2318c22f8ba2d8b22b8aa298a22789a258922388a21880ab2a8a92a0a7298a5290a3288a12809f2789d2709b26899260972589525093248912408f2388d2308b22889220000037)
 (.leaf 0x0)))))
 (.branch 24
 (.leaf 0x0)
 (.branch 28
 (.leaf 0x0)
 (.branch 30
 (.branch 29
 (.leaf 0x24390a419023f8fa3d8f23b8ea398e2378da358d2338c8f93e0f73d8f53d0f33c8f13c0ef3b8ed3b0eb3a8e93a0e7398e5390e3388e1380df378dd370db368d9360d7358000037)
 (.leaf 0x0))
 (.leaf 0x0)))))
 (.branch 48
 (.branch 40
 (.branch 36
 (.leaf 0x0)
 (.branch 38
 (.branch 37
 (.leaf 0x0)
 (.leaf 0x2559525394a519424f93a4d9324b92a499224791a459105d1705b16859160571585515053148511404f1384d1304b12849120471184511043108411003f0f83d0f03b0e8000037))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 56
 (.leaf 0x0)
 (.branch 60
 (.branch 58
 (.leaf 0x0)
 (.branch 59
 (.leaf 0x0)
 (.leaf 0x96257958000004)))
 (.leaf 0x0)))))
 (.branch 96
 (.branch 80
 (.leaf 0x0)
 (.branch 88
 (.branch 84
 (.leaf 0x0)
 (.branch 86
 (.branch 85
 (.leaf 0x26a9a66899e669966498e629866097e5e9765c96e5a965324c5304bd2e4b52c4ad2a4a52849d264952448d224852047d1e4751c46d1a4651845d164551444d124451043c000037)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 112
 (.branch 104
 (.branch 100
 (.leaf 0x0)
 (.branch 102
 (.branch 101
 (.leaf 0x27c9ee7a9e6789de769d6749ce729c6709be6e9b66c9ad6b5a9695a1675996559163589615815f5795d5715b56959561575595555153549515414f5394d5314b52949520000037)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 120
 (.branch 116
 (.branch 114
 (.branch 113
 (.leaf 0x28ea368ca2e8aa2688a1e86a1684a0e82a06809fe7e9f5ce735cc72dca725c871dc6715c470dc2705c06fdbe6f5bc6edba6e5b86ddb66d5b46cdb26c5b06bdae6b5ac6ac000037)
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
 (.leaf 0x25687e1d866170d4340c8310bc2e0b02b0a82909c2605814044100380a0200501002001b)))
 (.branch 134
 (.branch 133
 (.leaf 0x0)
 (.leaf 0x9565393e4d86e1a84e111b86d1ac6a1a0671946418c621805f13c4d1284911c431043e0f43b060130480f0380c01c0600c020028))
 (.branch 135
 (.leaf 0x8c62f8ae298561483e0e2f0bb2e4b82d8b52ccb22c4b02b8ad2749b260972549123c8c22c8905c15048100340b02406010010028)
 (.leaf 0x0))))
 (.branch 140
 (.branch 138
 (.leaf 0x0)
 (.branch 139
 (.leaf 0x2568b62c89623344d0338cd32cca320c7318c530cc227c9a26496254932388d22889001b)
 (.leaf 0x0)))
 (.branch 142
 (.branch 141
 (.leaf 0x90e418f63b89e26886204290941d0641103405003fcfe3f0fb3ace9398e538cdf374da364d72789c26497250922408d22c880028)
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 152
 (.branch 148
 (.leaf 0x0)
 (.branch 150
 (.branch 149
 (.leaf 0x9aa68992628fe3e8de3550d425013f4f53c4e9394e1374d5344912247d1e4711845913449103b4e839ce438ce1370db360d70028)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 156
 (.branch 154
 (.branch 153
 (.leaf 0x2568e6388ce32699a568da26819f6759c66d9a661973b0ea39ce5388e0378db364d6001b)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 176
 (.branch 168
 (.branch 164
 (.branch 162
 (.branch 161
 (.leaf 0x0)
 (.leaf 0x256946509264720c822007f1f47c1e8791e0771d4741444c12c4811c451003f0f03b001b))
 (.leaf 0x0))
 (.branch 166
 (.branch 165
 (.leaf 0x9f27a9da7492e4a916445f17b5e5785d9755cd725c5705b96d5755b561575555153d4c52d491404e12c49118441083f0f43a0028)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 184
 (.branch 180
 (.branch 178
 (.branch 177
 (.leaf 0x28ea3288a1a5677dde771db765d8759d5751d3745d0701be6edba6e1b46c9af6b9ac001b)
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
 (.leaf 0x9e2779c26e99a6597a5c645906398d62d8a621876198560d8257d5a56556555535394d52949499214811d4711a45514445100028)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 216
 (.branch 212
 (.branch 210
 (.branch 209
 (.leaf 0xa2a89a0a809825f96a597d1f37c5f07b9ed7adea7a5e8799e5709bd6f1b96e1b66c5b06b5ac495234811e46d1945d144490f0028)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 240
 (.branch 232
 (.branch 228
 (.branch 226
 (.branch 225
 (.leaf 0xa12839fa7d9ca719b26b8260881a0580e02801ff7f9fd7edfa705bf6f1ba6ddb56cdb06b9ab5795c56557551525414d52d480028)
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
 (.leaf 0x25787a1b862150dc360cc320c02f0b42b0a82809c25088200741c0680901c0600c01001b)))
 (.branch 262
 (.branch 261
 (.leaf 0x0)
 (.leaf 0x9525193a4b8761c84a0f1c06f1b06b1a4681986418c611805e16c591585514c421003f0f03a0901f0781b0680b02005010010028))
 (.branch 263
 (.leaf 0x8c22d8aa2785e16846102f8bd2e8b92dcb62d0b22c4af2b8ac2a4a7290a3284902388d2288808c210781c0640c0280500c020028)
 (.leaf 0x0))))
 (.branch 268
 (.branch 266
 (.leaf 0x0)
 (.branch 267
 (.leaf 0x2578be2e8922134cd233cce330cb324c7318c430cc12aca6294a22849223c8c22c88001b)
 (.leaf 0x0)))
 (.branch 270
 (.branch 269
 (.leaf 0x90a3f8f2398a62888e224310b4210741504409003fcfd3f0fa3dcf53c8f13bcde370db360d62a8a8294a3280932448c228890028)
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 280
 (.branch 276
 (.leaf 0x0)
 (.branch 278
 (.branch 277
 (.leaf 0x9a66698e60906408da3351544505404f93d4ed394e1364d5334c12e4ad2a4a117455144450f3e4f43ccf03bce0374da364d60028)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 284
 (.branch 282
 (.branch 281
 (.leaf 0x2578ee3a8d6346a1a7691a3685a06799c66d99661963e0f63ccf13b8e137cda360d7001b)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 304
 (.branch 296
 (.branch 292
 (.branch 290
 (.branch 289
 (.leaf 0x0)
 (.leaf 0x25794e529224521484204801f87d1ec791e0761d4731745815c5414c441043e0f43a001b))
 (.leaf 0x0))
 (.branch 294
 (.branch 293
 (.leaf 0x9ee789d6729364c91e465f97d5e9795dd765d1725c56f5b96c5a56759163585505394d529481705a15c551484510c3e0f03b0028)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 312
 (.branch 308
 (.branch 306
 (.branch 305
 (.leaf 0x28da2a87a1257785e0775dc769d975dd5751d2745cf731ca71dc6711b36c5b06b5ab001b)
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
 (.leaf 0x9ea799be6c9a2679765a64d9263d8e6318b625876198460d815ad66595625855253d4c52d484c92d4b1294a119459134490f0028)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 344
 (.branch 340
 (.branch 338
 (.branch 337
 (.leaf 0xa328ba067e98a619725b7d9f57c9f17bdee7b1ea7a5e7799e4739c9721c5711b56c9af6b9ab4c52f4b12a49d1a46113445100028)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 368
 (.branch 360
 (.branch 356
 (.branch 354
 (.branch 353
 (.leaf 0xa1a85a027f9d2739ba6d82e0a81e0681203805ff7f9fc7edf9735cb721c670db66d1af6b5ac5a96859563581535454c529490028)
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
 (.leaf 0x255952529421f87a1c8688520c7e1f07b1e8771d8751c06e1a4671986518861180411003f0f83d0f0370d4300b82d0b0290a027020070180501003002f))
 (.branch 387
 (.leaf 0x2318c22e8b21986216850d3344cc328c9320c5310c32f8bc2dcb52d0b32c0af2b88f2388d2308b228360d0330c42d0b02a09825028090180500801002f)
 (.leaf 0xe4380300b0004)))
 (.branch 390
 (.branch 389
 (.leaf 0x9f27b9e6779aa6999e6593e4e9324a90e429023e8ae2a8a22684e128420e64d916318a625886158460d7e5f1775d5745cd705bd6e53d4e5354c52d4a515434f93c4ed3a4dd364d5164551444d124450c4290540d02404fe3f4fc374dc36cda364d82f4bb2e8b82d0b32c4ad2b0912408d230892206f1b46c1a8661946317c5e10c420fc3e0ec3a0300b01003008010072)
 (.leaf 0x1c87111444028090006))
 (.branch 391
 (.leaf 0x300bf24c92020070006)
 (.leaf 0x0))))
 (.branch 396
 (.branch 394
 (.branch 393
 (.leaf 0x23d8f23a8e22589222881a8699a167d9e6759a6659842d0942106409013fcfb3e8df378db368d7358d2340cf334c9320c6308c124c9222c8a22488002f)
 (.leaf 0x0))
 (.branch 395
 (.leaf 0x354d4244900004)
 (.leaf 0x0)))
 (.branch 398
 (.branch 397
 (.leaf 0x4390d384e023c8e0006)
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 408
 (.branch 404
 (.branch 402
 (.branch 401
 (.leaf 0xa3a8da2e89992639865f8de368d2327d9f47bded7b1eb7a1e7799e177dda761d7759d3749d16c9b16c1af6b9ad69da5691a26799d66d9765944509414fd3b4e9384d13346117451134410f384e0364d835cd60042)
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 406
 (.branch 405
 (.leaf 0x51d464691937cde0006)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 412
 (.branch 410
 (.branch 409
 (.leaf 0x6a9a9374dc0004)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 432
 (.branch 424
 (.branch 420
 (.branch 418
 (.branch 417
 (.leaf 0xa2287a16839da759ce719264891a4482e0981202806007f5fc7ede0779dd76dd7759d4741cf6d1b36c1af6b1ab5f57b5e9785d1735c56d5b1515414d5314952084208811fc7b1e8781d073114440f43c0ec3a0042)
 (.leaf 0x21c8610c420004))
 (.leaf 0x0))
 (.branch 422
 (.branch 421
 (.leaf 0x6017f54d52104400006)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 440
 (.branch 436
 (.branch 434
 (.branch 433
 (.leaf 0x78de26d9b50004)
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
 (.leaf 0x282a067f9f6709be6d9ae5e9765b9660a8220781601801fe7e9f97d5f37c9f07b1eb7a5e5791b66d5ae6b5ac6ad926418f63589621866098154d5252d4a5254846919449114410f0039)
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 454
 (.branch 453
 (.leaf 0x6559454550461170006)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 472
 (.branch 468
 (.branch 466
 (.branch 465
 (.leaf 0x7e1f76d1b3459150006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 496
 (.branch 488
 (.branch 484
 (.branch 482
 (.branch 481
 (.leaf 0x8360c6c9b153d4e0006)
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
 (.leaf 0x2588721a85a140e4380cc310c02e0b42c0a428098250841f0781b0641504c1203c0d001b)))
 (.branch 518
 (.branch 517
 (.leaf 0x0)
 (.leaf 0x94a509324a87e1e8420e1c8711b06a1a467198651886117c5e1685815c541484e1304b1204608c200741c06417050110400d0028))
 (.branch 519
 (.leaf 0x8ba2c8a2268661884e12300bf2e8b82dcb52d0b32c0af2b4ac2a0a6294a22809c2689925894090220741b068180581103c0e0028)
 (.leaf 0x0))))
 (.branch 524
 (.branch 522
 (.leaf 0x0)
 (.branch 523
 (.leaf 0x2588c63088a20354d433ccd330ca324c8314c4308c12a8a7290a32809e26c9825c94001b)
 (.leaf 0x0)))
 (.branch 526
 (.branch 525
 (.leaf 0x9023e8ea388ae2a896244390d4210641503409013f8fd3ecfa3d8f43ccf03b8ea3a0e7390e22aca9290a22849f27498258950028)
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 536
 (.branch 532
 (.leaf 0x0)
 (.branch 534
 (.branch 533
 (.leaf 0x99e659865f90e428d23251d465053f4f93c4ed3a4dd364d1334bd2d4b12949d23485204751b3e0f53c8f13b8ec3a4e6394e20028)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 540
 (.branch 538
 (.branch 537
 (.leaf 0x2588f63c8de366a9a9691a26859f6799d6699965d963e4f73c8f03bced3ace6390e3001b)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 560
 (.branch 552
 (.branch 548
 (.branch 546
 (.branch 545
 (.leaf 0x0)
 (.leaf 0x2589565491a4421c862047f1f87c1ec7a1dc761d0731705915855148501344a12446001b))
 (.leaf 0x0))
 (.branch 550
 (.branch 549
 (.leaf 0x9e6779ce7193e4e926486017f5e9785dd755d1735c16f5b56c5a166595625815c56959559541745b1585414c5113c4a120470028)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 568
 (.branch 564
 (.branch 562
 (.branch 561
 (.leaf 0x28ba2685a0e5878de2775db769d875dd674dd2741cf72dc9721c570dbf6f5bc6e5b7001b)
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
 (.leaf 0x9f27b9b66b9aa6996e596559463d8d6318a6258861584609815a967591635815e56d5855d544c52e4ad2a49d254891f4791b0028)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 600
 (.branch 596
 (.branch 594
 (.branch 593
 (.leaf 0xa3a8d9fe7d9926397a5d7e1f77c9f07bded7b1eb7a1e7795e4735ca71dc670dc16f9bb6e9b74c9304ad294a1264911f4751c0028)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 624
 (.branch 616
 (.branch 612
 (.branch 610
 (.branch 609
 (.leaf 0xa2287a0a819da759c26f8360c81e0581202806007f5fc7e9f9739cc71dc5711c2701bb6e5b85ad69591625855f57558559550028)
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
 (.leaf 0x25494e529461e8761c86c872087e1f47b1e4781d8741c86d1a4681986418c6117c4d1304b12849120390d0300bc2d0ac2a0a02605013048110400f002f))
 (.branch 643
 (.leaf 0x2308be2e8b61885e16854d5340cc32cc931cc6310c2300bb2dcb62d0b22c4af2b49b2689926097258380d4330c82d0ac2909c2505815048110380d002f)
 (.leaf 0xdc36060170004)))
 (.branch 646
 (.branch 645
 (.leaf 0x9ee7a9e6789a66899e6693a4d9324b90a419023f8aa298a22784a118420f655906318b6258761984609805ed775d9745c9715bd6d56d5a5655855d5651d424f93d4ed394e1364d1224852047d1e4750e4250541102400ff3f4fb3a4e839ce6394e42fcbc2e8b92d0b22c0ae2b09d2709926095250711b86c1ac66190621805e13c4e12c4a11c46060170400f0380d0072)
 (.leaf 0x1c06f14450058150006))
 (.branch 647
 (.leaf 0x2f8bd27c9e050130006)
 (.leaf 0x0))))
 (.branch 652
 (.branch 650
 (.branch 649
 (.leaf 0x23c8ee3a8e62488e22885aa695a16819e6719b665974350a42107409003f8fc3e8eb3a8e7398e3388d4344cf338c931cc530cc127c9e25c9625494002f)
 (.leaf 0x0))
 (.branch 651
 (.leaf 0x34cd22749c0004)
 (.leaf 0x0)))
 (.branch 654
 (.branch 653
 (.leaf 0x4310b3b4ec26c9a0006)
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 664
 (.branch 660
 (.branch 658
 (.branch 657
 (.leaf 0xa368ca2e8a98e62986608da358d2337e1f37bdee7b1ea7a5e7795e3779da765d7755d4749d06f9bd6f1bb6e9b96a5a6691a36799c669986594650d415013b4e5374d533491234811f4711b3b4ec394e438ce20042)
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 662
 (.branch 661
 (.leaf 0x51544499253acea0006)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 668
 (.branch 666
 (.branch 665
 (.leaf 0x6a1a73a4e80004)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 688
 (.branch 680
 (.branch 676
 (.branch 674
 (.branch 673
 (.leaf 0xa1e86a16849d6749ce729224791a458360881203805ff7f9fc7e9e277ddd771d7755d3745cf701bf6f1bb6e1b75fd7c5e9795d1725c16e5b15d57159561555508620c812007b1e4771d473144501244811c460042)
 (.leaf 0x2148413c4e0004))
 (.leaf 0x0))
 (.branch 678
 (.branch 677
 (.leaf 0x5f97d57d5e1344c0006)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 696
 (.branch 692
 (.branch 690
 (.branch 689
 (.leaf 0x785e0709c10004)
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
 (.leaf 0x281a027f9fa6f9ba6d9b25d9725b96a0c8260781a017fdfd7edf97ddf47c9f17b1ea7a1e6791c2705ba6e5b86dd946458f6398961d8560d8157d5e55d5655554499254791d4711b0039)
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 710
 (.branch 709
 (.leaf 0x64d925755c491230006)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 728
 (.branch 724
 (.branch 722
 (.branch 721
 (.leaf 0x7d9f5701bf489210006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 752
 (.branch 744
 (.branch 740
 (.branch 738
 (.branch 737
 (.leaf 0x82e0a6f9bd56d5a0006)
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
 (.leaf 0x25594e519421f8761b868862107d1f07a1e4781dc731c46f1a0671946418c62178591605715855150380d82f0b82c0ac2a0a4250801f0781d0701b002f))
 (.branch 771
 (.leaf 0x2318be2d8b21985e15850d4348cb328c831cc6314c12fcbd2d8b52ccb22c4b02b0a7298a5290a3288390dc320c42c0ac2809c26088210781d06819002f)
 (.leaf 0xd434090230004)))
 (.branch 774
 (.branch 773
 (.leaf 0x9f27a9e2779aa6899a6593e4d92e4a90e418fe3e8ae2989e2684e1183e0e6519262d8a62187619856057f5f5765d5735c9715c16c59d665956458d62519444f53c4e9394e1374cd2e4b52c4ad2a4a50d42d0440d01400ff3f8fa3d4f43ccf23c4f0300be2e4b82ccb22bcae2b4a92a0a5290a1280721c06b1a865190611805f16c5a15c5614c52090230701b068190072)
 (.leaf 0x1b86d1745c088210006))
 (.branch 775
 (.leaf 0x2f0bb2acaa0801f0006)
 (.leaf 0x0))))
 (.branch 780
 (.branch 778
 (.branch 777
 (.leaf 0x23d8ee398e22588e21881a969da067d9d6719b669964390c41d06405003f4fc3ecf73d8f33c8ef3b8d534cce334c831cc430cc22acaa28ca2284a0002f)
 (.leaf 0x0))
 (.branch 779
 (.leaf 0x344d02a4a80004)
 (.leaf 0x0)))
 (.branch 782
 (.branch 781
 (.leaf 0x429093e4f829ca60006)
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 792
 (.branch 788
 (.branch 786
 (.branch 785
 (.leaf 0xa3a8ca2a89992629825f8de358ce327ddf57b9ed7adea7a5e8791e2781d9761d6755d474dcf729c9721c7719c56a9a868da26759c6659865d47515404fd3a4e5364d5344c12f4b12b4a1273e4f83c4f03bcee0042)
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 790
 (.branch 789
 (.leaf 0x50d424c9313dcf60006)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 796
 (.branch 794
 (.branch 793
 (.leaf 0x699a53d4f40004)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 816
 (.branch 808
 (.branch 804
 (.branch 802
 (.branch 801
 (.leaf 0xa2286a12839da749ca7192647916448320a80e02801ff7f9fd7e5e3785dc76dd6755d2745d0731cb721c7711c36017e5e5785cd725bd6e5b5695a1655916158087214801fc7a1e4761d4741745c1545414c520042)
 (.leaf 0x20c8216c5a0004))
 (.leaf 0x0))
 (.branch 806
 (.branch 805
 (.leaf 0x5f17b5ad6a164580006)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 824
 (.branch 820
 (.branch 818
 (.branch 817
 (.leaf 0x77dde739cd0004)
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
 (.leaf 0x282a027e9f6709ba6c9ae5e9725a9660d82e06816007fdfc7edfa7e1f67c5f07adea79de6795ce735c6715c470d9564d8e6358861d8460d825ad6a58d62585604c9314a9294a1270039)
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 838
 (.branch 837
 (.leaf 0x645905a5684c12f0006)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 856
 (.branch 852
 (.branch 850
 (.branch 849
 (.leaf 0x7d1f3731cb4b92d0006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 880
 (.branch 872
 (.branch 868
 (.branch 866
 (.branch 865
 (.leaf 0x82608729c959d660006)
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
 (.leaf 0x8360c82e0a826087f9fd7f1fb7e9f97e1f77d9f57d1f37a5e879de6795e478de2785e077dde751d3749d1741cf6a9a96a1a7699a566d9a6659865d966559464d92645906198561183609816017f5f97d5f17b5c5705bd6e5b56c51d465154450d424e1374d9354d1334390d4310b429093fcfe3f4fc3ecfa354d434cd2344d0318c5310c3308c1300bf2f8bd2f0bb2c4b02bcae2b4ac21c862148420c821e0771d8751d0731c8711c06f1b86d18c621846017c5e0e4380dc360d4340a8290a02709825009c)
 (.leaf 0x812007f1b06b1a8330c8310009))
 (.branch 899
 (.leaf 0xcf338cd2e8b92e0300bc2e0009)
 (.leaf 0x84e128461083e0e0006)))
 (.branch 902
 (.branch 901
 (.leaf 0x63d8e6357a5e578505404fd0841d062dcb62d4691a0670012)
 (.leaf 0x9264891e46916448661885e1685614000c))
 (.branch 903
 (.leaf 0x8962488e228862087e1e8761c86e1a000c)
 (.leaf 0x0))))
 (.branch 908
 (.branch 906
 (.branch 905
 (.leaf 0x1a468da24150440ccc32cca0009)
 (.leaf 0x0))
 (.branch 907
 (.leaf 0x8ae2a8a62889e260006)
 (.leaf 0x0)))
 (.branch 910
 (.branch 909
 (.leaf 0x8de368d6348ce328c6308be2e8b62c000c)
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 920
 (.branch 916
 (.branch 914
 (.branch 913
 (.leaf 0x7c9f17c1dd771db685a067d3e4f53c000c)
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 918
 (.branch 917
 (.leaf 0x97a5d9725b96a598f63c8ee3a8e638000c)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 924
 (.branch 922
 (.branch 921
 (.leaf 0x90e42906408fe3e0006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 944
 (.branch 936
 (.branch 932
 (.branch 930
 (.branch 929
 (.leaf 0x81e06815da765d85dd765d47e1f47c000c)
 (.leaf 0x93e4e9364c92e4a0006))
 (.leaf 0x0))
 (.branch 934
 (.branch 933
 (.leaf 0x9c26f9ba6d9b26b9565494e5294650000c)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 952
 (.branch 948
 (.branch 946
 (.branch 945
 (.leaf 0xa0a81a027f9fa7d0006)
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
 (.leaf 0x20480e027bdee7b58c62d8a0009)
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 966
 (.branch 965
 (.leaf 0x9da759d2739ca719926398a619825f000c)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 984
 (.branch 980
 (.branch 978
 (.branch 977
 (.leaf 0xa2287a1a85a12839aa699a26799a65000c)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 1008
 (.branch 1000
 (.branch 996
 (.branch 994
 (.branch 993
 (.leaf 0xa3a8da328ba2a899f27b9ea799e277000c)
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
 (.leaf 0x201801ff7f9fd7f1fb7e9f97b1eb7a9e97a1e7799e5791d7759d5751d3749d1741cf721c7719c5711c36f1bb6e9b96e1b76c1af6b9ad6b1ab6799d6719b669996619765989621876198561183609815d1735c9715c16f5b96d5b16559163589615815956157559555514d5314b529495213b4e9394e1374d9354d1334b12b4a9294a1274811f4791d4711b45113449114410f40901400ff3f8fd3f0fb3e8f33c8f13c0ef3b8e7398e5390e3388db368d9360d7358c9320c7318c5310c3308c12d0b32c8b12c0af2b8ad2b0a5290a3288a12809926097258952508d2308b228892207b1e8791e0771d8751d0731986519063188611805f1785715855150531484b12849120471183f0f83d0f03b0e82d0b02b0a8290a027098250781d0701b06819048110400f0380d01805010030080100f3)
 (.branch 4
 (.leaf 0x8360c82e0a8260881e068160480e027e1f77d9f57d1f37c9f17c1ef7b9ed78de2785e077dde775dc76dda765d8739cd731cb729c9709c1701bf6f9bd6d9b56d1b36c9b16a9a96a1a7699a5691a3689a16819f6559464d926459063d8e6358c62d8a6017f5f97d5f17b5e9795e1775d9755ad6a5a56859d6657d5e5755c56d5a54d525455053d4e51d465154450d42505404fd3e4f53c4c9314c12f4b92d4992549123489214691946117459154390d4310b429094210741905411033e4f83dcf63d4f43b4ec3acea3a4e8384e037cde374dc354d434cd2344d033cce334cc32cca300bf2f8bd2f0bb2e8b92e0b72d8b52acaa2a4a829ca627c9e2749c26c9a24c922449023c8e21c862148420c82204801fc7e1f47c1c8711c06f1b86d1b06b1a8691a0671745c16c5a164581445013c4e1344c1144410c42104400e4380dc360d4340cc320c4300bc2e09023088210801f0601705815050130300b0280902007011a)
 (.leaf 0x28ea368ca2e8aa2688a1e86a1684a0e82a06809fe7e9f67c9ee7a9e6789de769d6749ce729c6709be6e9b66c9ae6a9a66899e669966498e629866097e5e9765c96e5a9665895e569565494e529465093e4e9364c92e4a9264891e469164490e42906408fe3e8f63c8ee3a8e6388de368d6348ce328c6308be2e8b62c8ae2a8a62889e268962488e228862087e1e8761c86e1a8661885e168561484e128461083e0e0081))))
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
 (.leaf 0x3fe001ff000ff81f81f81f8007fc003fe001ff03f03f03f000ff81f81f81f8007fc0fc0fc0fc003fe001ff03f03f03f000ff8007fc0fc0fc0fc003fe07e07e07e)
 (.branch 4
 (.leaf 0x3ffc01ffe00fff007e07e07e07ff803ffc01ffe00fc0fc0fc0fff007e07e07e07ff803f03f03f03ffc01ffe00fc0fc0fc0fff007ff803f03f03f03ffc01f81f81f80)
 (.leaf 0x7fffffffffffffffffffffffffffffffc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))))
def kindMasks := kindMaskTable.get
def keys := List.range 5
def vertexMaskTable : Table Nat :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf 8299027180475562404938147655969775508133865379938285369551046526707336454386785294890366468044966623777728799881160567079789255156085931897450120080132251077185292786765978994212863)
 (.leaf 7261652245556833527095780253343374053084854561162361655291113466742542659400471130018361993683907421911389014731441114351628213418901836219284350858290010733888023097227580633251839))
 (.branch 3
 (.leaf 570305077195512750084604713035139482176668907212287330995149229557834208216188623869643149514468251892050945432872027760662631678427737200429630707507407490387638785961976297452629886272274431)
 (.branch 4
 (.leaf 7261656202828161189483162159346954628651928570145282747433262338812666887790554670336295764919481204409951359136219732076839644717338402160943502656842335356301412288443792488398849)
 (.leaf 149501483855342430331234124116448467236881448382827726876090049102614414266943332249006930173438087209449137656087297562051827501998582423680834083764263580775542847829001424449768259234225379606529))))
 (.branch 7
 (.branch 6
 (.leaf 149502054156068560004883613614916940192552832990340516071040646093410595897214482718523334053511376907257041677002001587485104188074353556089333097248184320886286028298751744565042901213482487644161)
 (.leaf 149502054158244084625402773413601229109505257868322639343252948762661923028219245512736836135400699891301387761033613960648165152281754422464308502480098742941563916528023196055816209015869817225217))
 (.branch 8
 (.leaf 149502054158244086700160557854097708365489516188779085286525820826260174603873550217100085285832651220038240377603166885582408593703973577752085790583185795005648770447850238831105042061417663954942)
 (.branch 9
 (.leaf 149502054158244087737539450074345947993591482111569373039661184310187136203057011301223421684185672336123201994401175464832317188510788290104049007660127879477066207435881322249131961548602968383486)
 (.leaf 149502054158244089812297234514842427249795413957149948545884306243276513382672851226789441681056036059540241653348585807175205913336471362116261551090679595495088511877740983202001362143067888410624)))))
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
 (.leaf (.leaf 0))
 (.branch 22
 (.branch 21
 (.leaf (.leaf 7))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 28
 (.branch 26
 (.branch 25
 (.leaf (.leaf 8))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 30
 (.branch 29
 (.leaf (.leaf 9))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))))
 (.branch 48
 (.branch 40
 (.branch 36
 (.branch 34
 (.branch 33
 (.leaf (.leaf 0))
 (.leaf (.leaf 10)))
 (.leaf (.leaf 0)))
 (.branch 38
 (.branch 37
 (.leaf (.leaf 11))
 (.leaf (.leaf 12)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
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
 (.leaf (.leaf 0))
 (.branch 59
 (.leaf (.leaf 0))
 (.leaf (.leaf 14))))
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
 (.branch 102
 (.branch 101
 (.leaf (.leaf 19))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
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
 (.leaf (.leaf 0)))
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
 (.leaf (.leaf 34)))
 (.leaf (.leaf 0)))
 (.branch 166
 (.branch 165
 (.leaf (.leaf 35))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
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
 (.leaf (.leaf 0)))
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
 (.leaf (.leaf 54)))
 (.leaf (.leaf 0)))
 (.branch 294
 (.branch 293
 (.leaf (.leaf 55))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
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
 (.leaf (.leaf 0)))
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
 (.leaf (.branch 0x1000000000000000000000001000000000000000000000000000000000000000200000000000000000000000200000000 (.leaf 82) (.leaf 83))))
 (.leaf (.leaf 0)))
 (.branch 422
 (.branch 421
 (.leaf (.branch 0x1000000000000000000000001000000000000000000000000000000000000001000000000000000000000001000000000 (.leaf 84) (.leaf 85)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
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
 (.leaf (.leaf 0)))
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
 (.leaf (.leaf 108)))
 (.leaf (.leaf 0)))
 (.branch 550
 (.branch 549
 (.leaf (.leaf 109))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
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
 (.leaf (.leaf 0)))
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
 (.leaf (.branch 0x10000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000200000000 (.leaf 136) (.leaf 137))))
 (.leaf (.leaf 0)))
 (.branch 678
 (.branch 677
 (.leaf (.branch 0x10000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000001000000000 (.leaf 138) (.leaf 139)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
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
 (.leaf (.leaf 0)))
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
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000200000000 (.leaf 170) (.leaf 171))))
 (.leaf (.leaf 0)))
 (.branch 806
 (.branch 805
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000001000000000 (.leaf 172) (.leaf 173)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
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
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000008 (.branch 0x10000000000000000000000000000000400000000000000000000000000000001000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000008 (.leaf 190) (.branch 0x1000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000008 (.leaf 191) (.leaf 192))) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000400000000000000000000000000000008 (.leaf 193) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000200000000000000000000000000000008 (.leaf 194) (.leaf 195)))))))
 (.branch 902
 (.branch 901
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000 (.leaf 196) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000000 (.leaf 197) (.leaf 198))))
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000020 (.branch 0x10000000000000000000000000000001000000000000000000000000000000001000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000020 (.leaf 199) (.branch 0x1000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000020 (.leaf 200) (.leaf 201))) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000001000000000000000000000000000000020 (.leaf 202) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000200000000000000000000000000000020 (.leaf 203) (.leaf 204))))))
 (.branch 903
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000040 (.branch 0x10000000000000000000000000000001000000000000000000000000000000001000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000040 (.leaf 205) (.branch 0x1000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000040 (.leaf 206) (.leaf 207))) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000001000000000000000000000000000000040 (.leaf 208) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000400000000000000000000000000000040 (.leaf 209) (.leaf 210)))))
 (.leaf (.leaf 0)))))
 (.branch 908
 (.branch 906
 (.branch 905
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000 (.leaf 211) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000000000000000000 (.leaf 212) (.leaf 213))))
 (.leaf (.leaf 0)))
 (.branch 907
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000400 (.branch 0x10000000000000000000000000000010000000000000000000000000000000001000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000400 (.leaf 214) (.branch 0x1000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000400 (.leaf 215) (.leaf 216))) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000010000000000000000000000000000000400 (.leaf 217) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000400000000000000000000000000000400 (.leaf 218) (.leaf 219)))))
 (.leaf (.leaf 0))))
 (.branch 910
 (.branch 909
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000001000 (.branch 0x10000000000000000000000000000010000000000000000000000000000000001000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000001000 (.leaf 220) (.branch 0x1000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000001000 (.leaf 221) (.leaf 222))) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000010000000000000000000000000000001000 (.leaf 223) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000001000000000000000000000000000001000 (.leaf 224) (.leaf 225)))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 920
 (.branch 916
 (.branch 914
 (.branch 913
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000 (.leaf 226) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000000000 (.leaf 227) (.leaf 228))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 918
 (.branch 917
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000100000 (.branch 0x10000000000000000000000000001000000000000000000000000000000000001000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000100000 (.leaf 229) (.branch 0x1000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000100000 (.leaf 230) (.leaf 231))) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000001000000000000000000000000000000100000 (.leaf 232) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000001000000000000000000000000000100000 (.leaf 233) (.leaf 234)))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 924
 (.branch 922
 (.branch 921
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000010000000000000000000000000001000000 (.branch 0x10000000000000000000000000001000000000000000000000000000000000001000000000000000000000000000001000000000000000000000000000000000000000000000000000000000001000000 (.leaf 235) (.branch 0x1000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000001000000000000000000000000000001000000 (.leaf 236) (.leaf 237))) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000001000000000000000000000000000001000000 (.leaf 238) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000010000000000000000000000000001000000 (.leaf 239) (.leaf 240)))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 944
 (.branch 936
 (.branch 932
 (.branch 930
 (.branch 929
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000 (.leaf 241) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000000000000000000000000 (.leaf 242) (.leaf 243))))
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000200000000000000000000000200000000 (.branch 0x10000000000000000000000010000000000000000000000000000000000000001000000000000000000000000000000020000000000000000000000000000000000000000000000000000000200000000 (.leaf 244) (.branch 0x1000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000001000000000000000000000000000000000000000000000000000000010000000000000000000000000000000200000000 (.leaf 245) (.leaf 246))) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000010000000000000000000000000000000200000000 (.leaf 247) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000200000000000000000000000200000000 (.leaf 248) (.leaf 249))))))
 (.leaf (.leaf 0)))
 (.branch 934
 (.branch 933
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000001000000000000000000000001000000000 (.branch 0x10000000000000000000000010000000000000000000000000000000000000001000000000000000000000000000000100000000000000000000000000000000000000000000000000000001000000000 (.leaf 250) (.branch 0x1000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000001000000000000000000000000000000000000000000000000000000010000000000000000000000000000001000000000 (.leaf 251) (.leaf 252))) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000010000000000000000000000000000001000000000 (.leaf 253) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000001000000000000000000000001000000000 (.leaf 254) (.leaf 255)))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
 (.branch 952
 (.branch 948
 (.branch 946
 (.branch 945
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000001000000000000000000000001000000000000 (.branch 0x10000000000000000000000010000000000000000000000000000000000000001000000000000000000000000000100000000000000000000000000000000000000000000000000000001000000000000 (.leaf 256) (.branch 0x1000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000010000000000000000000000000001000000000000 (.leaf 257) (.leaf 258))) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000010000000000000000000000000001000000000000 (.leaf 259) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000001000000000000000000000001000000000000 (.leaf 260) (.leaf 261)))))
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
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000 (.leaf 262) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000000000000000000000 (.leaf 263) (.leaf 264))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 966
 (.branch 965
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000001000000000000000100000000000000000 (.branch 0x10000000000000001000000000000000000000000000000000000000000000001000000000000000000000000000000100000000000000000000000000000000000000000000000100000000000000000 (.leaf 265) (.branch 0x1000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000001000000000000000000000000000000000000000000000001000000000000000000000000000000100000000000000000 (.leaf 266) (.leaf 267))) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000001000000000000000000000000000000100000000000000000 (.leaf 268) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000001000000000000000100000000000000000 (.leaf 269) (.leaf 270)))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
 (.branch 984
 (.branch 980
 (.branch 978
 (.branch 977
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000001000000000000000100000000000000000000 (.branch 0x10000000000000001000000000000000000000000000000000000000000000001000000000000000000000000000100000000000000000000000000000000000000000000000100000000000000000000 (.leaf 271) (.branch 0x1000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000001000000000000000000000000000000000000000000000001000000000000000000000000000100000000000000000000 (.leaf 272) (.leaf 273))) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000001000000000000000000000000000100000000000000000000 (.leaf 274) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000001000000000000000100000000000000000000 (.leaf 275) (.leaf 276)))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 1008
 (.branch 1000
 (.branch 996
 (.branch 994
 (.branch 993
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000010000000000000001000000000000000000000000 (.branch 0x10000000000000001000000000000000000000000000000000000000000000001000000000000000000000001000000000000000000000000000000000000000000000001000000000000000000000000 (.leaf 277) (.branch 0x1000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000001000000000000000000000000000000000000000000000001000000000000000000000001000000000000000000000000 (.leaf 278) (.leaf 279))) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000001000000000000000000000001000000000000000000000000 (.leaf 280) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000010000000000000001000000000000000000000000 (.leaf 281) (.leaf 282)))))
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
def candidateMasks (i : Nat) := PackedRawNatGrowth.take 655
  (PackedRawNatGrowth.drop (655*(i%64)) (candidateMasksBlocks.get (i/64)))

def badMasksBlocks : Table Nat :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf badMasksBlock0000)
 (.leaf badMasksBlock0001))
 (.branch 3
 (.leaf badMasksBlock0002)
 (.branch 4
 (.leaf badMasksBlock0003)
 (.leaf badMasksBlock0004))))
 (.branch 8
 (.branch 6
 (.leaf badMasksBlock0005)
 (.branch 7
 (.leaf badMasksBlock0006)
 (.leaf badMasksBlock0007)))
 (.branch 9
 (.leaf badMasksBlock0008)
 (.branch 10
 (.leaf badMasksBlock0009)
 (.leaf badMasksBlock0010)))))
def badMasks (i : Nat) := PackedRawNatGrowth.take 655
  (PackedRawNatGrowth.drop (655*(i%64)) (badMasksBlocks.get (i/64)))

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
def signatureMasks (i : Nat) := PackedRawNatGrowth.take 655
  (PackedRawNatGrowth.drop (655*(i%64)) (signatureMasksBlocks.get (i/64)))

def fastKind := rawKind
def candidateSupports := candidateRows
def kindSupports := kindRows
def wellFormedTest (i : Nat) : Bool := RawFacetEmbedding.wellFormedCheck (rawCells i)

def cellTest (i : Nat) := (listBounds 1024 (rawCells i).ridgeMasks && ((rawCells i).ridgeMasks.all (fun q => (candidateMasks q).testBit i) && (decide (rawKind i = (rawCells i).kind) && (decide ((rawCells i).vertices < 1024) && ((List.range 10).all (fun v => decide ((vertexMasks v).testBit i = (rawCells i).vertices.testBit v)) && (SignatureCompatibility.faces (rawCells i)).all (fun q => (SignatureCompatibility.profileMask (SignatureCompatibility.allMask 655) signatureIndex signatureMasks (rawCells i) q).testBit i))))))
def ridgeTest (i : Nat) := decide (candidateMasks i = RawNatGrowthCheck.mask (candidateRows i)) &&
  (candidateRows i).all (fun c => hasNat (rawCells c).ridgeMasks i)
def kindTest (i : Nat) := decide (kindMasks i = RawNatGrowthCheck.mask (kindRows i)) &&
  (kindRows i).all (fun c => decide ((rawCells c).kind = i))
def badTest (i : Nat) := if badMasks i = 0 then true else
  decide (Nat.land (badMasks i) (SignatureCompatibility.cover (SignatureCompatibility.allMask 655)
    vertexMasks signatureIndex signatureMasks (rawCells i)) = 0)

end Papers.RationalityTen.RootedCaches.RootedSevenMixed030

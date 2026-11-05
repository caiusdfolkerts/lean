module
prelude
public import RootedSevenPure009
public import SignatureCompatibility
public import PackedRawNatGrowth
public import FiniteChecks
public import RawFacetEmbedding
public import RootedSevenPure009GrowthCachecandidateMasksData000
public import RootedSevenPure009GrowthCachebadMasksData000
public import RootedSevenPure009GrowthCachesignatureMasksData000

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure009
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def rawCells := Papers.RationalityTen.FacetUniverses.RootedSevenPure009.rawCells
def cells (c : Fin 758) := rawCells c.val
def ridgeList := ConcreteGrowth.ridgeList cells
def literalCompatible (a b : Fin 758) := ConcreteGrowth.compatible (cells a) (cells b)
def kind (c : Fin 758) := (cells c).kind
def rawKindCode : Nat := 1493596731634803415675505274503925572118111935029548566838117801138183309059188696363024898544517790297189738648098443583470579265506708013638219492964538092110415853224151501487235162628189216047459443888569531173802132733398117629138043364626969968021874998722904801348813879134562548879316210503596463682460213006757367133583884204249240734572627862426723071206173738152977035376796592989045633093590561053668606028079466805209097304354508251100765173467262542417605113353465395876595614710001766555709141115853679832073454825161817696665443543194944269033093437431258301391338121960784378327808832048296014862558511967618154545399138666900475147419457910842512905255996456788333128
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
 (.leaf 0x1d8751d0731c8711c06f1b86d1b06b1a8691a0671986519063188611805f1785d1705b1685916057158551505300c02004000028))))
 (.branch 12
 (.branch 10
 (.leaf 0x0)
 (.branch 11
 (.leaf 0x0)
 (.leaf 0x26899260972589525093248912408f2388d2308b22889220872188521083208812007f1f87d1f07b1e8791e07701805010000028)))
 (.branch 14
 (.branch 13
 (.leaf 0x0)
 (.leaf 0x34cd2344d033cce334cc32cca324c831cc6314c430cc2304c02fcbe2f4bc2ecba2e4b82dcb62d4b42ccb22c4b00300b028000028))
 (.leaf 0x0))))
 (.branch 24
 (.branch 20
 (.leaf 0x0)
 (.branch 22
 (.leaf 0x0)
 (.branch 23
 (.leaf 0x4852047d1e4751c46d1a4651845d164551444d124451043d0e4350c42d0a4250841d064150440d02405003fcfe05815050000028)
 (.leaf 0x0))))
 (.leaf 0x0)))
 (.branch 48
 (.branch 40
 (.leaf 0x0)
 (.branch 44
 (.branch 42
 (.leaf 0x0)
 (.branch 43
 (.leaf 0x56959561575595555153549515414f5394d5314b52949521475194551143509415013f4f93d4f13b4e9394e1370701b068000028)
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 56
 (.branch 52
 (.branch 50
 (.leaf 0x0)
 (.branch 51
 (.leaf 0x64d926459063d8e6358c62d8a6258861d866158460d82605805fd7e5f57c5ed7a5e5785dd765d5745cd725c57008821080000028)
 (.leaf 0x0)))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 96
 (.branch 80
 (.branch 72
 (.leaf 0x0)
 (.branch 76
 (.leaf 0x0)
 (.branch 78
 (.branch 77
 (.leaf 0x785e077dde775dc76dda765d875dd6755d474dd2745d073dce735cc72dca725c871dc6715c470dc2705c06fdbe0b02b0a8000028)
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 88
 (.branch 84
 (.leaf 0x0)
 (.branch 86
 (.branch 85
 (.leaf 0x86a198621785a158521384a118420f83a0d8320b82a098220781a058120380a01801ff7f9fd7f1fb7e9f97e1f70c8310c0000028)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 112
 (.branch 104
 (.leaf 0x0)
 (.branch 108
 (.branch 106
 (.branch 105
 (.leaf 0x9a26799a659926398a619825f97a5d9725b96a599625795a559525394a519424f93a4d9324b92a499224791a450f03b0e8000028)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 120
 (.branch 116
 (.branch 114
 (.branch 113
 (.leaf 0xadab5ad2b3acab1ac2afabaadab2abaaaa9aa2a7a9aa5a92a3a8aa1a829fa7a9da729ba6a99a6297a5a95a529311845110000028)
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
 (.leaf 0x2acaa2a0a7294a4288a12809f2749c2308a21c86210801f87b1e8781a06618c621805c168571585402007010010024)))
 (.branch 134
 (.branch 133
 (.leaf 0x0)
 (.leaf 0x390e3384e0378dd36cda364d8358d5314c3300bf2f4b92dcb42ccb11a865190611805e16458154540380d028010024))
 (.branch 135
 (.leaf 0x4c9314bd2e4b12b4a52849d264912344d114390d42d0741502404ff1a4671906217c5d16c581585306017050010024)
 (.leaf 0x0))))
 (.branch 140
 (.branch 138
 (.branch 137
 (.leaf 0x0)
 (.leaf 0x3e4f83d8f53ccf23c0ef3b8ed3acea31cc2304be2f4bb2d8b52c8b12388922085210821f47c1e47804410028040024))
 (.branch 139
 (.leaf 0x5ad6a5a16759564589615815f5755c5314a51d46511404f93b4e9382348b2208620c811fc7c1e8770781d068040024)
 (.leaf 0x0)))
 (.branch 142
 (.branch 141
 (.leaf 0x7c9f17bdee7b1eb7a5e879de6791e374dd1739cd72dc7715c2705bf318c4304bf2f0ba2e0b52ccb00b82d0a80a0024)
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 152
 (.branch 148
 (.branch 146
 (.leaf 0x0)
 (.branch 147
 (.leaf 0x691a3685a06799d66d9a6659865995615836017f5f5795dd745cd714551043d0c42d0941103400ff09023080140024)
 (.leaf 0x0)))
 (.branch 150
 (.branch 149
 (.leaf 0x8ae2a8a2278962488a218821f8761c8320a81e06812007f9fb7e9f84511243d0d4290841903404fe0d0330c0140024)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 176
 (.branch 168
 (.branch 164
 (.branch 162
 (.leaf 0x0)
 (.branch 163
 (.leaf 0x6e5b86d9b56cdb26c1af6b9ad6adaa61d826057e5f57b5d9755c9715394952145511424f53c4e53809c260801a0024)
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 172
 (.branch 170
 (.branch 169
 (.leaf 0x9e6789da759ce729c26f9ba6d9ae6a96a589565494a4e93249922465354b5214650d414fd3c4e9370f83d0e81a0024)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 184
 (.branch 180
 (.branch 178
 (.branch 177
 (.leaf 0xb1ec6b12c3b06c0afabdaf2bbae6b8aa2a6a8ea2a829ca6a97a5a94619846057f5f17a5e1755cd7012047110200024)
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
 (.leaf 0x9023f8f63c8ea398de368d6348ca3183a0982205812027f5fc7e5f8755d073dcc72dc9711c3701bf0dc360c02a0024)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 204
 (.branch 202
 (.branch 201
 (.leaf 0xa3a8da2e8aa2287a1684a0e82a027f9725795a5394a5092e4a91e46751d273dcd729c8719c3705be104400e82a0024)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 216
 (.branch 212
 (.branch 210
 (.branch 209
 (.leaf 0xb72dbb66d8b5ad5b4ed2b46d0b3acdaaaa5a92a1a829ea6698a56948360b8220680e017fdfc7e9f712c4a110300024)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 240
 (.branch 232
 (.branch 228
 (.branch 226
 (.branch 225
 (.leaf 0xbc6f0bbaedbaeeaba2e7b9ae5b8ee2aa6a7a92a2a7e9da6e98a5a9396e5995a549464f9364a9224513c4e1103a0024)
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
 (.leaf 0x2b4ac2a4a8298a528ca12809e2749b2609624c922407f1f47c1e4771d0721bc6e1b05b164581545302407014020024)))
 (.branch 262
 (.branch 261
 (.leaf 0x0)
 (.leaf 0x398e5388e137cde370da364d7358d4344cf330cb324b82d8b52c8b01d8711c06d1b05d168571585303c0d02c020024))
 (.branch 263
 (.leaf 0x4d1334c12f4b52c4a92849d254912247d1d4691945d0641103400fe1d4731c06e1ac5e170571545406417054020024)
 (.leaf 0x0))))
 (.branch 268
 (.branch 266
 (.branch 265
 (.leaf 0x0)
 (.leaf 0x3ecfa3dcf63d0f33c4ef3b8ec3ace934cce334ca324ba2dcb42ccb02689525091240811f87b1e8770481002c050024))
 (.branch 267
 (.leaf 0x5b56c5a5685996558d615815e5755b5615654d525413f4f53c4e537264972509223c822007b1e47807c1d06c050024)
 (.leaf 0x0)))
 (.branch 270
 (.branch 269
 (.leaf 0x7d1f37c1ef7b5ec7a9e879de5791e277ddd769d975dc6711c3701be348d0334cb320bb2e4b42c8b10bc2d0ac0b0024)
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 280
 (.branch 276
 (.branch 274
 (.leaf 0x0)
 (.branch 275
 (.leaf 0x699a5689a167d9e6719a66597659946458f6318b625785d9755c9704851c46d1845d0841502404fe09423084150024)
 (.leaf 0x0)))
 (.branch 278
 (.branch 277
 (.leaf 0x8b62c8a62889a2588e218821e8761b8621684e12841ff7f5fc7e5f74811e46d194590941d02400ff0d4330c4150024)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 304
 (.branch 296
 (.branch 292
 (.branch 290
 (.leaf 0x0)
 (.branch 291
 (.leaf 0x6edba6ddb66d1b36c5af6b9ac6ada964d8e6358a6257a5dd745cd705695555151541414f93b4e9370a0260841b0024)
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 300
 (.branch 298
 (.branch 297
 (.leaf 0x9ee7a9de769d2739c66f9ba6c9ae6999a649866097a4d92e4a91e45565575515253d425013b4e5380fc3d0ec1b0024)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 312
 (.branch 308
 (.branch 306
 (.branch 305
 (.leaf 0xb26c8b16c4b0ac1afebdaf2baae6b7ad2b2abeaeab29ba6698a5693649906358b6217b5e5745c97112447114210024)
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
 (.leaf 0x90a418fa3d8ee3a8e2368d6338ca3086a1585211842017f9fb7e9f7785dc76dd875dc8715c2705be0e0360c42b0024)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 332
 (.branch 330
 (.branch 329
 (.leaf 0xa428fa328ba2688a1a84a0e81a027e9a26398a5f97a4f9324992245781de76dd9759c971dc2701bf108400ec2b0024)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 344
 (.branch 340
 (.branch 338
 (.branch 337
 (.leaf 0xb7addb6ad9b5ed6b52d2b46cfb3accadab1ac2adab29da6a97a5a93866178521283e02801fb7e5f81304a114310024)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 368
 (.branch 360
 (.branch 356
 (.branch 354
 (.branch 353
 (.leaf 0xbcef2bbeeebb2ebba6e7b9ae4b8ee1ad6b3ac2aeaae9ea7297a569499e6598a609765093a4991e461404e1143b0024)
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
 (.leaf 0xfb3e4f43c8f13c0ed3b0eb398e437cdd370db360d7358b72d8b52d0b32c8ad2aca6290a32889f2789d1f87d1f07b1e87916859160571585504c10034070031))
 (.branch 387
 (.leaf 0x1bb6e5b46c9b16c1ad6b1ab699a467d9d6719b66197659775d9755d1735c96d5ad66591635895f5795d4f93d4f13b4e9394d1324b52b4a92949925491054110340901400ac2a8a929ca3288a02709b2007f1f07b1e0771705b16057150530a42608c1d05c070051)
 (.leaf 0x2bcae208811785d0006)))
 (.branch 390
 (.branch 389
 (.leaf 0x2429023b8e6388de348ce328b62b89a2488e2287e1e875fe7f5fc7edfa7e5f47c9ed7adea7a5e6795e4715c470dc2705c04cd314c12e4a92949d234890741903408ff3f8e538ce2380dc36cd9354d42e4b82d4b42c4b01785d15855150530e4360cc2d05c0d0051)
 (.leaf 0x3a0e72ecba1705b0006))
 (.branch 391
 (.leaf 0x4d93542508168590006)
 (.leaf 0x0))))
 (.branch 396
 (.branch 394
 (.branch 393
 (.leaf 0x290a3a89a1e86a1682a06809ee799d2729c6709b66c9ae4c92e4a9264891df37c5f07b9ea7a5e778de271dc670dc26fdbe5b16a5a56758d625815c56d404fd3c4ed384dcfa3e0f73d4f13c0ee3a8e92ecba2ccb22c4b0208811e8791e07710c400f42d074100051)
 (.leaf 0x3f4fc2e4b82007f0006))
 (.branch 395
 (.leaf 0x5bd6e509411f87d0006)
 (.leaf 0x0)))
 (.branch 398
 (.branch 397
 (.leaf 0x7d9f5725c82dcb60006)
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 408
 (.branch 404
 (.branch 402
 (.branch 401
 (.leaf 0x2deb72d7b56d4b4ed0b3eceb26c7b0ac0afebeaeebaae69aa6698a5e96a562c8aa2989e2388a208721b801ff7f1fb7e1f7695a3689a06719b66595651795e1755d1715c10942101400ff3f84d128470cc230041)
 (.leaf 0x0))
 (.branch 403
 (.leaf 0x6a1a75ed7a41d060006)
 (.leaf 0x0)))
 (.branch 406
 (.branch 405
 (.leaf 0x8be2e80a01415040006)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 432
 (.branch 424
 (.branch 420
 (.branch 418
 (.branch 417
 (.leaf 0x2f3bc6ecbaae9ba2e5b92e3b22c6b16c3afebeaf2b8ade9ca6e98a5e94a4e7a9e2779d6719c26e9aa6993a4d92a4991a456e9b86ddb56c5b06b9aa6a57b5e9735c9715c1425053a4e5384dc51138470f4260041)
 (.leaf 0x0))
 (.branch 419
 (.leaf 0x6f5bc5e5785013f0006)
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 428
 (.branch 426
 (.branch 425
 (.leaf 0x9f67c9424f4f93d0006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 440
 (.branch 436
 (.branch 434
 (.branch 433
 (.leaf 0xb2ecaa7a9d5dd760006)
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
 (.leaf 0x2f2bc2efbb6e9ba2e6b8ae1b76dbb6ad8b52d3b46cdb329ea7696a5694a4e8fa368ca2a86a16839fe7e9424f9224791a459063f8fa3c8e2378d6318c202805fa7e5f87ddc9721c1701bf6f8521384a100360041)
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 454
 (.branch 453
 (.leaf 0x91243801ff71dc60006)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 460
 (.branch 458
 (.branch 457
 (.leaf 0xa4a9193a4d715c40006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 472
 (.branch 468
 (.branch 466
 (.branch 465
 (.leaf 0xb82dfa729b7f9fd0006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 496
 (.branch 488
 (.branch 484
 (.branch 482
 (.branch 481
 (.leaf 0xbd6f4a6a999324b0006)
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
 (.leaf 0x2bcae2a4a7298a428ca227c9e2709b25c952509123c8b22488214831cc711c06d1ac67194641845f02408018030024)))
 (.branch 518
 (.branch 517
 (.leaf 0x0)
 (.leaf 0x3a0e7388e037cdd370db360d7354d4340ce334ca320c4308c12f8bc1d4721bc6e1ac69198631885f03c0e030030024))
 (.branch 519
 (.leaf 0x4d9354c12e4b52b4a9294992548d224791c46d18459124410f4310a1d8741bc6d1b06a1a0631846006418058030024)
 (.leaf 0x0))))
 (.branch 524
 (.branch 522
 (.branch 521
 (.leaf 0x0)
 (.leaf 0x3f4fc3dcf53d0f23c4f03b4ec3a8e9348cf330cb320c630cc02fcbc2649624c9223c8d228872188304811030060024))
 (.branch 523
 (.leaf 0x5bd6e5a5675996458d6257d5e5715b55d555515153d4b52548515432689824c912408e230872148407c1e070060024)
 (.leaf 0x0)))
 (.branch 526
 (.branch 525
 (.leaf 0x7d9f57c1ee7b5eb7a9e9799e578de2779dc76dd8759d2741cf731ca34cd1330ca324c7314c02f8bd0bc2e0b00c0024)
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 536
 (.branch 532
 (.branch 530
 (.leaf 0x0)
 (.branch 531
 (.leaf 0x6a1a7689a067d9d6719b66197655946418e6358a62184609815f97c4811d46919459144450e4350a09424088160024)
 (.leaf 0x0)))
 (.branch 534
 (.branch 533
 (.leaf 0x8be2e8a62789a2488e2287e1e8721b85e158521183e0b82608816034851f4691845d1544d0e4310b0d4340c8160024)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 560
 (.branch 552
 (.branch 548
 (.branch 546
 (.leaf 0x0)
 (.branch 547
 (.leaf 0x6f5bc6ddb56d1b26c5b06b5ac6a9a96498f6318b6218660d805fd7c5655654d5253d4d52947519430a0270881c0024)
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 556
 (.branch 554
 (.branch 553
 (.leaf 0x9f67c9de759d2729c6709b66c9aa699966398a5f9765995e5694e515695854d515414e53147515440fc3e0f01c0024)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 568
 (.branch 564
 (.branch 562
 (.branch 561
 (.leaf 0xb2ecab16c3b0ac0afebeaeebaae2b7aceb1ac2adaaea7a96a4a869f64d916318a62587615805f97d12448118220024)
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
 (.leaf 0x912438fa3c8ee398e2378d2338c6308661684e1283e0d82a0781a03781dd769d9759d4745ce735ca0e0370c82c0024)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 588
 (.branch 586
 (.branch 585
 (.leaf 0xa4a91a328aa2687a1a85a0a819fe7e99e64986609765b9625595251785df769d875dd574dce731cb108410f02c0024)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 600
 (.branch 596
 (.branch 594
 (.branch 593
 (.leaf 0xb82dfb6ad8b5ed5b52d3b42cfb36ccad6b2abeaeaaea9a9aa3a8a9f86a1884e118420e83207816041304b118320024)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 624
 (.branch 616
 (.branch 612
 (.branch 610
 (.branch 609
 (.leaf 0xbd6f4bbeedbb2eaba6e8b96e4b8ae1adab4abeadab2aaaa2a3a86a09a2669865f97a5c96a5594e521404f1183c0024)
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
 (.leaf 0xfd3e0f43ccf13bcee3b0ea3a0e337cde370da364d7354c3308c1300bf2f8af2a8a6294a3284a02789c22889220872188519865190631886104c11038080031))
 (.branch 643
 (.leaf 0x1bd6e1b46cdb16bdae6b1aa6a1a367d9e6719a6659765583609816017f5f96f5a96659563585605795c5294952147519454d9314b52c4a92849d2548d114410f4390d430ae2aca92a0a32849f2749b2308b22087210831a067190631805f0a4270901e060080051)
 (.leaf 0x2b4ac2388d1a8690006)))
 (.branch 646
 (.branch 645
 (.leaf 0x2448fe3b8ea388da358ce318be2a89a2588e218821e8720a8260881e06815f67c5ed7b1ea7a1e7795e3745d073dce735cc4d5324c12f4a92849924489134490f4390b428e7390e2384dc368d8358d4314c4304c02f4bc1a869188611805f0e4370d02e0600e0051)
 (.leaf 0x398e531cc61a0670006))
 (.branch 647
 (.leaf 0x4d13345514198650006)
 (.leaf 0x0))))
 (.branch 652
 (.branch 650
 (.branch 649
 (.leaf 0x292a3689a2286a1283a067f9f6789d2739c66f9ba6c9aa5895e569565494df57c9f07bdea7a1e6791e274dd273dce72dca5b96b5a56858d6157d5d56d4c52d4851d4450cfc3e4f73d8f13bced3ace931cc62fcbe2f4bc2388d218852108310c410f82e078110051)
 (.leaf 0x3ecfa314c42308b0006))
 (.branch 651
 (.leaf 0x5b56c5394d228890006)
 (.leaf 0x0)))
 (.branch 654
 (.branch 653
 (.leaf 0x7d1f3755d430cc20006)
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 664
 (.branch 660
 (.branch 658
 (.branch 657
 (.leaf 0x2e0b6ed7b5ad4b4ad1b3ecdb2ec6b0ac1afebdaf2baae2a6a96a4a8ea2a862e8ae298a2238861f8761b8320b822078120369da4689a16719a6619665185611816017d5f1154510d4310b4284d12c480d0240041)
 (.leaf 0x0))
 (.branch 659
 (.leaf 0x699a561d8644d120006)
 (.leaf 0x0)))
 (.branch 662
 (.branch 661
 (.leaf 0x8b62c83a0d445100006)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 688
 (.branch 680
 (.branch 676
 (.branch 674
 (.branch 673
 (.leaf 0x2f5bc2ecbaee9b9ee6b92e2b2ac7b16c4afebdaeeb9adea8a9ea4a8ea0a7e7c9e6779da719be6d9ae6996a5995a5594a516f1b96ddb66c5af6b5ab6a5876197f5f97d5f14e535465154450c5113c480f8270041)
 (.leaf 0x0))
 (.branch 675
 (.leaf 0x6edba615845314b0006)
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 684
 (.branch 682
 (.branch 681
 (.leaf 0x9ee7a9725b529490006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 696
 (.branch 692
 (.branch 690
 (.branch 689
 (.leaf 0xb26c8aaaa960d820006)
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
 (.leaf 0x2f4bc6efbbae9b9ee5b8ee1b7edcb6ad9b52d2b42ceb32aaaa6a2a86a0a7e91a3a8ca2e86a1282a027e9725b9525394a5190e408fa3d8e2368d2328c20e836068160480dd5751cd731cb7285213c4b104370041)
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 710
 (.branch 709
 (.leaf 0x90a418320b74dd20006)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 716
 (.branch 714
 (.branch 713
 (.leaf 0xa428f96a59745d00006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 728
 (.branch 724
 (.branch 722
 (.branch 721
 (.leaf 0xb7addaa2a782a090006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 752
 (.branch 744
 (.branch 740
 (.branch 738
 (.branch 737
 (.leaf 0xbcef2a9aa5962570006)
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
 (.leaf 0xfc3e8f33c8f03bcee3b4e939ce5378dd36cda364d8350cf338cd330cb328ae2b0a5290a2284a027c9b2589525093248911c8711c06f1b86d04c1203c090031))
 (.branch 771
 (.leaf 0x1bc6e9b36c9b06bdae6b5a969da56799d66d9a665986518f6398d6318b6296e5b165591625856057d5b5595555153549514d5334b12b4a52849d264891d4711b46919460af2b4a829ca22849e2749c26097250932408f1d0731c06f1b06b0a4280941f064090051)
 (.leaf 0x2acaa268991d8750006)))
 (.branch 774
 (.branch 773
 (.leaf 0x2439063a8e6378da358d2308ba2c8962488a218821f86e168561484e12845f57cdec7ade97a1e7799e2775dc76dda765d84d9344bd2e4a5284952448d1f4791b46917458e8398e1380db368d7358d5344d0334cc324c81d8751b86d1b06b0e4380d42f0640f0051)
 (.leaf 0x390e334cd21d0730006))
 (.branch 775
 (.leaf 0x4c931485201c8710006)
 (.leaf 0x0))))
 (.branch 780
 (.branch 778
 (.branch 777
 (.leaf 0x291a3e88a1e85a1283a0a7e9f27a9ce729c26f9ba6d9a66498e629866097df67d1ef7b9e97a1e5791e377dde76dda75dd65bd6d5a167589615795d5715855d5454d5053cfd3ecf63d4f03bcec3acea34cd232cca324c826899248912408f10c420fc2f07c120051)
 (.leaf 0x3e4f8344d0260970006))
 (.branch 779
 (.leaf 0x5ad6a56959258950006)
 (.leaf 0x0)))
 (.branch 782
 (.branch 781
 (.leaf 0x7c9f1785e033cce0006)
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 792
 (.branch 788
 (.branch 786
 (.branch 785
 (.leaf 0x2dfb76d6b56d3b4ad1b42ccb2ac8b06c0afabdaf2bbadeb2ac6b0abeaeab62f8b62889e228861e8761c86217852138420f6a1a6685a066d9a65d96655916418d631896212148119461174584d130490d4250041)
 (.leaf 0x0))
 (.branch 787
 (.leaf 0x691a364d9247d1e0006)
 (.leaf 0x0)))
 (.branch 790
 (.branch 789
 (.leaf 0x8ae2a86a194751c0006)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 816
 (.branch 808
 (.branch 804
 (.branch 802
 (.branch 801
 (.leaf 0x2f4bcaebbaae8b9ee6b96e1b2ec9b12c3afabdaeab9ae2b4aceb0abeacaae7d9ee769d6709be6c9ae6a99a6598a6197a5d6f5bb6d9b56c1af6b1ab6a9936498b629896215a565525455053c51140490fc280041)
 (.leaf 0x0))
 (.branch 803
 (.leaf 0x6e5b864590561570006)
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 812
 (.branch 810
 (.branch 809
 (.leaf 0x9e6789a267559550006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 824
 (.branch 820
 (.branch 818
 (.branch 817
 (.leaf 0xb1ec6adab563d8e0006)
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
 (.leaf 0x2f5bceeebb6e8b9ee4b8ee2b82deb66d8b4ed2b3eceb36b6ad6aeab6acaae92a428ba2a85a1281a027f9a2679825f97a5d912428f63c8de368ce328c61a866128461083de1781d9761d7758521404c108380041)
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 838
 (.branch 837
 (.leaf 0x9023f8621777dde0006)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 844
 (.branch 842
 (.branch 841
 (.leaf 0xa3a8d99a65775dc0006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 856
 (.branch 852
 (.branch 850
 (.branch 849
 (.leaf 0xb72dbad2b385a150006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 880
 (.branch 872
 (.branch 868
 (.branch 866
 (.branch 865
 (.leaf 0xbc6f0acab1992630006)
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
 (.leaf 0x2f5bd2f3bcaf1bc2e6b96e4b8ee2b86e0b7edeb76dcb6ed1b42cfb3acdb32cbb2ac9b22c7b1abcaeebaae6b8ade92a4690a3e8ea3683a0a81a027f9fa7d9f27b9ea799e26e9b66c9ae6a9a64490e42906408fe358d2338ca318c22f8ba2d8b22b8aa2087e1e8761c86df67d5f47cdf27c5e7799e5791e3789bd6f1bb6e9b96e1ae6b5ac6adaa6a5a869da6695a468d9966197659956516f5b96d5b16b5a96057d5e5755c56d364d5344cd324c5274992549123488fd3f0fb3e8f93e0ee3b4ec3acea3a4e839ce6394e438cd9360d7358d5350af2b8ad2b0ab2a8a027c9e2749c26c521444d10c390a41300bb)
 (.leaf 0xf73d8f5388e1380a92a0a70009))
 (.branch 899
 (.leaf 0x1b76d9b5689a1681695a1674c12f4b8a6294a4000f)
 (.leaf 0x0)))
 (.branch 902
 (.branch 901
 (.leaf 0x23e8f63c8a62889df07bdee4b52c4acdf378dd000f)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 908
 (.branch 906
 (.branch 905
 (.leaf 0x28ca2e8a9de769d5ed7b1eb59965590f43ccf2000f)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 920
 (.branch 916
 (.branch 914
 (.branch 913
 (.leaf 0xb6ad9b62c5b12c389a258919f6799d000c)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 944
 (.branch 936
 (.branch 932
 (.branch 930
 (.branch 929
 (.leaf 0xbbeeebb6c2b06c09d2739c9b46cdb2000c)
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
 (.leaf 0xbb2ebbaad7b5ad5a2688a1e3b8ea39000c)
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
 (.leaf 0x148511404f1384d1304b12849120471184511043108411003f0f83d0f03b0e8390e0370d8350d0330c8310c02f0b82d0b02b0a8290a0270982509023088210801f0781d0701b06819060170581505013048110400f0380d0300b02809020070180501003008010052))
 (.branch 3
 (.leaf 0x2e9ba2e7b9ae5b92e3b8ae1b52d3b4ad1b42cfb3acdb32bfafabdaf2bbaeab9ae2b7ac2afabaadab2aba92a3a8aa1a829fa6297a5a95a5293a1a85a1283a0a81a027f9fa719c26f9ba6d9b26b9aa6998a619825f97a5d95a559525394a5192a499224791a458e2378da358d2338ca318c22388a218821f87a1d8721b8521384a118420f8220781a05812037f1fb7e9f97e1f77a9e97a1e7799e5791e3789db769d9761d7759cf739cd731cb729c3709c1701bf6f9b16c1af6b9ad6b1ab6a9a96719b6699966197659956518d6318b62989621816017f5f97d5f1755d1735c9715c163589615815f5795d5715b55153549515414f5214751945511434f13b4e9394e1374a9294a12749925491234891b46919461174590f4390d4310b4290340901400ff3f8f13c0ef3b8ed3b0eb3a8e9370db368d9360d7358d5350cd330cb328c9320c1300bf2f8bd2f0b52d0b32c8b12c0a3288a12809f2789d2709b25093248912408f2208721885210831f07b1e8791e0771c06f1b86d1b06b19063188611805f160571585515053013b)
 (.branch 4
 (.leaf 0xbd6f4bcef2bc6f0bbeeebb6ecbaeeab82dfb7addb72dbb6ad9b62d7b5ad5b2ecab26c8b1ec6b16c4b0ec2b06c0adab5ad2b3acab1aaaa9aa2a7a9aa5a7a9da729ba6a99a4a91a428fa3a8da328ba2a89a22879f67c9ee7a9e6789de769d6749ce729a26799a65992639725b96a59962579424f93a4d9324b9124390a419023f8fa3d8f23b8ea398be2e8b62c8ae2a8a62889e268962486a198621785a1583a0d8320b82a0980a01801ff7f9fd7d9f57d1f37c9f17c1ef7b9ed7b1eb785e077dde775dc755d474dd2745d0725c871dc6715c46f5bc6edba6e5b86ddb66d5b46cdb26a1a7699a5691a3689a16819f6799d64d926459063d8e61d866158460d825ed7a5e5785dd765bd6e5b56c5ad6a5a56859d66595645695956157559555394d5314b52949509415013f4f93d4d9354d1334c9314c12f4b92d4b12b4852047d1e4751c4551444d12445104250841d06415043f4fc3ecfa3e4f83dcf63d4f43ccf23a0e7398e5390e3388e1380df378dd34cd2344d033cce31cc6314c430cc22ecba2e4b82dcb62bcae2b4ac2acaa2a4a829ca6294a42689926097258952388d2308b22889208812007f1f87d1d8751d0731c8711a8691a067198651785d1705b168590168)
 (.leaf 0x0))))
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
 (.leaf 0x7fffffffffffffffffffe))
 (.branch 3
 (.leaf 0x3fe001ff000ff81f81f81f8007fc003fe07e07e07e001ff000ff81f81f81f8007fc0fc0fc0fc003fe001ff03f03f03f000ff81f81f81f8007fc0fc0fc0fc003fe001ff03f03f03f000ff81f81f81f81f81f81f800000000000000000000)
 (.branch 4
 (.leaf 0x3ffc01ffe00fff007e07e07e07ff803ffc01f81f81f81ffe00fff007e07e07e07ff803f03f03f03ffc01ffe00fc0fc0fc0fff007e07e07e07ff803f03f03f03ffc01ffe00fc0fc0fc0fff007e07e07e07e07e07e0000000000000000000000)
 (.leaf 0x0))))
def kindMasks := kindMaskTable.get
def keys := List.range 5
def vertexMaskTable : Table Nat :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf 28948022309329048855892746252171976963317496166410131338457839084944885809151)
 (.leaf 181709681073901722637330951972001133588410340171829515070343601772850492979493588181076562005595627541420909447779597506640231909032959))
 (.branch 3
 (.leaf 7914572847139345089936080672628710081124021461557704975527380464020739202275431343281802683977734542847098589836539308446552239931418511810812879727121139859082971671891606543)
 (.branch 4
 (.leaf 2392032866531905486790934664236547198800531051553847485036591697399599776587344870179019828932003182256153527707179505186334817545849692891732846499617140859034367623730106817821497097062475593358449)
 (.leaf 722947573429303679218969471571518201112459810491425040698575173501403338293907650291350830211090305445088723262375213605153333438056257294104501023719814784641903755417338486683853005575361026660677015792148605678165950465))))
 (.branch 7
 (.branch 6
 (.leaf 1516130226565182368444189936933577561020362414174905961547862666403559282270050989215692881540711635246367864595698162690250183407868356784478099240788761467200662226148540793808012432693495361501885771270274129347393961718710273)
 (.leaf 1516130949512066341379360654418878777065759642298058387753823187953608909735853802425311934490947666869637819952138033690710658514607822757029206827817781095972000239192437402294290050347589105171500686579850825874872745924231169))
 (.branch 8
 (.leaf 1516130949512411069317086166430356884466014750288488149583355349701628854438898815099250539967332237682401740611135140772658170571310809463803988728765519741479146618379460864532916669287776382905484205495115996867968377676326290)
 (.branch 9
 (.leaf 1516130949512411069481385159847348367983494148062984474773309576891606597709097571828748873879011601309450635096344363013130145608738705444778273505151723064722423022494936211384205353577314928668867873554701168686411167268973220)
 (.leaf 1516130949512411069481425271906288063169899782681581763915201655560354150869075647697091036558189257404086145080349541045903698337019327489695503555145957977643136713023284716107557718978752804290392137145859964064790690346750792)))))
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
 (.branch 9
 (.leaf (.leaf 0))
 (.leaf (.leaf 4)))
 (.branch 11
 (.leaf (.leaf 5))
 (.leaf (.leaf 6))))
 (.branch 14
 (.branch 13
 (.leaf (.leaf 7))
 (.leaf (.leaf 8)))
 (.leaf (.leaf 0)))))
 (.branch 24
 (.branch 20
 (.branch 18
 (.leaf (.leaf 0))
 (.branch 19
 (.leaf (.leaf 9))
 (.leaf (.leaf 0))))
 (.branch 22
 (.branch 21
 (.leaf (.leaf 10))
 (.leaf (.leaf 0)))
 (.branch 23
 (.leaf (.leaf 11))
 (.leaf (.leaf 0)))))
 (.leaf (.leaf 0))))
 (.branch 48
 (.branch 40
 (.branch 36
 (.branch 34
 (.leaf (.leaf 0))
 (.branch 35
 (.leaf (.leaf 12))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
 (.branch 44
 (.branch 42
 (.branch 41
 (.leaf (.leaf 13))
 (.leaf (.leaf 0)))
 (.branch 43
 (.leaf (.leaf 14))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0))))
 (.branch 56
 (.branch 52
 (.branch 50
 (.branch 49
 (.leaf (.leaf 15))
 (.leaf (.leaf 0)))
 (.branch 51
 (.leaf (.leaf 16))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 96
 (.branch 80
 (.branch 72
 (.branch 68
 (.leaf (.leaf 0))
 (.branch 70
 (.branch 69
 (.leaf (.leaf 17))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 76
 (.branch 74
 (.branch 73
 (.leaf (.leaf 18))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 78
 (.branch 77
 (.leaf (.leaf 19))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 88
 (.branch 84
 (.branch 82
 (.branch 81
 (.leaf (.leaf 20))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 86
 (.branch 85
 (.leaf (.leaf 21))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0))))
 (.branch 112
 (.branch 104
 (.branch 100
 (.branch 98
 (.branch 97
 (.leaf (.leaf 22))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 108
 (.branch 106
 (.branch 105
 (.leaf (.leaf 23))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 120
 (.branch 116
 (.branch 114
 (.branch 113
 (.leaf (.leaf 24))
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
 (.leaf (.leaf 25)))
 (.branch 131
 (.leaf (.leaf 26))
 (.leaf (.leaf 27))))
 (.branch 134
 (.branch 133
 (.leaf (.leaf 28))
 (.leaf (.leaf 29)))
 (.branch 135
 (.leaf (.leaf 30))
 (.leaf (.leaf 0)))))
 (.branch 140
 (.branch 138
 (.branch 137
 (.leaf (.leaf 31))
 (.leaf (.leaf 32)))
 (.branch 139
 (.leaf (.leaf 33))
 (.leaf (.leaf 0))))
 (.branch 142
 (.branch 141
 (.leaf (.leaf 34))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 152
 (.branch 148
 (.branch 146
 (.branch 145
 (.leaf (.leaf 35))
 (.leaf (.leaf 0)))
 (.branch 147
 (.leaf (.leaf 36))
 (.leaf (.leaf 0))))
 (.branch 150
 (.branch 149
 (.leaf (.leaf 37))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0))))
 (.branch 176
 (.branch 168
 (.branch 164
 (.branch 162
 (.branch 161
 (.leaf (.leaf 38))
 (.leaf (.leaf 0)))
 (.branch 163
 (.leaf (.leaf 39))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
 (.branch 172
 (.branch 170
 (.branch 169
 (.leaf (.leaf 40))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 184
 (.branch 180
 (.branch 178
 (.branch 177
 (.leaf (.leaf 41))
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
 (.leaf (.leaf 42))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 198
 (.branch 197
 (.leaf (.leaf 43))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 204
 (.branch 202
 (.branch 201
 (.leaf (.leaf 44))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 216
 (.branch 212
 (.branch 210
 (.branch 209
 (.leaf (.leaf 45))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 240
 (.branch 232
 (.branch 228
 (.branch 226
 (.branch 225
 (.leaf (.leaf 46))
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
 (.leaf (.leaf 47)))
 (.branch 259
 (.leaf (.leaf 48))
 (.leaf (.leaf 49))))
 (.branch 262
 (.branch 261
 (.leaf (.leaf 50))
 (.leaf (.leaf 51)))
 (.branch 263
 (.leaf (.leaf 52))
 (.leaf (.leaf 0)))))
 (.branch 268
 (.branch 266
 (.branch 265
 (.leaf (.leaf 53))
 (.leaf (.leaf 54)))
 (.branch 267
 (.leaf (.leaf 55))
 (.leaf (.leaf 0))))
 (.branch 270
 (.branch 269
 (.leaf (.leaf 56))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 280
 (.branch 276
 (.branch 274
 (.branch 273
 (.leaf (.leaf 57))
 (.leaf (.leaf 0)))
 (.branch 275
 (.leaf (.leaf 58))
 (.leaf (.leaf 0))))
 (.branch 278
 (.branch 277
 (.leaf (.leaf 59))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0))))
 (.branch 304
 (.branch 296
 (.branch 292
 (.branch 290
 (.branch 289
 (.leaf (.leaf 60))
 (.leaf (.leaf 0)))
 (.branch 291
 (.leaf (.leaf 61))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
 (.branch 300
 (.branch 298
 (.branch 297
 (.leaf (.leaf 62))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 312
 (.branch 308
 (.branch 306
 (.branch 305
 (.leaf (.leaf 63))
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
 (.leaf (.leaf 64))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 326
 (.branch 325
 (.leaf (.leaf 65))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 332
 (.branch 330
 (.branch 329
 (.leaf (.leaf 66))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 344
 (.branch 340
 (.branch 338
 (.branch 337
 (.leaf (.leaf 67))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 368
 (.branch 360
 (.branch 356
 (.branch 354
 (.branch 353
 (.leaf (.leaf 68))
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
 (.leaf (.leaf 69))
 (.leaf (.leaf 70)))
 (.branch 387
 (.leaf (.leaf 71))
 (.leaf (.branch 0x1000000000000000000000000000000040000000000000000000000000000000200000000000000000000000000000008 (.leaf 72) (.leaf 73)))))
 (.branch 390
 (.branch 389
 (.leaf (.leaf 74))
 (.leaf (.branch 0x1000000000000000000000000000000100000000000000000000000000000000200000000000000000000000000000020 (.leaf 75) (.leaf 76))))
 (.branch 391
 (.leaf (.branch 0x1000000000000000000000000000000100000000000000000000000000000000400000000000000000000000000000040 (.leaf 77) (.leaf 78)))
 (.leaf (.leaf 0)))))
 (.branch 396
 (.branch 394
 (.branch 393
 (.leaf (.leaf 79))
 (.leaf (.branch 0x1000000000000000000000000000001000000000000000000000000000000000200000000000000000000000000000200 (.leaf 80) (.leaf 81))))
 (.branch 395
 (.leaf (.branch 0x1000000000000000000000000000001000000000000000000000000000000000400000000000000000000000000000400 (.leaf 82) (.leaf 83)))
 (.leaf (.leaf 0))))
 (.branch 398
 (.branch 397
 (.leaf (.branch 0x1000000000000000000000000000001000000000000000000000000000000001000000000000000000000000000001000 (.leaf 84) (.leaf 85)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 408
 (.branch 404
 (.branch 402
 (.branch 401
 (.leaf (.leaf 86))
 (.leaf (.leaf 0)))
 (.branch 403
 (.leaf (.branch 0x1000000000000000000000000000100000000000000000000000000000000000400000000000000000000000000040000 (.leaf 87) (.leaf 88)))
 (.leaf (.leaf 0))))
 (.branch 406
 (.branch 405
 (.leaf (.branch 0x1000000000000000000000000000100000000000000000000000000000000001000000000000000000000000000100000 (.leaf 89) (.leaf 90)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0))))
 (.branch 432
 (.branch 424
 (.branch 420
 (.branch 418
 (.branch 417
 (.leaf (.leaf 91))
 (.leaf (.leaf 0)))
 (.branch 419
 (.leaf (.branch 0x1000000000000000000000001000000000000000000000000000000000000000400000000000000000000000400000000 (.leaf 92) (.leaf 93)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
 (.branch 428
 (.branch 426
 (.branch 425
 (.leaf (.branch 0x1000000000000000000000001000000000000000000000000000000000000010000000000000000000000010000000000 (.leaf 94) (.leaf 95)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 440
 (.branch 436
 (.branch 434
 (.branch 433
 (.leaf (.branch 0x1000000000000000000000001000000000000000000000000000000000001000000000000000000000001000000000000 (.leaf 96) (.leaf 97)))
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
 (.leaf (.leaf 98))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 454
 (.branch 453
 (.leaf (.branch 0x1000000000000000100000000000000000000000000000000000000000000001000000000000000100000000000000000 (.leaf 99) (.leaf 100)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 460
 (.branch 458
 (.branch 457
 (.leaf (.branch 0x1000000000000000100000000000000000000000000000000000000000000010000000000000001000000000000000000 (.leaf 101) (.leaf 102)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 472
 (.branch 468
 (.branch 466
 (.branch 465
 (.leaf (.branch 0x1000000000000000100000000000000000000000000000000000000000001000000000000000100000000000000000000 (.leaf 103) (.leaf 104)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 496
 (.branch 488
 (.branch 484
 (.branch 482
 (.branch 481
 (.leaf (.branch 0x1000000000000000100000000000000000000000000000000000000010000000000000001000000000000000000000000 (.leaf 105) (.leaf 106)))
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
 (.leaf (.leaf 107)))
 (.branch 515
 (.leaf (.leaf 108))
 (.leaf (.leaf 109))))
 (.branch 518
 (.branch 517
 (.leaf (.leaf 110))
 (.leaf (.leaf 111)))
 (.branch 519
 (.leaf (.leaf 112))
 (.leaf (.leaf 0)))))
 (.branch 524
 (.branch 522
 (.branch 521
 (.leaf (.leaf 113))
 (.leaf (.leaf 114)))
 (.branch 523
 (.leaf (.leaf 115))
 (.leaf (.leaf 0))))
 (.branch 526
 (.branch 525
 (.leaf (.leaf 116))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 536
 (.branch 532
 (.branch 530
 (.branch 529
 (.leaf (.leaf 117))
 (.leaf (.leaf 0)))
 (.branch 531
 (.leaf (.leaf 118))
 (.leaf (.leaf 0))))
 (.branch 534
 (.branch 533
 (.leaf (.leaf 119))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0))))
 (.branch 560
 (.branch 552
 (.branch 548
 (.branch 546
 (.branch 545
 (.leaf (.leaf 120))
 (.leaf (.leaf 0)))
 (.branch 547
 (.leaf (.leaf 121))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
 (.branch 556
 (.branch 554
 (.branch 553
 (.leaf (.leaf 122))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 568
 (.branch 564
 (.branch 562
 (.branch 561
 (.leaf (.leaf 123))
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
 (.leaf (.leaf 124))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 582
 (.branch 581
 (.leaf (.leaf 125))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 588
 (.branch 586
 (.branch 585
 (.leaf (.leaf 126))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 600
 (.branch 596
 (.branch 594
 (.branch 593
 (.leaf (.leaf 127))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 624
 (.branch 616
 (.branch 612
 (.branch 610
 (.branch 609
 (.leaf (.leaf 128))
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
 (.leaf (.leaf 129))
 (.leaf (.leaf 130)))
 (.branch 643
 (.leaf (.leaf 131))
 (.leaf (.branch 0x10000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000008 (.leaf 132) (.leaf 133)))))
 (.branch 646
 (.branch 645
 (.leaf (.leaf 134))
 (.leaf (.branch 0x10000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000020 (.leaf 135) (.leaf 136))))
 (.branch 647
 (.leaf (.branch 0x10000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000040 (.leaf 137) (.leaf 138)))
 (.leaf (.leaf 0)))))
 (.branch 652
 (.branch 650
 (.branch 649
 (.leaf (.leaf 139))
 (.leaf (.branch 0x10000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000200 (.leaf 140) (.leaf 141))))
 (.branch 651
 (.leaf (.branch 0x10000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000400 (.leaf 142) (.leaf 143)))
 (.leaf (.leaf 0))))
 (.branch 654
 (.branch 653
 (.leaf (.branch 0x10000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000001000 (.leaf 144) (.leaf 145)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 664
 (.branch 660
 (.branch 658
 (.branch 657
 (.leaf (.leaf 146))
 (.leaf (.leaf 0)))
 (.branch 659
 (.leaf (.branch 0x10000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000040000 (.leaf 147) (.leaf 148)))
 (.leaf (.leaf 0))))
 (.branch 662
 (.branch 661
 (.leaf (.branch 0x10000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000100000 (.leaf 149) (.leaf 150)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0))))
 (.branch 688
 (.branch 680
 (.branch 676
 (.branch 674
 (.branch 673
 (.leaf (.leaf 151))
 (.leaf (.leaf 0)))
 (.branch 675
 (.leaf (.branch 0x10000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000400000000 (.leaf 152) (.leaf 153)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
 (.branch 684
 (.branch 682
 (.branch 681
 (.leaf (.branch 0x10000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000010000000000 (.leaf 154) (.leaf 155)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 696
 (.branch 692
 (.branch 690
 (.branch 689
 (.leaf (.branch 0x10000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000001000000000000 (.leaf 156) (.leaf 157)))
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
 (.leaf (.leaf 158))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 710
 (.branch 709
 (.leaf (.branch 0x10000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000100000000000000000 (.leaf 159) (.leaf 160)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 716
 (.branch 714
 (.branch 713
 (.leaf (.branch 0x10000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000001000000000000000000 (.leaf 161) (.leaf 162)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 728
 (.branch 724
 (.branch 722
 (.branch 721
 (.leaf (.branch 0x10000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000100000000000000000000 (.leaf 163) (.leaf 164)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 752
 (.branch 744
 (.branch 740
 (.branch 738
 (.branch 737
 (.leaf (.branch 0x10000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000001000000000000000000000000 (.leaf 165) (.leaf 166)))
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
 (.leaf (.leaf 167))
 (.leaf (.leaf 168)))
 (.branch 771
 (.leaf (.leaf 169))
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000008 (.leaf 170) (.leaf 171)))))
 (.branch 774
 (.branch 773
 (.leaf (.leaf 172))
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000020 (.leaf 173) (.leaf 174))))
 (.branch 775
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000040 (.leaf 175) (.leaf 176)))
 (.leaf (.leaf 0)))))
 (.branch 780
 (.branch 778
 (.branch 777
 (.leaf (.leaf 177))
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000200 (.leaf 178) (.leaf 179))))
 (.branch 779
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000400 (.leaf 180) (.leaf 181)))
 (.leaf (.leaf 0))))
 (.branch 782
 (.branch 781
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000001000 (.leaf 182) (.leaf 183)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 792
 (.branch 788
 (.branch 786
 (.branch 785
 (.leaf (.leaf 184))
 (.leaf (.leaf 0)))
 (.branch 787
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000040000 (.leaf 185) (.leaf 186)))
 (.leaf (.leaf 0))))
 (.branch 790
 (.branch 789
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000100000 (.leaf 187) (.leaf 188)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0))))
 (.branch 816
 (.branch 808
 (.branch 804
 (.branch 802
 (.branch 801
 (.leaf (.leaf 189))
 (.leaf (.leaf 0)))
 (.branch 803
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000400000000 (.leaf 190) (.leaf 191)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
 (.branch 812
 (.branch 810
 (.branch 809
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000010000000000 (.leaf 192) (.leaf 193)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 824
 (.branch 820
 (.branch 818
 (.branch 817
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000001000000000000 (.leaf 194) (.leaf 195)))
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
 (.leaf (.leaf 196))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 838
 (.branch 837
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000100000000000000000 (.leaf 197) (.leaf 198)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 844
 (.branch 842
 (.branch 841
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000001000000000000000000 (.leaf 199) (.leaf 200)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 856
 (.branch 852
 (.branch 850
 (.branch 849
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000100000000000000000000 (.leaf 201) (.leaf 202)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 880
 (.branch 872
 (.branch 868
 (.branch 866
 (.branch 865
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000001000000000000000000000000 (.leaf 203) (.leaf 204)))
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
 (.leaf (.leaf 205))
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000 (.leaf 206) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000200000000000000000000000000000000 (.leaf 207) (.leaf 208)))))
 (.branch 899
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000 (.leaf 209) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000400000000000000000000000000000000 (.leaf 210) (.leaf 211))))
 (.leaf (.leaf 0))))
 (.branch 902
 (.branch 901
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000 (.leaf 212) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000000 (.leaf 213) (.leaf 214))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 908
 (.branch 906
 (.branch 905
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000 (.leaf 215) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000000000000000000 (.leaf 216) (.leaf 217))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 920
 (.branch 916
 (.branch 914
 (.branch 913
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000 (.leaf 218) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000000000 (.leaf 219) (.leaf 220))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 944
 (.branch 936
 (.branch 932
 (.branch 930
 (.branch 929
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000 (.leaf 221) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000000000000000000000000 (.leaf 222) (.leaf 223))))
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
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000 (.leaf 224) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000000000000000000000 (.leaf 225) (.leaf 226))))
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
def candidateMasks (i : Nat) := PackedRawNatGrowth.take 758
  (PackedRawNatGrowth.drop (758*(i%64)) (candidateMasksBlocks.get (i/64)))

def badMasksBlocks : Table Nat :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf badMasksBlock0000)
 (.branch 2
 (.leaf badMasksBlock0001)
 (.leaf badMasksBlock0002)))
 (.branch 4
 (.leaf badMasksBlock0003)
 (.branch 5
 (.leaf badMasksBlock0004)
 (.leaf badMasksBlock0005))))
 (.branch 9
 (.branch 7
 (.leaf badMasksBlock0006)
 (.branch 8
 (.leaf badMasksBlock0007)
 (.leaf badMasksBlock0008)))
 (.branch 10
 (.leaf badMasksBlock0009)
 (.branch 11
 (.leaf badMasksBlock0010)
 (.leaf badMasksBlock0011)))))
def badMasks (i : Nat) := PackedRawNatGrowth.take 758
  (PackedRawNatGrowth.drop (758*(i%64)) (badMasksBlocks.get (i/64)))

def signatureMasksBlocks : Table Nat :=
(.branch 2
 (.branch 1
 (.leaf signatureMasksBlock0000)
 (.leaf signatureMasksBlock0001))
 (.branch 3
 (.leaf signatureMasksBlock0002)
 (.leaf signatureMasksBlock0003)))
def signatureMasks (i : Nat) := PackedRawNatGrowth.take 758
  (PackedRawNatGrowth.drop (758*(i%64)) (signatureMasksBlocks.get (i/64)))

def fastKind := rawKind
def candidateSupports := candidateRows
def kindSupports := kindRows
def wellFormedTest (i : Nat) : Bool := RawFacetEmbedding.wellFormedCheck (rawCells i)

def cellTest (i : Nat) := (listBounds 1024 (rawCells i).ridgeMasks && ((rawCells i).ridgeMasks.all (fun q => (candidateMasks q).testBit i) && (decide (rawKind i = (rawCells i).kind) && (decide ((rawCells i).vertices < 1024) && ((List.range 10).all (fun v => decide ((vertexMasks v).testBit i = (rawCells i).vertices.testBit v)) && (SignatureCompatibility.faces (rawCells i)).all (fun q => (SignatureCompatibility.profileMask (SignatureCompatibility.allMask 758) signatureIndex signatureMasks (rawCells i) q).testBit i))))))
def ridgeTest (i : Nat) := decide (candidateMasks i = RawNatGrowthCheck.mask (candidateRows i)) &&
  (candidateRows i).all (fun c => hasNat (rawCells c).ridgeMasks i)
def kindTest (i : Nat) := decide (kindMasks i = RawNatGrowthCheck.mask (kindRows i)) &&
  (kindRows i).all (fun c => decide ((rawCells c).kind = i))
def badTest (i : Nat) := if badMasks i = 0 then true else
  decide (Nat.land (badMasks i) (SignatureCompatibility.cover (SignatureCompatibility.allMask 758)
    vertexMasks signatureIndex signatureMasks (rawCells i)) = 0)

end Papers.RationalityTen.RootedCaches.RootedSevenPure009

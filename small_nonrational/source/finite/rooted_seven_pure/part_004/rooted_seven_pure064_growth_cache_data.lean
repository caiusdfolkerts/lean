module
prelude
public import RootedSevenPure064
public import SignatureCompatibility
public import PackedRawNatGrowth
public import FiniteChecks
public import RawFacetEmbedding
public import RootedSevenPure064GrowthCachecandidateMasksData000
public import RootedSevenPure064GrowthCachebadMasksData000
public import RootedSevenPure064GrowthCachesignatureMasksData000

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure064
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def rawCells := Papers.RationalityTen.FacetUniverses.RootedSevenPure064.rawCells
def cells (c : Fin 560) := rawCells c.val
def ridgeList := ConcreteGrowth.ridgeList cells
def literalCompatible (a b : Fin 560) := ConcreteGrowth.compatible (cells a) (cells b)
def kind (c : Fin 560) := (cells c).kind
def rawKindCode : Nat := 23036469977724505976326189450461549439257552977567124093391953592818593713786997587417214610926636420094753578270829422280516539334030084139657214635673907121217947305609768510077761688707236649666325224350583860351522122282203567304588654286667310397339441522300310358245876004654804047374149527849803800360737406181080700862232224834591145606575675515563484499130827158088136586916257772577958383349146029125387429019458326647212917979164594645660827105919958638027552889610008042606676459533175837987400
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
 (.leaf 0x19063188611805f1785d1705b16859160571585515053148511404f1384d1304b128491204711845110431084100c02004000028))))
 (.leaf 0x0))
 (.branch 24
 (.branch 20
 (.leaf 0x0)
 (.branch 22
 (.branch 21
 (.leaf 0x0)
 (.leaf 0x2809f2789d2709b26899260972589525093248912408f2388d2308b22889220872188521083208812007f1f87d0240801c000028))
 (.leaf 0x0)))
 (.branch 28
 (.branch 26
 (.leaf 0x0)
 (.branch 27
 (.leaf 0x0)
 (.leaf 0x19c66194000004)))
 (.leaf 0x0))))
 (.branch 48
 (.leaf 0x0)
 (.branch 56
 (.branch 52
 (.leaf 0x0)
 (.branch 54
 (.branch 53
 (.leaf 0x55153549515414f5394d5314b52949521475194551143509415013f4f93d4f13b4e9394e1374d9354d1334c9310801f078000028)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 60
 (.branch 58
 (.branch 57
 (.leaf 0x689a16819f6799d6719b66999661976599565193649916418f6398d6318b62989621876198561183609816017f0a8290a0000028)
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
 (.leaf 0x419054110340901400ff3f8fd3f0fb3e8f93e0f73d8f53d0f33c8f13c0ef3b8ed3b0eb3a8e93a0e7398e5390e305815050000028)
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
 (.leaf 0x334cc32c000004)
 (.leaf 0x0))))
 (.branch 108
 (.branch 106
 (.branch 105
 (.leaf 0x76dda765d875dd6755d474dd2745d073dce735cc72dca725c871dc6715c470dc2705c06fdbe6f5bc6edba6e5b80c02f0b8000028)
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
 (.leaf 0x1e0771d4741c8711bc6e1b46c1a86919456150511404e12848114441080501001001a)))
 (.branch 134
 (.branch 133
 (.leaf 0x0)
 (.leaf 0x2c4b02b8ad2acaa2a0a7298a528ca2248902348c22886210812007e160531484f1384c11c4610c4202c0a01c010024))
 (.branch 135
 (.leaf 0x378dd36cda360d7354d434cd2340cf32c57154521404d12c49118441041204401001a)
 (.leaf 0x0))))
 (.branch 140
 (.branch 138
 (.leaf 0x0)
 (.branch 139
 (.leaf 0x45d1645113445104390d4310b425083e0f63ccf23c0ec3a8e7398e41941805c14001a)
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 152
 (.branch 148
 (.branch 146
 (.branch 145
 (.leaf 0x0)
 (.leaf 0x318c530cc2300bf2f4bc2ecba2e0b72508f2388b2288820c821fc7e1940e03407001a))
 (.leaf 0x0))
 (.branch 150
 (.branch 149
 (.leaf 0x595645896157d5e5715b5695955d5651944505404f93a4e1354d13224c912388c22487214822007d08821078070024)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 156
 (.branch 154
 (.branch 153
 (.leaf 0x6cdb26c1af6b5ac6a9a96a1a7695a46519263d8e6318861983609801942c0ac28001a)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 176
 (.branch 168
 (.branch 164
 (.leaf 0x0)
 (.branch 166
 (.branch 165
 (.leaf 0x5e9795dd765d1735c5705bd6e5b16b521435093f4f93c4dd364cd3232c250901e001a)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 172
 (.branch 170
 (.branch 169
 (.leaf 0x7b1eb7a5e8799e578de2785e0779dd735cb721c7715c16fdbc6edb9659916418d6318a61584605800c8310b8280024)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 184
 (.branch 180
 (.branch 178
 (.branch 177
 (.leaf 0x85a1584e128420f8360c82e0a82207655936418e62d8961d846097f51d45509404f53b4e5364d1310e4380a01e0024)
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
 (.leaf 0x4b12b4a5284992548d22485204791d3e8f53d0f13c0ee3a4e8394e432c1b06814001a)
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 204
 (.branch 202
 (.branch 201
 (.leaf 0x806007f9fd7edfa7e1f77d9f57cdf273dca725c6715c36f9bd6e9b93e4f73d0f23bced3ace8398e30d4340b8140024)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 240
 (.branch 232
 (.branch 228
 (.branch 226
 (.branch 225
 (.leaf 0x8ae2a8a2278962488a218821f8761c739cc725c7711c2701bd6edb832c3d0f02e001a)
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
 (.leaf 0x1e8791d8751cc721c06e1b46b1a868198621805d1705a12447118431040601002001a)))
 (.branch 262
 (.branch 261
 (.leaf 0x0)
 (.leaf 0x2ccb22bcae2b0ab2a4a7298a428ca12789c264982588520c821fc7d1905f1785b1684b12045110410300a020020024))
 (.branch 263
 (.leaf 0x380df370db364d8358d434cd1340ce330631845e170591304a114431081304402001a)
 (.leaf 0x0))))
 (.branch 268
 (.branch 266
 (.leaf 0x0)
 (.branch 267
 (.leaf 0x46518455144491143d0d4310a42507411023fcfe3f0eb3a4e8394e31981905c15001a)
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 280
 (.branch 276
 (.branch 274
 (.branch 273
 (.leaf 0x0)
 (.leaf 0x320c7310c3304c02f8bc2ecb92e0b62809b2689725887210812007d1980f03408001a))
 (.leaf 0x0))
 (.branch 278
 (.branch 277
 (.leaf 0x59d6658d625815f5755b5695855d55549505354c529394dd364cd3127c9d2689825488218811fc7e08c2107c080024)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 284
 (.branch 282
 (.branch 281
 (.leaf 0x6d5b46c5b06b9ad6ada96a1a6695a36819e66d9a66187615846057f1982d0ac29001a)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 304
 (.branch 296
 (.branch 292
 (.leaf 0x0)
 (.branch 294
 (.branch 293
 (.leaf 0x5f17b5e1775d5745c9705bd6d5b16a5514f5394b5293b4e1354d131330260901f001a)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 300
 (.branch 298
 (.branch 297
 (.leaf 0x7b9ed7a9e979de6791e2785df779dc765d7751d3745c06f9bd6e9b86899d6719966189619836097f0cc310bc290024)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 312
 (.branch 308
 (.branch 306
 (.branch 305
 (.leaf 0x86217852138461083a0c82e09822066859f6719a65d8a621836058054d515394c5253c4e9354cd320e8380a41f0024)
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
 (.leaf 0x4b92d4a92949d26491224851f4791c41901400fd3f0ed3a8e7398e33301c06815001a)
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 332
 (.branch 330
 (.branch 329
 (.leaf 0x80e027fdfe7f1fb7e5f77d9f47cdf176dd6755d2745c26fdbc6edb841503400fe3ecee3b0e7394e40d8340bc150024)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 368
 (.branch 360
 (.branch 356
 (.branch 354
 (.branch 353
 (.leaf 0x8b62c8a62889a2588e218821e8761b769d8755d3741c3705bc6e9b93303e0f02f001a)
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
 (.leaf 0xc8318c12fcbe2f4ba2e4b82ccb12b0aa2a4a8294a428c8420c82204801fc7a1e0731c4701bc6c1ac6a1204711845110430400d02804002b))
 (.branch 387
 (.leaf 0x12e4b1274952448d2047d1e465174491043d0e42d0a424ea3a4e839ce6394e0378d935cd6354d2344d01e4771d8741c06f1b4691a04a12446114421041d06817044040035)
 (.leaf 0x1f07b1304b0004)))
 (.branch 390
 (.branch 389
 (.leaf 0x17c5e9755cd725c56e5b56c59d655815e5755c5655855d384dd364d5344ccdf374dc368d6354d333cce2c8b02bcad2a4a8298a228486214822047e1f44c12c4410c4210427090210440a003b)
 (.leaf 0x2d4b422087128490006))
 (.branch 391
 (.leaf 0x388e1120470004)
 (.leaf 0x0))))
 (.branch 396
 (.branch 394
 (.branch 393
 (.leaf 0x203805fc7e9f97e1f57d1f37b9ec79de5791e3781df779bf6f9bd6f1bb6e9b56cdae6b1ab6a9a7699a5619856118360981461164551343d0e4310841cec3ace839ce438c370d0310ac17003b)
 (.leaf 0x0))
 (.branch 395
 (.leaf 0x46d1a3b8ed0004)
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 408
 (.branch 404
 (.branch 402
 (.branch 401
 (.leaf 0x21885a1183e0e8360a826086d1b26c5af6adaa6a1a468d8861d8460d805fd66591635855d5715a559554e9394d9354c93131cc5310c22f8bd2ecb72d88821c801fc7e1f43b0e02b0840d003b)
 (.leaf 0x328c9218850004))
 (.leaf 0x0))
 (.branch 406
 (.branch 405
 (.leaf 0x5a5684f13b210830006)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 412
 (.branch 410
 (.branch 409
 (.leaf 0x6ddb6629890004)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 432
 (.branch 424
 (.branch 420
 (.branch 418
 (.branch 417
 (.leaf 0x22d8ae268922388a1f87a1d85e158521283a0d82e07819ed7adea7a1e478de1775dc705c06f5bc6e5b862989609816017f5ed795e1765c9715bd6b5a93c4ed344cd324c43f0f0380c424003b)
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 422
 (.branch 421
 (.leaf 0x5f97d4e9390004)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 428
 (.branch 426
 (.branch 425
 (.leaf 0x7c1ef70dc2621870006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 440
 (.branch 436
 (.branch 434
 (.branch 433
 (.leaf 0x86a19619854e1370006)
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
 (.leaf 0x22c8aa2989e2388a208721b80a007fdfd7e5f87d9f27c5c3709bb6e9b96e12d4ad2a4a12448d214751c3b8ed398e5390e31003c0d01a002b)
 (.leaf 0x0))
 (.branch 451
 (.leaf 0x4c12f3b0eb0004)
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 460
 (.branch 458
 (.branch 457
 (.leaf 0x81604705c03a8e90006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 496
 (.branch 488
 (.branch 484
 (.branch 482
 (.branch 481
 (.leaf 0x8be2e6fdbe0004)
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
 (.leaf 0x1f07b1d8741cc711c06f1b06b1a46819c6117c5e16c59154531484f1340601403001a)))
 (.branch 518
 (.branch 517
 (.leaf 0x0)
 (.leaf 0x2d4b42bcad2b0aa2a4a8294a4288a12749b268972549123c8e22c8918c601745c16457150511404d0300b024030024))
 (.branch 519
 (.leaf 0x388e1370da364d7358d5348d133cce334641885d16c5a160561444f1381304803001a)
 (.leaf 0x0))))
 (.branch 524
 (.branch 522
 (.leaf 0x0)
 (.branch 523
 (.leaf 0x46d1a455134491043d0e42d0a4210740d01400fd3ecf73d4f43c4ef19c1906016001a)
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 536
 (.branch 532
 (.branch 530
 (.branch 529
 (.leaf 0x0)
 (.leaf 0x328c9310c2304bf2f8bd2e8b92dcb627c9c26498254932408d2308919c0f03809001a))
 (.leaf 0x0))
 (.branch 534
 (.branch 533
 (.leaf 0x5a56858d615815e5755c56558559555454f5394b5254550d424fd3d2809e26497258942488d22c8a08c22080090024)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 540
 (.branch 538
 (.branch 537
 (.leaf 0x6ddb66c5af6b9ac6adaa69da6691a367d9d6719965d93645906358b19c2d0b02a001a)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 560
 (.branch 552
 (.branch 548
 (.leaf 0x0)
 (.branch 550
 (.branch 549
 (.leaf 0x5f97d5e1765d5735c9715b96d5ad6a54d505354c52547511415013d3342609420001a)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 556
 (.branch 554
 (.branch 553
 (.leaf 0x7c1ef7a9e879de5791e3781df775dc761d6755d2741cc729c9719c46859e66d9a65d956498f6398b0cc320c02a0024)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 568
 (.branch 564
 (.branch 562
 (.branch 561
 (.leaf 0x86a19852128460f83a0d82a0981e06689a066d99661966518f6358c551525354b52948519414fd3e0e8390a8200024)
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
 (.leaf 0x4c12f4a92849d25491234811f4751c415023fcfe3ecf93d8f33c8ef3341c06c16001a)
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 588
 (.branch 586
 (.branch 585
 (.leaf 0x816047fdfd7f1fa7e5f87d5f47c9f1769d7751d3741ce72dc871dc4419043fcfd3f0fa3e0f33c4f00d8350c0160024)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 624
 (.branch 616
 (.branch 612
 (.branch 610
 (.branch 609
 (.leaf 0x8be2e8a62789a2488e2287e1e8721b76dd9751d2745cf735c8719c53343e0f430001a)
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
 (.leaf 0xca314c1300be2f0bb2e4b72d4b02b0ab2a4a7298a42889023c8e2348c22c7c1dc731c8701b86d1ac6915053148511404f0400e02c05002b))
 (.branch 643
 (.leaf 0x1304ad27499244892147d1d46d164491143d0d4310a420f63d4f43ccf23c4e2374d9360d6350d3344cf1ec781d8751c06e1b06a1a056154521444e1341d06c18048050035)
 (.leaf 0x1e879160570004)))
 (.branch 646
 (.branch 645
 (.leaf 0x17e5e5755d1725c16f5b56b5a5645815f5755b569585594450d42505404fce1378dc36cd6350d2340ce2d0b12bcae2a4a7294a3284922448e2348a2245815c5013c4e13427094220480b003b)
 (.leaf 0x2ccb225093158550006))
 (.branch 647
 (.leaf 0x380df150530004)
 (.leaf 0x0))))
 (.branch 652
 (.branch 650
 (.branch 649
 (.leaf 0x205801fc7edf97ddf67d1f27c1eb79de6791e2785df775cb729c9721c7719b76c9ae6b5ab6a5a8699a4649916418f6398d469174551443d0d42d0941cf83dcf43ccf03bc370d4320b018003b)
 (.leaf 0x0))
 (.branch 651
 (.leaf 0x465183e8f90004)
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 664
 (.branch 660
 (.branch 658
 (.branch 657
 (.leaf 0x21a856118420e8320b826076d9b36c5b06ada969da568d9464d9063d8c62d68595635895d56d5955d5551945509414f93d324c6310c32f8bc2e8b82d89424c8c22c8a2243b0e42c0880e003b)
 (.leaf 0x320c7248910004))
 (.leaf 0x0))
 (.branch 662
 (.branch 661
 (.leaf 0x59d66521472408f0006)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 668
 (.branch 666
 (.branch 665
 (.leaf 0x6d5b4659950004)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 688
 (.branch 680
 (.branch 676
 (.branch 674
 (.branch 673
 (.leaf 0x22f8aa26896238862087a1c866168521383a0c82a08819ef7b1ea7a5e4789e0779dc735cc725c8715c4659956398d6318b5f57a5e1775c9705b96c5a94851d404fd3e4f43f0f4390c825003b)
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 678
 (.branch 677
 (.leaf 0x5f17b519450004)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 684
 (.branch 682
 (.branch 681
 (.leaf 0x7b9ed73dce651930006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 696
 (.branch 692
 (.branch 690
 (.branch 689
 (.leaf 0x8621764991511430006)
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
 (.leaf 0x22e8ae298a2238861f8761b812017fdfe7e5f77d5f37c5cf739c7719c57112f4b12a4a524489204791c3e8f93c8f13c0ef1003d0d41b002b)
 (.leaf 0x0))
 (.branch 707
 (.leaf 0x4b92d3e0f70004)
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 716
 (.branch 714
 (.branch 713
 (.leaf 0x80e02735cc3d8f50006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 752
 (.branch 744
 (.branch 740
 (.branch 738
 (.branch 737
 (.leaf 0x8b62c72dca0004)
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
 (.leaf 0xc931cc02fcbd2f0bb2e8b62d0b22acaa2a0a7298a52849c26c9a2649825c7b1e4721c46f1b86d1b0681805f1785d1705b0400f03006002b))
 (.branch 771
 (.leaf 0x12f4b52649523489214811c46918445104390d4310b41d02405003fcfe3f4e137cd835cd5350d3348ce1f07a1d4741bc6e1ac6a1a4621845e1745a1641d0701904c060035)
 (.leaf 0x1e077190630004)))
 (.branch 774
 (.branch 773
 (.leaf 0x17d5ed745cd715c16f5b96a5a16657d5e5715b569595555053d4e5354c52ce2380db368d5350d1340cf2d4b32b8ad2a0a7290a32889e2749a264962546418c5c16c5a164270982304c0c003b)
 (.leaf 0x2c4b02809f188610006))
 (.branch 775
 (.leaf 0x378dd1805f0004)
 (.leaf 0x0))))
 (.branch 780
 (.branch 778
 (.branch 777
 (.leaf 0x204809fb7e9f87ddf67d5f17bded799e578de2785e0771d7759d5751d3749b66d1ad6b1aa6a5a869da36799d6719b6699946d19451134390d429094210440d003fcfc3ec370d8330b419003b)
 (.leaf 0x0))
 (.branch 779
 (.leaf 0x45d16419050004)
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 792
 (.branch 788
 (.branch 786
 (.branch 785
 (.leaf 0x21985e1083e0d8320b82a066ddb56c1af6a9a9699a5691a067d9c66d9865d6959d625855c56d5855d56549515394d52949328c830cc22f4bc2e4b82dca027c9825c962543b0e82d08c0f003b)
 (.leaf 0x318c52789d0004))
 (.leaf 0x0))
 (.branch 790
 (.branch 789
 (.leaf 0x59564551532709b0006)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 796
 (.branch 794
 (.branch 793
 (.leaf 0x6cdb2689a10004)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 816
 (.branch 808
 (.branch 804
 (.branch 802
 (.branch 801
 (.leaf 0x22e8b225892228862087e1b86a1884e128360c8260881df07b9e97a1e3789df779dd765d8755d4745d0689a166999661975f97c5dd765c5705b56c5ad5454d4c52d4a5243f0f83a0cc26003b)
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 806
 (.branch 805
 (.leaf 0x5e979549510004)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 812
 (.branch 810
 (.branch 809
 (.leaf 0x7b1eb76dda6819f0006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 824
 (.branch 820
 (.branch 818
 (.branch 817
 (.leaf 0x85a156799d5414f0006)
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
 (.leaf 0x22f8b62889e228861e8761c816037f9fd7e1f77d1f37c9db769d3749d1741304b9294a1234891f4791d419053f8fd3f0fb1003e0d81c002b)
 (.leaf 0x0))
 (.branch 835
 (.leaf 0x4b12b411030004)
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 844
 (.branch 842
 (.branch 841
 (.leaf 0x80600765d8409010006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 880
 (.branch 872
 (.branch 868
 (.branch 866
 (.branch 865
 (.leaf 0x8ae2a75dd60004)
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
 (.leaf 0x22f8ba2d8b22b8aa2087e1e8761c86e1a8661885e168560b82a098220781a058120380a01801f67d5f47cdf27c5f07bdee7b5ec7ade1781df779dd771b76d9b56d1b36c9a869da6695a468d7e5f57c5ed7a5e56f5b96d5b16b5a9695a167599655915a5655855d56555304bd2e4b52c4ad214811f4791d4711b46919461174590c42d0a4250841ce2384e037cde374d3348d1340cf338ca324c831cc6314bb2e8b92e0b72d8b52d0b32c8b12c0a6294a428ca22847c1ec7a1e4781dc6d1b06b1a8691a0400fc3b0dc270741000a3)
 (.leaf 0xc430cc22bcae2b4761d4740009))
 (.branch 899
 (.leaf 0x4a9294a11545113370db368731c871000c)
 (.leaf 0x0)))
 (.branch 902
 (.branch 901
 (.leaf 0x5e1775d96358961364d835cac2acaa000c)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 908
 (.branch 906
 (.branch 905
 (.leaf 0x7fdfe7f5ea7a5e86c5b06bd1244510000c)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 920
 (.branch 916
 (.branch 914
 (.branch 913
 (.leaf 0x85213849ae6b5ac5815f578c1300bf000c)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 944
 (.branch 936
 (.branch 932
 (.branch 930
 (.branch 929
 (.leaf 0x8a62889e118420f79de6795755d173000c)
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
 (.leaf 0x226896247f1fb7e927499250009)
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
 (.leaf 0x1003f0f83d0f03b0e8390e0370d8350d0330c8310c02f0b82d0b02b0a8290a0270982509023088210801f0781d0701b06819060170581505013048110400f0380d0300b02809020070180501003008010040))
 (.branch 3
 (.leaf 0x22388a218821f87a1d8721b83a0d8320b82a0982207819f97e1f77d9f57d1f37c9f1791e3789e1781df779dd771d5751d3749d1741c9721c7719c5711bd6f1bb6e9b96e1ab6a9a96a1a7699a5691a36719b66999661976418f6398d6318b61183609816017f5c9715c16f5b96d5b16b5a95d5715b5695956157559555394d5314b52949509415013f4f93d4d9354d1334c93149123489214811f4791d4710f4390d4310b4290942107400ff3f8fd3f0fb3d0f33c8f13c0ef3a0e7398e5390e3358d5350d3348d1340cf338be2f4bc2ecba2e4b82dcb62a4a829ca6294a428ca22849a2649825c962548e2348c22c8a22482204801fc7e1f4701bc6e1b46c1ac6a1a4681785d1705b16859148511404f1384d11845110431084100e1)
 (.branch 4
 (.leaf 0x8be2e8b62c8ae2a8a62889e268962486a198621785a158521384a118420f8160480e02806007fdfe7f5fc7edfa7c1ef7b9ed7b1eb7a9e97a1e7799e576dda765d875dd673dce735cc72dca70dc2705c06fdbe6ddb66d5b46cdb26c5b06bdae6b5ac689a16819f6799d6599565193649916298962187619855f97d5f17b5e9795e1775d9755d1735a56859d665956458d625856057d5e55153549515414f5214751945511434f13b4e9394e1374c12f4b92d4b12b4a9294a1274992546d1a4651845d164551444d12445104190541103409013e8f93e0f73d8f53b8ed3b0eb3a8e9388e1380df378dd370db368d9360d7334cc32cca324c831cc6314c430cc2304c02fcb52d0b32c8b12c0af2b8ad2b0ab2a8a027c9e2749c26c9424c922449023c8821c862148420c7c1ec7a1e4781dc761d4741cc721c4671986519063188611805f1605715855150531304b1284912047010e)
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
 (.leaf 0x1fffffffffffffffe))
 (.branch 3
 (.leaf 0xff8007fc003fe001ff03f03f03f000ff81f81f81f8007fc003fe07e07e07e001ff000ff81f81f81f8007fc0007fc003fe07e07e07e001ff007e07e07e0000000000000000)
 (.branch 4
 (.leaf 0xfff007ff803ffc01ffe00fc0fc0fc0fff007e07e07e07ff803ffc01f81f81f81ffe00fff007e07e07e07ff803fff803ffc01f81f81f81ffe00ff81f81f800000000000000000)
 (.leaf 0x0))))
def kindMasks := kindMaskTable.get
def keys := List.range 5
def vertexMaskTable : Table Nat :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf 12855504354071922204335696738729300820177587056774195263438847)
 (.leaf 65185151242703554760590262029087245649292916675105624366153060943637331864504850037811839103))
 (.branch 3
 (.leaf 19701003098197239606139454864920564198985109045186373794354699949401840955704436153967328907572787141661706515521423)
 (.branch 4
 (.leaf 858099707516326214372737599885174152158659711514814978934701792878142857200506742257349641391165017196644065005438087326521510045788716711923742125285441537)
 (.leaf 1799564659717571036798001030339632072140506403037861437747661663938314871963581397144837809489386075609401633433507477583209048082052691477900935462115737088353153))))
 (.branch 7
 (.branch 6
 (.leaf 3773962424820683252943212080760913884229472345430641309211593777619014486092718948935658304253360566922173605144592817898181912931163153744701262718078011757422721368065)
 (.leaf 3773960625256881634261344152109505212282714829156414338859588702089052531145953904009520399729014259553889714127593323102280355983936555995725821660699076146252527697921))
 (.branch 8
 (.leaf 3773962424821541352241554385926618598802842298733557953343054102070568893087758734213683407791838733040140864816000639055051030018659740646520135431469839319031352880306)
 (.branch 9
 (.leaf 3773962424821541352241554580940646417701073056617201443396950159572241580539291334967505523195875120072107635110399853573017671757935951361175010815483396431807968425300)
 (.leaf 3773962424821541352241554580988257264336546257485825379795889099039405074847751181793861436798268683643160387080548916907400665497054912094374308931510173931783022565992)))))
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
def candidateMasks (i : Nat) := PackedRawNatGrowth.take 560
  (PackedRawNatGrowth.drop (560*(i%64)) (candidateMasksBlocks.get (i/64)))

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
def badMasks (i : Nat) := PackedRawNatGrowth.take 560
  (PackedRawNatGrowth.drop (560*(i%64)) (badMasksBlocks.get (i/64)))

def signatureMasksBlocks : Table Nat :=
(.branch 2
 (.branch 1
 (.leaf signatureMasksBlock0000)
 (.leaf signatureMasksBlock0001))
 (.branch 3
 (.leaf signatureMasksBlock0002)
 (.leaf signatureMasksBlock0003)))
def signatureMasks (i : Nat) := PackedRawNatGrowth.take 560
  (PackedRawNatGrowth.drop (560*(i%64)) (signatureMasksBlocks.get (i/64)))

def fastKind := rawKind
def candidateSupports := candidateRows
def kindSupports := kindRows
def wellFormedTest (i : Nat) : Bool := RawFacetEmbedding.wellFormedCheck (rawCells i)

def cellTest (i : Nat) := (listBounds 1024 (rawCells i).ridgeMasks && ((rawCells i).ridgeMasks.all (fun q => (candidateMasks q).testBit i) && (decide (rawKind i = (rawCells i).kind) && (decide ((rawCells i).vertices < 1024) && ((List.range 10).all (fun v => decide ((vertexMasks v).testBit i = (rawCells i).vertices.testBit v)) && (SignatureCompatibility.faces (rawCells i)).all (fun q => (SignatureCompatibility.profileMask (SignatureCompatibility.allMask 560) signatureIndex signatureMasks (rawCells i) q).testBit i))))))
def ridgeTest (i : Nat) := decide (candidateMasks i = RawNatGrowthCheck.mask (candidateRows i)) &&
  (candidateRows i).all (fun c => hasNat (rawCells c).ridgeMasks i)
def kindTest (i : Nat) := decide (kindMasks i = RawNatGrowthCheck.mask (kindRows i)) &&
  (kindRows i).all (fun c => decide ((rawCells c).kind = i))
def badTest (i : Nat) := if badMasks i = 0 then true else
  decide (Nat.land (badMasks i) (SignatureCompatibility.cover (SignatureCompatibility.allMask 560)
    vertexMasks signatureIndex signatureMasks (rawCells i)) = 0)

end Papers.RationalityTen.RootedCaches.RootedSevenPure064

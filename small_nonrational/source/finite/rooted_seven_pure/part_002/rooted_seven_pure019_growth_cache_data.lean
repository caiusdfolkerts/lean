module
prelude
public import RootedSevenPure019
public import SignatureCompatibility
public import PackedRawNatGrowth
public import FiniteChecks
public import RawFacetEmbedding
public import RootedSevenPure019GrowthCachecandidateMasksData000
public import RootedSevenPure019GrowthCachebadMasksData000
public import RootedSevenPure019GrowthCachesignatureMasksData000

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure019
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def rawCells := Papers.RationalityTen.FacetUniverses.RootedSevenPure019.rawCells
def cells (c : Fin 586) := rawCells c.val
def ridgeList := ConcreteGrowth.ridgeList cells
def literalCompatible (a b : Fin 586) := ConcreteGrowth.compatible (cells a) (cells b)
def kind (c : Fin 586) := (cells c).kind
def rawKindCode : Nat := 6962345837212099168588236730831349673176561799330348054689740931942911910660944614107034560433683125266196722445281714320686811014397995951336985001959763325008251977111750288312617773990284062530201034875991559711185271847989934991721926618950895600917983373221226940143796369156736716022722847404479979540940905028405434539830899938581082728342871346982033945601517884255317747595684460188636272255782059565865639141715052238671736346298437293203295654804607399615262092962164856203874213410712672799457788895956971949119841424
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
 (.leaf 0x2408c220842007c1e0741c06c1a0641805c160541404c120441003c0e0340c02c0a0240801c060140400c02004000025))))
 (.leaf 0x0))
 (.branch 24
 (.branch 20
 (.leaf 0x0)
 (.branch 22
 (.branch 21
 (.leaf 0x0)
 (.leaf 0x6017c5e1745c16c5a1645815c561545414c521445013c4e1344c12c4a1244811c461144410c42104400fc3e0f4000025))
 (.leaf 0x0)))
 (.branch 28
 (.branch 26
 (.leaf 0x0)
 (.branch 27
 (.leaf 0x0)
 (.leaf 0x9c26094000004)))
 (.leaf 0x0))))
 (.branch 48
 (.branch 40
 (.branch 36
 (.leaf 0x0)
 (.branch 38
 (.leaf 0x0)
 (.branch 39
 (.leaf 0xae2b4ac2acaa2a4a829ca6294a428ca2284a027c9e2749c26c9a2649825c962549424c922449023c8e2348c22c000025)
 (.leaf 0x0))))
 (.branch 44
 (.branch 42
 (.leaf 0x0)
 (.branch 43
 (.leaf 0xe7398e5390e3388e1380df378dd370db368d9360d7358d5350d3348d1340cf338cd330cb328c9320c7318c5310000025)
 (.leaf 0x0)))
 (.branch 46
 (.branch 45
 (.leaf 0x1354d1334c9314c12f4b92d4b12b4a9294a1274992549123489214811f4791d4711b46919461174591545113448000025)
 (.leaf 0x0))
 (.leaf 0x0))))
 (.leaf 0x0)))
 (.branch 96
 (.branch 80
 (.branch 72
 (.leaf 0x0)
 (.branch 76
 (.leaf 0x0)
 (.branch 78
 (.branch 77
 (.leaf 0x159561575595555153549515414f5394d5314b52949521475194551143509415013f4f93d4f13b4e9394e1374d8000025)
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 88
 (.branch 84
 (.leaf 0x0)
 (.branch 86
 (.branch 85
 (.leaf 0x1926459063d8e6358c62d8a6258861d866158460d82605805fd7e5f57c5ed7a5e5785dd765d5745cd725c5705bc000025)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 92
 (.branch 90
 (.branch 89
 (.leaf 0x1f57d1f37c9f17c1ef7b9ed7b1eb7a9e97a1e7799e5791e3789e1781df779dd771db769d9761d7759d5751d3748000025)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.leaf 0x0)))
 (.branch 192
 (.branch 160
 (.branch 144
 (.branch 136
 (.branch 132
 (.branch 130
 (.leaf 0x0)
 (.branch 131
 (.leaf 0x0)
 (.leaf 0x380dc350d0320c42f0b82d0b02a0a42505814044100380a02005010020017)))
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
 (.leaf 0xf83dcf53d0f23c4ef3b8ed3b0ea3a4d935cd434cd1334cb320c7314250017)
 (.leaf 0x0)))
 (.branch 142
 (.branch 141
 (.leaf 0x5a96959d66591635856057d5e5715b52d495194550d3f4f53a4e53749d254892147d1b46516455130020)
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 152
 (.branch 148
 (.branch 146
 (.branch 145
 (.leaf 0x0)
 (.leaf 0x8621483208801fc7d1f07b1e8781dc5413c4e12c4a120431083f0f8250017))
 (.leaf 0x0))
 (.branch 150
 (.branch 149
 (.leaf 0x68da26819f6759c669996619765594611825fd7e5f1785d9735c97014c511384c12447114421003d0020)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 156
 (.branch 154
 (.branch 153
 (.leaf 0x2068160380a007fdfd7f1fb7e9f87dde7795e2785df76dd9759d574c250017)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 176
 (.branch 168
 (.branch 164
 (.branch 162
 (.leaf 0x0)
 (.branch 163
 (.leaf 0x4350c4290941d0641103409013fcfe36cd6354d2344cf328c9318c52889d2709926096244902348c0020)
 (.leaf 0x0)))
 (.branch 166
 (.branch 165
 (.leaf 0x6e1b76d5b46c9b16bdae6b5ac6a9a94a52448d2047d1d46117451132849f2709a25c9524c902388b0020)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 172
 (.branch 170
 (.branch 169
 (.leaf 0x86e1a862178561484a118420f8360c4a12648d214791c4691745512368d8354d3340ce330c931cc40020)
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
 (.leaf 0x735cc729c971dc6711c3709c16fdbe619816017d5f17a5d5745c5705354851d4450d414f13b4e1370020)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 204
 (.branch 202
 (.branch 201
 (.leaf 0x8c22f8b62c8aa2989e268962488a217a5e478de077ddd761d7751d35314a51d45509404f93b4e5360020)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 216
 (.branch 212
 (.branch 210
 (.branch 209
 (.leaf 0x9164490a418fe3e8f23b8ea398de367a1e678de1779dc769d7755d2615836017e5ed795dd745c96f0020)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))))
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
 (.leaf 0x3a0e4360d4330c8300b82d0ac2a0a026088200741c0680901c0600c010017)))
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
 (.leaf 0xfa3e4f63d4f33c8f03b8ed3acea3a0e538ce037cdd330ca324c6310260017)
 (.leaf 0x0)))
 (.branch 270
 (.branch 269
 (.leaf 0x5b16b5a167595645896057d5d5715a55d555495153d3e4f13b4e1364cd314b92d4ad1a46117451120020)
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 280
 (.branch 276
 (.branch 274
 (.branch 273
 (.leaf 0x0)
 (.leaf 0x8821c8420c812007e1f07b1e4781d86016c5a15c5611c44104400f4260017))
 (.leaf 0x0))
 (.branch 278
 (.branch 277
 (.leaf 0x695a4685a06799d66d9966196655936418e62d8a621775d5745c56f17c5d1685815448118410fc3e0020)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 284
 (.branch 282
 (.branch 281
 (.leaf 0x20881e0480e01801fe7f1fb7e5f87d9f37c5ee7b5eb769d875dd4748260017)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 304
 (.branch 296
 (.branch 292
 (.branch 290
 (.leaf 0x0)
 (.branch 291
 (.leaf 0x43d0e42d0a4210741503409003fcfd39ce2384de374ce32cc831cc42b8a92a0a5290952488f2388b0020)
 (.leaf 0x0)))
 (.branch 294
 (.branch 293
 (.leaf 0x6e9b96d9b56cdb26c1ae6b5ab6a9a84d5304bd2c4ad1c46516455122b4ab2a0a628c962508f2348c0020)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 300
 (.branch 298
 (.branch 297
 (.leaf 0x8761c8661885a1584e118420e8360b4d1324bd2d4a91d46d1645113398e4384df370cf334c8318c50020)
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
 (.leaf 0x73dce72dca721c7715c3709c06fdbd6498d63189621795d9735c96f5655454d5053d404f53a4e5360020)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 332
 (.branch 330
 (.branch 329
 (.leaf 0x8ca318ba2d8ae2a8a2268962388a207d5f07bdec7addc765d6755d25615654d51539414fd3a4e1370020)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 344
 (.branch 340
 (.branch 338
 (.branch 337
 (.leaf 0x91e4690e429023f8f63b8ea388de357d1f27bded7a9dd76dd6751d36458f6318a61d7a5e1735c5700020)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0)))
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
 (.leaf 0x43d0d4210641504405003fcfa3e0f33c4f03bcec3acea32cca324c831cc6304bf2e8b82dcb62ccb22c4922449023c8e234390dc360d0300bc2d0a4280280901805008010036)
 (.leaf 0xf03b0300b0004)))
 (.branch 390
 (.branch 389
 (.leaf 0x73dcd721c6715c4705c06fdba6e1b36c5b06bdac6adaa695a36799c66d9a65d96655765d5745cd725c56c5a96558d625855e5755c4f53c4ed3a4e5384651845d1645514300be2f4bb2dcb62d0b02bc9424c9023c8c22c721c06f1b4691a0661886111845108410f83d0300b0100300801005a)
 (.leaf 0x1d47412047028090006))
 (.branch 391
 (.leaf 0x30cc225895020070006)
 (.leaf 0x0))))
 (.branch 396
 (.branch 394
 (.branch 393
 (.leaf 0x2328c22b8a62889e2488e228761b85a1484e1283e0e8360881a017fdfe7f5fa7e5f8765d875dd6755d45ad695a1665896157d5b5693f4f93b4e9374d91b4691745913448f93dcf63d0f03bced3a4e8334cc324c8314c40045)
 (.leaf 0x0))
 (.branch 395
 (.leaf 0x3f0fb33cce0004)
 (.leaf 0x0)))
 (.branch 398
 (.branch 397
 (.leaf 0x5b96d505404751c0006)
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 408
 (.branch 404
 (.branch 402
 (.branch 401
 (.leaf 0x91e459023e8f63c8e6388de0781604809fe7f5fb7ddf676dda75dd674dd2691a26859f66d9a6619464d785dd745cd705bc87214842087e1f47b1dc76120471003f0f83d0036)
 (.leaf 0x22889118450004))
 (.leaf 0x0))
 (.branch 406
 (.branch 405
 (.leaf 0x69da65e979110430006)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 412
 (.branch 410
 (.branch 409
 (.leaf 0x82a09775dc0004)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 432
 (.branch 424
 (.branch 420
 (.branch 418
 (.branch 417
 (.leaf 0x21c86a1985e1384a108320b6e5b76d9b46c1af6b5a96a11d47115451134490e4310b42505411023f8fd33cce31cc6314c4258952388d2308b002d)
 (.leaf 0x0))
 (.branch 419
 (.leaf 0x44510334cc250930006)
 (.leaf 0x0)))
 (.branch 422
 (.branch 421
 (.leaf 0x6f1bb46d1a248910006)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 428
 (.branch 426
 (.branch 425
 (.leaf 0x87e1e4651832cca0006)
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
 (.leaf 0x246912439063d8f23a8da358c62f8ba2c8a22789621881dd771d5751d3749ce731cb725c5711c26f9bd5e9795c9715c16f505404e5384dd36002d)
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 454
 (.branch 453
 (.leaf 0x745d05e1774fd3e0006)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 460
 (.branch 458
 (.branch 457
 (.leaf 0x8d23376dda4f53c0006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 472
 (.branch 468
 (.branch 466
 (.branch 465
 (.leaf 0x92648765d85d9750006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0)))))
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
 (.leaf 0x3c0ec360d0330c4300bc2c0ac290a0270841f0781b0641504c1203c0d0017)))
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
 (.leaf 0xfc3ecf63d0f33c4f03bcec3ace93a0e4388e1378dc360d6354d2340270017)
 (.leaf 0x0)))
 (.branch 526
 (.branch 525
 (.leaf 0x5b96d5a16659563589615795d56d5a5595454d505394a52147511424c9304bd2c4a926491234811e0020)
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 536
 (.branch 532
 (.branch 530
 (.branch 529
 (.leaf 0x0)
 (.leaf 0x8a22484208811fc7e1f47a1e4771d85f170591605514c501344c124270017))
 (.leaf 0x0))
 (.branch 534
 (.branch 533
 (.leaf 0x69da66859f6799c66d9a65d966519363d8d6318961d83605805f57b1805e16457158541484d12c4a0020)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 540
 (.branch 538
 (.branch 537
 (.leaf 0x20a8260480a017fdfe7f5fa7e5f77d9f27c1ef7b1ea799e478de0778270017)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 560
 (.branch 552
 (.branch 548
 (.branch 546
 (.leaf 0x0)
 (.branch 547
 (.leaf 0x4451042d094210641504405003f8fd398e3380df370da35cd434cd02b4aa29ca628ca12789b268970020)
 (.leaf 0x0)))
 (.branch 550
 (.branch 549
 (.leaf 0x6f1bb6d9b46cdb16c1af6b1ab6a5a84d1314b92d4a928495224851e2b8ac29ca5290a22809b264980020)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 556
 (.branch 554
 (.branch 553
 (.leaf 0x87e1e8661785a1484e1283e0e8320b4d5334b92c4ad2949d224811f39ce5380de374db364d4348d10020)
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
 (.leaf 0x745d072dc9721c6715c4705c06f9bd6458e62d8a61d856097f5f97b56155549515394c52546515420020)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 588
 (.branch 586
 (.branch 585
 (.leaf 0x8d2338ba2c8ae298a22789223886207d1f17b9ed7a9e8795e2785de565575495053d4d52d46511430020)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 600
 (.branch 596
 (.branch 594
 (.branch 593
 (.leaf 0x9264890e419023e8f63c8e6388da357d5f37b9ec7ade979de2781df6499062d89621866117f5f57c0020)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0)))
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
 (.leaf 0x4450c4210741503409003f8fc3dcf33c8f03b8ed3ace935cd6354d434cd230cbe2e8b92dcb52d0b22c09e2749c26c9a2643b0e0360d4300b82c0a82805815048110380d0036)
 (.leaf 0xe839060170004)))
 (.branch 646
 (.branch 645
 (.leaf 0x745cc721c7715c3709c06f9bc6ddb36c9b06b9ad6ada969da26799d66d996619665182605805fd7e5f56e5a565591625815f5755b5254851d46515444952448d2248520308bf2f4bc2dcb52ccb12bca027c9c26c9825c741c46f1b86919c6518c61148511384d12849060170400f0380d005a)
 (.leaf 0x1cc7215053058150006))
 (.branch 647
 (.leaf 0x304c0288a1050130006)
 (.leaf 0x0))))
 (.branch 652
 (.branch 650
 (.branch 649
 (.leaf 0x2348be2b8aa2889a2588e2187e1a85a1584e118420e8320a81601801fe7f1fb7e5f7795e478de2785e05b56a5a167589605795c5694b529475194350927499234891f478fb3e0f63d4f03b8ec3a8e8364d8354d4344d00045)
 (.leaf 0x0))
 (.branch 651
 (.leaf 0x3e8f936cda0004)
 (.leaf 0x0)))
 (.branch 654
 (.branch 653
 (.leaf 0x5b16b5354c4a5280006)
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 664
 (.branch 660
 (.branch 658
 (.branch 657
 (.leaf 0x926449023f8f63b8ea388da0981a0480dfe7f1fa7e1f679de678de277dde699a3685a066d9965d9564d8460d805fd7c5ec892188420c7e1f07a1e076150531304b128490036)
 (.leaf 0x22087148510004))
 (.leaf 0x0))
 (.branch 662
 (.branch 661
 (.leaf 0x695a4619851404f0006)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 668
 (.branch 666
 (.branch 665
 (.leaf 0x822077a5e80004)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 688
 (.branch 680
 (.branch 676
 (.branch 674
 (.branch 673
 (.leaf 0x21e86e19862138460f8360b6edb86d9b56c1ae6b1aa6a1294a1214811f479104350b4290540d013fcfd36cda34cd2344d0288a12689926097002d)
 (.leaf 0x0))
 (.branch 675
 (.leaf 0x43d0e364d82809f0006)
 (.leaf 0x0)))
 (.branch 678
 (.branch 677
 (.leaf 0x6e9b949d262789d0006)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 684
 (.branch 682
 (.branch 681
 (.leaf 0x8761c4952435cd60006)
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
 (.leaf 0x2489164390a3d8ee398de358ce308ba2d8a22689222881e97a1e1781df779d0735cb729c570dc16fdbd619855f97d5f17b5354c5154450d42002d)
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 710
 (.branch 709
 (.leaf 0x73dce6118352d4a0006)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 716
 (.branch 714
 (.branch 713
 (.leaf 0x8ca3179de6525480006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 728
 (.branch 724
 (.branch 722
 (.branch 721
 (.leaf 0x91e46795e4609810006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))))
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
 (.leaf 0x4410e41d0641103409013f4fb3e4f23c4ef3b8ed3b0e838ce2384e037cde308c02e4b82d8b52d0b32bcaa2a4a829ca62943c0e8350d02f0b82b0a829088210781d068190036)
 (.leaf 0xe037090230004)))
 (.branch 774
 (.branch 773
 (.leaf 0x741ce71dc6711c3709c16f5bb6e5b26c5af6b9ad6b1a8699a46759c669996619764d8e6358c62d8a6256d5ad6458d615815f5795a5555454d52545504c5304bd2e4b52c30cc12f0bb2d8b52c8b12c0ac2aca829ca428c751cc6e1b46819c6418c621785d1685915855090230701b06819005a)
 (.leaf 0x1c4701805f088210006))
 (.branch 775
 (.leaf 0x2fcbe2b8ad0801f0006)
 (.leaf 0x0))))
 (.branch 780
 (.branch 778
 (.branch 777
 (.leaf 0x2338c62a8a62789a258922087a1c8561484a118420f82e0981e007fdfd7f1fb7e9f67c5f07bdee7b5ec5b96c59d66585605755c56d57559535494f539334c92f4b92b4a8fc3e8f53d0ef3b8eb3a8e9394e4384e0374dc0045)
 (.leaf 0x0))
 (.branch 779
 (.leaf 0x3e0f739ce60004)
 (.leaf 0x0)))
 (.branch 782
 (.branch 781
 (.leaf 0x5a969565584d5340006)
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 792
 (.branch 788
 (.branch 786
 (.branch 785
 (.leaf 0x922468fe3e8f23b8ea398d60a82203809fd7f1f97e1f77cdf27bdee7adea69da56819f66999659956519063d8c62d8861c8a220832087d1f0791e0771805f16057158550036)
 (.leaf 0x218851785d0004))
 (.leaf 0x0))
 (.branch 790
 (.branch 789
 (.leaf 0x68da2649911705b0006)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 796
 (.branch 794
 (.branch 793
 (.leaf 0x81a057d5f40004)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 816
 (.branch 808
 (.branch 804
 (.branch 802
 (.branch 801
 (.leaf 0x21f8761885e128460e8360c6f1ba6d5b46bdae6adaa6a5354d12d4b12b4a91143d0a4250440d003fcfe39ce637cde374dc2b8ad298a5290a3002d)
 (.leaf 0x0))
 (.branch 803
 (.leaf 0x4350c394e42b0ab0006)
 (.leaf 0x0)))
 (.branch 806
 (.branch 805
 (.leaf 0x6e1b74cd322a8a90006)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 812
 (.branch 810
 (.branch 809
 (.leaf 0x86e1a4c53038ce20006)
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
 (.leaf 0x24991e429063c8ee388de368d2328b62c89e2688e22885f57d1ed7b1eb7a9d173dca725c470dc06fdbe649916298962187565585455053d4e002d)
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 838
 (.branch 837
 (.leaf 0x735cc6418f55d560006)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 844
 (.branch 842
 (.branch 841
 (.leaf 0x8c22f7cdf2555540006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 856
 (.branch 852
 (.branch 850
 (.branch 849
 (.leaf 0x916447c5f06398d0006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 960
 (.branch 928
 (.branch 912
 (.branch 904
 (.branch 900
 (.branch 898
 (.branch 897
 (.leaf 0x9264891e46916448ea398e2378da358d2338ca318c22f8962488e228862087e1e8761c86e1a8420f83a0d8320b82a098220781a057edfa7e5f87ddf6745d073dce735cc709c1701bf6f9bd6f1bb6e9b96e1b76b5ac6adaa6a5a869da6695a468da26619765995651935b96d5b16b5a96957d5e5755c56d5a4451043d0e4350c40901400ff3f8fd3f0fb3e8f93e0f73b4ec3acea3a4e830cc2304c02fcbe2d0b32c8b12c0af2288922087218851ec7a1e4781dc761d4741cc721c4701986519063188610f03b0e8390e0370b42c0ac2a0a42800a8)
 (.leaf 0x8420c821bc6e1b4360d4340009))
 (.branch 899
 (.leaf 0x42d0a424f63d4f42f4bc2ec330c831000c)
 (.leaf 0x0)))
 (.branch 902
 (.branch 901
 (.leaf 0x72dca725b66d5b4685a067d6859d662e8b92e06c1ac6a0012)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 908
 (.branch 906
 (.branch 905
 (.leaf 0x22e8b62c8661885e0480e025956458cf33c8f1000f)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 920
 (.branch 916
 (.branch 914
 (.branch 913
 (.leaf 0x90e4290601801ff6799d670812007f000c)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 944
 (.branch 936
 (.branch 932
 (.branch 930
 (.branch 929
 (.leaf 0x216856146cdb26c50841d060009)
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
 (.leaf 0x2408fe3e8ae2a8a5c871dc60009)
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
 (.leaf 0x8f63c8ee3a8e6388de368d62889e268962488e228862084e128461083e0e8360c82dfe7f5fc7edfa7e5f87ddf67bdee7b5ec7adea78de2785e077dde75dd6755d474dd2715c470dc2705c06fdbe6f5b06bdae6b5ac6adaa6a5a866d9a6659865d966559464d8c62d8a6258861d805fd7e5f57c5ed745cd725c5705bd625856057d5e5755c56d5a54d525455053d4e51d465154450d424ed3a4e5384dd364bd2e4b52c4ad2a48d224852047d1e45d164551444d124150440d02405003fcfe3f4f03bcee3b4ec3acea3a4e8384e037cde374dc354d434cd2344d0324c831cc6314c42dcb62d4b42ccb22c4b02bca829ca6294a428c9c26c9a2649825c9023c8e2348c22c7e1f47c1ec7a1e4781dc761a46819c661946418c621845a1645815c561544e1344c12c4a12442104400fc3e0f4300bc2e0b42c0ac2a0a4280781d0701b06819048110400f0380d018050100300801010e)
 (.branch 4
 (.leaf 0x2499224791a459124390a419023f8fa348ce328c6308be2e8b62c8ae2a8a61f87a1d8721b86a198621785a158520a8260881e068160480e02806007fdf57d1f37c9f17c1e97a1e7799e5791dd771db769d9761d1741cf739cd731cb729c9721c7719bc6edba6e5b86ddb66d5b46cdb26c5a7699a5691a3689a16819f6799d671926459063d8e635866158460d826057a5e5785dd765d56e5b56c5ad6a5a56859d665956458d5956157559555514d5314b52949521415013f4f93d4f1354d1334c9314c1294a127499254911d4711b46919461114410f4390d4310b4290942107418fc3ecfa3e4f83dcf63d4f43ccf23c4e7398e5390e3388db368d9360d7358cf338cd330cb328c3308c1300bf2f8bd2f0bb2e8b92e0ae2b4ac2acaa2a4a2284a027c9e274962549424c922448a2248821c862148420c82204801fc751d0731c8711c06f1b86d1b06b1a86017c5e1745c16c5414c521445013c4811c461144410c3c0ec3a0e4380dc360d4340cc320c4270982509023088210801f0601705815050130300b0280902007013b)
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
 (.leaf 0x0))
 (.branch 3
 (.leaf 0x3fe001ff000ff8007fc0fc0fc0fc003fe001ff000ff81f81f81f8007fc0fc0fc0fc0fc0fc0fc003fe001ff03f03f03f000ff81f81f81f8007fc003fe07e07e07e001ff007e07e07e)
 (.branch 4
 (.leaf 0x3ffc01ffe00fff007ff803f03f03f03ffc01ffe00fff007e07e07e07ff803f03f03f03f03f03f03ffc01ffe00fc0fc0fc0fff007e07e07e07ff803ffc01f81f81f81ffe00ff81f81f80)
 (.leaf 0x0))))
def kindMasks := kindMaskTable.get
def keys := List.range 5
def vertexMaskTable : Table Nat :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf 696898287454081973172991196020261297061887)
 (.leaf 30354201441027016733116592294117482916286909961902225937586395913280202204248014847))
 (.branch 3
 (.leaf 190536410541747572716161940294993060653600960856016305594400612572568478526465468720560537081579440047975016408173117092918735429931779489791)
 (.branch 4
 (.leaf 120766797594289323271729746591434068098799731480609931767743909160656967286345916814677982919863608127287981088450691171115688803435873431290639056847823369692507508047873)
 (.leaf 253266210341661448616090500434894569640761184792783193862793300037985610904124513444062935882731041813231138609886597221024849105732369924980022956290169720069347880190431199233))))
 (.branch 7
 (.branch 6
 (.leaf 57586069110962273177536032970868226265173240927204265625541312691136208680238736370761302444634208802636983653414763495544910781357950427332512290107624526861828097)
 (.leaf 253266331108401456781384441703981179287643510109765642329079594131709922419447530409514572225908848188160453841677481319691415887601924005849610758211307928334098546116777738241))
 (.branch 8
 (.leaf 253266331108459042877954568433752961526930597471816892304259207301743008467701555358958665551104700923630187445181461230280107517288256429120706628189927351166328567793945935870)
 (.branch 9
 (.leaf 253266331108459042877954581520922832517588504432764013907994773208136186304488683965650223854404379979224549273615756403844133808245874504434041173802211062136844524235733868542)
 (.leaf 253266331108459042877954581524117942349373333023330651388855060211531301826421493323220216910630771502431481490859026495439242213102065329159459468369010936089718185632756391936)))))
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
 (.leaf (.leaf 0)))))
 (.branch 24
 (.branch 20
 (.branch 18
 (.branch 17
 (.leaf (.leaf 0))
 (.leaf (.leaf 6)))
 (.leaf (.leaf 0)))
 (.branch 22
 (.branch 21
 (.leaf (.leaf 7))
 (.leaf (.leaf 8)))
 (.leaf (.leaf 0))))
 (.branch 28
 (.branch 26
 (.branch 25
 (.leaf (.leaf 9))
 (.leaf (.leaf 0)))
 (.branch 27
 (.leaf (.leaf 0))
 (.leaf (.leaf 10))))
 (.leaf (.leaf 0)))))
 (.branch 48
 (.branch 40
 (.branch 36
 (.branch 34
 (.leaf (.leaf 0))
 (.branch 35
 (.leaf (.leaf 11))
 (.leaf (.leaf 0))))
 (.branch 38
 (.branch 37
 (.leaf (.leaf 12))
 (.leaf (.leaf 0)))
 (.branch 39
 (.leaf (.leaf 13))
 (.leaf (.leaf 0)))))
 (.branch 44
 (.branch 42
 (.branch 41
 (.leaf (.leaf 14))
 (.leaf (.leaf 0)))
 (.branch 43
 (.leaf (.leaf 15))
 (.leaf (.leaf 0))))
 (.branch 46
 (.branch 45
 (.leaf (.leaf 16))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.leaf (.leaf 0))))
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
 (.branch 92
 (.branch 90
 (.branch 89
 (.leaf (.leaf 22))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.leaf (.leaf 0))))
 (.branch 192
 (.branch 160
 (.branch 144
 (.branch 136
 (.branch 132
 (.branch 130
 (.branch 129
 (.leaf (.leaf 0))
 (.leaf (.leaf 23)))
 (.branch 131
 (.leaf (.leaf 24))
 (.leaf (.leaf 25))))
 (.branch 134
 (.branch 133
 (.leaf (.leaf 26))
 (.leaf (.leaf 27)))
 (.branch 135
 (.leaf (.leaf 28))
 (.leaf (.leaf 0)))))
 (.branch 140
 (.branch 138
 (.branch 137
 (.leaf (.leaf 29))
 (.leaf (.leaf 0)))
 (.branch 139
 (.leaf (.leaf 30))
 (.leaf (.leaf 0))))
 (.branch 142
 (.branch 141
 (.leaf (.leaf 31))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 152
 (.branch 148
 (.branch 146
 (.branch 145
 (.leaf (.leaf 32))
 (.leaf (.leaf 33)))
 (.leaf (.leaf 0)))
 (.branch 150
 (.branch 149
 (.leaf (.leaf 34))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 156
 (.branch 154
 (.branch 153
 (.leaf (.leaf 35))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 176
 (.branch 168
 (.branch 164
 (.branch 162
 (.branch 161
 (.leaf (.leaf 36))
 (.leaf (.leaf 0)))
 (.branch 163
 (.leaf (.leaf 37))
 (.leaf (.leaf 0))))
 (.branch 166
 (.branch 165
 (.leaf (.leaf 38))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 172
 (.branch 170
 (.branch 169
 (.leaf (.leaf 39))
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
 (.leaf (.leaf 40))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 198
 (.branch 197
 (.leaf (.leaf 41))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 204
 (.branch 202
 (.branch 201
 (.leaf (.leaf 42))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 216
 (.branch 212
 (.branch 210
 (.branch 209
 (.leaf (.leaf 43))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))))
 (.branch 384
 (.branch 320
 (.branch 288
 (.branch 272
 (.branch 264
 (.branch 260
 (.branch 258
 (.branch 257
 (.leaf (.leaf 0))
 (.leaf (.leaf 44)))
 (.branch 259
 (.leaf (.leaf 45))
 (.leaf (.leaf 46))))
 (.branch 262
 (.branch 261
 (.leaf (.leaf 47))
 (.leaf (.leaf 48)))
 (.branch 263
 (.leaf (.leaf 49))
 (.leaf (.leaf 0)))))
 (.branch 268
 (.branch 266
 (.branch 265
 (.leaf (.leaf 50))
 (.leaf (.leaf 0)))
 (.branch 267
 (.leaf (.leaf 51))
 (.leaf (.leaf 0))))
 (.branch 270
 (.branch 269
 (.leaf (.leaf 52))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 280
 (.branch 276
 (.branch 274
 (.branch 273
 (.leaf (.leaf 53))
 (.leaf (.leaf 54)))
 (.leaf (.leaf 0)))
 (.branch 278
 (.branch 277
 (.leaf (.leaf 55))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 284
 (.branch 282
 (.branch 281
 (.leaf (.leaf 56))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 304
 (.branch 296
 (.branch 292
 (.branch 290
 (.branch 289
 (.leaf (.leaf 57))
 (.leaf (.leaf 0)))
 (.branch 291
 (.leaf (.leaf 58))
 (.leaf (.leaf 0))))
 (.branch 294
 (.branch 293
 (.leaf (.leaf 59))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 300
 (.branch 298
 (.branch 297
 (.leaf (.leaf 60))
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
 (.leaf (.leaf 61))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 326
 (.branch 325
 (.leaf (.leaf 62))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 332
 (.branch 330
 (.branch 329
 (.leaf (.leaf 63))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 344
 (.branch 340
 (.branch 338
 (.branch 337
 (.leaf (.leaf 64))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0))))
 (.branch 448
 (.branch 416
 (.branch 400
 (.branch 392
 (.branch 388
 (.branch 386
 (.branch 385
 (.leaf (.leaf 65))
 (.leaf (.leaf 66)))
 (.branch 387
 (.leaf (.leaf 67))
 (.leaf (.branch 0x1000000000000000000000000000000040000000000000000000000000000000200000000000000000000000000000008 (.leaf 68) (.leaf 69)))))
 (.branch 390
 (.branch 389
 (.leaf (.leaf 70))
 (.leaf (.branch 0x1000000000000000000000000000000100000000000000000000000000000000200000000000000000000000000000020 (.leaf 71) (.leaf 72))))
 (.branch 391
 (.leaf (.branch 0x1000000000000000000000000000000100000000000000000000000000000000400000000000000000000000000000040 (.leaf 73) (.leaf 74)))
 (.leaf (.leaf 0)))))
 (.branch 396
 (.branch 394
 (.branch 393
 (.leaf (.leaf 75))
 (.leaf (.leaf 0)))
 (.branch 395
 (.leaf (.branch 0x1000000000000000000000000000001000000000000000000000000000000000400000000000000000000000000000400 (.leaf 76) (.leaf 77)))
 (.leaf (.leaf 0))))
 (.branch 398
 (.branch 397
 (.leaf (.branch 0x1000000000000000000000000000001000000000000000000000000000000001000000000000000000000000000001000 (.leaf 78) (.leaf 79)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 408
 (.branch 404
 (.branch 402
 (.branch 401
 (.leaf (.leaf 80))
 (.leaf (.branch 0x1000000000000000000000000000100000000000000000000000000000000000200000000000000000000000000020000 (.leaf 81) (.leaf 82))))
 (.leaf (.leaf 0)))
 (.branch 406
 (.branch 405
 (.leaf (.branch 0x1000000000000000000000000000100000000000000000000000000000000001000000000000000000000000000100000 (.leaf 83) (.leaf 84)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 412
 (.branch 410
 (.branch 409
 (.leaf (.branch 0x1000000000000000000000000000100000000000000000000000000000000010000000000000000000000000001000000 (.leaf 85) (.leaf 86)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 432
 (.branch 424
 (.branch 420
 (.branch 418
 (.branch 417
 (.leaf (.leaf 87))
 (.leaf (.leaf 0)))
 (.branch 419
 (.leaf (.branch 0x1000000000000000000000001000000000000000000000000000000000000000400000000000000000000000400000000 (.leaf 88) (.leaf 89)))
 (.leaf (.leaf 0))))
 (.branch 422
 (.branch 421
 (.leaf (.branch 0x1000000000000000000000001000000000000000000000000000000000000001000000000000000000000001000000000 (.leaf 90) (.leaf 91)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 428
 (.branch 426
 (.branch 425
 (.leaf (.branch 0x1000000000000000000000001000000000000000000000000000000000000010000000000000000000000010000000000 (.leaf 92) (.leaf 93)))
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
 (.leaf (.leaf 94))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 454
 (.branch 453
 (.leaf (.branch 0x1000000000000000100000000000000000000000000000000000000000000001000000000000000100000000000000000 (.leaf 95) (.leaf 96)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 460
 (.branch 458
 (.branch 457
 (.leaf (.branch 0x1000000000000000100000000000000000000000000000000000000000000010000000000000001000000000000000000 (.leaf 97) (.leaf 98)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 472
 (.branch 468
 (.branch 466
 (.branch 465
 (.leaf (.branch 0x1000000000000000100000000000000000000000000000000000000000001000000000000000100000000000000000000 (.leaf 99) (.leaf 100)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0))))))
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
 (.leaf (.leaf 101)))
 (.branch 515
 (.leaf (.leaf 102))
 (.leaf (.leaf 103))))
 (.branch 518
 (.branch 517
 (.leaf (.leaf 104))
 (.leaf (.leaf 105)))
 (.branch 519
 (.leaf (.leaf 106))
 (.leaf (.leaf 0)))))
 (.branch 524
 (.branch 522
 (.branch 521
 (.leaf (.leaf 107))
 (.leaf (.leaf 0)))
 (.branch 523
 (.leaf (.leaf 108))
 (.leaf (.leaf 0))))
 (.branch 526
 (.branch 525
 (.leaf (.leaf 109))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 536
 (.branch 532
 (.branch 530
 (.branch 529
 (.leaf (.leaf 110))
 (.leaf (.leaf 111)))
 (.leaf (.leaf 0)))
 (.branch 534
 (.branch 533
 (.leaf (.leaf 112))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 540
 (.branch 538
 (.branch 537
 (.leaf (.leaf 113))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 560
 (.branch 552
 (.branch 548
 (.branch 546
 (.branch 545
 (.leaf (.leaf 114))
 (.leaf (.leaf 0)))
 (.branch 547
 (.leaf (.leaf 115))
 (.leaf (.leaf 0))))
 (.branch 550
 (.branch 549
 (.leaf (.leaf 116))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 556
 (.branch 554
 (.branch 553
 (.leaf (.leaf 117))
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
 (.leaf (.leaf 118))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 582
 (.branch 581
 (.leaf (.leaf 119))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 588
 (.branch 586
 (.branch 585
 (.leaf (.leaf 120))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 600
 (.branch 596
 (.branch 594
 (.branch 593
 (.leaf (.leaf 121))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0))))
 (.branch 704
 (.branch 672
 (.branch 656
 (.branch 648
 (.branch 644
 (.branch 642
 (.branch 641
 (.leaf (.leaf 122))
 (.leaf (.leaf 123)))
 (.branch 643
 (.leaf (.leaf 124))
 (.leaf (.branch 0x10000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000008 (.leaf 125) (.leaf 126)))))
 (.branch 646
 (.branch 645
 (.leaf (.leaf 127))
 (.leaf (.branch 0x10000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000020 (.leaf 128) (.leaf 129))))
 (.branch 647
 (.leaf (.branch 0x10000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000040 (.leaf 130) (.leaf 131)))
 (.leaf (.leaf 0)))))
 (.branch 652
 (.branch 650
 (.branch 649
 (.leaf (.leaf 132))
 (.leaf (.leaf 0)))
 (.branch 651
 (.leaf (.branch 0x10000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000400 (.leaf 133) (.leaf 134)))
 (.leaf (.leaf 0))))
 (.branch 654
 (.branch 653
 (.leaf (.branch 0x10000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000001000 (.leaf 135) (.leaf 136)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 664
 (.branch 660
 (.branch 658
 (.branch 657
 (.leaf (.leaf 137))
 (.leaf (.branch 0x10000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000020000 (.leaf 138) (.leaf 139))))
 (.leaf (.leaf 0)))
 (.branch 662
 (.branch 661
 (.leaf (.branch 0x10000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000100000 (.leaf 140) (.leaf 141)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 668
 (.branch 666
 (.branch 665
 (.leaf (.branch 0x10000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000001000000 (.leaf 142) (.leaf 143)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 688
 (.branch 680
 (.branch 676
 (.branch 674
 (.branch 673
 (.leaf (.leaf 144))
 (.leaf (.leaf 0)))
 (.branch 675
 (.leaf (.branch 0x10000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000400000000 (.leaf 145) (.leaf 146)))
 (.leaf (.leaf 0))))
 (.branch 678
 (.branch 677
 (.leaf (.branch 0x10000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000001000000000 (.leaf 147) (.leaf 148)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 684
 (.branch 682
 (.branch 681
 (.leaf (.branch 0x10000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000010000000000 (.leaf 149) (.leaf 150)))
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
 (.leaf (.leaf 151))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 710
 (.branch 709
 (.leaf (.branch 0x10000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000100000000000000000 (.leaf 152) (.leaf 153)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 716
 (.branch 714
 (.branch 713
 (.leaf (.branch 0x10000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000001000000000000000000 (.leaf 154) (.leaf 155)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 728
 (.branch 724
 (.branch 722
 (.branch 721
 (.leaf (.branch 0x10000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000100000000000000000000 (.leaf 156) (.leaf 157)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))))
 (.branch 896
 (.branch 832
 (.branch 800
 (.branch 784
 (.branch 776
 (.branch 772
 (.branch 770
 (.branch 769
 (.leaf (.leaf 158))
 (.leaf (.leaf 159)))
 (.branch 771
 (.leaf (.leaf 160))
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000008 (.leaf 161) (.leaf 162)))))
 (.branch 774
 (.branch 773
 (.leaf (.leaf 163))
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000020 (.leaf 164) (.leaf 165))))
 (.branch 775
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000040 (.leaf 166) (.leaf 167)))
 (.leaf (.leaf 0)))))
 (.branch 780
 (.branch 778
 (.branch 777
 (.leaf (.leaf 168))
 (.leaf (.leaf 0)))
 (.branch 779
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000400 (.leaf 169) (.leaf 170)))
 (.leaf (.leaf 0))))
 (.branch 782
 (.branch 781
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000001000 (.leaf 171) (.leaf 172)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 792
 (.branch 788
 (.branch 786
 (.branch 785
 (.leaf (.leaf 173))
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000020000 (.leaf 174) (.leaf 175))))
 (.leaf (.leaf 0)))
 (.branch 790
 (.branch 789
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000100000 (.leaf 176) (.leaf 177)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 796
 (.branch 794
 (.branch 793
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000001000000 (.leaf 178) (.leaf 179)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 816
 (.branch 808
 (.branch 804
 (.branch 802
 (.branch 801
 (.leaf (.leaf 180))
 (.leaf (.leaf 0)))
 (.branch 803
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000400000000 (.leaf 181) (.leaf 182)))
 (.leaf (.leaf 0))))
 (.branch 806
 (.branch 805
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000001000000000 (.leaf 183) (.leaf 184)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 812
 (.branch 810
 (.branch 809
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000010000000000 (.leaf 185) (.leaf 186)))
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
 (.leaf (.leaf 187))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 838
 (.branch 837
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000100000000000000000 (.leaf 188) (.leaf 189)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 844
 (.branch 842
 (.branch 841
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000001000000000000000000 (.leaf 190) (.leaf 191)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 856
 (.branch 852
 (.branch 850
 (.branch 849
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000100000000000000000000 (.leaf 192) (.leaf 193)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0))))
 (.branch 960
 (.branch 928
 (.branch 912
 (.branch 904
 (.branch 900
 (.branch 898
 (.branch 897
 (.leaf (.leaf 194))
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000 (.leaf 195) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000200000000000000000000000000000000 (.leaf 196) (.leaf 197)))))
 (.branch 899
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000 (.leaf 198) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000400000000000000000000000000000000 (.leaf 199) (.leaf 200))))
 (.leaf (.leaf 0))))
 (.branch 902
 (.branch 901
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000 (.leaf 201) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000000 (.leaf 202) (.leaf 203))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 908
 (.branch 906
 (.branch 905
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000 (.leaf 204) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000000000000000000 (.leaf 205) (.leaf 206))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 920
 (.branch 916
 (.branch 914
 (.branch 913
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000 (.leaf 207) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000000000 (.leaf 208) (.leaf 209))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 944
 (.branch 936
 (.branch 932
 (.branch 930
 (.branch 929
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000 (.leaf 210) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000000000000000000000000 (.leaf 211) (.leaf 212))))
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
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000 (.leaf 213) (.branch 0x1000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000000000000000000000 (.leaf 214) (.leaf 215))))
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
def candidateMasks (i : Nat) := PackedRawNatGrowth.take 586
  (PackedRawNatGrowth.drop (586*(i%64)) (candidateMasksBlocks.get (i/64)))

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
 (.branch 7
 (.branch 6
 (.leaf badMasksBlock0005)
 (.leaf badMasksBlock0006))
 (.branch 8
 (.leaf badMasksBlock0007)
 (.branch 9
 (.leaf badMasksBlock0008)
 (.leaf badMasksBlock0009)))))
def badMasks (i : Nat) := PackedRawNatGrowth.take 586
  (PackedRawNatGrowth.drop (586*(i%64)) (badMasksBlocks.get (i/64)))

def signatureMasksBlocks : Table Nat :=
(.branch 2
 (.branch 1
 (.leaf signatureMasksBlock0000)
 (.leaf signatureMasksBlock0001))
 (.branch 3
 (.leaf signatureMasksBlock0002)
 (.leaf signatureMasksBlock0003)))
def signatureMasks (i : Nat) := PackedRawNatGrowth.take 586
  (PackedRawNatGrowth.drop (586*(i%64)) (signatureMasksBlocks.get (i/64)))

def fastKind := rawKind
def candidateSupports := candidateRows
def kindSupports := kindRows
def wellFormedTest (i : Nat) : Bool := RawFacetEmbedding.wellFormedCheck (rawCells i)

def cellTest (i : Nat) := (listBounds 1024 (rawCells i).ridgeMasks && ((rawCells i).ridgeMasks.all (fun q => (candidateMasks q).testBit i) && (decide (rawKind i = (rawCells i).kind) && (decide ((rawCells i).vertices < 1024) && ((List.range 10).all (fun v => decide ((vertexMasks v).testBit i = (rawCells i).vertices.testBit v)) && (SignatureCompatibility.faces (rawCells i)).all (fun q => (SignatureCompatibility.profileMask (SignatureCompatibility.allMask 586) signatureIndex signatureMasks (rawCells i) q).testBit i))))))
def ridgeTest (i : Nat) := decide (candidateMasks i = RawNatGrowthCheck.mask (candidateRows i)) &&
  (candidateRows i).all (fun c => hasNat (rawCells c).ridgeMasks i)
def kindTest (i : Nat) := decide (kindMasks i = RawNatGrowthCheck.mask (kindRows i)) &&
  (kindRows i).all (fun c => decide ((rawCells c).kind = i))
def badTest (i : Nat) := if badMasks i = 0 then true else
  decide (Nat.land (badMasks i) (SignatureCompatibility.cover (SignatureCompatibility.allMask 586)
    vertexMasks signatureIndex signatureMasks (rawCells i)) = 0)

end Papers.RationalityTen.RootedCaches.RootedSevenPure019

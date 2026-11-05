module
prelude
public import RootedSevenPure017
public import SignatureCompatibility
public import PackedRawNatGrowth
public import FiniteChecks
public import RawFacetEmbedding
public import RootedSevenPure017GrowthCachecandidateMasksData000
public import RootedSevenPure017GrowthCachebadMasksData000
public import RootedSevenPure017GrowthCachesignatureMasksData000

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure017
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def rawCells := Papers.RationalityTen.FacetUniverses.RootedSevenPure017.rawCells
def cells (c : Fin 586) := rawCells c.val
def ridgeList := ConcreteGrowth.ridgeList cells
def literalCompatible (a b : Fin 586) := ConcreteGrowth.compatible (cells a) (cells b)
def kind (c : Fin 586) := (cells c).kind
def rawKindCode : Nat := 6962345837212099168588236730831349673176561799330348054689740920659981192319054254396073125020595092890205482978977313264059095072837977149797067777939552794285816294312144582297565278583760340630790085679486106013357214258717366462192395595799577219400393779979130237566868293976948569595414156338669733814218279529013752652155473971948568737083647615534161453617381207254624879235445072847069929412961577730337176651255954958974099170690814318419725923374986872108072831225582945045790791174361634421402047181011771306128516240
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
 (.leaf 0x0)
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
 (.branch 37
 (.leaf 0x0)
 (.leaf 0x6017c5e1745c16c5a1645815c561545414c521445013c4e1344c12c4a1244811c461144410c42104400fc3e0f4000025))
 (.branch 39
 (.leaf 0xe7398e5390e3388e1380df378dd370db368d9360d7358d5350d3348d1340cf338cd330cb328c9320c7318c5310000025)
 (.leaf 0x0))))
 (.branch 44
 (.branch 42
 (.leaf 0x0)
 (.branch 43
 (.leaf 0x12047d1e4751c46d1a4651845d164551444d124451043d0e4350c42d0a4250841d064150440d02405003fcfe3f4000025)
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 56
 (.branch 52
 (.branch 50
 (.branch 49
 (.leaf 0x0)
 (.leaf 0x99260972589525093248912408f2388d2308b22889220872188521083208812007f1f87d1f07b1e8791e0771d8000025))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 96
 (.branch 80
 (.leaf 0x0)
 (.branch 88
 (.leaf 0x0)
 (.branch 92
 (.branch 90
 (.branch 89
 (.leaf 0x183609816017f5f97d5f17b5e9795e1775d9755d1735c9715c16f5b96d5b16b5a9695a167599655916358961580000025)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 112
 (.branch 104
 (.leaf 0x0)
 (.branch 108
 (.branch 106
 (.branch 105
 (.leaf 0x1bc6edba6e5b86ddb66d5b46cdb26c5b06bdae6b5ac6adaa6a5a869da6695a468da2685a067d9e6759c66d9a664000025)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 120
 (.branch 116
 (.branch 114
 (.branch 113
 (.leaf 0x20a8260881e068160480e02806007fdfe7f5fc7edfa7e5f87ddf67d5f47cdf27c5f07bdee7b5ec7adea7a5e879c000025)
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
 (.leaf 0x380dc350d0320c42f0b82d0b02a0a42505814044100380a02005010020017)))
 (.branch 134
 (.branch 133
 (.leaf 0x0)
 (.leaf 0x1c4701b86d1ac6a1a0671986518c62148501344c12846110411003e060130480f0380c01c0600c020020))
 (.branch 135
 (.leaf 0x3e0f73d4f43c8f13bcee3b4ec3a8e9364d7350d3344cd32cc831cc505c15048100340b02406010010020)
 (.leaf 0x0))))
 (.branch 140
 (.branch 138
 (.leaf 0x0)
 (.branch 139
 (.leaf 0x1314c12e4b52b4a92849d2649523489124410d4310a41904405003f8250017)
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 152
 (.branch 148
 (.branch 146
 (.branch 145
 (.leaf 0x0)
 (.leaf 0xaa2a4a7298a428ca12809f2789c26c8b22486214831fc7d1e8791dc250017))
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 156
 (.branch 154
 (.branch 153
 (.leaf 0x19464d916418e6358b6298962186615755cd705bd6d5a56759163584250017)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 176
 (.branch 168
 (.branch 164
 (.branch 162
 (.branch 161
 (.leaf 0x0)
 (.leaf 0x2fcbe2f0bb2e4b82d8b52d0b32c4b02348821c8420c811f07b1e0771504f1384b1284810c420fc3e0020))
 (.branch 163
 (.leaf 0x5194550d425013f4f53c4ed3a4e1374510f4390b4290840d023fcfe36cd6354d2344cf328c9318c50020)
 (.leaf 0x0)))
 (.branch 166
 (.branch 165
 (.leaf 0x56d5a5615755554549515414f5354c368d8354d3340ce330c931cc414c511384c12447114421003d0020)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 172
 (.branch 170
 (.branch 169
 (.leaf 0x735cc729c971dc6711c3709c16fdbe6b9ac6a5a8699a26819d6719a44d114390c4250741502400fd0020)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 184
 (.branch 180
 (.branch 178
 (.branch 177
 (.leaf 0x86e1a862178561484a118420f8360c7f1fa7ddf67d1f07b9eb7a9e82308a21c85208801f87b1e4760020)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 224
 (.branch 208
 (.branch 200
 (.leaf 0x0)
 (.branch 204
 (.branch 202
 (.branch 201
 (.leaf 0x789e177dde771db765d875dd6751d36c1ab6a9a7699a467d9e66d9a5dd725c56e5b56b59965589610020)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 216
 (.branch 212
 (.branch 210
 (.branch 209
 (.leaf 0x8c22f8b62c8aa2989e268962488a217f9f97e1f57d1f27b5ec7a5e85d9745c56f5b16a5a16558d600020)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 240
 (.branch 232
 (.branch 228
 (.branch 226
 (.branch 225
 (.leaf 0x9164490a418fe3e8f23b8ea398de367f5fb7e1f67cdf17bdec7a9e76bdad6a9a8695a36859e671990020)
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
 (.leaf 0x3a0e4360d4330c8300b82d0ac2a0a026088200741c0680901c0600c010017)))
 (.branch 262
 (.branch 261
 (.leaf 0x0)
 (.leaf 0x1cc721bc6e1b06b1a4671986418c611785c164581584510c420fc3d0901f0781b0680b02005010010020))
 (.branch 263
 (.leaf 0x3e8f93d8f53ccf23c0ee3b4eb3a8e8394e3380df374cc328c9318c408c210781c0640c0280500c020020)
 (.leaf 0x0))))
 (.branch 268
 (.branch 266
 (.leaf 0x0)
 (.branch 267
 (.leaf 0x1334c92f4b92c4ad2949d26491234851e471194611641503408ff3f4260017)
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 280
 (.branch 276
 (.branch 274
 (.branch 273
 (.leaf 0x0)
 (.leaf 0xac2aca829ca5290a22809f2749c26897254922448f1f87c1ec781d8260017))
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 284
 (.branch 282
 (.branch 281
 (.leaf 0x196655926458f6398c6298961d86611815fd7c5ed795a16659562580260017)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 304
 (.branch 296
 (.branch 292
 (.branch 290
 (.branch 289
 (.leaf 0x0)
 (.leaf 0x304c02f4bc2e8b92dcb52d0b22c4af2649424c9023c801f47a1e4761805b1685715847110411003d0020))
 (.branch 291
 (.leaf 0x5214751143505404f93c4ed394e1364811b469174590741101400fd39ce2384de374ce32cc831cc40020)
 (.leaf 0x0)))
 (.branch 294
 (.branch 293
 (.leaf 0x5755c565585595554d515414e5354b398e4384df370cf334c8318c517c5d1685815448118410fc3e0020)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 300
 (.branch 298
 (.branch 297
 (.leaf 0x73dce72dca721c7715c3709c06fdbd6e9b86d5b46c9a167d9e66d9947d1d4691845508419013fcfe0020)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 312
 (.branch 308
 (.branch 306
 (.branch 305
 (.leaf 0x8761c8661885a1584e118420e8360b8220680e02801ef7b5ec7a5e72609624c91238811fc7a1e0770020)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 352
 (.branch 336
 (.branch 328
 (.leaf 0x0)
 (.branch 332
 (.branch 330
 (.branch 329
 (.leaf 0x791e3781df775dc769d875dd5751d26f1b76d9b36c9a36819d6719960d7e5f57a5e56a59d6458d600020)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 344
 (.branch 340
 (.branch 338
 (.branch 337
 (.leaf 0x8ca318ba2d8ae2a8a2268962388a2082a0581201801f17b9eb7a9e7609805f57b5e16b5a564589610020)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 368
 (.branch 360
 (.branch 356
 (.branch 354
 (.branch 353
 (.leaf 0x91e4690e429023f8f63b8ea388de3582607812027fdf27c1eb7a5e86edb96d9b46c5a46899d66d9a0020)
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
 (.leaf 0x304bf2e8b82dcb62ccb22c4ac2a8a528ca22849e2749c1f47c1ec7a1e4781cc711b06a1a4681946418c4410c42104400fc3a0e0330c4300bc2c0ac2a0200701805010030036))
 (.branch 387
 (.leaf 0x521465053f4f93d4e9394e1334c52c4a9294a125491234110340901400ff3e8f83ccf13c0ef3b0eb3a8cb328c9320c7318390dc360d0300bc2d0a4280280901805008010036)
 (.leaf 0xf03b0300b0004)))
 (.branch 390
 (.branch 389
 (.leaf 0x15d56d56551535494f5394d3e4f73d8f43c0ef3b4e93a0cd330c9320c5310721c06f1b4691a0661886111845108410f83d0300b0100300801002d)
 (.leaf 0x1d47412047028090006))
 (.branch 391
 (.leaf 0x3f0fb33cce020070006)
 (.leaf 0x0))))
 (.branch 396
 (.branch 394
 (.branch 393
 (.leaf 0x791e2775db769d9759d5751cf735c8719c5711c1701bf6819f6799d6719b6599463d8d6318b62187619675996559163589324c12f4b5294a1264892141905409013f8fd0036)
 (.leaf 0x0))
 (.branch 395
 (.leaf 0x4d534421070004)
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 408
 (.branch 404
 (.branch 402
 (.branch 401
 (.leaf 0x8ca308ae298a2278922388a1d86e168521384a0f83a0d7b9ed7b1eb7a9e965593649906318b62585611695a16559161580ab2a4a8298a22849f26c9a1fc7e1ec7a1dc760036)
 (.leaf 0x2b8ad204800004))
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 412
 (.branch 410
 (.branch 409
 (.leaf 0x661975ad6a0004)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 432
 (.branch 424
 (.branch 420
 (.branch 418
 (.branch 417
 (.leaf 0x91e459023e8f63c8e6388de1c86a1985e1384a108320b7c1ef7b1eb7a1e7739cc72dc9715c4709be6f5a26859e6759a6655c5695955d53549505314b51d45511424f93d4ed374d90841d003fcfe3f4cf338c7318c5310c02f8bd2ecb72d8b42c0af204801e4781dc76120471003f0f83d005a)
 (.leaf 0x30cc21fc7e118450006))
 (.branch 419
 (.leaf 0x5294941905334cc0006)
 (.leaf 0x0)))
 (.branch 422
 (.branch 421
 (.leaf 0x57d5e32cca110430006)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 428
 (.branch 426
 (.branch 425
 (.leaf 0x745d0691a3411030006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 440
 (.branch 436
 (.branch 434
 (.branch 433
 (.leaf 0x87e1e7c9f11f47c0006)
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
 (.leaf 0x246912439063d8f23a8da358c62f8ba2c8a22789621881f27c5ea7a5e879de3785e0779da765d774dd2691a36719b669995ad6a58d6258560002d)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 460
 (.branch 458
 (.branch 457
 (.leaf 0x799e5689a15a5680006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 472
 (.branch 468
 (.branch 466
 (.branch 465
 (.leaf 0x8d2337c1ef59d660006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 496
 (.branch 488
 (.branch 484
 (.branch 482
 (.branch 481
 (.leaf 0x926487b9ed6819f0006)
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
 (.leaf 0x3c0ec360d0330c4300bc2c0ac290a0270841f0781b0641504c1203c0d0017)))
 (.branch 518
 (.branch 517
 (.leaf 0x0)
 (.leaf 0x1d4741bc6d1b06a1a46819464188611745b168571545113c4e12c4908c200741c06417050110400d0020))
 (.branch 519
 (.leaf 0x3f0fb3d8f43ccf13c0ef3b0eb3a4e8390e2384de370d8358d5348d0090220741b068180581103c0e0020)
 (.leaf 0x0))))
 (.branch 524
 (.branch 522
 (.leaf 0x0)
 (.branch 523
 (.leaf 0x1354d12f4b52c4a9294a125491224851d46d1a45d154450f4390b424270017)
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 536
 (.branch 532
 (.branch 530
 (.branch 529
 (.leaf 0x0)
 (.leaf 0xae2b4a8298a528ca22849e2749b26896250932408e2288821c84208270017))
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 540
 (.branch 538
 (.branch 537
 (.leaf 0x19865d926418f6358c62d8861d85611805f97d5e9785d1725c56e5b0270017)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 560
 (.branch 552
 (.branch 548
 (.branch 546
 (.branch 545
 (.leaf 0x0)
 (.leaf 0x30cc22f4bb2e8b82dcb62ccb22c0af26095248912388c224862148217c5c16458154531404d130490020))
 (.branch 547
 (.leaf 0x52949511425053f4f93d4e9394dd3647d1c46518455134410d43109398e3380df370da35cd434cd00020)
 (.leaf 0x0)))
 (.branch 550
 (.branch 549
 (.leaf 0x57d5e565575595454d5253d4e5314b39ce5380de374db364d4348d11805e16457158541484d12c4a0020)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 556
 (.branch 554
 (.branch 553
 (.leaf 0x745d072dc9721c6715c4705c06f9bd6e5b76d9b36c5ad6adaa69da54811e46517459144490d42d0a0020)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 568
 (.branch 564
 (.branch 562
 (.branch 561
 (.leaf 0x87e1e8661785a1484e1283e0e8320b81e05812017fdfb7e5f87d5f3264972489023c8d22c86210830020)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 608
 (.branch 592
 (.branch 584
 (.leaf 0x0)
 (.branch 588
 (.branch 586
 (.branch 585
 (.leaf 0x799e5781de775db769d9759d574dd26edb86d5b46c5af6b1a96a1a56097f5f17b5e1765cd705bd6c0020)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 600
 (.branch 596
 (.branch 594
 (.branch 593
 (.leaf 0x8d2338ba2c8ae298a22789223886208260680e027fdfd7e9f77d9f360d815f17a5e5775d5705b96d0020)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 624
 (.branch 616
 (.branch 612
 (.branch 610
 (.branch 609
 (.leaf 0x9264890e419023e8f63c8e6388da3582a0880e01801fe7f1f77d5f46f1ba6d5b36c9b06b9a969da60020)
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
 (.leaf 0x30cbe2e8b92dcb52d0b22c0ae2a4a5290a22809f2749b2248821c86214841d4701b06b1a467198641885013c4e1344c12c3c0dc330c8300b82d0ac2905013048110400f0036))
 (.branch 643
 (.leaf 0x52945505404f93c4ed394dd354c12c4ad2949d26491224410f4390d4310b3f0f73ccf23c0ee3b4eb3a4d7358d5350d33483b0e0360d4300b82c0a82805815048110380d0036)
 (.leaf 0xe839060170004)))
 (.branch 646
 (.branch 645
 (.leaf 0x15f5695655553545505394c3ecf83d8f53c0ee3b0ea3a0d9360d5350d1340741c46f1b86919c6518c61148511384d12849060170400f0380d002d)
 (.leaf 0x1cc7215053058150006))
 (.branch 647
 (.leaf 0x3e8f936cda050130006)
 (.leaf 0x0))))
 (.branch 652
 (.branch 650
 (.branch 649
 (.leaf 0x799e1775dc769d875dd574dd1731c871dc570dc2701be6b1ab6a9a96a1a76619363d8e6318a62587615735c9715c16f5b9344c52f4b92949d2548d21449114390d429090036)
 (.leaf 0x0))
 (.branch 651
 (.leaf 0x4cd32451130004)
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 664
 (.branch 660
 (.branch 658
 (.branch 657
 (.leaf 0x8d22f8ae2a8a226896238861f86a16856138461083a0c7e9f97e1f77d9f565d94649916318a62186611755d1715c16d5b0ad2a8a829ca22809e2709a22c8a21c8620c820036)
 (.leaf 0x2b0ab2348c0004))
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 668
 (.branch 666
 (.branch 665
 (.leaf 0x659955dd760004)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 688
 (.branch 680
 (.branch 676
 (.branch 674
 (.branch 673
 (.leaf 0x926449023f8f63b8ea388da1e86e19862138460f8360b7f1fb7e1f77d1f3741cd72dca715c3705bf6f5ae6b5aa6a5a66955e56d59561535454f5354b52546511434f93c4e9384d91444d0c42d0a424db368d3348d1340c22fcbd2f0b72d4b32c4af2348c2148420c82150531304b12849005a)
 (.leaf 0x304c022c8a148510006))
 (.branch 675
 (.leaf 0x5214744911364d80006)
 (.leaf 0x0)))
 (.branch 678
 (.branch 677
 (.leaf 0x5755c35cd61404f0006)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 684
 (.branch 682
 (.branch 681
 (.leaf 0x73dce6c1af4410f0006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 696
 (.branch 692
 (.branch 690
 (.branch 689
 (.leaf 0x8761c7f9fd224880006)
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
 (.leaf 0x2489164390a3d8ee398de358ce308ba2d8a22689222881fe7f5f67d5f47cde5789e077dda761d6751d26c1af6a1a7699a55dd765bd6e5b56c002d)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 716
 (.branch 714
 (.branch 713
 (.leaf 0x791e36b9ad5d5740006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 728
 (.branch 724
 (.branch 722
 (.branch 721
 (.leaf 0x8ca317f1fb5cd720006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 752
 (.branch 744
 (.branch 740
 (.branch 738
 (.branch 737
 (.leaf 0x91e467e9f96b1ab0006)
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
 (.leaf 0x308c02e4b82d8b52d0b32bcad2aca428ca12809f2789a2549424c92244901d0721ac6a1a067198651845c16c5a1645815c3b0e4320c42f0b82d0b0280801f0781d0701b0036))
 (.branch 771
 (.leaf 0x525475013f4f53c4ed3a4d9344c92b4a92849d26495214711b46919461173ecf93c8f13bcee3b4ec3a0e3388e1380df3783c0e8350d02f0b82b0a829088210781d068190036)
 (.leaf 0xe037090230004)))
 (.branch 774
 (.branch 773
 (.leaf 0x15e57155551525455053d4b3f0fa3d4f43bcee3acea3a4e5390e1380dd370751cc6e1b46819c6418c621785d1685915855090230701b06819002d)
 (.leaf 0x1c4701805f088210006))
 (.branch 775
 (.leaf 0x3e0f739ce60801f0006)
 (.leaf 0x0))))
 (.branch 780
 (.branch 778
 (.branch 777
 (.leaf 0x795e3771db765d875dd6749d0739c7719c470dc2705bd6e1b76d9b56d1b365d956398d62d8a625886117f5f97d5f17b5e9354cd2e4b52849d2448d224791d46919459150036)
 (.leaf 0x0))
 (.branch 779
 (.leaf 0x4c5304811f0004)
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 792
 (.branch 788
 (.branch 786
 (.branch 785
 (.leaf 0x8ce318aa2989e26896248821e87215852128461083e0b81a058120380a01661966459062d8a61d86615816017d5f1795e0ae2b0a7298a12809d2709b25c9624c9223c8e0036)
 (.leaf 0x2a8a9264980004))
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 796
 (.branch 794
 (.branch 793
 (.leaf 0x6519360d820004)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 816
 (.branch 808
 (.branch 804
 (.branch 802
 (.branch 801
 (.leaf 0x922468fe3e8f23b8ea398d61f8761885e128460e8360c8220781203801ff745cf729c9711c3701bf6f9ba6e5b66d5b26c55f5755855d525454e5354c5294850d424f53c4e5384dd2047d1845d16454e7398df378dd370c3304bc2ecb62d4b22c4b0264982449023c8e1805f1605715855005a)
 (.leaf 0x2fcbe25c961785d0006))
 (.branch 803
 (.leaf 0x519454791d394e40006)
 (.leaf 0x0)))
 (.branch 806
 (.branch 805
 (.leaf 0x56d5a38ce21705b0006)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 812
 (.branch 810
 (.branch 809
 (.leaf 0x735cc6f1bb4711b0006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 824
 (.branch 820
 (.branch 818
 (.branch 817
 (.leaf 0x86e1a82a09254940006)
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
 (.leaf 0x24991e429063c8ee388de368d2328b62c89e2688e228860a82602806007fde6791df779d9761d5751d36f1bb6d1b36c9b160d825ed7a5e578002d)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 844
 (.branch 842
 (.branch 841
 (.leaf 0x789e16e9b9605800006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 856
 (.branch 852
 (.branch 850
 (.branch 849
 (.leaf 0x8c22f822075fd7e0006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 880
 (.branch 872
 (.branch 868
 (.branch 866
 (.branch 865
 (.leaf 0x9164481a056e1b70006)
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
 (.leaf 0x9264891e46916448ea398e2378da358d2338ca318c22f8962488e228862087e1e8761c86e1a8420f83a0d8320b799e5791e3789e175dd6755d474dd2745d073dce735cc709c1701bf6f9bd6619765995651936258861d866158457d5e5755c56d5a5414f5394d5314b5294952147519454ed3a4e5384dd364d5344cd324c5304992549123489213f0fb3e8f93e0f73b4ec3acea3a4e830cc2304c02fcbe2d0b32c8b12c0af2b8ad2b0ab2a8a927c9e2749c26c9a1d4741cc721c4701986519063188610f03b0e8390e0370b42c0ac2a0a42800a8)
 (.leaf 0x2f4bc2eca829ca61bc6e1b4360d434000c))
 (.branch 899
 (.leaf 0x511435092f4b92d3d8f53d0330c831000c)
 (.leaf 0x0)))
 (.branch 902
 (.branch 901
 (.leaf 0x159561573ccf23c46c1ac6a0009)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 908
 (.branch 906
 (.branch 905
 (.leaf 0x781df779cb729c9649916412c4ad2a000c)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 920
 (.branch 916
 (.branch 914
 (.branch 913
 (.leaf 0x8ba2d8b2198621763d8e634a5290a3000c)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 944
 (.branch 936
 (.branch 932
 (.branch 930
 (.branch 929
 (.leaf 0x90e429061685614721c77195655554505404fcba2e4b80012)
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
 (.leaf 0x2408fe3e8ae2a8a5dd771db0009)
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
 (.leaf 0x8f63c8ee3a8e6388de368d62889e268962488e228862084e128461083e0e8360c82e0480e02806007fdf87ddf67d5f47cdec7adea7a5e879dda765d875dd6755d474dd2715c470dc2705c06fdbe6f5b66d5b46cdb26c5aa6a5a869da66959e6759c66d9a6658c62d8a6258861d86615845f57c5ed7a5e5785c5705bd6e5b56c5956458d625856054d525455053d4e5354c52d3e4f53c4ed3a4e5384dd364a52849d264952448d224851a4651845d164550e4350c42d0a42502405003fcfe3f4f03bcee3b4ec3acea3a4e8384e037cde374dc354d434cd2344d0324c831cc6314c42dcb62d4b42ccb22c4b02bca2284a027c9e2749c26c9a24c922449023c8e21c862148420c821ec7a1e4781dc761a46819c661946418c621845a1645815c561544e1344c12c4a12442104400fc3e0f4300bc2e0b42c0ac2a0a4280781d0701b06819048110400f0380d018050100300801010e)
 (.branch 4
 (.leaf 0x2499224791a459124390a419023f8fa348ce328c6308be2e8b62c8ae2a8a61f87a1d8721b86a198621785a158520a8260881e06815fe7f5fc7edfa7e5f27c5f07bdee7b5e6795e478de2785e077dde775dc76dd1741cf739cd731cb729c9721c7719bc6edba6e5b86ddb06bdae6b5ac6ada468da2685a067d9865d966559464d926459063d8e63583609816017f5f9775d9755d1735c96b5a9695a1675995f5795d5715b5695956157559555514a5254851d465154450d42505404fd354d1334c9314c12f4b92d4b12b4a92047d1e4751c46d1444d124451043d0841d064150440cfc3ecfa3e4f83dcf63d4f43ccf23c4e7398e5390e3388db368d9360d7358cf338cd330cb328c3308c1300bf2f8bd2f0bb2e8b92e0ae2b4ac2acaa2a4a829ca6294a428c9926097258952508d2308b22889220812007f1f87d1f0751d0731c8711c06f1b86d1b06b1a86017c5e1745c16c5414c521445013c4811c461144410c3c0ec3a0e4380dc360d4340cc320c4270982509023088210801f0601705815050130300b0280902007013b)
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
 (.leaf 0x3fe001ff000ff81f81f81f8007fc003fe07e07e07e001ff03f03f03f000ff8007fc003fe07e07e07e001ff03f03f03f000ff8007fc0fc0fc0fc003fe07e07e07e001ff007e07e07e)
 (.branch 4
 (.leaf 0x3ffc01ffe00fff007e07e07e07ff803ffc01f81f81f81ffe00fc0fc0fc0fff007ff803ffc01f81f81f81ffe00fc0fc0fc0fff007ff803f03f03f03ffc01f81f81f81ffe00ff81f81f80)
 (.leaf 0x0))))
def kindMasks := kindMaskTable.get
def keys := List.range 5
def vertexMaskTable : Table Nat :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf 100433627766186892221372630771322662657637687111424552206335)
 (.leaf 4374501449566023848745004454235242730706238428158658685959319840189134675736094211065757938707595263))
 (.branch 3
 (.leaf 9173990089458836480419434836218367539098193774661775453885381602266765134066822187604488196412606584455167)
 (.branch 4
 (.leaf 399583814440447005616844445413525287135811388266652349109850487314980112086044043382121317037962530981030538484695430725201006838195247121189306369)
 (.leaf 120766797594289323271729347007810164062335862210202792120331962976027548232346709327878748942822726306710650235678938045233103236472123232111072268338261298240599986536449))))
 (.branch 7
 (.branch 6
 (.leaf 253266210341719034685201462707672522240364336242086129817657603360788891681948559396037699420350849629035875849924712261593025357667466901175858020230361284530876227732742602753)
 (.leaf 253266331108401456808843619250941186372467404421265927730552117328881151056145204086080828893617921108239642028216394828826653457381257452734766914039621888659949871739407695873))
 (.branch 8
 (.leaf 253266331108459042850502094787561255034596594463155274728091137854430104933776053307028490622347758991654445980897798397827987169524240831014685339430013595830892997021314056190)
 (.branch 9
 (.leaf 253266331108459042877947879256849055245495649451560727380266216550556275927649346684875826839040913928948188008609827775222929677301596180313409820948509911317670833910838206462)
 (.leaf 253266331108459042877954579887823002462344013478657506055230126481878572356114647781891902848859442531227800738597062157395145239437284011209234704855130637957193973306016915456)))))
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
 (.branch 34
 (.branch 33
 (.leaf (.leaf 0))
 (.leaf (.leaf 8)))
 (.branch 35
 (.leaf (.leaf 9))
 (.leaf (.leaf 0))))
 (.branch 38
 (.branch 37
 (.leaf (.leaf 10))
 (.leaf (.leaf 11)))
 (.branch 39
 (.leaf (.leaf 12))
 (.leaf (.leaf 0)))))
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
 (.leaf (.leaf 16)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 96
 (.branch 80
 (.branch 72
 (.leaf (.leaf 0))
 (.branch 76
 (.branch 74
 (.branch 73
 (.leaf (.leaf 17))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 88
 (.branch 84
 (.branch 82
 (.branch 81
 (.leaf (.leaf 18))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 92
 (.branch 90
 (.branch 89
 (.leaf (.leaf 19))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 112
 (.branch 104
 (.branch 100
 (.branch 98
 (.branch 97
 (.leaf (.leaf 20))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 108
 (.branch 106
 (.branch 105
 (.leaf (.leaf 21))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 120
 (.branch 116
 (.branch 114
 (.branch 113
 (.leaf (.leaf 22))
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
 (.leaf (.leaf 0))))
 (.branch 152
 (.branch 148
 (.branch 146
 (.branch 145
 (.leaf (.leaf 31))
 (.leaf (.leaf 32)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
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
 (.leaf (.leaf 35)))
 (.branch 163
 (.leaf (.leaf 36))
 (.leaf (.leaf 0))))
 (.branch 166
 (.branch 165
 (.leaf (.leaf 37))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 172
 (.branch 170
 (.branch 169
 (.leaf (.leaf 38))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 184
 (.branch 180
 (.branch 178
 (.branch 177
 (.leaf (.leaf 39))
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
 (.leaf (.leaf 40))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 204
 (.branch 202
 (.branch 201
 (.leaf (.leaf 41))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 216
 (.branch 212
 (.branch 210
 (.branch 209
 (.leaf (.leaf 42))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 240
 (.branch 232
 (.branch 228
 (.branch 226
 (.branch 225
 (.leaf (.leaf 43))
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
 (.leaf (.leaf 0))))
 (.branch 280
 (.branch 276
 (.branch 274
 (.branch 273
 (.leaf (.leaf 52))
 (.leaf (.leaf 53)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 284
 (.branch 282
 (.branch 281
 (.leaf (.leaf 54))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 304
 (.branch 296
 (.branch 292
 (.branch 290
 (.branch 289
 (.leaf (.leaf 55))
 (.leaf (.leaf 56)))
 (.branch 291
 (.leaf (.leaf 57))
 (.leaf (.leaf 0))))
 (.branch 294
 (.branch 293
 (.leaf (.leaf 58))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 300
 (.branch 298
 (.branch 297
 (.leaf (.leaf 59))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 312
 (.branch 308
 (.branch 306
 (.branch 305
 (.leaf (.leaf 60))
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
 (.leaf (.leaf 61))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 332
 (.branch 330
 (.branch 329
 (.leaf (.leaf 62))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 344
 (.branch 340
 (.branch 338
 (.branch 337
 (.leaf (.leaf 63))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 368
 (.branch 360
 (.branch 356
 (.branch 354
 (.branch 353
 (.leaf (.leaf 64))
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
 (.leaf (.leaf 0))))
 (.branch 408
 (.branch 404
 (.branch 402
 (.branch 401
 (.leaf (.leaf 78))
 (.leaf (.branch 0x1000000000000000000000000000100000000000000000000000000000000000200000000000000000000000000020000 (.leaf 79) (.leaf 80))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
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
 (.leaf (.branch 0x1000000000000000000000001000000000000000000000000000000000000000200000000000000000000000200000000 (.leaf 84) (.leaf 85))))
 (.branch 419
 (.leaf (.branch 0x1000000000000000000000001000000000000000000000000000000000000000400000000000000000000000400000000 (.leaf 86) (.leaf 87)))
 (.leaf (.leaf 0))))
 (.branch 422
 (.branch 421
 (.leaf (.branch 0x1000000000000000000000001000000000000000000000000000000000000001000000000000000000000001000000000 (.leaf 88) (.leaf 89)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 428
 (.branch 426
 (.branch 425
 (.leaf (.branch 0x1000000000000000000000001000000000000000000000000000000000000010000000000000000000000010000000000 (.leaf 90) (.leaf 91)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 440
 (.branch 436
 (.branch 434
 (.branch 433
 (.leaf (.branch 0x1000000000000000000000001000000000000000000000000000000000001000000000000000000000001000000000000 (.leaf 92) (.leaf 93)))
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
 (.leaf (.leaf 94))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 460
 (.branch 458
 (.branch 457
 (.leaf (.branch 0x1000000000000000100000000000000000000000000000000000000000000010000000000000001000000000000000000 (.leaf 95) (.leaf 96)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 472
 (.branch 468
 (.branch 466
 (.branch 465
 (.leaf (.branch 0x1000000000000000100000000000000000000000000000000000000000001000000000000000100000000000000000000 (.leaf 97) (.leaf 98)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 496
 (.branch 488
 (.branch 484
 (.branch 482
 (.branch 481
 (.leaf (.branch 0x1000000000000000100000000000000000000000000000000000000010000000000000001000000000000000000000000 (.leaf 99) (.leaf 100)))
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
 (.leaf (.leaf 0))))
 (.branch 536
 (.branch 532
 (.branch 530
 (.branch 529
 (.leaf (.leaf 109))
 (.leaf (.leaf 110)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 540
 (.branch 538
 (.branch 537
 (.leaf (.leaf 111))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 560
 (.branch 552
 (.branch 548
 (.branch 546
 (.branch 545
 (.leaf (.leaf 112))
 (.leaf (.leaf 113)))
 (.branch 547
 (.leaf (.leaf 114))
 (.leaf (.leaf 0))))
 (.branch 550
 (.branch 549
 (.leaf (.leaf 115))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 556
 (.branch 554
 (.branch 553
 (.leaf (.leaf 116))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 568
 (.branch 564
 (.branch 562
 (.branch 561
 (.leaf (.leaf 117))
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
 (.leaf (.leaf 118))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 588
 (.branch 586
 (.branch 585
 (.leaf (.leaf 119))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 600
 (.branch 596
 (.branch 594
 (.branch 593
 (.leaf (.leaf 120))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 624
 (.branch 616
 (.branch 612
 (.branch 610
 (.branch 609
 (.leaf (.leaf 121))
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
 (.leaf (.leaf 0))))
 (.branch 664
 (.branch 660
 (.branch 658
 (.branch 657
 (.leaf (.leaf 135))
 (.leaf (.branch 0x10000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000020000 (.leaf 136) (.leaf 137))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 668
 (.branch 666
 (.branch 665
 (.leaf (.branch 0x10000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000001000000 (.leaf 138) (.leaf 139)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 688
 (.branch 680
 (.branch 676
 (.branch 674
 (.branch 673
 (.leaf (.leaf 140))
 (.leaf (.branch 0x10000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000200000000 (.leaf 141) (.leaf 142))))
 (.branch 675
 (.leaf (.branch 0x10000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000400000000 (.leaf 143) (.leaf 144)))
 (.leaf (.leaf 0))))
 (.branch 678
 (.branch 677
 (.leaf (.branch 0x10000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000001000000000 (.leaf 145) (.leaf 146)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 684
 (.branch 682
 (.branch 681
 (.leaf (.branch 0x10000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000010000000000 (.leaf 147) (.leaf 148)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 696
 (.branch 692
 (.branch 690
 (.branch 689
 (.leaf (.branch 0x10000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000001000000000000 (.leaf 149) (.leaf 150)))
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
 (.leaf (.leaf 151))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 716
 (.branch 714
 (.branch 713
 (.leaf (.branch 0x10000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000001000000000000000000 (.leaf 152) (.leaf 153)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 728
 (.branch 724
 (.branch 722
 (.branch 721
 (.leaf (.branch 0x10000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000100000000000000000000 (.leaf 154) (.leaf 155)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 752
 (.branch 744
 (.branch 740
 (.branch 738
 (.branch 737
 (.leaf (.branch 0x10000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000001000000000000000000000000 (.leaf 156) (.leaf 157)))
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
 (.leaf (.leaf 0))))
 (.branch 792
 (.branch 788
 (.branch 786
 (.branch 785
 (.leaf (.leaf 171))
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000020000 (.leaf 172) (.leaf 173))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 796
 (.branch 794
 (.branch 793
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000001000000 (.leaf 174) (.leaf 175)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 816
 (.branch 808
 (.branch 804
 (.branch 802
 (.branch 801
 (.leaf (.leaf 176))
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000200000000 (.leaf 177) (.leaf 178))))
 (.branch 803
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000400000000 (.leaf 179) (.leaf 180)))
 (.leaf (.leaf 0))))
 (.branch 806
 (.branch 805
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000001000000000 (.leaf 181) (.leaf 182)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 812
 (.branch 810
 (.branch 809
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000010000000000 (.leaf 183) (.leaf 184)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 824
 (.branch 820
 (.branch 818
 (.branch 817
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000001000000000000 (.leaf 185) (.leaf 186)))
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
 (.leaf (.leaf 187))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 844
 (.branch 842
 (.branch 841
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000001000000000000000000 (.leaf 188) (.leaf 189)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 856
 (.branch 852
 (.branch 850
 (.branch 849
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000100000000000000000000 (.leaf 190) (.leaf 191)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 880
 (.branch 872
 (.branch 868
 (.branch 866
 (.branch 865
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000001000000000000000000000000 (.leaf 192) (.leaf 193)))
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

end Papers.RationalityTen.RootedCaches.RootedSevenPure017

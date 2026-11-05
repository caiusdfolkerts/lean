module
prelude
public import RootedSevenPure039
public import SignatureCompatibility
public import PackedRawNatGrowth
public import FiniteChecks
public import RawFacetEmbedding
public import RootedSevenPure039GrowthCachecandidateMasksData000
public import RootedSevenPure039GrowthCachebadMasksData000
public import RootedSevenPure039GrowthCachesignatureMasksData000

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure039
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def rawCells := Papers.RationalityTen.FacetUniverses.RootedSevenPure039.rawCells
def cells (c : Fin 659) := rawCells c.val
def ridgeList := ConcreteGrowth.ridgeList cells
def literalCompatible (a b : Fin 659) := ConcreteGrowth.compatible (cells a) (cells b)
def kind (c : Fin 659) := (cells c).kind
def rawKindCode : Nat := 5865764764046764496861633806697378647365356459577421308601650068951229541351162546895260167018968163882800717684802750326563739338416210474440221664150351280645241897782788699861138073272463434234935115889800830211735939249592683218017754935745220404369775373714328291379898233226387970313545048767766107938015192652785379145546260124273159222549472662695463598385780521116822043838471389009533023887089476891118858694262510629111807450897333340084681606134100847788546252801746336026908070980514221088917239833271384181355103692046685661608886588853687305587629281913055598632467585666763756104
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
 (.leaf 0x1b46c1ac6a1a46819c661946418c621846017c5e1745c16c5a1645815c561545414c521445013c4e1344c12c4a00c02004000028))))
 (.leaf 0x0))
 (.branch 24
 (.branch 20
 (.leaf 0x0)
 (.branch 22
 (.branch 21
 (.leaf 0x0)
 (.leaf 0x2a4a829ca6294a428ca2284a027c9e2749c26c9a2649825c962549424c922449023c8e2348c22c8a2248821c860240801c000028))
 (.leaf 0x0)))
 (.branch 28
 (.branch 26
 (.leaf 0x0)
 (.branch 27
 (.leaf 0x0)
 (.leaf 0x1c06f1b8000004)))
 (.leaf 0x0))))
 (.branch 48
 (.branch 40
 (.branch 36
 (.leaf 0x0)
 (.branch 38
 (.leaf 0x0)
 (.branch 39
 (.leaf 0x3dcf63d4f43ccf23c4f03bcee3b4ec3acea3a4e839ce6394e438ce2384e037cde374dc36cda364d835cd6354d404c12044000028)
 (.leaf 0x0))))
 (.leaf 0x0))
 (.branch 56
 (.branch 52
 (.leaf 0x0)
 (.branch 54
 (.branch 53
 (.leaf 0x6ddb66d5b46cdb26c5b06bdae6b5ac6adaa6a5a869da6695a468da2685a067d9e6759c66d9a6659865d96655940a42809c000028)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))))
 (.branch 96
 (.branch 80
 (.branch 72
 (.leaf 0x0)
 (.branch 76
 (.branch 74
 (.leaf 0x0)
 (.branch 75
 (.leaf 0x4c12f4b92d4b12b4a9294a1274992549123489214811f4791d4711b46919461174591545113449114410f4390d0641805c000028)
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 88
 (.leaf 0x0)
 (.branch 92
 (.branch 90
 (.branch 89
 (.leaf 0x8160480e02806007fdfe7f5fc7edfa7e5f87ddf67d5f47cdf27c5f07bdee7b5ec7adea7a5e879de6795e478de20cc320c4000028)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 112
 (.branch 104
 (.branch 100
 (.branch 98
 (.leaf 0x0)
 (.branch 99
 (.leaf 0x5a56859d665956458d625856057d5e5755c56d5a5655855d565555454d525455053d4e5354c52d4a5254851d4607c1e074000028)
 (.leaf 0x0)))
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 120
 (.branch 116
 (.branch 114
 (.branch 113
 (.leaf 0x94e529465093e4e9364c92e4a9264891e469164490e42906408fe3e8f63c8ee3a8e6388de368d6348ce328c6300f43c0ec000028)
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
 (.leaf 0x204801f87d1ec7a1e0771d8751cc721b85f1745a1645714c511384d12c0501001001a)))
 (.branch 134
 (.branch 133
 (.leaf 0x0)
 (.leaf 0x2e8b92dcb62d0b32c4b02bcae2b0ab26c992589524c8f2348a224871845c16c5815c551404f1304b02c0a01c010024))
 (.branch 135
 (.leaf 0x4210741504409013fcfe3f4fc3e8f93a4e7390e3384dd36cd835cd51805e16c59158541484f1344a05414044010024)
 (.leaf 0x0))))
 (.branch 140
 (.branch 138
 (.leaf 0x0)
 (.branch 139
 (.leaf 0x505404f93d4ed3a4e1374d9354cd32489204751c46916451114410e1b81b06817001a)
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 152
 (.branch 148
 (.branch 146
 (.branch 145
 (.leaf 0x0)
 (.leaf 0x33cce330cb324c8318c5310c3304c02749825c9424c912308b220871b80e03407001a))
 (.leaf 0x0))
 (.branch 150
 (.branch 149
 (.leaf 0x721c7715c4709c16fdbe6f5bc6e9b96a5a7691a36859d66d9865d952709a25c95248902388b224860ac2a09c070024)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 156
 (.branch 154
 (.branch 153
 (.leaf 0x85a1584e128420f8360c82e0a822077ddf57c9f17bdeb7a5e6795e31b8350d031001a)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 176
 (.branch 168
 (.branch 164
 (.branch 162
 (.leaf 0x0)
 (.branch 163
 (.leaf 0x5e9795dd765d1735c5705bd6e5b16b56d595595554d4f5354a525473ace6394e2384df368d9358d508420074110024)
 (.leaf 0x0)))
 (.branch 166
 (.branch 165
 (.leaf 0x775dc769d975dd6751d3749d173dce6ada6695a26859f66999659953a8e8394e3380de370d935cd40b82d09c110024)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 184
 (.branch 180
 (.branch 178
 (.branch 177
 (.leaf 0x992639866097a5d96e5a9665895a55916439023f8f6398de348ce316a9a8695a36819e6719965d940fc3e0ec270024)
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
 (.leaf 0x63d8e6318b625886198561183605805755855d5454d515314b521474911f4791b4691844d1243d0e09023074170024)
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 204
 (.branch 202
 (.branch 201
 (.leaf 0x8ae2a8a2278962488a218821f8761c7e5f47cdf07bded7a1e7791e348d214791c46517455124410d0e0370c4170024)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 216
 (.branch 212
 (.branch 210
 (.branch 209
 (.leaf 0x9e6789da759ce729c26f9ba6d9ae6a91e429063e8f63b8da358ca317e1f67cdf17b9ec7a9e7795e2108410ec310024)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 240
 (.branch 232
 (.branch 228
 (.branch 226
 (.branch 225
 (.leaf 0xa3a8da2e8aa2287a1684a0e82a027f91a449063f8f23a8e2358ce305715a55d55549505394b52546118450ec1d0024)
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
 (.leaf 0x20c821fc7e1f07b1e4771d8741cc711bc6b1a466194631485013c4c1280601002001a)))
 (.branch 262
 (.branch 261
 (.leaf 0x0)
 (.leaf 0x2f0bb2e0b72d4b42c8b02bcad2b0aa29ca5288a127c8e2308b220861b46819c6418c541444e1344a0300a020020024))
 (.branch 263
 (.leaf 0x429094190540d02400fe3f4fb3e8f83d4f33c0ef3b4dc368d9358d41b06a19c651885514c4e1304b05814048020024)
 (.leaf 0x0))))
 (.branch 268
 (.branch 266
 (.leaf 0x0)
 (.branch 267
 (.leaf 0x50d424fd3e4f13b4e5374d9344cd314b92c4a5284991544d1243d0d1bc1c06818001a)
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 280
 (.branch 276
 (.branch 274
 (.branch 273
 (.leaf 0x0)
 (.leaf 0x344d0334cc328c931cc5310c2304bf2a4a428ca027c902348a224861bc0f03408001a))
 (.leaf 0x0))
 (.branch 278
 (.branch 277
 (.leaf 0x729c9719c570dc2701be6f5bb6e9b86d5b36c1af6b59c66999659942a0a628ca12789123c8a220870b02a0a0080024)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 284
 (.branch 282
 (.branch 281
 (.leaf 0x86217852138461083a0c82e098220680e017f9fd7edea7a1e7791e21bc360d032001a)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 304
 (.branch 296
 (.branch 292
 (.branch 290
 (.leaf 0x0)
 (.branch 291
 (.leaf 0x5f17b5e1775d5745c9705bd6d5b16a59d655896157d4e5314b521463dcf23c4ee3b4de36cd835cd408820078120024)
 (.leaf 0x0)))
 (.branch 294
 (.branch 293
 (.leaf 0x77dde76dda761d7755d3749d073dcd6ddb26c5ae6b59e66d9865d943d8f43c4ef3b0df374d8358d50bc2d0a0120024)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 312
 (.branch 308
 (.branch 306
 (.branch 305
 (.leaf 0x99a6598a6197e5e9725a9665795a549464f9324b926388da358ca306d9b46c5af6b19f67598659951003e0f0280024)
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
 (.leaf 0x645906358c6298961d85611826057f5a56458d6057d505354a525464c12b4a92749917451114410d09423078180024)
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 332
 (.branch 330
 (.branch 329
 (.leaf 0x8b62c8a62889a2588e218821e8761b816007fdfc7edec7a5e6795e24bd2d4a928495184591143d0e0e4370c8180024)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 344
 (.branch 340
 (.branch 338
 (.branch 337
 (.leaf 0x9ee7a9de769d2739c66f9ba6c9ae6994e4e9364a9263a8de348ce30812027fdfd7e9ed7ade6791e310c410f0320024)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 368
 (.branch 360
 (.branch 356
 (.branch 354
 (.branch 353
 (.leaf 0xa428fa328ba2688a1a84a0e81a027e94a509364b9223b8e6348ca315a16658d615795153d4a5214711c450f01e0024)
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
 (.leaf 0xd133cca320c7318c3308c12f0ba2d4b32c8b12b8ad2b08d2308b22889220832047c1e8791e0751d0731445013c4e1344c0400d02804002b))
 (.branch 387
 (.leaf 0x19163d8a6218761983609815f17a5d5735c9715b96d5b14d5314b52949521435053c4e9394e1354d13345113449114410f4290840d01400ff3f0fb3e8db368d9360d7358822007f1f4791e0761c87114c5213c4e12c4a098230801a05004004b)
 (.leaf 0x21484154540004)))
 (.branch 390
 (.branch 389
 (.leaf 0x1df775d8759d5751d1741cf729c870dc1701bf6f1bb6e99b66999661976590941d06411003fcfd3e4f8374dc364d8354d42ecb92e0b62c8b12bcab2a88f2388b22887218551504d1304b128300b42a0500a0041)
 (.leaf 0x2f8bd2449014c520006))
 (.branch 391
 (.leaf 0x4310b37cde144500006)
 (.leaf 0x0))))
 (.branch 396
 (.branch 394
 (.branch 393
 (.leaf 0x22d8ae268922388a1f87a1d862168460f83a0d82a09821e97a1e7799e5791425013f4f5394e1364c93145915449114390d0e8370d01a002b)
 (.leaf 0x0))
 (.branch 395
 (.leaf 0x51544461170004)
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 408
 (.branch 404
 (.branch 402
 (.branch 401
 (.leaf 0x27b9e6749ca719c26d9b26b99a6497e5d9725b9625795a378da358d2338ca178561484a0e8360b81e067adea79de678de2725c7719c4701bf6f5b96e19d6719966195650d0338cd32cc7318c4300bf244902248821c86110410f8340a80d004b)
 (.leaf 0x34cd223c8e0004))
 (.leaf 0x0))
 (.branch 406
 (.branch 405
 (.leaf 0x731cb67d9e2348c0006)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 412
 (.branch 410
 (.branch 409
 (.leaf 0x86a197b5ec0004)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 432
 (.branch 424
 (.branch 420
 (.branch 418
 (.branch 417
 (.leaf 0x290a3a89a1e86a1682a06809966398a609725b96655952398e2358d2318c1de771db765d5751d2739cd67d9e65d96655945ed795e1765c9715bd6b5a94f5394b52947518df378d7358d5350481143e0b4200041)
 (.leaf 0x0))
 (.branch 419
 (.leaf 0x5f97d54550374dc0006)
 (.leaf 0x0)))
 (.branch 422
 (.branch 421
 (.leaf 0x785e06759c36cda0006)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 440
 (.branch 436
 (.branch 434
 (.branch 433
 (.leaf 0x9a2678ee3a66d9a0006)
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
 (.leaf 0x28fa368ca2a86a16839fe7e9ea789de759c6709ba6a9a63b8ea338ca318c22c8aa2989e2388a208721b7b5ec795e478de26418e6358b61d86611805fd5154149521475191845d1043d0e43449114410dc230041)
 (.leaf 0x0))
 (.branch 451
 (.leaf 0x64d9253d4e459150006)
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 460
 (.branch 458
 (.branch 457
 (.leaf 0x8be2e7adea451130006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 472
 (.branch 468
 (.branch 466
 (.branch 465
 (.leaf 0x9f67c8e6387a5e80006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 496
 (.branch 488
 (.branch 484
 (.branch 482
 (.branch 481
 (.leaf 0xa4a918de365354c0006)
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
 (.leaf 0x214841fc7d1f07a1e4781d4741c8711c06a1a067190621785c16c581580601403001a)))
 (.branch 518
 (.branch 517
 (.leaf 0x0)
 (.leaf 0x2f8bd2e0b62d4b32c8b12b8ad2acaa298a428ca02789a26097250921b06919865188601745a164560300b024030024))
 (.branch 519
 (.leaf 0x4310b4190440d01400ff3f0fb3e4f83d0f23c4ee3b0e8398e5388e01b46b1986418c6117c5a160570581504c030024)
 (.leaf 0x0))))
 (.branch 524
 (.branch 522
 (.leaf 0x0)
 (.branch 523
 (.leaf 0x515444fd3d4f13a4e5384d5344c9314b52b4a9274952147d1e46d191c01c06c19001a)
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 536
 (.branch 532
 (.branch 530
 (.branch 529
 (.leaf 0x0)
 (.leaf 0x34cd2334cb328c831cc630cc2300bf2a0a5288a12789c26496254921c00f03809001a))
 (.leaf 0x0))
 (.branch 534
 (.branch 533
 (.leaf 0x731cb719c470dc1701bf6f1bb6e5b86d1b26c5ae6b1a8699a5689a02a4a7288a027c9d26c96250930b02b0a4090024)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 540
 (.branch 538
 (.branch 537
 (.leaf 0x86a19852128460f83a0d82a0981e0680a007fdfc7e9f67d1f37c1ee1c0360d433001a)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 560
 (.branch 552
 (.branch 548
 (.branch 546
 (.leaf 0x0)
 (.branch 547
 (.leaf 0x5f97d5e1765d5735c9715b96d5ad6a5996458d605795a56157551523d8f33c0ef3b0ea39ce438ce00882107c130024)
 (.leaf 0x0)))
 (.branch 550
 (.branch 549
 (.leaf 0x785e076dd9761d6755d4745d0739cd6d9b36c1af6b1aa69da468da03dcf53c0ee3b4eb3a4e4388e10bc2e0a4130024)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 568
 (.branch 564
 (.branch 562
 (.branch 561
 (.leaf 0x9a26798a6097e5d9725b96257956549424e9364a9224490a418fa3c6ddb56c1ae6b5ab6a5a4689a11003f0f4290024)
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
 (.leaf 0x64d926358b6298861d8660d826017f5a165589615795c56556555524bd2c4a528495234811d471190942407c190024)
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 588
 (.branch 586
 (.branch 585
 (.leaf 0x8be2e8a62789a2488e2287e1e8721b812017f9fd7e9f87d5f27c5ee4c12e4a527499244891d46d1a0e4380cc190024)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 600
 (.branch 596
 (.branch 594
 (.branch 593
 (.leaf 0x9f67c9de759d2729c6709b66c9aa6994a4f9324b9224690e408fe3c816037f9fc7edf97ddf27c1ef10c420f4330024)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 624
 (.branch 616
 (.branch 612
 (.branch 610
 (.branch 609
 (.leaf 0xa4a91a328aa2687a1a85a0a819fe7e94e519324a92647916408fa3d5a5675896057d5d56d565515311c460f41f0024)
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
 (.leaf 0xd3338ca324c7314c4308c02f8b92d4b42c8b02bcad2ac992609725895250852007c1ec791dc761d0721745c16c5a164580400e02c05002b))
 (.branch 643
 (.leaf 0x1936398a6258761584609805f9795d5745c9705bd6d5ad595615755955551455013c4ed394dd364d1324811f4791d4711b4310740d02400fe3f4fb3e4e7398e5390e3388842047f1f8791dc751cc7117c5e16c5a15c56098240841b05405004b)
 (.leaf 0x20c82184600004)))
 (.branch 646
 (.branch 645
 (.leaf 0x1e1771d875dd574dd2741ce731c770dc2701be6f5bb6e5a7699a5691a36890b42106415003f8fc3e8f83a4e8394e4384e02f4ba2e0b72c8b02b8ac2a89b2689725893248611805916057158300b82b0540b0041)
 (.leaf 0x2f0bb2749c17c5e0006))
 (.branch 647
 (.leaf 0x429093acea1745c0006)
 (.leaf 0x0))))
 (.branch 652
 (.branch 650
 (.branch 649
 (.leaf 0x22f8aa26896238862087a1c86a158461083a0c82e0981df57d1f37c9f17c1445053f4f9394dd354cd31489214791d469190e8380d41b002b)
 (.leaf 0x0))
 (.branch 651
 (.leaf 0x50d42491230004)
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 664
 (.branch 660
 (.branch 658
 (.branch 657
 (.leaf 0x27d9e2749ce719be6e9b26a9a26397e5e9725a966579564390a419023f8fa1985a1484e0e8320a822067ddf67cdf27bdee72dc8719c5701be6f1ba6e1a96a1a5691a1680d233ccd330c7314c3304bf2749c2549424c92110420fc350ac0e004b)
 (.leaf 0x344d026c9a0004))
 (.leaf 0x0))
 (.branch 662
 (.branch 661
 (.leaf 0x729c96adaa264980006)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 668
 (.branch 666
 (.branch 665
 (.leaf 0x862177e5f80004)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 688
 (.branch 680
 (.branch 676
 (.branch 674
 (.branch 673
 (.leaf 0x292a3689a2286a1283a067f99e6498a619725a9625695245912419023d8f1e0775db769d574dd173dcd6adaa68da2685a05f57a5e1775c9705b96c5a95b5695755953548eb3a8e3388e1380481183f0b8210041)
 (.leaf 0x0))
 (.branch 675
 (.leaf 0x5f17b5755c3a4e80006)
 (.leaf 0x0)))
 (.branch 678
 (.branch 677
 (.leaf 0x77dde6a5a839ce60006)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 696
 (.branch 692
 (.branch 690
 (.branch 689
 (.leaf 0x99a6591e4669da60006)
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
 (.leaf 0x291a3a8ca2e86a1282a027e9f2799de769c66f9b66b9a64791a3f8fa3d8f22e8ae298a2238861f8761b7e5f87c5f07bdee6498f6358c61d8560d815fd5d57155551535492448d1c46d1a46449118420e0240041)
 (.leaf 0x0))
 (.branch 707
 (.leaf 0x6459056d5a489210006)
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 716
 (.branch 714
 (.branch 713
 (.leaf 0x8b62c7ddf64811f0006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 728
 (.branch 724
 (.branch 722
 (.branch 721
 (.leaf 0x9ee7a916447d5f40006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 752
 (.branch 744
 (.branch 740
 (.branch 738
 (.branch 737
 (.leaf 0xa428f90e42565580006)
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
 (.leaf 0xd2340c9320c6314c430cbf2f4bb2d0b32c4b02bcae2a8a5290a3288a1280842087b1e8781dc761d4711a46819c66194640400f03006002b))
 (.branch 771
 (.leaf 0x19264189621866158460d7f5f57b5d1735c5705bd6e5a9655916358961581445093b4e9384dd364d5314b12b4a9294a12742d09409013fcfe3f4fc3e0f33c8f13c0ef3b88520c7e1f4781dc741cc721ac6a19c6618c62098250881c05806004b)
 (.leaf 0x204801b46c0004)))
 (.branch 774
 (.branch 773
 (.leaf 0x1e0779d7759d474dd2745cd72dc9709c16fdbe6f5bc6e1b36c9b16c1af6b90c42905410ff3f8fb3e8f93d4f43c4f03b4ec2f8bc2dcb62c4b02b4ac2aca7298a32889f2786d1b06519063188300bc2c0580c0041)
 (.leaf 0x2e8b92a4a81ac6a0006))
 (.branch 775
 (.leaf 0x421073dcf61a4680006)
 (.leaf 0x0))))
 (.branch 780
 (.branch 778
 (.branch 777
 (.leaf 0x22e8b225892228862087e1b866178420f8360c82e0a81a01801ff7f9fd7f14550d3e4f5384dd344cd324b92d4a929499250e8390d81c002b)
 (.leaf 0x0))
 (.branch 779
 (.leaf 0x505404c12f0004)
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 792
 (.branch 788
 (.branch 786
 (.branch 785
 (.leaf 0x27c9ea739ca709be6e9b66999e6597a5d96e5a966589524f93a4d9324b92a1a8621384a0d832098220780e027fdfe7edfa731ca715c46fdbe6edba6e5b56d1b16c1ad6b0d3344cc32cc6314c2304c02a4a8284a027c9e11043100360b00f004b)
 (.leaf 0x33cce29ca60004))
 (.leaf 0x0))
 (.branch 790
 (.branch 789
 (.leaf 0x721c76ddb6294a40006)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 796
 (.branch 794
 (.branch 793
 (.leaf 0x85a15816040004)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 816
 (.branch 808
 (.branch 804
 (.branch 802
 (.branch 801
 (.leaf 0x291a3e88a1e85a1283a0a7e9a2669866096e5a95e56956519424d93249921e177dda765d474dd073dce6ddb66bdae6b5ac5f97c5dd765c5705b56c5ad67599635895f578f73d8ef3b8ed3b04811c400bc220041)
 (.leaf 0x0))
 (.branch 803
 (.leaf 0x5e9795a5683d4f40006)
 (.leaf 0x0)))
 (.branch 806
 (.branch 805
 (.leaf 0x775dc6d5b43ccf20006)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 824
 (.branch 820
 (.branch 818
 (.branch 817
 (.leaf 0x9926394e526cdb20006)
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
 (.leaf 0x292a428ba2a85a1281a027f9f67b9da759c26f9b26b9aa5394a4b92a499222f8b62889e228861e8761c816047f5fc7edfa64d916318b6198560981601695a1615815f579304bd2849d264944911c430e4250041)
 (.leaf 0x0))
 (.branch 835
 (.leaf 0x63d8e59d664b92d0006)
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 844
 (.branch 842
 (.branch 841
 (.leaf 0x8ae2a80e024b12b0006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 856
 (.branch 852
 (.branch 850
 (.branch 849
 (.leaf 0x9e67894650806000006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 880
 (.branch 872
 (.branch 868
 (.branch 866
 (.branch 865
 (.leaf 0xa3a8d93e4e595640006)
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
 (.leaf 0x292a4690a3e8ea3683a0a81a027f9fa7d9f27b9ea799e26e9b66c9ae6a9a66899e669966498e599625795a559522f8ba2d8b22b8aa2087e1e8761c86e1a8661885e168560b82a0982207819e1781df779dd771d2745d073dce735cc72dca725c871dbd6f1bb6e9b96e193649916418f6398460d82605805fd7e5f57c5ed7a5e56f5b96d5b16b5a9455114350941501364d5344cd324c50c42d0a4250841cfd3f0fb3e8f93e0d3348d1340cf338c430cc2304c02fcbe2f4bc2ecba2e4af2b8ad2b0ab2a8852108320881200761d4741cc721c449120440e8300981000af)
 (.leaf 0xcd330cb2e0b72d87f1f87d0009))
 (.branch 899
 (.leaf 0x18d6318b5e1775d93f4f93d419054107c1ec7a000f)
 (.leaf 0x0)))
 (.branch 902
 (.branch 901
 (.leaf 0x76dda765c6715c440d02404b52d0b3000c)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 908
 (.branch 906
 (.branch 905
 (.leaf 0x2298a227852138493c4ed3a0009)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 920
 (.branch 916
 (.branch 914
 (.branch 913
 (.leaf 0x2779da7598a61982118420f70dc2704ca324c8000f)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 944
 (.branch 936
 (.branch 932
 (.branch 930
 (.branch 929
 (.leaf 0xa328ba2a5f97a5d761d7759755d173000c)
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
 (.leaf 0xa2688a1e749ce7289a258918a62588000c)
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
 (.leaf 0x49120471184511043108411003f0f83d0f03b0e8390e0370d8350d0330c8310c02f0b82d0b02b0a8290a0270982509023088210801f0781d0701b06819060170581505013048110400f0380d0300b02809020070180501003008010049))
 (.branch 3
 (.leaf 0xa1a85a1283a0a81a027f9fa719c26f9ba6d9b26b9aa699725b96a599625795a559524d9324b92a49922419023f8fa3d8f2358d2338ca318c22388a218821f87a1d8721b83a0d8320b82a0982207819ff7f9fd7f1fb7e9f37c9f17c1ef7b9e7799e5791e3789d5751d3749d1741cf739cd701bf6f9bd6f1bb6e9b96e1b16c1af6b9ad6b1a5691a3689a1681996619765995651876198561183609816017f5c9715c16f5b96d5b16b5a963589615815f5795755955551535494b5294952147519394e1374d9354d1334c9314a9294a127499254791d4711b46919449114410f4390d400ff3f8fd3f0fb3e8f93e0f13c0ef3b8ed3b0e5390e3388e1380d9360d7358d5350c7318c5310c3308c1300bf2c8b12c0af2b8ad2b0ab2a8a3288a12809f2789725895250932488b2288922087218791e0771d8751d0731c87119c661946418c6216c5a1645815c5613c4e1344c12c4a010e)
 (.branch 4
 (.leaf 0x292a4690a3e8ea368ca2e8aa2688a1e7d9f27b9ea799e2779da759d2739ca6899e669966498e629866097e5e9765394a519424f93a4791a459124390a3b8ea398e2378da2f8ba2d8b22b8aa298a22789a258921a8661885e168561484e128461083e058120380a01801f97e1f77d9f57d1ed7b1eb7a9e97a1e1781df779dd771db769d9761d7759cc72dca725c871dc6715c470dc2705b76d9b56d1b36c9ab6a9a96a1a76999f6799d6719b66993649916418f6398d6318b629896217e5f57c5ed7a5e5785dd765d5745cd695a167599655915d5715b56959561515414f5394d5314551143509415013f4f93d4f13b4e9304bd2e4b52c4ad2448d224852047d1845d164551444d0c42d0a4250841d064150440d02404f73d8f53d0f33c8eb3a8e93a0e7398df378dd370db368d3348d1340cf338cd330cb328c9320be2f4bc2ecba2e4b82dcb62d4b42cca92a0a7298a52909d2709b26899260912408f2388d2308521083208812007f1f87d1f07b1e8701bc6e1b46c1ac6a1a4681846017c5e1745c1545414c5214450013b)
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
 (.leaf 0x3fffffffffffffffffe))
 (.branch 3
 (.leaf 0x7fc003fe001ff03f03f03f000ff8007fc0fc0fc0fc003fe001ff03f03f03f000ff8007fc0fc0fc0fc003fe07e07e07e001ff03f03f03f000ff8007fc0fc0fc0fc003fe00fc0fc0fc000000000000000000)
 (.branch 4
 (.leaf 0x7ff803ffc01ffe00fc0fc0fc0fff007ff803f03f03f03ffc01ffe00fc0fc0fc0fff007ff803f03f03f03ffc01f81f81f81ffe00fc0fc0fc0fff007ff803f03f03f03ffc01ff03f03f00000000000000000000)
 (.leaf 0x0))))
def kindMasks := kindMaskTable.get
def keys := List.range 5
def vertexMaskTable : Table Nat :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf 6582018229284824168619876730229402019930924573068387974813712383)
 (.leaf 41315998049390537434494706752048189989275292685267576205283967686421077128100839259122167733402336002278425376814905819263))
 (.branch 3
 (.leaf 12486994201263968925526347603174615832456958075953132555246638564157370482734951456259398180349230481034664774136026228042943206569516626440232847)
 (.branch 4
 (.leaf 3773962424821541352241542093994067626947995694027521255710983305853053639210715714396532548403297651236050318485931830586322087945148835787151193619945913361895178371073)
 (.leaf 1140610154405548804660289127464447575199772163798196221531980465801231471353951656678419577793888582926960019126974579908287971515335671016248294263404014082508396420584064732543200520430478209))))
 (.branch 7
 (.branch 6
 (.leaf 2392031725922294966546782288021777088971477950823350138002073500828663723305291957813877609084650873449083386530989222213044293347870853694275419945696782062921526246577545398036659149131349991751681)
 (.leaf 2392032866531361601745642932355398257929572091497074008184233864049409470417640127641109342548592833857362012044117499196826180523482513109156969036642055688694370761262954556228624698141972694564865))
 (.branch 8
 (.leaf 2392032866531905486531661172337109392999314126882805929205013497874998517670250469503065159116969187253421021334988536340185143627915161586918111773360110388885333360776875479137889790877440532507826)
 (.branch 9
 (.leaf 2392032866531905486790879277684767315453934877534913670753699367930588709954078427404470280947475934213454945227632106971600519480337183556160921136977763784614576980364240295831005093565503376831828)
 (.leaf 2392032866531905486790942563355018208501409150179115845495288402566832750528366471339504803682297835274724484759832459405836704874832403776368255807232553250775643692828135133937445005031360057432680)))))
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
 (.branch 34
 (.leaf (.leaf 0))
 (.branch 35
 (.leaf (.leaf 10))
 (.leaf (.leaf 0))))
 (.branch 38
 (.branch 37
 (.leaf (.leaf 11))
 (.leaf (.leaf 0)))
 (.branch 39
 (.leaf (.leaf 12))
 (.leaf (.leaf 0)))))
 (.leaf (.leaf 0)))
 (.branch 56
 (.branch 52
 (.branch 50
 (.branch 49
 (.leaf (.leaf 13))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 54
 (.branch 53
 (.leaf (.leaf 14))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))))
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
 (.branch 99
 (.leaf (.leaf 21))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
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
 (.branch 150
 (.branch 149
 (.leaf (.leaf 33))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 156
 (.branch 154
 (.branch 153
 (.leaf (.leaf 34))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 176
 (.branch 168
 (.branch 164
 (.branch 162
 (.branch 161
 (.leaf (.leaf 35))
 (.leaf (.leaf 0)))
 (.branch 163
 (.leaf (.leaf 36))
 (.leaf (.leaf 0))))
 (.branch 166
 (.branch 165
 (.leaf (.leaf 37))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
 (.branch 184
 (.branch 180
 (.branch 178
 (.branch 177
 (.leaf (.leaf 38))
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
 (.leaf (.leaf 39))
 (.leaf (.leaf 0)))
 (.branch 195
 (.leaf (.leaf 40))
 (.leaf (.leaf 0))))
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
 (.branch 278
 (.branch 277
 (.leaf (.leaf 54))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 284
 (.branch 282
 (.branch 281
 (.leaf (.leaf 55))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 304
 (.branch 296
 (.branch 292
 (.branch 290
 (.branch 289
 (.leaf (.leaf 56))
 (.leaf (.leaf 0)))
 (.branch 291
 (.leaf (.leaf 57))
 (.leaf (.leaf 0))))
 (.branch 294
 (.branch 293
 (.leaf (.leaf 58))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
 (.branch 312
 (.branch 308
 (.branch 306
 (.branch 305
 (.leaf (.leaf 59))
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
 (.leaf (.leaf 60))
 (.leaf (.leaf 0)))
 (.branch 323
 (.leaf (.leaf 61))
 (.leaf (.leaf 0))))
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
 (.branch 406
 (.branch 405
 (.leaf (.branch 0x1000000000000000000000000000100000000000000000000000000000000001000000000000000000000000000100000 (.leaf 81) (.leaf 82)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 412
 (.branch 410
 (.branch 409
 (.leaf (.branch 0x1000000000000000000000000000100000000000000000000000000000000010000000000000000000000000001000000 (.leaf 83) (.leaf 84)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 432
 (.branch 424
 (.branch 420
 (.branch 418
 (.branch 417
 (.leaf (.leaf 85))
 (.leaf (.leaf 0)))
 (.branch 419
 (.leaf (.branch 0x1000000000000000000000001000000000000000000000000000000000000000400000000000000000000000400000000 (.leaf 86) (.leaf 87)))
 (.leaf (.leaf 0))))
 (.branch 422
 (.branch 421
 (.leaf (.branch 0x1000000000000000000000001000000000000000000000000000000000000001000000000000000000000001000000000 (.leaf 88) (.leaf 89)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
 (.branch 440
 (.branch 436
 (.branch 434
 (.branch 433
 (.leaf (.branch 0x1000000000000000000000001000000000000000000000000000000000001000000000000000000000001000000000000 (.leaf 90) (.leaf 91)))
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
 (.leaf (.leaf 92))
 (.leaf (.leaf 0)))
 (.branch 451
 (.leaf (.branch 0x1000000000000000100000000000000000000000000000000000000000000000400000000000000040000000000000000 (.leaf 93) (.leaf 94)))
 (.leaf (.leaf 0))))
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
 (.branch 534
 (.branch 533
 (.leaf (.leaf 111))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 540
 (.branch 538
 (.branch 537
 (.leaf (.leaf 112))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 560
 (.branch 552
 (.branch 548
 (.branch 546
 (.branch 545
 (.leaf (.leaf 113))
 (.leaf (.leaf 0)))
 (.branch 547
 (.leaf (.leaf 114))
 (.leaf (.leaf 0))))
 (.branch 550
 (.branch 549
 (.leaf (.leaf 115))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
 (.branch 568
 (.branch 564
 (.branch 562
 (.branch 561
 (.leaf (.leaf 116))
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
 (.leaf (.leaf 117))
 (.leaf (.leaf 0)))
 (.branch 579
 (.leaf (.leaf 118))
 (.leaf (.leaf 0))))
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
 (.branch 662
 (.branch 661
 (.leaf (.branch 0x10000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000100000 (.leaf 138) (.leaf 139)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 668
 (.branch 666
 (.branch 665
 (.leaf (.branch 0x10000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000001000000 (.leaf 140) (.leaf 141)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 688
 (.branch 680
 (.branch 676
 (.branch 674
 (.branch 673
 (.leaf (.leaf 142))
 (.leaf (.leaf 0)))
 (.branch 675
 (.leaf (.branch 0x10000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000400000000 (.leaf 143) (.leaf 144)))
 (.leaf (.leaf 0))))
 (.branch 678
 (.branch 677
 (.leaf (.branch 0x10000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000001000000000 (.leaf 145) (.leaf 146)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
 (.branch 696
 (.branch 692
 (.branch 690
 (.branch 689
 (.leaf (.branch 0x10000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000001000000000000 (.leaf 147) (.leaf 148)))
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
 (.leaf (.leaf 149))
 (.leaf (.leaf 0)))
 (.branch 707
 (.leaf (.branch 0x10000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000040000000000000000 (.leaf 150) (.leaf 151)))
 (.leaf (.leaf 0))))
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
 (.branch 790
 (.branch 789
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000100000 (.leaf 174) (.leaf 175)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 796
 (.branch 794
 (.branch 793
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000001000000 (.leaf 176) (.leaf 177)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 816
 (.branch 808
 (.branch 804
 (.branch 802
 (.branch 801
 (.leaf (.leaf 178))
 (.leaf (.leaf 0)))
 (.branch 803
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000400000000 (.leaf 179) (.leaf 180)))
 (.leaf (.leaf 0))))
 (.branch 806
 (.branch 805
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000001000000000 (.leaf 181) (.leaf 182)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
 (.branch 824
 (.branch 820
 (.branch 818
 (.branch 817
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000001000000000000 (.leaf 183) (.leaf 184)))
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
 (.leaf (.leaf 185))
 (.leaf (.leaf 0)))
 (.branch 835
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000040000000000000000 (.leaf 186) (.leaf 187)))
 (.leaf (.leaf 0))))
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
def candidateMasks (i : Nat) := PackedRawNatGrowth.take 659
  (PackedRawNatGrowth.drop (659*(i%64)) (candidateMasksBlocks.get (i/64)))

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
def badMasks (i : Nat) := PackedRawNatGrowth.take 659
  (PackedRawNatGrowth.drop (659*(i%64)) (badMasksBlocks.get (i/64)))

def signatureMasksBlocks : Table Nat :=
(.branch 2
 (.branch 1
 (.leaf signatureMasksBlock0000)
 (.leaf signatureMasksBlock0001))
 (.branch 3
 (.leaf signatureMasksBlock0002)
 (.leaf signatureMasksBlock0003)))
def signatureMasks (i : Nat) := PackedRawNatGrowth.take 659
  (PackedRawNatGrowth.drop (659*(i%64)) (signatureMasksBlocks.get (i/64)))

def fastKind := rawKind
def candidateSupports := candidateRows
def kindSupports := kindRows
def wellFormedTest (i : Nat) : Bool := RawFacetEmbedding.wellFormedCheck (rawCells i)

def cellTest (i : Nat) := (listBounds 1024 (rawCells i).ridgeMasks && ((rawCells i).ridgeMasks.all (fun q => (candidateMasks q).testBit i) && (decide (rawKind i = (rawCells i).kind) && (decide ((rawCells i).vertices < 1024) && ((List.range 10).all (fun v => decide ((vertexMasks v).testBit i = (rawCells i).vertices.testBit v)) && (SignatureCompatibility.faces (rawCells i)).all (fun q => (SignatureCompatibility.profileMask (SignatureCompatibility.allMask 659) signatureIndex signatureMasks (rawCells i) q).testBit i))))))
def ridgeTest (i : Nat) := decide (candidateMasks i = RawNatGrowthCheck.mask (candidateRows i)) &&
  (candidateRows i).all (fun c => hasNat (rawCells c).ridgeMasks i)
def kindTest (i : Nat) := decide (kindMasks i = RawNatGrowthCheck.mask (kindRows i)) &&
  (kindRows i).all (fun c => decide ((rawCells c).kind = i))
def badTest (i : Nat) := if badMasks i = 0 then true else
  decide (Nat.land (badMasks i) (SignatureCompatibility.cover (SignatureCompatibility.allMask 659)
    vertexMasks signatureIndex signatureMasks (rawCells i)) = 0)

end Papers.RationalityTen.RootedCaches.RootedSevenPure039

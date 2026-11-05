module
prelude
public import RootedSevenPure033
public import SignatureCompatibility
public import PackedRawNatGrowth
public import FiniteChecks
public import RawFacetEmbedding
public import RootedSevenPure033GrowthCachecandidateMasksData000
public import RootedSevenPure033GrowthCachebadMasksData000
public import RootedSevenPure033GrowthCachesignatureMasksData000

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure033
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def rawCells := Papers.RationalityTen.FacetUniverses.RootedSevenPure033.rawCells
def cells (c : Fin 758) := rawCells c.val
def ridgeList := ConcreteGrowth.ridgeList cells
def literalCompatible (a b : Fin 758) := ConcreteGrowth.compatible (cells a) (cells b)
def kind (c : Fin 758) := (cells c).kind
def rawKindCode : Nat := 1493596731634803415675505274503925572118111935029548566838117803558653196393225833444385332313115096063990345834200480155662914141519751923959699287769021077573950435862272702066933468858362230793506806826098086862409566975923054799595272978887701186521340472731346943789722808409258153443948778740272547429215223889698030187891314441726013334276684350123261800682536820305207597025656904459222295191973258894268544360195425522909842528864276846366512699116993768459025432211068617456811802407845522812843900102754536623328065871670895697193181967823057619641061987685831998978721116463166203587722508041263958498526571447243672278767811687426707156831703157207657969167142544101118536
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
 (.leaf 0x0)))
 (.branch 24
 (.branch 20
 (.leaf 0x0)
 (.branch 22
 (.branch 21
 (.leaf 0x0)
 (.leaf 0x34cd2344d033cce334cc32cca324c831cc6314c430cc2304c02fcbe2f4bc2ecba2e4b82dcb62d4b42ccb22c4b00300b028000028))
 (.leaf 0x0)))
 (.branch 28
 (.branch 26
 (.branch 25
 (.leaf 0x0)
 (.leaf 0x4310b4290942107419054110340901400ff3f8fd3f0fb3e8f93e0f73d8f53d0f33c8f13c0ef3b8ed3b0eb3a8e904811040000028))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 48
 (.branch 40
 (.branch 36
 (.leaf 0x0)
 (.branch 38
 (.leaf 0x0)
 (.branch 39
 (.leaf 0x56959561575595555153549515414f5394d5314b52949521475194551143509415013f4f93d4f13b4e9394e1370701b068000028)
 (.leaf 0x0))))
 (.branch 44
 (.branch 42
 (.leaf 0x0)
 (.branch 43
 (.leaf 0x64d926459063d8e6358c62d8a6258861d866158460d82605805fd7e5f57c5ed7a5e5785dd765d5745cd725c57008821080000028)
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 96
 (.branch 80
 (.leaf 0x0)
 (.branch 88
 (.branch 84
 (.leaf 0x0)
 (.branch 86
 (.branch 85
 (.leaf 0x785e077dde775dc76dda765d875dd6755d474dd2745d073dce735cc72dca725c871dc6715c470dc2705c06fdbe0b02b0a8000028)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 92
 (.branch 90
 (.branch 89
 (.leaf 0x9a26799a659926398a619825f97a5d9725b96a599625795a559525394a519424f93a4d9324b92a499224791a450f03b0e8000028)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 112
 (.branch 104
 (.branch 100
 (.leaf 0x0)
 (.branch 102
 (.branch 101
 (.leaf 0x86a198621785a158521384a118420f83a0d8320b82a098220781a058120380a01801ff7f9fd7f1fb7e9f97e1f70c8310c0000028)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 108
 (.branch 106
 (.branch 105
 (.leaf 0xa86a0a7e9ea769ca6e9aa6698a5e96a5694a4e92a4690a3e8ea368ca2e8aa2688a1e86a1684a0e82a06809fe7e10841100000028)
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
 (.leaf 0x2acaa2a0a7294a4288a12809f2749c2308a21c86210801f87b1e8781a06618c621805c168571585402007010010024)))
 (.branch 134
 (.branch 133
 (.leaf 0x0)
 (.leaf 0x390e3384e0378dd36cda364d8358d5314c3300bf2f4b92dcb42ccb11a865190611805e16458154540380d028010024))
 (.branch 135
 (.leaf 0x5ad6a5a16759564589615815f5755c5314a51d46511404f93b4e9381a4671906217c5d16c58158530781d068010024)
 (.leaf 0x0))))
 (.branch 140
 (.branch 138
 (.branch 137
 (.leaf 0x0)
 (.leaf 0x4751c4691945d16451134491143d0e3f8fc3e4f83d8f23c0ed3b0ea2388922085210821f47c1e47805013040040024))
 (.branch 139
 (.leaf 0x691a3685a06799d66d9a6659865995615836017f5f5795dd745cd712348b2208620c811fc7c1e87709023080040024)
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 152
 (.branch 148
 (.branch 146
 (.branch 145
 (.leaf 0x0)
 (.leaf 0x4c9314bd2e4b12b4a52849d2649123400fb3e8f73d8f43bcee3acea31cc2304be2f4bb2d8b52c8b105c160400a0024))
 (.leaf 0x0))
 (.branch 150
 (.branch 149
 (.leaf 0x7c9f17bdee7b1eb7a5e879de6791e374dd1739cd72dc7715c2705bf318c4304bf2f0ba2e0b52ccb00b82d0a80a0024)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 156
 (.branch 154
 (.branch 153
 (.leaf 0x9e6789da759ce729c26f9ba6d9ae6a96a589565494a4e93249922463fcfd3e8f83d4f33c4ee3b0e90f83d0e8100024)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 176
 (.branch 168
 (.branch 164
 (.branch 162
 (.leaf 0x0)
 (.branch 163
 (.leaf 0x6e5b86d9b56cdb26c1af6b9ad6adaa61d826057e5f57b5d9755c9715394952145511424f53c4e53809c260801a0024)
 (.leaf 0x0)))
 (.branch 166
 (.branch 165
 (.leaf 0x8ae2a8a2278962488a218821f8761c8320a81e06812007f9fb7e9f85354b5214650d414fd3c4e9370d0330c01a0024)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 172
 (.branch 170
 (.branch 169
 (.leaf 0xacab1abeaeab2abaa6a8a9ea6a92a3a4e91a3a8da2e87a1682a067f619846057f5f17a5e1755cd7011043100200024)
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
 (.leaf 0x9023f8f63c8ea398de368d6348ca3183a0982205812027f5fc7e5f8755d073dcc72dc9711c3701bf0dc360c02a0024)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 204
 (.branch 202
 (.branch 201
 (.leaf 0xb1ec6b12c3b06c0afabdaf2bbae6b8a5690a3e8ca2e89a1283a027f9725795a5394a5092e4a91e4611c461003a0024)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 216
 (.branch 212
 (.branch 210
 (.branch 209
 (.leaf 0xb72dbb66d8b5ad5b4ed2b46d0b3acd96e5995a549464f9364a92245751d273dcd729c8719c3705be12c4a0e82a0024)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 240
 (.branch 232
 (.branch 228
 (.branch 226
 (.branch 225
 (.leaf 0xbc6f0bbaedbaeeaba2e7b9ae5b8ee2a5292a3e8da2a88a1a83a067e8360b8220680e017fdfc7e9f713c4e100300024)
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
 (.leaf 0x5b56c5a5685996558d615815e5755b5615654d525413f4f53c4e5371d4731c06e1ac5e170571545407c1d06c020024)
 (.leaf 0x0))))
 (.branch 268
 (.branch 266
 (.branch 265
 (.leaf 0x0)
 (.leaf 0x47d1e46d1a46117455134491043d0d4290841504408f13bcee3ace92689525091240811f87b1e87705413044050024))
 (.branch 267
 (.leaf 0x699a5689a167d9e6719a66597659946458f6318b625785d9755c970264972509223c822007b1e47809423084050024)
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 280
 (.branch 276
 (.branch 274
 (.branch 273
 (.leaf 0x0)
 (.leaf 0x4d1334c12f4b52c4a92849d25491224310741903408f33c0ed3b0e934cce334ca324ba2dcb42ccb0060160440b0024))
 (.leaf 0x0))
 (.branch 278
 (.branch 277
 (.leaf 0x7d1f37c1ef7b5ec7a9e879de5791e277ddd769d975dc6711c3701be348d0334cb320bb2e4b42c8b10bc2d0ac0b0024)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 284
 (.branch 282
 (.branch 281
 (.leaf 0x9ee7a9de769d2739c66f9ba6c9ae6999a649866097a4d92e4a91e4542d0941904404f43c8ed3acea0fc3d0ec110024)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 304
 (.branch 296
 (.branch 292
 (.branch 290
 (.leaf 0x0)
 (.branch 291
 (.leaf 0x6edba6ddb66d1b36c5af6b9ac6ada964d8e6358a6257a5dd745cd705695555151541414f93b4e9370a0260841b0024)
 (.leaf 0x0)))
 (.branch 294
 (.branch 293
 (.leaf 0x8b62c8a62889a2588e218821e8761b8621684e12841ff7f5fc7e5f7565575515253d425013b4e5380d4330c41b0024)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 300
 (.branch 298
 (.branch 297
 (.leaf 0xad2b3ac2afab6acaaaa8a9ea5a92a2a7e9da6a99a5e86a1283a027e649906358b6217b5e5745c97111443104210024)
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
 (.leaf 0x90a418fa3d8ee3a8e2368d6338ca3086a1585211842017f9fb7e9f7785dc76dd875dc8715c2705be0e0360c42b0024)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 332
 (.branch 330
 (.branch 329
 (.leaf 0xb26c8b16c4b0ac1afebdaf2baae6b7a869ca6e98a5e88a1682a067e9a26398a5f97a4f9324992245120461043b0024)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 344
 (.branch 340
 (.branch 338
 (.branch 337
 (.leaf 0xb7addb6ad9b5ed6b52d2b46cfb3acc99e6598a609765093a4991e46781de76dd9759c971dc2701bf1304a0ec2b0024)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 368
 (.branch 360
 (.branch 356
 (.branch 354
 (.branch 353
 (.leaf 0xbcef2bbeeebb2ebba6e7b9ae4b8ee1a829ea6e99a5a89a1e82a027f866178521283e02801fb7e5f81404e104310024)
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
 (.leaf 0x1344c92d4ad2a4a5264952447d1d46116455144451043cf03bcee3b4ec3ace6390df374dc36cd835cd62dcb62d4b42ccb22b4ab298a428ca227c9e2747e1f47c1ec7a1e45a1645815c561541905813034070041))
 (.branch 387
 (.leaf 0x1bb6e5b46c9b16c1ad6b1ab699a467d9d6719b66197659775d9755d1735c96d5ad66591635895f5795d4f93d4f13b4e9392b0aa2a4a728ca22809c26c801fc7c1ec781dc5c16c5815c5414c2909823074070041)
 (.leaf 0x2bcae208811785d0006)))
 (.branch 390
 (.branch 389
 (.leaf 0x2429023b8e6388de348ce328b62b89a2488e2287e1e875fe7f5fc7edfa7e5f47c9ed7adea7a5e6795e4715c470dc2705c05b16a5a56758d625815c56d404fd3c4ed384dce538ce2380dc36cd9354d42e4b82d4b42c4b01785d15855150530e4360cc2d0740d0051)
 (.leaf 0x3a0e72ecba1705b0006))
 (.branch 391
 (.leaf 0x5bd6e50941168590006)
 (.leaf 0x0))))
 (.branch 396
 (.branch 394
 (.branch 393
 (.leaf 0x2c9b1ec2b02bfafabbaeab9ad2b2ab6abaaaa9a9aa5a9285a1283a0a81a027b9e6749ca719c26d9b26b9324b92a4992247695a3689a06719b66595651795e1755d1715c11e4711b46515451124390d3c8f13b8ed3a8e9208811e8791e0771244610c3d08c130051)
 (.leaf 0x485203d0f32007f0006))
 (.branch 395
 (.leaf 0x6a1a75ed7a1f87d0006)
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 408
 (.branch 404
 (.branch 402
 (.branch 401
 (.leaf 0x2deb72d7b56d4b4ed0b3ece9ea789de759c6709ba6a9a64e9364a92646915f37c5f07b9ea7a5e778de271dc670dc26fdbe4cd314c12e4a92949d23488f43ccec3acea3a4bb2e8b32c8b12c04d1283d0b4160041)
 (.leaf 0x4d9353c8f12e4b80006))
 (.leaf 0x0))
 (.branch 406
 (.branch 405
 (.leaf 0x7d9f5725c82dcb60006)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 412
 (.branch 410
 (.branch 409
 (.leaf 0x9f67c9424f3c0ef0006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 432
 (.branch 424
 (.branch 420
 (.branch 418
 (.branch 417
 (.leaf 0x2f3bc6ecbaae9ba2e5b92e3aceb1ac2aeaaaa9a9ea3a8a87a1a83a0a7f9fa2c8aa2989e2388a208721b801ff7f1fb7e1f76e9b86ddb56c5b06b9aa6a57b5e9735c9715c1425053a4e5384dc51138430cc260041)
 (.leaf 0x0))
 (.branch 419
 (.leaf 0x6f5bc5e5785013f0006)
 (.leaf 0x0)))
 (.branch 422
 (.branch 421
 (.leaf 0x8be2e80a014f93d0006)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 428
 (.branch 426
 (.branch 425
 (.leaf 0xadab5a26885dd760006)
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
 (.leaf 0x2f2bc2efbb6e9ba2e6b8ae1b76dbb6ad8b52d3b46cdb32c8b1ac5b0ebfafabcae2b7a2688a06809fe7e9424f9224791a459063f8fa3c8e2378d6318c202805fa7e5f87ddc9721c1701bf6f8521384a118360041)
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
 (.leaf 0xb2ecaa1e8693a4d0006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 472
 (.branch 468
 (.branch 466
 (.branch 465
 (.leaf 0xb82df9324b715c40006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 496
 (.branch 488
 (.branch 484
 (.branch 482
 (.branch 481
 (.leaf 0xbd6f4a16847f9fd0006)
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
 (.leaf 0x5bd6e5a5675996458d6257d5e5715b55d555515153d4b52548515431d8741bc6d1b06a1a0631846007c1e070030024)
 (.leaf 0x0))))
 (.branch 524
 (.branch 522
 (.branch 521
 (.leaf 0x0)
 (.leaf 0x4852046d194611645514445104390d4250741903404fd3ecfa3dcf52649624c9223c8d228872188305414048060024))
 (.branch 523
 (.leaf 0x6a1a7689a067d9d6719b66197655946418e6358a62184609815f97c2689824c912408e230872148409424088060024)
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 536
 (.branch 532
 (.branch 530
 (.branch 529
 (.leaf 0x0)
 (.leaf 0x4d9354c12e4b52b4a9294992548d2242d0841504404ff3f0f93e0f5348cf330cb320c630cc02fcbc060170480c0024))
 (.leaf 0x0))
 (.branch 534
 (.branch 533
 (.leaf 0x7d9f57c1ee7b5eb7a9e9799e578de2779dc76dd8759d2741cf731ca34cd1330ca324c7314c02f8bd0bc2e0b00c0024)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 540
 (.branch 538
 (.branch 537
 (.leaf 0x9f67c9de759d2729c6709b66c9aa699966398a5f9765995e5694e514310a41503409003f8f93dcf60fc3e0f0120024)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 560
 (.branch 552
 (.branch 548
 (.branch 546
 (.leaf 0x0)
 (.branch 547
 (.leaf 0x6f5bc6ddb56d1b26c5b06b5ac6a9a96498f6318b6218660d805fd7c5655654d5253d4d52947519430a0270881c0024)
 (.leaf 0x0)))
 (.branch 550
 (.branch 549
 (.leaf 0x8be2e8a62789a2488e2287e1e8721b85e158521183e0b82608816035695854d515414e53147515440d4340c81c0024)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 556
 (.branch 554
 (.branch 553
 (.leaf 0xadab5ac2aeab6abaaaa9a9aa5a8ea2a7a9ca6e98a5a92a428fa328a64d916318a62587615805f97d11444108220024)
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
 (.leaf 0x912438fa3c8ee398e2378d2338c6308661684e1283e0d82a0781a03781dd769d9759d4745ce735ca0e0370c82c0024)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 588
 (.branch 586
 (.branch 585
 (.leaf 0xb2ecab16c3b0ac0afebeaeebaae2b7a829da6a99a5a94a468ea368a99e64986609765b9625595251120471083c0024)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 600
 (.branch 596
 (.branch 594
 (.branch 593
 (.leaf 0xb82dfb6ad8b5ed5b52d3b42cfb36cc9a2669865f97a5c96a5594e52785df769d875dd574dce731cb1304b0f02c0024)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 624
 (.branch 616
 (.branch 612
 (.branch 610
 (.branch 609
 (.leaf 0xbd6f4bbeedbb2eaba6e8b96e4b8ae1a869fa6a98a5e95a4e8ea328b86a1884e118420e83207816041404f108320024)
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
 (.leaf 0x1364c52d4b12a4a127495234851c461174551344910438fc3ecfa3e4f83dce838cdf378dc368d935cd530cc2304c02fcbe2bcaa298a528ca12809e2708a2248821c86214661946418c621841905c14038080041))
 (.branch 643
 (.leaf 0x1bd6e1b46cdb16bdae6b1aa6a1a367d9e6719a6659765583609816017f5f96f5a96659563585605795c5294952147519452b8ab2a4a828ca127c9d26c8c22c8821c8420c6819c6418c6017c2909c24078080041)
 (.leaf 0x2b4ac2388d1a8690006)))
 (.branch 646
 (.branch 645
 (.leaf 0x2448fe3b8ea388da358ce318be2a89a2588e218821e8720a8260881e06815f67c5ed7b1ea7a1e7795e3745d073dce735cc5b96b5a56858d6157d5d56d4c52d4851d4450ce7390e2384dc368d8358d4314c4304c02f4bc1a869188611805f0e4370d02e0780e0051)
 (.leaf 0x398e531cc61a0670006))
 (.branch 647
 (.leaf 0x5b56c5394d198650006)
 (.leaf 0x0))))
 (.branch 652
 (.branch 650
 (.branch 649
 (.leaf 0x2cbb1ac2b06bfaf6bcaeab8adab1ab6acaaaa8a9ea5a8e91a428fa3a8da327d9e2749ce719be6e9b26a9625795a559525369da4689a16719a6619665185611816017d5f1204751b4691544d1143d0d3f8fd3e8f93d8f52388d2188521083124471103e090140051)
 (.leaf 0x47d1e400ff2308b0006))
 (.branch 651
 (.leaf 0x699a561d86228890006)
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 664
 (.branch 660
 (.branch 658
 (.branch 657
 (.leaf 0x2e0b6ed7b5ad4b4ad1b3ecd9f2799de769c66f9b66b9a65a9665695652945f57c9f07bdea7a1e6791e274dd273dce72dca4d5324c12f4a92849924489003fcf83dcf63d4c7318bf2f8bd2f04d12c3e0b8170041)
 (.leaf 0x4d1333f8fd314c40006))
 (.leaf 0x0))
 (.branch 662
 (.branch 661
 (.leaf 0x7d1f3755d430cc20006)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 668
 (.branch 666
 (.branch 665
 (.leaf 0x9ee7a9725b3f0fb0006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 688
 (.branch 680
 (.branch 676
 (.branch 674
 (.branch 673
 (.leaf 0x2f5bc2ecbaee9b9ee6b92e2ad6b2ac2afaaaa8a9aa4a8a93a4a8fa3a8ba2a2e8ae298a2238861f8761b8320b82207812036f1b96ddb66c5af6b5ab6a5876197f5f97d5f14e535465154450c5113c440d0270041)
 (.leaf 0x0))
 (.branch 675
 (.leaf 0x6edba615845314b0006)
 (.leaf 0x0)))
 (.branch 678
 (.branch 677
 (.leaf 0x8b62c83a0d529490006)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 684
 (.branch 682
 (.branch 681
 (.leaf 0xad2b3a569460d820006)
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
 (.leaf 0x2f4bc6efbbae9b9ee5b8ee1b7edcb6ad9b52d2b42ceb32cab1ec5b12bfaf6bbae6b7a5694a368ca2e8a9725b9525394a5190e408fa3d8e2368d2328c20e836068160480dd5751cd731cb7285213c4b11c370041)
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
 (.leaf 0xb26c8a4e9296a590006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 728
 (.branch 724
 (.branch 722
 (.branch 721
 (.leaf 0xb7add96257745d00006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 752
 (.branch 744
 (.branch 740
 (.branch 738
 (.branch 737
 (.leaf 0xbcef2a469082a090006)
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
 (.leaf 0x1354cd2c4ad294a127499224811e45d1645113449114350841d064150440ce7394de374db368d9360d433cce334cc32cca2b8ac294a4288a12809f26c962549424c92244721c4701bc6e1b4190601503c090041))
 (.branch 771
 (.leaf 0x1bc6e9b36c9b06bdae6b5a969da56799d66d9a665986518f6398d6318b6296e5b165591625856057d5b5595555153549512bcad2a0a7288a12789d2709825c9424c9023c741cc701bc6c1ac290a02507c090041)
 (.leaf 0x2acaa268991d8750006)))
 (.branch 774
 (.branch 773
 (.leaf 0x2439063a8e6378da358d2308ba2c8962488a218821f86e168561484e12845f57cdec7ade97a1e7799e2775dc76dda765d85bd6d5a167589615795d5715855d5454d5053ce8398e1380db368d7358d5344d0334cc324c81d8751b86d1b06b0e4380d42f07c0f0051)
 (.leaf 0x390e334cd21d0730006))
 (.branch 775
 (.leaf 0x5ad6a569591c8710006)
 (.leaf 0x0))))
 (.branch 780
 (.branch 778
 (.branch 777
 (.leaf 0x2cab22c1b02beaf6bcaeeb7ad6b3ab2abaa6a8a9ea6a8a9da729ba6a99a627c9ea739ca709be6e9b6699926398a619825f6a1a6685a066d9a65d96655916418d631896212147d1a4651444d1043d0e42909419054090126899248912408f124481143f094150051)
 (.leaf 0x4751c4310b260970006))
 (.branch 779
 (.leaf 0x691a364d92258950006)
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 792
 (.branch 788
 (.branch 786
 (.branch 785
 (.leaf 0x2dfb76d6b56d3b4ad1b42cc9f67b9da759c26f9b26b9aa66996629865e975f67d1ef7b9e97a1e5791e377dde76dda75dd64d9344bd2e4a5284952448d0c42d0440d02404d3348cb328c93204d1303f0bc180041)
 (.leaf 0x4c93142909344d00006))
 (.leaf 0x0))
 (.branch 790
 (.branch 789
 (.leaf 0x7c9f1785e033cce0006)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 796
 (.branch 794
 (.branch 793
 (.leaf 0x9e6789a267421070006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 816
 (.branch 808
 (.branch 804
 (.branch 802
 (.branch 801
 (.leaf 0x2f4bcaebbaae8b9ee6b96e1adab4abeaeaa6a8a96a4a8e9fa7a9ba6a97a5a2f8b62889e228861e8761c86217852138420f6f5bb6d9b56c1af6b1ab6a9936498b629896215a565525455053c51140450d4280041)
 (.leaf 0x0))
 (.branch 803
 (.leaf 0x6e5b864590561570006)
 (.leaf 0x0)))
 (.branch 806
 (.branch 805
 (.leaf 0x8ae2a86a19559550006)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 812
 (.branch 810
 (.branch 809
 (.leaf 0xacab1a86a063d8e0006)
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
 (.leaf 0x2f5bceeebb6e8b9ee4b8ee2b82deb66d8b4ed2b3eceb36cbb26c4b0ebeaf6baae6b8a86a0a6698a5e969a2679825f97a5d912428f63c8de368ce328c61a866128461083de1781d9761d7758521404c120380041)
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
 (.leaf 0xb1ec6a7e9e99a650006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 856
 (.branch 852
 (.branch 850
 (.branch 849
 (.leaf 0xb72db99263775dc0006)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 880
 (.branch 872
 (.branch 868
 (.branch 866
 (.branch 865
 (.leaf 0xbc6f0a769c85a150006)
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
 (.leaf 0x2f5bd2f3bcaf1bc2e6b96e4b8ee2b86e0b7edeb76dcb6ed1b42cfb3acdb32cbb2ac9b22c7b1abcaeebaae6b8adeb6ad6b4aceb2ac6a7a9aa5a92a3a8a7d9f27b9ea799e26e9b66c9ae6a9a64490e42906408fe358d2338ca318c22f8ba2d8b22b8aa2087e1e8761c86df67d5f47cdf27c5e7799e5791e3789bd6f1bb6e9b96e1ae6b5ac6adaa6a5a869da6695a468d9966197659956516f5b96d5b16b5a96057d5e5755c56d364d5344cd324c5274992549123489214811f4791d471124451043d0e434e839ce6394e438cd9360d7358d5350af2b8ad2b0ab2a8a027c9e2749c26c521444d124390a41900bb)
 (.leaf 0x4c12f4b91b46919388e1380a92a0a7000c))
 (.branch 899
 (.leaf 0x6ddb66d5a2685a05a56859ca6294a4000c)
 (.leaf 0x0)))
 (.branch 902
 (.branch 901
 (.leaf 0x23e8f63c8a62889df07bdee59965590df378dd000f)
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 908
 (.branch 906
 (.branch 905
 (.leaf 0x2c5b12c3ac2afaba779da7567d9e6751845d16000f)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 920
 (.branch 916
 (.branch 914
 (.branch 913
 (.leaf 0xb6ad9b62749ce727b5ec7ad2d4b12b000c)
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 944
 (.branch 936
 (.branch 932
 (.branch 930
 (.branch 929
 (.leaf 0xbbeeebb6adab2ab89a25891b46cdb2000c)
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
 (.leaf 0xbb2ebbaad7b5ad5b0ac1b023b8ea39000c)
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
 (.leaf 0x2e9ba2e7b9ae5b92e3b8ae1b52d3b4ad1b42cfb3acdb32bfafabdaf2bbaeab9ae2b7aaaa9aa2a7a9aa5a92a3a8a9ba6a99a6297a5a8fa3a8da328ba2a83a0a81a027f9fa719c26f9ba6d9b26b9aa6998a619825f97a5d95a559525394a5192a499224791a458e2378da358d2338ca318c22388a218821f87a1d8721b8521384a118420f8220781a05812037f1fb7e9f97e1f77a9e97a1e7799e5791e3789db769d9761d7759cf739cd731cb729c3709c1701bf6f9b16c1af6b9ad6b1ab6a9a96719b6699966197659956518d6318b62989621816017f5f97d5f1755d1735c9715c163589615815f5795d5715b55153549515414f5214751945511434f13b4e9394e1374a9294a12749925491234891545113449114410f4390d4190541103409013e8f93e0f73d8f53b8ed3b0eb3a8e9370db368d9360d7358d5350cd330cb328c9320c1300bf2f8bd2f0b52d0b32c8b12c0a3288a12809f2789d2709b25093248912408f2208721885210831f07b1e8791e0771c06f1b86d1b06b19063188611805f160571585515053013b)
 (.branch 4
 (.leaf 0xbd6f4bcef2bc6f0bbeeebb6ecbaeeab82dfb7addb72dbb6ad9b62d7b5ad5b2ecab26c8b1ec6b16c4b0ec2b06c0adab5ad2b3acab1ac2afabaadab2aba86a0a7e9ea769ca5694a4e92a4690a2688a1e86a16849f67c9ee7a9e6789de769d6749ce729a26799a65992639725b96a59962579424f93a4d9324b9124390a419023f8fa3d8f23b8ea398be2e8b62c8ae2a8a62889e268962486a198621785a1583a0d8320b82a0980a01801ff7f9fd7d9f57d1f37c9f17c1ef7b9ed7b1eb785e077dde775dc755d474dd2745d0725c871dc6715c46f5bc6edba6e5b86ddb66d5b46cdb26a1a7699a5691a3689a16819f6799d64d926459063d8e61d866158460d825ed7a5e5785dd765bd6e5b56c5ad6a5a56859d66595645695956157559555394d5314b52949509415013f4f93d4d9354d1334c9314c12f4b92d4b12b4852047d1e4751c46d1a4651845d164310b4290942107400ff3f8fd3f0fb3d0f33c8f13c0ef3a0e7398e5390e3388e1380df378dd34cd2344d033cce31cc6314c430cc22ecba2e4b82dcb62bcae2b4ac2acaa2a4a829ca6294a42689926097258952388d2308b22889208812007f1f87d1d8751d0731c8711a8691a067198651785d1705b168590168)
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
 (.leaf 0x3fe001ff000ff8007fc0fc0fc0fc003fe07e07e07e001ff000ff81f81f81f8007fc0fc0fc0fc003fe001ff03f03f03f000ff81f81f81f8007fc003fe07e07e07e001ff03f03f03f000ff81f81f81f81f81f81f800000000000000000000)
 (.branch 4
 (.leaf 0x3ffc01ffe00fff007ff803f03f03f03ffc01f81f81f81ffe00fff007e07e07e07ff803f03f03f03ffc01ffe00fc0fc0fc0fff007e07e07e07ff803ffc01f81f81f81ffe00fc0fc0fc0fff007e07e07e07e07e07e0000000000000000000000)
 (.leaf 0x0))))
def kindMasks := kindMaskTable.get
def keys := List.range 5
def vertexMaskTable : Table Nat :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf 4171849679533027504677776769862406473833407270227837441302815640277763230508756657230267285503)
 (.leaf 181709681073901722637330951972001133588406168322149982042867872018389959621875647520058506145117642221947041815887546589067946527556607))
 (.branch 3
 (.leaf 7914572847139345089936080672628710081124021461557704975527380464621966103465532641277810357689749841447742091961305103573550440359966102952017527108423289479352613103315516431)
 (.branch 4
 (.leaf 344728266443874206170545512964432112225499154744972382710989401182839801753932364554870097988538727997280343734297151026350384070729206362162389800896219122958929939674342233399637220121866485493314173569983068438641)
 (.leaf 722947228701037235344765693060012378740239924723680248553714565962799609701344645033070339087601298370135845909843019508308938517880512507776580078041606429811370292307634172785717162138539380238555127869071373485723819009))))
 (.branch 7
 (.branch 6
 (.leaf 1516130226564837640342125309653185718193990512578377816449793178309497256060509561429158186529099468558951048160139347040953103561575605844410725346791314027185166061170420686833639733969943497163208000783024970259746911326044161)
 (.leaf 1516130949512411069317046113160408948893641197895882275652478442154925144804330138148628998197264017802459079302117307986986536396814160193460178629596459358628514618373619567395038617645266539234589138689754527152291380228784129))
 (.branch 8
 (.leaf 1516130949512411069481425203338665944032828460066725006354404704766546245173276953356376990526144288559961841174614372696484000238387073503806866755891166776624114843011146454620301621569078813815142486034329614638389531399251346)
 (.branch 9
 (.leaf 1516130949512411069481425281682531060624989952191348302130919696363057993556444832116409305141355061282809414417770993684986548399184768985803664832795064287143112712002902931498972781544180481020164176845851922638547398609775268)
 (.leaf 1516130949512411069481425281701657980819470460368136540240240134593428235682514941461809703655665415475368703376082311219407569529106838735677199207325558402746266764217012247045085738370346277325634152844907535883544974914278216)))))
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
 (.leaf (.leaf 0))))
 (.branch 24
 (.branch 20
 (.branch 18
 (.branch 17
 (.leaf (.leaf 0))
 (.leaf (.leaf 7)))
 (.leaf (.leaf 0)))
 (.branch 22
 (.branch 21
 (.leaf (.leaf 8))
 (.leaf (.leaf 9)))
 (.leaf (.leaf 0))))
 (.branch 28
 (.branch 26
 (.branch 25
 (.leaf (.leaf 10))
 (.leaf (.leaf 11)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 48
 (.branch 40
 (.branch 36
 (.branch 34
 (.leaf (.leaf 0))
 (.branch 35
 (.leaf (.leaf 12))
 (.leaf (.leaf 0))))
 (.branch 38
 (.branch 37
 (.leaf (.leaf 13))
 (.leaf (.leaf 0)))
 (.branch 39
 (.leaf (.leaf 14))
 (.leaf (.leaf 0)))))
 (.branch 44
 (.branch 42
 (.branch 41
 (.leaf (.leaf 15))
 (.leaf (.leaf 0)))
 (.branch 43
 (.leaf (.leaf 16))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0))))
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
 (.leaf (.leaf 0))))
 (.branch 88
 (.branch 84
 (.branch 82
 (.branch 81
 (.leaf (.leaf 19))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 86
 (.branch 85
 (.leaf (.leaf 20))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 92
 (.branch 90
 (.branch 89
 (.leaf (.leaf 21))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 112
 (.branch 104
 (.branch 100
 (.branch 98
 (.branch 97
 (.leaf (.leaf 22))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 102
 (.branch 101
 (.leaf (.leaf 23))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 108
 (.branch 106
 (.branch 105
 (.leaf (.leaf 24))
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
 (.leaf (.leaf 0))))
 (.branch 152
 (.branch 148
 (.branch 146
 (.branch 145
 (.leaf (.leaf 34))
 (.leaf (.leaf 35)))
 (.leaf (.leaf 0)))
 (.branch 150
 (.branch 149
 (.leaf (.leaf 36))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 156
 (.branch 154
 (.branch 153
 (.leaf (.leaf 37))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
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
 (.branch 166
 (.branch 165
 (.leaf (.leaf 40))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 172
 (.branch 170
 (.branch 169
 (.leaf (.leaf 41))
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
 (.leaf (.leaf 0))))
 (.branch 280
 (.branch 276
 (.branch 274
 (.branch 273
 (.leaf (.leaf 56))
 (.leaf (.leaf 57)))
 (.leaf (.leaf 0)))
 (.branch 278
 (.branch 277
 (.leaf (.leaf 58))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 284
 (.branch 282
 (.branch 281
 (.leaf (.leaf 59))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
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
 (.branch 294
 (.branch 293
 (.leaf (.leaf 62))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 300
 (.branch 298
 (.branch 297
 (.leaf (.leaf 63))
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
 (.leaf (.leaf 0))))
 (.branch 408
 (.branch 404
 (.branch 402
 (.branch 401
 (.leaf (.leaf 84))
 (.leaf (.branch 0x1000000000000000000000000000100000000000000000000000000000000000200000000000000000000000000020000 (.leaf 85) (.leaf 86))))
 (.leaf (.leaf 0)))
 (.branch 406
 (.branch 405
 (.leaf (.branch 0x1000000000000000000000000000100000000000000000000000000000000001000000000000000000000000000100000 (.leaf 87) (.leaf 88)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 412
 (.branch 410
 (.branch 409
 (.leaf (.branch 0x1000000000000000000000000000100000000000000000000000000000000010000000000000000000000000001000000 (.leaf 89) (.leaf 90)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
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
 (.branch 422
 (.branch 421
 (.leaf (.branch 0x1000000000000000000000001000000000000000000000000000000000000001000000000000000000000001000000000 (.leaf 94) (.leaf 95)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 428
 (.branch 426
 (.branch 425
 (.leaf (.branch 0x1000000000000000000000001000000000000000000000000000000000000010000000000000000000000010000000000 (.leaf 96) (.leaf 97)))
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
 (.leaf (.leaf 0))))
 (.branch 536
 (.branch 532
 (.branch 530
 (.branch 529
 (.leaf (.leaf 116))
 (.leaf (.leaf 117)))
 (.leaf (.leaf 0)))
 (.branch 534
 (.branch 533
 (.leaf (.leaf 118))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 540
 (.branch 538
 (.branch 537
 (.leaf (.leaf 119))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
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
 (.branch 550
 (.branch 549
 (.leaf (.leaf 122))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 556
 (.branch 554
 (.branch 553
 (.leaf (.leaf 123))
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
 (.leaf (.leaf 0))))
 (.branch 664
 (.branch 660
 (.branch 658
 (.branch 657
 (.leaf (.leaf 144))
 (.leaf (.branch 0x10000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000020000 (.leaf 145) (.leaf 146))))
 (.leaf (.leaf 0)))
 (.branch 662
 (.branch 661
 (.leaf (.branch 0x10000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000100000 (.leaf 147) (.leaf 148)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 668
 (.branch 666
 (.branch 665
 (.leaf (.branch 0x10000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000001000000 (.leaf 149) (.leaf 150)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
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
 (.branch 678
 (.branch 677
 (.leaf (.branch 0x10000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000001000000000 (.leaf 154) (.leaf 155)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 684
 (.branch 682
 (.branch 681
 (.leaf (.branch 0x10000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000010000000000 (.leaf 156) (.leaf 157)))
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
 (.leaf (.leaf 0))))
 (.branch 792
 (.branch 788
 (.branch 786
 (.branch 785
 (.leaf (.leaf 182))
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000020000 (.leaf 183) (.leaf 184))))
 (.leaf (.leaf 0)))
 (.branch 790
 (.branch 789
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000100000 (.leaf 185) (.leaf 186)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 796
 (.branch 794
 (.branch 793
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000001000000 (.leaf 187) (.leaf 188)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
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
 (.branch 806
 (.branch 805
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000001000000000 (.leaf 192) (.leaf 193)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 812
 (.branch 810
 (.branch 809
 (.leaf (.branch 0x1000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000010000000000 (.leaf 194) (.leaf 195)))
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

end Papers.RationalityTen.RootedCaches.RootedSevenPure033

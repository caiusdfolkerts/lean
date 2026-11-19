module
prelude
public meta import CertificateNumbers
public import RootedSixExtra06
public import SignatureCompatibility
public import PackedRawNatGrowth
public import FiniteChecks
public import RawFacetEmbedding
public import RootedSixExtra06GrowthCachecandidateMasksData000
public import RootedSixExtra06GrowthCachecandidateMasksData001
public import RootedSixExtra06GrowthCachecandidateMasksData002
public import RootedSixExtra06GrowthCachecandidateMasksData003
public import RootedSixExtra06GrowthCachebadMasksData000
public import RootedSixExtra06GrowthCachebadMasksData001
public import RootedSixExtra06GrowthCachebadMasksData002
public import RootedSixExtra06GrowthCachebadMasksData003
public import RootedSixExtra06GrowthCachebadMasksData004
public import RootedSixExtra06GrowthCachebadMasksData005
public import RootedSixExtra06GrowthCachebadMasksData006
public import RootedSixExtra06GrowthCachebadMasksData007
public import RootedSixExtra06GrowthCachebadMasksData008
public import RootedSixExtra06GrowthCachesignatureMasksData000
public import RootedSixExtra06GrowthCachesignatureMasksData001
public import RootedSixExtra06GrowthCachesignatureMasksData002
public import RootedSixExtra06GrowthCachesignatureMasksData003

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra06
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def rawCells := Papers.RationalityTen.FacetUniverses.RootedSixExtra06.rawCells
def cells (c : Fin 2300) := rawCells c.val
def ridgeList := ConcreteGrowth.ridgeList cells
def literalCompatible (a b : Fin 2300) := ConcreteGrowth.compatible (cells a) (cells b)
def kind (c : Fin 2300) := (cells c).kind
def rawKindCode : Nat := 1994659866604506756751036595747792104972204447817096288132453466037269923743224053072139514507432940561995026209145773537468422590671782605457733746984145092719031897688997120899964415372275317954487163492512117588497495817423472545604953317801292128321856959221351930218351544775675939340871533545031689722222345023802799241515274200639113821454193136632343316846006981622451160853020290576623568874596457549800616848164706894594288415482929294422252935652820647229901030089651343277419407070601362969109966520463825178112849232167429853534881232864173618130081827351050745725693316559880853639614432301684244944413839151779395721177619687583443888372962668472819800731148582030377581658247736777253561956164708817957528770579001488978320181116299293160352081373018931685752874106376114319523654941389992103588720192499670327169681878687822486939883420806394109079586996497084079938366555563722780329519135629057410627432949612783045725713337333804671478325352172281179327966140730869973406480704894575994165431822704946726494188621988508398259001483655934848173065847437250901542208669719269244801016477369832734180265458950272164708446256535004926527751342515769384958074077827649791015436501343905531535908207652488490622447119868069397279496805975055240929761456279067411012939302431518873831110500421686274507563282819938449593108775312000956450584124303166245534146451558065932236821701274903024112957774398008969106368237724699345704721067024086486809176569902196115126750737501659548668289078122655781681025514049981401386029925590279889783185235013336765976967069563172265177911586047077831594935710164949364890284227440344856520010705812239009242902870719082585469474132096871693073294923121262860835712130121667760761318533972438491772160357010452941029209167046404911467077617962329014098478715074824205341011693325261530335044271109705794062871032361671773118101404167464193784402517606166457158372988270766728968561024538551755289860133305522682011019310683988761041950203110677892434180460004149725746780936637671798384295175908409722815853745612100082241696411684650577229598508836731167550012042828710169808605591173192350294575171743011481524800578572969685056572084466038038765805417088822883957866269693340935717016412497469311377085707110357502202479945846600255844740336398535259394429466668888382500375721431155691391060792823985161826444332991395815688571680111344158709548367367224961157712682604394944774463807671561976040518308757911398238241935473841629273482702773813676777162236091371506013488083677925829310959676563838570652347971127009958849461449257628915074704972390252973913072634353915961641978616017842691468672380287003125865792156207640808200078284958507740491195007290093209345301839571517444997436925218501295227528787778408720
def rawKind (i : Nat) := PackedRawNatGrowth.take 4
  (PackedRawNatGrowth.drop (4*i) rawKindCode)
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
 (.leaf (certNat% 0)))))
 (.branch 12
 (.leaf 0x0)
 (.branch 14
 (.leaf 0x0)
 (.branch 15
 (.leaf (certNat% 1))
 (.leaf 0x0)))))
 (.branch 24
 (.leaf 0x0)
 (.branch 28
 (.leaf 0x0)
 (.branch 30
 (.branch 29
 (.leaf (certNat% 2))
 (.leaf 0x0))
 (.leaf 0x0)))))
 (.branch 48
 (.branch 40
 (.branch 36
 (.leaf 0x0)
 (.branch 38
 (.branch 37
 (.leaf 0x0)
 (.leaf (certNat% 3)))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 56
 (.branch 52
 (.leaf 0x0)
 (.branch 54
 (.branch 53
 (.leaf (certNat% 4))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 60
 (.branch 58
 (.leaf 0x0)
 (.branch 59
 (.leaf 0x0)
 (.leaf (certNat% 5))))
 (.leaf 0x0)))))
 (.branch 96
 (.branch 80
 (.branch 72
 (.branch 68
 (.branch 66
 (.leaf 0x0)
 (.branch 67
 (.leaf 0x0)
 (.leaf (certNat% 6))))
 (.branch 70
 (.branch 69
 (.leaf 0x0)
 (.leaf (certNat% 7)))
 (.branch 71
 (.leaf (certNat% 8))
 (.leaf 0x0))))
 (.branch 76
 (.branch 74
 (.leaf 0x0)
 (.branch 75
 (.leaf (certNat% 9))
 (.leaf 0x0)))
 (.branch 78
 (.branch 77
 (.leaf (certNat% 10))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 88
 (.branch 84
 (.leaf 0x0)
 (.branch 86
 (.branch 85
 (.leaf (certNat% 11))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 92
 (.branch 90
 (.branch 89
 (.leaf (certNat% 12))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 112
 (.branch 104
 (.branch 100
 (.branch 98
 (.branch 97
 (.leaf 0x0)
 (.leaf (certNat% 13)))
 (.leaf 0x0))
 (.branch 102
 (.branch 101
 (.leaf (certNat% 14))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 120
 (.branch 116
 (.branch 114
 (.branch 113
 (.leaf (certNat% 15))
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
 (.leaf (certNat% 16))))
 (.branch 134
 (.branch 133
 (.leaf 0x0)
 (.leaf (certNat% 17)))
 (.branch 135
 (.leaf (certNat% 18))
 (.leaf 0x0))))
 (.branch 140
 (.branch 138
 (.leaf 0x0)
 (.branch 139
 (.leaf (certNat% 19))
 (.leaf 0x0)))
 (.branch 142
 (.branch 141
 (.leaf (certNat% 20))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 152
 (.branch 148
 (.leaf 0x0)
 (.branch 150
 (.branch 149
 (.leaf (certNat% 21))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 156
 (.branch 154
 (.branch 153
 (.leaf (certNat% 22))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 176
 (.branch 168
 (.branch 164
 (.branch 162
 (.branch 161
 (.leaf 0x0)
 (.leaf (certNat% 23)))
 (.leaf 0x0))
 (.branch 166
 (.branch 165
 (.leaf (certNat% 24))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 184
 (.branch 180
 (.branch 178
 (.branch 177
 (.leaf (certNat% 25))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 224
 (.branch 208
 (.branch 200
 (.branch 196
 (.branch 194
 (.branch 193
 (.leaf 0x0)
 (.leaf (certNat% 26)))
 (.branch 195
 (.leaf (certNat% 27))
 (.leaf (certNat% 28))))
 (.branch 198
 (.branch 197
 (.leaf (certNat% 29))
 (.leaf (certNat% 30)))
 (.branch 199
 (.leaf (certNat% 31))
 (.leaf 0x0))))
 (.branch 204
 (.branch 202
 (.branch 201
 (.leaf (certNat% 32))
 (.leaf 0x0))
 (.branch 203
 (.leaf (certNat% 33))
 (.leaf 0x0)))
 (.branch 206
 (.branch 205
 (.leaf (certNat% 34))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 216
 (.branch 212
 (.branch 210
 (.branch 209
 (.leaf (certNat% 35))
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 214
 (.branch 213
 (.leaf (certNat% 36))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 220
 (.branch 218
 (.branch 217
 (.leaf (certNat% 37))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 240
 (.branch 232
 (.branch 228
 (.branch 226
 (.branch 225
 (.leaf (certNat% 38))
 (.leaf (certNat% 39)))
 (.leaf 0x0))
 (.branch 230
 (.branch 229
 (.leaf (certNat% 40))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 248
 (.branch 244
 (.branch 242
 (.branch 241
 (.leaf (certNat% 41))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))))
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
 (.leaf (certNat% 42))))
 (.branch 262
 (.branch 261
 (.leaf 0x0)
 (.leaf (certNat% 43)))
 (.branch 263
 (.leaf (certNat% 44))
 (.leaf 0x0))))
 (.branch 268
 (.branch 266
 (.leaf 0x0)
 (.branch 267
 (.leaf (certNat% 45))
 (.leaf 0x0)))
 (.branch 270
 (.branch 269
 (.leaf (certNat% 46))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 280
 (.branch 276
 (.leaf 0x0)
 (.branch 278
 (.branch 277
 (.leaf (certNat% 47))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 284
 (.branch 282
 (.branch 281
 (.leaf (certNat% 48))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 304
 (.branch 296
 (.branch 292
 (.branch 290
 (.branch 289
 (.leaf 0x0)
 (.leaf (certNat% 49)))
 (.leaf 0x0))
 (.branch 294
 (.branch 293
 (.leaf (certNat% 50))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 312
 (.branch 308
 (.branch 306
 (.branch 305
 (.leaf (certNat% 51))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 352
 (.branch 336
 (.branch 328
 (.branch 324
 (.branch 322
 (.branch 321
 (.leaf 0x0)
 (.leaf (certNat% 52)))
 (.branch 323
 (.leaf (certNat% 53))
 (.leaf (certNat% 54))))
 (.branch 326
 (.branch 325
 (.leaf (certNat% 55))
 (.leaf (certNat% 56)))
 (.branch 327
 (.leaf (certNat% 57))
 (.leaf 0x0))))
 (.branch 332
 (.branch 330
 (.branch 329
 (.leaf (certNat% 58))
 (.leaf 0x0))
 (.branch 331
 (.leaf (certNat% 59))
 (.leaf 0x0)))
 (.branch 334
 (.branch 333
 (.leaf (certNat% 60))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 344
 (.branch 340
 (.branch 338
 (.branch 337
 (.leaf (certNat% 61))
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 342
 (.branch 341
 (.leaf (certNat% 62))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 348
 (.branch 346
 (.branch 345
 (.leaf (certNat% 63))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 368
 (.branch 360
 (.branch 356
 (.branch 354
 (.branch 353
 (.leaf (certNat% 64))
 (.leaf (certNat% 65)))
 (.leaf 0x0))
 (.branch 358
 (.branch 357
 (.leaf (certNat% 66))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 376
 (.branch 372
 (.branch 370
 (.branch 369
 (.leaf (certNat% 67))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))))
 (.branch 448
 (.branch 416
 (.branch 400
 (.branch 392
 (.branch 388
 (.branch 386
 (.branch 385
 (.leaf 0x0)
 (.leaf (certNat% 68)))
 (.branch 387
 (.leaf (certNat% 69))
 (.leaf (certNat% 70))))
 (.branch 390
 (.branch 389
 (.leaf (certNat% 71))
 (.leaf (certNat% 72)))
 (.branch 391
 (.leaf (certNat% 73))
 (.leaf 0x0))))
 (.branch 396
 (.branch 394
 (.branch 393
 (.leaf (certNat% 74))
 (.leaf 0x0))
 (.branch 395
 (.leaf (certNat% 75))
 (.leaf 0x0)))
 (.branch 398
 (.branch 397
 (.leaf (certNat% 76))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 408
 (.branch 404
 (.branch 402
 (.branch 401
 (.leaf (certNat% 77))
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 406
 (.branch 405
 (.leaf (certNat% 78))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 412
 (.branch 410
 (.branch 409
 (.leaf (certNat% 79))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 432
 (.branch 424
 (.branch 420
 (.branch 418
 (.branch 417
 (.leaf (certNat% 80))
 (.leaf (certNat% 81)))
 (.leaf 0x0))
 (.branch 422
 (.branch 421
 (.leaf (certNat% 82))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 440
 (.branch 436
 (.branch 434
 (.branch 433
 (.leaf (certNat% 83))
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
 (.leaf (certNat% 84))
 (.leaf (certNat% 85)))
 (.branch 451
 (.leaf (certNat% 86))
 (.leaf (certNat% 87))))
 (.branch 454
 (.branch 453
 (.leaf (certNat% 88))
 (.leaf (certNat% 89)))
 (.branch 455
 (.leaf (certNat% 90))
 (.leaf 0x0))))
 (.branch 460
 (.branch 458
 (.branch 457
 (.leaf (certNat% 91))
 (.leaf 0x0))
 (.branch 459
 (.leaf (certNat% 92))
 (.leaf 0x0)))
 (.branch 462
 (.branch 461
 (.leaf (certNat% 93))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 472
 (.branch 468
 (.branch 466
 (.branch 465
 (.leaf (certNat% 94))
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 470
 (.branch 469
 (.leaf (certNat% 95))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 476
 (.branch 474
 (.branch 473
 (.leaf (certNat% 96))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 496
 (.branch 488
 (.branch 484
 (.branch 482
 (.branch 481
 (.leaf (certNat% 97))
 (.leaf (certNat% 98)))
 (.leaf 0x0))
 (.branch 486
 (.branch 485
 (.leaf (certNat% 99))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 504
 (.branch 500
 (.branch 498
 (.branch 497
 (.leaf (certNat% 100))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))))))
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
 (.leaf (certNat% 101))))
 (.branch 518
 (.branch 517
 (.leaf 0x0)
 (.leaf (certNat% 102)))
 (.branch 519
 (.leaf (certNat% 103))
 (.leaf 0x0))))
 (.branch 524
 (.branch 522
 (.leaf 0x0)
 (.branch 523
 (.leaf (certNat% 104))
 (.leaf 0x0)))
 (.branch 526
 (.branch 525
 (.leaf (certNat% 105))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 536
 (.branch 532
 (.leaf 0x0)
 (.branch 534
 (.branch 533
 (.leaf (certNat% 106))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 540
 (.branch 538
 (.branch 537
 (.leaf (certNat% 107))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 560
 (.branch 552
 (.branch 548
 (.branch 546
 (.branch 545
 (.leaf 0x0)
 (.leaf (certNat% 108)))
 (.leaf 0x0))
 (.branch 550
 (.branch 549
 (.leaf (certNat% 109))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 568
 (.branch 564
 (.branch 562
 (.branch 561
 (.leaf (certNat% 110))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 608
 (.branch 592
 (.branch 584
 (.branch 580
 (.branch 578
 (.branch 577
 (.leaf 0x0)
 (.leaf (certNat% 111)))
 (.branch 579
 (.leaf (certNat% 112))
 (.leaf (certNat% 113))))
 (.branch 582
 (.branch 581
 (.leaf (certNat% 114))
 (.leaf (certNat% 115)))
 (.branch 583
 (.leaf (certNat% 116))
 (.leaf 0x0))))
 (.branch 588
 (.branch 586
 (.branch 585
 (.leaf (certNat% 117))
 (.leaf 0x0))
 (.branch 587
 (.leaf (certNat% 118))
 (.leaf 0x0)))
 (.branch 590
 (.branch 589
 (.leaf (certNat% 119))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 600
 (.branch 596
 (.branch 594
 (.branch 593
 (.leaf (certNat% 120))
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 598
 (.branch 597
 (.leaf (certNat% 121))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 604
 (.branch 602
 (.branch 601
 (.leaf (certNat% 122))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 624
 (.branch 616
 (.branch 612
 (.branch 610
 (.branch 609
 (.leaf (certNat% 123))
 (.leaf (certNat% 124)))
 (.leaf 0x0))
 (.branch 614
 (.branch 613
 (.leaf (certNat% 125))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 632
 (.branch 628
 (.branch 626
 (.branch 625
 (.leaf (certNat% 126))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))))
 (.branch 704
 (.branch 672
 (.branch 656
 (.branch 648
 (.branch 644
 (.branch 642
 (.branch 641
 (.leaf 0x0)
 (.leaf (certNat% 127)))
 (.branch 643
 (.leaf (certNat% 128))
 (.leaf (certNat% 129))))
 (.branch 646
 (.branch 645
 (.leaf (certNat% 130))
 (.leaf (certNat% 131)))
 (.branch 647
 (.leaf (certNat% 132))
 (.leaf 0x0))))
 (.branch 652
 (.branch 650
 (.branch 649
 (.leaf (certNat% 133))
 (.leaf 0x0))
 (.branch 651
 (.leaf (certNat% 134))
 (.leaf 0x0)))
 (.branch 654
 (.branch 653
 (.leaf (certNat% 135))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 664
 (.branch 660
 (.branch 658
 (.branch 657
 (.leaf (certNat% 136))
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 662
 (.branch 661
 (.leaf (certNat% 137))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 668
 (.branch 666
 (.branch 665
 (.leaf (certNat% 138))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 688
 (.branch 680
 (.branch 676
 (.branch 674
 (.branch 673
 (.leaf (certNat% 139))
 (.leaf (certNat% 140)))
 (.leaf 0x0))
 (.branch 678
 (.branch 677
 (.leaf (certNat% 141))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 696
 (.branch 692
 (.branch 690
 (.branch 689
 (.leaf (certNat% 142))
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
 (.leaf (certNat% 143))
 (.leaf (certNat% 144)))
 (.branch 707
 (.leaf (certNat% 145))
 (.leaf (certNat% 146))))
 (.branch 710
 (.branch 709
 (.leaf (certNat% 147))
 (.leaf (certNat% 148)))
 (.branch 711
 (.leaf (certNat% 149))
 (.leaf 0x0))))
 (.branch 716
 (.branch 714
 (.branch 713
 (.leaf (certNat% 150))
 (.leaf 0x0))
 (.branch 715
 (.leaf (certNat% 151))
 (.leaf 0x0)))
 (.branch 718
 (.branch 717
 (.leaf (certNat% 152))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 728
 (.branch 724
 (.branch 722
 (.branch 721
 (.leaf (certNat% 153))
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 726
 (.branch 725
 (.leaf (certNat% 154))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 732
 (.branch 730
 (.branch 729
 (.leaf (certNat% 155))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 752
 (.branch 744
 (.branch 740
 (.branch 738
 (.branch 737
 (.leaf (certNat% 156))
 (.leaf (certNat% 157)))
 (.leaf 0x0))
 (.branch 742
 (.branch 741
 (.leaf (certNat% 158))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 760
 (.branch 756
 (.branch 754
 (.branch 753
 (.leaf (certNat% 159))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))))
 (.branch 896
 (.branch 832
 (.branch 800
 (.branch 784
 (.branch 776
 (.branch 772
 (.branch 770
 (.branch 769
 (.leaf 0x0)
 (.leaf (certNat% 160)))
 (.branch 771
 (.leaf (certNat% 161))
 (.leaf (certNat% 162))))
 (.branch 774
 (.branch 773
 (.leaf (certNat% 163))
 (.leaf (certNat% 164)))
 (.branch 775
 (.leaf (certNat% 165))
 (.leaf 0x0))))
 (.branch 780
 (.branch 778
 (.branch 777
 (.leaf (certNat% 166))
 (.leaf 0x0))
 (.branch 779
 (.leaf (certNat% 167))
 (.leaf 0x0)))
 (.branch 782
 (.branch 781
 (.leaf (certNat% 168))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 792
 (.branch 788
 (.branch 786
 (.branch 785
 (.leaf (certNat% 169))
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 790
 (.branch 789
 (.leaf (certNat% 170))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 796
 (.branch 794
 (.branch 793
 (.leaf (certNat% 171))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 816
 (.branch 808
 (.branch 804
 (.branch 802
 (.branch 801
 (.leaf (certNat% 172))
 (.leaf (certNat% 173)))
 (.leaf 0x0))
 (.branch 806
 (.branch 805
 (.leaf (certNat% 174))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 824
 (.branch 820
 (.branch 818
 (.branch 817
 (.leaf (certNat% 175))
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
 (.leaf (certNat% 176))
 (.leaf (certNat% 177)))
 (.branch 835
 (.leaf (certNat% 178))
 (.leaf (certNat% 179))))
 (.branch 838
 (.branch 837
 (.leaf (certNat% 180))
 (.leaf (certNat% 181)))
 (.branch 839
 (.leaf (certNat% 182))
 (.leaf 0x0))))
 (.branch 844
 (.branch 842
 (.branch 841
 (.leaf (certNat% 183))
 (.leaf 0x0))
 (.branch 843
 (.leaf (certNat% 184))
 (.leaf 0x0)))
 (.branch 846
 (.branch 845
 (.leaf (certNat% 185))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 856
 (.branch 852
 (.branch 850
 (.branch 849
 (.leaf (certNat% 186))
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 854
 (.branch 853
 (.leaf (certNat% 187))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 860
 (.branch 858
 (.branch 857
 (.leaf (certNat% 188))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 880
 (.branch 872
 (.branch 868
 (.branch 866
 (.branch 865
 (.leaf (certNat% 189))
 (.leaf (certNat% 190)))
 (.leaf 0x0))
 (.branch 870
 (.branch 869
 (.leaf (certNat% 191))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 888
 (.branch 884
 (.branch 882
 (.branch 881
 (.leaf (certNat% 192))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))))
 (.branch 960
 (.branch 928
 (.branch 912
 (.branch 904
 (.branch 900
 (.branch 898
 (.branch 897
 (.leaf (certNat% 193))
 (.leaf (certNat% 194)))
 (.branch 899
 (.leaf (certNat% 195))
 (.leaf (certNat% 196))))
 (.branch 902
 (.branch 901
 (.leaf (certNat% 197))
 (.leaf (certNat% 198)))
 (.branch 903
 (.leaf (certNat% 199))
 (.leaf 0x0))))
 (.branch 908
 (.branch 906
 (.branch 905
 (.leaf (certNat% 200))
 (.leaf 0x0))
 (.branch 907
 (.leaf (certNat% 201))
 (.leaf 0x0)))
 (.branch 910
 (.branch 909
 (.leaf (certNat% 202))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 920
 (.branch 916
 (.branch 914
 (.branch 913
 (.leaf (certNat% 203))
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 918
 (.branch 917
 (.leaf (certNat% 204))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 924
 (.branch 922
 (.branch 921
 (.leaf (certNat% 205))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 944
 (.branch 936
 (.branch 932
 (.branch 930
 (.branch 929
 (.leaf (certNat% 206))
 (.leaf (certNat% 207)))
 (.leaf 0x0))
 (.branch 934
 (.branch 933
 (.leaf (certNat% 208))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 952
 (.branch 948
 (.branch 946
 (.branch 945
 (.leaf (certNat% 209))
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
 (.leaf (certNat% 210))
 (.leaf (certNat% 211)))
 (.branch 963
 (.leaf (certNat% 212))
 (.leaf 0x0)))
 (.branch 966
 (.branch 965
 (.leaf (certNat% 213))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 972
 (.branch 970
 (.branch 969
 (.leaf (certNat% 214))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 984
 (.branch 980
 (.branch 978
 (.branch 977
 (.leaf (certNat% 215))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 1008
 (.branch 1000
 (.branch 996
 (.branch 994
 (.branch 993
 (.leaf (certNat% 216))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))))))
def kindRowTable : Table Nat :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf 0x1)
 (.leaf (certNat% 217)))
 (.branch 3
 (.leaf (certNat% 218))
 (.branch 4
 (.leaf (certNat% 219))
 (.leaf 0x0))))
 (.branch 8
 (.leaf 0x0)
 (.branch 9
 (.leaf 0x0)
 (.branch 10
 (.leaf 0x0)
 (.leaf (certNat% 220))))))
def decodeRow (table : Table Nat) (i : Nat) : List Nat :=
  let code := table.get i
  (PackedRawNatGrowth.readList 12 (PackedRawNatGrowth.take 16 code)
    (PackedRawNatGrowth.drop 16 code)).1
def candidateRows := decodeRow candidateRowTable
def kindRows := decodeRow kindRowTable
def kindMaskTable : Table Nat :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf 0x1)
 (.leaf (certNat% 221)))
 (.branch 3
 (.leaf (certNat% 222))
 (.branch 4
 (.leaf (certNat% 223))
 (.leaf 0x0))))
 (.branch 8
 (.leaf 0x0)
 (.branch 9
 (.leaf 0x0)
 (.branch 10
 (.leaf 0x0)
 (.leaf (certNat% 224))))))
def kindMasks := kindMaskTable.get
def keys := List.range 11
def vertexMaskTable : Table Nat :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf 219260956106960943302812486730761081606266174321312946795743834941893465267080508740780848600871176138269571700549150845904234810818244507043972208156394923447302074326995953222901683071667098527330127819838520429770444340304949755559914333434816064365065241058662521725240008300224102103537000855889578493982658847629485428117629045867085851745651630843115077523510899397545334588933232876379133738451590654578262218948150728085313384411584179822525495426001820904419608518590998726558402597527407934344299725896421237109296981111725770093572499887015385319778487966177643058730519596418496842027575565891255027965049624256363903055398537761610391975353549006643195800475794367041448320172031)
 (.leaf 219260956106960943302812486730761081595269267003568898594565924436412671160887119070386198250620840686134843440066224145561563319022557281460583177117610692599915017514161363632518085444136289611486578770872906924639181351965064123958021190000136338738072101804641220029794949089340409724813557986787521769717049992815704722027950582463728377084591081947510002864645982588202786985878790766691258901931311311725581254248787800578210718635229934140618894658556634816611126440962359940819180134338392186187179986036404763115602211532921010606562190020157897503752396310812594358573752325394550507785762467467959409818115737518559588811287574417397371964256032354075464718190327582949342579787775))
 (.branch 3
 (.leaf 14617397073797396220184403761152920868839823019332170495234897164804828866995723378355562103688964683824445878592326398457323152235408705403157757868261903648716987148127970193274809734180148696058966016652266575262445666873453577451102501287708363608119831065473949559385954647602394053669511063348751950128733112867512643556697648561579274830774816195215840485670671533838368340893958245201777801237248261625606075950195985540460845353133746783656416366026997193317283383044367345401750689802752010607809467608014581569222436578155727657895043020153758676753199998142083004222538543818072825885437609338477088212619821090293105296022053120398928179088177192146872535350217549265388863223839)
 (.branch 4
 (.leaf 219260956106960943302812486730761081595269267003568898594565924436412671160887119070386227642766639707050663800596174294220332178162869763823218387110634672825867582852797086833562882808910766010102653892581435509750852230531131386297655577569870497675284383662465555279180101969835348077952754974224545458276421690485672303054066589585531453495157019041203059152178134994118155291216769404218339473352242253275003739760123043740973286192447641640793713772747812119968137885892918677094075735438187700053125355044900085660505497400254079945392080057242531091214197604655614423351923167175785271998703903219688881818769503777707099076458303127570459672241024296548705479313500532078807475027969)
 (.leaf 233878353180758339522999985846145153690623644152729443633023413540988714026076233981791056362332575427635664971226534208967683971010389366653151963517790433635318340797933307808810707434903937150819397483791542141179409109475350212643058851683927224400858390042319615446009996067325901884710190913937323923890018048276437347198438510642760219727327457507753772236646942973625301571307083132023591983290057663932754548109008539661568194126103909663691545319292790466201035125197866081863127578899631674548701149506847352153315124187071848161856931520682890635657277967067237690582166126722922268386106388260826089229205326099761681272785472282426041789608545689486578039913340765545209496862721))))
 (.branch 7
 (.branch 6
 (.leaf 233878353180758339522999985846145153701620551470473491834203652732173515904946260341745248741849764377628012642207355606606876568957554296210360985222847135978368345845114781185734611980570617016225749260233366362297886006512839203902129662922482687098003621895018203041828703373306279604189965505152409385689331726978574656746716419555383644071553847275997191101739364116004336015525148286174392391274416270110168651763296193160851720350369402502694481149540211010323515644208837352873457845156456327896897658061747288709772761899840384966968116163591566741771494622342718784711410453085249010218656848479426747311434503642266769395364433218387893759219778028515193811073573247568542854838273)
 (.leaf 14617452834742044189991195509347372358080654875111871975718844763936878686900170396815990555754332139231883556676014173412197918266695466860625644796430629091626566481991315409387942702051990326955241864310513416428647924848775026167742869227015142135888999091830663422444760181265457440917801184743799296757633402647447204347062692924219072726260097766006387076180130000880723957203418139291397346834671878869764694200407696015981838770724774362659511714748367930597347629593623022178982723258385375740359744202169126947018694600757364288074421784721076866631284501118616534870795414035332384135642981688532643913007201570595428796740362885764317647895443059112812905254719573562554195347682))
 (.branch 8
 (.leaf 43852135460660251813836078340557118125801844497538201802521798639221058154865712624379417452518230198104632925624753518424118404120809866137000717499996418083661537736357937412875011608988092764971472232508680267374839251924362092943715840890238076740284124113808991899229769674231760775339930083564333320135785821970186560769135172702594545707926208048268928773697369869068486369953549693011322244497584437770624145861221558371816312143900287535314387819846245309692005525422941453920281060473776309098353116188011934600984613065172440722013889338130169320512575698546105018127870923409996127722200751097826483823286159414163285617376079924363250516728113649534187661551999531657557426606884)
 (.branch 9
 (.leaf 73086985368774270789288757759465047440103768632706776716156184541448235936954957334459623286875606337245070179933462901992999255013873042889708345774141474092601608606757205537011726618415639840142752685970131020291878152867237990388319592104339555530978866599089760877380830819017335777333846684948451590762746947168311283750781747987808348320243756033736369727866694309476421052978066367508347865406781709074874913043740901290344355452306045138948544877657964247077508019814170666895528872398417184797133457190919378138448862682566520250021370955698391079784104644280496553076173103710538667298878551862757794515722938039706458997007810771752196114519985136294708308683958259600606203553096)
 (.leaf 131556573664176565170262047821774911227848313846498250563487441195749056264083757111371495806695250696138208920951838438046675664135964304363180090197350970164581881840660148775428425842658595453430104008922837004264120569072778877157424756343638275958779415353268094656253859480543561423979089210082836037916783868423777603284743450875609940311751582274088415459931765965484474118270373935512713986588328434398576990237714763882507493643797696440947518620177839250099277290210256950152361872060516299460814124219827523457325724069042687100330480512995001477080907557375842882749154571631221731397555100421672725991359096887109489902781465463759142266347083685869768475768896734086738147427984)))))
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
 (.branch 54
 (.branch 53
 (.leaf (.leaf 14))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 60
 (.branch 58
 (.leaf (.leaf 0))
 (.branch 59
 (.leaf (.leaf 0))
 (.leaf (.leaf 15))))
 (.leaf (.leaf 0))))))
 (.branch 96
 (.branch 80
 (.branch 72
 (.branch 68
 (.branch 66
 (.branch 65
 (.leaf (.leaf 0))
 (.leaf (.leaf 16)))
 (.branch 67
 (.leaf (.leaf 17))
 (.leaf (.leaf 18))))
 (.branch 70
 (.branch 69
 (.leaf (.leaf 19))
 (.leaf (.leaf 20)))
 (.branch 71
 (.leaf (.leaf 21))
 (.leaf (.leaf 0)))))
 (.branch 76
 (.branch 74
 (.branch 73
 (.leaf (.leaf 22))
 (.leaf (.leaf 0)))
 (.branch 75
 (.leaf (.leaf 23))
 (.leaf (.leaf 0))))
 (.branch 78
 (.branch 77
 (.leaf (.leaf 24))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 88
 (.branch 84
 (.branch 82
 (.branch 81
 (.leaf (.leaf 25))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 86
 (.branch 85
 (.leaf (.leaf 26))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 92
 (.branch 90
 (.branch 89
 (.leaf (.leaf 27))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 112
 (.branch 104
 (.branch 100
 (.branch 98
 (.branch 97
 (.leaf (.leaf 28))
 (.leaf (.leaf 29)))
 (.leaf (.leaf 0)))
 (.branch 102
 (.branch 101
 (.leaf (.leaf 30))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
 (.branch 120
 (.branch 116
 (.branch 114
 (.branch 113
 (.leaf (.leaf 31))
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
 (.leaf (.leaf 32)))
 (.branch 131
 (.leaf (.leaf 33))
 (.leaf (.leaf 34))))
 (.branch 134
 (.branch 133
 (.leaf (.leaf 35))
 (.leaf (.leaf 36)))
 (.branch 135
 (.leaf (.leaf 37))
 (.leaf (.leaf 0)))))
 (.branch 140
 (.branch 138
 (.branch 137
 (.leaf (.leaf 38))
 (.leaf (.leaf 0)))
 (.branch 139
 (.leaf (.leaf 39))
 (.leaf (.leaf 0))))
 (.branch 142
 (.branch 141
 (.leaf (.leaf 40))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 152
 (.branch 148
 (.branch 146
 (.branch 145
 (.leaf (.leaf 41))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 150
 (.branch 149
 (.leaf (.leaf 42))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 156
 (.branch 154
 (.branch 153
 (.leaf (.leaf 43))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 176
 (.branch 168
 (.branch 164
 (.branch 162
 (.branch 161
 (.leaf (.leaf 44))
 (.leaf (.leaf 45)))
 (.leaf (.leaf 0)))
 (.branch 166
 (.branch 165
 (.leaf (.leaf 46))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
 (.branch 184
 (.branch 180
 (.branch 178
 (.branch 177
 (.leaf (.leaf 47))
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
 (.leaf (.leaf 48))
 (.leaf (.leaf 49)))
 (.branch 195
 (.leaf (.leaf 50))
 (.leaf (.branch (certNat% 225) (.leaf 51) (.leaf 52)))))
 (.branch 198
 (.branch 197
 (.leaf (.leaf 53))
 (.leaf (.branch (certNat% 226) (.leaf 54) (.leaf 55))))
 (.branch 199
 (.leaf (.branch (certNat% 227) (.leaf 56) (.leaf 57)))
 (.leaf (.leaf 0)))))
 (.branch 204
 (.branch 202
 (.branch 201
 (.leaf (.leaf 58))
 (.leaf (.leaf 0)))
 (.branch 203
 (.leaf (.branch (certNat% 228) (.leaf 59) (.leaf 60)))
 (.leaf (.leaf 0))))
 (.branch 206
 (.branch 205
 (.leaf (.branch (certNat% 229) (.leaf 61) (.leaf 62)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 216
 (.branch 212
 (.branch 210
 (.branch 209
 (.leaf (.leaf 63))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 214
 (.branch 213
 (.leaf (.branch (certNat% 230) (.leaf 64) (.leaf 65)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 220
 (.branch 218
 (.branch 217
 (.leaf (.branch (certNat% 231) (.leaf 66) (.leaf 67)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 240
 (.branch 232
 (.branch 228
 (.branch 226
 (.branch 225
 (.leaf (.leaf 68))
 (.leaf (.branch (certNat% 232) (.leaf 69) (.leaf 70))))
 (.leaf (.leaf 0)))
 (.branch 230
 (.branch 229
 (.leaf (.branch (certNat% 233) (.leaf 71) (.leaf 72)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
 (.branch 248
 (.branch 244
 (.branch 242
 (.branch 241
 (.leaf (.branch (certNat% 234) (.leaf 73) (.leaf 74)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))))
 (.branch 384
 (.branch 320
 (.branch 288
 (.branch 272
 (.branch 264
 (.branch 260
 (.branch 258
 (.branch 257
 (.leaf (.leaf 0))
 (.leaf (.leaf 75)))
 (.branch 259
 (.leaf (.leaf 76))
 (.leaf (.leaf 77))))
 (.branch 262
 (.branch 261
 (.leaf (.leaf 78))
 (.leaf (.leaf 79)))
 (.branch 263
 (.leaf (.leaf 80))
 (.leaf (.leaf 0)))))
 (.branch 268
 (.branch 266
 (.branch 265
 (.leaf (.leaf 81))
 (.leaf (.leaf 0)))
 (.branch 267
 (.leaf (.leaf 82))
 (.leaf (.leaf 0))))
 (.branch 270
 (.branch 269
 (.leaf (.leaf 83))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 280
 (.branch 276
 (.branch 274
 (.branch 273
 (.leaf (.leaf 84))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 278
 (.branch 277
 (.leaf (.leaf 85))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 284
 (.branch 282
 (.branch 281
 (.leaf (.leaf 86))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 304
 (.branch 296
 (.branch 292
 (.branch 290
 (.branch 289
 (.leaf (.leaf 87))
 (.leaf (.leaf 88)))
 (.leaf (.leaf 0)))
 (.branch 294
 (.branch 293
 (.leaf (.leaf 89))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
 (.branch 312
 (.branch 308
 (.branch 306
 (.branch 305
 (.leaf (.leaf 90))
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
 (.leaf (.leaf 91))
 (.leaf (.leaf 92)))
 (.branch 323
 (.leaf (.leaf 93))
 (.leaf (.branch (certNat% 235) (.leaf 94) (.leaf 95)))))
 (.branch 326
 (.branch 325
 (.leaf (.leaf 96))
 (.leaf (.branch (certNat% 236) (.leaf 97) (.leaf 98))))
 (.branch 327
 (.leaf (.branch (certNat% 237) (.leaf 99) (.leaf 100)))
 (.leaf (.leaf 0)))))
 (.branch 332
 (.branch 330
 (.branch 329
 (.leaf (.leaf 101))
 (.leaf (.leaf 0)))
 (.branch 331
 (.leaf (.branch (certNat% 238) (.leaf 102) (.leaf 103)))
 (.leaf (.leaf 0))))
 (.branch 334
 (.branch 333
 (.leaf (.branch (certNat% 239) (.leaf 104) (.leaf 105)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 344
 (.branch 340
 (.branch 338
 (.branch 337
 (.leaf (.leaf 106))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 342
 (.branch 341
 (.leaf (.branch (certNat% 240) (.leaf 107) (.leaf 108)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 348
 (.branch 346
 (.branch 345
 (.leaf (.branch (certNat% 241) (.leaf 109) (.leaf 110)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 368
 (.branch 360
 (.branch 356
 (.branch 354
 (.branch 353
 (.leaf (.leaf 111))
 (.leaf (.branch (certNat% 242) (.leaf 112) (.leaf 113))))
 (.leaf (.leaf 0)))
 (.branch 358
 (.branch 357
 (.leaf (.branch (certNat% 243) (.leaf 114) (.leaf 115)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
 (.branch 376
 (.branch 372
 (.branch 370
 (.branch 369
 (.leaf (.branch (certNat% 244) (.leaf 116) (.leaf 117)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))))
 (.branch 448
 (.branch 416
 (.branch 400
 (.branch 392
 (.branch 388
 (.branch 386
 (.branch 385
 (.leaf (.leaf 118))
 (.leaf (.leaf 119)))
 (.branch 387
 (.leaf (.leaf 120))
 (.leaf (.branch (certNat% 245) (.leaf 121) (.leaf 122)))))
 (.branch 390
 (.branch 389
 (.leaf (.leaf 123))
 (.leaf (.branch (certNat% 246) (.leaf 124) (.leaf 125))))
 (.branch 391
 (.leaf (.branch (certNat% 247) (.leaf 126) (.leaf 127)))
 (.leaf (.leaf 0)))))
 (.branch 396
 (.branch 394
 (.branch 393
 (.leaf (.leaf 128))
 (.leaf (.leaf 0)))
 (.branch 395
 (.leaf (.branch (certNat% 248) (.leaf 129) (.leaf 130)))
 (.leaf (.leaf 0))))
 (.branch 398
 (.branch 397
 (.leaf (.branch (certNat% 249) (.leaf 131) (.leaf 132)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 408
 (.branch 404
 (.branch 402
 (.branch 401
 (.leaf (.leaf 133))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 406
 (.branch 405
 (.leaf (.branch (certNat% 250) (.leaf 134) (.leaf 135)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 412
 (.branch 410
 (.branch 409
 (.leaf (.branch (certNat% 251) (.leaf 136) (.leaf 137)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 432
 (.branch 424
 (.branch 420
 (.branch 418
 (.branch 417
 (.leaf (.leaf 138))
 (.leaf (.branch (certNat% 252) (.leaf 139) (.leaf 140))))
 (.leaf (.leaf 0)))
 (.branch 422
 (.branch 421
 (.leaf (.branch (certNat% 253) (.leaf 141) (.leaf 142)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
 (.branch 440
 (.branch 436
 (.branch 434
 (.branch 433
 (.leaf (.branch (certNat% 254) (.leaf 143) (.leaf 144)))
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
 (.leaf (.leaf 145))
 (.leaf (.branch (certNat% 255) (.leaf 146) (.branch (certNat% 256) (.leaf 147) (.leaf 148)))))
 (.branch 451
 (.leaf (.branch (certNat% 257) (.leaf 149) (.branch (certNat% 258) (.leaf 150) (.leaf 151))))
 (.leaf (.branch (certNat% 259) (.branch (certNat% 260) (.leaf 152) (.branch (certNat% 261) (.leaf 153) (.leaf 154))) (.branch (certNat% 262) (.leaf 155) (.branch (certNat% 263) (.leaf 156) (.leaf 157)))))))
 (.branch 454
 (.branch 453
 (.leaf (.branch (certNat% 264) (.leaf 158) (.branch (certNat% 265) (.leaf 159) (.leaf 160))))
 (.leaf (.branch (certNat% 266) (.branch (certNat% 267) (.leaf 161) (.branch (certNat% 268) (.leaf 162) (.leaf 163))) (.branch (certNat% 269) (.leaf 164) (.branch (certNat% 270) (.leaf 165) (.leaf 166))))))
 (.branch 455
 (.leaf (.branch (certNat% 271) (.branch (certNat% 272) (.leaf 167) (.branch (certNat% 273) (.leaf 168) (.leaf 169))) (.branch (certNat% 274) (.leaf 170) (.branch (certNat% 275) (.leaf 171) (.leaf 172)))))
 (.leaf (.leaf 0)))))
 (.branch 460
 (.branch 458
 (.branch 457
 (.leaf (.branch (certNat% 276) (.leaf 173) (.branch (certNat% 277) (.leaf 174) (.leaf 175))))
 (.leaf (.leaf 0)))
 (.branch 459
 (.leaf (.branch (certNat% 278) (.branch (certNat% 279) (.leaf 176) (.branch (certNat% 280) (.leaf 177) (.leaf 178))) (.branch (certNat% 281) (.leaf 179) (.branch (certNat% 282) (.leaf 180) (.leaf 181)))))
 (.leaf (.leaf 0))))
 (.branch 462
 (.branch 461
 (.leaf (.branch (certNat% 283) (.branch (certNat% 284) (.leaf 182) (.branch (certNat% 285) (.leaf 183) (.leaf 184))) (.branch (certNat% 286) (.leaf 185) (.branch (certNat% 287) (.leaf 186) (.leaf 187)))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 472
 (.branch 468
 (.branch 466
 (.branch 465
 (.leaf (.branch (certNat% 288) (.leaf 188) (.branch (certNat% 289) (.leaf 189) (.leaf 190))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 470
 (.branch 469
 (.leaf (.branch (certNat% 290) (.branch (certNat% 291) (.leaf 191) (.branch (certNat% 292) (.leaf 192) (.leaf 193))) (.branch (certNat% 293) (.leaf 194) (.branch (certNat% 294) (.leaf 195) (.leaf 196)))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 476
 (.branch 474
 (.branch 473
 (.leaf (.branch (certNat% 295) (.branch (certNat% 296) (.leaf 197) (.branch (certNat% 297) (.leaf 198) (.leaf 199))) (.branch (certNat% 298) (.leaf 200) (.branch (certNat% 299) (.leaf 201) (.leaf 202)))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 496
 (.branch 488
 (.branch 484
 (.branch 482
 (.branch 481
 (.leaf (.branch (certNat% 300) (.leaf 203) (.branch (certNat% 301) (.leaf 204) (.leaf 205))))
 (.leaf (.branch (certNat% 302) (.branch (certNat% 303) (.leaf 206) (.branch (certNat% 304) (.leaf 207) (.leaf 208))) (.branch (certNat% 305) (.leaf 209) (.branch (certNat% 306) (.leaf 210) (.leaf 211))))))
 (.leaf (.leaf 0)))
 (.branch 486
 (.branch 485
 (.leaf (.branch (certNat% 307) (.branch (certNat% 308) (.leaf 212) (.branch (certNat% 309) (.leaf 213) (.leaf 214))) (.branch (certNat% 310) (.leaf 215) (.branch (certNat% 311) (.leaf 216) (.leaf 217)))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
 (.branch 504
 (.branch 500
 (.branch 498
 (.branch 497
 (.leaf (.branch (certNat% 312) (.branch (certNat% 313) (.leaf 218) (.branch (certNat% 314) (.leaf 219) (.leaf 220))) (.branch (certNat% 315) (.leaf 221) (.branch (certNat% 316) (.leaf 222) (.leaf 223)))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))))))
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
 (.leaf (.leaf 224)))
 (.branch 515
 (.leaf (.leaf 225))
 (.leaf (.leaf 226))))
 (.branch 518
 (.branch 517
 (.leaf (.leaf 227))
 (.leaf (.leaf 228)))
 (.branch 519
 (.leaf (.leaf 229))
 (.leaf (.leaf 0)))))
 (.branch 524
 (.branch 522
 (.branch 521
 (.leaf (.leaf 230))
 (.leaf (.leaf 0)))
 (.branch 523
 (.leaf (.leaf 231))
 (.leaf (.leaf 0))))
 (.branch 526
 (.branch 525
 (.leaf (.leaf 232))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 536
 (.branch 532
 (.branch 530
 (.branch 529
 (.leaf (.leaf 233))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 534
 (.branch 533
 (.leaf (.leaf 234))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 540
 (.branch 538
 (.branch 537
 (.leaf (.leaf 235))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 560
 (.branch 552
 (.branch 548
 (.branch 546
 (.branch 545
 (.leaf (.leaf 236))
 (.leaf (.leaf 237)))
 (.leaf (.leaf 0)))
 (.branch 550
 (.branch 549
 (.leaf (.leaf 238))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
 (.branch 568
 (.branch 564
 (.branch 562
 (.branch 561
 (.leaf (.leaf 239))
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
 (.leaf (.leaf 240))
 (.leaf (.leaf 241)))
 (.branch 579
 (.leaf (.leaf 242))
 (.leaf (.branch (certNat% 317) (.leaf 243) (.leaf 244)))))
 (.branch 582
 (.branch 581
 (.leaf (.leaf 245))
 (.leaf (.branch (certNat% 318) (.leaf 246) (.leaf 247))))
 (.branch 583
 (.leaf (.branch (certNat% 319) (.leaf 248) (.leaf 249)))
 (.leaf (.leaf 0)))))
 (.branch 588
 (.branch 586
 (.branch 585
 (.leaf (.leaf 250))
 (.leaf (.leaf 0)))
 (.branch 587
 (.leaf (.branch (certNat% 320) (.leaf 251) (.leaf 252)))
 (.leaf (.leaf 0))))
 (.branch 590
 (.branch 589
 (.leaf (.branch (certNat% 321) (.leaf 253) (.leaf 254)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 600
 (.branch 596
 (.branch 594
 (.branch 593
 (.leaf (.leaf 255))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 598
 (.branch 597
 (.leaf (.branch (certNat% 322) (.leaf 256) (.leaf 257)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 604
 (.branch 602
 (.branch 601
 (.leaf (.branch (certNat% 323) (.leaf 258) (.leaf 259)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 624
 (.branch 616
 (.branch 612
 (.branch 610
 (.branch 609
 (.leaf (.leaf 260))
 (.leaf (.branch (certNat% 324) (.leaf 261) (.leaf 262))))
 (.leaf (.leaf 0)))
 (.branch 614
 (.branch 613
 (.leaf (.branch (certNat% 325) (.leaf 263) (.leaf 264)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
 (.branch 632
 (.branch 628
 (.branch 626
 (.branch 625
 (.leaf (.branch (certNat% 326) (.leaf 265) (.leaf 266)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))))
 (.branch 704
 (.branch 672
 (.branch 656
 (.branch 648
 (.branch 644
 (.branch 642
 (.branch 641
 (.leaf (.leaf 267))
 (.leaf (.leaf 268)))
 (.branch 643
 (.leaf (.leaf 269))
 (.leaf (.branch (certNat% 327) (.leaf 270) (.leaf 271)))))
 (.branch 646
 (.branch 645
 (.leaf (.leaf 272))
 (.leaf (.branch (certNat% 328) (.leaf 273) (.leaf 274))))
 (.branch 647
 (.leaf (.branch (certNat% 329) (.leaf 275) (.leaf 276)))
 (.leaf (.leaf 0)))))
 (.branch 652
 (.branch 650
 (.branch 649
 (.leaf (.leaf 277))
 (.leaf (.leaf 0)))
 (.branch 651
 (.leaf (.branch (certNat% 330) (.leaf 278) (.leaf 279)))
 (.leaf (.leaf 0))))
 (.branch 654
 (.branch 653
 (.leaf (.branch (certNat% 331) (.leaf 280) (.leaf 281)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 664
 (.branch 660
 (.branch 658
 (.branch 657
 (.leaf (.leaf 282))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 662
 (.branch 661
 (.leaf (.branch (certNat% 332) (.leaf 283) (.leaf 284)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 668
 (.branch 666
 (.branch 665
 (.leaf (.branch (certNat% 333) (.leaf 285) (.leaf 286)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 688
 (.branch 680
 (.branch 676
 (.branch 674
 (.branch 673
 (.leaf (.leaf 287))
 (.leaf (.branch (certNat% 334) (.leaf 288) (.leaf 289))))
 (.leaf (.leaf 0)))
 (.branch 678
 (.branch 677
 (.leaf (.branch (certNat% 335) (.leaf 290) (.leaf 291)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
 (.branch 696
 (.branch 692
 (.branch 690
 (.branch 689
 (.leaf (.branch (certNat% 336) (.leaf 292) (.leaf 293)))
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
 (.leaf (.leaf 294))
 (.leaf (.branch (certNat% 337) (.leaf 295) (.branch (certNat% 338) (.leaf 296) (.leaf 297)))))
 (.branch 707
 (.leaf (.branch (certNat% 339) (.leaf 298) (.branch (certNat% 340) (.leaf 299) (.leaf 300))))
 (.leaf (.branch (certNat% 341) (.branch (certNat% 342) (.leaf 301) (.branch (certNat% 343) (.leaf 302) (.leaf 303))) (.branch (certNat% 344) (.leaf 304) (.branch (certNat% 345) (.leaf 305) (.leaf 306)))))))
 (.branch 710
 (.branch 709
 (.leaf (.branch (certNat% 346) (.leaf 307) (.branch (certNat% 347) (.leaf 308) (.leaf 309))))
 (.leaf (.branch (certNat% 348) (.branch (certNat% 349) (.leaf 310) (.branch (certNat% 350) (.leaf 311) (.leaf 312))) (.branch (certNat% 351) (.leaf 313) (.branch (certNat% 352) (.leaf 314) (.leaf 315))))))
 (.branch 711
 (.leaf (.branch (certNat% 353) (.branch (certNat% 354) (.leaf 316) (.branch (certNat% 355) (.leaf 317) (.leaf 318))) (.branch (certNat% 356) (.leaf 319) (.branch (certNat% 357) (.leaf 320) (.leaf 321)))))
 (.leaf (.leaf 0)))))
 (.branch 716
 (.branch 714
 (.branch 713
 (.leaf (.branch (certNat% 358) (.leaf 322) (.branch (certNat% 359) (.leaf 323) (.leaf 324))))
 (.leaf (.leaf 0)))
 (.branch 715
 (.leaf (.branch (certNat% 360) (.branch (certNat% 361) (.leaf 325) (.branch (certNat% 362) (.leaf 326) (.leaf 327))) (.branch (certNat% 363) (.leaf 328) (.branch (certNat% 364) (.leaf 329) (.leaf 330)))))
 (.leaf (.leaf 0))))
 (.branch 718
 (.branch 717
 (.leaf (.branch (certNat% 365) (.branch (certNat% 366) (.leaf 331) (.branch (certNat% 367) (.leaf 332) (.leaf 333))) (.branch (certNat% 368) (.leaf 334) (.branch (certNat% 369) (.leaf 335) (.leaf 336)))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 728
 (.branch 724
 (.branch 722
 (.branch 721
 (.leaf (.branch (certNat% 370) (.leaf 337) (.branch (certNat% 371) (.leaf 338) (.leaf 339))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 726
 (.branch 725
 (.leaf (.branch (certNat% 372) (.branch (certNat% 373) (.leaf 340) (.branch (certNat% 374) (.leaf 341) (.leaf 342))) (.branch (certNat% 375) (.leaf 343) (.branch (certNat% 376) (.leaf 344) (.leaf 345)))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 732
 (.branch 730
 (.branch 729
 (.leaf (.branch (certNat% 377) (.branch (certNat% 378) (.leaf 346) (.branch (certNat% 379) (.leaf 347) (.leaf 348))) (.branch (certNat% 380) (.leaf 349) (.branch (certNat% 381) (.leaf 350) (.leaf 351)))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 752
 (.branch 744
 (.branch 740
 (.branch 738
 (.branch 737
 (.leaf (.branch (certNat% 382) (.leaf 352) (.branch (certNat% 383) (.leaf 353) (.leaf 354))))
 (.leaf (.branch (certNat% 384) (.branch (certNat% 385) (.leaf 355) (.branch (certNat% 386) (.leaf 356) (.leaf 357))) (.branch (certNat% 387) (.leaf 358) (.branch (certNat% 388) (.leaf 359) (.leaf 360))))))
 (.leaf (.leaf 0)))
 (.branch 742
 (.branch 741
 (.leaf (.branch (certNat% 389) (.branch (certNat% 390) (.leaf 361) (.branch (certNat% 391) (.leaf 362) (.leaf 363))) (.branch (certNat% 392) (.leaf 364) (.branch (certNat% 393) (.leaf 365) (.leaf 366)))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
 (.branch 760
 (.branch 756
 (.branch 754
 (.branch 753
 (.leaf (.branch (certNat% 394) (.branch (certNat% 395) (.leaf 367) (.branch (certNat% 396) (.leaf 368) (.leaf 369))) (.branch (certNat% 397) (.leaf 370) (.branch (certNat% 398) (.leaf 371) (.leaf 372)))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))))
 (.branch 896
 (.branch 832
 (.branch 800
 (.branch 784
 (.branch 776
 (.branch 772
 (.branch 770
 (.branch 769
 (.leaf (.leaf 373))
 (.leaf (.leaf 374)))
 (.branch 771
 (.leaf (.leaf 375))
 (.leaf (.branch (certNat% 399) (.leaf 376) (.leaf 377)))))
 (.branch 774
 (.branch 773
 (.leaf (.leaf 378))
 (.leaf (.branch (certNat% 400) (.leaf 379) (.leaf 380))))
 (.branch 775
 (.leaf (.branch (certNat% 401) (.leaf 381) (.leaf 382)))
 (.leaf (.leaf 0)))))
 (.branch 780
 (.branch 778
 (.branch 777
 (.leaf (.leaf 383))
 (.leaf (.leaf 0)))
 (.branch 779
 (.leaf (.branch (certNat% 402) (.leaf 384) (.leaf 385)))
 (.leaf (.leaf 0))))
 (.branch 782
 (.branch 781
 (.leaf (.branch (certNat% 403) (.leaf 386) (.leaf 387)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 792
 (.branch 788
 (.branch 786
 (.branch 785
 (.leaf (.leaf 388))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 790
 (.branch 789
 (.leaf (.branch (certNat% 404) (.leaf 389) (.leaf 390)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 796
 (.branch 794
 (.branch 793
 (.leaf (.branch (certNat% 405) (.leaf 391) (.leaf 392)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 816
 (.branch 808
 (.branch 804
 (.branch 802
 (.branch 801
 (.leaf (.leaf 393))
 (.leaf (.branch (certNat% 406) (.leaf 394) (.leaf 395))))
 (.leaf (.leaf 0)))
 (.branch 806
 (.branch 805
 (.leaf (.branch (certNat% 407) (.leaf 396) (.leaf 397)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
 (.branch 824
 (.branch 820
 (.branch 818
 (.branch 817
 (.leaf (.branch (certNat% 408) (.leaf 398) (.leaf 399)))
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
 (.leaf (.leaf 400))
 (.leaf (.branch (certNat% 409) (.leaf 401) (.branch (certNat% 410) (.leaf 402) (.leaf 403)))))
 (.branch 835
 (.leaf (.branch (certNat% 411) (.leaf 404) (.branch (certNat% 412) (.leaf 405) (.leaf 406))))
 (.leaf (.branch (certNat% 413) (.branch (certNat% 414) (.leaf 407) (.branch (certNat% 415) (.leaf 408) (.leaf 409))) (.branch (certNat% 416) (.leaf 410) (.branch (certNat% 417) (.leaf 411) (.leaf 412)))))))
 (.branch 838
 (.branch 837
 (.leaf (.branch (certNat% 418) (.leaf 413) (.branch (certNat% 419) (.leaf 414) (.leaf 415))))
 (.leaf (.branch (certNat% 420) (.branch (certNat% 421) (.leaf 416) (.branch (certNat% 422) (.leaf 417) (.leaf 418))) (.branch (certNat% 423) (.leaf 419) (.branch (certNat% 424) (.leaf 420) (.leaf 421))))))
 (.branch 839
 (.leaf (.branch (certNat% 425) (.branch (certNat% 426) (.leaf 422) (.branch (certNat% 427) (.leaf 423) (.leaf 424))) (.branch (certNat% 428) (.leaf 425) (.branch (certNat% 429) (.leaf 426) (.leaf 427)))))
 (.leaf (.leaf 0)))))
 (.branch 844
 (.branch 842
 (.branch 841
 (.leaf (.branch (certNat% 430) (.leaf 428) (.branch (certNat% 431) (.leaf 429) (.leaf 430))))
 (.leaf (.leaf 0)))
 (.branch 843
 (.leaf (.branch (certNat% 432) (.branch (certNat% 433) (.leaf 431) (.branch (certNat% 434) (.leaf 432) (.leaf 433))) (.branch (certNat% 435) (.leaf 434) (.branch (certNat% 436) (.leaf 435) (.leaf 436)))))
 (.leaf (.leaf 0))))
 (.branch 846
 (.branch 845
 (.leaf (.branch (certNat% 437) (.branch (certNat% 438) (.leaf 437) (.branch (certNat% 439) (.leaf 438) (.leaf 439))) (.branch (certNat% 440) (.leaf 440) (.branch (certNat% 441) (.leaf 441) (.leaf 442)))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 856
 (.branch 852
 (.branch 850
 (.branch 849
 (.leaf (.branch (certNat% 442) (.leaf 443) (.branch (certNat% 443) (.leaf 444) (.leaf 445))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 854
 (.branch 853
 (.leaf (.branch (certNat% 444) (.branch (certNat% 445) (.leaf 446) (.branch (certNat% 446) (.leaf 447) (.leaf 448))) (.branch (certNat% 447) (.leaf 449) (.branch (certNat% 448) (.leaf 450) (.leaf 451)))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 860
 (.branch 858
 (.branch 857
 (.leaf (.branch (certNat% 449) (.branch (certNat% 450) (.leaf 452) (.branch (certNat% 451) (.leaf 453) (.leaf 454))) (.branch (certNat% 452) (.leaf 455) (.branch (certNat% 453) (.leaf 456) (.leaf 457)))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 880
 (.branch 872
 (.branch 868
 (.branch 866
 (.branch 865
 (.leaf (.branch (certNat% 454) (.leaf 458) (.branch (certNat% 455) (.leaf 459) (.leaf 460))))
 (.leaf (.branch (certNat% 456) (.branch (certNat% 457) (.leaf 461) (.branch (certNat% 458) (.leaf 462) (.leaf 463))) (.branch (certNat% 459) (.leaf 464) (.branch (certNat% 460) (.leaf 465) (.leaf 466))))))
 (.leaf (.leaf 0)))
 (.branch 870
 (.branch 869
 (.leaf (.branch (certNat% 461) (.branch (certNat% 462) (.leaf 467) (.branch (certNat% 463) (.leaf 468) (.leaf 469))) (.branch (certNat% 464) (.leaf 470) (.branch (certNat% 465) (.leaf 471) (.leaf 472)))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
 (.branch 888
 (.branch 884
 (.branch 882
 (.branch 881
 (.leaf (.branch (certNat% 466) (.branch (certNat% 467) (.leaf 473) (.branch (certNat% 468) (.leaf 474) (.leaf 475))) (.branch (certNat% 469) (.leaf 476) (.branch (certNat% 470) (.leaf 477) (.leaf 478)))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))))
 (.branch 960
 (.branch 928
 (.branch 912
 (.branch 904
 (.branch 900
 (.branch 898
 (.branch 897
 (.leaf (.leaf 479))
 (.leaf (.branch (certNat% 471) (.leaf 480) (.branch (certNat% 472) (.leaf 481) (.leaf 482)))))
 (.branch 899
 (.leaf (.branch (certNat% 473) (.leaf 483) (.branch (certNat% 474) (.leaf 484) (.leaf 485))))
 (.leaf (.branch (certNat% 475) (.branch (certNat% 476) (.leaf 486) (.branch (certNat% 477) (.leaf 487) (.leaf 488))) (.branch (certNat% 478) (.leaf 489) (.branch (certNat% 479) (.leaf 490) (.leaf 491)))))))
 (.branch 902
 (.branch 901
 (.leaf (.branch (certNat% 480) (.leaf 492) (.branch (certNat% 481) (.leaf 493) (.leaf 494))))
 (.leaf (.branch (certNat% 482) (.branch (certNat% 483) (.leaf 495) (.branch (certNat% 484) (.leaf 496) (.leaf 497))) (.branch (certNat% 485) (.leaf 498) (.branch (certNat% 486) (.leaf 499) (.leaf 500))))))
 (.branch 903
 (.leaf (.branch (certNat% 487) (.branch (certNat% 488) (.leaf 501) (.branch (certNat% 489) (.leaf 502) (.leaf 503))) (.branch (certNat% 490) (.leaf 504) (.branch (certNat% 491) (.leaf 505) (.leaf 506)))))
 (.leaf (.leaf 0)))))
 (.branch 908
 (.branch 906
 (.branch 905
 (.leaf (.branch (certNat% 492) (.leaf 507) (.branch (certNat% 493) (.leaf 508) (.leaf 509))))
 (.leaf (.leaf 0)))
 (.branch 907
 (.leaf (.branch (certNat% 494) (.branch (certNat% 495) (.leaf 510) (.branch (certNat% 496) (.leaf 511) (.leaf 512))) (.branch (certNat% 497) (.leaf 513) (.branch (certNat% 498) (.leaf 514) (.leaf 515)))))
 (.leaf (.leaf 0))))
 (.branch 910
 (.branch 909
 (.leaf (.branch (certNat% 499) (.branch (certNat% 500) (.leaf 516) (.branch (certNat% 501) (.leaf 517) (.leaf 518))) (.branch (certNat% 502) (.leaf 519) (.branch (certNat% 503) (.leaf 520) (.leaf 521)))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 920
 (.branch 916
 (.branch 914
 (.branch 913
 (.leaf (.branch (certNat% 504) (.leaf 522) (.branch (certNat% 505) (.leaf 523) (.leaf 524))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 918
 (.branch 917
 (.leaf (.branch (certNat% 506) (.branch (certNat% 507) (.leaf 525) (.branch (certNat% 508) (.leaf 526) (.leaf 527))) (.branch (certNat% 509) (.leaf 528) (.branch (certNat% 510) (.leaf 529) (.leaf 530)))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 924
 (.branch 922
 (.branch 921
 (.leaf (.branch (certNat% 511) (.branch (certNat% 512) (.leaf 531) (.branch (certNat% 513) (.leaf 532) (.leaf 533))) (.branch (certNat% 514) (.leaf 534) (.branch (certNat% 515) (.leaf 535) (.leaf 536)))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 944
 (.branch 936
 (.branch 932
 (.branch 930
 (.branch 929
 (.leaf (.branch (certNat% 516) (.leaf 537) (.branch (certNat% 517) (.leaf 538) (.leaf 539))))
 (.leaf (.branch (certNat% 518) (.branch (certNat% 519) (.leaf 540) (.branch (certNat% 520) (.leaf 541) (.leaf 542))) (.branch (certNat% 521) (.leaf 543) (.branch (certNat% 522) (.leaf 544) (.leaf 545))))))
 (.leaf (.leaf 0)))
 (.branch 934
 (.branch 933
 (.leaf (.branch (certNat% 523) (.branch (certNat% 524) (.leaf 546) (.branch (certNat% 525) (.leaf 547) (.leaf 548))) (.branch (certNat% 526) (.leaf 549) (.branch (certNat% 527) (.leaf 550) (.leaf 551)))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
 (.branch 952
 (.branch 948
 (.branch 946
 (.branch 945
 (.leaf (.branch (certNat% 528) (.branch (certNat% 529) (.leaf 552) (.branch (certNat% 530) (.leaf 553) (.leaf 554))) (.branch (certNat% 531) (.leaf 555) (.branch (certNat% 532) (.leaf 556) (.leaf 557)))))
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
 (.leaf (.branch (certNat% 533) (.leaf 558) (.branch (certNat% 534) (.leaf 559) (.leaf 560))))
 (.leaf (.branch (certNat% 535) (.branch (certNat% 536) (.branch (certNat% 537) (.leaf 561) (.branch (certNat% 538) (.leaf 562) (.leaf 563))) (.branch (certNat% 539) (.leaf 564) (.branch (certNat% 540) (.leaf 565) (.leaf 566)))) (.branch (certNat% 541) (.branch (certNat% 542) (.leaf 567) (.branch (certNat% 543) (.leaf 568) (.leaf 569))) (.branch (certNat% 544) (.leaf 570) (.branch (certNat% 545) (.leaf 571) (.leaf 572)))))))
 (.branch 963
 (.leaf (.branch (certNat% 546) (.branch (certNat% 547) (.branch (certNat% 548) (.leaf 573) (.branch (certNat% 549) (.leaf 574) (.leaf 575))) (.branch (certNat% 550) (.leaf 576) (.branch (certNat% 551) (.leaf 577) (.leaf 578)))) (.branch (certNat% 552) (.branch (certNat% 553) (.leaf 579) (.branch (certNat% 554) (.leaf 580) (.leaf 581))) (.branch (certNat% 555) (.leaf 582) (.branch (certNat% 556) (.leaf 583) (.leaf 584))))))
 (.leaf (.leaf 0))))
 (.branch 966
 (.branch 965
 (.leaf (.branch (certNat% 557) (.branch (certNat% 558) (.branch (certNat% 559) (.leaf 585) (.branch (certNat% 560) (.leaf 586) (.leaf 587))) (.branch (certNat% 561) (.leaf 588) (.branch (certNat% 562) (.leaf 589) (.leaf 590)))) (.branch (certNat% 563) (.branch (certNat% 564) (.leaf 591) (.branch (certNat% 565) (.leaf 592) (.leaf 593))) (.branch (certNat% 566) (.leaf 594) (.branch (certNat% 567) (.leaf 595) (.leaf 596))))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 972
 (.branch 970
 (.branch 969
 (.leaf (.branch (certNat% 568) (.branch (certNat% 569) (.branch (certNat% 570) (.leaf 597) (.branch (certNat% 571) (.leaf 598) (.leaf 599))) (.branch (certNat% 572) (.leaf 600) (.branch (certNat% 573) (.leaf 601) (.leaf 602)))) (.branch (certNat% 574) (.branch (certNat% 575) (.leaf 603) (.branch (certNat% 576) (.leaf 604) (.leaf 605))) (.branch (certNat% 577) (.leaf 606) (.branch (certNat% 578) (.leaf 607) (.leaf 608))))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 984
 (.branch 980
 (.branch 978
 (.branch 977
 (.leaf (.branch (certNat% 579) (.branch (certNat% 580) (.branch (certNat% 581) (.leaf 609) (.branch (certNat% 582) (.leaf 610) (.leaf 611))) (.branch (certNat% 583) (.leaf 612) (.branch (certNat% 584) (.leaf 613) (.leaf 614)))) (.branch (certNat% 585) (.branch (certNat% 586) (.leaf 615) (.branch (certNat% 587) (.leaf 616) (.leaf 617))) (.branch (certNat% 588) (.leaf 618) (.branch (certNat% 589) (.leaf 619) (.leaf 620))))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 1008
 (.branch 1000
 (.branch 996
 (.branch 994
 (.branch 993
 (.leaf (.branch (certNat% 590) (.branch (certNat% 591) (.branch (certNat% 592) (.leaf 621) (.branch (certNat% 593) (.leaf 622) (.leaf 623))) (.branch (certNat% 594) (.leaf 624) (.branch (certNat% 595) (.leaf 625) (.leaf 626)))) (.branch (certNat% 596) (.branch (certNat% 597) (.leaf 627) (.branch (certNat% 598) (.leaf 628) (.leaf 629))) (.branch (certNat% 599) (.leaf 630) (.branch (certNat% 600) (.leaf 631) (.leaf 632))))))
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
def candidateMasks (i : Nat) := PackedRawNatGrowth.take 2300
  (PackedRawNatGrowth.drop (2300*(i%64)) (candidateMasksBlocks.get (i/64)))

def badMasksBlocks : Table Nat :=
(.branch 18
 (.branch 9
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
 (.branch 13
 (.branch 11
 (.branch 10
 (.leaf badMasksBlock0009)
 (.leaf badMasksBlock0010))
 (.branch 12
 (.leaf badMasksBlock0011)
 (.leaf badMasksBlock0012)))
 (.branch 15
 (.branch 14
 (.leaf badMasksBlock0013)
 (.leaf badMasksBlock0014))
 (.branch 16
 (.leaf badMasksBlock0015)
 (.branch 17
 (.leaf badMasksBlock0016)
 (.leaf badMasksBlock0017))))))
 (.branch 27
 (.branch 22
 (.branch 20
 (.branch 19
 (.leaf badMasksBlock0018)
 (.leaf badMasksBlock0019))
 (.branch 21
 (.leaf badMasksBlock0020)
 (.leaf badMasksBlock0021)))
 (.branch 24
 (.branch 23
 (.leaf badMasksBlock0022)
 (.leaf badMasksBlock0023))
 (.branch 25
 (.leaf badMasksBlock0024)
 (.branch 26
 (.leaf badMasksBlock0025)
 (.leaf badMasksBlock0026)))))
 (.branch 31
 (.branch 29
 (.branch 28
 (.leaf badMasksBlock0027)
 (.leaf badMasksBlock0028))
 (.branch 30
 (.leaf badMasksBlock0029)
 (.leaf badMasksBlock0030)))
 (.branch 33
 (.branch 32
 (.leaf badMasksBlock0031)
 (.leaf badMasksBlock0032))
 (.branch 34
 (.leaf badMasksBlock0033)
 (.branch 35
 (.leaf badMasksBlock0034)
 (.leaf badMasksBlock0035)))))))
def badMasks (i : Nat) := PackedRawNatGrowth.take 2300
  (PackedRawNatGrowth.drop (2300*(i%64)) (badMasksBlocks.get (i/64)))

def signatureMasksBlocks : Table Nat :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf signatureMasksBlock0000)
 (.leaf signatureMasksBlock0001))
 (.branch 3
 (.leaf signatureMasksBlock0002)
 (.branch 4
 (.leaf signatureMasksBlock0003)
 (.leaf signatureMasksBlock0004))))
 (.branch 7
 (.branch 6
 (.leaf signatureMasksBlock0005)
 (.leaf signatureMasksBlock0006))
 (.branch 8
 (.leaf signatureMasksBlock0007)
 (.branch 9
 (.leaf signatureMasksBlock0008)
 (.leaf signatureMasksBlock0009)))))
def signatureMasks (i : Nat) := PackedRawNatGrowth.take 2300
  (PackedRawNatGrowth.drop (2300*(i%64)) (signatureMasksBlocks.get (i/64)))

def fastKind := rawKind
def candidateSupports := candidateRows
def kindSupports := kindRows
def wellFormedTest (i : Nat) : Bool := RawFacetEmbedding.wellFormedCheck (rawCells i)

def cellTest (i : Nat) := (listBounds 1024 (rawCells i).ridgeMasks && ((rawCells i).ridgeMasks.all (fun q => (candidateMasks q).testBit i) && (decide (rawKind i = (rawCells i).kind) && (decide ((rawCells i).vertices < 1024) && ((List.range 10).all (fun v => decide ((vertexMasks v).testBit i = (rawCells i).vertices.testBit v)) && (SignatureCompatibility.faces (rawCells i)).all (fun q => (SignatureCompatibility.profileMask (SignatureCompatibility.allMask 2300) signatureIndex signatureMasks (rawCells i) q).testBit i))))))
def ridgeTest (i : Nat) := decide (candidateMasks i = RawNatGrowthCheck.mask (candidateRows i)) &&
  (candidateRows i).all (fun c => hasNat (rawCells c).ridgeMasks i)
def kindTest (i : Nat) := decide (kindMasks i = RawNatGrowthCheck.mask (kindRows i)) &&
  (kindRows i).all (fun c => decide ((rawCells c).kind = i))
def badTest (i : Nat) := if badMasks i = 0 then true else
  decide (Nat.land (badMasks i) (SignatureCompatibility.cover (SignatureCompatibility.allMask 2300)
    vertexMasks signatureIndex signatureMasks (rawCells i)) = 0)

end Papers.RationalityTen.RootedCaches.RootedSixExtra06

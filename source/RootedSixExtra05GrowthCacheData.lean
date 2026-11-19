module
prelude
public meta import CertificateNumbers
public import RootedSixExtra05
public import SignatureCompatibility
public import PackedRawNatGrowth
public import FiniteChecks
public import RawFacetEmbedding
public import RootedSixExtra05GrowthCachecandidateMasksData000
public import RootedSixExtra05GrowthCachecandidateMasksData001
public import RootedSixExtra05GrowthCachecandidateMasksData002
public import RootedSixExtra05GrowthCachecandidateMasksData003
public import RootedSixExtra05GrowthCachebadMasksData000
public import RootedSixExtra05GrowthCachebadMasksData001
public import RootedSixExtra05GrowthCachebadMasksData002
public import RootedSixExtra05GrowthCachebadMasksData003
public import RootedSixExtra05GrowthCachebadMasksData004
public import RootedSixExtra05GrowthCachebadMasksData005
public import RootedSixExtra05GrowthCachebadMasksData006
public import RootedSixExtra05GrowthCachebadMasksData007
public import RootedSixExtra05GrowthCachesignatureMasksData000
public import RootedSixExtra05GrowthCachesignatureMasksData001
public import RootedSixExtra05GrowthCachesignatureMasksData002

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra05
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def rawCells := Papers.RationalityTen.FacetUniverses.RootedSixExtra05.rawCells
def cells (c : Fin 2170) := rawCells c.val
def ridgeList := ConcreteGrowth.ridgeList cells
def literalCompatible (a b : Fin 2170) := ConcreteGrowth.compatible (cells a) (cells b)
def kind (c : Fin 2170) := (cells c).kind
def rawKindCode : Nat := 581127067499482959683868948154523101318306720227778164960661651832695359769563793803628265700719324493006371228532179130358462352686715946145842963803299741050891169177332704223688990291791915781918354769832428468105718039473526987803916727911082572798247135720750910474049149901956480302151336914864162290961789992291219639306492111859852646473418265437912629887316843302581347073619315343260236801290191172812702425195020046538660872142038317950416346439601113215970446132169901138597990286754920224499406913165629069186945523870726476543725934376032237411431320278407206414248600077758111471741792921717197033306926007347459288354640636175297125740846290677747803896724051152378062656207157505255076217040857986874654379237885669204568187518245165413987977197132034587079899772908534310620111695779234887012052736179296649492962178117865657047670613868955823412297662451283265026927090879926482636073888919968094179585553537337586504210550112706986357851977939275509195691064571675643173526591465559182875806922031441888489072218032043654655383257016455635121114512090710162506497804808810920571083649762556829105177629933242508255536223571250332889229643943788382074256029646187546958470131854543092739998249818874352684696783765702637685668722538405405492891257027026947478987399621177023091985549846420107057627993445932851481923054051246753828515987021839371866820555243832340351019567756396418499528780641434720778907792969539976141649406874259209464361705882801384750373008612307997554572917348960297673606070321135781837420901580557301264030787873654125145507893380817619828679665194230027071872616789594859283496652449572244281193351116812347898107584110359083462725090851178216609184751670610121035758319477267157539495444666742344833360086626935379547317591970285965951160579824751134887911586168343206326311662131154955118807648593179935175682856426057953776331640247987300566584227843901974039771592060660930725769350856214353468909724157546834924251124275001676268462092014459433721877150692337215854518232005896191075122451171180402725773363147262641421120945599205727947781816573232683983949316892373745422578255654165229720631006977667702049560372742099445476049398893121953967811759616786023923793504313609122115527540591910465703040366437254880228389992408191135085678988948186542073328479980590573157750147940964301739166926027892182960968063117122531899021640740519331127891624366573820159781615556111850156799180065801682541105709303346853905404029977675198339126684158271278582910559725616014323665865943654840183176876630758029828813874945429672568201400282005296360913249920001579749648
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
 (.leaf 0x0))
 (.branch 24
 (.leaf 0x0)
 (.branch 28
 (.branch 26
 (.leaf 0x0)
 (.branch 27
 (.leaf 0x0)
 (.leaf (certNat% 1))))
 (.leaf 0x0))))
 (.branch 48
 (.branch 40
 (.leaf 0x0)
 (.branch 44
 (.leaf 0x0)
 (.branch 46
 (.branch 45
 (.leaf 0x0)
 (.leaf (certNat% 2)))
 (.leaf 0x0))))
 (.branch 56
 (.branch 52
 (.leaf 0x0)
 (.branch 54
 (.leaf 0x0)
 (.branch 55
 (.leaf (certNat% 3))
 (.leaf 0x0))))
 (.branch 60
 (.branch 58
 (.branch 57
 (.leaf (certNat% 4))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))))
 (.branch 96
 (.branch 80
 (.branch 72
 (.branch 68
 (.branch 66
 (.leaf 0x0)
 (.branch 67
 (.leaf 0x0)
 (.leaf (certNat% 5))))
 (.branch 70
 (.branch 69
 (.leaf 0x0)
 (.leaf (certNat% 6)))
 (.branch 71
 (.leaf (certNat% 7))
 (.leaf 0x0))))
 (.branch 76
 (.branch 74
 (.branch 73
 (.leaf 0x0)
 (.leaf (certNat% 8)))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 88
 (.branch 84
 (.branch 82
 (.leaf 0x0)
 (.branch 83
 (.leaf (certNat% 9))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 92
 (.branch 90
 (.branch 89
 (.leaf (certNat% 10))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 112
 (.branch 104
 (.branch 100
 (.leaf 0x0)
 (.branch 102
 (.branch 101
 (.leaf (certNat% 11))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 108
 (.branch 106
 (.branch 105
 (.leaf (certNat% 12))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 120
 (.branch 116
 (.branch 114
 (.branch 113
 (.leaf (certNat% 13))
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
 (.leaf (certNat% 14))))
 (.branch 134
 (.branch 133
 (.leaf 0x0)
 (.leaf (certNat% 15)))
 (.branch 135
 (.leaf (certNat% 16))
 (.leaf 0x0))))
 (.branch 140
 (.branch 138
 (.branch 137
 (.leaf 0x0)
 (.leaf (certNat% 17)))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 152
 (.branch 148
 (.branch 146
 (.leaf 0x0)
 (.branch 147
 (.leaf (certNat% 18))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 156
 (.branch 154
 (.branch 153
 (.leaf (certNat% 19))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 176
 (.branch 168
 (.branch 164
 (.leaf 0x0)
 (.branch 166
 (.branch 165
 (.leaf (certNat% 20))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 172
 (.branch 170
 (.branch 169
 (.leaf (certNat% 21))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 184
 (.branch 180
 (.branch 178
 (.branch 177
 (.leaf (certNat% 22))
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
 (.leaf (certNat% 23)))
 (.branch 195
 (.leaf (certNat% 24))
 (.leaf (certNat% 25))))
 (.branch 198
 (.branch 197
 (.leaf (certNat% 26))
 (.leaf (certNat% 27)))
 (.branch 199
 (.leaf (certNat% 28))
 (.leaf 0x0))))
 (.branch 204
 (.branch 202
 (.branch 201
 (.leaf (certNat% 29))
 (.leaf (certNat% 30)))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 216
 (.branch 212
 (.branch 210
 (.branch 209
 (.leaf (certNat% 31))
 (.leaf 0x0))
 (.branch 211
 (.leaf (certNat% 32))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 220
 (.branch 218
 (.branch 217
 (.leaf (certNat% 33))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 240
 (.branch 232
 (.branch 228
 (.branch 226
 (.branch 225
 (.leaf (certNat% 34))
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 230
 (.branch 229
 (.leaf (certNat% 35))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 236
 (.branch 234
 (.branch 233
 (.leaf (certNat% 36))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 248
 (.branch 244
 (.branch 242
 (.branch 241
 (.leaf (certNat% 37))
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
 (.leaf (certNat% 38))))
 (.branch 262
 (.branch 261
 (.leaf 0x0)
 (.leaf (certNat% 39)))
 (.branch 263
 (.leaf (certNat% 40))
 (.leaf 0x0))))
 (.branch 268
 (.branch 266
 (.branch 265
 (.leaf 0x0)
 (.leaf (certNat% 41)))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 280
 (.branch 276
 (.branch 274
 (.leaf 0x0)
 (.branch 275
 (.leaf (certNat% 42))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 284
 (.branch 282
 (.branch 281
 (.leaf (certNat% 43))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 304
 (.branch 296
 (.branch 292
 (.leaf 0x0)
 (.branch 294
 (.branch 293
 (.leaf (certNat% 44))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 300
 (.branch 298
 (.branch 297
 (.leaf (certNat% 45))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 312
 (.branch 308
 (.branch 306
 (.branch 305
 (.leaf (certNat% 46))
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
 (.leaf (certNat% 47)))
 (.branch 323
 (.leaf (certNat% 48))
 (.leaf (certNat% 49))))
 (.branch 326
 (.branch 325
 (.leaf (certNat% 50))
 (.leaf (certNat% 51)))
 (.branch 327
 (.leaf (certNat% 52))
 (.leaf 0x0))))
 (.branch 332
 (.branch 330
 (.branch 329
 (.leaf (certNat% 53))
 (.leaf (certNat% 54)))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 344
 (.branch 340
 (.branch 338
 (.branch 337
 (.leaf (certNat% 55))
 (.leaf 0x0))
 (.branch 339
 (.leaf (certNat% 56))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 348
 (.branch 346
 (.branch 345
 (.leaf (certNat% 57))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 368
 (.branch 360
 (.branch 356
 (.branch 354
 (.branch 353
 (.leaf (certNat% 58))
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 358
 (.branch 357
 (.leaf (certNat% 59))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 364
 (.branch 362
 (.branch 361
 (.leaf (certNat% 60))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 376
 (.branch 372
 (.branch 370
 (.branch 369
 (.leaf (certNat% 61))
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
 (.leaf (certNat% 62)))
 (.branch 387
 (.leaf (certNat% 63))
 (.leaf (certNat% 64))))
 (.branch 390
 (.branch 389
 (.leaf (certNat% 65))
 (.leaf (certNat% 66)))
 (.branch 391
 (.leaf (certNat% 67))
 (.leaf 0x0))))
 (.branch 396
 (.branch 394
 (.branch 393
 (.leaf (certNat% 68))
 (.leaf (certNat% 69)))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 408
 (.branch 404
 (.branch 402
 (.branch 401
 (.leaf (certNat% 70))
 (.leaf 0x0))
 (.branch 403
 (.leaf (certNat% 71))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 412
 (.branch 410
 (.branch 409
 (.leaf (certNat% 72))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 432
 (.branch 424
 (.branch 420
 (.branch 418
 (.branch 417
 (.leaf (certNat% 73))
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 422
 (.branch 421
 (.leaf (certNat% 74))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 428
 (.branch 426
 (.branch 425
 (.leaf (certNat% 75))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 440
 (.branch 436
 (.branch 434
 (.branch 433
 (.leaf (certNat% 76))
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
 (.leaf (certNat% 77))
 (.leaf (certNat% 78)))
 (.branch 451
 (.leaf (certNat% 79))
 (.leaf (certNat% 80))))
 (.branch 454
 (.branch 453
 (.leaf (certNat% 81))
 (.leaf (certNat% 82)))
 (.branch 455
 (.leaf (certNat% 83))
 (.leaf 0x0))))
 (.branch 460
 (.branch 458
 (.branch 457
 (.leaf (certNat% 84))
 (.leaf (certNat% 85)))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 472
 (.branch 468
 (.branch 466
 (.branch 465
 (.leaf (certNat% 86))
 (.leaf 0x0))
 (.branch 467
 (.leaf (certNat% 87))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 476
 (.branch 474
 (.branch 473
 (.leaf (certNat% 88))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 496
 (.branch 488
 (.branch 484
 (.branch 482
 (.branch 481
 (.leaf (certNat% 89))
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 486
 (.branch 485
 (.leaf (certNat% 90))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 492
 (.branch 490
 (.branch 489
 (.leaf (certNat% 91))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 504
 (.branch 500
 (.branch 498
 (.branch 497
 (.leaf (certNat% 92))
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
 (.leaf (certNat% 93))))
 (.branch 518
 (.branch 517
 (.leaf 0x0)
 (.leaf (certNat% 94)))
 (.branch 519
 (.leaf (certNat% 95))
 (.leaf 0x0))))
 (.branch 524
 (.branch 522
 (.branch 521
 (.leaf 0x0)
 (.leaf (certNat% 96)))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 536
 (.branch 532
 (.branch 530
 (.leaf 0x0)
 (.branch 531
 (.leaf (certNat% 97))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 540
 (.branch 538
 (.branch 537
 (.leaf (certNat% 98))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 560
 (.branch 552
 (.branch 548
 (.leaf 0x0)
 (.branch 550
 (.branch 549
 (.leaf (certNat% 99))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 556
 (.branch 554
 (.branch 553
 (.leaf (certNat% 100))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 568
 (.branch 564
 (.branch 562
 (.branch 561
 (.leaf (certNat% 101))
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
 (.leaf (certNat% 102)))
 (.branch 579
 (.leaf (certNat% 103))
 (.leaf (certNat% 104))))
 (.branch 582
 (.branch 581
 (.leaf (certNat% 105))
 (.leaf (certNat% 106)))
 (.branch 583
 (.leaf (certNat% 107))
 (.leaf 0x0))))
 (.branch 588
 (.branch 586
 (.branch 585
 (.leaf (certNat% 108))
 (.leaf (certNat% 109)))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 600
 (.branch 596
 (.branch 594
 (.branch 593
 (.leaf (certNat% 110))
 (.leaf 0x0))
 (.branch 595
 (.leaf (certNat% 111))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 604
 (.branch 602
 (.branch 601
 (.leaf (certNat% 112))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 624
 (.branch 616
 (.branch 612
 (.branch 610
 (.branch 609
 (.leaf (certNat% 113))
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 614
 (.branch 613
 (.leaf (certNat% 114))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 620
 (.branch 618
 (.branch 617
 (.leaf (certNat% 115))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 632
 (.branch 628
 (.branch 626
 (.branch 625
 (.leaf (certNat% 116))
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
 (.leaf (certNat% 117)))
 (.branch 643
 (.leaf (certNat% 118))
 (.leaf (certNat% 119))))
 (.branch 646
 (.branch 645
 (.leaf (certNat% 120))
 (.leaf (certNat% 121)))
 (.branch 647
 (.leaf (certNat% 122))
 (.leaf 0x0))))
 (.branch 652
 (.branch 650
 (.branch 649
 (.leaf (certNat% 123))
 (.leaf (certNat% 124)))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 664
 (.branch 660
 (.branch 658
 (.branch 657
 (.leaf (certNat% 125))
 (.leaf 0x0))
 (.branch 659
 (.leaf (certNat% 126))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 668
 (.branch 666
 (.branch 665
 (.leaf (certNat% 127))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 688
 (.branch 680
 (.branch 676
 (.branch 674
 (.branch 673
 (.leaf (certNat% 128))
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 678
 (.branch 677
 (.leaf (certNat% 129))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 684
 (.branch 682
 (.branch 681
 (.leaf (certNat% 130))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 696
 (.branch 692
 (.branch 690
 (.branch 689
 (.leaf (certNat% 131))
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
 (.leaf (certNat% 132))
 (.leaf (certNat% 133)))
 (.branch 707
 (.leaf (certNat% 134))
 (.leaf (certNat% 135))))
 (.branch 710
 (.branch 709
 (.leaf (certNat% 136))
 (.leaf (certNat% 137)))
 (.branch 711
 (.leaf (certNat% 138))
 (.leaf 0x0))))
 (.branch 716
 (.branch 714
 (.branch 713
 (.leaf (certNat% 139))
 (.leaf (certNat% 140)))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 728
 (.branch 724
 (.branch 722
 (.branch 721
 (.leaf (certNat% 141))
 (.leaf 0x0))
 (.branch 723
 (.leaf (certNat% 142))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 732
 (.branch 730
 (.branch 729
 (.leaf (certNat% 143))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 752
 (.branch 744
 (.branch 740
 (.branch 738
 (.branch 737
 (.leaf (certNat% 144))
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 742
 (.branch 741
 (.leaf (certNat% 145))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 748
 (.branch 746
 (.branch 745
 (.leaf (certNat% 146))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 760
 (.branch 756
 (.branch 754
 (.branch 753
 (.leaf (certNat% 147))
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
 (.leaf (certNat% 148)))
 (.branch 771
 (.leaf (certNat% 149))
 (.leaf (certNat% 150))))
 (.branch 774
 (.branch 773
 (.leaf (certNat% 151))
 (.leaf (certNat% 152)))
 (.branch 775
 (.leaf (certNat% 153))
 (.leaf 0x0))))
 (.branch 780
 (.branch 778
 (.branch 777
 (.leaf (certNat% 154))
 (.leaf (certNat% 155)))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 792
 (.branch 788
 (.branch 786
 (.branch 785
 (.leaf (certNat% 156))
 (.leaf 0x0))
 (.branch 787
 (.leaf (certNat% 157))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 796
 (.branch 794
 (.branch 793
 (.leaf (certNat% 158))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 816
 (.branch 808
 (.branch 804
 (.branch 802
 (.branch 801
 (.leaf (certNat% 159))
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 806
 (.branch 805
 (.leaf (certNat% 160))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 812
 (.branch 810
 (.branch 809
 (.leaf (certNat% 161))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 824
 (.branch 820
 (.branch 818
 (.branch 817
 (.leaf (certNat% 162))
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
 (.leaf (certNat% 163))
 (.leaf (certNat% 164)))
 (.branch 835
 (.leaf (certNat% 165))
 (.leaf (certNat% 166))))
 (.branch 838
 (.branch 837
 (.leaf (certNat% 167))
 (.leaf (certNat% 168)))
 (.branch 839
 (.leaf (certNat% 169))
 (.leaf 0x0))))
 (.branch 844
 (.branch 842
 (.branch 841
 (.leaf (certNat% 170))
 (.leaf (certNat% 171)))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 856
 (.branch 852
 (.branch 850
 (.branch 849
 (.leaf (certNat% 172))
 (.leaf 0x0))
 (.branch 851
 (.leaf (certNat% 173))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 860
 (.branch 858
 (.branch 857
 (.leaf (certNat% 174))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 880
 (.branch 872
 (.branch 868
 (.branch 866
 (.branch 865
 (.leaf (certNat% 175))
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 870
 (.branch 869
 (.leaf (certNat% 176))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 876
 (.branch 874
 (.branch 873
 (.leaf (certNat% 177))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 888
 (.branch 884
 (.branch 882
 (.branch 881
 (.leaf (certNat% 178))
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
 (.leaf (certNat% 179))
 (.leaf (certNat% 180)))
 (.branch 899
 (.leaf (certNat% 181))
 (.leaf (certNat% 182))))
 (.branch 902
 (.branch 901
 (.leaf (certNat% 183))
 (.leaf (certNat% 184)))
 (.branch 903
 (.leaf (certNat% 185))
 (.leaf 0x0))))
 (.branch 908
 (.branch 906
 (.branch 905
 (.leaf (certNat% 186))
 (.leaf (certNat% 187)))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 920
 (.branch 916
 (.branch 914
 (.branch 913
 (.leaf (certNat% 188))
 (.leaf 0x0))
 (.branch 915
 (.leaf (certNat% 189))
 (.leaf 0x0)))
 (.leaf 0x0))
 (.branch 924
 (.branch 922
 (.branch 921
 (.leaf (certNat% 190))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 944
 (.branch 936
 (.branch 932
 (.branch 930
 (.branch 929
 (.leaf (certNat% 191))
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 934
 (.branch 933
 (.leaf (certNat% 192))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 940
 (.branch 938
 (.branch 937
 (.leaf (certNat% 193))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 952
 (.branch 948
 (.branch 946
 (.branch 945
 (.leaf (certNat% 194))
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
 (.leaf (certNat% 195))
 (.leaf (certNat% 196)))
 (.branch 963
 (.leaf (certNat% 197))
 (.leaf 0x0)))
 (.branch 966
 (.branch 965
 (.leaf (certNat% 198))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 972
 (.branch 970
 (.branch 969
 (.leaf (certNat% 199))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 984
 (.branch 980
 (.branch 978
 (.branch 977
 (.leaf (certNat% 200))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 1008
 (.branch 1000
 (.branch 996
 (.branch 994
 (.branch 993
 (.leaf (certNat% 201))
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
 (.leaf (certNat% 202)))
 (.branch 3
 (.leaf (certNat% 203))
 (.branch 4
 (.leaf (certNat% 204))
 (.leaf 0x0))))
 (.branch 8
 (.leaf 0x0)
 (.branch 9
 (.leaf 0x0)
 (.branch 10
 (.leaf (certNat% 205))
 (.leaf (certNat% 206))))))
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
 (.leaf (certNat% 207)))
 (.branch 3
 (.leaf (certNat% 208))
 (.branch 4
 (.leaf (certNat% 209))
 (.leaf 0x0))))
 (.branch 8
 (.leaf 0x0)
 (.branch 9
 (.leaf 0x0)
 (.branch 10
 (.leaf (certNat% 210))
 (.leaf (certNat% 211))))))
def kindMasks := kindMaskTable.get
def keys := List.range 11
def vertexMaskTable : Table Nat :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf 20593584385689566374772843940890757682807130179374741208651285371953482044268526721524124205689214088296612288804247538577529647211972583008837204989399331527620411950266340489541623150182977161929445323694840761542481767422192277051029903694858260917696851542697922049753857122177642864080314463954639626277718849805233759602676871423154535752992702473828509800158180570987204096293270146395799100385842604505030316723168965254377849262499851923519044076059839644438057972008364008924359190632762949213456527106062151207901210837795898197777607171049147858943)
 (.leaf 5796578685350879150401812045851329961507106833489896736956795829519204939146943033500474010407206610117183719433086301232317321579281629105920960774648377247578270148540731063217137279972439042061051121101019989361478191676244994886420966627337272381714095313787475345381696498387885713515868205762905710024707305410456222330243395387672874901606149009747194735167002182620863086848714677453816366594718625050116138593907414349190079492004418049903751318894124505397845617352157459640881609397904651023051975794190544250609773640610488131545805192455190133649425110025635839))
 (.branch 3
 (.leaf 459252278109700178101282819841593559958766731220934528328787180187490403201705668259880395452172803104279802150331731226173517129407849718961372826288049478051860474877703733264787509284112314164173720970314147453364184095882670154533423911653363211868464787117973336241297115466670079848470924458717814841640802425475870444139892548924985663498279115532430421647837084191707829303753071818569570985443663594461031805002599311872630096601041723580062862159601141577550055887754352318826336806184835096821980458556735238878777802372810658457521452175817592672616209460681600977265227665222335075232905247)
 (.branch 4
 (.leaf 171826676839750753143404851648137407909271713599916411722661491441236720920506353375509206868778077042707743383689751424649197820013879827455556080258641093323595830457313375559278641834844159185038300866713858250446152549447653789632598280245479318785716986605376433665048094034223612609264267327576737676431289236944399141560898530728181277207823813979679985878324949985146502998009588407126783891858926296859350609092605866280845764693294742844458974662237500263385170480008996315384366759656689202127191174021952285964140725182785495738307067443470900636657633898348712470730744057741337136089088004452235169323929103501548045038440512190647271030785)
 (.leaf 171826676839750753143441237362262529228076137589041145231652789994201602634320495284071316228893762228331852017601229362969882553554441436343909254127527158585491890891853378009065776870160049019200781180661327568234957883447604324133408621461071343576276542826349786853596186449640863220608381522905808261100228520665407372066730798727658380461470163573311179965451264649959156610390621973431651542743946631440576112822824058416838342070531353083211427361357926515896191016410048461417278082542283056256715743992383021512941749812301761222668316128230338774553012357638992699183091774135655893161128076845303647940088997240949591098617353013960422457345))))
 (.branch 7
 (.branch 6
 (.leaf 171826676839750753143441237362262529357344161874285174434512296745618226775175647004465952036736508435712437453292262262353401750325295682274984479009839609547334463963986528232405624410688910413403552642123510770899522894128272610579054307908728108791454404928349645056798164164686107476252017267093381875319636101909334190630439488347344462977688502898983618750056880355864755007024011666780549262695798139921609142461863130029055860172581532753666546237503095928691297052727614529191008759370449256777731093639322458471023049224345464396857223963305478346912585971436459710778143854499120946524357612508455336623074745654106707762719628164526438875137)
 (.leaf 655466754302027714322819661568689458302857062813893029916810214032172464849991899428175362385124675671558840177545095211517425649255320518802145166421765834000253021422820451087019752506372047041506883704853372470577112180310066551503372657965798026649912503501169066815168945584710017225638003740598476192715456789907852167309507617439790192996430831576767971500709242062626472981264786726027373523847416087696572926086485303827781275083680843916810475980320413652047801989267486092991250294305941384632858793148377182567640430563351969945516777388628229076110083730784248164821765437991046415676935150290953996923407246658202906610852469511436514))
 (.branch 8
 (.leaf 171826021375496858351070953369821189479411926591925031832123756546520688697862025799241854546275798410562156742825917096677750991961842837658711683142999673867089260134246775263325386782316097729340719901680620345214724235705656259586879691627429698292882425724359669678356078537070695602838890427976096827121157195207753106273236246231019685912113466799587456000387465098457616319180082396105541380175819666300664579324551758901161323157475835583749142005827875510370937021833900552294564027744294970517171814322817816898568426600344567263910119244444827295942675566483895174028865357872390186200772561775701748472038797739176264178686224410379809901348)
 (.branch 9
 (.leaf 171826676837250355446393842150913070886656761314915963771126514930613921068835709717911773912831473586851852049547352589153457407288817844500685324320676820142617600493972274332955604438168546199793701788982940232267364804199723875125094362021879100360543499702364656566693082622780944870988788908227308753459281713052269960487753836195528258170585538102423964827235563410187339094643162919301252457919577802615777843385048778908112060366043032277844590633996777247285701019532047269431568561444980421766526739806428152944638235686806567192705728635755013486840312327410051752986359752638341096599674955863051629818781217094517537221752925073574110516552)
 (.leaf 171826676839750743605180979460516880593845967418564046469688904314915618201832730338959437296007768126018021367537872003809114129191342132582834227113192298952532286805085096772310094837839397562963261985521491117320147875681466536437406182681564899865166444817237616415092024598120633848046551012713244778438990014834593491747801954991570262308547776574858909920334158425023575438422911559310647410438922438126017750397921335600259853588509635371991512699505763615364585922296060736845036202417813239685362023624068264212481236726129612861473092026414833930093852517514832482984219210947620069232901406887993381036625004050768782315133379952771951339152)))))
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
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 24
 (.branch 20
 (.branch 18
 (.leaf (.leaf 0))
 (.branch 19
 (.leaf (.leaf 5))
 (.leaf (.leaf 0))))
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
 (.leaf (.leaf 0))
 (.branch 38
 (.branch 37
 (.leaf (.leaf 8))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 44
 (.branch 42
 (.branch 41
 (.leaf (.leaf 9))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 46
 (.branch 45
 (.leaf (.leaf 0))
 (.leaf (.leaf 10)))
 (.leaf (.leaf 0)))))
 (.branch 56
 (.branch 52
 (.branch 50
 (.branch 49
 (.leaf (.leaf 11))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 54
 (.leaf (.leaf 0))
 (.branch 55
 (.leaf (.leaf 12))
 (.leaf (.leaf 0)))))
 (.branch 60
 (.branch 58
 (.branch 57
 (.leaf (.leaf 13))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))))
 (.branch 96
 (.branch 80
 (.branch 72
 (.branch 68
 (.branch 66
 (.branch 65
 (.leaf (.leaf 0))
 (.leaf (.leaf 14)))
 (.branch 67
 (.leaf (.leaf 15))
 (.leaf (.leaf 16))))
 (.branch 70
 (.branch 69
 (.leaf (.leaf 17))
 (.leaf (.leaf 18)))
 (.branch 71
 (.leaf (.leaf 19))
 (.leaf (.leaf 0)))))
 (.branch 76
 (.branch 74
 (.branch 73
 (.leaf (.leaf 20))
 (.leaf (.leaf 21)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 88
 (.branch 84
 (.branch 82
 (.branch 81
 (.leaf (.leaf 22))
 (.leaf (.leaf 0)))
 (.branch 83
 (.leaf (.leaf 23))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
 (.branch 92
 (.branch 90
 (.branch 89
 (.leaf (.leaf 24))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 112
 (.branch 104
 (.branch 100
 (.branch 98
 (.branch 97
 (.leaf (.leaf 25))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 102
 (.branch 101
 (.leaf (.leaf 26))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 108
 (.branch 106
 (.branch 105
 (.leaf (.leaf 27))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 120
 (.branch 116
 (.branch 114
 (.branch 113
 (.leaf (.leaf 28))
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
 (.leaf (.leaf 29)))
 (.branch 131
 (.leaf (.leaf 30))
 (.leaf (.leaf 31))))
 (.branch 134
 (.branch 133
 (.leaf (.leaf 32))
 (.leaf (.leaf 33)))
 (.branch 135
 (.leaf (.leaf 34))
 (.leaf (.leaf 0)))))
 (.branch 140
 (.branch 138
 (.branch 137
 (.leaf (.leaf 35))
 (.leaf (.leaf 36)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 152
 (.branch 148
 (.branch 146
 (.branch 145
 (.leaf (.leaf 37))
 (.leaf (.leaf 0)))
 (.branch 147
 (.leaf (.leaf 38))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
 (.branch 156
 (.branch 154
 (.branch 153
 (.leaf (.leaf 39))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 176
 (.branch 168
 (.branch 164
 (.branch 162
 (.branch 161
 (.leaf (.leaf 40))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 166
 (.branch 165
 (.leaf (.leaf 41))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 172
 (.branch 170
 (.branch 169
 (.leaf (.leaf 42))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 184
 (.branch 180
 (.branch 178
 (.branch 177
 (.leaf (.leaf 43))
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
 (.leaf (.leaf 44))
 (.leaf (.leaf 45)))
 (.branch 195
 (.leaf (.leaf 46))
 (.leaf (.branch (certNat% 212) (.leaf 47) (.leaf 48)))))
 (.branch 198
 (.branch 197
 (.leaf (.leaf 49))
 (.leaf (.branch (certNat% 213) (.leaf 50) (.leaf 51))))
 (.branch 199
 (.leaf (.branch (certNat% 214) (.leaf 52) (.leaf 53)))
 (.leaf (.leaf 0)))))
 (.branch 204
 (.branch 202
 (.branch 201
 (.leaf (.leaf 54))
 (.leaf (.branch (certNat% 215) (.leaf 55) (.leaf 56))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 216
 (.branch 212
 (.branch 210
 (.branch 209
 (.leaf (.leaf 57))
 (.leaf (.leaf 0)))
 (.branch 211
 (.leaf (.branch (certNat% 216) (.leaf 58) (.leaf 59)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
 (.branch 220
 (.branch 218
 (.branch 217
 (.leaf (.branch (certNat% 217) (.leaf 60) (.leaf 61)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 240
 (.branch 232
 (.branch 228
 (.branch 226
 (.branch 225
 (.leaf (.leaf 62))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 230
 (.branch 229
 (.leaf (.branch (certNat% 218) (.leaf 63) (.leaf 64)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 236
 (.branch 234
 (.branch 233
 (.leaf (.branch (certNat% 219) (.leaf 65) (.leaf 66)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 248
 (.branch 244
 (.branch 242
 (.branch 241
 (.leaf (.branch (certNat% 220) (.leaf 67) (.leaf 68)))
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
 (.leaf (.leaf 69)))
 (.branch 259
 (.leaf (.leaf 70))
 (.leaf (.leaf 71))))
 (.branch 262
 (.branch 261
 (.leaf (.leaf 72))
 (.leaf (.leaf 73)))
 (.branch 263
 (.leaf (.leaf 74))
 (.leaf (.leaf 0)))))
 (.branch 268
 (.branch 266
 (.branch 265
 (.leaf (.leaf 75))
 (.leaf (.leaf 76)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 280
 (.branch 276
 (.branch 274
 (.branch 273
 (.leaf (.leaf 77))
 (.leaf (.leaf 0)))
 (.branch 275
 (.leaf (.leaf 78))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
 (.branch 284
 (.branch 282
 (.branch 281
 (.leaf (.leaf 79))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 304
 (.branch 296
 (.branch 292
 (.branch 290
 (.branch 289
 (.leaf (.leaf 80))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 294
 (.branch 293
 (.leaf (.leaf 81))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 300
 (.branch 298
 (.branch 297
 (.leaf (.leaf 82))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 312
 (.branch 308
 (.branch 306
 (.branch 305
 (.leaf (.leaf 83))
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
 (.leaf (.leaf 84))
 (.leaf (.leaf 85)))
 (.branch 323
 (.leaf (.leaf 86))
 (.leaf (.branch (certNat% 221) (.leaf 87) (.leaf 88)))))
 (.branch 326
 (.branch 325
 (.leaf (.leaf 89))
 (.leaf (.branch (certNat% 222) (.leaf 90) (.leaf 91))))
 (.branch 327
 (.leaf (.branch (certNat% 223) (.leaf 92) (.leaf 93)))
 (.leaf (.leaf 0)))))
 (.branch 332
 (.branch 330
 (.branch 329
 (.leaf (.leaf 94))
 (.leaf (.branch (certNat% 224) (.leaf 95) (.leaf 96))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 344
 (.branch 340
 (.branch 338
 (.branch 337
 (.leaf (.leaf 97))
 (.leaf (.leaf 0)))
 (.branch 339
 (.leaf (.branch (certNat% 225) (.leaf 98) (.leaf 99)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
 (.branch 348
 (.branch 346
 (.branch 345
 (.leaf (.branch (certNat% 226) (.leaf 100) (.leaf 101)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 368
 (.branch 360
 (.branch 356
 (.branch 354
 (.branch 353
 (.leaf (.leaf 102))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 358
 (.branch 357
 (.leaf (.branch (certNat% 227) (.leaf 103) (.leaf 104)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 364
 (.branch 362
 (.branch 361
 (.leaf (.branch (certNat% 228) (.leaf 105) (.leaf 106)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 376
 (.branch 372
 (.branch 370
 (.branch 369
 (.leaf (.branch (certNat% 229) (.leaf 107) (.leaf 108)))
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
 (.leaf (.leaf 109))
 (.leaf (.leaf 110)))
 (.branch 387
 (.leaf (.leaf 111))
 (.leaf (.branch (certNat% 230) (.leaf 112) (.leaf 113)))))
 (.branch 390
 (.branch 389
 (.leaf (.leaf 114))
 (.leaf (.branch (certNat% 231) (.leaf 115) (.leaf 116))))
 (.branch 391
 (.leaf (.branch (certNat% 232) (.leaf 117) (.leaf 118)))
 (.leaf (.leaf 0)))))
 (.branch 396
 (.branch 394
 (.branch 393
 (.leaf (.leaf 119))
 (.leaf (.branch (certNat% 233) (.leaf 120) (.leaf 121))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 408
 (.branch 404
 (.branch 402
 (.branch 401
 (.leaf (.leaf 122))
 (.leaf (.leaf 0)))
 (.branch 403
 (.leaf (.branch (certNat% 234) (.leaf 123) (.leaf 124)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
 (.branch 412
 (.branch 410
 (.branch 409
 (.leaf (.branch (certNat% 235) (.leaf 125) (.leaf 126)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 432
 (.branch 424
 (.branch 420
 (.branch 418
 (.branch 417
 (.leaf (.leaf 127))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 422
 (.branch 421
 (.leaf (.branch (certNat% 236) (.leaf 128) (.leaf 129)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 428
 (.branch 426
 (.branch 425
 (.leaf (.branch (certNat% 237) (.leaf 130) (.leaf 131)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 440
 (.branch 436
 (.branch 434
 (.branch 433
 (.leaf (.branch (certNat% 238) (.leaf 132) (.leaf 133)))
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
 (.leaf (.leaf 134))
 (.leaf (.branch (certNat% 239) (.leaf 135) (.branch (certNat% 240) (.leaf 136) (.leaf 137)))))
 (.branch 451
 (.leaf (.branch (certNat% 241) (.leaf 138) (.branch (certNat% 242) (.leaf 139) (.leaf 140))))
 (.leaf (.branch (certNat% 243) (.branch (certNat% 244) (.leaf 141) (.branch (certNat% 245) (.leaf 142) (.leaf 143))) (.branch (certNat% 246) (.leaf 144) (.branch (certNat% 247) (.leaf 145) (.leaf 146)))))))
 (.branch 454
 (.branch 453
 (.leaf (.branch (certNat% 248) (.leaf 147) (.branch (certNat% 249) (.leaf 148) (.leaf 149))))
 (.leaf (.branch (certNat% 250) (.branch (certNat% 251) (.leaf 150) (.branch (certNat% 252) (.leaf 151) (.leaf 152))) (.branch (certNat% 253) (.leaf 153) (.branch (certNat% 254) (.leaf 154) (.leaf 155))))))
 (.branch 455
 (.leaf (.branch (certNat% 255) (.branch (certNat% 256) (.leaf 156) (.branch (certNat% 257) (.leaf 157) (.leaf 158))) (.branch (certNat% 258) (.leaf 159) (.branch (certNat% 259) (.leaf 160) (.leaf 161)))))
 (.leaf (.leaf 0)))))
 (.branch 460
 (.branch 458
 (.branch 457
 (.leaf (.branch (certNat% 260) (.leaf 162) (.branch (certNat% 261) (.leaf 163) (.leaf 164))))
 (.leaf (.branch (certNat% 262) (.branch (certNat% 263) (.leaf 165) (.branch (certNat% 264) (.leaf 166) (.leaf 167))) (.branch (certNat% 265) (.leaf 168) (.branch (certNat% 266) (.leaf 169) (.leaf 170))))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 472
 (.branch 468
 (.branch 466
 (.branch 465
 (.leaf (.branch (certNat% 267) (.leaf 171) (.branch (certNat% 268) (.leaf 172) (.leaf 173))))
 (.leaf (.leaf 0)))
 (.branch 467
 (.leaf (.branch (certNat% 269) (.branch (certNat% 270) (.leaf 174) (.branch (certNat% 271) (.leaf 175) (.leaf 176))) (.branch (certNat% 272) (.leaf 177) (.branch (certNat% 273) (.leaf 178) (.leaf 179)))))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
 (.branch 476
 (.branch 474
 (.branch 473
 (.leaf (.branch (certNat% 274) (.branch (certNat% 275) (.leaf 180) (.branch (certNat% 276) (.leaf 181) (.leaf 182))) (.branch (certNat% 277) (.leaf 183) (.branch (certNat% 278) (.leaf 184) (.leaf 185)))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 496
 (.branch 488
 (.branch 484
 (.branch 482
 (.branch 481
 (.leaf (.branch (certNat% 279) (.leaf 186) (.branch (certNat% 280) (.leaf 187) (.leaf 188))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 486
 (.branch 485
 (.leaf (.branch (certNat% 281) (.branch (certNat% 282) (.leaf 189) (.branch (certNat% 283) (.leaf 190) (.leaf 191))) (.branch (certNat% 284) (.leaf 192) (.branch (certNat% 285) (.leaf 193) (.leaf 194)))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 492
 (.branch 490
 (.branch 489
 (.leaf (.branch (certNat% 286) (.branch (certNat% 287) (.leaf 195) (.branch (certNat% 288) (.leaf 196) (.leaf 197))) (.branch (certNat% 289) (.leaf 198) (.branch (certNat% 290) (.leaf 199) (.leaf 200)))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 504
 (.branch 500
 (.branch 498
 (.branch 497
 (.leaf (.branch (certNat% 291) (.branch (certNat% 292) (.leaf 201) (.branch (certNat% 293) (.leaf 202) (.leaf 203))) (.branch (certNat% 294) (.leaf 204) (.branch (certNat% 295) (.leaf 205) (.leaf 206)))))
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
 (.leaf (.leaf 207)))
 (.branch 515
 (.leaf (.leaf 208))
 (.leaf (.leaf 209))))
 (.branch 518
 (.branch 517
 (.leaf (.leaf 210))
 (.leaf (.leaf 211)))
 (.branch 519
 (.leaf (.leaf 212))
 (.leaf (.leaf 0)))))
 (.branch 524
 (.branch 522
 (.branch 521
 (.leaf (.leaf 213))
 (.leaf (.leaf 214)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 536
 (.branch 532
 (.branch 530
 (.branch 529
 (.leaf (.leaf 215))
 (.leaf (.leaf 0)))
 (.branch 531
 (.leaf (.leaf 216))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
 (.branch 540
 (.branch 538
 (.branch 537
 (.leaf (.leaf 217))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 560
 (.branch 552
 (.branch 548
 (.branch 546
 (.branch 545
 (.leaf (.leaf 218))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 550
 (.branch 549
 (.leaf (.leaf 219))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 556
 (.branch 554
 (.branch 553
 (.leaf (.leaf 220))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 568
 (.branch 564
 (.branch 562
 (.branch 561
 (.leaf (.leaf 221))
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
 (.leaf (.leaf 222))
 (.leaf (.leaf 223)))
 (.branch 579
 (.leaf (.leaf 224))
 (.leaf (.branch (certNat% 296) (.leaf 225) (.leaf 226)))))
 (.branch 582
 (.branch 581
 (.leaf (.leaf 227))
 (.leaf (.branch (certNat% 297) (.leaf 228) (.leaf 229))))
 (.branch 583
 (.leaf (.branch (certNat% 298) (.leaf 230) (.leaf 231)))
 (.leaf (.leaf 0)))))
 (.branch 588
 (.branch 586
 (.branch 585
 (.leaf (.leaf 232))
 (.leaf (.branch (certNat% 299) (.leaf 233) (.leaf 234))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 600
 (.branch 596
 (.branch 594
 (.branch 593
 (.leaf (.leaf 235))
 (.leaf (.leaf 0)))
 (.branch 595
 (.leaf (.branch (certNat% 300) (.leaf 236) (.leaf 237)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
 (.branch 604
 (.branch 602
 (.branch 601
 (.leaf (.branch (certNat% 301) (.leaf 238) (.leaf 239)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 624
 (.branch 616
 (.branch 612
 (.branch 610
 (.branch 609
 (.leaf (.leaf 240))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 614
 (.branch 613
 (.leaf (.branch (certNat% 302) (.leaf 241) (.leaf 242)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 620
 (.branch 618
 (.branch 617
 (.leaf (.branch (certNat% 303) (.leaf 243) (.leaf 244)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 632
 (.branch 628
 (.branch 626
 (.branch 625
 (.leaf (.branch (certNat% 304) (.leaf 245) (.leaf 246)))
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
 (.leaf (.leaf 247))
 (.leaf (.leaf 248)))
 (.branch 643
 (.leaf (.leaf 249))
 (.leaf (.branch (certNat% 305) (.leaf 250) (.leaf 251)))))
 (.branch 646
 (.branch 645
 (.leaf (.leaf 252))
 (.leaf (.branch (certNat% 306) (.leaf 253) (.leaf 254))))
 (.branch 647
 (.leaf (.branch (certNat% 307) (.leaf 255) (.leaf 256)))
 (.leaf (.leaf 0)))))
 (.branch 652
 (.branch 650
 (.branch 649
 (.leaf (.leaf 257))
 (.leaf (.branch (certNat% 308) (.leaf 258) (.leaf 259))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 664
 (.branch 660
 (.branch 658
 (.branch 657
 (.leaf (.leaf 260))
 (.leaf (.leaf 0)))
 (.branch 659
 (.leaf (.branch (certNat% 309) (.leaf 261) (.leaf 262)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
 (.branch 668
 (.branch 666
 (.branch 665
 (.leaf (.branch (certNat% 310) (.leaf 263) (.leaf 264)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 688
 (.branch 680
 (.branch 676
 (.branch 674
 (.branch 673
 (.leaf (.leaf 265))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 678
 (.branch 677
 (.leaf (.branch (certNat% 311) (.leaf 266) (.leaf 267)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 684
 (.branch 682
 (.branch 681
 (.leaf (.branch (certNat% 312) (.leaf 268) (.leaf 269)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 696
 (.branch 692
 (.branch 690
 (.branch 689
 (.leaf (.branch (certNat% 313) (.leaf 270) (.leaf 271)))
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
 (.leaf (.leaf 272))
 (.leaf (.branch (certNat% 314) (.leaf 273) (.branch (certNat% 315) (.leaf 274) (.leaf 275)))))
 (.branch 707
 (.leaf (.branch (certNat% 316) (.leaf 276) (.branch (certNat% 317) (.leaf 277) (.leaf 278))))
 (.leaf (.branch (certNat% 318) (.branch (certNat% 319) (.leaf 279) (.branch (certNat% 320) (.leaf 280) (.leaf 281))) (.branch (certNat% 321) (.leaf 282) (.branch (certNat% 322) (.leaf 283) (.leaf 284)))))))
 (.branch 710
 (.branch 709
 (.leaf (.branch (certNat% 323) (.leaf 285) (.branch (certNat% 324) (.leaf 286) (.leaf 287))))
 (.leaf (.branch (certNat% 325) (.branch (certNat% 326) (.leaf 288) (.branch (certNat% 327) (.leaf 289) (.leaf 290))) (.branch (certNat% 328) (.leaf 291) (.branch (certNat% 329) (.leaf 292) (.leaf 293))))))
 (.branch 711
 (.leaf (.branch (certNat% 330) (.branch (certNat% 331) (.leaf 294) (.branch (certNat% 332) (.leaf 295) (.leaf 296))) (.branch (certNat% 333) (.leaf 297) (.branch (certNat% 334) (.leaf 298) (.leaf 299)))))
 (.leaf (.leaf 0)))))
 (.branch 716
 (.branch 714
 (.branch 713
 (.leaf (.branch (certNat% 335) (.leaf 300) (.branch (certNat% 336) (.leaf 301) (.leaf 302))))
 (.leaf (.branch (certNat% 337) (.branch (certNat% 338) (.leaf 303) (.branch (certNat% 339) (.leaf 304) (.leaf 305))) (.branch (certNat% 340) (.leaf 306) (.branch (certNat% 341) (.leaf 307) (.leaf 308))))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 728
 (.branch 724
 (.branch 722
 (.branch 721
 (.leaf (.branch (certNat% 342) (.leaf 309) (.branch (certNat% 343) (.leaf 310) (.leaf 311))))
 (.leaf (.leaf 0)))
 (.branch 723
 (.leaf (.branch (certNat% 344) (.branch (certNat% 345) (.leaf 312) (.branch (certNat% 346) (.leaf 313) (.leaf 314))) (.branch (certNat% 347) (.leaf 315) (.branch (certNat% 348) (.leaf 316) (.leaf 317)))))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
 (.branch 732
 (.branch 730
 (.branch 729
 (.leaf (.branch (certNat% 349) (.branch (certNat% 350) (.leaf 318) (.branch (certNat% 351) (.leaf 319) (.leaf 320))) (.branch (certNat% 352) (.leaf 321) (.branch (certNat% 353) (.leaf 322) (.leaf 323)))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 752
 (.branch 744
 (.branch 740
 (.branch 738
 (.branch 737
 (.leaf (.branch (certNat% 354) (.leaf 324) (.branch (certNat% 355) (.leaf 325) (.leaf 326))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 742
 (.branch 741
 (.leaf (.branch (certNat% 356) (.branch (certNat% 357) (.leaf 327) (.branch (certNat% 358) (.leaf 328) (.leaf 329))) (.branch (certNat% 359) (.leaf 330) (.branch (certNat% 360) (.leaf 331) (.leaf 332)))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 748
 (.branch 746
 (.branch 745
 (.leaf (.branch (certNat% 361) (.branch (certNat% 362) (.leaf 333) (.branch (certNat% 363) (.leaf 334) (.leaf 335))) (.branch (certNat% 364) (.leaf 336) (.branch (certNat% 365) (.leaf 337) (.leaf 338)))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 760
 (.branch 756
 (.branch 754
 (.branch 753
 (.leaf (.branch (certNat% 366) (.branch (certNat% 367) (.leaf 339) (.branch (certNat% 368) (.leaf 340) (.leaf 341))) (.branch (certNat% 369) (.leaf 342) (.branch (certNat% 370) (.leaf 343) (.leaf 344)))))
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
 (.leaf (.leaf 345))
 (.leaf (.leaf 346)))
 (.branch 771
 (.leaf (.leaf 347))
 (.leaf (.branch (certNat% 371) (.leaf 348) (.leaf 349)))))
 (.branch 774
 (.branch 773
 (.leaf (.leaf 350))
 (.leaf (.branch (certNat% 372) (.leaf 351) (.leaf 352))))
 (.branch 775
 (.leaf (.branch (certNat% 373) (.leaf 353) (.leaf 354)))
 (.leaf (.leaf 0)))))
 (.branch 780
 (.branch 778
 (.branch 777
 (.leaf (.leaf 355))
 (.leaf (.branch (certNat% 374) (.leaf 356) (.leaf 357))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 792
 (.branch 788
 (.branch 786
 (.branch 785
 (.leaf (.leaf 358))
 (.leaf (.leaf 0)))
 (.branch 787
 (.leaf (.branch (certNat% 375) (.leaf 359) (.leaf 360)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
 (.branch 796
 (.branch 794
 (.branch 793
 (.leaf (.branch (certNat% 376) (.leaf 361) (.leaf 362)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 816
 (.branch 808
 (.branch 804
 (.branch 802
 (.branch 801
 (.leaf (.leaf 363))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 806
 (.branch 805
 (.leaf (.branch (certNat% 377) (.leaf 364) (.leaf 365)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 812
 (.branch 810
 (.branch 809
 (.leaf (.branch (certNat% 378) (.leaf 366) (.leaf 367)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 824
 (.branch 820
 (.branch 818
 (.branch 817
 (.leaf (.branch (certNat% 379) (.leaf 368) (.leaf 369)))
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
 (.leaf (.leaf 370))
 (.leaf (.branch (certNat% 380) (.leaf 371) (.branch (certNat% 381) (.leaf 372) (.leaf 373)))))
 (.branch 835
 (.leaf (.branch (certNat% 382) (.leaf 374) (.branch (certNat% 383) (.leaf 375) (.leaf 376))))
 (.leaf (.branch (certNat% 384) (.branch (certNat% 385) (.leaf 377) (.branch (certNat% 386) (.leaf 378) (.leaf 379))) (.branch (certNat% 387) (.leaf 380) (.branch (certNat% 388) (.leaf 381) (.leaf 382)))))))
 (.branch 838
 (.branch 837
 (.leaf (.branch (certNat% 389) (.leaf 383) (.branch (certNat% 390) (.leaf 384) (.leaf 385))))
 (.leaf (.branch (certNat% 391) (.branch (certNat% 392) (.leaf 386) (.branch (certNat% 393) (.leaf 387) (.leaf 388))) (.branch (certNat% 394) (.leaf 389) (.branch (certNat% 395) (.leaf 390) (.leaf 391))))))
 (.branch 839
 (.leaf (.branch (certNat% 396) (.branch (certNat% 397) (.leaf 392) (.branch (certNat% 398) (.leaf 393) (.leaf 394))) (.branch (certNat% 399) (.leaf 395) (.branch (certNat% 400) (.leaf 396) (.leaf 397)))))
 (.leaf (.leaf 0)))))
 (.branch 844
 (.branch 842
 (.branch 841
 (.leaf (.branch (certNat% 401) (.leaf 398) (.branch (certNat% 402) (.leaf 399) (.leaf 400))))
 (.leaf (.branch (certNat% 403) (.branch (certNat% 404) (.leaf 401) (.branch (certNat% 405) (.leaf 402) (.leaf 403))) (.branch (certNat% 406) (.leaf 404) (.branch (certNat% 407) (.leaf 405) (.leaf 406))))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 856
 (.branch 852
 (.branch 850
 (.branch 849
 (.leaf (.branch (certNat% 408) (.leaf 407) (.branch (certNat% 409) (.leaf 408) (.leaf 409))))
 (.leaf (.leaf 0)))
 (.branch 851
 (.leaf (.branch (certNat% 410) (.branch (certNat% 411) (.leaf 410) (.branch (certNat% 412) (.leaf 411) (.leaf 412))) (.branch (certNat% 413) (.leaf 413) (.branch (certNat% 414) (.leaf 414) (.leaf 415)))))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
 (.branch 860
 (.branch 858
 (.branch 857
 (.leaf (.branch (certNat% 415) (.branch (certNat% 416) (.leaf 416) (.branch (certNat% 417) (.leaf 417) (.leaf 418))) (.branch (certNat% 418) (.leaf 419) (.branch (certNat% 419) (.leaf 420) (.leaf 421)))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 880
 (.branch 872
 (.branch 868
 (.branch 866
 (.branch 865
 (.leaf (.branch (certNat% 420) (.leaf 422) (.branch (certNat% 421) (.leaf 423) (.leaf 424))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 870
 (.branch 869
 (.leaf (.branch (certNat% 422) (.branch (certNat% 423) (.leaf 425) (.branch (certNat% 424) (.leaf 426) (.leaf 427))) (.branch (certNat% 425) (.leaf 428) (.branch (certNat% 426) (.leaf 429) (.leaf 430)))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 876
 (.branch 874
 (.branch 873
 (.leaf (.branch (certNat% 427) (.branch (certNat% 428) (.leaf 431) (.branch (certNat% 429) (.leaf 432) (.leaf 433))) (.branch (certNat% 430) (.leaf 434) (.branch (certNat% 431) (.leaf 435) (.leaf 436)))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 888
 (.branch 884
 (.branch 882
 (.branch 881
 (.leaf (.branch (certNat% 432) (.branch (certNat% 433) (.leaf 437) (.branch (certNat% 434) (.leaf 438) (.leaf 439))) (.branch (certNat% 435) (.leaf 440) (.branch (certNat% 436) (.leaf 441) (.leaf 442)))))
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
 (.leaf (.leaf 443))
 (.leaf (.branch (certNat% 437) (.leaf 444) (.branch (certNat% 438) (.leaf 445) (.leaf 446)))))
 (.branch 899
 (.leaf (.branch (certNat% 439) (.leaf 447) (.branch (certNat% 440) (.leaf 448) (.leaf 449))))
 (.leaf (.branch (certNat% 441) (.branch (certNat% 442) (.leaf 450) (.branch (certNat% 443) (.leaf 451) (.leaf 452))) (.branch (certNat% 444) (.leaf 453) (.branch (certNat% 445) (.leaf 454) (.leaf 455)))))))
 (.branch 902
 (.branch 901
 (.leaf (.branch (certNat% 446) (.leaf 456) (.branch (certNat% 447) (.leaf 457) (.leaf 458))))
 (.leaf (.branch (certNat% 448) (.branch (certNat% 449) (.leaf 459) (.branch (certNat% 450) (.leaf 460) (.leaf 461))) (.branch (certNat% 451) (.leaf 462) (.branch (certNat% 452) (.leaf 463) (.leaf 464))))))
 (.branch 903
 (.leaf (.branch (certNat% 453) (.branch (certNat% 454) (.leaf 465) (.branch (certNat% 455) (.leaf 466) (.leaf 467))) (.branch (certNat% 456) (.leaf 468) (.branch (certNat% 457) (.leaf 469) (.leaf 470)))))
 (.leaf (.leaf 0)))))
 (.branch 908
 (.branch 906
 (.branch 905
 (.leaf (.branch (certNat% 458) (.leaf 471) (.branch (certNat% 459) (.leaf 472) (.leaf 473))))
 (.leaf (.branch (certNat% 460) (.branch (certNat% 461) (.leaf 474) (.branch (certNat% 462) (.leaf 475) (.leaf 476))) (.branch (certNat% 463) (.leaf 477) (.branch (certNat% 464) (.leaf 478) (.leaf 479))))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 920
 (.branch 916
 (.branch 914
 (.branch 913
 (.leaf (.branch (certNat% 465) (.leaf 480) (.branch (certNat% 466) (.leaf 481) (.leaf 482))))
 (.leaf (.leaf 0)))
 (.branch 915
 (.leaf (.branch (certNat% 467) (.branch (certNat% 468) (.leaf 483) (.branch (certNat% 469) (.leaf 484) (.leaf 485))) (.branch (certNat% 470) (.leaf 486) (.branch (certNat% 471) (.leaf 487) (.leaf 488)))))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0)))
 (.branch 924
 (.branch 922
 (.branch 921
 (.leaf (.branch (certNat% 472) (.branch (certNat% 473) (.leaf 489) (.branch (certNat% 474) (.leaf 490) (.leaf 491))) (.branch (certNat% 475) (.leaf 492) (.branch (certNat% 476) (.leaf 493) (.leaf 494)))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 944
 (.branch 936
 (.branch 932
 (.branch 930
 (.branch 929
 (.leaf (.branch (certNat% 477) (.leaf 495) (.branch (certNat% 478) (.leaf 496) (.leaf 497))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 934
 (.branch 933
 (.leaf (.branch (certNat% 479) (.branch (certNat% 480) (.leaf 498) (.branch (certNat% 481) (.leaf 499) (.leaf 500))) (.branch (certNat% 482) (.leaf 501) (.branch (certNat% 483) (.leaf 502) (.leaf 503)))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 940
 (.branch 938
 (.branch 937
 (.leaf (.branch (certNat% 484) (.branch (certNat% 485) (.leaf 504) (.branch (certNat% 486) (.leaf 505) (.leaf 506))) (.branch (certNat% 487) (.leaf 507) (.branch (certNat% 488) (.leaf 508) (.leaf 509)))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 952
 (.branch 948
 (.branch 946
 (.branch 945
 (.leaf (.branch (certNat% 489) (.branch (certNat% 490) (.leaf 510) (.branch (certNat% 491) (.leaf 511) (.leaf 512))) (.branch (certNat% 492) (.leaf 513) (.branch (certNat% 493) (.leaf 514) (.leaf 515)))))
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
 (.leaf (.branch (certNat% 494) (.leaf 516) (.branch (certNat% 495) (.leaf 517) (.leaf 518))))
 (.leaf (.branch (certNat% 496) (.branch (certNat% 497) (.branch (certNat% 498) (.leaf 519) (.branch (certNat% 499) (.leaf 520) (.leaf 521))) (.branch (certNat% 500) (.leaf 522) (.branch (certNat% 501) (.leaf 523) (.leaf 524)))) (.branch (certNat% 502) (.branch (certNat% 503) (.leaf 525) (.branch (certNat% 504) (.leaf 526) (.leaf 527))) (.branch (certNat% 505) (.leaf 528) (.branch (certNat% 506) (.leaf 529) (.leaf 530)))))))
 (.branch 963
 (.leaf (.branch (certNat% 507) (.branch (certNat% 508) (.branch (certNat% 509) (.leaf 531) (.branch (certNat% 510) (.leaf 532) (.leaf 533))) (.branch (certNat% 511) (.leaf 534) (.branch (certNat% 512) (.leaf 535) (.leaf 536)))) (.branch (certNat% 513) (.branch (certNat% 514) (.leaf 537) (.branch (certNat% 515) (.leaf 538) (.leaf 539))) (.branch (certNat% 516) (.leaf 540) (.branch (certNat% 517) (.leaf 541) (.leaf 542))))))
 (.leaf (.leaf 0))))
 (.branch 966
 (.branch 965
 (.leaf (.branch (certNat% 518) (.branch (certNat% 519) (.branch (certNat% 520) (.leaf 543) (.branch (certNat% 521) (.leaf 544) (.leaf 545))) (.branch (certNat% 522) (.leaf 546) (.branch (certNat% 523) (.leaf 547) (.leaf 548)))) (.branch (certNat% 524) (.branch (certNat% 525) (.leaf 549) (.branch (certNat% 526) (.leaf 550) (.leaf 551))) (.branch (certNat% 527) (.leaf 552) (.branch (certNat% 528) (.leaf 553) (.leaf 554))))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 972
 (.branch 970
 (.branch 969
 (.leaf (.branch (certNat% 529) (.branch (certNat% 530) (.branch (certNat% 531) (.leaf 555) (.branch (certNat% 532) (.leaf 556) (.leaf 557))) (.branch (certNat% 533) (.leaf 558) (.branch (certNat% 534) (.leaf 559) (.leaf 560)))) (.branch (certNat% 535) (.branch (certNat% 536) (.leaf 561) (.branch (certNat% 537) (.leaf 562) (.leaf 563))) (.branch (certNat% 538) (.leaf 564) (.branch (certNat% 539) (.leaf 565) (.leaf 566))))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 984
 (.branch 980
 (.branch 978
 (.branch 977
 (.leaf (.branch (certNat% 540) (.branch (certNat% 541) (.branch (certNat% 542) (.leaf 567) (.branch (certNat% 543) (.leaf 568) (.leaf 569))) (.branch (certNat% 544) (.leaf 570) (.branch (certNat% 545) (.leaf 571) (.leaf 572)))) (.branch (certNat% 546) (.branch (certNat% 547) (.leaf 573) (.branch (certNat% 548) (.leaf 574) (.leaf 575))) (.branch (certNat% 549) (.leaf 576) (.branch (certNat% 550) (.leaf 577) (.leaf 578))))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 1008
 (.branch 1000
 (.branch 996
 (.branch 994
 (.branch 993
 (.leaf (.branch (certNat% 551) (.branch (certNat% 552) (.branch (certNat% 553) (.leaf 579) (.branch (certNat% 554) (.leaf 580) (.leaf 581))) (.branch (certNat% 555) (.leaf 582) (.branch (certNat% 556) (.leaf 583) (.leaf 584)))) (.branch (certNat% 557) (.branch (certNat% 558) (.leaf 585) (.branch (certNat% 559) (.leaf 586) (.leaf 587))) (.branch (certNat% 560) (.leaf 588) (.branch (certNat% 561) (.leaf 589) (.leaf 590))))))
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
def candidateMasks (i : Nat) := PackedRawNatGrowth.take 2170
  (PackedRawNatGrowth.drop (2170*(i%64)) (candidateMasksBlocks.get (i/64)))

def badMasksBlocks : Table Nat :=
(.branch 17
 (.branch 8
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
 (.leaf badMasksBlock0007))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf badMasksBlock0008)
 (.leaf badMasksBlock0009))
 (.branch 11
 (.leaf badMasksBlock0010)
 (.leaf badMasksBlock0011)))
 (.branch 14
 (.branch 13
 (.leaf badMasksBlock0012)
 (.leaf badMasksBlock0013))
 (.branch 15
 (.leaf badMasksBlock0014)
 (.branch 16
 (.leaf badMasksBlock0015)
 (.leaf badMasksBlock0016))))))
 (.branch 25
 (.branch 21
 (.branch 19
 (.branch 18
 (.leaf badMasksBlock0017)
 (.leaf badMasksBlock0018))
 (.branch 20
 (.leaf badMasksBlock0019)
 (.leaf badMasksBlock0020)))
 (.branch 23
 (.branch 22
 (.leaf badMasksBlock0021)
 (.leaf badMasksBlock0022))
 (.branch 24
 (.leaf badMasksBlock0023)
 (.leaf badMasksBlock0024))))
 (.branch 29
 (.branch 27
 (.branch 26
 (.leaf badMasksBlock0025)
 (.leaf badMasksBlock0026))
 (.branch 28
 (.leaf badMasksBlock0027)
 (.leaf badMasksBlock0028)))
 (.branch 31
 (.branch 30
 (.leaf badMasksBlock0029)
 (.leaf badMasksBlock0030))
 (.branch 32
 (.leaf badMasksBlock0031)
 (.branch 33
 (.leaf badMasksBlock0032)
 (.leaf badMasksBlock0033)))))))
def badMasks (i : Nat) := PackedRawNatGrowth.take 2170
  (PackedRawNatGrowth.drop (2170*(i%64)) (badMasksBlocks.get (i/64)))

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
def signatureMasks (i : Nat) := PackedRawNatGrowth.take 2170
  (PackedRawNatGrowth.drop (2170*(i%64)) (signatureMasksBlocks.get (i/64)))

def fastKind := rawKind
def candidateSupports := candidateRows
def kindSupports := kindRows
def wellFormedTest (i : Nat) : Bool := RawFacetEmbedding.wellFormedCheck (rawCells i)

def cellTest (i : Nat) := (listBounds 1024 (rawCells i).ridgeMasks && ((rawCells i).ridgeMasks.all (fun q => (candidateMasks q).testBit i) && (decide (rawKind i = (rawCells i).kind) && (decide ((rawCells i).vertices < 1024) && ((List.range 10).all (fun v => decide ((vertexMasks v).testBit i = (rawCells i).vertices.testBit v)) && (SignatureCompatibility.faces (rawCells i)).all (fun q => (SignatureCompatibility.profileMask (SignatureCompatibility.allMask 2170) signatureIndex signatureMasks (rawCells i) q).testBit i))))))
def ridgeTest (i : Nat) := decide (candidateMasks i = RawNatGrowthCheck.mask (candidateRows i)) &&
  (candidateRows i).all (fun c => hasNat (rawCells c).ridgeMasks i)
def kindTest (i : Nat) := decide (kindMasks i = RawNatGrowthCheck.mask (kindRows i)) &&
  (kindRows i).all (fun c => decide ((rawCells c).kind = i))
def badTest (i : Nat) := if badMasks i = 0 then true else
  decide (Nat.land (badMasks i) (SignatureCompatibility.cover (SignatureCompatibility.allMask 2170)
    vertexMasks signatureIndex signatureMasks (rawCells i)) = 0)

end Papers.RationalityTen.RootedCaches.RootedSixExtra05

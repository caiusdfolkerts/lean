module
prelude
public meta import CertificateNumbers
public import RootedSixBase04
public import SignatureCompatibility
public import PackedRawNatGrowth
public import FiniteChecks
public import RawFacetEmbedding
public import RootedSixBase04GrowthCachecandidateMasksDataGrouped000
public import RootedSixBase04GrowthCachebadMasksDataGrouped000
public import RootedSixBase04GrowthCachesignatureMasksData000
public import RootedSixBase04GrowthCachesignatureMasksData001

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase04
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def rawCells := Papers.RationalityTen.FacetUniverses.RootedSixBase04.rawCells
def cells (c : Fin 2824) := rawCells c.val
def ridgeList := ConcreteGrowth.ridgeList cells
def literalCompatible (a b : Fin 2824) := ConcreteGrowth.compatible (cells a) (cells b)
def kind (c : Fin 2824) := (cells c).kind
def rawKindCode : Nat := 16329852828703062614138233011094871567115082518584918176922476709317812021542971946640143200785864245743196000559196677987070323997000439725577888862534975824944900006154130822176166725084383367626445040312288264798249055549454036867467264514649483599005321471954696901011863172019047479714518015633374596735327368717750827738226537450099544645732351075741530477961269848437742205853292419058665685520802962614286766017973442014263396090636168508136667503948460145689375239563955555424489320340605425877010868404031334286823536777192936359438362204093103222804381533704673136119517476269829800195248207051791904752817427190250173676613659189117564750865120858731134306409633442841829834671855652182862137201159205245368463695322561428360434773592243026996505985771130247303845442873192178896721596294764491716745732412914524806544791489498461775595714610191705667408804521016731748553451425488661125442928093576313032481715144752670186326860656577401109327097359482206210043968497746684773677096082259083171125979706568857212729707082831517215383843362755211510650073333523847511984994427773179731164827189607754326138420516478656578629227288048724238801225955330362402598934829847510746021705460356042769806939422696825064189568883911832264087073080166014629098258822008881955870828669198620755675235468516546273618307697212481264477201160445300454391560775240328935324740228488807823801264540430475793642771140247074418251469348772541357678412036798858898130570467677563886328666887321710679895149353340851726391684775255943471432856368695821608655680194339234593692116482267726578189793356245311161686191479385262165856082459965533543601299572926830864151383121011977031944719361369329568846523198062318360294965229652842979844583353814341639627982084115052361862484129117993976611108467917804751243257286990024718114461213255107406558482623387869398053899000588173135090322700579728704964009355949608584741667010766446267903319323315298098792163274430290393454789297059838865250747113293564717869038372578385392863036620306310872011010764907775567744877597650366951073688616863526525755562725314849977563921519064696199940602759653229525582544854016835794847632026165441163597644288808335047605702572433645633113228916302146967296794726011249928989576596572105371418750895534743942220910157344188386291596974049351455998542274155945609005832535005566687418796484327366060925473554171387169696851170635076491209758304198015877204778114115570913968959060582527721315905504040956168114402768233817369791801635315869573464417436395583944995194132610150945831640948322730000521274081989621692761471065621041211388257581512118819584619491588745021835030533883351463981143718358737182545490512372446052173602834085330305183607987703071260640681970494254293205012083614944485439979426777665712212959972401692245991497892997317471831391115609135911618307735101032269002574744961456196104052417344198918015794064147583823848977874521438367811828933201866577155201313356091607396805002905463170448268075572381803049375571427082514256735971598468515361820681149016526461569388378905159594548304210871660201488187893510084752373211571748813560764193121833489131338734622855518603804753457140354616705508817624498144469535619691988392889964886081581956096929597037858068321454783629261450937677817642622620610377975770799809820452242478897896777499246612962374424265784968289847631128898405119947754801883844880
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
 (.branch 10
 (.leaf 0x0)
 (.branch 11
 (.leaf 0x0)
 (.leaf (certNat% 1))))
 (.leaf 0x0)))
 (.branch 24
 (.branch 20
 (.leaf 0x0)
 (.branch 22
 (.branch 21
 (.leaf 0x0)
 (.leaf (certNat% 2)))
 (.leaf 0x0)))
 (.branch 28
 (.branch 26
 (.branch 25
 (.leaf 0x0)
 (.leaf (certNat% 3)))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 48
 (.branch 40
 (.branch 36
 (.leaf 0x0)
 (.branch 38
 (.leaf 0x0)
 (.branch 39
 (.leaf (certNat% 4))
 (.leaf 0x0))))
 (.branch 44
 (.branch 42
 (.leaf 0x0)
 (.branch 43
 (.leaf (certNat% 5))
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 56
 (.branch 52
 (.leaf 0x0)
 (.branch 54
 (.branch 53
 (.leaf (certNat% 6))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 60
 (.branch 58
 (.branch 57
 (.leaf (certNat% 7))
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
 (.leaf (certNat% 8))))
 (.branch 70
 (.branch 69
 (.leaf 0x0)
 (.leaf (certNat% 9)))
 (.branch 71
 (.leaf (certNat% 10))
 (.leaf 0x0))))
 (.branch 76
 (.branch 74
 (.branch 73
 (.leaf 0x0)
 (.leaf (certNat% 11)))
 (.branch 75
 (.leaf (certNat% 12))
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 88
 (.branch 84
 (.branch 82
 (.branch 81
 (.leaf 0x0)
 (.leaf (certNat% 13)))
 (.leaf 0x0))
 (.branch 86
 (.branch 85
 (.leaf (certNat% 14))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 92
 (.branch 90
 (.branch 89
 (.leaf (certNat% 15))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 112
 (.branch 104
 (.branch 100
 (.branch 98
 (.leaf 0x0)
 (.branch 99
 (.leaf (certNat% 16))
 (.leaf 0x0)))
 (.branch 102
 (.branch 101
 (.leaf (certNat% 17))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 108
 (.branch 106
 (.branch 105
 (.leaf (certNat% 18))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 120
 (.branch 116
 (.branch 114
 (.branch 113
 (.leaf (certNat% 19))
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
 (.leaf (certNat% 20))))
 (.branch 134
 (.branch 133
 (.leaf 0x0)
 (.leaf (certNat% 21)))
 (.branch 135
 (.leaf (certNat% 22))
 (.leaf 0x0))))
 (.branch 140
 (.branch 138
 (.branch 137
 (.leaf 0x0)
 (.leaf (certNat% 23)))
 (.branch 139
 (.leaf (certNat% 24))
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 152
 (.branch 148
 (.branch 146
 (.branch 145
 (.leaf 0x0)
 (.leaf (certNat% 25)))
 (.leaf 0x0))
 (.branch 150
 (.branch 149
 (.leaf (certNat% 26))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 156
 (.branch 154
 (.branch 153
 (.leaf (certNat% 27))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 176
 (.branch 168
 (.branch 164
 (.branch 162
 (.leaf 0x0)
 (.branch 163
 (.leaf (certNat% 28))
 (.leaf 0x0)))
 (.branch 166
 (.branch 165
 (.leaf (certNat% 29))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 172
 (.branch 170
 (.branch 169
 (.leaf (certNat% 30))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 184
 (.branch 180
 (.branch 178
 (.branch 177
 (.leaf (certNat% 31))
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
 (.leaf (certNat% 32)))
 (.branch 195
 (.leaf (certNat% 33))
 (.leaf (certNat% 34))))
 (.branch 198
 (.branch 197
 (.leaf (certNat% 35))
 (.leaf (certNat% 36)))
 (.branch 199
 (.leaf (certNat% 37))
 (.leaf 0x0))))
 (.branch 204
 (.branch 202
 (.branch 201
 (.leaf (certNat% 38))
 (.leaf (certNat% 39)))
 (.branch 203
 (.leaf (certNat% 40))
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 216
 (.branch 212
 (.branch 210
 (.branch 209
 (.leaf (certNat% 41))
 (.leaf (certNat% 42)))
 (.leaf 0x0))
 (.branch 214
 (.branch 213
 (.leaf (certNat% 43))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 220
 (.branch 218
 (.branch 217
 (.leaf (certNat% 44))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 240
 (.branch 232
 (.branch 228
 (.branch 226
 (.branch 225
 (.leaf (certNat% 45))
 (.leaf 0x0))
 (.branch 227
 (.leaf (certNat% 46))
 (.leaf 0x0)))
 (.branch 230
 (.branch 229
 (.leaf (certNat% 47))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 236
 (.branch 234
 (.branch 233
 (.leaf (certNat% 48))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 248
 (.branch 244
 (.branch 242
 (.branch 241
 (.leaf (certNat% 49))
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
 (.leaf (certNat% 50))))
 (.branch 262
 (.branch 261
 (.leaf 0x0)
 (.leaf (certNat% 51)))
 (.branch 263
 (.leaf (certNat% 52))
 (.leaf 0x0))))
 (.branch 268
 (.branch 266
 (.branch 265
 (.leaf 0x0)
 (.leaf (certNat% 53)))
 (.branch 267
 (.leaf (certNat% 54))
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 280
 (.branch 276
 (.branch 274
 (.branch 273
 (.leaf 0x0)
 (.leaf (certNat% 55)))
 (.leaf 0x0))
 (.branch 278
 (.branch 277
 (.leaf (certNat% 56))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 284
 (.branch 282
 (.branch 281
 (.leaf (certNat% 57))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 304
 (.branch 296
 (.branch 292
 (.branch 290
 (.leaf 0x0)
 (.branch 291
 (.leaf (certNat% 58))
 (.leaf 0x0)))
 (.branch 294
 (.branch 293
 (.leaf (certNat% 59))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 300
 (.branch 298
 (.branch 297
 (.leaf (certNat% 60))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 312
 (.branch 308
 (.branch 306
 (.branch 305
 (.leaf (certNat% 61))
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
 (.leaf (certNat% 62)))
 (.branch 323
 (.leaf (certNat% 63))
 (.leaf (certNat% 64))))
 (.branch 326
 (.branch 325
 (.leaf (certNat% 65))
 (.leaf (certNat% 66)))
 (.branch 327
 (.leaf (certNat% 67))
 (.leaf 0x0))))
 (.branch 332
 (.branch 330
 (.branch 329
 (.leaf (certNat% 68))
 (.leaf (certNat% 69)))
 (.branch 331
 (.leaf (certNat% 70))
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 344
 (.branch 340
 (.branch 338
 (.branch 337
 (.leaf (certNat% 71))
 (.leaf (certNat% 72)))
 (.leaf 0x0))
 (.branch 342
 (.branch 341
 (.leaf (certNat% 73))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 348
 (.branch 346
 (.branch 345
 (.leaf (certNat% 74))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 368
 (.branch 360
 (.branch 356
 (.branch 354
 (.branch 353
 (.leaf (certNat% 75))
 (.leaf 0x0))
 (.branch 355
 (.leaf (certNat% 76))
 (.leaf 0x0)))
 (.branch 358
 (.branch 357
 (.leaf (certNat% 77))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 364
 (.branch 362
 (.branch 361
 (.leaf (certNat% 78))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 376
 (.branch 372
 (.branch 370
 (.branch 369
 (.leaf (certNat% 79))
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
 (.leaf (certNat% 80)))
 (.branch 387
 (.leaf (certNat% 81))
 (.leaf (certNat% 82))))
 (.branch 390
 (.branch 389
 (.leaf (certNat% 83))
 (.leaf (certNat% 84)))
 (.branch 391
 (.leaf (certNat% 85))
 (.leaf 0x0))))
 (.branch 396
 (.branch 394
 (.branch 393
 (.leaf (certNat% 86))
 (.leaf (certNat% 87)))
 (.branch 395
 (.leaf (certNat% 88))
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 408
 (.branch 404
 (.branch 402
 (.branch 401
 (.leaf (certNat% 89))
 (.leaf (certNat% 90)))
 (.leaf 0x0))
 (.branch 406
 (.branch 405
 (.leaf (certNat% 91))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 412
 (.branch 410
 (.branch 409
 (.leaf (certNat% 92))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 432
 (.branch 424
 (.branch 420
 (.branch 418
 (.branch 417
 (.leaf (certNat% 93))
 (.leaf 0x0))
 (.branch 419
 (.leaf (certNat% 94))
 (.leaf 0x0)))
 (.branch 422
 (.branch 421
 (.leaf (certNat% 95))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 428
 (.branch 426
 (.branch 425
 (.leaf (certNat% 96))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 440
 (.branch 436
 (.branch 434
 (.branch 433
 (.leaf (certNat% 97))
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
 (.leaf (certNat% 98))
 (.leaf (certNat% 99)))
 (.branch 451
 (.leaf (certNat% 100))
 (.leaf 0x0)))
 (.branch 454
 (.branch 453
 (.leaf (certNat% 101))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 460
 (.branch 458
 (.branch 457
 (.leaf (certNat% 102))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 472
 (.branch 468
 (.branch 466
 (.branch 465
 (.leaf (certNat% 103))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 496
 (.branch 488
 (.branch 484
 (.branch 482
 (.branch 481
 (.leaf (certNat% 104))
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
 (.leaf (certNat% 105))))
 (.branch 518
 (.branch 517
 (.leaf 0x0)
 (.leaf (certNat% 106)))
 (.branch 519
 (.leaf (certNat% 107))
 (.leaf 0x0))))
 (.branch 524
 (.branch 522
 (.branch 521
 (.leaf 0x0)
 (.leaf (certNat% 108)))
 (.branch 523
 (.leaf (certNat% 109))
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 536
 (.branch 532
 (.branch 530
 (.branch 529
 (.leaf 0x0)
 (.leaf (certNat% 110)))
 (.leaf 0x0))
 (.branch 534
 (.branch 533
 (.leaf (certNat% 111))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 540
 (.branch 538
 (.branch 537
 (.leaf (certNat% 112))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 560
 (.branch 552
 (.branch 548
 (.branch 546
 (.leaf 0x0)
 (.branch 547
 (.leaf (certNat% 113))
 (.leaf 0x0)))
 (.branch 550
 (.branch 549
 (.leaf (certNat% 114))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 556
 (.branch 554
 (.branch 553
 (.leaf (certNat% 115))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 568
 (.branch 564
 (.branch 562
 (.branch 561
 (.leaf (certNat% 116))
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
 (.leaf (certNat% 117)))
 (.branch 579
 (.leaf (certNat% 118))
 (.leaf (certNat% 119))))
 (.branch 582
 (.branch 581
 (.leaf (certNat% 120))
 (.leaf (certNat% 121)))
 (.branch 583
 (.leaf (certNat% 122))
 (.leaf 0x0))))
 (.branch 588
 (.branch 586
 (.branch 585
 (.leaf (certNat% 123))
 (.leaf (certNat% 124)))
 (.branch 587
 (.leaf (certNat% 125))
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 600
 (.branch 596
 (.branch 594
 (.branch 593
 (.leaf (certNat% 126))
 (.leaf (certNat% 127)))
 (.leaf 0x0))
 (.branch 598
 (.branch 597
 (.leaf (certNat% 128))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 604
 (.branch 602
 (.branch 601
 (.leaf (certNat% 129))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 624
 (.branch 616
 (.branch 612
 (.branch 610
 (.branch 609
 (.leaf (certNat% 130))
 (.leaf 0x0))
 (.branch 611
 (.leaf (certNat% 131))
 (.leaf 0x0)))
 (.branch 614
 (.branch 613
 (.leaf (certNat% 132))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 620
 (.branch 618
 (.branch 617
 (.leaf (certNat% 133))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 632
 (.branch 628
 (.branch 626
 (.branch 625
 (.leaf (certNat% 134))
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
 (.leaf (certNat% 135)))
 (.branch 643
 (.leaf (certNat% 136))
 (.leaf (certNat% 137))))
 (.branch 646
 (.branch 645
 (.leaf (certNat% 138))
 (.leaf (certNat% 139)))
 (.branch 647
 (.leaf (certNat% 140))
 (.leaf 0x0))))
 (.branch 652
 (.branch 650
 (.branch 649
 (.leaf (certNat% 141))
 (.leaf (certNat% 142)))
 (.branch 651
 (.leaf (certNat% 143))
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 664
 (.branch 660
 (.branch 658
 (.branch 657
 (.leaf (certNat% 144))
 (.leaf (certNat% 145)))
 (.leaf 0x0))
 (.branch 662
 (.branch 661
 (.leaf (certNat% 146))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 668
 (.branch 666
 (.branch 665
 (.leaf (certNat% 147))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 688
 (.branch 680
 (.branch 676
 (.branch 674
 (.branch 673
 (.leaf (certNat% 148))
 (.leaf 0x0))
 (.branch 675
 (.leaf (certNat% 149))
 (.leaf 0x0)))
 (.branch 678
 (.branch 677
 (.leaf (certNat% 150))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 684
 (.branch 682
 (.branch 681
 (.leaf (certNat% 151))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 696
 (.branch 692
 (.branch 690
 (.branch 689
 (.leaf (certNat% 152))
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
 (.leaf (certNat% 153))
 (.leaf (certNat% 154)))
 (.branch 707
 (.leaf (certNat% 155))
 (.leaf 0x0)))
 (.branch 710
 (.branch 709
 (.leaf (certNat% 156))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 716
 (.branch 714
 (.branch 713
 (.leaf (certNat% 157))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 728
 (.branch 724
 (.branch 722
 (.branch 721
 (.leaf (certNat% 158))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 752
 (.branch 744
 (.branch 740
 (.branch 738
 (.branch 737
 (.leaf (certNat% 159))
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
 (.leaf (certNat% 167)))
 (.branch 779
 (.leaf (certNat% 168))
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 792
 (.branch 788
 (.branch 786
 (.branch 785
 (.leaf (certNat% 169))
 (.leaf (certNat% 170)))
 (.leaf 0x0))
 (.branch 790
 (.branch 789
 (.leaf (certNat% 171))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 796
 (.branch 794
 (.branch 793
 (.leaf (certNat% 172))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 816
 (.branch 808
 (.branch 804
 (.branch 802
 (.branch 801
 (.leaf (certNat% 173))
 (.leaf 0x0))
 (.branch 803
 (.leaf (certNat% 174))
 (.leaf 0x0)))
 (.branch 806
 (.branch 805
 (.leaf (certNat% 175))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 812
 (.branch 810
 (.branch 809
 (.leaf (certNat% 176))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 824
 (.branch 820
 (.branch 818
 (.branch 817
 (.leaf (certNat% 177))
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
 (.leaf (certNat% 178))
 (.leaf (certNat% 179)))
 (.branch 835
 (.leaf (certNat% 180))
 (.leaf 0x0)))
 (.branch 838
 (.branch 837
 (.leaf (certNat% 181))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 844
 (.branch 842
 (.branch 841
 (.leaf (certNat% 182))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 856
 (.branch 852
 (.branch 850
 (.branch 849
 (.leaf (certNat% 183))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 880
 (.branch 872
 (.branch 868
 (.branch 866
 (.branch 865
 (.leaf (certNat% 184))
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
 (.leaf (certNat% 185))
 (.leaf (certNat% 186)))
 (.branch 899
 (.leaf (certNat% 187))
 (.leaf 0x0)))
 (.branch 902
 (.branch 901
 (.leaf (certNat% 188))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 908
 (.branch 906
 (.branch 905
 (.leaf (certNat% 189))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 920
 (.branch 916
 (.branch 914
 (.branch 913
 (.leaf (certNat% 190))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 944
 (.branch 936
 (.branch 932
 (.branch 930
 (.branch 929
 (.leaf (certNat% 191))
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
 (.leaf (certNat% 192))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))))))
def kindRowTable : Table Nat :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf 0x1)
 (.leaf (certNat% 193)))
 (.branch 3
 (.leaf (certNat% 194))
 (.branch 4
 (.leaf (certNat% 195))
 (.leaf 0x0))))
 (.branch 8
 (.leaf 0x0)
 (.branch 9
 (.leaf (certNat% 196))
 (.branch 10
 (.leaf (certNat% 197))
 (.leaf 0x0)))))
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
 (.leaf (certNat% 198)))
 (.branch 3
 (.leaf (certNat% 199))
 (.branch 4
 (.leaf (certNat% 200))
 (.leaf 0x0))))
 (.branch 8
 (.leaf 0x0)
 (.branch 9
 (.leaf (certNat% 201))
 (.branch 10
 (.leaf (certNat% 202))
 (.leaf 0x0)))))
def kindMasks := kindMaskTable.get
def keys := List.range 11
def vertexMaskTable : Table Nat :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf 7269570787327655691899729042895991422148537771129148661447315774312689293940672384543882233157815820761291836630351942347751672555148988487039834764240212916972514552383101132087777487138576962346695096469140456715161320639221035738751761480937930847516258401461321882486542455688549049011391248297297567561739737296699164283222607812145040227004894324584093593301360425760081776668496796024566010951126409708941151142273730752232683737041279321523622316948359751565921213198422498628737981596259385962108210255669095138371979296604432117667244808190226337059526419426287591146552694556522062020494298405756436347753798776596032109677354568335049236797110134394912643555662384258913854637489240263164546211621354189632640400457569359041655449933573193469094708433024955906523135)
 (.leaf 664030600523266864793675102270867211351232814165457762260366063662319788300687069194223133372248602474343270493390333238561612939665162354908934468301693231233021118528860059225771718245373663079988746691901745623402975634932558799740923754597007290364877960765979062291719996846391436740094061764954157640517464363140491803539432686466692518876823137061768805532314098734108471582639329351922044043478288054192630175646621741442688315093352158098814418966079793128161070563467214055869170983134962520679457299035009338150502372611710361788701142711150881871970357331391966119158987187578706026294145927572596657870393345642030882064617586914701826779597588911479467749340504714760847772526896938925443792024552220203893819335492622732580253803634340116802331389587009095861377690194554667295420366897007584790959550453809151))
 (.branch 3
 (.leaf 765575159060272981986266462615257776217195341952698666173201124861326759457722652437754972106971394145111198918491015567147126883640231341428746078264561788838430251169098966464453451744925270244585590152898184550668048966424972840954582275472246448081988023535192193301033712196432157996495860616676015802181862920167150021450435071088855838966051070667916833885642760651232982372692785576261339733421721630426301774463053808128404841175096974718269425077083951929138478158885575962711523649737824474581314682058588902159023246804222123699095762737053783640866564147063744480051713634515324830409226689218427062117343249834920766163229059299315504984881720699365210060811380779082745874514919018886777972790588287758374759294942530343991446418600610819366639529062705206002207513445837138986255524668528718375486240848290222223927175244906527)
 (.branch 4
 (.leaf 12844219807788556837747702140882744700189918513464753641751472617957573739596039564153113827360309463890450254984205367671291000496964651803788136545382961242057338168416595132323863246977282218666813709599673307552030301717771732337005119766213031096577390225632212314415227389030924860204844284559000308626620758793951475709867115041404690499681066729688508597522534421975985447367635428214624225183839614281249846854598026723640091636776558792714655146140513815952455210129972693718724113385279204450443357293935579157108310985534820875028462304337909483584915556946160818531553329516526814328491153760937520291307502831573112536362639955418201027502995198266924573383153590434077406912190141244221135308762432324254686849105398355341808135514023207585851993572602558738532970234318662296592255638219267157338192452629329231617890514472094067065313)
 (.leaf 12844220573363761529858807319336489596168315048814473881426721434514164695371129739682341921119229959742643765191176935567120343789787401191451870438601773050014345313754280739483831678270611855576659171128990302105713514146456220548936919830087909375175469450074016810933106177426586559373701610215371307455237394561360843212829380700349911513406437081128993535091428393434493995600801263733265169002311119258507562952516300845695479494230296418622499268590813428765822194255031912291412559782016969133515518351256516675991914239315066980944162184461883896916985016149640455224544598579485858700371497544919708181663302025368519033735099335546123879649695139213882506300811856418337830925128923878620229923929444741076631520753364539769931728445708332588735536580559331198712457745933315800148672679393474129979743409241520296778751445992358239764481))))
 (.branch 7
 (.branch 6
 (.leaf 12844220573363761529858807983367129698745602555910593038528602085847946446932743354829915914842903256401216862690732637563176863943527781190706950790587488760456174763891569547320383880658651542381415596908925097893147586356147176352651790436510051472797971502267206069803205460782597083916220243087230246273121318248716892496831459734349332070378498338870449985275726043532616115259576065234649458241937837466044097664287957383336520190476367743811457985182305790472741813539073609286685636448958326213874459307161433650822689080769047339279100929809137075360022269556099797883921201197218371038177361709068899103005212250398300335296628265480514381210125576272036267197023641878852356869107443944738887658186833371608359085307487116563767326987620422723672249481952304048828750398922978217270237842214673868345261813204062088448085361264780168396801)
 (.leaf 200690192845716655107172753734222216640613781057995269480195055323405656083527374333375602577279853794298480247212455216347711263810697033481263116541578233909444951722729509332649613397326800532266594318247585111209981196296678810247852099416045702601790471387138787029461936206881767128281430331585268619954777244691600255856019054781156814042504470071697862560518474111165931684976946270905280431047777469425332763253097308063835809018252249432092747153983004227330246384583898724681122381739718538928431474980665902805891795724755314005582621686469485861296160130951303894257648341116897685255992131083592421421590859519596149988206563971805117986819734424401423905456113008245990122659381562184297654104199772251139352126384676210318294389271733790214851774607787436207115501554124818750118892451911143062348203264259754466575944552788654591522))
 (.branch 8
 (.leaf 12646665411168167078690813682904115519337712106303521198387220725996000504231708525440213027351770544972120100893109298069425787751549152134459478520134782321929650304544796176347713287193630890998155946101027199630243689745528330799733550403221128625804334409968581740490339745854273820511702514311084154271511292261324787522149800743121149501755550252662621372580332886437951848583625546407876042566699339678696918254582920379984498643597588471384117652495027809474198902419925736315139188647532984588686429034917196318989550303175550511510781461020725615371198601135106613508975929586096622961011656912690503994125583564025938616233362514721017154455718618353387271431134284106434679369341503722976786601796093805493271719885707418555082994308538500752986082633645811528541349652268216856577165631994160136434285164717028485551943976023255222399556)
 (.branch 9
 (.leaf 12841133773954455366559308072422395102192354267635482541026393002100259798734023855926257362113871962021773563715701436239005132696670065495412263135815926135804966013182640968019823657096698142411685467222633131107103591441610075362069264439218083046479374159008916786638165961630014321345818468748263824341526661205947989784531860281457917115691988684099568333949897982748314526354256110540584608367880767953408411346767767646987058880129628110595244701868896046267413460625143889008939592721033866521278278540643544717572322178899999099659746808935645552759793434431658977606490751833233009415843807653321159229689153215221143479569521816798653217152147942767657890541745714399066783112241668271845451864791262273541170391210905157168255282158025542240538362102200184824801766249354384055089182110540398837248096087239964806543740779711764276335752)
 (.leaf 12844172342122991121057253297258618220674458051406294437005130068914388850210622532965101804844529796663174399072304438397904809961437579766677150395435944007896767821130107292889700381626433568215021865990158223786429527405611352620855759971030535459302421655087672021734225746251510266671351530536344756686370642624259972215963843596530653215711776188984010168396776146363252347733839393611748440095113787038077258312790712231712373136912756038100057108481031521710927660187881369802583882148739396785113508469074156376548103013347421178002062747363179290923095812854828968400289089406447339827648517782508888839610821961119420380839669023875856917593018677831317218983705126721054761376943757264243422259228704427403520701765549090948746604696403856121924226700623233100656428658417877522904831809352604189028917543068363194291339809848192271673616)))))
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
 (.branch 56
 (.branch 52
 (.branch 50
 (.branch 49
 (.leaf (.leaf 17))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 54
 (.branch 53
 (.leaf (.leaf 18))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 60
 (.branch 58
 (.branch 57
 (.leaf (.leaf 19))
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
 (.leaf (.leaf 20)))
 (.branch 67
 (.leaf (.leaf 21))
 (.leaf (.leaf 22))))
 (.branch 70
 (.branch 69
 (.leaf (.leaf 23))
 (.leaf (.leaf 24)))
 (.branch 71
 (.leaf (.leaf 25))
 (.leaf (.leaf 0)))))
 (.branch 76
 (.branch 74
 (.branch 73
 (.leaf (.leaf 26))
 (.leaf (.leaf 27)))
 (.branch 75
 (.leaf (.leaf 28))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0))))
 (.branch 88
 (.branch 84
 (.branch 82
 (.branch 81
 (.leaf (.leaf 29))
 (.leaf (.leaf 30)))
 (.leaf (.leaf 0)))
 (.branch 86
 (.branch 85
 (.leaf (.leaf 31))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 92
 (.branch 90
 (.branch 89
 (.leaf (.leaf 32))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 112
 (.branch 104
 (.branch 100
 (.branch 98
 (.branch 97
 (.leaf (.leaf 33))
 (.leaf (.leaf 0)))
 (.branch 99
 (.leaf (.leaf 34))
 (.leaf (.leaf 0))))
 (.branch 102
 (.branch 101
 (.leaf (.leaf 35))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 108
 (.branch 106
 (.branch 105
 (.leaf (.leaf 36))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 120
 (.branch 116
 (.branch 114
 (.branch 113
 (.leaf (.leaf 37))
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
 (.leaf (.leaf 38)))
 (.branch 131
 (.leaf (.leaf 39))
 (.leaf (.leaf 40))))
 (.branch 134
 (.branch 133
 (.leaf (.leaf 41))
 (.leaf (.leaf 42)))
 (.branch 135
 (.leaf (.leaf 43))
 (.leaf (.leaf 0)))))
 (.branch 140
 (.branch 138
 (.branch 137
 (.leaf (.leaf 44))
 (.leaf (.leaf 45)))
 (.branch 139
 (.leaf (.leaf 46))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0))))
 (.branch 152
 (.branch 148
 (.branch 146
 (.branch 145
 (.leaf (.leaf 47))
 (.leaf (.leaf 48)))
 (.leaf (.leaf 0)))
 (.branch 150
 (.branch 149
 (.leaf (.leaf 49))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 156
 (.branch 154
 (.branch 153
 (.leaf (.leaf 50))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 176
 (.branch 168
 (.branch 164
 (.branch 162
 (.branch 161
 (.leaf (.leaf 51))
 (.leaf (.leaf 0)))
 (.branch 163
 (.leaf (.leaf 52))
 (.leaf (.leaf 0))))
 (.branch 166
 (.branch 165
 (.leaf (.leaf 53))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 172
 (.branch 170
 (.branch 169
 (.leaf (.leaf 54))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 184
 (.branch 180
 (.branch 178
 (.branch 177
 (.leaf (.leaf 55))
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
 (.leaf (.leaf 56))
 (.leaf (.leaf 57)))
 (.branch 195
 (.leaf (.leaf 58))
 (.leaf (.branch (certNat% 203) (.leaf 59) (.leaf 60)))))
 (.branch 198
 (.branch 197
 (.leaf (.leaf 61))
 (.leaf (.branch (certNat% 204) (.leaf 62) (.leaf 63))))
 (.branch 199
 (.leaf (.branch (certNat% 205) (.leaf 64) (.leaf 65)))
 (.leaf (.leaf 0)))))
 (.branch 204
 (.branch 202
 (.branch 201
 (.leaf (.leaf 66))
 (.leaf (.branch (certNat% 206) (.leaf 67) (.leaf 68))))
 (.branch 203
 (.leaf (.branch (certNat% 207) (.leaf 69) (.leaf 70)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0))))
 (.branch 216
 (.branch 212
 (.branch 210
 (.branch 209
 (.leaf (.leaf 71))
 (.leaf (.branch (certNat% 208) (.leaf 72) (.leaf 73))))
 (.leaf (.leaf 0)))
 (.branch 214
 (.branch 213
 (.leaf (.branch (certNat% 209) (.leaf 74) (.leaf 75)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 220
 (.branch 218
 (.branch 217
 (.leaf (.branch (certNat% 210) (.leaf 76) (.leaf 77)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 240
 (.branch 232
 (.branch 228
 (.branch 226
 (.branch 225
 (.leaf (.leaf 78))
 (.leaf (.leaf 0)))
 (.branch 227
 (.leaf (.branch (certNat% 211) (.leaf 79) (.leaf 80)))
 (.leaf (.leaf 0))))
 (.branch 230
 (.branch 229
 (.leaf (.branch (certNat% 212) (.leaf 81) (.leaf 82)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 236
 (.branch 234
 (.branch 233
 (.leaf (.branch (certNat% 213) (.leaf 83) (.leaf 84)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 248
 (.branch 244
 (.branch 242
 (.branch 241
 (.leaf (.branch (certNat% 214) (.leaf 85) (.leaf 86)))
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
 (.leaf (.leaf 87)))
 (.branch 259
 (.leaf (.leaf 88))
 (.leaf (.leaf 89))))
 (.branch 262
 (.branch 261
 (.leaf (.leaf 90))
 (.leaf (.leaf 91)))
 (.branch 263
 (.leaf (.leaf 92))
 (.leaf (.leaf 0)))))
 (.branch 268
 (.branch 266
 (.branch 265
 (.leaf (.leaf 93))
 (.leaf (.leaf 94)))
 (.branch 267
 (.leaf (.leaf 95))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0))))
 (.branch 280
 (.branch 276
 (.branch 274
 (.branch 273
 (.leaf (.leaf 96))
 (.leaf (.leaf 97)))
 (.leaf (.leaf 0)))
 (.branch 278
 (.branch 277
 (.leaf (.leaf 98))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 284
 (.branch 282
 (.branch 281
 (.leaf (.leaf 99))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 304
 (.branch 296
 (.branch 292
 (.branch 290
 (.branch 289
 (.leaf (.leaf 100))
 (.leaf (.leaf 0)))
 (.branch 291
 (.leaf (.leaf 101))
 (.leaf (.leaf 0))))
 (.branch 294
 (.branch 293
 (.leaf (.leaf 102))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 300
 (.branch 298
 (.branch 297
 (.leaf (.leaf 103))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 312
 (.branch 308
 (.branch 306
 (.branch 305
 (.leaf (.leaf 104))
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
 (.leaf (.leaf 105))
 (.leaf (.leaf 106)))
 (.branch 323
 (.leaf (.leaf 107))
 (.leaf (.branch (certNat% 215) (.leaf 108) (.leaf 109)))))
 (.branch 326
 (.branch 325
 (.leaf (.leaf 110))
 (.leaf (.branch (certNat% 216) (.leaf 111) (.leaf 112))))
 (.branch 327
 (.leaf (.branch (certNat% 217) (.leaf 113) (.leaf 114)))
 (.leaf (.leaf 0)))))
 (.branch 332
 (.branch 330
 (.branch 329
 (.leaf (.leaf 115))
 (.leaf (.branch (certNat% 218) (.leaf 116) (.leaf 117))))
 (.branch 331
 (.leaf (.branch (certNat% 219) (.leaf 118) (.leaf 119)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0))))
 (.branch 344
 (.branch 340
 (.branch 338
 (.branch 337
 (.leaf (.leaf 120))
 (.leaf (.branch (certNat% 220) (.leaf 121) (.leaf 122))))
 (.leaf (.leaf 0)))
 (.branch 342
 (.branch 341
 (.leaf (.branch (certNat% 221) (.leaf 123) (.leaf 124)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 348
 (.branch 346
 (.branch 345
 (.leaf (.branch (certNat% 222) (.leaf 125) (.leaf 126)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 368
 (.branch 360
 (.branch 356
 (.branch 354
 (.branch 353
 (.leaf (.leaf 127))
 (.leaf (.leaf 0)))
 (.branch 355
 (.leaf (.branch (certNat% 223) (.leaf 128) (.leaf 129)))
 (.leaf (.leaf 0))))
 (.branch 358
 (.branch 357
 (.leaf (.branch (certNat% 224) (.leaf 130) (.leaf 131)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 364
 (.branch 362
 (.branch 361
 (.leaf (.branch (certNat% 225) (.leaf 132) (.leaf 133)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 376
 (.branch 372
 (.branch 370
 (.branch 369
 (.leaf (.branch (certNat% 226) (.leaf 134) (.leaf 135)))
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
 (.leaf (.leaf 136))
 (.leaf (.leaf 137)))
 (.branch 387
 (.leaf (.leaf 138))
 (.leaf (.branch (certNat% 227) (.leaf 139) (.leaf 140)))))
 (.branch 390
 (.branch 389
 (.leaf (.leaf 141))
 (.leaf (.branch (certNat% 228) (.leaf 142) (.leaf 143))))
 (.branch 391
 (.leaf (.branch (certNat% 229) (.leaf 144) (.leaf 145)))
 (.leaf (.leaf 0)))))
 (.branch 396
 (.branch 394
 (.branch 393
 (.leaf (.leaf 146))
 (.leaf (.branch (certNat% 230) (.leaf 147) (.leaf 148))))
 (.branch 395
 (.leaf (.branch (certNat% 231) (.leaf 149) (.leaf 150)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0))))
 (.branch 408
 (.branch 404
 (.branch 402
 (.branch 401
 (.leaf (.leaf 151))
 (.leaf (.branch (certNat% 232) (.leaf 152) (.leaf 153))))
 (.leaf (.leaf 0)))
 (.branch 406
 (.branch 405
 (.leaf (.branch (certNat% 233) (.leaf 154) (.leaf 155)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 412
 (.branch 410
 (.branch 409
 (.leaf (.branch (certNat% 234) (.leaf 156) (.leaf 157)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 432
 (.branch 424
 (.branch 420
 (.branch 418
 (.branch 417
 (.leaf (.leaf 158))
 (.leaf (.leaf 0)))
 (.branch 419
 (.leaf (.branch (certNat% 235) (.leaf 159) (.leaf 160)))
 (.leaf (.leaf 0))))
 (.branch 422
 (.branch 421
 (.leaf (.branch (certNat% 236) (.leaf 161) (.leaf 162)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 428
 (.branch 426
 (.branch 425
 (.leaf (.branch (certNat% 237) (.leaf 163) (.leaf 164)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 440
 (.branch 436
 (.branch 434
 (.branch 433
 (.leaf (.branch (certNat% 238) (.leaf 165) (.leaf 166)))
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
 (.leaf (.leaf 167))
 (.leaf (.branch (certNat% 239) (.leaf 168) (.branch (certNat% 240) (.leaf 169) (.leaf 170)))))
 (.branch 451
 (.leaf (.branch (certNat% 241) (.leaf 171) (.branch (certNat% 242) (.leaf 172) (.leaf 173))))
 (.leaf (.leaf 0))))
 (.branch 454
 (.branch 453
 (.leaf (.branch (certNat% 243) (.leaf 174) (.branch (certNat% 244) (.leaf 175) (.leaf 176))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 460
 (.branch 458
 (.branch 457
 (.leaf (.branch (certNat% 245) (.leaf 177) (.branch (certNat% 246) (.leaf 178) (.leaf 179))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 472
 (.branch 468
 (.branch 466
 (.branch 465
 (.leaf (.branch (certNat% 247) (.leaf 180) (.branch (certNat% 248) (.leaf 181) (.leaf 182))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 496
 (.branch 488
 (.branch 484
 (.branch 482
 (.branch 481
 (.leaf (.branch (certNat% 249) (.leaf 183) (.branch (certNat% 250) (.leaf 184) (.leaf 185))))
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
 (.leaf (.leaf 186)))
 (.branch 515
 (.leaf (.leaf 187))
 (.leaf (.leaf 188))))
 (.branch 518
 (.branch 517
 (.leaf (.leaf 189))
 (.leaf (.leaf 190)))
 (.branch 519
 (.leaf (.leaf 191))
 (.leaf (.leaf 0)))))
 (.branch 524
 (.branch 522
 (.branch 521
 (.leaf (.leaf 192))
 (.leaf (.leaf 193)))
 (.branch 523
 (.leaf (.leaf 194))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0))))
 (.branch 536
 (.branch 532
 (.branch 530
 (.branch 529
 (.leaf (.leaf 195))
 (.leaf (.leaf 196)))
 (.leaf (.leaf 0)))
 (.branch 534
 (.branch 533
 (.leaf (.leaf 197))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 540
 (.branch 538
 (.branch 537
 (.leaf (.leaf 198))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 560
 (.branch 552
 (.branch 548
 (.branch 546
 (.branch 545
 (.leaf (.leaf 199))
 (.leaf (.leaf 0)))
 (.branch 547
 (.leaf (.leaf 200))
 (.leaf (.leaf 0))))
 (.branch 550
 (.branch 549
 (.leaf (.leaf 201))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 556
 (.branch 554
 (.branch 553
 (.leaf (.leaf 202))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 568
 (.branch 564
 (.branch 562
 (.branch 561
 (.leaf (.leaf 203))
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
 (.leaf (.leaf 204))
 (.leaf (.leaf 205)))
 (.branch 579
 (.leaf (.leaf 206))
 (.leaf (.branch (certNat% 251) (.leaf 207) (.leaf 208)))))
 (.branch 582
 (.branch 581
 (.leaf (.leaf 209))
 (.leaf (.branch (certNat% 252) (.leaf 210) (.leaf 211))))
 (.branch 583
 (.leaf (.branch (certNat% 253) (.leaf 212) (.leaf 213)))
 (.leaf (.leaf 0)))))
 (.branch 588
 (.branch 586
 (.branch 585
 (.leaf (.leaf 214))
 (.leaf (.branch (certNat% 254) (.leaf 215) (.leaf 216))))
 (.branch 587
 (.leaf (.branch (certNat% 255) (.leaf 217) (.leaf 218)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0))))
 (.branch 600
 (.branch 596
 (.branch 594
 (.branch 593
 (.leaf (.leaf 219))
 (.leaf (.branch (certNat% 256) (.leaf 220) (.leaf 221))))
 (.leaf (.leaf 0)))
 (.branch 598
 (.branch 597
 (.leaf (.branch (certNat% 257) (.leaf 222) (.leaf 223)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 604
 (.branch 602
 (.branch 601
 (.leaf (.branch (certNat% 258) (.leaf 224) (.leaf 225)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 624
 (.branch 616
 (.branch 612
 (.branch 610
 (.branch 609
 (.leaf (.leaf 226))
 (.leaf (.leaf 0)))
 (.branch 611
 (.leaf (.branch (certNat% 259) (.leaf 227) (.leaf 228)))
 (.leaf (.leaf 0))))
 (.branch 614
 (.branch 613
 (.leaf (.branch (certNat% 260) (.leaf 229) (.leaf 230)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 620
 (.branch 618
 (.branch 617
 (.leaf (.branch (certNat% 261) (.leaf 231) (.leaf 232)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 632
 (.branch 628
 (.branch 626
 (.branch 625
 (.leaf (.branch (certNat% 262) (.leaf 233) (.leaf 234)))
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
 (.leaf (.leaf 235))
 (.leaf (.leaf 236)))
 (.branch 643
 (.leaf (.leaf 237))
 (.leaf (.branch (certNat% 263) (.leaf 238) (.leaf 239)))))
 (.branch 646
 (.branch 645
 (.leaf (.leaf 240))
 (.leaf (.branch (certNat% 264) (.leaf 241) (.leaf 242))))
 (.branch 647
 (.leaf (.branch (certNat% 265) (.leaf 243) (.leaf 244)))
 (.leaf (.leaf 0)))))
 (.branch 652
 (.branch 650
 (.branch 649
 (.leaf (.leaf 245))
 (.leaf (.branch (certNat% 266) (.leaf 246) (.leaf 247))))
 (.branch 651
 (.leaf (.branch (certNat% 267) (.leaf 248) (.leaf 249)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0))))
 (.branch 664
 (.branch 660
 (.branch 658
 (.branch 657
 (.leaf (.leaf 250))
 (.leaf (.branch (certNat% 268) (.leaf 251) (.leaf 252))))
 (.leaf (.leaf 0)))
 (.branch 662
 (.branch 661
 (.leaf (.branch (certNat% 269) (.leaf 253) (.leaf 254)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 668
 (.branch 666
 (.branch 665
 (.leaf (.branch (certNat% 270) (.leaf 255) (.leaf 256)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 688
 (.branch 680
 (.branch 676
 (.branch 674
 (.branch 673
 (.leaf (.leaf 257))
 (.leaf (.leaf 0)))
 (.branch 675
 (.leaf (.branch (certNat% 271) (.leaf 258) (.leaf 259)))
 (.leaf (.leaf 0))))
 (.branch 678
 (.branch 677
 (.leaf (.branch (certNat% 272) (.leaf 260) (.leaf 261)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 684
 (.branch 682
 (.branch 681
 (.leaf (.branch (certNat% 273) (.leaf 262) (.leaf 263)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 696
 (.branch 692
 (.branch 690
 (.branch 689
 (.leaf (.branch (certNat% 274) (.leaf 264) (.leaf 265)))
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
 (.leaf (.leaf 266))
 (.leaf (.branch (certNat% 275) (.leaf 267) (.branch (certNat% 276) (.leaf 268) (.leaf 269)))))
 (.branch 707
 (.leaf (.branch (certNat% 277) (.leaf 270) (.branch (certNat% 278) (.leaf 271) (.leaf 272))))
 (.leaf (.leaf 0))))
 (.branch 710
 (.branch 709
 (.leaf (.branch (certNat% 279) (.leaf 273) (.branch (certNat% 280) (.leaf 274) (.leaf 275))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 716
 (.branch 714
 (.branch 713
 (.leaf (.branch (certNat% 281) (.leaf 276) (.branch (certNat% 282) (.leaf 277) (.leaf 278))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 728
 (.branch 724
 (.branch 722
 (.branch 721
 (.leaf (.branch (certNat% 283) (.leaf 279) (.branch (certNat% 284) (.leaf 280) (.leaf 281))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 752
 (.branch 744
 (.branch 740
 (.branch 738
 (.branch 737
 (.leaf (.branch (certNat% 285) (.leaf 282) (.branch (certNat% 286) (.leaf 283) (.leaf 284))))
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
 (.leaf (.leaf 285))
 (.leaf (.leaf 286)))
 (.branch 771
 (.leaf (.leaf 287))
 (.leaf (.branch (certNat% 287) (.leaf 288) (.leaf 289)))))
 (.branch 774
 (.branch 773
 (.leaf (.leaf 290))
 (.leaf (.branch (certNat% 288) (.leaf 291) (.leaf 292))))
 (.branch 775
 (.leaf (.branch (certNat% 289) (.leaf 293) (.leaf 294)))
 (.leaf (.leaf 0)))))
 (.branch 780
 (.branch 778
 (.branch 777
 (.leaf (.leaf 295))
 (.leaf (.branch (certNat% 290) (.leaf 296) (.leaf 297))))
 (.branch 779
 (.leaf (.branch (certNat% 291) (.leaf 298) (.leaf 299)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0))))
 (.branch 792
 (.branch 788
 (.branch 786
 (.branch 785
 (.leaf (.leaf 300))
 (.leaf (.branch (certNat% 292) (.leaf 301) (.leaf 302))))
 (.leaf (.leaf 0)))
 (.branch 790
 (.branch 789
 (.leaf (.branch (certNat% 293) (.leaf 303) (.leaf 304)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 796
 (.branch 794
 (.branch 793
 (.leaf (.branch (certNat% 294) (.leaf 305) (.leaf 306)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 816
 (.branch 808
 (.branch 804
 (.branch 802
 (.branch 801
 (.leaf (.leaf 307))
 (.leaf (.leaf 0)))
 (.branch 803
 (.leaf (.branch (certNat% 295) (.leaf 308) (.leaf 309)))
 (.leaf (.leaf 0))))
 (.branch 806
 (.branch 805
 (.leaf (.branch (certNat% 296) (.leaf 310) (.leaf 311)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 812
 (.branch 810
 (.branch 809
 (.leaf (.branch (certNat% 297) (.leaf 312) (.leaf 313)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 824
 (.branch 820
 (.branch 818
 (.branch 817
 (.leaf (.branch (certNat% 298) (.leaf 314) (.leaf 315)))
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
 (.leaf (.leaf 316))
 (.leaf (.branch (certNat% 299) (.leaf 317) (.branch (certNat% 300) (.leaf 318) (.leaf 319)))))
 (.branch 835
 (.leaf (.branch (certNat% 301) (.leaf 320) (.branch (certNat% 302) (.leaf 321) (.leaf 322))))
 (.leaf (.leaf 0))))
 (.branch 838
 (.branch 837
 (.leaf (.branch (certNat% 303) (.leaf 323) (.branch (certNat% 304) (.leaf 324) (.leaf 325))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 844
 (.branch 842
 (.branch 841
 (.leaf (.branch (certNat% 305) (.leaf 326) (.branch (certNat% 306) (.leaf 327) (.leaf 328))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 856
 (.branch 852
 (.branch 850
 (.branch 849
 (.leaf (.branch (certNat% 307) (.leaf 329) (.branch (certNat% 308) (.leaf 330) (.leaf 331))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 880
 (.branch 872
 (.branch 868
 (.branch 866
 (.branch 865
 (.leaf (.branch (certNat% 309) (.leaf 332) (.branch (certNat% 310) (.leaf 333) (.leaf 334))))
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
 (.leaf (.leaf 335))
 (.leaf (.branch (certNat% 311) (.leaf 336) (.branch (certNat% 312) (.leaf 337) (.leaf 338)))))
 (.branch 899
 (.leaf (.branch (certNat% 313) (.leaf 339) (.branch (certNat% 314) (.leaf 340) (.leaf 341))))
 (.leaf (.leaf 0))))
 (.branch 902
 (.branch 901
 (.leaf (.branch (certNat% 315) (.leaf 342) (.branch (certNat% 316) (.leaf 343) (.leaf 344))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 908
 (.branch 906
 (.branch 905
 (.leaf (.branch (certNat% 317) (.leaf 345) (.branch (certNat% 318) (.leaf 346) (.leaf 347))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 920
 (.branch 916
 (.branch 914
 (.branch 913
 (.leaf (.branch (certNat% 319) (.leaf 348) (.branch (certNat% 320) (.leaf 349) (.leaf 350))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 944
 (.branch 936
 (.branch 932
 (.branch 930
 (.branch 929
 (.leaf (.branch (certNat% 321) (.leaf 351) (.branch (certNat% 322) (.leaf 352) (.leaf 353))))
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
 (.leaf (.branch (certNat% 323) (.leaf 354) (.branch (certNat% 324) (.leaf 355) (.leaf 356))))
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
def candidateMasks (i : Nat) := PackedRawNatGrowth.take 2824
  (PackedRawNatGrowth.drop (2824*(i%64)) (candidateMasksBlocks.get (i/64)))

def badMasksBlocks : Table Nat :=
(.branch 22
 (.branch 11
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
 (.branch 16
 (.branch 13
 (.branch 12
 (.leaf badMasksBlock0011)
 (.leaf badMasksBlock0012))
 (.branch 14
 (.leaf badMasksBlock0013)
 (.branch 15
 (.leaf badMasksBlock0014)
 (.leaf badMasksBlock0015))))
 (.branch 19
 (.branch 17
 (.leaf badMasksBlock0016)
 (.branch 18
 (.leaf badMasksBlock0017)
 (.leaf badMasksBlock0018)))
 (.branch 20
 (.leaf badMasksBlock0019)
 (.branch 21
 (.leaf badMasksBlock0020)
 (.leaf badMasksBlock0021))))))
 (.branch 33
 (.branch 27
 (.branch 24
 (.branch 23
 (.leaf badMasksBlock0022)
 (.leaf badMasksBlock0023))
 (.branch 25
 (.leaf badMasksBlock0024)
 (.branch 26
 (.leaf badMasksBlock0025)
 (.leaf badMasksBlock0026))))
 (.branch 30
 (.branch 28
 (.leaf badMasksBlock0027)
 (.branch 29
 (.leaf badMasksBlock0028)
 (.leaf badMasksBlock0029)))
 (.branch 31
 (.leaf badMasksBlock0030)
 (.branch 32
 (.leaf badMasksBlock0031)
 (.leaf badMasksBlock0032)))))
 (.branch 39
 (.branch 36
 (.branch 34
 (.leaf badMasksBlock0033)
 (.branch 35
 (.leaf badMasksBlock0034)
 (.leaf badMasksBlock0035)))
 (.branch 37
 (.leaf badMasksBlock0036)
 (.branch 38
 (.leaf badMasksBlock0037)
 (.leaf badMasksBlock0038))))
 (.branch 42
 (.branch 40
 (.leaf badMasksBlock0039)
 (.branch 41
 (.leaf badMasksBlock0040)
 (.leaf badMasksBlock0041)))
 (.branch 43
 (.leaf badMasksBlock0042)
 (.branch 44
 (.leaf badMasksBlock0043)
 (.leaf badMasksBlock0044)))))))
def badMasks (i : Nat) := PackedRawNatGrowth.take 2824
  (PackedRawNatGrowth.drop (2824*(i%64)) (badMasksBlocks.get (i/64)))

def signatureMasksBlocks : Table Nat :=
(.branch 3
 (.branch 1
 (.leaf signatureMasksBlock0000)
 (.branch 2
 (.leaf signatureMasksBlock0001)
 (.leaf signatureMasksBlock0002)))
 (.branch 4
 (.leaf signatureMasksBlock0003)
 (.branch 5
 (.leaf signatureMasksBlock0004)
 (.leaf signatureMasksBlock0005))))
def signatureMasks (i : Nat) := PackedRawNatGrowth.take 2824
  (PackedRawNatGrowth.drop (2824*(i%64)) (signatureMasksBlocks.get (i/64)))

def fastKind := rawKind
def candidateSupports := candidateRows
def kindSupports := kindRows
def wellFormedTest (i : Nat) : Bool := RawFacetEmbedding.wellFormedCheck (rawCells i)

def cellTest (i : Nat) := (listBounds 1024 (rawCells i).ridgeMasks && ((rawCells i).ridgeMasks.all (fun q => (candidateMasks q).testBit i) && (decide (rawKind i = (rawCells i).kind) && (decide ((rawCells i).vertices < 1024) && ((List.range 10).all (fun v => decide ((vertexMasks v).testBit i = (rawCells i).vertices.testBit v)) && (SignatureCompatibility.faces (rawCells i)).all (fun q => (SignatureCompatibility.profileMask (SignatureCompatibility.allMask 2824) signatureIndex signatureMasks (rawCells i) q).testBit i))))))
def ridgeTest (i : Nat) := decide (candidateMasks i = RawNatGrowthCheck.mask (candidateRows i)) &&
  (candidateRows i).all (fun c => hasNat (rawCells c).ridgeMasks i)
def kindTest (i : Nat) := decide (kindMasks i = RawNatGrowthCheck.mask (kindRows i)) &&
  (kindRows i).all (fun c => decide ((rawCells c).kind = i))
def badTest (i : Nat) := if badMasks i = 0 then true else
  decide (Nat.land (badMasks i) (SignatureCompatibility.cover (SignatureCompatibility.allMask 2824)
    vertexMasks signatureIndex signatureMasks (rawCells i)) = 0)

end Papers.RationalityTen.RootedCaches.RootedSixBase04

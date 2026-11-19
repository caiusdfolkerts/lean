module
prelude
public meta import CertificateNumbers
public import RootedSixExtra01
public import SignatureCompatibility
public import PackedRawNatGrowth
public import FiniteChecks
public import RawFacetEmbedding
public import RootedSixExtra01GrowthCachecandidateMasksData000
public import RootedSixExtra01GrowthCachecandidateMasksData001
public import RootedSixExtra01GrowthCachecandidateMasksData002
public import RootedSixExtra01GrowthCachecandidateMasksData003
public import RootedSixExtra01GrowthCachecandidateMasksData004
public import RootedSixExtra01GrowthCachecandidateMasksData005
public import RootedSixExtra01GrowthCachebadMasksData000
public import RootedSixExtra01GrowthCachebadMasksData001
public import RootedSixExtra01GrowthCachebadMasksData002
public import RootedSixExtra01GrowthCachebadMasksData003
public import RootedSixExtra01GrowthCachebadMasksData004
public import RootedSixExtra01GrowthCachebadMasksData005
public import RootedSixExtra01GrowthCachebadMasksData006
public import RootedSixExtra01GrowthCachebadMasksData007
public import RootedSixExtra01GrowthCachebadMasksData008
public import RootedSixExtra01GrowthCachebadMasksData009
public import RootedSixExtra01GrowthCachebadMasksData010
public import RootedSixExtra01GrowthCachebadMasksData011
public import RootedSixExtra01GrowthCachebadMasksData012
public import RootedSixExtra01GrowthCachebadMasksData013
public import RootedSixExtra01GrowthCachebadMasksData014
public import RootedSixExtra01GrowthCachebadMasksData015
public import RootedSixExtra01GrowthCachebadMasksData016
public import RootedSixExtra01GrowthCachebadMasksData017
public import RootedSixExtra01GrowthCachebadMasksData018
public import RootedSixExtra01GrowthCachesignatureMasksData000
public import RootedSixExtra01GrowthCachesignatureMasksData001
public import RootedSixExtra01GrowthCachesignatureMasksData002
public import RootedSixExtra01GrowthCachesignatureMasksData003
public import RootedSixExtra01GrowthCachesignatureMasksData004

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def rawCells := Papers.RationalityTen.FacetUniverses.RootedSixExtra01.rawCells
def cells (c : Fin 3150) := rawCells c.val
def ridgeList := ConcreteGrowth.ridgeList cells
def literalCompatible (a b : Fin 3150) := ConcreteGrowth.compatible (cells a) (cells b)
def kind (c : Fin 3150) := (cells c).kind
def rawKindCode : Nat := 6336568106598395432885819064929346900338981161174555219015416097523052595747385479870830246739588008010898012142727853533925805518241397336706597953288210400711640609498749283162613466586968512297946707897816267706406153359428653162160025579139790153060507003601872535423805887953061325701437421115257588902347289396946238650560327794905002976904611481738881809835274066070494752763637867933074757433113772429476984037132692841262537993973832849076388057008887162661745162315663300310645714580397673712128508172949455291309227667316332102732969622528287882032506974687550252157163052386713285671590976568370894453480268166313058958157830442089967405561183316764117719104901253886733600195909889653012794792861607296694800441198910871274816008678229097500340200208513433837020371407299583687309237509126904778696442940367023251450650603932137277726100327475311676785782561521491873427085114903965084950275968858937371778535214924886960563769750026411483005606883467381116061211044358161914243132012288281095161458698009239333447631770440783290031054911204785577351721943680498943216047932349632202764725380085919874673794163427330862195516355377138040109073915931726025620757781527793947238969138575450771156168781679830574291022346254058604460156842976547777856016418236379597507238640590979660440265512382262978053693473138178951662286690712390934703709119226223808616153595547977642985546974668618520804755870263263297622101081739998877003635359639679692826427386541534182191394106995127542258468224474227312168127677494940336034369032211965698069808212598694134612811856805949992076810041646347952347159827815257985497792290639447157144811751551761781925132252848069510711057999372870556063040871687966753092666713983322747059388311600995747452130567623023162300212616679239004641119342175217711104035132331128660745202768067351894078530292239803958658882562349810191549875411252534261210639083267949750435088712696839039735856132396881378269096024690776598075644829463777269254953922192512719889304174462267577188090440979590885947403224713582409629789305265412462411627548932590983438136010993705865836556050086786945485012339467115237022917539380963528951112968486046887933242680531982151691529662764979755118249416013890693840784124076858068168804225485490909206101341759238121777892660614134439775373238264433171781843701376632109751296278358437969874339211360632057769813916765241941757914063668482858260609657385319365378834113943872299084690961863016282415704906072764247973380360028692103544858428165904466399632180362300693109757257728523853973318849431514388937902150594543168810499713254646794352367667460030202874033066421418915610475243576683543321471380125489784289291553343828423814682632379767469353709702563020740262640961343969453041990229882915711058905543470447821530110594444289547195102600712343744461520246022383077804989677828323120837737531950857532694043091870000239431870819185308794463438227413487192657626741425024032288537090959893739763991735937668757378271341071083828832501240985257278806563736317911853424521516914228446579697498395746987287652923839904502205810788578432848538856504910968305229587690838166810395509822685352238527710973573693229996495413807495937233967192859539050957184234785546508651837524722430615369141986374803606254045466608038634454681083347013076145549825397351659798791093552581189144499844619384176576741883193086759969093296815956213193193021238411789087500156227965450289588717286084284141326615303850323932562390992713424766488979653661804138291766032956015609004454790489139388385525181933290773064291226295477619750965744189503829217822395047018225460535545970696480974498425168808164614192485428211839547903901665831336182253769380852473249358921241555173415743648730057519057026634330517061440008010559944609461085212944
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
 (.branch 14
 (.branch 13
 (.leaf 0x0)
 (.leaf (certNat% 2)))
 (.leaf 0x0))))
 (.branch 24
 (.branch 20
 (.leaf 0x0)
 (.branch 22
 (.leaf 0x0)
 (.branch 23
 (.leaf (certNat% 3))
 (.leaf 0x0))))
 (.leaf 0x0)))
 (.branch 48
 (.branch 40
 (.leaf 0x0)
 (.branch 44
 (.leaf 0x0)
 (.branch 46
 (.branch 45
 (.leaf (certNat% 4))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 56
 (.branch 52
 (.leaf 0x0)
 (.branch 54
 (.branch 53
 (.leaf (certNat% 5))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 60
 (.branch 58
 (.leaf 0x0)
 (.branch 59
 (.leaf (certNat% 6))
 (.leaf 0x0)))
 (.leaf 0x0)))))
 (.branch 96
 (.branch 80
 (.branch 72
 (.branch 68
 (.branch 66
 (.leaf 0x0)
 (.branch 67
 (.leaf 0x0)
 (.leaf (certNat% 7))))
 (.branch 70
 (.branch 69
 (.leaf 0x0)
 (.leaf (certNat% 8)))
 (.branch 71
 (.leaf (certNat% 9))
 (.leaf 0x0))))
 (.branch 76
 (.branch 74
 (.branch 73
 (.leaf 0x0)
 (.leaf (certNat% 10)))
 (.branch 75
 (.leaf (certNat% 11))
 (.leaf 0x0)))
 (.branch 78
 (.branch 77
 (.leaf (certNat% 12))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 88
 (.branch 84
 (.branch 82
 (.leaf 0x0)
 (.branch 83
 (.leaf (certNat% 13))
 (.leaf 0x0)))
 (.branch 86
 (.branch 85
 (.leaf (certNat% 14))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 112
 (.branch 104
 (.branch 100
 (.leaf 0x0)
 (.branch 102
 (.branch 101
 (.leaf (certNat% 15))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 108
 (.branch 106
 (.branch 105
 (.leaf (certNat% 16))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 120
 (.branch 116
 (.branch 114
 (.branch 113
 (.leaf (certNat% 17))
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
 (.leaf (certNat% 18))))
 (.branch 134
 (.branch 133
 (.leaf 0x0)
 (.leaf (certNat% 19)))
 (.branch 135
 (.leaf (certNat% 20))
 (.leaf 0x0))))
 (.branch 140
 (.branch 138
 (.branch 137
 (.leaf 0x0)
 (.leaf (certNat% 21)))
 (.branch 139
 (.leaf (certNat% 22))
 (.leaf 0x0)))
 (.branch 142
 (.branch 141
 (.leaf (certNat% 23))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 152
 (.branch 148
 (.branch 146
 (.leaf 0x0)
 (.branch 147
 (.leaf (certNat% 24))
 (.leaf 0x0)))
 (.branch 150
 (.branch 149
 (.leaf (certNat% 25))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 176
 (.branch 168
 (.branch 164
 (.leaf 0x0)
 (.branch 166
 (.branch 165
 (.leaf (certNat% 26))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 172
 (.branch 170
 (.branch 169
 (.leaf (certNat% 27))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 184
 (.branch 180
 (.branch 178
 (.branch 177
 (.leaf (certNat% 28))
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
 (.leaf (certNat% 29)))
 (.branch 195
 (.leaf (certNat% 30))
 (.leaf (certNat% 31))))
 (.branch 198
 (.branch 197
 (.leaf (certNat% 32))
 (.leaf (certNat% 33)))
 (.branch 199
 (.leaf (certNat% 34))
 (.leaf 0x0))))
 (.branch 204
 (.branch 202
 (.branch 201
 (.leaf (certNat% 35))
 (.leaf (certNat% 36)))
 (.branch 203
 (.leaf (certNat% 37))
 (.leaf 0x0)))
 (.branch 206
 (.branch 205
 (.leaf (certNat% 38))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 216
 (.branch 212
 (.branch 210
 (.branch 209
 (.leaf (certNat% 39))
 (.leaf 0x0))
 (.branch 211
 (.leaf (certNat% 40))
 (.leaf 0x0)))
 (.branch 214
 (.branch 213
 (.leaf (certNat% 41))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 240
 (.branch 232
 (.branch 228
 (.branch 226
 (.branch 225
 (.leaf (certNat% 42))
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 230
 (.branch 229
 (.leaf (certNat% 43))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 236
 (.branch 234
 (.branch 233
 (.leaf (certNat% 44))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 248
 (.branch 244
 (.branch 242
 (.branch 241
 (.leaf (certNat% 45))
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
 (.leaf (certNat% 46))))
 (.branch 262
 (.branch 261
 (.leaf 0x0)
 (.leaf (certNat% 47)))
 (.branch 263
 (.leaf (certNat% 48))
 (.leaf 0x0))))
 (.branch 268
 (.branch 266
 (.branch 265
 (.leaf 0x0)
 (.leaf (certNat% 49)))
 (.branch 267
 (.leaf (certNat% 50))
 (.leaf 0x0)))
 (.branch 270
 (.branch 269
 (.leaf (certNat% 51))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 280
 (.branch 276
 (.branch 274
 (.leaf 0x0)
 (.branch 275
 (.leaf (certNat% 52))
 (.leaf 0x0)))
 (.branch 278
 (.branch 277
 (.leaf (certNat% 53))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 304
 (.branch 296
 (.branch 292
 (.leaf 0x0)
 (.branch 294
 (.branch 293
 (.leaf (certNat% 54))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 300
 (.branch 298
 (.branch 297
 (.leaf (certNat% 55))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 312
 (.branch 308
 (.branch 306
 (.branch 305
 (.leaf (certNat% 56))
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
 (.leaf (certNat% 57)))
 (.branch 323
 (.leaf (certNat% 58))
 (.leaf (certNat% 59))))
 (.branch 326
 (.branch 325
 (.leaf (certNat% 60))
 (.leaf (certNat% 61)))
 (.branch 327
 (.leaf (certNat% 62))
 (.leaf 0x0))))
 (.branch 332
 (.branch 330
 (.branch 329
 (.leaf (certNat% 63))
 (.leaf (certNat% 64)))
 (.branch 331
 (.leaf (certNat% 65))
 (.leaf 0x0)))
 (.branch 334
 (.branch 333
 (.leaf (certNat% 66))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 344
 (.branch 340
 (.branch 338
 (.branch 337
 (.leaf (certNat% 67))
 (.leaf 0x0))
 (.branch 339
 (.leaf (certNat% 68))
 (.leaf 0x0)))
 (.branch 342
 (.branch 341
 (.leaf (certNat% 69))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 368
 (.branch 360
 (.branch 356
 (.branch 354
 (.branch 353
 (.leaf (certNat% 70))
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 358
 (.branch 357
 (.leaf (certNat% 71))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 364
 (.branch 362
 (.branch 361
 (.leaf (certNat% 72))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 376
 (.branch 372
 (.branch 370
 (.branch 369
 (.leaf (certNat% 73))
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
 (.leaf (certNat% 74)))
 (.branch 387
 (.leaf (certNat% 75))
 (.leaf (certNat% 76))))
 (.branch 390
 (.branch 389
 (.leaf (certNat% 77))
 (.leaf (certNat% 78)))
 (.branch 391
 (.leaf (certNat% 79))
 (.leaf 0x0))))
 (.branch 396
 (.branch 394
 (.branch 393
 (.leaf (certNat% 80))
 (.leaf (certNat% 81)))
 (.branch 395
 (.leaf (certNat% 82))
 (.leaf 0x0)))
 (.branch 398
 (.branch 397
 (.leaf (certNat% 83))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 408
 (.branch 404
 (.branch 402
 (.branch 401
 (.leaf (certNat% 84))
 (.leaf 0x0))
 (.branch 403
 (.leaf (certNat% 85))
 (.leaf 0x0)))
 (.branch 406
 (.branch 405
 (.leaf (certNat% 86))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 432
 (.branch 424
 (.branch 420
 (.branch 418
 (.branch 417
 (.leaf (certNat% 87))
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 422
 (.branch 421
 (.leaf (certNat% 88))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 428
 (.branch 426
 (.branch 425
 (.leaf (certNat% 89))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 440
 (.branch 436
 (.branch 434
 (.branch 433
 (.leaf (certNat% 90))
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
 (.leaf (certNat% 91))
 (.leaf (certNat% 92)))
 (.branch 451
 (.leaf (certNat% 93))
 (.leaf (certNat% 94))))
 (.branch 454
 (.branch 453
 (.leaf (certNat% 95))
 (.leaf (certNat% 96)))
 (.branch 455
 (.leaf (certNat% 97))
 (.leaf 0x0))))
 (.branch 460
 (.branch 458
 (.branch 457
 (.leaf (certNat% 98))
 (.leaf (certNat% 99)))
 (.branch 459
 (.leaf (certNat% 100))
 (.leaf 0x0)))
 (.branch 462
 (.branch 461
 (.leaf (certNat% 101))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 472
 (.branch 468
 (.branch 466
 (.branch 465
 (.leaf (certNat% 102))
 (.leaf 0x0))
 (.branch 467
 (.leaf (certNat% 103))
 (.leaf 0x0)))
 (.branch 470
 (.branch 469
 (.leaf (certNat% 104))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 496
 (.branch 488
 (.branch 484
 (.branch 482
 (.branch 481
 (.leaf (certNat% 105))
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 486
 (.branch 485
 (.leaf (certNat% 106))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 492
 (.branch 490
 (.branch 489
 (.leaf (certNat% 107))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 504
 (.branch 500
 (.branch 498
 (.branch 497
 (.leaf (certNat% 108))
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
 (.leaf (certNat% 109))))
 (.branch 518
 (.branch 517
 (.leaf 0x0)
 (.leaf (certNat% 110)))
 (.branch 519
 (.leaf (certNat% 111))
 (.leaf 0x0))))
 (.branch 524
 (.branch 522
 (.branch 521
 (.leaf 0x0)
 (.leaf (certNat% 112)))
 (.branch 523
 (.leaf (certNat% 113))
 (.leaf 0x0)))
 (.branch 526
 (.branch 525
 (.leaf (certNat% 114))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 536
 (.branch 532
 (.branch 530
 (.leaf 0x0)
 (.branch 531
 (.leaf (certNat% 115))
 (.leaf 0x0)))
 (.branch 534
 (.branch 533
 (.leaf (certNat% 116))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 560
 (.branch 552
 (.branch 548
 (.leaf 0x0)
 (.branch 550
 (.branch 549
 (.leaf (certNat% 117))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 556
 (.branch 554
 (.branch 553
 (.leaf (certNat% 118))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 568
 (.branch 564
 (.branch 562
 (.branch 561
 (.leaf (certNat% 119))
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
 (.leaf (certNat% 120)))
 (.branch 579
 (.leaf (certNat% 121))
 (.leaf (certNat% 122))))
 (.branch 582
 (.branch 581
 (.leaf (certNat% 123))
 (.leaf (certNat% 124)))
 (.branch 583
 (.leaf (certNat% 125))
 (.leaf 0x0))))
 (.branch 588
 (.branch 586
 (.branch 585
 (.leaf (certNat% 126))
 (.leaf (certNat% 127)))
 (.branch 587
 (.leaf (certNat% 128))
 (.leaf 0x0)))
 (.branch 590
 (.branch 589
 (.leaf (certNat% 129))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 600
 (.branch 596
 (.branch 594
 (.branch 593
 (.leaf (certNat% 130))
 (.leaf 0x0))
 (.branch 595
 (.leaf (certNat% 131))
 (.leaf 0x0)))
 (.branch 598
 (.branch 597
 (.leaf (certNat% 132))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 624
 (.branch 616
 (.branch 612
 (.branch 610
 (.branch 609
 (.leaf (certNat% 133))
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 614
 (.branch 613
 (.leaf (certNat% 134))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 620
 (.branch 618
 (.branch 617
 (.leaf (certNat% 135))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 632
 (.branch 628
 (.branch 626
 (.branch 625
 (.leaf (certNat% 136))
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
 (.leaf (certNat% 137)))
 (.branch 643
 (.leaf (certNat% 138))
 (.leaf (certNat% 139))))
 (.branch 646
 (.branch 645
 (.leaf (certNat% 140))
 (.leaf (certNat% 141)))
 (.branch 647
 (.leaf (certNat% 142))
 (.leaf 0x0))))
 (.branch 652
 (.branch 650
 (.branch 649
 (.leaf (certNat% 143))
 (.leaf (certNat% 144)))
 (.branch 651
 (.leaf (certNat% 145))
 (.leaf 0x0)))
 (.branch 654
 (.branch 653
 (.leaf (certNat% 146))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 664
 (.branch 660
 (.branch 658
 (.branch 657
 (.leaf (certNat% 147))
 (.leaf 0x0))
 (.branch 659
 (.leaf (certNat% 148))
 (.leaf 0x0)))
 (.branch 662
 (.branch 661
 (.leaf (certNat% 149))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 688
 (.branch 680
 (.branch 676
 (.branch 674
 (.branch 673
 (.leaf (certNat% 150))
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 678
 (.branch 677
 (.leaf (certNat% 151))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 684
 (.branch 682
 (.branch 681
 (.leaf (certNat% 152))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 696
 (.branch 692
 (.branch 690
 (.branch 689
 (.leaf (certNat% 153))
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
 (.leaf (certNat% 154))
 (.leaf (certNat% 155)))
 (.branch 707
 (.leaf (certNat% 156))
 (.leaf (certNat% 157))))
 (.branch 710
 (.branch 709
 (.leaf (certNat% 158))
 (.leaf (certNat% 159)))
 (.branch 711
 (.leaf (certNat% 160))
 (.leaf 0x0))))
 (.branch 716
 (.branch 714
 (.branch 713
 (.leaf (certNat% 161))
 (.leaf (certNat% 162)))
 (.branch 715
 (.leaf (certNat% 163))
 (.leaf 0x0)))
 (.branch 718
 (.branch 717
 (.leaf (certNat% 164))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 728
 (.branch 724
 (.branch 722
 (.branch 721
 (.leaf (certNat% 165))
 (.leaf 0x0))
 (.branch 723
 (.leaf (certNat% 166))
 (.leaf 0x0)))
 (.branch 726
 (.branch 725
 (.leaf (certNat% 167))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 752
 (.branch 744
 (.branch 740
 (.branch 738
 (.branch 737
 (.leaf (certNat% 168))
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 742
 (.branch 741
 (.leaf (certNat% 169))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 748
 (.branch 746
 (.branch 745
 (.leaf (certNat% 170))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 760
 (.branch 756
 (.branch 754
 (.branch 753
 (.leaf (certNat% 171))
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
 (.leaf (certNat% 172)))
 (.branch 771
 (.leaf (certNat% 173))
 (.leaf (certNat% 174))))
 (.branch 774
 (.branch 773
 (.leaf (certNat% 175))
 (.leaf (certNat% 176)))
 (.branch 775
 (.leaf (certNat% 177))
 (.leaf 0x0))))
 (.branch 780
 (.branch 778
 (.branch 777
 (.leaf (certNat% 178))
 (.leaf (certNat% 179)))
 (.branch 779
 (.leaf (certNat% 180))
 (.leaf 0x0)))
 (.branch 782
 (.branch 781
 (.leaf (certNat% 181))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 792
 (.branch 788
 (.branch 786
 (.branch 785
 (.leaf (certNat% 182))
 (.leaf 0x0))
 (.branch 787
 (.leaf (certNat% 183))
 (.leaf 0x0)))
 (.branch 790
 (.branch 789
 (.leaf (certNat% 184))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 816
 (.branch 808
 (.branch 804
 (.branch 802
 (.branch 801
 (.leaf (certNat% 185))
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 806
 (.branch 805
 (.leaf (certNat% 186))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 812
 (.branch 810
 (.branch 809
 (.leaf (certNat% 187))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 824
 (.branch 820
 (.branch 818
 (.branch 817
 (.leaf (certNat% 188))
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
 (.leaf (certNat% 189))
 (.leaf (certNat% 190)))
 (.branch 835
 (.leaf (certNat% 191))
 (.leaf (certNat% 192))))
 (.branch 838
 (.branch 837
 (.leaf (certNat% 193))
 (.leaf (certNat% 194)))
 (.branch 839
 (.leaf (certNat% 195))
 (.leaf 0x0))))
 (.branch 844
 (.branch 842
 (.branch 841
 (.leaf (certNat% 196))
 (.leaf (certNat% 197)))
 (.branch 843
 (.leaf (certNat% 198))
 (.leaf 0x0)))
 (.branch 846
 (.branch 845
 (.leaf (certNat% 199))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 856
 (.branch 852
 (.branch 850
 (.branch 849
 (.leaf (certNat% 200))
 (.leaf 0x0))
 (.branch 851
 (.leaf (certNat% 201))
 (.leaf 0x0)))
 (.branch 854
 (.branch 853
 (.leaf (certNat% 202))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 880
 (.branch 872
 (.branch 868
 (.branch 866
 (.branch 865
 (.leaf (certNat% 203))
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 870
 (.branch 869
 (.leaf (certNat% 204))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 876
 (.branch 874
 (.branch 873
 (.leaf (certNat% 205))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 888
 (.branch 884
 (.branch 882
 (.branch 881
 (.leaf (certNat% 206))
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
 (.leaf (certNat% 207))
 (.leaf (certNat% 208)))
 (.branch 899
 (.leaf (certNat% 209))
 (.leaf (certNat% 210))))
 (.branch 902
 (.branch 901
 (.leaf (certNat% 211))
 (.leaf (certNat% 212)))
 (.branch 903
 (.leaf (certNat% 213))
 (.leaf 0x0))))
 (.branch 908
 (.branch 906
 (.branch 905
 (.leaf (certNat% 214))
 (.leaf (certNat% 215)))
 (.branch 907
 (.leaf (certNat% 216))
 (.leaf 0x0)))
 (.branch 910
 (.branch 909
 (.leaf (certNat% 217))
 (.leaf 0x0))
 (.leaf 0x0))))
 (.branch 920
 (.branch 916
 (.branch 914
 (.branch 913
 (.leaf (certNat% 218))
 (.leaf 0x0))
 (.branch 915
 (.leaf (certNat% 219))
 (.leaf 0x0)))
 (.branch 918
 (.branch 917
 (.leaf (certNat% 220))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.leaf 0x0)))
 (.branch 944
 (.branch 936
 (.branch 932
 (.branch 930
 (.branch 929
 (.leaf (certNat% 221))
 (.leaf 0x0))
 (.leaf 0x0))
 (.branch 934
 (.branch 933
 (.leaf (certNat% 222))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 940
 (.branch 938
 (.branch 937
 (.leaf (certNat% 223))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 952
 (.branch 948
 (.branch 946
 (.branch 945
 (.leaf (certNat% 224))
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
 (.leaf (certNat% 225))
 (.leaf (certNat% 226)))
 (.branch 963
 (.leaf (certNat% 227))
 (.leaf 0x0)))
 (.branch 966
 (.branch 965
 (.leaf (certNat% 228))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 972
 (.branch 970
 (.branch 969
 (.leaf (certNat% 229))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 984
 (.branch 980
 (.branch 978
 (.branch 977
 (.leaf (certNat% 230))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0))
 (.leaf 0x0)))
 (.branch 1008
 (.branch 1000
 (.branch 996
 (.branch 994
 (.branch 993
 (.leaf (certNat% 231))
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
 (.leaf (certNat% 232)))
 (.branch 3
 (.leaf (certNat% 233))
 (.branch 4
 (.leaf (certNat% 234))
 (.leaf 0x0))))
 (.branch 8
 (.leaf 0x0)
 (.branch 9
 (.leaf 0x0)
 (.branch 10
 (.leaf (certNat% 235))
 (.leaf (certNat% 236))))))
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
 (.leaf (certNat% 237)))
 (.branch 3
 (.leaf (certNat% 238))
 (.branch 4
 (.leaf (certNat% 239))
 (.leaf 0x0))))
 (.branch 8
 (.leaf 0x0)
 (.branch 9
 (.leaf 0x0)
 (.branch 10
 (.leaf (certNat% 240))
 (.leaf (certNat% 241))))))
def kindMasks := kindMaskTable.get
def keys := List.range 11
def vertexMaskTable : Table Nat :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf 9436442952940315187603282328148616922776587777934983902315654287645969425482143236130047054609576464602674676387859887270577192754764525492234177312354370269940003930217668407428836030437838806381511086146586556725912263248667575982356715354025682301410468859933890426846049488756730532576845848356783618690142786477022820242720389773275125389349859998154084903689478658409582384951783517942227277252404755554384784609955464336471759515239964906115607322226091931330591173238769491785645518193386000787637370370148011398214340636132250304682309588693687943724376602557498561169528090247929516280756166013817715341321285749531369188149478008223951657822612384506627869321459656841773426790394277804969511712881035769789681531007012963544046204156467255987157888168473233275186751256568904709717813526322630098943)
 (.leaf 3530592467533294366865588866274922040023847284723899938846984433410589015264723728266767650749767401815822817536188971560677693130023878733182998093236590362433860763622543197183129009672080708387449073025810357155204672465344871622246749775834087476807277586672696999197204443040380346843633803953853525901899484158927728341581116969084800073369313238733846424491256063939140310497005131084718872308596203052974617768451132367343333472922989949777290287798828236685524947547678111818053840918282618455744148879069594935489635685684050905864376068101192252217643436387311210006550327422714684466967438211432407206409837152469972984483730330944440828065949426266591441846467867815655252984709078220390283803298214093603484026803335203260275834403840062256319462603630764533743467238656545317946601536643751867922616100496725879125031558857431656737767388113567743))
 (.branch 3
 (.leaf 1755845672397672524359719948712336067160661248520417246974434489093977610120643664365181616027261987866859128694843405880429765984294574205114755676899061807102367360867539428013393255590894187308312577559334383616399035947191568562815480946248109988856274127303488875400092686458526736038500592045265782723343965332854670044321053977150900200627786787887720064035359844134708845825937128526958779259195948847623462477459056715681472911208271485965341868669328078772805434094982769582478219593550945178339761008392159631134821204061357238882981909304757136137918878331710434694079611869795883681521159967931850194856965543914172670164354205601321360420749210589432465462879327655113114392769530346384123369309383890445360130841227849011830895382647399363329401615505509904635116446608773608561035356574510410231861481018430059561063470148723796491947741073455491990754270356636355436393859420895382150185512005459962861162348435794506280413844963359)
 (.branch 4
 (.leaf 1320951468044303979436222683331055660873133410496862126229431027379899921428923631133139176883894753826982121592902705011009297945054436865931852985720691416549251614586100276620766905054333055285047394126016105585967355406454788522224008829627190049082737263486615545338412694862156519026482779763329120664335803335519256681272027306972234007550142038093957057220320024475534801309683502004741441062062669046368412604324217384178292645383836187503063225359776187014622863770758340195427397737351242260846761208765056833801780643969502353971175288404056289161164957044373432990458426964472986907189307748940262035833547153756650459158755647336524030708728502201730599428585905119604588677327928313504130025865147380352811699051700260962365704988014940623417568621318145715713140315912949480439786543901168016092898333389392056783148100486888975939015332190142793889780963015122311546582518544855447585163229757921)
 (.leaf 1755845672397672524360091763496039741834781320593940780861992811196942876071323419757595945863040490237858095561587221193830911729666983092079959875228377263045074372997953595247082494653256103361382680413196189286886475682299251072280943876020174245488602523799481785336616268787908346919691212774521236722642940618216070704790665266168708329815874558978641360954232180032559878822491183793926778721548630125667249811160775465592714975179212419494057684821347975307562939721537963078874350004139104745635558722643554720975607817369120540147499477027417741793452439267343429361323931350914561170633340903404163983106748764982884132789246509061399888916995794389843434307940651133683328021163206010993247090328967287512618871073882124138891361495740610864950139388325902170895173834878886445564126569987754959088318671027077578222808371324849520459199377501668107982961411821555263515968116842560465986884056614452323324209585121473010878482911068161))))
 (.branch 7
 (.branch 6
 (.leaf 1755845672397672524360091763496039743155732788638244760298215494527998537938230262828202542629514553678731087407841852866990356882456276386923835731312844611359588896399251605232367805733932571196933428148150603637379369649195675726853470024267432655618375851043966094848026664383750521774517143195380620458596015896895633239243667791545023439216766574379892227965166147230271223707154470798082170677777645202772483598108416194674218290938740436322734821777349393625555476161474736114937355045434342475214651278109783428838187515346160843332217962317557568846298909296179681079903543901463055102523791210051254417934943826615458574159567727769701851739538227390865586453588119012612561601725587038880604727967050420586643217821086312479934803205574368541555156027451186783299038558323854910160212345584330711802455251498394495249914032728890946986611819288306708720351454432974254574368881264316631062431987008431495132945299403713566111834820313089)
 (.leaf 6698019685354890916290633253081106052303486826553968088437420050062674565802258308511923277900041010147362728067021827035128234855822505403044606503004545698569407002155536916599921765682701273802427373789224724592972648980958671940864241933729803632289011791499446923993283427465274385280165799167639642861699377984357538827471999514629597723762567268292801783095492796225504693064124485329303482077541206964132473567915029455217778452220403686324036112091446880734159262124319651178074633618414572942223034645386292034567425241164270731577042058866548466515689687654441143409179950397732926827850427493252703324536651803164358066226178856768214014800564792014858197460858761618139522926630945600119888583826248544579170870889270077761196558570116722508296428997998848698213021517114092635303911628436300714337514304899374034126814984387891580116109948594091191655744861236138366364830019375548816210267831174345539993197396379024172672126498))
 (.branch 8
 (.leaf 1755838974403538086848001198098880690167062250001140148259769716150247729418961221139437419743125814450412208170127587281077300127604172871276430354496174939910649453704928850018579369846989574236766044386751215897005811154046694415550708991223505779091033094738733552975393666282710024949834921279370709005439725120359680698085951688343055992137305748227335509545952608966436624990872695134009752087190924422535922853570587913408828953105598727748099272470630756910588717930012945968160801784585533989645174671422100683121451987372903954871278877991722451326669091526961872819056132109849573912660432686703270133385056357815730143751669231284839412212508142883130264425907648305981836027012881705980511765778054814127053837154546620301349841775505348040824628957984216365668048724821065544830060583556739810022367120982868032269002792158351219812131590800236523918148890605033283330845089511938530987795601191383864241683015057556978027919143678532)
 (.branch 9
 (.leaf 1755845672372121704450280697476732045252851209542256917339337784392430385507472666739637619362067387966931409075205740508007000026381178522052525825028820698241701718684803643745288665740734711351830800750589256734967665254152672037443473573926626894096714275314316922963085654158354706051066259807233096014255038870451364226823711127721348117034959943550165780723145588091366313966242861369590622713561691489624956736028015154051185195171515505081657114280652532077469712919449207255911275965379727285018508259678097479918434468122479163572989088054436740639243143706560471146125442831740478938328760364286341149681232614122244856268403453798790482274614150041753688820550910441074973585277450242957733521932106899296136558352673826675422853306558024866189239069913979979017463719009269023434167173899488551322534438587248470710959184194117674141834725315596399549331222949968596813822017641633835436069855982743630605828813457009012876722562028680)
 (.leaf 1755845672397672426891448919062957088936304143002338174651231551055288365025051129384007126961705826922518859175917200919663291719877496488535263465773871253073238320904442391436609949879589286490445894228816352674759680184321205766911330525695817503537002840687472805162830785429670759993493726023037419084454946176597217581347112723666791577757617159890609128573108980087519786664708906045907732536981894566355695925700808673889358591837841093830197030244670483937940409025595984546782318098178001191103055475971101057640461715548513608897743176099138906477532412914546922154460500431901410176041553155572567433345487994402817055306658502644360718645994048068100285171772481105848776993743795105957944494569731983458162143154709242073937747852261566386534136029391825606103030400270769658896452369745968292463059605158221204573588527039815966932774500286457476264637752118589503362241688058542060562310758033834334121237999805197640561989177862416)))))
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
 (.leaf (.leaf 0))
 (.branch 38
 (.branch 37
 (.leaf (.leaf 12))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 44
 (.branch 42
 (.branch 41
 (.leaf (.leaf 13))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 46
 (.branch 45
 (.leaf (.leaf 14))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 56
 (.branch 52
 (.branch 50
 (.branch 49
 (.leaf (.leaf 15))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 54
 (.branch 53
 (.leaf (.leaf 16))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 60
 (.branch 58
 (.leaf (.leaf 0))
 (.branch 59
 (.leaf (.leaf 17))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0))))))
 (.branch 96
 (.branch 80
 (.branch 72
 (.branch 68
 (.branch 66
 (.branch 65
 (.leaf (.leaf 0))
 (.leaf (.leaf 18)))
 (.branch 67
 (.leaf (.leaf 19))
 (.leaf (.leaf 20))))
 (.branch 70
 (.branch 69
 (.leaf (.leaf 21))
 (.leaf (.leaf 22)))
 (.branch 71
 (.leaf (.leaf 23))
 (.leaf (.leaf 0)))))
 (.branch 76
 (.branch 74
 (.branch 73
 (.leaf (.leaf 24))
 (.leaf (.leaf 25)))
 (.branch 75
 (.leaf (.leaf 26))
 (.leaf (.leaf 0))))
 (.branch 78
 (.branch 77
 (.leaf (.leaf 27))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 88
 (.branch 84
 (.branch 82
 (.branch 81
 (.leaf (.leaf 28))
 (.leaf (.leaf 0)))
 (.branch 83
 (.leaf (.leaf 29))
 (.leaf (.leaf 0))))
 (.branch 86
 (.branch 85
 (.leaf (.leaf 30))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0))))
 (.branch 112
 (.branch 104
 (.branch 100
 (.branch 98
 (.branch 97
 (.leaf (.leaf 31))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 102
 (.branch 101
 (.leaf (.leaf 32))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 108
 (.branch 106
 (.branch 105
 (.leaf (.leaf 33))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 120
 (.branch 116
 (.branch 114
 (.branch 113
 (.leaf (.leaf 34))
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
 (.leaf (.leaf 35)))
 (.branch 131
 (.leaf (.leaf 36))
 (.leaf (.leaf 37))))
 (.branch 134
 (.branch 133
 (.leaf (.leaf 38))
 (.leaf (.leaf 39)))
 (.branch 135
 (.leaf (.leaf 40))
 (.leaf (.leaf 0)))))
 (.branch 140
 (.branch 138
 (.branch 137
 (.leaf (.leaf 41))
 (.leaf (.leaf 42)))
 (.branch 139
 (.leaf (.leaf 43))
 (.leaf (.leaf 0))))
 (.branch 142
 (.branch 141
 (.leaf (.leaf 44))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 152
 (.branch 148
 (.branch 146
 (.branch 145
 (.leaf (.leaf 45))
 (.leaf (.leaf 0)))
 (.branch 147
 (.leaf (.leaf 46))
 (.leaf (.leaf 0))))
 (.branch 150
 (.branch 149
 (.leaf (.leaf 47))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0))))
 (.branch 176
 (.branch 168
 (.branch 164
 (.branch 162
 (.branch 161
 (.leaf (.leaf 48))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 166
 (.branch 165
 (.leaf (.leaf 49))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 172
 (.branch 170
 (.branch 169
 (.leaf (.leaf 50))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 184
 (.branch 180
 (.branch 178
 (.branch 177
 (.leaf (.leaf 51))
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
 (.leaf (.leaf 52))
 (.leaf (.leaf 53)))
 (.branch 195
 (.leaf (.leaf 54))
 (.leaf (.branch (certNat% 242) (.leaf 55) (.leaf 56)))))
 (.branch 198
 (.branch 197
 (.leaf (.leaf 57))
 (.leaf (.branch (certNat% 243) (.leaf 58) (.leaf 59))))
 (.branch 199
 (.leaf (.branch (certNat% 244) (.leaf 60) (.leaf 61)))
 (.leaf (.leaf 0)))))
 (.branch 204
 (.branch 202
 (.branch 201
 (.leaf (.leaf 62))
 (.leaf (.branch (certNat% 245) (.leaf 63) (.leaf 64))))
 (.branch 203
 (.leaf (.branch (certNat% 246) (.leaf 65) (.leaf 66)))
 (.leaf (.leaf 0))))
 (.branch 206
 (.branch 205
 (.leaf (.branch (certNat% 247) (.leaf 67) (.leaf 68)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 216
 (.branch 212
 (.branch 210
 (.branch 209
 (.leaf (.leaf 69))
 (.leaf (.leaf 0)))
 (.branch 211
 (.leaf (.branch (certNat% 248) (.leaf 70) (.leaf 71)))
 (.leaf (.leaf 0))))
 (.branch 214
 (.branch 213
 (.leaf (.branch (certNat% 249) (.leaf 72) (.leaf 73)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0))))
 (.branch 240
 (.branch 232
 (.branch 228
 (.branch 226
 (.branch 225
 (.leaf (.leaf 74))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 230
 (.branch 229
 (.leaf (.branch (certNat% 250) (.leaf 75) (.leaf 76)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 236
 (.branch 234
 (.branch 233
 (.leaf (.branch (certNat% 251) (.leaf 77) (.leaf 78)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 248
 (.branch 244
 (.branch 242
 (.branch 241
 (.leaf (.branch (certNat% 252) (.leaf 79) (.leaf 80)))
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
 (.leaf (.leaf 81)))
 (.branch 259
 (.leaf (.leaf 82))
 (.leaf (.leaf 83))))
 (.branch 262
 (.branch 261
 (.leaf (.leaf 84))
 (.leaf (.leaf 85)))
 (.branch 263
 (.leaf (.leaf 86))
 (.leaf (.leaf 0)))))
 (.branch 268
 (.branch 266
 (.branch 265
 (.leaf (.leaf 87))
 (.leaf (.leaf 88)))
 (.branch 267
 (.leaf (.leaf 89))
 (.leaf (.leaf 0))))
 (.branch 270
 (.branch 269
 (.leaf (.leaf 90))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 280
 (.branch 276
 (.branch 274
 (.branch 273
 (.leaf (.leaf 91))
 (.leaf (.leaf 0)))
 (.branch 275
 (.leaf (.leaf 92))
 (.leaf (.leaf 0))))
 (.branch 278
 (.branch 277
 (.leaf (.leaf 93))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0))))
 (.branch 304
 (.branch 296
 (.branch 292
 (.branch 290
 (.branch 289
 (.leaf (.leaf 94))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 294
 (.branch 293
 (.leaf (.leaf 95))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 300
 (.branch 298
 (.branch 297
 (.leaf (.leaf 96))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 312
 (.branch 308
 (.branch 306
 (.branch 305
 (.leaf (.leaf 97))
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
 (.leaf (.leaf 98))
 (.leaf (.leaf 99)))
 (.branch 323
 (.leaf (.leaf 100))
 (.leaf (.branch (certNat% 253) (.leaf 101) (.leaf 102)))))
 (.branch 326
 (.branch 325
 (.leaf (.leaf 103))
 (.leaf (.branch (certNat% 254) (.leaf 104) (.leaf 105))))
 (.branch 327
 (.leaf (.branch (certNat% 255) (.leaf 106) (.leaf 107)))
 (.leaf (.leaf 0)))))
 (.branch 332
 (.branch 330
 (.branch 329
 (.leaf (.leaf 108))
 (.leaf (.branch (certNat% 256) (.leaf 109) (.leaf 110))))
 (.branch 331
 (.leaf (.branch (certNat% 257) (.leaf 111) (.leaf 112)))
 (.leaf (.leaf 0))))
 (.branch 334
 (.branch 333
 (.leaf (.branch (certNat% 258) (.leaf 113) (.leaf 114)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 344
 (.branch 340
 (.branch 338
 (.branch 337
 (.leaf (.leaf 115))
 (.leaf (.leaf 0)))
 (.branch 339
 (.leaf (.branch (certNat% 259) (.leaf 116) (.leaf 117)))
 (.leaf (.leaf 0))))
 (.branch 342
 (.branch 341
 (.leaf (.branch (certNat% 260) (.leaf 118) (.leaf 119)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0))))
 (.branch 368
 (.branch 360
 (.branch 356
 (.branch 354
 (.branch 353
 (.leaf (.leaf 120))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 358
 (.branch 357
 (.leaf (.branch (certNat% 261) (.leaf 121) (.leaf 122)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 364
 (.branch 362
 (.branch 361
 (.leaf (.branch (certNat% 262) (.leaf 123) (.leaf 124)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 376
 (.branch 372
 (.branch 370
 (.branch 369
 (.leaf (.branch (certNat% 263) (.leaf 125) (.leaf 126)))
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
 (.leaf (.leaf 127))
 (.leaf (.leaf 128)))
 (.branch 387
 (.leaf (.leaf 129))
 (.leaf (.branch (certNat% 264) (.leaf 130) (.leaf 131)))))
 (.branch 390
 (.branch 389
 (.leaf (.leaf 132))
 (.leaf (.branch (certNat% 265) (.leaf 133) (.leaf 134))))
 (.branch 391
 (.leaf (.branch (certNat% 266) (.leaf 135) (.leaf 136)))
 (.leaf (.leaf 0)))))
 (.branch 396
 (.branch 394
 (.branch 393
 (.leaf (.leaf 137))
 (.leaf (.branch (certNat% 267) (.leaf 138) (.leaf 139))))
 (.branch 395
 (.leaf (.branch (certNat% 268) (.leaf 140) (.leaf 141)))
 (.leaf (.leaf 0))))
 (.branch 398
 (.branch 397
 (.leaf (.branch (certNat% 269) (.leaf 142) (.leaf 143)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 408
 (.branch 404
 (.branch 402
 (.branch 401
 (.leaf (.leaf 144))
 (.leaf (.leaf 0)))
 (.branch 403
 (.leaf (.branch (certNat% 270) (.leaf 145) (.leaf 146)))
 (.leaf (.leaf 0))))
 (.branch 406
 (.branch 405
 (.leaf (.branch (certNat% 271) (.leaf 147) (.leaf 148)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0))))
 (.branch 432
 (.branch 424
 (.branch 420
 (.branch 418
 (.branch 417
 (.leaf (.leaf 149))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 422
 (.branch 421
 (.leaf (.branch (certNat% 272) (.leaf 150) (.leaf 151)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 428
 (.branch 426
 (.branch 425
 (.leaf (.branch (certNat% 273) (.leaf 152) (.leaf 153)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 440
 (.branch 436
 (.branch 434
 (.branch 433
 (.leaf (.branch (certNat% 274) (.leaf 154) (.leaf 155)))
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
 (.leaf (.leaf 156))
 (.leaf (.branch (certNat% 275) (.leaf 157) (.branch (certNat% 276) (.leaf 158) (.leaf 159)))))
 (.branch 451
 (.leaf (.branch (certNat% 277) (.leaf 160) (.branch (certNat% 278) (.leaf 161) (.leaf 162))))
 (.leaf (.branch (certNat% 279) (.branch (certNat% 280) (.leaf 163) (.branch (certNat% 281) (.leaf 164) (.leaf 165))) (.branch (certNat% 282) (.leaf 166) (.branch (certNat% 283) (.leaf 167) (.leaf 168)))))))
 (.branch 454
 (.branch 453
 (.leaf (.branch (certNat% 284) (.leaf 169) (.branch (certNat% 285) (.leaf 170) (.leaf 171))))
 (.leaf (.branch (certNat% 286) (.branch (certNat% 287) (.leaf 172) (.branch (certNat% 288) (.leaf 173) (.leaf 174))) (.branch (certNat% 289) (.leaf 175) (.branch (certNat% 290) (.leaf 176) (.leaf 177))))))
 (.branch 455
 (.leaf (.branch (certNat% 291) (.branch (certNat% 292) (.leaf 178) (.branch (certNat% 293) (.leaf 179) (.leaf 180))) (.branch (certNat% 294) (.leaf 181) (.branch (certNat% 295) (.leaf 182) (.leaf 183)))))
 (.leaf (.leaf 0)))))
 (.branch 460
 (.branch 458
 (.branch 457
 (.leaf (.branch (certNat% 296) (.leaf 184) (.branch (certNat% 297) (.leaf 185) (.leaf 186))))
 (.leaf (.branch (certNat% 298) (.branch (certNat% 299) (.leaf 187) (.branch (certNat% 300) (.leaf 188) (.leaf 189))) (.branch (certNat% 301) (.leaf 190) (.branch (certNat% 302) (.leaf 191) (.leaf 192))))))
 (.branch 459
 (.leaf (.branch (certNat% 303) (.branch (certNat% 304) (.leaf 193) (.branch (certNat% 305) (.leaf 194) (.leaf 195))) (.branch (certNat% 306) (.leaf 196) (.branch (certNat% 307) (.leaf 197) (.leaf 198)))))
 (.leaf (.leaf 0))))
 (.branch 462
 (.branch 461
 (.leaf (.branch (certNat% 308) (.branch (certNat% 309) (.leaf 199) (.branch (certNat% 310) (.leaf 200) (.leaf 201))) (.branch (certNat% 311) (.leaf 202) (.branch (certNat% 312) (.leaf 203) (.leaf 204)))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 472
 (.branch 468
 (.branch 466
 (.branch 465
 (.leaf (.branch (certNat% 313) (.leaf 205) (.branch (certNat% 314) (.leaf 206) (.leaf 207))))
 (.leaf (.leaf 0)))
 (.branch 467
 (.leaf (.branch (certNat% 315) (.branch (certNat% 316) (.leaf 208) (.branch (certNat% 317) (.leaf 209) (.leaf 210))) (.branch (certNat% 318) (.leaf 211) (.branch (certNat% 319) (.leaf 212) (.leaf 213)))))
 (.leaf (.leaf 0))))
 (.branch 470
 (.branch 469
 (.leaf (.branch (certNat% 320) (.branch (certNat% 321) (.leaf 214) (.branch (certNat% 322) (.leaf 215) (.leaf 216))) (.branch (certNat% 323) (.leaf 217) (.branch (certNat% 324) (.leaf 218) (.leaf 219)))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0))))
 (.branch 496
 (.branch 488
 (.branch 484
 (.branch 482
 (.branch 481
 (.leaf (.branch (certNat% 325) (.leaf 220) (.branch (certNat% 326) (.leaf 221) (.leaf 222))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 486
 (.branch 485
 (.leaf (.branch (certNat% 327) (.branch (certNat% 328) (.leaf 223) (.branch (certNat% 329) (.leaf 224) (.leaf 225))) (.branch (certNat% 330) (.leaf 226) (.branch (certNat% 331) (.leaf 227) (.leaf 228)))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 492
 (.branch 490
 (.branch 489
 (.leaf (.branch (certNat% 332) (.branch (certNat% 333) (.leaf 229) (.branch (certNat% 334) (.leaf 230) (.leaf 231))) (.branch (certNat% 335) (.leaf 232) (.branch (certNat% 336) (.leaf 233) (.leaf 234)))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 504
 (.branch 500
 (.branch 498
 (.branch 497
 (.leaf (.branch (certNat% 337) (.branch (certNat% 338) (.leaf 235) (.branch (certNat% 339) (.leaf 236) (.leaf 237))) (.branch (certNat% 340) (.leaf 238) (.branch (certNat% 341) (.leaf 239) (.leaf 240)))))
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
 (.leaf (.leaf 241)))
 (.branch 515
 (.leaf (.leaf 242))
 (.leaf (.leaf 243))))
 (.branch 518
 (.branch 517
 (.leaf (.leaf 244))
 (.leaf (.leaf 245)))
 (.branch 519
 (.leaf (.leaf 246))
 (.leaf (.leaf 0)))))
 (.branch 524
 (.branch 522
 (.branch 521
 (.leaf (.leaf 247))
 (.leaf (.leaf 248)))
 (.branch 523
 (.leaf (.leaf 249))
 (.leaf (.leaf 0))))
 (.branch 526
 (.branch 525
 (.leaf (.leaf 250))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 536
 (.branch 532
 (.branch 530
 (.branch 529
 (.leaf (.leaf 251))
 (.leaf (.leaf 0)))
 (.branch 531
 (.leaf (.leaf 252))
 (.leaf (.leaf 0))))
 (.branch 534
 (.branch 533
 (.leaf (.leaf 253))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0))))
 (.branch 560
 (.branch 552
 (.branch 548
 (.branch 546
 (.branch 545
 (.leaf (.leaf 254))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 550
 (.branch 549
 (.leaf (.leaf 255))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 556
 (.branch 554
 (.branch 553
 (.leaf (.leaf 256))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 568
 (.branch 564
 (.branch 562
 (.branch 561
 (.leaf (.leaf 257))
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
 (.leaf (.leaf 258))
 (.leaf (.leaf 259)))
 (.branch 579
 (.leaf (.leaf 260))
 (.leaf (.branch (certNat% 342) (.leaf 261) (.leaf 262)))))
 (.branch 582
 (.branch 581
 (.leaf (.leaf 263))
 (.leaf (.branch (certNat% 343) (.leaf 264) (.leaf 265))))
 (.branch 583
 (.leaf (.branch (certNat% 344) (.leaf 266) (.leaf 267)))
 (.leaf (.leaf 0)))))
 (.branch 588
 (.branch 586
 (.branch 585
 (.leaf (.leaf 268))
 (.leaf (.branch (certNat% 345) (.leaf 269) (.leaf 270))))
 (.branch 587
 (.leaf (.branch (certNat% 346) (.leaf 271) (.leaf 272)))
 (.leaf (.leaf 0))))
 (.branch 590
 (.branch 589
 (.leaf (.branch (certNat% 347) (.leaf 273) (.leaf 274)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 600
 (.branch 596
 (.branch 594
 (.branch 593
 (.leaf (.leaf 275))
 (.leaf (.leaf 0)))
 (.branch 595
 (.leaf (.branch (certNat% 348) (.leaf 276) (.leaf 277)))
 (.leaf (.leaf 0))))
 (.branch 598
 (.branch 597
 (.leaf (.branch (certNat% 349) (.leaf 278) (.leaf 279)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0))))
 (.branch 624
 (.branch 616
 (.branch 612
 (.branch 610
 (.branch 609
 (.leaf (.leaf 280))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 614
 (.branch 613
 (.leaf (.branch (certNat% 350) (.leaf 281) (.leaf 282)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 620
 (.branch 618
 (.branch 617
 (.leaf (.branch (certNat% 351) (.leaf 283) (.leaf 284)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 632
 (.branch 628
 (.branch 626
 (.branch 625
 (.leaf (.branch (certNat% 352) (.leaf 285) (.leaf 286)))
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
 (.leaf (.leaf 287))
 (.leaf (.leaf 288)))
 (.branch 643
 (.leaf (.leaf 289))
 (.leaf (.branch (certNat% 353) (.leaf 290) (.leaf 291)))))
 (.branch 646
 (.branch 645
 (.leaf (.leaf 292))
 (.leaf (.branch (certNat% 354) (.leaf 293) (.leaf 294))))
 (.branch 647
 (.leaf (.branch (certNat% 355) (.leaf 295) (.leaf 296)))
 (.leaf (.leaf 0)))))
 (.branch 652
 (.branch 650
 (.branch 649
 (.leaf (.leaf 297))
 (.leaf (.branch (certNat% 356) (.leaf 298) (.leaf 299))))
 (.branch 651
 (.leaf (.branch (certNat% 357) (.leaf 300) (.leaf 301)))
 (.leaf (.leaf 0))))
 (.branch 654
 (.branch 653
 (.leaf (.branch (certNat% 358) (.leaf 302) (.leaf 303)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 664
 (.branch 660
 (.branch 658
 (.branch 657
 (.leaf (.leaf 304))
 (.leaf (.leaf 0)))
 (.branch 659
 (.leaf (.branch (certNat% 359) (.leaf 305) (.leaf 306)))
 (.leaf (.leaf 0))))
 (.branch 662
 (.branch 661
 (.leaf (.branch (certNat% 360) (.leaf 307) (.leaf 308)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0))))
 (.branch 688
 (.branch 680
 (.branch 676
 (.branch 674
 (.branch 673
 (.leaf (.leaf 309))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 678
 (.branch 677
 (.leaf (.branch (certNat% 361) (.leaf 310) (.leaf 311)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 684
 (.branch 682
 (.branch 681
 (.leaf (.branch (certNat% 362) (.leaf 312) (.leaf 313)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 696
 (.branch 692
 (.branch 690
 (.branch 689
 (.leaf (.branch (certNat% 363) (.leaf 314) (.leaf 315)))
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
 (.leaf (.leaf 316))
 (.leaf (.branch (certNat% 364) (.leaf 317) (.branch (certNat% 365) (.leaf 318) (.leaf 319)))))
 (.branch 707
 (.leaf (.branch (certNat% 366) (.leaf 320) (.branch (certNat% 367) (.leaf 321) (.leaf 322))))
 (.leaf (.branch (certNat% 368) (.branch (certNat% 369) (.leaf 323) (.branch (certNat% 370) (.leaf 324) (.leaf 325))) (.branch (certNat% 371) (.leaf 326) (.branch (certNat% 372) (.leaf 327) (.leaf 328)))))))
 (.branch 710
 (.branch 709
 (.leaf (.branch (certNat% 373) (.leaf 329) (.branch (certNat% 374) (.leaf 330) (.leaf 331))))
 (.leaf (.branch (certNat% 375) (.branch (certNat% 376) (.leaf 332) (.branch (certNat% 377) (.leaf 333) (.leaf 334))) (.branch (certNat% 378) (.leaf 335) (.branch (certNat% 379) (.leaf 336) (.leaf 337))))))
 (.branch 711
 (.leaf (.branch (certNat% 380) (.branch (certNat% 381) (.leaf 338) (.branch (certNat% 382) (.leaf 339) (.leaf 340))) (.branch (certNat% 383) (.leaf 341) (.branch (certNat% 384) (.leaf 342) (.leaf 343)))))
 (.leaf (.leaf 0)))))
 (.branch 716
 (.branch 714
 (.branch 713
 (.leaf (.branch (certNat% 385) (.leaf 344) (.branch (certNat% 386) (.leaf 345) (.leaf 346))))
 (.leaf (.branch (certNat% 387) (.branch (certNat% 388) (.leaf 347) (.branch (certNat% 389) (.leaf 348) (.leaf 349))) (.branch (certNat% 390) (.leaf 350) (.branch (certNat% 391) (.leaf 351) (.leaf 352))))))
 (.branch 715
 (.leaf (.branch (certNat% 392) (.branch (certNat% 393) (.leaf 353) (.branch (certNat% 394) (.leaf 354) (.leaf 355))) (.branch (certNat% 395) (.leaf 356) (.branch (certNat% 396) (.leaf 357) (.leaf 358)))))
 (.leaf (.leaf 0))))
 (.branch 718
 (.branch 717
 (.leaf (.branch (certNat% 397) (.branch (certNat% 398) (.leaf 359) (.branch (certNat% 399) (.leaf 360) (.leaf 361))) (.branch (certNat% 400) (.leaf 362) (.branch (certNat% 401) (.leaf 363) (.leaf 364)))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 728
 (.branch 724
 (.branch 722
 (.branch 721
 (.leaf (.branch (certNat% 402) (.leaf 365) (.branch (certNat% 403) (.leaf 366) (.leaf 367))))
 (.leaf (.leaf 0)))
 (.branch 723
 (.leaf (.branch (certNat% 404) (.branch (certNat% 405) (.leaf 368) (.branch (certNat% 406) (.leaf 369) (.leaf 370))) (.branch (certNat% 407) (.leaf 371) (.branch (certNat% 408) (.leaf 372) (.leaf 373)))))
 (.leaf (.leaf 0))))
 (.branch 726
 (.branch 725
 (.leaf (.branch (certNat% 409) (.branch (certNat% 410) (.leaf 374) (.branch (certNat% 411) (.leaf 375) (.leaf 376))) (.branch (certNat% 412) (.leaf 377) (.branch (certNat% 413) (.leaf 378) (.leaf 379)))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0))))
 (.branch 752
 (.branch 744
 (.branch 740
 (.branch 738
 (.branch 737
 (.leaf (.branch (certNat% 414) (.leaf 380) (.branch (certNat% 415) (.leaf 381) (.leaf 382))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 742
 (.branch 741
 (.leaf (.branch (certNat% 416) (.branch (certNat% 417) (.leaf 383) (.branch (certNat% 418) (.leaf 384) (.leaf 385))) (.branch (certNat% 419) (.leaf 386) (.branch (certNat% 420) (.leaf 387) (.leaf 388)))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 748
 (.branch 746
 (.branch 745
 (.leaf (.branch (certNat% 421) (.branch (certNat% 422) (.leaf 389) (.branch (certNat% 423) (.leaf 390) (.leaf 391))) (.branch (certNat% 424) (.leaf 392) (.branch (certNat% 425) (.leaf 393) (.leaf 394)))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 760
 (.branch 756
 (.branch 754
 (.branch 753
 (.leaf (.branch (certNat% 426) (.branch (certNat% 427) (.leaf 395) (.branch (certNat% 428) (.leaf 396) (.leaf 397))) (.branch (certNat% 429) (.leaf 398) (.branch (certNat% 430) (.leaf 399) (.leaf 400)))))
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
 (.leaf (.leaf 401))
 (.leaf (.leaf 402)))
 (.branch 771
 (.leaf (.leaf 403))
 (.leaf (.branch (certNat% 431) (.leaf 404) (.leaf 405)))))
 (.branch 774
 (.branch 773
 (.leaf (.leaf 406))
 (.leaf (.branch (certNat% 432) (.leaf 407) (.leaf 408))))
 (.branch 775
 (.leaf (.branch (certNat% 433) (.leaf 409) (.leaf 410)))
 (.leaf (.leaf 0)))))
 (.branch 780
 (.branch 778
 (.branch 777
 (.leaf (.leaf 411))
 (.leaf (.branch (certNat% 434) (.leaf 412) (.leaf 413))))
 (.branch 779
 (.leaf (.branch (certNat% 435) (.leaf 414) (.leaf 415)))
 (.leaf (.leaf 0))))
 (.branch 782
 (.branch 781
 (.leaf (.branch (certNat% 436) (.leaf 416) (.leaf 417)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 792
 (.branch 788
 (.branch 786
 (.branch 785
 (.leaf (.leaf 418))
 (.leaf (.leaf 0)))
 (.branch 787
 (.leaf (.branch (certNat% 437) (.leaf 419) (.leaf 420)))
 (.leaf (.leaf 0))))
 (.branch 790
 (.branch 789
 (.leaf (.branch (certNat% 438) (.leaf 421) (.leaf 422)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0))))
 (.branch 816
 (.branch 808
 (.branch 804
 (.branch 802
 (.branch 801
 (.leaf (.leaf 423))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 806
 (.branch 805
 (.leaf (.branch (certNat% 439) (.leaf 424) (.leaf 425)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 812
 (.branch 810
 (.branch 809
 (.leaf (.branch (certNat% 440) (.leaf 426) (.leaf 427)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 824
 (.branch 820
 (.branch 818
 (.branch 817
 (.leaf (.branch (certNat% 441) (.leaf 428) (.leaf 429)))
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
 (.leaf (.leaf 430))
 (.leaf (.branch (certNat% 442) (.leaf 431) (.branch (certNat% 443) (.leaf 432) (.leaf 433)))))
 (.branch 835
 (.leaf (.branch (certNat% 444) (.leaf 434) (.branch (certNat% 445) (.leaf 435) (.leaf 436))))
 (.leaf (.branch (certNat% 446) (.branch (certNat% 447) (.leaf 437) (.branch (certNat% 448) (.leaf 438) (.leaf 439))) (.branch (certNat% 449) (.leaf 440) (.branch (certNat% 450) (.leaf 441) (.leaf 442)))))))
 (.branch 838
 (.branch 837
 (.leaf (.branch (certNat% 451) (.leaf 443) (.branch (certNat% 452) (.leaf 444) (.leaf 445))))
 (.leaf (.branch (certNat% 453) (.branch (certNat% 454) (.leaf 446) (.branch (certNat% 455) (.leaf 447) (.leaf 448))) (.branch (certNat% 456) (.leaf 449) (.branch (certNat% 457) (.leaf 450) (.leaf 451))))))
 (.branch 839
 (.leaf (.branch (certNat% 458) (.branch (certNat% 459) (.leaf 452) (.branch (certNat% 460) (.leaf 453) (.leaf 454))) (.branch (certNat% 461) (.leaf 455) (.branch (certNat% 462) (.leaf 456) (.leaf 457)))))
 (.leaf (.leaf 0)))))
 (.branch 844
 (.branch 842
 (.branch 841
 (.leaf (.branch (certNat% 463) (.leaf 458) (.branch (certNat% 464) (.leaf 459) (.leaf 460))))
 (.leaf (.branch (certNat% 465) (.branch (certNat% 466) (.leaf 461) (.branch (certNat% 467) (.leaf 462) (.leaf 463))) (.branch (certNat% 468) (.leaf 464) (.branch (certNat% 469) (.leaf 465) (.leaf 466))))))
 (.branch 843
 (.leaf (.branch (certNat% 470) (.branch (certNat% 471) (.leaf 467) (.branch (certNat% 472) (.leaf 468) (.leaf 469))) (.branch (certNat% 473) (.leaf 470) (.branch (certNat% 474) (.leaf 471) (.leaf 472)))))
 (.leaf (.leaf 0))))
 (.branch 846
 (.branch 845
 (.leaf (.branch (certNat% 475) (.branch (certNat% 476) (.leaf 473) (.branch (certNat% 477) (.leaf 474) (.leaf 475))) (.branch (certNat% 478) (.leaf 476) (.branch (certNat% 479) (.leaf 477) (.leaf 478)))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 856
 (.branch 852
 (.branch 850
 (.branch 849
 (.leaf (.branch (certNat% 480) (.leaf 479) (.branch (certNat% 481) (.leaf 480) (.leaf 481))))
 (.leaf (.leaf 0)))
 (.branch 851
 (.leaf (.branch (certNat% 482) (.branch (certNat% 483) (.leaf 482) (.branch (certNat% 484) (.leaf 483) (.leaf 484))) (.branch (certNat% 485) (.leaf 485) (.branch (certNat% 486) (.leaf 486) (.leaf 487)))))
 (.leaf (.leaf 0))))
 (.branch 854
 (.branch 853
 (.leaf (.branch (certNat% 487) (.branch (certNat% 488) (.leaf 488) (.branch (certNat% 489) (.leaf 489) (.leaf 490))) (.branch (certNat% 490) (.leaf 491) (.branch (certNat% 491) (.leaf 492) (.leaf 493)))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0))))
 (.branch 880
 (.branch 872
 (.branch 868
 (.branch 866
 (.branch 865
 (.leaf (.branch (certNat% 492) (.leaf 494) (.branch (certNat% 493) (.leaf 495) (.leaf 496))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 870
 (.branch 869
 (.leaf (.branch (certNat% 494) (.branch (certNat% 495) (.leaf 497) (.branch (certNat% 496) (.leaf 498) (.leaf 499))) (.branch (certNat% 497) (.leaf 500) (.branch (certNat% 498) (.leaf 501) (.leaf 502)))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 876
 (.branch 874
 (.branch 873
 (.leaf (.branch (certNat% 499) (.branch (certNat% 500) (.leaf 503) (.branch (certNat% 501) (.leaf 504) (.leaf 505))) (.branch (certNat% 502) (.leaf 506) (.branch (certNat% 503) (.leaf 507) (.leaf 508)))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 888
 (.branch 884
 (.branch 882
 (.branch 881
 (.leaf (.branch (certNat% 504) (.branch (certNat% 505) (.leaf 509) (.branch (certNat% 506) (.leaf 510) (.leaf 511))) (.branch (certNat% 507) (.leaf 512) (.branch (certNat% 508) (.leaf 513) (.leaf 514)))))
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
 (.leaf (.leaf 515))
 (.leaf (.branch (certNat% 509) (.leaf 516) (.branch (certNat% 510) (.leaf 517) (.leaf 518)))))
 (.branch 899
 (.leaf (.branch (certNat% 511) (.leaf 519) (.branch (certNat% 512) (.leaf 520) (.leaf 521))))
 (.leaf (.branch (certNat% 513) (.branch (certNat% 514) (.leaf 522) (.branch (certNat% 515) (.leaf 523) (.leaf 524))) (.branch (certNat% 516) (.leaf 525) (.branch (certNat% 517) (.leaf 526) (.leaf 527)))))))
 (.branch 902
 (.branch 901
 (.leaf (.branch (certNat% 518) (.leaf 528) (.branch (certNat% 519) (.leaf 529) (.leaf 530))))
 (.leaf (.branch (certNat% 520) (.branch (certNat% 521) (.leaf 531) (.branch (certNat% 522) (.leaf 532) (.leaf 533))) (.branch (certNat% 523) (.leaf 534) (.branch (certNat% 524) (.leaf 535) (.leaf 536))))))
 (.branch 903
 (.leaf (.branch (certNat% 525) (.branch (certNat% 526) (.leaf 537) (.branch (certNat% 527) (.leaf 538) (.leaf 539))) (.branch (certNat% 528) (.leaf 540) (.branch (certNat% 529) (.leaf 541) (.leaf 542)))))
 (.leaf (.leaf 0)))))
 (.branch 908
 (.branch 906
 (.branch 905
 (.leaf (.branch (certNat% 530) (.leaf 543) (.branch (certNat% 531) (.leaf 544) (.leaf 545))))
 (.leaf (.branch (certNat% 532) (.branch (certNat% 533) (.leaf 546) (.branch (certNat% 534) (.leaf 547) (.leaf 548))) (.branch (certNat% 535) (.leaf 549) (.branch (certNat% 536) (.leaf 550) (.leaf 551))))))
 (.branch 907
 (.leaf (.branch (certNat% 537) (.branch (certNat% 538) (.leaf 552) (.branch (certNat% 539) (.leaf 553) (.leaf 554))) (.branch (certNat% 540) (.leaf 555) (.branch (certNat% 541) (.leaf 556) (.leaf 557)))))
 (.leaf (.leaf 0))))
 (.branch 910
 (.branch 909
 (.leaf (.branch (certNat% 542) (.branch (certNat% 543) (.leaf 558) (.branch (certNat% 544) (.leaf 559) (.leaf 560))) (.branch (certNat% 545) (.leaf 561) (.branch (certNat% 546) (.leaf 562) (.leaf 563)))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))))
 (.branch 920
 (.branch 916
 (.branch 914
 (.branch 913
 (.leaf (.branch (certNat% 547) (.leaf 564) (.branch (certNat% 548) (.leaf 565) (.leaf 566))))
 (.leaf (.leaf 0)))
 (.branch 915
 (.leaf (.branch (certNat% 549) (.branch (certNat% 550) (.leaf 567) (.branch (certNat% 551) (.leaf 568) (.leaf 569))) (.branch (certNat% 552) (.leaf 570) (.branch (certNat% 553) (.leaf 571) (.leaf 572)))))
 (.leaf (.leaf 0))))
 (.branch 918
 (.branch 917
 (.leaf (.branch (certNat% 554) (.branch (certNat% 555) (.leaf 573) (.branch (certNat% 556) (.leaf 574) (.leaf 575))) (.branch (certNat% 557) (.leaf 576) (.branch (certNat% 558) (.leaf 577) (.leaf 578)))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.leaf (.leaf 0))))
 (.branch 944
 (.branch 936
 (.branch 932
 (.branch 930
 (.branch 929
 (.leaf (.branch (certNat% 559) (.leaf 579) (.branch (certNat% 560) (.leaf 580) (.leaf 581))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.branch 934
 (.branch 933
 (.leaf (.branch (certNat% 561) (.branch (certNat% 562) (.leaf 582) (.branch (certNat% 563) (.leaf 583) (.leaf 584))) (.branch (certNat% 564) (.leaf 585) (.branch (certNat% 565) (.leaf 586) (.leaf 587)))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 940
 (.branch 938
 (.branch 937
 (.leaf (.branch (certNat% 566) (.branch (certNat% 567) (.leaf 588) (.branch (certNat% 568) (.leaf 589) (.leaf 590))) (.branch (certNat% 569) (.leaf 591) (.branch (certNat% 570) (.leaf 592) (.leaf 593)))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 952
 (.branch 948
 (.branch 946
 (.branch 945
 (.leaf (.branch (certNat% 571) (.branch (certNat% 572) (.leaf 594) (.branch (certNat% 573) (.leaf 595) (.leaf 596))) (.branch (certNat% 574) (.leaf 597) (.branch (certNat% 575) (.leaf 598) (.leaf 599)))))
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
 (.leaf (.branch (certNat% 576) (.leaf 600) (.branch (certNat% 577) (.leaf 601) (.leaf 602))))
 (.leaf (.branch (certNat% 578) (.branch (certNat% 579) (.branch (certNat% 580) (.leaf 603) (.branch (certNat% 581) (.leaf 604) (.leaf 605))) (.branch (certNat% 582) (.leaf 606) (.branch (certNat% 583) (.leaf 607) (.leaf 608)))) (.branch (certNat% 584) (.branch (certNat% 585) (.leaf 609) (.branch (certNat% 586) (.leaf 610) (.leaf 611))) (.branch (certNat% 587) (.leaf 612) (.branch (certNat% 588) (.leaf 613) (.leaf 614)))))))
 (.branch 963
 (.leaf (.branch (certNat% 589) (.branch (certNat% 590) (.branch (certNat% 591) (.leaf 615) (.branch (certNat% 592) (.leaf 616) (.leaf 617))) (.branch (certNat% 593) (.leaf 618) (.branch (certNat% 594) (.leaf 619) (.leaf 620)))) (.branch (certNat% 595) (.branch (certNat% 596) (.leaf 621) (.branch (certNat% 597) (.leaf 622) (.leaf 623))) (.branch (certNat% 598) (.leaf 624) (.branch (certNat% 599) (.leaf 625) (.leaf 626))))))
 (.leaf (.leaf 0))))
 (.branch 966
 (.branch 965
 (.leaf (.branch (certNat% 600) (.branch (certNat% 601) (.branch (certNat% 602) (.leaf 627) (.branch (certNat% 603) (.leaf 628) (.leaf 629))) (.branch (certNat% 604) (.leaf 630) (.branch (certNat% 605) (.leaf 631) (.leaf 632)))) (.branch (certNat% 606) (.branch (certNat% 607) (.leaf 633) (.branch (certNat% 608) (.leaf 634) (.leaf 635))) (.branch (certNat% 609) (.leaf 636) (.branch (certNat% 610) (.leaf 637) (.leaf 638))))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 972
 (.branch 970
 (.branch 969
 (.leaf (.branch (certNat% 611) (.branch (certNat% 612) (.branch (certNat% 613) (.leaf 639) (.branch (certNat% 614) (.leaf 640) (.leaf 641))) (.branch (certNat% 615) (.leaf 642) (.branch (certNat% 616) (.leaf 643) (.leaf 644)))) (.branch (certNat% 617) (.branch (certNat% 618) (.leaf 645) (.branch (certNat% 619) (.leaf 646) (.leaf 647))) (.branch (certNat% 620) (.leaf 648) (.branch (certNat% 621) (.leaf 649) (.leaf 650))))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 984
 (.branch 980
 (.branch 978
 (.branch 977
 (.leaf (.branch (certNat% 622) (.branch (certNat% 623) (.branch (certNat% 624) (.leaf 651) (.branch (certNat% 625) (.leaf 652) (.leaf 653))) (.branch (certNat% 626) (.leaf 654) (.branch (certNat% 627) (.leaf 655) (.leaf 656)))) (.branch (certNat% 628) (.branch (certNat% 629) (.leaf 657) (.branch (certNat% 630) (.leaf 658) (.leaf 659))) (.branch (certNat% 631) (.leaf 660) (.branch (certNat% 632) (.leaf 661) (.leaf 662))))))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0)))
 (.leaf (.leaf 0))))
 (.branch 1008
 (.branch 1000
 (.branch 996
 (.branch 994
 (.branch 993
 (.leaf (.branch (certNat% 633) (.branch (certNat% 634) (.branch (certNat% 635) (.leaf 663) (.branch (certNat% 636) (.leaf 664) (.leaf 665))) (.branch (certNat% 637) (.leaf 666) (.branch (certNat% 638) (.leaf 667) (.leaf 668)))) (.branch (certNat% 639) (.branch (certNat% 640) (.leaf 669) (.branch (certNat% 641) (.leaf 670) (.leaf 671))) (.branch (certNat% 642) (.leaf 672) (.branch (certNat% 643) (.leaf 673) (.leaf 674))))))
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
def candidateMasks (i : Nat) := PackedRawNatGrowth.take 3150
  (PackedRawNatGrowth.drop (3150*(i%64)) (candidateMasksBlocks.get (i/64)))

def badMasksBlocks : Table Nat :=
(.branch 25
 (.branch 12
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
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf badMasksBlock0012)
 (.branch 14
 (.leaf badMasksBlock0013)
 (.leaf badMasksBlock0014)))
 (.branch 16
 (.leaf badMasksBlock0015)
 (.branch 17
 (.leaf badMasksBlock0016)
 (.leaf badMasksBlock0017))))
 (.branch 21
 (.branch 19
 (.leaf badMasksBlock0018)
 (.branch 20
 (.leaf badMasksBlock0019)
 (.leaf badMasksBlock0020)))
 (.branch 23
 (.branch 22
 (.leaf badMasksBlock0021)
 (.leaf badMasksBlock0022))
 (.branch 24
 (.leaf badMasksBlock0023)
 (.leaf badMasksBlock0024))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf badMasksBlock0025)
 (.branch 27
 (.leaf badMasksBlock0026)
 (.leaf badMasksBlock0027)))
 (.branch 29
 (.leaf badMasksBlock0028)
 (.branch 30
 (.leaf badMasksBlock0029)
 (.leaf badMasksBlock0030))))
 (.branch 34
 (.branch 32
 (.leaf badMasksBlock0031)
 (.branch 33
 (.leaf badMasksBlock0032)
 (.leaf badMasksBlock0033)))
 (.branch 35
 (.leaf badMasksBlock0034)
 (.branch 36
 (.leaf badMasksBlock0035)
 (.leaf badMasksBlock0036)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf badMasksBlock0037)
 (.branch 39
 (.leaf badMasksBlock0038)
 (.leaf badMasksBlock0039)))
 (.branch 41
 (.leaf badMasksBlock0040)
 (.branch 42
 (.leaf badMasksBlock0041)
 (.leaf badMasksBlock0042))))
 (.branch 46
 (.branch 44
 (.leaf badMasksBlock0043)
 (.branch 45
 (.leaf badMasksBlock0044)
 (.leaf badMasksBlock0045)))
 (.branch 48
 (.branch 47
 (.leaf badMasksBlock0046)
 (.leaf badMasksBlock0047))
 (.branch 49
 (.leaf badMasksBlock0048)
 (.leaf badMasksBlock0049)))))))
def badMasks (i : Nat) := PackedRawNatGrowth.take 3150
  (PackedRawNatGrowth.drop (3150*(i%64)) (badMasksBlocks.get (i/64)))

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
 (.branch 8
 (.branch 6
 (.leaf signatureMasksBlock0005)
 (.branch 7
 (.leaf signatureMasksBlock0006)
 (.leaf signatureMasksBlock0007)))
 (.branch 9
 (.leaf signatureMasksBlock0008)
 (.branch 10
 (.leaf signatureMasksBlock0009)
 (.leaf signatureMasksBlock0010)))))
def signatureMasks (i : Nat) := PackedRawNatGrowth.take 3150
  (PackedRawNatGrowth.drop (3150*(i%64)) (signatureMasksBlocks.get (i/64)))

def fastKind := rawKind
def candidateSupports := candidateRows
def kindSupports := kindRows
def wellFormedTest (i : Nat) : Bool := RawFacetEmbedding.wellFormedCheck (rawCells i)

def cellTest (i : Nat) := (listBounds 1024 (rawCells i).ridgeMasks && ((rawCells i).ridgeMasks.all (fun q => (candidateMasks q).testBit i) && (decide (rawKind i = (rawCells i).kind) && (decide ((rawCells i).vertices < 1024) && ((List.range 10).all (fun v => decide ((vertexMasks v).testBit i = (rawCells i).vertices.testBit v)) && (SignatureCompatibility.faces (rawCells i)).all (fun q => (SignatureCompatibility.profileMask (SignatureCompatibility.allMask 3150) signatureIndex signatureMasks (rawCells i) q).testBit i))))))
def ridgeTest (i : Nat) := decide (candidateMasks i = RawNatGrowthCheck.mask (candidateRows i)) &&
  (candidateRows i).all (fun c => hasNat (rawCells c).ridgeMasks i)
def kindTest (i : Nat) := decide (kindMasks i = RawNatGrowthCheck.mask (kindRows i)) &&
  (kindRows i).all (fun c => decide ((rawCells c).kind = i))
def badTest (i : Nat) := if badMasks i = 0 then true else
  decide (Nat.land (badMasks i) (SignatureCompatibility.cover (SignatureCompatibility.allMask 3150)
    vertexMasks signatureIndex signatureMasks (rawCells i)) = 0)

end Papers.RationalityTen.RootedCaches.RootedSixExtra01

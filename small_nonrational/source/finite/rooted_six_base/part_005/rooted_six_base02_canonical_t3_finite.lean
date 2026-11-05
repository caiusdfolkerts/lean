module
prelude
public import RootedSixBase02
public import RawKindedFacePlacement
public import RootedSixBase02OutsideData
public import RawOutsidePlacement

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase02.T3
open ConcreteGrowth
abbrev blockCount : Nat := 136
noncomputable def template : Cell := ⟨7, 63, [3, 5, 6, 10, 17, 20, 24, 34, 36, 40, 48], [7, 21, 27, 38, 42, 52, 56]⟩
noncomputable def root : Cell := FacetUniverses.RootedSixBase02.cells 0
noncomputable def records : Table (RawFacePlacement.Block × Nat) :=
(.branch 68
 (.branch 34
 (.branch 17
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf (⟨2, 4, 5517840, 5517840, 361626105360, 361626105360⟩, 339612710))
 (.leaf (⟨2, 4, 5517840, 5517840, 361609328160, 361626104160⟩, 348263594)))
 (.branch 3
 (.leaf (⟨2, 4, 5517840, 5517840, 361592550945, 361626104070⟩, 356914478))
 (.leaf (⟨2, 4, 5517840, 5517840, 361340892720, 361626081120⟩, 379721354))))
 (.branch 6
 (.branch 5
 (.leaf (⟨2, 4, 5517840, 5517840, 361324115505, 361626081030⟩, 388372238))
 (.leaf (⟨2, 4, 5517840, 5517840, 356760712770, 361625649270⟩, 411179114)))
 (.branch 7
 (.leaf (⟨2, 4, 5517840, 5517840, 352465745475, 361625618550⟩, 419829998))
 (.leaf (⟨2, 4, 5517840, 5517840, 288309671505, 361617786630⟩, 430053770)))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf (⟨2, 4, 5517840, 5517840, 283746268755, 361617754230⟩, 438704654))
 (.leaf (⟨2, 4, 5517840, 5517840, 215026792020, 361617201270⟩, 461511530)))
 (.branch 11
 (.leaf (⟨2, 4, 5517600, 5517600, 361626105360, 361626105360⟩, 337253390))
 (.leaf (⟨2, 4, 5517600, 5517600, 361609328160, 361626104160⟩, 345904274))))
 (.branch 14
 (.branch 13
 (.leaf (⟨2, 4, 5517600, 5517600, 361592550945, 361626104070⟩, 354555158))
 (.leaf (⟨2, 4, 5517600, 5517600, 361340892720, 361626081120⟩, 377362034)))
 (.branch 15
 (.leaf (⟨2, 4, 5517600, 5517600, 361324115505, 361626081030⟩, 386012918))
 (.branch 16
 (.leaf (⟨2, 4, 5517600, 5517600, 356760712770, 361625649270⟩, 408819794))
 (.leaf (⟨2, 4, 5517600, 5517600, 352465745475, 361625618550⟩, 417470678)))))))
 (.branch 25
 (.branch 21
 (.branch 19
 (.branch 18
 (.leaf (⟨2, 4, 5517600, 5517600, 288309671505, 361617786630⟩, 427694450))
 (.leaf (⟨2, 4, 5517600, 5517600, 283746268755, 361617754230⟩, 436345334)))
 (.branch 20
 (.leaf (⟨2, 4, 5517600, 5517600, 215026792020, 361617201270⟩, 459152210))
 (.leaf (⟨2, 4, 5517345, 5517570, 361626105360, 361626105360⟩, 341185646))))
 (.branch 23
 (.branch 22
 (.leaf (⟨2, 4, 5517345, 5517570, 361609328160, 361626104160⟩, 349836530))
 (.leaf (⟨2, 4, 5517345, 5517570, 361592550945, 361626104070⟩, 358487414)))
 (.branch 24
 (.leaf (⟨2, 4, 5517345, 5517570, 361340892720, 361626081120⟩, 381294290))
 (.leaf (⟨2, 4, 5517345, 5517570, 361324115505, 361626081030⟩, 389945174)))))
 (.branch 29
 (.branch 27
 (.branch 26
 (.leaf (⟨2, 4, 5517345, 5517570, 356760712770, 361625649270⟩, 412752050))
 (.leaf (⟨2, 4, 5517345, 5517570, 352465745475, 361625618550⟩, 421402934)))
 (.branch 28
 (.leaf (⟨2, 4, 5517345, 5517570, 288309671505, 361617786630⟩, 431626706))
 (.leaf (⟨2, 4, 5517345, 5517570, 283746268755, 361617754230⟩, 440277590))))
 (.branch 31
 (.branch 30
 (.leaf (⟨2, 4, 5517345, 5517570, 215026792020, 361617201270⟩, 463084466))
 (.leaf (⟨3, 4, 5517840, 5517840, 361742426640, 434925761040⟩, 6714476235551887436244850080)))
 (.branch 32
 (.leaf (⟨3, 4, 5517840, 5517840, 361473991440, 434925741840⟩, 7294769483539174871125464960))
 (.branch 33
 (.leaf (⟨3, 4, 5517840, 5517840, 283627709745, 434918463495⟩, 8223238680318834766934448768))
 (.leaf (⟨3, 4, 5517840, 5517840, 141893788995, 434917935495⟩, 8672965947508982528966925300))))))))
 (.branch 51
 (.branch 42
 (.branch 38
 (.branch 36
 (.branch 35
 (.leaf (⟨2, 4, 5513265, 5509890, 361626105360, 361626105360⟩, 339350610))
 (.leaf (⟨2, 4, 5513265, 5509890, 361609328160, 361626104160⟩, 348001494)))
 (.branch 37
 (.leaf (⟨2, 4, 5513265, 5509890, 361592550945, 361626104070⟩, 356652378))
 (.leaf (⟨2, 4, 5513265, 5509890, 361340892720, 361626081120⟩, 379459254))))
 (.branch 40
 (.branch 39
 (.leaf (⟨2, 4, 5513265, 5509890, 361324115505, 361626081030⟩, 388110138))
 (.leaf (⟨2, 4, 5513265, 5509890, 356760712770, 361625649270⟩, 410917014)))
 (.branch 41
 (.leaf (⟨2, 4, 5513265, 5509890, 352465745475, 361625618550⟩, 419567898))
 (.leaf (⟨2, 4, 5513265, 5509890, 288309671505, 361617786630⟩, 429791670)))))
 (.branch 46
 (.branch 44
 (.branch 43
 (.leaf (⟨2, 4, 5513265, 5509890, 283746268755, 361617754230⟩, 438442554))
 (.leaf (⟨2, 4, 5513265, 5509890, 215026792020, 361617201270⟩, 461249430)))
 (.branch 45
 (.leaf (⟨2, 4, 5448000, 5325600, 361626105360, 361626105360⟩, 339874858))
 (.leaf (⟨2, 4, 5448000, 5325600, 361609328160, 361626104160⟩, 348525742))))
 (.branch 48
 (.branch 47
 (.leaf (⟨2, 4, 5448000, 5325600, 361592550945, 361626104070⟩, 357176626))
 (.leaf (⟨2, 4, 5448000, 5325600, 361340892720, 361626081120⟩, 379983502)))
 (.branch 49
 (.leaf (⟨2, 4, 5448000, 5325600, 361324115505, 361626081030⟩, 388634386))
 (.branch 50
 (.leaf (⟨2, 4, 5448000, 5325600, 356760712770, 361625649270⟩, 411441262))
 (.leaf (⟨2, 4, 5448000, 5325600, 352465745475, 361625618550⟩, 420092146)))))))
 (.branch 59
 (.branch 55
 (.branch 53
 (.branch 52
 (.leaf (⟨2, 4, 5448000, 5325600, 288309671505, 361617786630⟩, 430315918))
 (.leaf (⟨2, 4, 5448000, 5325600, 283746268755, 361617754230⟩, 438966802)))
 (.branch 54
 (.leaf (⟨2, 4, 5448000, 5325600, 215026792020, 361617201270⟩, 461773678))
 (.leaf (⟨2, 4, 5443650, 5324850, 361626105360, 361626105360⟩, 342627412))))
 (.branch 57
 (.branch 56
 (.leaf (⟨2, 4, 5443650, 5324850, 361609328160, 361626104160⟩, 351278296))
 (.leaf (⟨2, 4, 5443650, 5324850, 361592550945, 361626104070⟩, 359929180)))
 (.branch 58
 (.leaf (⟨2, 4, 5443650, 5324850, 361340892720, 361626081120⟩, 382736056))
 (.leaf (⟨2, 4, 5443650, 5324850, 361324115505, 361626081030⟩, 391386940)))))
 (.branch 63
 (.branch 61
 (.branch 60
 (.leaf (⟨2, 4, 5443650, 5324850, 356760712770, 361625649270⟩, 414193816))
 (.leaf (⟨2, 4, 5443650, 5324850, 352465745475, 361625618550⟩, 422844700)))
 (.branch 62
 (.leaf (⟨2, 4, 5443650, 5324850, 288309671505, 361617786630⟩, 433068472))
 (.leaf (⟨2, 4, 5443650, 5324850, 283746268755, 361617754230⟩, 441719356))))
 (.branch 65
 (.branch 64
 (.leaf (⟨2, 4, 5443650, 5324850, 215026792020, 361617201270⟩, 464526232))
 (.leaf (⟨3, 4, 5444640, 5390640, 361742426640, 434925761040⟩, 6719312012618448113328461208)))
 (.branch 66
 (.leaf (⟨3, 4, 5444640, 5390640, 361473991440, 434925741840⟩, 7299605260605735548209076088))
 (.branch 67
 (.leaf (⟨3, 4, 5444640, 5390640, 283627709745, 434918463495⟩, 8228074457385395444018059896))
 (.leaf (⟨3, 4, 5444640, 5390640, 141893788995, 434917935495⟩, 8677801724575543206050536428)))))))))
 (.branch 102
 (.branch 85
 (.branch 76
 (.branch 72
 (.branch 70
 (.branch 69
 (.leaf (⟨2, 4, 5378115, 5309490, 361626105360, 361626105360⟩, 340792376))
 (.leaf (⟨2, 4, 5378115, 5309490, 361609328160, 361626104160⟩, 349443260)))
 (.branch 71
 (.leaf (⟨2, 4, 5378115, 5309490, 361592550945, 361626104070⟩, 358094144))
 (.leaf (⟨2, 4, 5378115, 5309490, 361340892720, 361626081120⟩, 380901020))))
 (.branch 74
 (.branch 73
 (.leaf (⟨2, 4, 5378115, 5309490, 361324115505, 361626081030⟩, 389551904))
 (.leaf (⟨2, 4, 5378115, 5309490, 356760712770, 361625649270⟩, 412358780)))
 (.branch 75
 (.leaf (⟨2, 4, 5378115, 5309490, 352465745475, 361625618550⟩, 421009664))
 (.leaf (⟨2, 4, 5378115, 5309490, 288309671505, 361617786630⟩, 431233436)))))
 (.branch 80
 (.branch 78
 (.branch 77
 (.leaf (⟨2, 4, 5378115, 5309490, 283746268755, 361617754230⟩, 439884320))
 (.leaf (⟨2, 4, 5378115, 5309490, 215026792020, 361617201270⟩, 462691196)))
 (.branch 79
 (.leaf (⟨4, 4, 5391120, 5448720, 350450238240, 508225069440⟩, 59549306562027262599296261088899699981024033947168921909758629157290976406777544842388869481460838462318575616))
 (.leaf (⟨4, 4, 5391120, 5448720, 208716321825, 508218741000⟩, 4284944124781867227054735923226809870493085700876059609151756168639171470757155733539394055185764159490798020205524))))
 (.branch 82
 (.branch 81
 (.leaf (⟨2, 4, 4399185, 1393410, 361626105360, 361626105360⟩, 342103164))
 (.leaf (⟨2, 4, 4399185, 1393410, 361609328160, 361626104160⟩, 350754048)))
 (.branch 83
 (.leaf (⟨2, 4, 4399185, 1393410, 361592550945, 361626104070⟩, 359404932))
 (.branch 84
 (.leaf (⟨2, 4, 4399185, 1393410, 361340892720, 361626081120⟩, 382211808))
 (.leaf (⟨2, 4, 4399185, 1393410, 361324115505, 361626081030⟩, 390862692)))))))
 (.branch 93
 (.branch 89
 (.branch 87
 (.branch 86
 (.leaf (⟨2, 4, 4399185, 1393410, 356760712770, 361625649270⟩, 413669568))
 (.leaf (⟨2, 4, 4399185, 1393410, 352465745475, 361625618550⟩, 422320452)))
 (.branch 88
 (.leaf (⟨2, 4, 4399185, 1393410, 288309671505, 361617786630⟩, 432544224))
 (.leaf (⟨2, 4, 4399185, 1393410, 283746268755, 361617754230⟩, 441195108))))
 (.branch 91
 (.branch 90
 (.leaf (⟨2, 4, 4399185, 1393410, 215026792020, 361617201270⟩, 464001984))
 (.leaf (⟨2, 4, 4395090, 1392690, 361626105360, 361626105360⟩, 344724613)))
 (.branch 92
 (.leaf (⟨2, 4, 4395090, 1392690, 361609328160, 361626104160⟩, 353375497))
 (.leaf (⟨2, 4, 4395090, 1392690, 361592550945, 361626104070⟩, 362026381)))))
 (.branch 97
 (.branch 95
 (.branch 94
 (.leaf (⟨2, 4, 4395090, 1392690, 361340892720, 361626081120⟩, 384833257))
 (.leaf (⟨2, 4, 4395090, 1392690, 361324115505, 361626081030⟩, 393484141)))
 (.branch 96
 (.leaf (⟨2, 4, 4395090, 1392690, 356760712770, 361625649270⟩, 416291017))
 (.leaf (⟨2, 4, 4395090, 1392690, 352465745475, 361625618550⟩, 424941901))))
 (.branch 99
 (.branch 98
 (.leaf (⟨2, 4, 4395090, 1392690, 288309671505, 361617786630⟩, 435165673))
 (.leaf (⟨2, 4, 4395090, 1392690, 283746268755, 361617754230⟩, 443816557)))
 (.branch 100
 (.leaf (⟨2, 4, 4395090, 1392690, 215026792020, 361617201270⟩, 466623433))
 (.branch 101
 (.leaf (⟨3, 4, 4392225, 2441475, 361742426640, 434925761040⟩, 6737446287306959554407634377))
 (.leaf (⟨3, 4, 4392225, 2441475, 361473991440, 434925741840⟩, 7317739535294246989288249257))))))))
 (.branch 119
 (.branch 110
 (.branch 106
 (.branch 104
 (.branch 103
 (.leaf (⟨3, 4, 4392225, 2441475, 283627709745, 434918463495⟩, 8246208732073906885097233065))
 (.leaf (⟨3, 4, 4392225, 2441475, 141893788995, 434917935495⟩, 8695935999264054647129709597)))
 (.branch 105
 (.leaf (⟨2, 4, 4329555, 1377330, 361626105360, 361626105360⟩, 337646612))
 (.leaf (⟨2, 4, 4329555, 1377330, 361609328160, 361626104160⟩, 346297496))))
 (.branch 108
 (.branch 107
 (.leaf (⟨2, 4, 4329555, 1377330, 361592550945, 361626104070⟩, 354948380))
 (.leaf (⟨2, 4, 4329555, 1377330, 361340892720, 361626081120⟩, 377755256)))
 (.branch 109
 (.leaf (⟨2, 4, 4329555, 1377330, 361324115505, 361626081030⟩, 386406140))
 (.leaf (⟨2, 4, 4329555, 1377330, 356760712770, 361625649270⟩, 409213016)))))
 (.branch 114
 (.branch 112
 (.branch 111
 (.leaf (⟨2, 4, 4329555, 1377330, 352465745475, 361625618550⟩, 417863900))
 (.leaf (⟨2, 4, 4329555, 1377330, 288309671505, 361617786630⟩, 428087672)))
 (.branch 113
 (.leaf (⟨2, 4, 4329555, 1377330, 283746268755, 361617754230⟩, 436738556))
 (.leaf (⟨2, 4, 4329555, 1377330, 215026792020, 361617201270⟩, 459545432))))
 (.branch 116
 (.branch 115
 (.leaf (⟨3, 4, 4326705, 2429955, 361742426640, 434925761040⟩, 6702387235619165255426512302))
 (.leaf (⟨3, 4, 4326705, 2429955, 361473991440, 434925741840⟩, 7282680483606452690307127182)))
 (.branch 117
 (.leaf (⟨3, 4, 4326705, 2429955, 283627709745, 434918463495⟩, 8211149680386112586116110990))
 (.branch 118
 (.leaf (⟨3, 4, 4326705, 2429955, 141893788995, 434917935495⟩, 8660876947576260348148587522))
 (.leaf (⟨2, 4, 3280980, 1070130, 361626105360, 361626105360⟩, 342365312)))))))
 (.branch 127
 (.branch 123
 (.branch 121
 (.branch 120
 (.leaf (⟨2, 4, 3280980, 1070130, 361609328160, 361626104160⟩, 351016196))
 (.leaf (⟨2, 4, 3280980, 1070130, 361592550945, 361626104070⟩, 359667080)))
 (.branch 122
 (.leaf (⟨2, 4, 3280980, 1070130, 361340892720, 361626081120⟩, 382473956))
 (.leaf (⟨2, 4, 3280980, 1070130, 361324115505, 361626081030⟩, 391124840))))
 (.branch 125
 (.branch 124
 (.leaf (⟨2, 4, 3280980, 1070130, 356760712770, 361625649270⟩, 413931716))
 (.leaf (⟨2, 4, 3280980, 1070130, 352465745475, 361625618550⟩, 422582600)))
 (.branch 126
 (.leaf (⟨2, 4, 3280980, 1070130, 288309671505, 361617786630⟩, 432806372))
 (.leaf (⟨2, 4, 3280980, 1070130, 283746268755, 361617754230⟩, 441457256)))))
 (.branch 131
 (.branch 129
 (.branch 128
 (.leaf (⟨2, 4, 3280980, 1070130, 215026792020, 361617201270⟩, 464264132))
 (.leaf (⟨3, 4, 3212610, 2183235, 361742426640, 434925761040⟩, 6732610731599920395545220540)))
 (.branch 130
 (.leaf (⟨3, 4, 3212610, 2183235, 361473991440, 434925741840⟩, 7312903979587207830425835420))
 (.leaf (⟨3, 4, 3212610, 2183235, 283627709745, 434918463495⟩, 8241373176366867726234819228))))
 (.branch 133
 (.branch 132
 (.leaf (⟨3, 4, 3212610, 2183235, 141893788995, 434917935495⟩, 8691100443557015488267295760))
 (.leaf (⟨3, 4, 2164035, 2164035, 361742426640, 434925761040⟩, 6714476235551887436244850080)))
 (.branch 134
 (.leaf (⟨3, 4, 2164035, 2164035, 361473991440, 434925741840⟩, 7294769483539174871125464960))
 (.branch 135
 (.leaf (⟨3, 4, 2164035, 2164035, 283627709745, 434918463495⟩, 8223238680318834766934448768))
 (.leaf (⟨3, 4, 2164035, 2164035, 141893788995, 434917935495⟩, 8672965947508982528966925300))))))))))
noncomputable def raw (i : Fin blockCount) : RawFacePlacement.Block := (records.get i.val).1
noncomputable def witness (i : Fin blockCount) (code : Nat) : Fin 8084 :=
  Fin.ofNat 8084 (Nat.land (Nat.shiftRight (records.get i.val).2 (16 * code)) 65535)
noncomputable def faceTable : Table Nat :=
(.branch 24579
 (.branch 10243
 (.branch 5154
 (.branch 3112
 (.branch 3082
 (.branch 3078
 (.branch 3077
 (.leaf 0)
 (.leaf 1))
 (.branch 3081
 (.leaf 2)
 (.leaf 3)))
 (.branch 3096
 (.branch 3092
 (.leaf 4)
 (.leaf 5))
 (.branch 3106
 (.leaf 6)
 (.leaf 7))))
 (.branch 5126
 (.branch 5123
 (.branch 3120
 (.leaf 8)
 (.leaf 9))
 (.branch 5125
 (.leaf 10)
 (.leaf 11)))
 (.branch 5130
 (.branch 5129
 (.leaf 12)
 (.leaf 13))
 (.branch 5140
 (.leaf 14)
 (.branch 5144
 (.leaf 15)
 (.leaf 16))))))
 (.branch 6164
 (.branch 6149
 (.branch 5168
 (.branch 5160
 (.leaf 17)
 (.leaf 18))
 (.branch 6147
 (.leaf 19)
 (.leaf 20)))
 (.branch 6153
 (.branch 6150
 (.leaf 21)
 (.leaf 22))
 (.branch 6154
 (.leaf 23)
 (.leaf 24))))
 (.branch 6192
 (.branch 6178
 (.branch 6168
 (.leaf 25)
 (.leaf 26))
 (.branch 6184
 (.leaf 27)
 (.leaf 28)))
 (.branch 7179
 (.branch 7175
 (.leaf 29)
 (.leaf 30))
 (.branch 7210
 (.leaf 31)
 (.branch 7224
 (.leaf 32)
 (.leaf 33)))))))
 (.branch 17442
 (.branch 10280
 (.branch 10250
 (.branch 10246
 (.branch 10245
 (.leaf 34)
 (.leaf 35))
 (.branch 10249
 (.leaf 36)
 (.leaf 37)))
 (.branch 10264
 (.branch 10260
 (.leaf 38)
 (.leaf 39))
 (.branch 10274
 (.leaf 40)
 (.leaf 41))))
 (.branch 17414
 (.branch 17411
 (.branch 10288
 (.leaf 42)
 (.leaf 43))
 (.branch 17413
 (.leaf 44)
 (.leaf 45)))
 (.branch 17418
 (.branch 17417
 (.leaf 46)
 (.leaf 47))
 (.branch 17428
 (.leaf 48)
 (.branch 17432
 (.leaf 49)
 (.leaf 50))))))
 (.branch 20500
 (.branch 20485
 (.branch 17456
 (.branch 17448
 (.leaf 51)
 (.leaf 52))
 (.branch 20483
 (.leaf 53)
 (.leaf 54)))
 (.branch 20489
 (.branch 20486
 (.leaf 55)
 (.leaf 56))
 (.branch 20490
 (.leaf 57)
 (.leaf 58))))
 (.branch 20528
 (.branch 20514
 (.branch 20504
 (.leaf 59)
 (.leaf 60))
 (.branch 20520
 (.leaf 61)
 (.leaf 62)))
 (.branch 21515
 (.branch 21511
 (.leaf 63)
 (.leaf 64))
 (.branch 21546
 (.leaf 65)
 (.branch 21560
 (.leaf 66)
 (.leaf 67))))))))
 (.branch 38954
 (.branch 34836
 (.branch 24616
 (.branch 24586
 (.branch 24582
 (.branch 24581
 (.leaf 68)
 (.leaf 69))
 (.branch 24585
 (.leaf 70)
 (.leaf 71)))
 (.branch 24600
 (.branch 24596
 (.leaf 72)
 (.leaf 73))
 (.branch 24610
 (.leaf 74)
 (.leaf 75))))
 (.branch 34819
 (.branch 27677
 (.branch 24624
 (.leaf 76)
 (.leaf 77))
 (.branch 27702
 (.leaf 78)
 (.leaf 79)))
 (.branch 34822
 (.branch 34821
 (.leaf 80)
 (.leaf 81))
 (.branch 34825
 (.leaf 82)
 (.branch 34826
 (.leaf 83)
 (.leaf 84))))))
 (.branch 36873
 (.branch 34864
 (.branch 34850
 (.branch 34840
 (.leaf 85)
 (.leaf 86))
 (.branch 34856
 (.leaf 87)
 (.leaf 88)))
 (.branch 36869
 (.branch 36867
 (.leaf 89)
 (.leaf 90))
 (.branch 36870
 (.leaf 91)
 (.leaf 92))))
 (.branch 36898
 (.branch 36884
 (.branch 36874
 (.leaf 93)
 (.leaf 94))
 (.branch 36888
 (.leaf 95)
 (.leaf 96)))
 (.branch 36912
 (.branch 36904
 (.leaf 97)
 (.leaf 98))
 (.branch 38919
 (.leaf 99)
 (.branch 38923
 (.leaf 100)
 (.leaf 101)))))))
 (.branch 49157
 (.branch 40984
 (.branch 40966
 (.branch 40963
 (.branch 38968
 (.leaf 102)
 (.leaf 103))
 (.branch 40965
 (.leaf 104)
 (.leaf 105)))
 (.branch 40970
 (.branch 40969
 (.leaf 106)
 (.leaf 107))
 (.branch 40980
 (.leaf 108)
 (.leaf 109))))
 (.branch 43015
 (.branch 41000
 (.branch 40994
 (.leaf 110)
 (.leaf 111))
 (.branch 41008
 (.leaf 112)
 (.leaf 113)))
 (.branch 43050
 (.branch 43019
 (.leaf 114)
 (.leaf 115))
 (.branch 43064
 (.leaf 116)
 (.branch 49155
 (.leaf 117)
 (.leaf 118))))))
 (.branch 49200
 (.branch 49172
 (.branch 49161
 (.branch 49158
 (.leaf 119)
 (.leaf 120))
 (.branch 49162
 (.leaf 121)
 (.leaf 122)))
 (.branch 49186
 (.branch 49176
 (.leaf 123)
 (.leaf 124))
 (.branch 49192
 (.leaf 125)
 (.leaf 126))))
 (.branch 53304
 (.branch 53259
 (.branch 53255
 (.leaf 127)
 (.leaf 128))
 (.branch 53290
 (.leaf 129)
 (.leaf 130)))
 (.branch 57355
 (.branch 57351
 (.leaf 131)
 (.leaf 132))
 (.branch 57386
 (.leaf 133)
 (.branch 57400
 (.leaf 134)
 (.leaf 135)))))))))
noncomputable def faceWitness (s r : Nat) : Fin blockCount :=
  Fin.ofNat blockCount (faceTable.get (s * 1024 + r))
noncomputable def validity (i : Nat) : Bool :=
  RawFaceNormalizers.blockValidCheck 6 (raw (Fin.ofNat blockCount i))
noncomputable def placement (b : Fin blockCount) (code : Nat) : Bool :=
  RawKindedFacePlacement.check 6 (raw b) template root FacetUniverses.RootedSixBase02.cells
    code 0 (witness b code)
noncomputable def test (i : Nat) : Bool :=
  let b := Fin.ofNat blockCount i
  FiniteChecks.checkRange (placement b)
    0 (RawFacePlacement.count (raw b).shared (raw b).shared)
noncomputable def symmetry (i : Nat) : Bool :=
  RawOutsidePlacement.blockCheck FacetUniverses.RootedSixBase02.Outside.vertexCode root.vertices
    (raw (Fin.ofNat blockCount i))
end Papers.RationalityTen.RootedCanonical.RootedSixBase02.T3

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase02.T3
theorem check_0000_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 0)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 0)) 0 2 (by decide +kernel)
theorem block_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 0)) 0 2 :=
  check_0000_0000
theorem check_0001_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 1)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 1)) 0 2 (by decide +kernel)
theorem block_0001 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 1)) 0 2 :=
  check_0001_0000
theorem check_0002_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 2)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 2)) 0 2 (by decide +kernel)
theorem block_0002 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 2)) 0 2 :=
  check_0002_0000
theorem check_0003_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 3)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 3)) 0 2 (by decide +kernel)
theorem block_0003 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 3)) 0 2 :=
  check_0003_0000
theorem check_0004_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 4)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 4)) 0 2 (by decide +kernel)
theorem block_0004 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 4)) 0 2 :=
  check_0004_0000
theorem check_0005_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 5)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 5)) 0 2 (by decide +kernel)
theorem block_0005 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 5)) 0 2 :=
  check_0005_0000
theorem check_0006_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 6)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 6)) 0 2 (by decide +kernel)
theorem block_0006 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 6)) 0 2 :=
  check_0006_0000
theorem check_0007_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 7)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 7)) 0 2 (by decide +kernel)
theorem block_0007 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 7)) 0 2 :=
  check_0007_0000
theorem check_0008_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 8)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 8)) 0 2 (by decide +kernel)
theorem block_0008 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 8)) 0 2 :=
  check_0008_0000
theorem check_0009_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 9)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 9)) 0 2 (by decide +kernel)
theorem block_0009 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 9)) 0 2 :=
  check_0009_0000
theorem check_0010_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 10)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 10)) 0 2 (by decide +kernel)
theorem block_0010 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 10)) 0 2 :=
  check_0010_0000
theorem check_0011_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 11)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 11)) 0 2 (by decide +kernel)
theorem block_0011 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 11)) 0 2 :=
  check_0011_0000
theorem check_0012_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 12)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 12)) 0 2 (by decide +kernel)
theorem block_0012 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 12)) 0 2 :=
  check_0012_0000
theorem check_0013_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 13)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 13)) 0 2 (by decide +kernel)
theorem block_0013 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 13)) 0 2 :=
  check_0013_0000
theorem check_0014_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 14)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 14)) 0 2 (by decide +kernel)
theorem block_0014 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 14)) 0 2 :=
  check_0014_0000
theorem check_0015_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 15)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 15)) 0 2 (by decide +kernel)
theorem block_0015 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 15)) 0 2 :=
  check_0015_0000
theorem check_0016_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 16)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 16)) 0 2 (by decide +kernel)
theorem block_0016 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 16)) 0 2 :=
  check_0016_0000
theorem check_0017_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 17)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 17)) 0 2 (by decide +kernel)
theorem block_0017 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 17)) 0 2 :=
  check_0017_0000
theorem check_0018_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 18)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 18)) 0 2 (by decide +kernel)
theorem block_0018 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 18)) 0 2 :=
  check_0018_0000
theorem check_0019_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 19)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 19)) 0 2 (by decide +kernel)
theorem block_0019 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 19)) 0 2 :=
  check_0019_0000
theorem check_0020_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 20)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 20)) 0 2 (by decide +kernel)
theorem block_0020 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 20)) 0 2 :=
  check_0020_0000
theorem check_0021_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 21)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 21)) 0 2 (by decide +kernel)
theorem block_0021 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 21)) 0 2 :=
  check_0021_0000
theorem check_0022_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 22)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 22)) 0 2 (by decide +kernel)
theorem block_0022 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 22)) 0 2 :=
  check_0022_0000
theorem check_0023_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 23)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 23)) 0 2 (by decide +kernel)
theorem block_0023 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 23)) 0 2 :=
  check_0023_0000
theorem check_0024_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 24)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 24)) 0 2 (by decide +kernel)
theorem block_0024 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 24)) 0 2 :=
  check_0024_0000
theorem check_0025_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 25)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 25)) 0 2 (by decide +kernel)
theorem block_0025 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 25)) 0 2 :=
  check_0025_0000
theorem check_0026_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 26)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 26)) 0 2 (by decide +kernel)
theorem block_0026 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 26)) 0 2 :=
  check_0026_0000
theorem check_0027_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 27)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 27)) 0 2 (by decide +kernel)
theorem block_0027 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 27)) 0 2 :=
  check_0027_0000
theorem check_0028_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 28)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 28)) 0 2 (by decide +kernel)
theorem block_0028 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 28)) 0 2 :=
  check_0028_0000
theorem check_0029_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 29)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 29)) 0 2 (by decide +kernel)
theorem block_0029 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 29)) 0 2 :=
  check_0029_0000
theorem check_0030_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 30)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 30)) 0 6 (by decide +kernel)
theorem block_0030 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 30)) 0 6 :=
  check_0030_0000
theorem check_0031_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 31)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 31)) 0 6 (by decide +kernel)
theorem block_0031 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 31)) 0 6 :=
  check_0031_0000
theorem check_0032_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 32)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 32)) 0 6 (by decide +kernel)
theorem block_0032 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 32)) 0 6 :=
  check_0032_0000
theorem check_0033_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 33)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 33)) 0 6 (by decide +kernel)
theorem block_0033 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 33)) 0 6 :=
  check_0033_0000
theorem check_0034_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 34)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 34)) 0 2 (by decide +kernel)
theorem block_0034 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 34)) 0 2 :=
  check_0034_0000
theorem check_0035_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 35)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 35)) 0 2 (by decide +kernel)
theorem block_0035 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 35)) 0 2 :=
  check_0035_0000
theorem check_0036_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 36)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 36)) 0 2 (by decide +kernel)
theorem block_0036 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 36)) 0 2 :=
  check_0036_0000
theorem check_0037_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 37)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 37)) 0 2 (by decide +kernel)
theorem block_0037 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 37)) 0 2 :=
  check_0037_0000
theorem check_0038_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 38)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 38)) 0 2 (by decide +kernel)
theorem block_0038 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 38)) 0 2 :=
  check_0038_0000
theorem check_0039_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 39)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 39)) 0 2 (by decide +kernel)
theorem block_0039 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 39)) 0 2 :=
  check_0039_0000
theorem check_0040_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 40)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 40)) 0 2 (by decide +kernel)
theorem block_0040 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 40)) 0 2 :=
  check_0040_0000
theorem check_0041_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 41)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 41)) 0 2 (by decide +kernel)
theorem block_0041 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 41)) 0 2 :=
  check_0041_0000
theorem check_0042_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 42)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 42)) 0 2 (by decide +kernel)
theorem block_0042 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 42)) 0 2 :=
  check_0042_0000
theorem check_0043_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 43)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 43)) 0 2 (by decide +kernel)
theorem block_0043 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 43)) 0 2 :=
  check_0043_0000
theorem check_0044_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 44)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 44)) 0 2 (by decide +kernel)
theorem block_0044 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 44)) 0 2 :=
  check_0044_0000
theorem check_0045_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 45)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 45)) 0 2 (by decide +kernel)
theorem block_0045 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 45)) 0 2 :=
  check_0045_0000
theorem check_0046_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 46)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 46)) 0 2 (by decide +kernel)
theorem block_0046 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 46)) 0 2 :=
  check_0046_0000
theorem check_0047_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 47)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 47)) 0 2 (by decide +kernel)
theorem block_0047 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 47)) 0 2 :=
  check_0047_0000
theorem check_0048_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 48)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 48)) 0 2 (by decide +kernel)
theorem block_0048 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 48)) 0 2 :=
  check_0048_0000
theorem check_0049_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 49)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 49)) 0 2 (by decide +kernel)
theorem block_0049 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 49)) 0 2 :=
  check_0049_0000
theorem check_0050_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 50)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 50)) 0 2 (by decide +kernel)
theorem block_0050 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 50)) 0 2 :=
  check_0050_0000
theorem check_0051_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 51)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 51)) 0 2 (by decide +kernel)
theorem block_0051 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 51)) 0 2 :=
  check_0051_0000
theorem check_0052_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 52)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 52)) 0 2 (by decide +kernel)
theorem block_0052 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 52)) 0 2 :=
  check_0052_0000
theorem check_0053_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 53)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 53)) 0 2 (by decide +kernel)
theorem block_0053 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 53)) 0 2 :=
  check_0053_0000
theorem check_0054_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 54)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 54)) 0 2 (by decide +kernel)
theorem block_0054 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 54)) 0 2 :=
  check_0054_0000
theorem check_0055_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 55)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 55)) 0 2 (by decide +kernel)
theorem block_0055 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 55)) 0 2 :=
  check_0055_0000
theorem check_0056_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 56)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 56)) 0 2 (by decide +kernel)
theorem block_0056 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 56)) 0 2 :=
  check_0056_0000
theorem check_0057_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 57)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 57)) 0 2 (by decide +kernel)
theorem block_0057 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 57)) 0 2 :=
  check_0057_0000
theorem check_0058_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 58)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 58)) 0 2 (by decide +kernel)
theorem block_0058 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 58)) 0 2 :=
  check_0058_0000
theorem check_0059_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 59)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 59)) 0 2 (by decide +kernel)
theorem block_0059 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 59)) 0 2 :=
  check_0059_0000
theorem check_0060_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 60)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 60)) 0 2 (by decide +kernel)
theorem block_0060 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 60)) 0 2 :=
  check_0060_0000
theorem check_0061_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 61)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 61)) 0 2 (by decide +kernel)
theorem block_0061 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 61)) 0 2 :=
  check_0061_0000
theorem check_0062_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 62)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 62)) 0 2 (by decide +kernel)
theorem block_0062 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 62)) 0 2 :=
  check_0062_0000
theorem check_0063_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 63)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 63)) 0 2 (by decide +kernel)
theorem block_0063 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 63)) 0 2 :=
  check_0063_0000
end Papers.RationalityTen.RootedCanonical.RootedSixBase02.T3

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase02.T3
theorem check_0064_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 64)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 64)) 0 6 (by decide +kernel)
theorem block_0064 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 64)) 0 6 :=
  check_0064_0000
theorem check_0065_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 65)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 65)) 0 6 (by decide +kernel)
theorem block_0065 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 65)) 0 6 :=
  check_0065_0000
theorem check_0066_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 66)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 66)) 0 6 (by decide +kernel)
theorem block_0066 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 66)) 0 6 :=
  check_0066_0000
theorem check_0067_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 67)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 67)) 0 6 (by decide +kernel)
theorem block_0067 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 67)) 0 6 :=
  check_0067_0000
theorem check_0068_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 68)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 68)) 0 2 (by decide +kernel)
theorem block_0068 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 68)) 0 2 :=
  check_0068_0000
theorem check_0069_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 69)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 69)) 0 2 (by decide +kernel)
theorem block_0069 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 69)) 0 2 :=
  check_0069_0000
theorem check_0070_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 70)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 70)) 0 2 (by decide +kernel)
theorem block_0070 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 70)) 0 2 :=
  check_0070_0000
theorem check_0071_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 71)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 71)) 0 2 (by decide +kernel)
theorem block_0071 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 71)) 0 2 :=
  check_0071_0000
theorem check_0072_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 72)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 72)) 0 2 (by decide +kernel)
theorem block_0072 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 72)) 0 2 :=
  check_0072_0000
theorem check_0073_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 73)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 73)) 0 2 (by decide +kernel)
theorem block_0073 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 73)) 0 2 :=
  check_0073_0000
theorem check_0074_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 74)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 74)) 0 2 (by decide +kernel)
theorem block_0074 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 74)) 0 2 :=
  check_0074_0000
theorem check_0075_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 75)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 75)) 0 2 (by decide +kernel)
theorem block_0075 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 75)) 0 2 :=
  check_0075_0000
theorem check_0076_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 76)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 76)) 0 2 (by decide +kernel)
theorem block_0076 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 76)) 0 2 :=
  check_0076_0000
theorem check_0077_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 77)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 77)) 0 2 (by decide +kernel)
theorem block_0077 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 77)) 0 2 :=
  check_0077_0000
theorem check_0078_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 78)) 0 8 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 78)) 0 8 (by decide +kernel)
theorem check_0078_0008 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 78)) 8 16 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 78)) 8 8 (by decide +kernel)
theorem check_0078_0016 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 78)) 16 24 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 78)) 16 8 (by decide +kernel)
theorem block_0078 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 78)) 0 24 :=
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 78)) 0 8 24
  check_0078_0000
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 78)) 8 16 24
  check_0078_0008
  check_0078_0016))
theorem check_0079_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 79)) 0 8 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 79)) 0 8 (by decide +kernel)
theorem check_0079_0008 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 79)) 8 16 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 79)) 8 8 (by decide +kernel)
theorem check_0079_0016 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 79)) 16 24 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 79)) 16 8 (by decide +kernel)
theorem block_0079 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 79)) 0 24 :=
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 79)) 0 8 24
  check_0079_0000
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 79)) 8 16 24
  check_0079_0008
  check_0079_0016))
theorem check_0080_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 80)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 80)) 0 2 (by decide +kernel)
theorem block_0080 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 80)) 0 2 :=
  check_0080_0000
theorem check_0081_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 81)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 81)) 0 2 (by decide +kernel)
theorem block_0081 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 81)) 0 2 :=
  check_0081_0000
theorem check_0082_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 82)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 82)) 0 2 (by decide +kernel)
theorem block_0082 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 82)) 0 2 :=
  check_0082_0000
theorem check_0083_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 83)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 83)) 0 2 (by decide +kernel)
theorem block_0083 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 83)) 0 2 :=
  check_0083_0000
theorem check_0084_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 84)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 84)) 0 2 (by decide +kernel)
theorem block_0084 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 84)) 0 2 :=
  check_0084_0000
theorem check_0085_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 85)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 85)) 0 2 (by decide +kernel)
theorem block_0085 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 85)) 0 2 :=
  check_0085_0000
theorem check_0086_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 86)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 86)) 0 2 (by decide +kernel)
theorem block_0086 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 86)) 0 2 :=
  check_0086_0000
theorem check_0087_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 87)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 87)) 0 2 (by decide +kernel)
theorem block_0087 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 87)) 0 2 :=
  check_0087_0000
theorem check_0088_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 88)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 88)) 0 2 (by decide +kernel)
theorem block_0088 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 88)) 0 2 :=
  check_0088_0000
theorem check_0089_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 89)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 89)) 0 2 (by decide +kernel)
theorem block_0089 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 89)) 0 2 :=
  check_0089_0000
theorem check_0090_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 90)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 90)) 0 2 (by decide +kernel)
theorem block_0090 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 90)) 0 2 :=
  check_0090_0000
theorem check_0091_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 91)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 91)) 0 2 (by decide +kernel)
theorem block_0091 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 91)) 0 2 :=
  check_0091_0000
theorem check_0092_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 92)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 92)) 0 2 (by decide +kernel)
theorem block_0092 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 92)) 0 2 :=
  check_0092_0000
theorem check_0093_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 93)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 93)) 0 2 (by decide +kernel)
theorem block_0093 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 93)) 0 2 :=
  check_0093_0000
theorem check_0094_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 94)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 94)) 0 2 (by decide +kernel)
theorem block_0094 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 94)) 0 2 :=
  check_0094_0000
theorem check_0095_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 95)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 95)) 0 2 (by decide +kernel)
theorem block_0095 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 95)) 0 2 :=
  check_0095_0000
theorem check_0096_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 96)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 96)) 0 2 (by decide +kernel)
theorem block_0096 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 96)) 0 2 :=
  check_0096_0000
theorem check_0097_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 97)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 97)) 0 2 (by decide +kernel)
theorem block_0097 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 97)) 0 2 :=
  check_0097_0000
theorem check_0098_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 98)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 98)) 0 2 (by decide +kernel)
theorem block_0098 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 98)) 0 2 :=
  check_0098_0000
theorem check_0099_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 99)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 99)) 0 2 (by decide +kernel)
theorem block_0099 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 99)) 0 2 :=
  check_0099_0000
theorem check_0100_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 100)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 100)) 0 6 (by decide +kernel)
theorem block_0100 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 100)) 0 6 :=
  check_0100_0000
theorem check_0101_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 101)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 101)) 0 6 (by decide +kernel)
theorem block_0101 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 101)) 0 6 :=
  check_0101_0000
theorem check_0102_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 102)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 102)) 0 6 (by decide +kernel)
theorem block_0102 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 102)) 0 6 :=
  check_0102_0000
theorem check_0103_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 103)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 103)) 0 6 (by decide +kernel)
theorem block_0103 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 103)) 0 6 :=
  check_0103_0000
theorem check_0104_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 104)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 104)) 0 2 (by decide +kernel)
theorem block_0104 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 104)) 0 2 :=
  check_0104_0000
theorem check_0105_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 105)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 105)) 0 2 (by decide +kernel)
theorem block_0105 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 105)) 0 2 :=
  check_0105_0000
theorem check_0106_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 106)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 106)) 0 2 (by decide +kernel)
theorem block_0106 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 106)) 0 2 :=
  check_0106_0000
theorem check_0107_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 107)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 107)) 0 2 (by decide +kernel)
theorem block_0107 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 107)) 0 2 :=
  check_0107_0000
theorem check_0108_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 108)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 108)) 0 2 (by decide +kernel)
theorem block_0108 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 108)) 0 2 :=
  check_0108_0000
theorem check_0109_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 109)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 109)) 0 2 (by decide +kernel)
theorem block_0109 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 109)) 0 2 :=
  check_0109_0000
theorem check_0110_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 110)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 110)) 0 2 (by decide +kernel)
theorem block_0110 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 110)) 0 2 :=
  check_0110_0000
theorem check_0111_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 111)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 111)) 0 2 (by decide +kernel)
theorem block_0111 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 111)) 0 2 :=
  check_0111_0000
theorem check_0112_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 112)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 112)) 0 2 (by decide +kernel)
theorem block_0112 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 112)) 0 2 :=
  check_0112_0000
theorem check_0113_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 113)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 113)) 0 2 (by decide +kernel)
theorem block_0113 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 113)) 0 2 :=
  check_0113_0000
theorem check_0114_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 114)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 114)) 0 6 (by decide +kernel)
theorem block_0114 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 114)) 0 6 :=
  check_0114_0000
theorem check_0115_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 115)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 115)) 0 6 (by decide +kernel)
theorem block_0115 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 115)) 0 6 :=
  check_0115_0000
theorem check_0116_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 116)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 116)) 0 6 (by decide +kernel)
theorem block_0116 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 116)) 0 6 :=
  check_0116_0000
theorem check_0117_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 117)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 117)) 0 6 (by decide +kernel)
theorem block_0117 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 117)) 0 6 :=
  check_0117_0000
theorem check_0118_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 118)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 118)) 0 2 (by decide +kernel)
theorem block_0118 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 118)) 0 2 :=
  check_0118_0000
theorem check_0119_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 119)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 119)) 0 2 (by decide +kernel)
theorem block_0119 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 119)) 0 2 :=
  check_0119_0000
theorem check_0120_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 120)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 120)) 0 2 (by decide +kernel)
theorem block_0120 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 120)) 0 2 :=
  check_0120_0000
theorem check_0121_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 121)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 121)) 0 2 (by decide +kernel)
theorem block_0121 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 121)) 0 2 :=
  check_0121_0000
theorem check_0122_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 122)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 122)) 0 2 (by decide +kernel)
theorem block_0122 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 122)) 0 2 :=
  check_0122_0000
theorem check_0123_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 123)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 123)) 0 2 (by decide +kernel)
theorem block_0123 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 123)) 0 2 :=
  check_0123_0000
theorem check_0124_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 124)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 124)) 0 2 (by decide +kernel)
theorem block_0124 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 124)) 0 2 :=
  check_0124_0000
theorem check_0125_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 125)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 125)) 0 2 (by decide +kernel)
theorem block_0125 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 125)) 0 2 :=
  check_0125_0000
theorem check_0126_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 126)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 126)) 0 2 (by decide +kernel)
theorem block_0126 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 126)) 0 2 :=
  check_0126_0000
theorem check_0127_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 127)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 127)) 0 2 (by decide +kernel)
theorem block_0127 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 127)) 0 2 :=
  check_0127_0000
end Papers.RationalityTen.RootedCanonical.RootedSixBase02.T3

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase02.T3
theorem check_0128_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 128)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 128)) 0 6 (by decide +kernel)
theorem block_0128 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 128)) 0 6 :=
  check_0128_0000
theorem check_0129_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 129)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 129)) 0 6 (by decide +kernel)
theorem block_0129 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 129)) 0 6 :=
  check_0129_0000
theorem check_0130_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 130)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 130)) 0 6 (by decide +kernel)
theorem block_0130 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 130)) 0 6 :=
  check_0130_0000
theorem check_0131_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 131)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 131)) 0 6 (by decide +kernel)
theorem block_0131 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 131)) 0 6 :=
  check_0131_0000
theorem check_0132_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 132)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 132)) 0 6 (by decide +kernel)
theorem block_0132 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 132)) 0 6 :=
  check_0132_0000
theorem check_0133_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 133)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 133)) 0 6 (by decide +kernel)
theorem block_0133 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 133)) 0 6 :=
  check_0133_0000
theorem check_0134_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 134)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 134)) 0 6 (by decide +kernel)
theorem block_0134 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 134)) 0 6 :=
  check_0134_0000
theorem check_0135_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 135)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 135)) 0 6 (by decide +kernel)
theorem block_0135 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 135)) 0 6 :=
  check_0135_0000
end Papers.RationalityTen.RootedCanonical.RootedSixBase02.T3

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase02.T3
theorem metadata_validity_0000 : FiniteChecks.Interval validity 0 16 :=
  FiniteChecks.interval_of_check validity 0 16 (by decide +kernel)
theorem metadata_validity_0016 : FiniteChecks.Interval validity 16 32 :=
  FiniteChecks.interval_of_check validity 16 16 (by decide +kernel)
theorem metadata_validity_0032 : FiniteChecks.Interval validity 32 48 :=
  FiniteChecks.interval_of_check validity 32 16 (by decide +kernel)
theorem metadata_validity_0048 : FiniteChecks.Interval validity 48 64 :=
  FiniteChecks.interval_of_check validity 48 16 (by decide +kernel)
theorem metadata_validity_0064 : FiniteChecks.Interval validity 64 80 :=
  FiniteChecks.interval_of_check validity 64 16 (by decide +kernel)
theorem metadata_validity_0080 : FiniteChecks.Interval validity 80 96 :=
  FiniteChecks.interval_of_check validity 80 16 (by decide +kernel)
theorem metadata_validity_0096 : FiniteChecks.Interval validity 96 112 :=
  FiniteChecks.interval_of_check validity 96 16 (by decide +kernel)
theorem metadata_validity_0112 : FiniteChecks.Interval validity 112 128 :=
  FiniteChecks.interval_of_check validity 112 16 (by decide +kernel)
theorem metadata_validity_0128 : FiniteChecks.Interval validity 128 136 :=
  FiniteChecks.interval_of_check validity 128 8 (by decide +kernel)
theorem metadata_validity : FiniteChecks.Interval validity 0 blockCount :=
  (FiniteChecks.interval_append (validity) 0 64 136
  (FiniteChecks.interval_append (validity) 0 32 64
  (FiniteChecks.interval_append (validity) 0 16 32
  metadata_validity_0000
  metadata_validity_0016)
  (FiniteChecks.interval_append (validity) 32 48 64
  metadata_validity_0032
  metadata_validity_0048))
  (FiniteChecks.interval_append (validity) 64 96 136
  (FiniteChecks.interval_append (validity) 64 80 96
  metadata_validity_0064
  metadata_validity_0080)
  (FiniteChecks.interval_append (validity) 96 112 136
  metadata_validity_0096
  (FiniteChecks.interval_append (validity) 112 128 136
  metadata_validity_0112
  metadata_validity_0128))))
theorem metadata_symmetry_0000 : FiniteChecks.Interval symmetry 0 16 :=
  FiniteChecks.interval_of_check symmetry 0 16 (by decide +kernel)
theorem metadata_symmetry_0016 : FiniteChecks.Interval symmetry 16 32 :=
  FiniteChecks.interval_of_check symmetry 16 16 (by decide +kernel)
theorem metadata_symmetry_0032 : FiniteChecks.Interval symmetry 32 48 :=
  FiniteChecks.interval_of_check symmetry 32 16 (by decide +kernel)
theorem metadata_symmetry_0048 : FiniteChecks.Interval symmetry 48 64 :=
  FiniteChecks.interval_of_check symmetry 48 16 (by decide +kernel)
theorem metadata_symmetry_0064 : FiniteChecks.Interval symmetry 64 80 :=
  FiniteChecks.interval_of_check symmetry 64 16 (by decide +kernel)
theorem metadata_symmetry_0080 : FiniteChecks.Interval symmetry 80 96 :=
  FiniteChecks.interval_of_check symmetry 80 16 (by decide +kernel)
theorem metadata_symmetry_0096 : FiniteChecks.Interval symmetry 96 112 :=
  FiniteChecks.interval_of_check symmetry 96 16 (by decide +kernel)
theorem metadata_symmetry_0112 : FiniteChecks.Interval symmetry 112 128 :=
  FiniteChecks.interval_of_check symmetry 112 16 (by decide +kernel)
theorem metadata_symmetry_0128 : FiniteChecks.Interval symmetry 128 136 :=
  FiniteChecks.interval_of_check symmetry 128 8 (by decide +kernel)
theorem metadata_symmetry : FiniteChecks.Interval symmetry 0 blockCount :=
  (FiniteChecks.interval_append (symmetry) 0 64 136
  (FiniteChecks.interval_append (symmetry) 0 32 64
  (FiniteChecks.interval_append (symmetry) 0 16 32
  metadata_symmetry_0000
  metadata_symmetry_0016)
  (FiniteChecks.interval_append (symmetry) 32 48 64
  metadata_symmetry_0032
  metadata_symmetry_0048))
  (FiniteChecks.interval_append (symmetry) 64 96 136
  (FiniteChecks.interval_append (symmetry) 64 80 96
  metadata_symmetry_0064
  metadata_symmetry_0080)
  (FiniteChecks.interval_append (symmetry) 96 112 136
  metadata_symmetry_0096
  (FiniteChecks.interval_append (symmetry) 112 128 136
  metadata_symmetry_0112
  metadata_symmetry_0128))))
theorem metadata_normalizers :
    RawFaceNormalizers.completeCheck 6 template root raw faceWitness = true := by decide +kernel
theorem metadata_root : RawFacetEmbedding.wellFormedCheck root = true := by decide +kernel
end Papers.RationalityTen.RootedCanonical.RootedSixBase02.T3

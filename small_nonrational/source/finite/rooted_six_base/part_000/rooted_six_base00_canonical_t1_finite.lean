module
prelude
public import RootedSixBase00
public import RawKindedFacePlacement
public import RootedSixBase00OutsideData
public import RawOutsidePlacement

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase00.T1
open ConcreteGrowth
abbrev blockCount : Nat := 180
noncomputable def template : Cell := ⟨5, 63, [3, 5, 6, 10, 12, 17, 20, 24, 36, 40, 48], [7, 14, 21, 27, 44, 52, 56]⟩
noncomputable def root : Cell := FacetUniverses.RootedSixBase00.cells 0
noncomputable def records : Table (RawFacePlacement.Block × Nat) :=
(.branch 90
 (.branch 45
 (.branch 22
 (.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf (⟨2, 4, 5517840, 5517840, 361626105360, 361626105360⟩, 403445774))
 (.leaf (⟨2, 4, 5517840, 5517840, 361609328160, 361626104160⟩, 420747542)))
 (.branch 3
 (.leaf (⟨2, 4, 5517840, 5517840, 361592550945, 361626104070⟩, 438049310))
 (.branch 4
 (.leaf (⟨2, 4, 5517840, 5517840, 361340892720, 361626081120⟩, 483663062))
 (.leaf (⟨2, 4, 5517840, 5517840, 361324115505, 361626081030⟩, 500964830)))))
 (.branch 8
 (.branch 6
 (.leaf (⟨2, 4, 5517840, 5517840, 361055680050, 361626079350⟩, 546578582))
 (.branch 7
 (.leaf (⟨2, 4, 5517840, 5517840, 357029148225, 361625650950⟩, 592192334))
 (.leaf (⟨2, 4, 5517840, 5517840, 356760712770, 361625649270⟩, 609494102))))
 (.branch 9
 (.leaf (⟨2, 4, 5517840, 5517840, 352465745475, 361625618550⟩, 655107854))
 (.branch 10
 (.leaf (⟨2, 4, 5517840, 5517840, 288041236050, 361617784950⟩, 700721606))
 (.leaf (⟨2, 4, 5517840, 5517840, 283746268755, 361617754230⟩, 718023374))))))
 (.branch 16
 (.branch 13
 (.branch 12
 (.leaf (⟨2, 4, 5517840, 5517840, 215026792020, 361617201270⟩, 763637126))
 (.leaf (⟨2, 4, 5517600, 5517600, 361626105360, 361626105360⟩, 400496631)))
 (.branch 14
 (.leaf (⟨2, 4, 5517600, 5517600, 361609328160, 361626104160⟩, 417798399))
 (.branch 15
 (.leaf (⟨2, 4, 5517600, 5517600, 361592550945, 361626104070⟩, 435100167))
 (.leaf (⟨2, 4, 5517600, 5517600, 361340892720, 361626081120⟩, 480713919)))))
 (.branch 19
 (.branch 17
 (.leaf (⟨2, 4, 5517600, 5517600, 361324115505, 361626081030⟩, 498015687))
 (.branch 18
 (.leaf (⟨2, 4, 5517600, 5517600, 361055680050, 361626079350⟩, 543629439))
 (.leaf (⟨2, 4, 5517600, 5517600, 357029148225, 361625650950⟩, 589243191))))
 (.branch 20
 (.leaf (⟨2, 4, 5517600, 5517600, 356760712770, 361625649270⟩, 606544959))
 (.branch 21
 (.leaf (⟨2, 4, 5517600, 5517600, 352465745475, 361625618550⟩, 652158711))
 (.leaf (⟨2, 4, 5517600, 5517600, 288041236050, 361617784950⟩, 697772463)))))))
 (.branch 33
 (.branch 27
 (.branch 24
 (.branch 23
 (.leaf (⟨2, 4, 5517600, 5517600, 283746268755, 361617754230⟩, 715074231))
 (.leaf (⟨2, 4, 5517600, 5517600, 215026792020, 361617201270⟩, 760687983)))
 (.branch 25
 (.leaf (⟨2, 4, 5517345, 5517570, 361626105360, 361626105360⟩, 400365557))
 (.branch 26
 (.leaf (⟨2, 4, 5517345, 5517570, 361609328160, 361626104160⟩, 417667325))
 (.leaf (⟨2, 4, 5517345, 5517570, 361592550945, 361626104070⟩, 434969093)))))
 (.branch 30
 (.branch 28
 (.leaf (⟨2, 4, 5517345, 5517570, 361340892720, 361626081120⟩, 480582845))
 (.branch 29
 (.leaf (⟨2, 4, 5517345, 5517570, 361324115505, 361626081030⟩, 497884613))
 (.leaf (⟨2, 4, 5517345, 5517570, 361055680050, 361626079350⟩, 543498365))))
 (.branch 31
 (.leaf (⟨2, 4, 5517345, 5517570, 357029148225, 361625650950⟩, 589112117))
 (.branch 32
 (.leaf (⟨2, 4, 5517345, 5517570, 356760712770, 361625649270⟩, 606413885))
 (.leaf (⟨2, 4, 5517345, 5517570, 352465745475, 361625618550⟩, 652027637))))))
 (.branch 39
 (.branch 36
 (.branch 34
 (.leaf (⟨2, 4, 5517345, 5517570, 288041236050, 361617784950⟩, 697641389))
 (.branch 35
 (.leaf (⟨2, 4, 5517345, 5517570, 283746268755, 361617754230⟩, 714943157))
 (.leaf (⟨2, 4, 5517345, 5517570, 215026792020, 361617201270⟩, 760556909))))
 (.branch 37
 (.leaf (⟨3, 4, 5517840, 5517840, 361742426640, 434925761040⟩, 8199060034802429806317804171))
 (.branch 38
 (.leaf (⟨3, 4, 5517840, 5517840, 361473991440, 434925741840⟩, 9359646530777004676079033931))
 (.leaf (⟨3, 4, 5517840, 5517840, 361205556000, 434925740400⟩, 10201071740358571456655925507)))))
 (.branch 42
 (.branch 40
 (.leaf (⟨3, 4, 5517840, 5517840, 356642153505, 434925371655⟩, 11361658236333146326417155267))
 (.branch 41
 (.leaf (⟨3, 4, 5517840, 5517840, 352347186225, 434925344775⟩, 12203083445914713106994046843))
 (.leaf (⟨3, 4, 5517840, 5517840, 279332742450, 434918461575⟩, 13363669941889287976755276603))))
 (.branch 43
 (.leaf (⟨3, 4, 5517840, 5517840, 210613265730, 434917970055⟩, 14205095151470854757332168179))
 (.branch 44
 (.leaf (⟨3, 4, 5517840, 5517840, 141893788995, 434917935495⟩, 14727359074659413448724721571))
 (.leaf (⟨2, 4, 5513265, 5509890, 361626105360, 361626105360⟩, 397219781))))))))
 (.branch 67
 (.branch 56
 (.branch 50
 (.branch 47
 (.branch 46
 (.leaf (⟨2, 4, 5513265, 5509890, 361609328160, 361626104160⟩, 414521549))
 (.leaf (⟨2, 4, 5513265, 5509890, 361592550945, 361626104070⟩, 431823317)))
 (.branch 48
 (.leaf (⟨2, 4, 5513265, 5509890, 361340892720, 361626081120⟩, 477437069))
 (.branch 49
 (.leaf (⟨2, 4, 5513265, 5509890, 361324115505, 361626081030⟩, 494738837))
 (.leaf (⟨2, 4, 5513265, 5509890, 361055680050, 361626079350⟩, 540352589)))))
 (.branch 53
 (.branch 51
 (.leaf (⟨2, 4, 5513265, 5509890, 357029148225, 361625650950⟩, 585966341))
 (.branch 52
 (.leaf (⟨2, 4, 5513265, 5509890, 356760712770, 361625649270⟩, 603268109))
 (.leaf (⟨2, 4, 5513265, 5509890, 352465745475, 361625618550⟩, 648881861))))
 (.branch 54
 (.leaf (⟨2, 4, 5513265, 5509890, 288041236050, 361617784950⟩, 694495613))
 (.branch 55
 (.leaf (⟨2, 4, 5513265, 5509890, 283746268755, 361617754230⟩, 711797381))
 (.leaf (⟨2, 4, 5513265, 5509890, 215026792020, 361617201270⟩, 757411133))))))
 (.branch 61
 (.branch 58
 (.branch 57
 (.leaf (⟨2, 4, 5509170, 5509170, 361626105360, 361626105360⟩, 392632191))
 (.leaf (⟨2, 4, 5509170, 5509170, 361609328160, 361626104160⟩, 409933959)))
 (.branch 59
 (.leaf (⟨2, 4, 5509170, 5509170, 361592550945, 361626104070⟩, 427235727))
 (.branch 60
 (.leaf (⟨2, 4, 5509170, 5509170, 361340892720, 361626081120⟩, 472849479))
 (.leaf (⟨2, 4, 5509170, 5509170, 361324115505, 361626081030⟩, 490151247)))))
 (.branch 64
 (.branch 62
 (.leaf (⟨2, 4, 5509170, 5509170, 361055680050, 361626079350⟩, 535764999))
 (.branch 63
 (.leaf (⟨2, 4, 5509170, 5509170, 357029148225, 361625650950⟩, 581378751))
 (.leaf (⟨2, 4, 5509170, 5509170, 356760712770, 361625649270⟩, 598680519))))
 (.branch 65
 (.leaf (⟨2, 4, 5509170, 5509170, 352465745475, 361625618550⟩, 644294271))
 (.branch 66
 (.leaf (⟨2, 4, 5509170, 5509170, 288041236050, 361617784950⟩, 689908023))
 (.leaf (⟨2, 4, 5509170, 5509170, 283746268755, 361617754230⟩, 707209791)))))))
 (.branch 78
 (.branch 72
 (.branch 69
 (.branch 68
 (.leaf (⟨2, 4, 5509170, 5509170, 215026792020, 361617201270⟩, 752823543))
 (.leaf (⟨3, 4, 5505825, 5513475, 361742426640, 434925761040⟩, 8156747077706840049919924857)))
 (.branch 70
 (.leaf (⟨3, 4, 5505825, 5513475, 361473991440, 434925741840⟩, 9317333573681414919681154617))
 (.branch 71
 (.leaf (⟨3, 4, 5505825, 5513475, 361205556000, 434925740400⟩, 10158758783262981700258046193))
 (.leaf (⟨3, 4, 5505825, 5513475, 356642153505, 434925371655⟩, 11319345279237556570019275953)))))
 (.branch 75
 (.branch 73
 (.leaf (⟨3, 4, 5505825, 5513475, 352347186225, 434925344775⟩, 12160770488819123350596167529))
 (.branch 74
 (.leaf (⟨3, 4, 5505825, 5513475, 279332742450, 434918461575⟩, 13321356984793698220357397289))
 (.leaf (⟨3, 4, 5505825, 5513475, 210613265730, 434917970055⟩, 14162782194375265000934288865))))
 (.branch 76
 (.leaf (⟨3, 4, 5505825, 5513475, 141893788995, 434917935495⟩, 14685046117563823692326842257))
 (.branch 77
 (.leaf (⟨2, 4, 5448000, 5325600, 361626105360, 361626105360⟩, 397219781))
 (.leaf (⟨2, 4, 5448000, 5325600, 361609328160, 361626104160⟩, 414521549))))))
 (.branch 84
 (.branch 81
 (.branch 79
 (.leaf (⟨2, 4, 5448000, 5325600, 361592550945, 361626104070⟩, 431823317))
 (.branch 80
 (.leaf (⟨2, 4, 5448000, 5325600, 361340892720, 361626081120⟩, 477437069))
 (.leaf (⟨2, 4, 5448000, 5325600, 361324115505, 361626081030⟩, 494738837))))
 (.branch 82
 (.leaf (⟨2, 4, 5448000, 5325600, 361055680050, 361626079350⟩, 540352589))
 (.branch 83
 (.leaf (⟨2, 4, 5448000, 5325600, 357029148225, 361625650950⟩, 585966341))
 (.leaf (⟨2, 4, 5448000, 5325600, 356760712770, 361625649270⟩, 603268109)))))
 (.branch 87
 (.branch 85
 (.leaf (⟨2, 4, 5448000, 5325600, 352465745475, 361625618550⟩, 648881861))
 (.branch 86
 (.leaf (⟨2, 4, 5448000, 5325600, 288041236050, 361617784950⟩, 694495613))
 (.leaf (⟨2, 4, 5448000, 5325600, 283746268755, 361617754230⟩, 711797381))))
 (.branch 88
 (.leaf (⟨2, 4, 5448000, 5325600, 215026792020, 361617201270⟩, 757411133))
 (.branch 89
 (.leaf (⟨2, 4, 5443650, 5324850, 361626105360, 361626105360⟩, 392566654))
 (.leaf (⟨2, 4, 5443650, 5324850, 361609328160, 361626104160⟩, 409868422)))))))))
 (.branch 135
 (.branch 112
 (.branch 101
 (.branch 95
 (.branch 92
 (.branch 91
 (.leaf (⟨2, 4, 5443650, 5324850, 361592550945, 361626104070⟩, 427170190))
 (.leaf (⟨2, 4, 5443650, 5324850, 361340892720, 361626081120⟩, 472783942)))
 (.branch 93
 (.leaf (⟨2, 4, 5443650, 5324850, 361324115505, 361626081030⟩, 490085710))
 (.branch 94
 (.leaf (⟨2, 4, 5443650, 5324850, 361055680050, 361626079350⟩, 535699462))
 (.leaf (⟨2, 4, 5443650, 5324850, 357029148225, 361625650950⟩, 581313214)))))
 (.branch 98
 (.branch 96
 (.leaf (⟨2, 4, 5443650, 5324850, 356760712770, 361625649270⟩, 598614982))
 (.branch 97
 (.leaf (⟨2, 4, 5443650, 5324850, 352465745475, 361625618550⟩, 644228734))
 (.leaf (⟨2, 4, 5443650, 5324850, 288041236050, 361617784950⟩, 689842486))))
 (.branch 99
 (.leaf (⟨2, 4, 5443650, 5324850, 283746268755, 361617754230⟩, 707144254))
 (.branch 100
 (.leaf (⟨2, 4, 5443650, 5324850, 215026792020, 361617201270⟩, 752758006))
 (.leaf (⟨3, 4, 5444640, 5390640, 361742426640, 434925761040⟩, 8156747077706840049919924857))))))
 (.branch 106
 (.branch 103
 (.branch 102
 (.leaf (⟨3, 4, 5444640, 5390640, 361473991440, 434925741840⟩, 9317333573681414919681154617))
 (.leaf (⟨3, 4, 5444640, 5390640, 361205556000, 434925740400⟩, 10158758783262981700258046193)))
 (.branch 104
 (.leaf (⟨3, 4, 5444640, 5390640, 356642153505, 434925371655⟩, 11319345279237556570019275953))
 (.branch 105
 (.leaf (⟨3, 4, 5444640, 5390640, 352347186225, 434925344775⟩, 12160770488819123350596167529))
 (.leaf (⟨3, 4, 5444640, 5390640, 279332742450, 434918461575⟩, 13321356984793698220357397289)))))
 (.branch 109
 (.branch 107
 (.leaf (⟨3, 4, 5444640, 5390640, 210613265730, 434917970055⟩, 14162782194375265000934288865))
 (.branch 108
 (.leaf (⟨3, 4, 5444640, 5390640, 141893788995, 434917935495⟩, 14685046117563823692326842257))
 (.leaf (⟨2, 4, 5378115, 5309490, 361626105360, 361626105360⟩, 395712407))))
 (.branch 110
 (.leaf (⟨2, 4, 5378115, 5309490, 361609328160, 361626104160⟩, 413014175))
 (.branch 111
 (.leaf (⟨2, 4, 5378115, 5309490, 361592550945, 361626104070⟩, 430315943))
 (.leaf (⟨2, 4, 5378115, 5309490, 361340892720, 361626081120⟩, 475929695)))))))
 (.branch 123
 (.branch 117
 (.branch 114
 (.branch 113
 (.leaf (⟨2, 4, 5378115, 5309490, 361324115505, 361626081030⟩, 493231463))
 (.leaf (⟨2, 4, 5378115, 5309490, 361055680050, 361626079350⟩, 538845215)))
 (.branch 115
 (.leaf (⟨2, 4, 5378115, 5309490, 357029148225, 361625650950⟩, 584458967))
 (.branch 116
 (.leaf (⟨2, 4, 5378115, 5309490, 356760712770, 361625649270⟩, 601760735))
 (.leaf (⟨2, 4, 5378115, 5309490, 352465745475, 361625618550⟩, 647374487)))))
 (.branch 120
 (.branch 118
 (.leaf (⟨2, 4, 5378115, 5309490, 288041236050, 361617784950⟩, 692988239))
 (.branch 119
 (.leaf (⟨2, 4, 5378115, 5309490, 283746268755, 361617754230⟩, 710290007))
 (.leaf (⟨2, 4, 5378115, 5309490, 215026792020, 361617201270⟩, 755903759))))
 (.branch 121
 (.leaf (⟨2, 4, 4395090, 1392690, 361626105360, 361626105360⟩, 390272847))
 (.branch 122
 (.leaf (⟨2, 4, 4395090, 1392690, 361609328160, 361626104160⟩, 407574615))
 (.leaf (⟨2, 4, 4395090, 1392690, 361592550945, 361626104070⟩, 424876383))))))
 (.branch 129
 (.branch 126
 (.branch 124
 (.leaf (⟨2, 4, 4395090, 1392690, 361340892720, 361626081120⟩, 470490135))
 (.branch 125
 (.leaf (⟨2, 4, 4395090, 1392690, 361324115505, 361626081030⟩, 487791903))
 (.leaf (⟨2, 4, 4395090, 1392690, 361055680050, 361626079350⟩, 533405655))))
 (.branch 127
 (.leaf (⟨2, 4, 4395090, 1392690, 357029148225, 361625650950⟩, 579019407))
 (.branch 128
 (.leaf (⟨2, 4, 4395090, 1392690, 356760712770, 361625649270⟩, 596321175))
 (.leaf (⟨2, 4, 4395090, 1392690, 352465745475, 361625618550⟩, 641934927)))))
 (.branch 132
 (.branch 130
 (.leaf (⟨2, 4, 4395090, 1392690, 288041236050, 361617784950⟩, 687548679))
 (.branch 131
 (.leaf (⟨2, 4, 4395090, 1392690, 283746268755, 361617754230⟩, 704850447))
 (.leaf (⟨2, 4, 4395090, 1392690, 215026792020, 361617201270⟩, 750464199))))
 (.branch 133
 (.leaf (⟨2, 4, 4329555, 1377330, 361626105360, 361626105360⟩, 387520305))
 (.branch 134
 (.leaf (⟨2, 4, 4329555, 1377330, 361609328160, 361626104160⟩, 404822073))
 (.leaf (⟨2, 4, 4329555, 1377330, 361592550945, 361626104070⟩, 422123841))))))))
 (.branch 157
 (.branch 146
 (.branch 140
 (.branch 137
 (.branch 136
 (.leaf (⟨2, 4, 4329555, 1377330, 361340892720, 361626081120⟩, 467737593))
 (.leaf (⟨2, 4, 4329555, 1377330, 361324115505, 361626081030⟩, 485039361)))
 (.branch 138
 (.leaf (⟨2, 4, 4329555, 1377330, 361055680050, 361626079350⟩, 530653113))
 (.branch 139
 (.leaf (⟨2, 4, 4329555, 1377330, 357029148225, 361625650950⟩, 576266865))
 (.leaf (⟨2, 4, 4329555, 1377330, 356760712770, 361625649270⟩, 593568633)))))
 (.branch 143
 (.branch 141
 (.leaf (⟨2, 4, 4329555, 1377330, 352465745475, 361625618550⟩, 639182385))
 (.branch 142
 (.leaf (⟨2, 4, 4329555, 1377330, 288041236050, 361617784950⟩, 684796137))
 (.leaf (⟨2, 4, 4329555, 1377330, 283746268755, 361617754230⟩, 702097905))))
 (.branch 144
 (.leaf (⟨2, 4, 4329555, 1377330, 215026792020, 361617201270⟩, 747711657))
 (.branch 145
 (.leaf (⟨3, 4, 4261170, 2428995, 361742426640, 434925761040⟩, 8091464087308270213495855683))
 (.leaf (⟨3, 4, 4261170, 2428995, 361473991440, 434925741840⟩, 9252050583282845083257085443))))))
 (.branch 151
 (.branch 148
 (.branch 147
 (.leaf (⟨3, 4, 4261170, 2428995, 361205556000, 434925740400⟩, 10093475792864411863833977019))
 (.leaf (⟨3, 4, 4261170, 2428995, 356642153505, 434925371655⟩, 11254062288838986733595206779)))
 (.branch 149
 (.leaf (⟨3, 4, 4261170, 2428995, 352347186225, 434925344775⟩, 12095487498420553514172098355))
 (.branch 150
 (.leaf (⟨3, 4, 4261170, 2428995, 279332742450, 434918461575⟩, 13256073994395128383933328115))
 (.leaf (⟨3, 4, 4261170, 2428995, 210613265730, 434917970055⟩, 14097499203976695164510219691)))))
 (.branch 154
 (.branch 152
 (.leaf (⟨3, 4, 4261170, 2428995, 141893788995, 434917935495⟩, 14619763127165253855902773083))
 (.branch 153
 (.leaf (⟨2, 4, 3280980, 1070130, 361626105360, 361626105360⟩, 387454768))
 (.leaf (⟨2, 4, 3280980, 1070130, 361609328160, 361626104160⟩, 404756536))))
 (.branch 155
 (.leaf (⟨2, 4, 3280980, 1070130, 361592550945, 361626104070⟩, 422058304))
 (.branch 156
 (.leaf (⟨2, 4, 3280980, 1070130, 361340892720, 361626081120⟩, 467672056))
 (.leaf (⟨2, 4, 3280980, 1070130, 361324115505, 361626081030⟩, 484973824)))))))
 (.branch 168
 (.branch 162
 (.branch 159
 (.branch 158
 (.leaf (⟨2, 4, 3280980, 1070130, 361055680050, 361626079350⟩, 530587576))
 (.leaf (⟨2, 4, 3280980, 1070130, 357029148225, 361625650950⟩, 576201328)))
 (.branch 160
 (.leaf (⟨2, 4, 3280980, 1070130, 356760712770, 361625649270⟩, 593503096))
 (.branch 161
 (.leaf (⟨2, 4, 3280980, 1070130, 352465745475, 361625618550⟩, 639116848))
 (.leaf (⟨2, 4, 3280980, 1070130, 288041236050, 361617784950⟩, 684730600)))))
 (.branch 165
 (.branch 163
 (.leaf (⟨2, 4, 3280980, 1070130, 283746268755, 361617754230⟩, 702032368))
 (.branch 164
 (.leaf (⟨2, 4, 3280980, 1070130, 215026792020, 361617201270⟩, 747646120))
 (.leaf (⟨3, 4, 3212610, 2183235, 361742426640, 434925761040⟩, 8090255143041630031339854402))))
 (.branch 166
 (.leaf (⟨3, 4, 3212610, 2183235, 361473991440, 434925741840⟩, 9250841639016204901101084162))
 (.branch 167
 (.leaf (⟨3, 4, 3212610, 2183235, 361205556000, 434925740400⟩, 10092266848597771681677975738))
 (.leaf (⟨3, 4, 3212610, 2183235, 356642153505, 434925371655⟩, 11252853344572346551439205498))))))
 (.branch 174
 (.branch 171
 (.branch 169
 (.leaf (⟨3, 4, 3212610, 2183235, 352347186225, 434925344775⟩, 12094278554153913332016097074))
 (.branch 170
 (.leaf (⟨3, 4, 3212610, 2183235, 279332742450, 434918461575⟩, 13254865050128488201777326834))
 (.leaf (⟨3, 4, 3212610, 2183235, 210613265730, 434917970055⟩, 14096290259710054982354218410))))
 (.branch 172
 (.leaf (⟨3, 4, 3212610, 2183235, 141893788995, 434917935495⟩, 14618554182898613673746771802))
 (.branch 173
 (.leaf (⟨3, 4, 2164035, 2164035, 361742426640, 434925761040⟩, 8133777044403859969893734997))
 (.leaf (⟨3, 4, 2164035, 2164035, 361473991440, 434925741840⟩, 9294363540378434839654964757)))))
 (.branch 177
 (.branch 175
 (.leaf (⟨3, 4, 2164035, 2164035, 361205556000, 434925740400⟩, 10135788749960001620231856333))
 (.branch 176
 (.leaf (⟨3, 4, 2164035, 2164035, 356642153505, 434925371655⟩, 11296375245934576489993086093))
 (.leaf (⟨3, 4, 2164035, 2164035, 352347186225, 434925344775⟩, 12137800455516143270569977669))))
 (.branch 178
 (.leaf (⟨3, 4, 2164035, 2164035, 279332742450, 434918461575⟩, 13298386951490718140331207429))
 (.branch 179
 (.leaf (⟨3, 4, 2164035, 2164035, 210613265730, 434917970055⟩, 14139812161072284920908099005))
 (.leaf (⟨3, 4, 2164035, 2164035, 141893788995, 434917935495⟩, 14662076084260843612300652397))))))))))
noncomputable def raw (i : Fin blockCount) : RawFacePlacement.Block := (records.get i.val).1
noncomputable def witness (i : Fin blockCount) (code : Nat) : Fin 21976 :=
  Fin.ofNat 21976 (Nat.land (Nat.shiftRight (records.get i.val).2 (16 * code)) 65535)
noncomputable def faceTable : Table Nat :=
(.branch 20486
 (.branch 10245
 (.branch 5160
 (.branch 3120
 (.branch 3084
 (.branch 3078
 (.branch 3077
 (.leaf 0)
 (.leaf 1))
 (.branch 3081
 (.leaf 2)
 (.branch 3082
 (.leaf 3)
 (.leaf 4))))
 (.branch 3096
 (.branch 3090
 (.leaf 5)
 (.branch 3092
 (.leaf 6)
 (.leaf 7)))
 (.branch 3108
 (.leaf 8)
 (.branch 3112
 (.leaf 9)
 (.leaf 10)))))
 (.branch 5130
 (.branch 5125
 (.branch 5123
 (.leaf 11)
 (.leaf 12))
 (.branch 5126
 (.leaf 13)
 (.branch 5129
 (.leaf 14)
 (.leaf 15))))
 (.branch 5140
 (.branch 5132
 (.leaf 16)
 (.branch 5138
 (.leaf 17)
 (.leaf 18)))
 (.branch 5144
 (.leaf 19)
 (.branch 5156
 (.leaf 20)
 (.leaf 21))))))
 (.branch 6180
 (.branch 6153
 (.branch 6147
 (.branch 5168
 (.leaf 22)
 (.leaf 23))
 (.branch 6149
 (.leaf 24)
 (.branch 6150
 (.leaf 25)
 (.leaf 26))))
 (.branch 6162
 (.branch 6154
 (.leaf 27)
 (.branch 6156
 (.leaf 28)
 (.leaf 29)))
 (.branch 6164
 (.leaf 30)
 (.branch 6168
 (.leaf 31)
 (.leaf 32)))))
 (.branch 7190
 (.branch 7175
 (.branch 6184
 (.leaf 33)
 (.branch 6192
 (.leaf 34)
 (.leaf 35)))
 (.branch 7179
 (.leaf 36)
 (.branch 7181
 (.leaf 37)
 (.leaf 38))))
 (.branch 7220
 (.branch 7194
 (.leaf 39)
 (.branch 7212
 (.leaf 40)
 (.leaf 41)))
 (.branch 7224
 (.leaf 42)
 (.branch 10243
 (.leaf 43)
 (.leaf 44)))))))
 (.branch 12336
 (.branch 12291
 (.branch 10258
 (.branch 10249
 (.branch 10246
 (.leaf 45)
 (.leaf 46))
 (.branch 10250
 (.leaf 47)
 (.branch 10252
 (.leaf 48)
 (.leaf 49))))
 (.branch 10276
 (.branch 10260
 (.leaf 50)
 (.branch 10264
 (.leaf 51)
 (.leaf 52)))
 (.branch 10280
 (.leaf 53)
 (.branch 10288
 (.leaf 54)
 (.leaf 55)))))
 (.branch 12300
 (.branch 12294
 (.branch 12293
 (.leaf 56)
 (.leaf 57))
 (.branch 12297
 (.leaf 58)
 (.branch 12298
 (.leaf 59)
 (.leaf 60))))
 (.branch 12312
 (.branch 12306
 (.leaf 61)
 (.branch 12308
 (.leaf 62)
 (.leaf 63)))
 (.branch 12324
 (.leaf 64)
 (.branch 12328
 (.leaf 65)
 (.leaf 66))))))
 (.branch 17414
 (.branch 14362
 (.branch 14347
 (.branch 14343
 (.leaf 67)
 (.leaf 68))
 (.branch 14349
 (.leaf 69)
 (.branch 14358
 (.leaf 70)
 (.leaf 71))))
 (.branch 14392
 (.branch 14380
 (.leaf 72)
 (.branch 14388
 (.leaf 73)
 (.leaf 74)))
 (.branch 17411
 (.leaf 75)
 (.branch 17413
 (.leaf 76)
 (.leaf 77)))))
 (.branch 17432
 (.branch 17420
 (.branch 17417
 (.leaf 78)
 (.branch 17418
 (.leaf 79)
 (.leaf 80)))
 (.branch 17426
 (.leaf 81)
 (.branch 17428
 (.leaf 82)
 (.leaf 83))))
 (.branch 17456
 (.branch 17444
 (.leaf 84)
 (.branch 17448
 (.leaf 85)
 (.leaf 86)))
 (.branch 20483
 (.leaf 87)
 (.branch 20485
 (.leaf 88)
 (.leaf 89))))))))
 (.branch 40969
 (.branch 24586
 (.branch 21515
 (.branch 20500
 (.branch 20490
 (.branch 20489
 (.leaf 90)
 (.leaf 91))
 (.branch 20492
 (.leaf 92)
 (.branch 20498
 (.leaf 93)
 (.leaf 94))))
 (.branch 20520
 (.branch 20504
 (.leaf 95)
 (.branch 20516
 (.leaf 96)
 (.leaf 97)))
 (.branch 20528
 (.leaf 98)
 (.branch 21511
 (.leaf 99)
 (.leaf 100)))))
 (.branch 21556
 (.branch 21526
 (.branch 21517
 (.leaf 101)
 (.leaf 102))
 (.branch 21530
 (.leaf 103)
 (.branch 21548
 (.leaf 104)
 (.leaf 105))))
 (.branch 24581
 (.branch 21560
 (.leaf 106)
 (.branch 24579
 (.leaf 107)
 (.leaf 108)))
 (.branch 24582
 (.leaf 109)
 (.branch 24585
 (.leaf 110)
 (.leaf 111))))))
 (.branch 36873
 (.branch 24612
 (.branch 24594
 (.branch 24588
 (.leaf 112)
 (.leaf 113))
 (.branch 24596
 (.leaf 114)
 (.branch 24600
 (.leaf 115)
 (.leaf 116))))
 (.branch 36867
 (.branch 24616
 (.leaf 117)
 (.branch 24624
 (.leaf 118)
 (.leaf 119)))
 (.branch 36869
 (.leaf 120)
 (.branch 36870
 (.leaf 121)
 (.leaf 122)))))
 (.branch 36900
 (.branch 36882
 (.branch 36874
 (.leaf 123)
 (.branch 36876
 (.leaf 124)
 (.leaf 125)))
 (.branch 36884
 (.leaf 126)
 (.branch 36888
 (.leaf 127)
 (.leaf 128))))
 (.branch 40963
 (.branch 36904
 (.leaf 129)
 (.branch 36912
 (.leaf 130)
 (.leaf 131)))
 (.branch 40965
 (.leaf 132)
 (.branch 40966
 (.leaf 133)
 (.leaf 134)))))))
 (.branch 49164
 (.branch 45069
 (.branch 40984
 (.branch 40972
 (.branch 40970
 (.leaf 135)
 (.leaf 136))
 (.branch 40978
 (.leaf 137)
 (.branch 40980
 (.leaf 138)
 (.leaf 139))))
 (.branch 41008
 (.branch 40996
 (.leaf 140)
 (.branch 41000
 (.leaf 141)
 (.leaf 142)))
 (.branch 45063
 (.leaf 143)
 (.branch 45067
 (.leaf 144)
 (.leaf 145)))))
 (.branch 45112
 (.branch 45082
 (.branch 45078
 (.leaf 146)
 (.leaf 147))
 (.branch 45100
 (.leaf 148)
 (.branch 45108
 (.leaf 149)
 (.leaf 150))))
 (.branch 49158
 (.branch 49155
 (.leaf 151)
 (.branch 49157
 (.leaf 152)
 (.leaf 153)))
 (.branch 49161
 (.leaf 154)
 (.branch 49162
 (.leaf 155)
 (.leaf 156))))))
 (.branch 53274
 (.branch 49192
 (.branch 49172
 (.branch 49170
 (.leaf 157)
 (.leaf 158))
 (.branch 49176
 (.leaf 159)
 (.branch 49188
 (.leaf 160)
 (.leaf 161))))
 (.branch 53259
 (.branch 49200
 (.leaf 162)
 (.branch 53255
 (.leaf 163)
 (.leaf 164)))
 (.branch 53261
 (.leaf 165)
 (.branch 53270
 (.leaf 166)
 (.leaf 167)))))
 (.branch 57357
 (.branch 53304
 (.branch 53292
 (.leaf 168)
 (.branch 53300
 (.leaf 169)
 (.leaf 170)))
 (.branch 57351
 (.leaf 171)
 (.branch 57355
 (.leaf 172)
 (.leaf 173))))
 (.branch 57388
 (.branch 57366
 (.leaf 174)
 (.branch 57370
 (.leaf 175)
 (.leaf 176)))
 (.branch 57396
 (.leaf 177)
 (.branch 57400
 (.leaf 178)
 (.leaf 179)))))))))
noncomputable def faceWitness (s r : Nat) : Fin blockCount :=
  Fin.ofNat blockCount (faceTable.get (s * 1024 + r))
noncomputable def validity (i : Nat) : Bool :=
  RawFaceNormalizers.blockValidCheck 6 (raw (Fin.ofNat blockCount i))
noncomputable def placement (b : Fin blockCount) (code : Nat) : Bool :=
  RawKindedFacePlacement.check 6 (raw b) template root FacetUniverses.RootedSixBase00.cells
    code 0 (witness b code)
noncomputable def test (i : Nat) : Bool :=
  let b := Fin.ofNat blockCount i
  FiniteChecks.checkRange (placement b)
    0 (RawFacePlacement.count (raw b).shared (raw b).shared)
noncomputable def symmetry (i : Nat) : Bool :=
  RawOutsidePlacement.blockCheck FacetUniverses.RootedSixBase00.Outside.vertexCode root.vertices
    (raw (Fin.ofNat blockCount i))
end Papers.RationalityTen.RootedCanonical.RootedSixBase00.T1

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase00.T1
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
theorem check_0030_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 30)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 30)) 0 2 (by decide +kernel)
theorem block_0030 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 30)) 0 2 :=
  check_0030_0000
theorem check_0031_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 31)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 31)) 0 2 (by decide +kernel)
theorem block_0031 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 31)) 0 2 :=
  check_0031_0000
theorem check_0032_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 32)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 32)) 0 2 (by decide +kernel)
theorem block_0032 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 32)) 0 2 :=
  check_0032_0000
theorem check_0033_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 33)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 33)) 0 2 (by decide +kernel)
theorem block_0033 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 33)) 0 2 :=
  check_0033_0000
theorem check_0034_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 34)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 34)) 0 2 (by decide +kernel)
theorem block_0034 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 34)) 0 2 :=
  check_0034_0000
theorem check_0035_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 35)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 35)) 0 2 (by decide +kernel)
theorem block_0035 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 35)) 0 2 :=
  check_0035_0000
theorem check_0036_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 36)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 36)) 0 6 (by decide +kernel)
theorem block_0036 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 36)) 0 6 :=
  check_0036_0000
theorem check_0037_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 37)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 37)) 0 6 (by decide +kernel)
theorem block_0037 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 37)) 0 6 :=
  check_0037_0000
theorem check_0038_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 38)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 38)) 0 6 (by decide +kernel)
theorem block_0038 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 38)) 0 6 :=
  check_0038_0000
theorem check_0039_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 39)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 39)) 0 6 (by decide +kernel)
theorem block_0039 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 39)) 0 6 :=
  check_0039_0000
theorem check_0040_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 40)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 40)) 0 6 (by decide +kernel)
theorem block_0040 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 40)) 0 6 :=
  check_0040_0000
theorem check_0041_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 41)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 41)) 0 6 (by decide +kernel)
theorem block_0041 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 41)) 0 6 :=
  check_0041_0000
theorem check_0042_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 42)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 42)) 0 6 (by decide +kernel)
theorem block_0042 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 42)) 0 6 :=
  check_0042_0000
theorem check_0043_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 43)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 43)) 0 6 (by decide +kernel)
theorem block_0043 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 43)) 0 6 :=
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
end Papers.RationalityTen.RootedCanonical.RootedSixBase00.T1

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase00.T1
theorem check_0064_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 64)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 64)) 0 2 (by decide +kernel)
theorem block_0064 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 64)) 0 2 :=
  check_0064_0000
theorem check_0065_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 65)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 65)) 0 2 (by decide +kernel)
theorem block_0065 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 65)) 0 2 :=
  check_0065_0000
theorem check_0066_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 66)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 66)) 0 2 (by decide +kernel)
theorem block_0066 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 66)) 0 2 :=
  check_0066_0000
theorem check_0067_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 67)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 67)) 0 2 (by decide +kernel)
theorem block_0067 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 67)) 0 2 :=
  check_0067_0000
theorem check_0068_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 68)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 68)) 0 6 (by decide +kernel)
theorem block_0068 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 68)) 0 6 :=
  check_0068_0000
theorem check_0069_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 69)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 69)) 0 6 (by decide +kernel)
theorem block_0069 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 69)) 0 6 :=
  check_0069_0000
theorem check_0070_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 70)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 70)) 0 6 (by decide +kernel)
theorem block_0070 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 70)) 0 6 :=
  check_0070_0000
theorem check_0071_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 71)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 71)) 0 6 (by decide +kernel)
theorem block_0071 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 71)) 0 6 :=
  check_0071_0000
theorem check_0072_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 72)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 72)) 0 6 (by decide +kernel)
theorem block_0072 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 72)) 0 6 :=
  check_0072_0000
theorem check_0073_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 73)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 73)) 0 6 (by decide +kernel)
theorem block_0073 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 73)) 0 6 :=
  check_0073_0000
theorem check_0074_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 74)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 74)) 0 6 (by decide +kernel)
theorem block_0074 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 74)) 0 6 :=
  check_0074_0000
theorem check_0075_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 75)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 75)) 0 6 (by decide +kernel)
theorem block_0075 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 75)) 0 6 :=
  check_0075_0000
theorem check_0076_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 76)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 76)) 0 2 (by decide +kernel)
theorem block_0076 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 76)) 0 2 :=
  check_0076_0000
theorem check_0077_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 77)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 77)) 0 2 (by decide +kernel)
theorem block_0077 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 77)) 0 2 :=
  check_0077_0000
theorem check_0078_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 78)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 78)) 0 2 (by decide +kernel)
theorem block_0078 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 78)) 0 2 :=
  check_0078_0000
theorem check_0079_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 79)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 79)) 0 2 (by decide +kernel)
theorem block_0079 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 79)) 0 2 :=
  check_0079_0000
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
theorem check_0104_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 104)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 104)) 0 6 (by decide +kernel)
theorem block_0104 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 104)) 0 6 :=
  check_0104_0000
theorem check_0105_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 105)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 105)) 0 6 (by decide +kernel)
theorem block_0105 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 105)) 0 6 :=
  check_0105_0000
theorem check_0106_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 106)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 106)) 0 6 (by decide +kernel)
theorem block_0106 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 106)) 0 6 :=
  check_0106_0000
theorem check_0107_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 107)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 107)) 0 6 (by decide +kernel)
theorem block_0107 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 107)) 0 6 :=
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
theorem check_0114_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 114)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 114)) 0 2 (by decide +kernel)
theorem block_0114 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 114)) 0 2 :=
  check_0114_0000
theorem check_0115_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 115)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 115)) 0 2 (by decide +kernel)
theorem block_0115 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 115)) 0 2 :=
  check_0115_0000
theorem check_0116_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 116)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 116)) 0 2 (by decide +kernel)
theorem block_0116 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 116)) 0 2 :=
  check_0116_0000
theorem check_0117_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 117)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 117)) 0 2 (by decide +kernel)
theorem block_0117 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 117)) 0 2 :=
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
end Papers.RationalityTen.RootedCanonical.RootedSixBase00.T1

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase00.T1
theorem check_0128_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 128)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 128)) 0 2 (by decide +kernel)
theorem block_0128 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 128)) 0 2 :=
  check_0128_0000
theorem check_0129_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 129)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 129)) 0 2 (by decide +kernel)
theorem block_0129 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 129)) 0 2 :=
  check_0129_0000
theorem check_0130_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 130)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 130)) 0 2 (by decide +kernel)
theorem block_0130 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 130)) 0 2 :=
  check_0130_0000
theorem check_0131_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 131)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 131)) 0 2 (by decide +kernel)
theorem block_0131 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 131)) 0 2 :=
  check_0131_0000
theorem check_0132_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 132)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 132)) 0 2 (by decide +kernel)
theorem block_0132 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 132)) 0 2 :=
  check_0132_0000
theorem check_0133_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 133)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 133)) 0 2 (by decide +kernel)
theorem block_0133 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 133)) 0 2 :=
  check_0133_0000
theorem check_0134_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 134)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 134)) 0 2 (by decide +kernel)
theorem block_0134 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 134)) 0 2 :=
  check_0134_0000
theorem check_0135_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 135)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 135)) 0 2 (by decide +kernel)
theorem block_0135 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 135)) 0 2 :=
  check_0135_0000
theorem check_0136_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 136)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 136)) 0 2 (by decide +kernel)
theorem block_0136 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 136)) 0 2 :=
  check_0136_0000
theorem check_0137_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 137)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 137)) 0 2 (by decide +kernel)
theorem block_0137 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 137)) 0 2 :=
  check_0137_0000
theorem check_0138_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 138)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 138)) 0 2 (by decide +kernel)
theorem block_0138 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 138)) 0 2 :=
  check_0138_0000
theorem check_0139_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 139)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 139)) 0 2 (by decide +kernel)
theorem block_0139 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 139)) 0 2 :=
  check_0139_0000
theorem check_0140_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 140)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 140)) 0 2 (by decide +kernel)
theorem block_0140 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 140)) 0 2 :=
  check_0140_0000
theorem check_0141_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 141)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 141)) 0 2 (by decide +kernel)
theorem block_0141 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 141)) 0 2 :=
  check_0141_0000
theorem check_0142_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 142)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 142)) 0 2 (by decide +kernel)
theorem block_0142 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 142)) 0 2 :=
  check_0142_0000
theorem check_0143_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 143)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 143)) 0 2 (by decide +kernel)
theorem block_0143 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 143)) 0 2 :=
  check_0143_0000
theorem check_0144_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 144)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 144)) 0 6 (by decide +kernel)
theorem block_0144 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 144)) 0 6 :=
  check_0144_0000
theorem check_0145_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 145)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 145)) 0 6 (by decide +kernel)
theorem block_0145 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 145)) 0 6 :=
  check_0145_0000
theorem check_0146_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 146)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 146)) 0 6 (by decide +kernel)
theorem block_0146 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 146)) 0 6 :=
  check_0146_0000
theorem check_0147_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 147)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 147)) 0 6 (by decide +kernel)
theorem block_0147 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 147)) 0 6 :=
  check_0147_0000
theorem check_0148_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 148)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 148)) 0 6 (by decide +kernel)
theorem block_0148 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 148)) 0 6 :=
  check_0148_0000
theorem check_0149_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 149)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 149)) 0 6 (by decide +kernel)
theorem block_0149 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 149)) 0 6 :=
  check_0149_0000
theorem check_0150_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 150)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 150)) 0 6 (by decide +kernel)
theorem block_0150 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 150)) 0 6 :=
  check_0150_0000
theorem check_0151_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 151)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 151)) 0 6 (by decide +kernel)
theorem block_0151 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 151)) 0 6 :=
  check_0151_0000
theorem check_0152_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 152)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 152)) 0 2 (by decide +kernel)
theorem block_0152 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 152)) 0 2 :=
  check_0152_0000
theorem check_0153_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 153)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 153)) 0 2 (by decide +kernel)
theorem block_0153 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 153)) 0 2 :=
  check_0153_0000
theorem check_0154_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 154)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 154)) 0 2 (by decide +kernel)
theorem block_0154 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 154)) 0 2 :=
  check_0154_0000
theorem check_0155_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 155)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 155)) 0 2 (by decide +kernel)
theorem block_0155 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 155)) 0 2 :=
  check_0155_0000
theorem check_0156_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 156)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 156)) 0 2 (by decide +kernel)
theorem block_0156 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 156)) 0 2 :=
  check_0156_0000
theorem check_0157_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 157)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 157)) 0 2 (by decide +kernel)
theorem block_0157 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 157)) 0 2 :=
  check_0157_0000
theorem check_0158_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 158)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 158)) 0 2 (by decide +kernel)
theorem block_0158 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 158)) 0 2 :=
  check_0158_0000
theorem check_0159_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 159)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 159)) 0 2 (by decide +kernel)
theorem block_0159 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 159)) 0 2 :=
  check_0159_0000
theorem check_0160_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 160)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 160)) 0 2 (by decide +kernel)
theorem block_0160 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 160)) 0 2 :=
  check_0160_0000
theorem check_0161_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 161)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 161)) 0 2 (by decide +kernel)
theorem block_0161 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 161)) 0 2 :=
  check_0161_0000
theorem check_0162_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 162)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 162)) 0 2 (by decide +kernel)
theorem block_0162 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 162)) 0 2 :=
  check_0162_0000
theorem check_0163_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 163)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 163)) 0 2 (by decide +kernel)
theorem block_0163 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 163)) 0 2 :=
  check_0163_0000
theorem check_0164_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 164)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 164)) 0 6 (by decide +kernel)
theorem block_0164 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 164)) 0 6 :=
  check_0164_0000
theorem check_0165_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 165)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 165)) 0 6 (by decide +kernel)
theorem block_0165 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 165)) 0 6 :=
  check_0165_0000
theorem check_0166_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 166)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 166)) 0 6 (by decide +kernel)
theorem block_0166 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 166)) 0 6 :=
  check_0166_0000
theorem check_0167_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 167)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 167)) 0 6 (by decide +kernel)
theorem block_0167 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 167)) 0 6 :=
  check_0167_0000
theorem check_0168_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 168)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 168)) 0 6 (by decide +kernel)
theorem block_0168 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 168)) 0 6 :=
  check_0168_0000
theorem check_0169_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 169)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 169)) 0 6 (by decide +kernel)
theorem block_0169 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 169)) 0 6 :=
  check_0169_0000
theorem check_0170_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 170)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 170)) 0 6 (by decide +kernel)
theorem block_0170 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 170)) 0 6 :=
  check_0170_0000
theorem check_0171_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 171)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 171)) 0 6 (by decide +kernel)
theorem block_0171 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 171)) 0 6 :=
  check_0171_0000
theorem check_0172_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 172)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 172)) 0 6 (by decide +kernel)
theorem block_0172 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 172)) 0 6 :=
  check_0172_0000
theorem check_0173_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 173)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 173)) 0 6 (by decide +kernel)
theorem block_0173 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 173)) 0 6 :=
  check_0173_0000
theorem check_0174_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 174)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 174)) 0 6 (by decide +kernel)
theorem block_0174 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 174)) 0 6 :=
  check_0174_0000
theorem check_0175_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 175)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 175)) 0 6 (by decide +kernel)
theorem block_0175 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 175)) 0 6 :=
  check_0175_0000
theorem check_0176_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 176)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 176)) 0 6 (by decide +kernel)
theorem block_0176 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 176)) 0 6 :=
  check_0176_0000
theorem check_0177_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 177)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 177)) 0 6 (by decide +kernel)
theorem block_0177 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 177)) 0 6 :=
  check_0177_0000
theorem check_0178_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 178)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 178)) 0 6 (by decide +kernel)
theorem block_0178 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 178)) 0 6 :=
  check_0178_0000
theorem check_0179_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 179)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 179)) 0 6 (by decide +kernel)
theorem block_0179 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 179)) 0 6 :=
  check_0179_0000
end Papers.RationalityTen.RootedCanonical.RootedSixBase00.T1

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase00.T1
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
theorem metadata_validity_0128 : FiniteChecks.Interval validity 128 144 :=
  FiniteChecks.interval_of_check validity 128 16 (by decide +kernel)
theorem metadata_validity_0144 : FiniteChecks.Interval validity 144 160 :=
  FiniteChecks.interval_of_check validity 144 16 (by decide +kernel)
theorem metadata_validity_0160 : FiniteChecks.Interval validity 160 176 :=
  FiniteChecks.interval_of_check validity 160 16 (by decide +kernel)
theorem metadata_validity_0176 : FiniteChecks.Interval validity 176 180 :=
  FiniteChecks.interval_of_check validity 176 4 (by decide +kernel)
theorem metadata_validity : FiniteChecks.Interval validity 0 blockCount :=
  (FiniteChecks.interval_append (validity) 0 96 180
  (FiniteChecks.interval_append (validity) 0 48 96
  (FiniteChecks.interval_append (validity) 0 16 48
  metadata_validity_0000
  (FiniteChecks.interval_append (validity) 16 32 48
  metadata_validity_0016
  metadata_validity_0032))
  (FiniteChecks.interval_append (validity) 48 64 96
  metadata_validity_0048
  (FiniteChecks.interval_append (validity) 64 80 96
  metadata_validity_0064
  metadata_validity_0080)))
  (FiniteChecks.interval_append (validity) 96 144 180
  (FiniteChecks.interval_append (validity) 96 112 144
  metadata_validity_0096
  (FiniteChecks.interval_append (validity) 112 128 144
  metadata_validity_0112
  metadata_validity_0128))
  (FiniteChecks.interval_append (validity) 144 160 180
  metadata_validity_0144
  (FiniteChecks.interval_append (validity) 160 176 180
  metadata_validity_0160
  metadata_validity_0176))))
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
theorem metadata_symmetry_0128 : FiniteChecks.Interval symmetry 128 144 :=
  FiniteChecks.interval_of_check symmetry 128 16 (by decide +kernel)
theorem metadata_symmetry_0144 : FiniteChecks.Interval symmetry 144 160 :=
  FiniteChecks.interval_of_check symmetry 144 16 (by decide +kernel)
theorem metadata_symmetry_0160 : FiniteChecks.Interval symmetry 160 176 :=
  FiniteChecks.interval_of_check symmetry 160 16 (by decide +kernel)
theorem metadata_symmetry_0176 : FiniteChecks.Interval symmetry 176 180 :=
  FiniteChecks.interval_of_check symmetry 176 4 (by decide +kernel)
theorem metadata_symmetry : FiniteChecks.Interval symmetry 0 blockCount :=
  (FiniteChecks.interval_append (symmetry) 0 96 180
  (FiniteChecks.interval_append (symmetry) 0 48 96
  (FiniteChecks.interval_append (symmetry) 0 16 48
  metadata_symmetry_0000
  (FiniteChecks.interval_append (symmetry) 16 32 48
  metadata_symmetry_0016
  metadata_symmetry_0032))
  (FiniteChecks.interval_append (symmetry) 48 64 96
  metadata_symmetry_0048
  (FiniteChecks.interval_append (symmetry) 64 80 96
  metadata_symmetry_0064
  metadata_symmetry_0080)))
  (FiniteChecks.interval_append (symmetry) 96 144 180
  (FiniteChecks.interval_append (symmetry) 96 112 144
  metadata_symmetry_0096
  (FiniteChecks.interval_append (symmetry) 112 128 144
  metadata_symmetry_0112
  metadata_symmetry_0128))
  (FiniteChecks.interval_append (symmetry) 144 160 180
  metadata_symmetry_0144
  (FiniteChecks.interval_append (symmetry) 160 176 180
  metadata_symmetry_0160
  metadata_symmetry_0176))))
theorem metadata_normalizers :
    RawFaceNormalizers.completeCheck 6 template root raw faceWitness = true := by decide +kernel
theorem metadata_root : RawFacetEmbedding.wellFormedCheck root = true := by decide +kernel
end Papers.RationalityTen.RootedCanonical.RootedSixBase00.T1

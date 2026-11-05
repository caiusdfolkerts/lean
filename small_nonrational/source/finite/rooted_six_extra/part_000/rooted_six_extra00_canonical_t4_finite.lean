module
prelude
public import RootedSixExtra00
public import RawKindedFacePlacement
public import RootedSixExtra00OutsideData
public import RawOutsidePlacement

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra00.T4
open ConcreteGrowth
abbrev blockCount : Nat := 160
noncomputable def template : Cell := ⟨10, 63, [3, 5, 6, 10, 12, 20, 24, 33, 36, 48], [7, 14, 28, 37, 52, 59]⟩
noncomputable def root : Cell := FacetUniverses.RootedSixExtra00.cells 0
noncomputable def records : Table (RawFacePlacement.Block × Nat) :=
(.branch 80
 (.branch 40
 (.branch 20
 (.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf (⟨2, 4, 5517840, 5517840, 361626105360, 361626105360⟩, 503127544))
 (.leaf (⟨2, 4, 5517840, 5517840, 361609328160, 361626104160⟩, 506273320)))
 (.branch 3
 (.leaf (⟨2, 4, 5517840, 5517840, 361592550945, 361626104070⟩, 509419096))
 (.branch 4
 (.leaf (⟨2, 4, 5517840, 5517840, 361340892720, 361626081120⟩, 517283536))
 (.leaf (⟨2, 4, 5517840, 5517840, 361324115505, 361626081030⟩, 520429312)))))
 (.branch 7
 (.branch 6
 (.leaf (⟨2, 4, 5517840, 5517840, 361055680050, 361626079350⟩, 528293752))
 (.leaf (⟨2, 4, 5517840, 5517840, 357029148225, 361625650950⟩, 536158192)))
 (.branch 8
 (.leaf (⟨2, 4, 5517840, 5517840, 356760712770, 361625649270⟩, 539303968))
 (.branch 9
 (.leaf (⟨2, 4, 5517840, 5517840, 352465745475, 361625618550⟩, 547168408))
 (.leaf (⟨2, 4, 5517840, 5517840, 288041236050, 361617784950⟩, 555032848))))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf (⟨2, 4, 5517840, 5517840, 283746268755, 361617754230⟩, 558178624))
 (.leaf (⟨2, 4, 5517840, 5517840, 215026792020, 361617201270⟩, 566043064)))
 (.branch 13
 (.leaf (⟨2, 4, 5517600, 5517600, 361626105360, 361626105360⟩, 505159184))
 (.branch 14
 (.leaf (⟨2, 4, 5517600, 5517600, 361609328160, 361626104160⟩, 508304960))
 (.leaf (⟨2, 4, 5517600, 5517600, 361592550945, 361626104070⟩, 511450736)))))
 (.branch 17
 (.branch 16
 (.leaf (⟨2, 4, 5517600, 5517600, 361340892720, 361626081120⟩, 519315176))
 (.leaf (⟨2, 4, 5517600, 5517600, 361324115505, 361626081030⟩, 522460952)))
 (.branch 18
 (.leaf (⟨2, 4, 5517600, 5517600, 361055680050, 361626079350⟩, 530325392))
 (.branch 19
 (.leaf (⟨2, 4, 5517600, 5517600, 357029148225, 361625650950⟩, 538189832))
 (.leaf (⟨2, 4, 5517600, 5517600, 356760712770, 361625649270⟩, 541335608)))))))
 (.branch 30
 (.branch 25
 (.branch 22
 (.branch 21
 (.leaf (⟨2, 4, 5517600, 5517600, 352465745475, 361625618550⟩, 549200048))
 (.leaf (⟨2, 4, 5517600, 5517600, 288041236050, 361617784950⟩, 557064488)))
 (.branch 23
 (.leaf (⟨2, 4, 5517600, 5517600, 283746268755, 361617754230⟩, 560210264))
 (.branch 24
 (.leaf (⟨2, 4, 5517600, 5517600, 215026792020, 361617201270⟩, 568074704))
 (.leaf (⟨2, 4, 5517345, 5517570, 361626105360, 361626105360⟩, 505486869)))))
 (.branch 27
 (.branch 26
 (.leaf (⟨2, 4, 5517345, 5517570, 361609328160, 361626104160⟩, 508632645))
 (.leaf (⟨2, 4, 5517345, 5517570, 361592550945, 361626104070⟩, 511778421)))
 (.branch 28
 (.leaf (⟨2, 4, 5517345, 5517570, 361340892720, 361626081120⟩, 519642861))
 (.branch 29
 (.leaf (⟨2, 4, 5517345, 5517570, 361324115505, 361626081030⟩, 522788637))
 (.leaf (⟨2, 4, 5517345, 5517570, 361055680050, 361626079350⟩, 530653077))))))
 (.branch 35
 (.branch 32
 (.branch 31
 (.leaf (⟨2, 4, 5517345, 5517570, 357029148225, 361625650950⟩, 538517517))
 (.leaf (⟨2, 4, 5517345, 5517570, 356760712770, 361625649270⟩, 541663293)))
 (.branch 33
 (.leaf (⟨2, 4, 5517345, 5517570, 352465745475, 361625618550⟩, 549527733))
 (.branch 34
 (.leaf (⟨2, 4, 5517345, 5517570, 288041236050, 361617784950⟩, 557392173))
 (.leaf (⟨2, 4, 5517345, 5517570, 283746268755, 361617754230⟩, 560537949)))))
 (.branch 37
 (.branch 36
 (.leaf (⟨2, 4, 5517345, 5517570, 215026792020, 361617201270⟩, 568402389))
 (.leaf (⟨3, 4, 5517840, 5517840, 361742426640, 434925761040⟩, 9469660348355730208895868552)))
 (.branch 38
 (.leaf (⟨3, 4, 5517840, 5517840, 361473991440, 434925741840⟩, 9672762985151280811104083760))
 (.branch 39
 (.leaf (⟨3, 4, 5517840, 5517840, 361205556000, 434925740400⟩, 9817836297148102669824237480))
 (.leaf (⟨3, 4, 5517840, 5517840, 356642153505, 434925371655⟩, 10020938933943653272032452688))))))))
 (.branch 60
 (.branch 50
 (.branch 45
 (.branch 42
 (.branch 41
 (.leaf (⟨3, 4, 5517840, 5517840, 352347186225, 434925344775⟩, 10166012245940475130752606408))
 (.leaf (⟨3, 4, 5517840, 5517840, 279332742450, 434918461575⟩, 10369114882736025732960821616)))
 (.branch 43
 (.leaf (⟨3, 4, 5517840, 5517840, 210613265730, 434917970055⟩, 10514188194732847591680975336))
 (.branch 44
 (.leaf (⟨3, 4, 5517840, 5517840, 141893788995, 434917935495⟩, 10601232181930940706913067568))
 (.leaf (⟨2, 4, 5513265, 5509890, 361626105360, 361626105360⟩, 503258625)))))
 (.branch 47
 (.branch 46
 (.leaf (⟨2, 4, 5513265, 5509890, 361609328160, 361626104160⟩, 506404401))
 (.leaf (⟨2, 4, 5513265, 5509890, 361592550945, 361626104070⟩, 509550177)))
 (.branch 48
 (.leaf (⟨2, 4, 5513265, 5509890, 361340892720, 361626081120⟩, 517414617))
 (.branch 49
 (.leaf (⟨2, 4, 5513265, 5509890, 361324115505, 361626081030⟩, 520560393))
 (.leaf (⟨2, 4, 5513265, 5509890, 361055680050, 361626079350⟩, 528424833))))))
 (.branch 55
 (.branch 52
 (.branch 51
 (.leaf (⟨2, 4, 5513265, 5509890, 357029148225, 361625650950⟩, 536289273))
 (.leaf (⟨2, 4, 5513265, 5509890, 356760712770, 361625649270⟩, 539435049)))
 (.branch 53
 (.leaf (⟨2, 4, 5513265, 5509890, 352465745475, 361625618550⟩, 547299489))
 (.branch 54
 (.leaf (⟨2, 4, 5513265, 5509890, 288041236050, 361617784950⟩, 555163929))
 (.leaf (⟨2, 4, 5513265, 5509890, 283746268755, 361617754230⟩, 558309705)))))
 (.branch 57
 (.branch 56
 (.leaf (⟨2, 4, 5513265, 5509890, 215026792020, 361617201270⟩, 566174145))
 (.leaf (⟨2, 4, 5509170, 5509170, 361626105360, 361626105360⟩, 504831523)))
 (.branch 58
 (.leaf (⟨2, 4, 5509170, 5509170, 361609328160, 361626104160⟩, 507977299))
 (.branch 59
 (.leaf (⟨2, 4, 5509170, 5509170, 361592550945, 361626104070⟩, 511123075))
 (.leaf (⟨2, 4, 5509170, 5509170, 361340892720, 361626081120⟩, 518987515)))))))
 (.branch 70
 (.branch 65
 (.branch 62
 (.branch 61
 (.leaf (⟨2, 4, 5509170, 5509170, 361324115505, 361626081030⟩, 522133291))
 (.leaf (⟨2, 4, 5509170, 5509170, 361055680050, 361626079350⟩, 529997731)))
 (.branch 63
 (.leaf (⟨2, 4, 5509170, 5509170, 357029148225, 361625650950⟩, 537862171))
 (.branch 64
 (.leaf (⟨2, 4, 5509170, 5509170, 356760712770, 361625649270⟩, 541007947))
 (.leaf (⟨2, 4, 5509170, 5509170, 352465745475, 361625618550⟩, 548872387)))))
 (.branch 67
 (.branch 66
 (.leaf (⟨2, 4, 5509170, 5509170, 288041236050, 361617784950⟩, 556736827))
 (.leaf (⟨2, 4, 5509170, 5509170, 283746268755, 361617754230⟩, 559882603)))
 (.branch 68
 (.leaf (⟨2, 4, 5509170, 5509170, 215026792020, 361617201270⟩, 567747043))
 (.branch 69
 (.leaf (⟨3, 4, 5505825, 5513475, 361742426640, 434925761040⟩, 9457570887244554690004197009))
 (.leaf (⟨3, 4, 5505825, 5513475, 361473991440, 434925741840⟩, 9660673524040105292212412217))))))
 (.branch 75
 (.branch 72
 (.branch 71
 (.leaf (⟨3, 4, 5505825, 5513475, 361205556000, 434925740400⟩, 9805746836036927150932565937))
 (.leaf (⟨3, 4, 5505825, 5513475, 356642153505, 434925371655⟩, 10008849472832477753140781145)))
 (.branch 73
 (.leaf (⟨3, 4, 5505825, 5513475, 352347186225, 434925344775⟩, 10153922784829299611860934865))
 (.branch 74
 (.leaf (⟨3, 4, 5505825, 5513475, 279332742450, 434918461575⟩, 10357025421624850214069150073))
 (.leaf (⟨3, 4, 5505825, 5513475, 210613265730, 434917970055⟩, 10502098733621672072789303793)))))
 (.branch 77
 (.branch 76
 (.leaf (⟨3, 4, 5505825, 5513475, 141893788995, 434917935495⟩, 10589142720819765188021396025))
 (.leaf (⟨2, 4, 5443650, 5324850, 361626105360, 361626105360⟩, 505093671)))
 (.branch 78
 (.leaf (⟨2, 4, 5443650, 5324850, 361609328160, 361626104160⟩, 508239447))
 (.branch 79
 (.leaf (⟨2, 4, 5443650, 5324850, 361592550945, 361626104070⟩, 511385223))
 (.leaf (⟨2, 4, 5443650, 5324850, 361340892720, 361626081120⟩, 519249663)))))))))
 (.branch 120
 (.branch 100
 (.branch 90
 (.branch 85
 (.branch 82
 (.branch 81
 (.leaf (⟨2, 4, 5443650, 5324850, 361324115505, 361626081030⟩, 522395439))
 (.leaf (⟨2, 4, 5443650, 5324850, 361055680050, 361626079350⟩, 530259879)))
 (.branch 83
 (.leaf (⟨2, 4, 5443650, 5324850, 357029148225, 361625650950⟩, 538124319))
 (.branch 84
 (.leaf (⟨2, 4, 5443650, 5324850, 356760712770, 361625649270⟩, 541270095))
 (.leaf (⟨2, 4, 5443650, 5324850, 352465745475, 361625618550⟩, 549134535)))))
 (.branch 87
 (.branch 86
 (.leaf (⟨2, 4, 5443650, 5324850, 288041236050, 361617784950⟩, 556998975))
 (.leaf (⟨2, 4, 5443650, 5324850, 283746268755, 361617754230⟩, 560144751)))
 (.branch 88
 (.leaf (⟨2, 4, 5443650, 5324850, 215026792020, 361617201270⟩, 568009191))
 (.branch 89
 (.leaf (⟨2, 4, 5378115, 5309490, 361626105360, 361626105360⟩, 503717384))
 (.leaf (⟨2, 4, 5378115, 5309490, 361609328160, 361626104160⟩, 506863160))))))
 (.branch 95
 (.branch 92
 (.branch 91
 (.leaf (⟨2, 4, 5378115, 5309490, 361592550945, 361626104070⟩, 510008936))
 (.leaf (⟨2, 4, 5378115, 5309490, 361340892720, 361626081120⟩, 517873376)))
 (.branch 93
 (.leaf (⟨2, 4, 5378115, 5309490, 361324115505, 361626081030⟩, 521019152))
 (.branch 94
 (.leaf (⟨2, 4, 5378115, 5309490, 361055680050, 361626079350⟩, 528883592))
 (.leaf (⟨2, 4, 5378115, 5309490, 357029148225, 361625650950⟩, 536748032)))))
 (.branch 97
 (.branch 96
 (.leaf (⟨2, 4, 5378115, 5309490, 356760712770, 361625649270⟩, 539893808))
 (.leaf (⟨2, 4, 5378115, 5309490, 352465745475, 361625618550⟩, 547758248)))
 (.branch 98
 (.leaf (⟨2, 4, 5378115, 5309490, 288041236050, 361617784950⟩, 555622688))
 (.branch 99
 (.leaf (⟨2, 4, 5378115, 5309490, 283746268755, 361617754230⟩, 558768464))
 (.leaf (⟨2, 4, 5378115, 5309490, 215026792020, 361617201270⟩, 566632904)))))))
 (.branch 110
 (.branch 105
 (.branch 102
 (.branch 101
 (.leaf (⟨3, 4, 5309490, 5378115, 361742426640, 434925761040⟩, 9451526387276786246186311320))
 (.leaf (⟨3, 4, 5309490, 5378115, 361473991440, 434925741840⟩, 9654629024072336848394526528)))
 (.branch 103
 (.leaf (⟨3, 4, 5309490, 5378115, 361205556000, 434925740400⟩, 9799702336069158707114680248))
 (.branch 104
 (.leaf (⟨3, 4, 5309490, 5378115, 356642153505, 434925371655⟩, 10002804972864709309322895456))
 (.leaf (⟨3, 4, 5309490, 5378115, 352347186225, 434925344775⟩, 10147878284861531168043049176)))))
 (.branch 107
 (.branch 106
 (.leaf (⟨3, 4, 5309490, 5378115, 279332742450, 434918461575⟩, 10350980921657081770251264384))
 (.leaf (⟨3, 4, 5309490, 5378115, 210613265730, 434917970055⟩, 10496054233653903628971418104)))
 (.branch 108
 (.leaf (⟨3, 4, 5309490, 5378115, 141893788995, 434917935495⟩, 10583098220851996744203510336))
 (.branch 109
 (.leaf (⟨2, 4, 4399440, 1393440, 361626105360, 361626105360⟩, 503193091))
 (.leaf (⟨2, 4, 4399440, 1393440, 361609328160, 361626104160⟩, 506338867))))))
 (.branch 115
 (.branch 112
 (.branch 111
 (.leaf (⟨2, 4, 4399440, 1393440, 361592550945, 361626104070⟩, 509484643))
 (.leaf (⟨2, 4, 4399440, 1393440, 361340892720, 361626081120⟩, 517349083)))
 (.branch 113
 (.leaf (⟨2, 4, 4399440, 1393440, 361324115505, 361626081030⟩, 520494859))
 (.branch 114
 (.leaf (⟨2, 4, 4399440, 1393440, 361055680050, 361626079350⟩, 528359299))
 (.leaf (⟨2, 4, 4399440, 1393440, 357029148225, 361625650950⟩, 536223739)))))
 (.branch 117
 (.branch 116
 (.leaf (⟨2, 4, 4399440, 1393440, 356760712770, 361625649270⟩, 539369515))
 (.leaf (⟨2, 4, 4399440, 1393440, 352465745475, 361625618550⟩, 547233955)))
 (.branch 118
 (.leaf (⟨2, 4, 4399440, 1393440, 288041236050, 361617784950⟩, 555098395))
 (.branch 119
 (.leaf (⟨2, 4, 4399440, 1393440, 283746268755, 361617754230⟩, 558244171))
 (.leaf (⟨2, 4, 4399440, 1393440, 215026792020, 361617201270⟩, 566108611))))))))
 (.branch 140
 (.branch 130
 (.branch 125
 (.branch 122
 (.branch 121
 (.leaf (⟨2, 4, 4395090, 1392690, 361626105360, 361626105360⟩, 504372764))
 (.leaf (⟨2, 4, 4395090, 1392690, 361609328160, 361626104160⟩, 507518540)))
 (.branch 123
 (.leaf (⟨2, 4, 4395090, 1392690, 361592550945, 361626104070⟩, 510664316))
 (.branch 124
 (.leaf (⟨2, 4, 4395090, 1392690, 361340892720, 361626081120⟩, 518528756))
 (.leaf (⟨2, 4, 4395090, 1392690, 361324115505, 361626081030⟩, 521674532)))))
 (.branch 127
 (.branch 126
 (.leaf (⟨2, 4, 4395090, 1392690, 361055680050, 361626079350⟩, 529538972))
 (.leaf (⟨2, 4, 4395090, 1392690, 357029148225, 361625650950⟩, 537403412)))
 (.branch 128
 (.leaf (⟨2, 4, 4395090, 1392690, 356760712770, 361625649270⟩, 540549188))
 (.branch 129
 (.leaf (⟨2, 4, 4395090, 1392690, 352465745475, 361625618550⟩, 548413628))
 (.leaf (⟨2, 4, 4395090, 1392690, 288041236050, 361617784950⟩, 556278068))))))
 (.branch 135
 (.branch 132
 (.branch 131
 (.leaf (⟨2, 4, 4395090, 1392690, 283746268755, 361617754230⟩, 559423844))
 (.leaf (⟨2, 4, 4395090, 1392690, 215026792020, 361617201270⟩, 567288284)))
 (.branch 133
 (.leaf (⟨3, 4, 4396320, 2441520, 361742426640, 434925761040⟩, 9456361942978758932778524307))
 (.branch 134
 (.leaf (⟨3, 4, 4396320, 2441520, 361473991440, 434925741840⟩, 9659464579774309534986739515))
 (.leaf (⟨3, 4, 4396320, 2441520, 361205556000, 434925740400⟩, 9804537891771131393706893235)))))
 (.branch 137
 (.branch 136
 (.leaf (⟨3, 4, 4396320, 2441520, 356642153505, 434925371655⟩, 10007640528566681995915108443))
 (.leaf (⟨3, 4, 4396320, 2441520, 352347186225, 434925344775⟩, 10152713840563503854635262163)))
 (.branch 138
 (.leaf (⟨3, 4, 4396320, 2441520, 279332742450, 434918461575⟩, 10355816477359054456843477371))
 (.branch 139
 (.leaf (⟨3, 4, 4396320, 2441520, 210613265730, 434917970055⟩, 10500889789355876315563631091))
 (.leaf (⟨3, 4, 4396320, 2441520, 141893788995, 434917935495⟩, 10587933776553969430795723323)))))))
 (.branch 150
 (.branch 145
 (.branch 142
 (.branch 141
 (.leaf (⟨2, 4, 3280980, 1070130, 361626105360, 361626105360⟩, 503913988))
 (.leaf (⟨2, 4, 3280980, 1070130, 361609328160, 361626104160⟩, 507059764)))
 (.branch 143
 (.leaf (⟨2, 4, 3280980, 1070130, 361592550945, 361626104070⟩, 510205540))
 (.branch 144
 (.leaf (⟨2, 4, 3280980, 1070130, 361340892720, 361626081120⟩, 518069980))
 (.leaf (⟨2, 4, 3280980, 1070130, 361324115505, 361626081030⟩, 521215756)))))
 (.branch 147
 (.branch 146
 (.leaf (⟨2, 4, 3280980, 1070130, 361055680050, 361626079350⟩, 529080196))
 (.leaf (⟨2, 4, 3280980, 1070130, 357029148225, 361625650950⟩, 536944636)))
 (.branch 148
 (.leaf (⟨2, 4, 3280980, 1070130, 356760712770, 361625649270⟩, 540090412))
 (.branch 149
 (.leaf (⟨2, 4, 3280980, 1070130, 352465745475, 361625618550⟩, 547954852))
 (.leaf (⟨2, 4, 3280980, 1070130, 288041236050, 361617784950⟩, 555819292))))))
 (.branch 155
 (.branch 152
 (.branch 151
 (.leaf (⟨2, 4, 3280980, 1070130, 283746268755, 361617754230⟩, 558965068))
 (.leaf (⟨2, 4, 3280980, 1070130, 215026792020, 361617201270⟩, 566829508)))
 (.branch 153
 (.leaf (⟨3, 4, 3212610, 2183235, 361742426640, 434925761040⟩, 9455153220076706762589085332))
 (.branch 154
 (.leaf (⟨3, 4, 3212610, 2183235, 361473991440, 434925741840⟩, 9658255856872257364797300540))
 (.leaf (⟨3, 4, 3212610, 2183235, 361205556000, 434925740400⟩, 9803329168869079223517454260)))))
 (.branch 157
 (.branch 156
 (.leaf (⟨3, 4, 3212610, 2183235, 356642153505, 434925371655⟩, 10006431805664629825725669468))
 (.leaf (⟨3, 4, 3212610, 2183235, 352347186225, 434925344775⟩, 10151505117661451684445823188)))
 (.branch 158
 (.leaf (⟨3, 4, 3212610, 2183235, 279332742450, 434918461575⟩, 10354607754457002286654038396))
 (.branch 159
 (.leaf (⟨3, 4, 3212610, 2183235, 210613265730, 434917970055⟩, 10499681066453824145374192116))
 (.leaf (⟨3, 4, 3212610, 2183235, 141893788995, 434917935495⟩, 10586725053651917260606284348))))))))))
noncomputable def raw (i : Fin blockCount) : RawFacePlacement.Block := (records.get i.val).1
noncomputable def witness (i : Fin blockCount) (code : Nat) : Fin 8824 :=
  Fin.ofNat 8824 (Nat.land (Nat.shiftRight (records.get i.val).2 (16 * code)) 65535)
noncomputable def faceTable : Table Nat :=
(.branch 20490
 (.branch 7194
 (.branch 5144
 (.branch 3112
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
 (.branch 3092
 (.branch 3090
 (.leaf 5)
 (.leaf 6))
 (.branch 3096
 (.leaf 7)
 (.branch 3108
 (.leaf 8)
 (.leaf 9)))))
 (.branch 5129
 (.branch 5123
 (.branch 3120
 (.leaf 10)
 (.leaf 11))
 (.branch 5125
 (.leaf 12)
 (.branch 5126
 (.leaf 13)
 (.leaf 14))))
 (.branch 5132
 (.branch 5130
 (.leaf 15)
 (.leaf 16))
 (.branch 5138
 (.leaf 17)
 (.branch 5140
 (.leaf 18)
 (.leaf 19))))))
 (.branch 6162
 (.branch 6149
 (.branch 5160
 (.branch 5156
 (.leaf 20)
 (.leaf 21))
 (.branch 5168
 (.leaf 22)
 (.branch 6147
 (.leaf 23)
 (.leaf 24))))
 (.branch 6153
 (.branch 6150
 (.leaf 25)
 (.leaf 26))
 (.branch 6154
 (.leaf 27)
 (.branch 6156
 (.leaf 28)
 (.leaf 29)))))
 (.branch 6192
 (.branch 6168
 (.branch 6164
 (.leaf 30)
 (.leaf 31))
 (.branch 6180
 (.leaf 32)
 (.branch 6184
 (.leaf 33)
 (.leaf 34))))
 (.branch 7179
 (.branch 7175
 (.leaf 35)
 (.leaf 36))
 (.branch 7181
 (.leaf 37)
 (.branch 7190
 (.leaf 38)
 (.leaf 39)))))))
 (.branch 12298
 (.branch 10258
 (.branch 10245
 (.branch 7220
 (.branch 7212
 (.leaf 40)
 (.leaf 41))
 (.branch 7224
 (.leaf 42)
 (.branch 10243
 (.leaf 43)
 (.leaf 44))))
 (.branch 10249
 (.branch 10246
 (.leaf 45)
 (.leaf 46))
 (.branch 10250
 (.leaf 47)
 (.branch 10252
 (.leaf 48)
 (.leaf 49)))))
 (.branch 10288
 (.branch 10264
 (.branch 10260
 (.leaf 50)
 (.leaf 51))
 (.branch 10276
 (.leaf 52)
 (.branch 10280
 (.leaf 53)
 (.leaf 54))))
 (.branch 12293
 (.branch 12291
 (.leaf 55)
 (.leaf 56))
 (.branch 12294
 (.leaf 57)
 (.branch 12297
 (.leaf 58)
 (.leaf 59))))))
 (.branch 14349
 (.branch 12324
 (.branch 12306
 (.branch 12300
 (.leaf 60)
 (.leaf 61))
 (.branch 12308
 (.leaf 62)
 (.branch 12312
 (.leaf 63)
 (.leaf 64))))
 (.branch 12336
 (.branch 12328
 (.leaf 65)
 (.leaf 66))
 (.branch 14343
 (.leaf 67)
 (.branch 14347
 (.leaf 68)
 (.leaf 69)))))
 (.branch 14392
 (.branch 14362
 (.branch 14358
 (.leaf 70)
 (.leaf 71))
 (.branch 14380
 (.leaf 72)
 (.branch 14388
 (.leaf 73)
 (.leaf 74))))
 (.branch 20485
 (.branch 20483
 (.leaf 75)
 (.leaf 76))
 (.branch 20486
 (.leaf 77)
 (.branch 20489
 (.leaf 78)
 (.leaf 79))))))))
 (.branch 36867
 (.branch 28679
 (.branch 24582
 (.branch 20516
 (.branch 20498
 (.branch 20492
 (.leaf 80)
 (.leaf 81))
 (.branch 20500
 (.leaf 82)
 (.branch 20504
 (.leaf 83)
 (.leaf 84))))
 (.branch 20528
 (.branch 20520
 (.leaf 85)
 (.leaf 86))
 (.branch 24579
 (.leaf 87)
 (.branch 24581
 (.leaf 88)
 (.leaf 89)))))
 (.branch 24596
 (.branch 24586
 (.branch 24585
 (.leaf 90)
 (.leaf 91))
 (.branch 24588
 (.leaf 92)
 (.branch 24594
 (.leaf 93)
 (.leaf 94))))
 (.branch 24612
 (.branch 24600
 (.leaf 95)
 (.leaf 96))
 (.branch 24616
 (.leaf 97)
 (.branch 24624
 (.leaf 98)
 (.leaf 99))))))
 (.branch 33798
 (.branch 28716
 (.branch 28685
 (.branch 28683
 (.leaf 100)
 (.leaf 101))
 (.branch 28694
 (.leaf 102)
 (.branch 28698
 (.leaf 103)
 (.leaf 104))))
 (.branch 28728
 (.branch 28724
 (.leaf 105)
 (.leaf 106))
 (.branch 33795
 (.leaf 107)
 (.branch 33797
 (.leaf 108)
 (.leaf 109)))))
 (.branch 33812
 (.branch 33802
 (.branch 33801
 (.leaf 110)
 (.leaf 111))
 (.branch 33804
 (.leaf 112)
 (.branch 33810
 (.leaf 113)
 (.leaf 114))))
 (.branch 33828
 (.branch 33816
 (.leaf 115)
 (.leaf 116))
 (.branch 33832
 (.leaf 117)
 (.branch 33840
 (.leaf 118)
 (.leaf 119)))))))
 (.branch 49155
 (.branch 36904
 (.branch 36876
 (.branch 36870
 (.branch 36869
 (.leaf 120)
 (.leaf 121))
 (.branch 36873
 (.leaf 122)
 (.branch 36874
 (.leaf 123)
 (.leaf 124))))
 (.branch 36884
 (.branch 36882
 (.leaf 125)
 (.leaf 126))
 (.branch 36888
 (.leaf 127)
 (.branch 36900
 (.leaf 128)
 (.leaf 129)))))
 (.branch 37910
 (.branch 37895
 (.branch 36912
 (.leaf 130)
 (.leaf 131))
 (.branch 37899
 (.leaf 132)
 (.branch 37901
 (.leaf 133)
 (.leaf 134))))
 (.branch 37932
 (.branch 37914
 (.leaf 135)
 (.leaf 136))
 (.branch 37940
 (.leaf 137)
 (.branch 37944
 (.leaf 138)
 (.leaf 139))))))
 (.branch 49192
 (.branch 49164
 (.branch 49158
 (.branch 49157
 (.leaf 140)
 (.leaf 141))
 (.branch 49161
 (.leaf 142)
 (.branch 49162
 (.leaf 143)
 (.leaf 144))))
 (.branch 49172
 (.branch 49170
 (.leaf 145)
 (.leaf 146))
 (.branch 49176
 (.leaf 147)
 (.branch 49188
 (.leaf 148)
 (.leaf 149)))))
 (.branch 53270
 (.branch 53255
 (.branch 49200
 (.leaf 150)
 (.leaf 151))
 (.branch 53259
 (.leaf 152)
 (.branch 53261
 (.leaf 153)
 (.leaf 154))))
 (.branch 53292
 (.branch 53274
 (.leaf 155)
 (.leaf 156))
 (.branch 53300
 (.leaf 157)
 (.branch 53304
 (.leaf 158)
 (.leaf 159)))))))))
noncomputable def faceWitness (s r : Nat) : Fin blockCount :=
  Fin.ofNat blockCount (faceTable.get (s * 1024 + r))
noncomputable def validity (i : Nat) : Bool :=
  RawFaceNormalizers.blockValidCheck 6 (raw (Fin.ofNat blockCount i))
noncomputable def placement (b : Fin blockCount) (code : Nat) : Bool :=
  RawKindedFacePlacement.check 6 (raw b) template root FacetUniverses.RootedSixExtra00.cells
    code 0 (witness b code)
noncomputable def test (i : Nat) : Bool :=
  let b := Fin.ofNat blockCount i
  FiniteChecks.checkRange (placement b)
    0 (RawFacePlacement.count (raw b).shared (raw b).shared)
noncomputable def symmetry (i : Nat) : Bool :=
  RawOutsidePlacement.blockCheck FacetUniverses.RootedSixExtra00.Outside.vertexCode root.vertices
    (raw (Fin.ofNat blockCount i))
end Papers.RationalityTen.RootedCanonical.RootedSixExtra00.T4

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra00.T4
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
end Papers.RationalityTen.RootedCanonical.RootedSixExtra00.T4

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra00.T4
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
end Papers.RationalityTen.RootedCanonical.RootedSixExtra00.T4

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra00.T4
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
theorem check_0136_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 136)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 136)) 0 6 (by decide +kernel)
theorem block_0136 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 136)) 0 6 :=
  check_0136_0000
theorem check_0137_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 137)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 137)) 0 6 (by decide +kernel)
theorem block_0137 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 137)) 0 6 :=
  check_0137_0000
theorem check_0138_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 138)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 138)) 0 6 (by decide +kernel)
theorem block_0138 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 138)) 0 6 :=
  check_0138_0000
theorem check_0139_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 139)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 139)) 0 6 (by decide +kernel)
theorem block_0139 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 139)) 0 6 :=
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
theorem check_0144_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 144)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 144)) 0 2 (by decide +kernel)
theorem block_0144 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 144)) 0 2 :=
  check_0144_0000
theorem check_0145_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 145)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 145)) 0 2 (by decide +kernel)
theorem block_0145 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 145)) 0 2 :=
  check_0145_0000
theorem check_0146_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 146)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 146)) 0 2 (by decide +kernel)
theorem block_0146 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 146)) 0 2 :=
  check_0146_0000
theorem check_0147_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 147)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 147)) 0 2 (by decide +kernel)
theorem block_0147 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 147)) 0 2 :=
  check_0147_0000
theorem check_0148_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 148)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 148)) 0 2 (by decide +kernel)
theorem block_0148 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 148)) 0 2 :=
  check_0148_0000
theorem check_0149_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 149)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 149)) 0 2 (by decide +kernel)
theorem block_0149 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 149)) 0 2 :=
  check_0149_0000
theorem check_0150_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 150)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 150)) 0 2 (by decide +kernel)
theorem block_0150 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 150)) 0 2 :=
  check_0150_0000
theorem check_0151_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 151)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 151)) 0 2 (by decide +kernel)
theorem block_0151 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 151)) 0 2 :=
  check_0151_0000
theorem check_0152_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 152)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 152)) 0 6 (by decide +kernel)
theorem block_0152 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 152)) 0 6 :=
  check_0152_0000
theorem check_0153_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 153)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 153)) 0 6 (by decide +kernel)
theorem block_0153 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 153)) 0 6 :=
  check_0153_0000
theorem check_0154_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 154)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 154)) 0 6 (by decide +kernel)
theorem block_0154 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 154)) 0 6 :=
  check_0154_0000
theorem check_0155_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 155)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 155)) 0 6 (by decide +kernel)
theorem block_0155 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 155)) 0 6 :=
  check_0155_0000
theorem check_0156_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 156)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 156)) 0 6 (by decide +kernel)
theorem block_0156 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 156)) 0 6 :=
  check_0156_0000
theorem check_0157_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 157)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 157)) 0 6 (by decide +kernel)
theorem block_0157 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 157)) 0 6 :=
  check_0157_0000
theorem check_0158_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 158)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 158)) 0 6 (by decide +kernel)
theorem block_0158 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 158)) 0 6 :=
  check_0158_0000
theorem check_0159_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 159)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 159)) 0 6 (by decide +kernel)
theorem block_0159 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 159)) 0 6 :=
  check_0159_0000
end Papers.RationalityTen.RootedCanonical.RootedSixExtra00.T4

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra00.T4
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
theorem metadata_validity : FiniteChecks.Interval validity 0 blockCount :=
  (FiniteChecks.interval_append (validity) 0 80 160
  (FiniteChecks.interval_append (validity) 0 32 80
  (FiniteChecks.interval_append (validity) 0 16 32
  metadata_validity_0000
  metadata_validity_0016)
  (FiniteChecks.interval_append (validity) 32 48 80
  metadata_validity_0032
  (FiniteChecks.interval_append (validity) 48 64 80
  metadata_validity_0048
  metadata_validity_0064)))
  (FiniteChecks.interval_append (validity) 80 112 160
  (FiniteChecks.interval_append (validity) 80 96 112
  metadata_validity_0080
  metadata_validity_0096)
  (FiniteChecks.interval_append (validity) 112 128 160
  metadata_validity_0112
  (FiniteChecks.interval_append (validity) 128 144 160
  metadata_validity_0128
  metadata_validity_0144))))
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
theorem metadata_symmetry : FiniteChecks.Interval symmetry 0 blockCount :=
  (FiniteChecks.interval_append (symmetry) 0 80 160
  (FiniteChecks.interval_append (symmetry) 0 32 80
  (FiniteChecks.interval_append (symmetry) 0 16 32
  metadata_symmetry_0000
  metadata_symmetry_0016)
  (FiniteChecks.interval_append (symmetry) 32 48 80
  metadata_symmetry_0032
  (FiniteChecks.interval_append (symmetry) 48 64 80
  metadata_symmetry_0048
  metadata_symmetry_0064)))
  (FiniteChecks.interval_append (symmetry) 80 112 160
  (FiniteChecks.interval_append (symmetry) 80 96 112
  metadata_symmetry_0080
  metadata_symmetry_0096)
  (FiniteChecks.interval_append (symmetry) 112 128 160
  metadata_symmetry_0112
  (FiniteChecks.interval_append (symmetry) 128 144 160
  metadata_symmetry_0128
  metadata_symmetry_0144))))
theorem metadata_normalizers :
    RawFaceNormalizers.completeCheck 6 template root raw faceWitness = true := by decide +kernel
theorem metadata_root : RawFacetEmbedding.wellFormedCheck root = true := by decide +kernel
end Papers.RationalityTen.RootedCanonical.RootedSixExtra00.T4

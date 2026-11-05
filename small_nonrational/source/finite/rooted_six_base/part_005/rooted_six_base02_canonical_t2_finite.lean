module
prelude
public import RootedSixBase02
public import RawKindedFacePlacement
public import RootedSixBase02OutsideData
public import RawOutsidePlacement

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase02.T2
open ConcreteGrowth
abbrev blockCount : Nat := 152
noncomputable def template : Cell := ⟨8, 63, [3, 5, 6, 9, 10, 17, 20, 24, 34, 36, 40, 48], [7, 11, 21, 25, 38, 42, 52, 56]⟩
noncomputable def root : Cell := FacetUniverses.RootedSixBase02.cells 0
noncomputable def records : Table (RawFacePlacement.Block × Nat) :=
(.branch 76
 (.branch 38
 (.branch 19
 (.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf (⟨2, 4, 5517840, 5517840, 361626105360, 361626105360⟩, 482680004))
 (.leaf (⟨2, 4, 5517840, 5517840, 361609328160, 361626104160⟩, 483466448)))
 (.branch 3
 (.leaf (⟨2, 4, 5517840, 5517840, 361592550945, 361626104070⟩, 484252892))
 (.leaf (⟨2, 4, 5517840, 5517840, 361340892720, 361626081120⟩, 486612224))))
 (.branch 6
 (.branch 5
 (.leaf (⟨2, 4, 5517840, 5517840, 361324115505, 361626081030⟩, 487398668))
 (.leaf (⟨2, 4, 5517840, 5517840, 356760712770, 361625649270⟩, 489758000)))
 (.branch 7
 (.leaf (⟨2, 4, 5517840, 5517840, 352465745475, 361625618550⟩, 490544444))
 (.branch 8
 (.leaf (⟨2, 4, 5517840, 5517840, 288309671505, 361617786630⟩, 491330888))
 (.leaf (⟨2, 4, 5517840, 5517840, 283746268755, 361617754230⟩, 492117332))))))
 (.branch 14
 (.branch 11
 (.branch 10
 (.leaf (⟨2, 4, 5517840, 5517840, 215026792020, 361617201270⟩, 494476664))
 (.leaf (⟨2, 4, 5517600, 5517600, 361626105360, 361626105360⟩, 482811078)))
 (.branch 12
 (.leaf (⟨2, 4, 5517600, 5517600, 361609328160, 361626104160⟩, 483597522))
 (.branch 13
 (.leaf (⟨2, 4, 5517600, 5517600, 361592550945, 361626104070⟩, 484383966))
 (.leaf (⟨2, 4, 5517600, 5517600, 361340892720, 361626081120⟩, 486743298)))))
 (.branch 16
 (.branch 15
 (.leaf (⟨2, 4, 5517600, 5517600, 361324115505, 361626081030⟩, 487529742))
 (.leaf (⟨2, 4, 5517600, 5517600, 356760712770, 361625649270⟩, 489889074)))
 (.branch 17
 (.leaf (⟨2, 4, 5517600, 5517600, 352465745475, 361625618550⟩, 490675518))
 (.branch 18
 (.leaf (⟨2, 4, 5517600, 5517600, 288309671505, 361617786630⟩, 491461962))
 (.leaf (⟨2, 4, 5517600, 5517600, 283746268755, 361617754230⟩, 492248406)))))))
 (.branch 28
 (.branch 23
 (.branch 21
 (.branch 20
 (.leaf (⟨2, 4, 5517600, 5517600, 215026792020, 361617201270⟩, 494607738))
 (.leaf (⟨2, 4, 5517345, 5517570, 361626105360, 361626105360⟩, 482942152)))
 (.branch 22
 (.leaf (⟨2, 4, 5517345, 5517570, 361609328160, 361626104160⟩, 483728596))
 (.leaf (⟨2, 4, 5517345, 5517570, 361592550945, 361626104070⟩, 484515040))))
 (.branch 25
 (.branch 24
 (.leaf (⟨2, 4, 5517345, 5517570, 361340892720, 361626081120⟩, 486874372))
 (.leaf (⟨2, 4, 5517345, 5517570, 361324115505, 361626081030⟩, 487660816)))
 (.branch 26
 (.leaf (⟨2, 4, 5517345, 5517570, 356760712770, 361625649270⟩, 490020148))
 (.branch 27
 (.leaf (⟨2, 4, 5517345, 5517570, 352465745475, 361625618550⟩, 490806592))
 (.leaf (⟨2, 4, 5517345, 5517570, 288309671505, 361617786630⟩, 491593036))))))
 (.branch 33
 (.branch 30
 (.branch 29
 (.leaf (⟨2, 4, 5517345, 5517570, 283746268755, 361617754230⟩, 492379480))
 (.leaf (⟨2, 4, 5517345, 5517570, 215026792020, 361617201270⟩, 494738812)))
 (.branch 31
 (.leaf (⟨3, 4, 5517840, 5517840, 361742426640, 434925761040⟩, 8952232257576216288545021160))
 (.branch 32
 (.leaf (⟨3, 4, 5517840, 5517840, 361473991440, 434925741840⟩, 9010261582374945032033082648))
 (.leaf (⟨3, 4, 5517840, 5517840, 283627709745, 434918463495⟩, 9097305569573038147265174880)))))
 (.branch 35
 (.branch 34
 (.leaf (⟨3, 4, 5517840, 5517840, 141893788995, 434917935495⟩, 9140827563172084704881220996))
 (.leaf (⟨2, 4, 5513520, 5509920, 361626105360, 361626105360⟩, 482811078)))
 (.branch 36
 (.leaf (⟨2, 4, 5513520, 5509920, 361609328160, 361626104160⟩, 483597522))
 (.branch 37
 (.leaf (⟨2, 4, 5513520, 5509920, 361592550945, 361626104070⟩, 484383966))
 (.leaf (⟨2, 4, 5513520, 5509920, 361340892720, 361626081120⟩, 486743298))))))))
 (.branch 57
 (.branch 47
 (.branch 42
 (.branch 40
 (.branch 39
 (.leaf (⟨2, 4, 5513520, 5509920, 361324115505, 361626081030⟩, 487529742))
 (.leaf (⟨2, 4, 5513520, 5509920, 356760712770, 361625649270⟩, 489889074)))
 (.branch 41
 (.leaf (⟨2, 4, 5513520, 5509920, 352465745475, 361625618550⟩, 490675518))
 (.leaf (⟨2, 4, 5513520, 5509920, 288309671505, 361617786630⟩, 491461962))))
 (.branch 44
 (.branch 43
 (.leaf (⟨2, 4, 5513520, 5509920, 283746268755, 361617754230⟩, 492248406))
 (.leaf (⟨2, 4, 5513520, 5509920, 215026792020, 361617201270⟩, 494607738)))
 (.branch 45
 (.leaf (⟨2, 4, 5513265, 5509890, 361626105360, 361626105360⟩, 482942152))
 (.branch 46
 (.leaf (⟨2, 4, 5513265, 5509890, 361609328160, 361626104160⟩, 483728596))
 (.leaf (⟨2, 4, 5513265, 5509890, 361592550945, 361626104070⟩, 484515040))))))
 (.branch 52
 (.branch 49
 (.branch 48
 (.leaf (⟨2, 4, 5513265, 5509890, 361340892720, 361626081120⟩, 486874372))
 (.leaf (⟨2, 4, 5513265, 5509890, 361324115505, 361626081030⟩, 487660816)))
 (.branch 50
 (.leaf (⟨2, 4, 5513265, 5509890, 356760712770, 361625649270⟩, 490020148))
 (.branch 51
 (.leaf (⟨2, 4, 5513265, 5509890, 352465745475, 361625618550⟩, 490806592))
 (.leaf (⟨2, 4, 5513265, 5509890, 288309671505, 361617786630⟩, 491593036)))))
 (.branch 54
 (.branch 53
 (.leaf (⟨2, 4, 5513265, 5509890, 283746268755, 361617754230⟩, 492379480))
 (.leaf (⟨2, 4, 5513265, 5509890, 215026792020, 361617201270⟩, 494738812)))
 (.branch 55
 (.leaf (⟨3, 4, 5514000, 5514000, 361742426640, 434925761040⟩, 8952232257576216288545021160))
 (.branch 56
 (.leaf (⟨3, 4, 5514000, 5514000, 361473991440, 434925741840⟩, 9010261582374945032033082648))
 (.leaf (⟨3, 4, 5514000, 5514000, 283627709745, 434918463495⟩, 9097305569573038147265174880)))))))
 (.branch 66
 (.branch 61
 (.branch 59
 (.branch 58
 (.leaf (⟨3, 4, 5514000, 5514000, 141893788995, 434917935495⟩, 9140827563172084704881220996))
 (.leaf (⟨2, 4, 5448000, 5325600, 361626105360, 361626105360⟩, 483073226)))
 (.branch 60
 (.leaf (⟨2, 4, 5448000, 5325600, 361609328160, 361626104160⟩, 483859670))
 (.leaf (⟨2, 4, 5448000, 5325600, 361592550945, 361626104070⟩, 484646114))))
 (.branch 63
 (.branch 62
 (.leaf (⟨2, 4, 5448000, 5325600, 361340892720, 361626081120⟩, 487005446))
 (.leaf (⟨2, 4, 5448000, 5325600, 361324115505, 361626081030⟩, 487791890)))
 (.branch 64
 (.leaf (⟨2, 4, 5448000, 5325600, 356760712770, 361625649270⟩, 490151222))
 (.branch 65
 (.leaf (⟨2, 4, 5448000, 5325600, 352465745475, 361625618550⟩, 490937666))
 (.leaf (⟨2, 4, 5448000, 5325600, 288309671505, 361617786630⟩, 491724110))))))
 (.branch 71
 (.branch 68
 (.branch 67
 (.leaf (⟨2, 4, 5448000, 5325600, 283746268755, 361617754230⟩, 492510554))
 (.leaf (⟨2, 4, 5448000, 5325600, 215026792020, 361617201270⟩, 494869886)))
 (.branch 69
 (.leaf (⟨2, 4, 5443650, 5324850, 361626105360, 361626105360⟩, 482942152))
 (.branch 70
 (.leaf (⟨2, 4, 5443650, 5324850, 361609328160, 361626104160⟩, 483728596))
 (.leaf (⟨2, 4, 5443650, 5324850, 361592550945, 361626104070⟩, 484515040)))))
 (.branch 73
 (.branch 72
 (.leaf (⟨2, 4, 5443650, 5324850, 361340892720, 361626081120⟩, 486874372))
 (.leaf (⟨2, 4, 5443650, 5324850, 361324115505, 361626081030⟩, 487660816)))
 (.branch 74
 (.leaf (⟨2, 4, 5443650, 5324850, 356760712770, 361625649270⟩, 490020148))
 (.branch 75
 (.leaf (⟨2, 4, 5443650, 5324850, 352465745475, 361625618550⟩, 490806592))
 (.leaf (⟨2, 4, 5443650, 5324850, 288309671505, 361617786630⟩, 491593036)))))))))
 (.branch 114
 (.branch 95
 (.branch 85
 (.branch 80
 (.branch 78
 (.branch 77
 (.leaf (⟨2, 4, 5443650, 5324850, 283746268755, 361617754230⟩, 492379480))
 (.leaf (⟨2, 4, 5443650, 5324850, 215026792020, 361617201270⟩, 494738812)))
 (.branch 79
 (.leaf (⟨3, 4, 5444640, 5390640, 361742426640, 434925761040⟩, 8952232257576216288545021160))
 (.leaf (⟨3, 4, 5444640, 5390640, 361473991440, 434925741840⟩, 9010261582374945032033082648))))
 (.branch 82
 (.branch 81
 (.leaf (⟨3, 4, 5444640, 5390640, 283627709745, 434918463495⟩, 9097305569573038147265174880))
 (.leaf (⟨3, 4, 5444640, 5390640, 141893788995, 434917935495⟩, 9140827563172084704881220996)))
 (.branch 83
 (.leaf (⟨2, 4, 5378115, 5309490, 361626105360, 361626105360⟩, 482942152))
 (.branch 84
 (.leaf (⟨2, 4, 5378115, 5309490, 361609328160, 361626104160⟩, 483728596))
 (.leaf (⟨2, 4, 5378115, 5309490, 361592550945, 361626104070⟩, 484515040))))))
 (.branch 90
 (.branch 87
 (.branch 86
 (.leaf (⟨2, 4, 5378115, 5309490, 361340892720, 361626081120⟩, 486874372))
 (.leaf (⟨2, 4, 5378115, 5309490, 361324115505, 361626081030⟩, 487660816)))
 (.branch 88
 (.leaf (⟨2, 4, 5378115, 5309490, 356760712770, 361625649270⟩, 490020148))
 (.branch 89
 (.leaf (⟨2, 4, 5378115, 5309490, 352465745475, 361625618550⟩, 490806592))
 (.leaf (⟨2, 4, 5378115, 5309490, 288309671505, 361617786630⟩, 491593036)))))
 (.branch 92
 (.branch 91
 (.leaf (⟨2, 4, 5378115, 5309490, 283746268755, 361617754230⟩, 492379480))
 (.leaf (⟨2, 4, 5378115, 5309490, 215026792020, 361617201270⟩, 494738812)))
 (.branch 93
 (.leaf (⟨3, 4, 5379120, 5379120, 361742426640, 434925761040⟩, 8952232257576216288545021160))
 (.branch 94
 (.leaf (⟨3, 4, 5379120, 5379120, 361473991440, 434925741840⟩, 9010261582374945032033082648))
 (.leaf (⟨3, 4, 5379120, 5379120, 283627709745, 434918463495⟩, 9097305569573038147265174880)))))))
 (.branch 104
 (.branch 99
 (.branch 97
 (.branch 96
 (.leaf (⟨3, 4, 5379120, 5379120, 141893788995, 434917935495⟩, 9140827563172084704881220996))
 (.leaf (⟨2, 4, 4399185, 1393410, 361626105360, 361626105360⟩, 483073226)))
 (.branch 98
 (.leaf (⟨2, 4, 4399185, 1393410, 361609328160, 361626104160⟩, 483859670))
 (.leaf (⟨2, 4, 4399185, 1393410, 361592550945, 361626104070⟩, 484646114))))
 (.branch 101
 (.branch 100
 (.leaf (⟨2, 4, 4399185, 1393410, 361340892720, 361626081120⟩, 487005446))
 (.leaf (⟨2, 4, 4399185, 1393410, 361324115505, 361626081030⟩, 487791890)))
 (.branch 102
 (.leaf (⟨2, 4, 4399185, 1393410, 356760712770, 361625649270⟩, 490151222))
 (.branch 103
 (.leaf (⟨2, 4, 4399185, 1393410, 352465745475, 361625618550⟩, 490937666))
 (.leaf (⟨2, 4, 4399185, 1393410, 288309671505, 361617786630⟩, 491724110))))))
 (.branch 109
 (.branch 106
 (.branch 105
 (.leaf (⟨2, 4, 4399185, 1393410, 283746268755, 361617754230⟩, 492510554))
 (.leaf (⟨2, 4, 4399185, 1393410, 215026792020, 361617201270⟩, 494869886)))
 (.branch 107
 (.leaf (⟨2, 4, 4395090, 1392690, 361626105360, 361626105360⟩, 483204300))
 (.branch 108
 (.leaf (⟨2, 4, 4395090, 1392690, 361609328160, 361626104160⟩, 483990744))
 (.leaf (⟨2, 4, 4395090, 1392690, 361592550945, 361626104070⟩, 484777188)))))
 (.branch 111
 (.branch 110
 (.leaf (⟨2, 4, 4395090, 1392690, 361340892720, 361626081120⟩, 487136520))
 (.leaf (⟨2, 4, 4395090, 1392690, 361324115505, 361626081030⟩, 487922964)))
 (.branch 112
 (.leaf (⟨2, 4, 4395090, 1392690, 356760712770, 361625649270⟩, 490282296))
 (.branch 113
 (.leaf (⟨2, 4, 4395090, 1392690, 352465745475, 361625618550⟩, 491068740))
 (.leaf (⟨2, 4, 4395090, 1392690, 288309671505, 361617786630⟩, 491855184))))))))
 (.branch 133
 (.branch 123
 (.branch 118
 (.branch 116
 (.branch 115
 (.leaf (⟨2, 4, 4395090, 1392690, 283746268755, 361617754230⟩, 492641628))
 (.leaf (⟨2, 4, 4395090, 1392690, 215026792020, 361617201270⟩, 495000960)))
 (.branch 117
 (.leaf (⟨3, 4, 4392225, 2441475, 361742426640, 434925761040⟩, 8952232257576216288545021160))
 (.leaf (⟨3, 4, 4392225, 2441475, 361473991440, 434925741840⟩, 9010261582374945032033082648))))
 (.branch 120
 (.branch 119
 (.leaf (⟨3, 4, 4392225, 2441475, 283627709745, 434918463495⟩, 9097305569573038147265174880))
 (.leaf (⟨3, 4, 4392225, 2441475, 141893788995, 434917935495⟩, 9140827563172084704881220996)))
 (.branch 121
 (.leaf (⟨2, 4, 4329555, 1377330, 361626105360, 361626105360⟩, 483204300))
 (.branch 122
 (.leaf (⟨2, 4, 4329555, 1377330, 361609328160, 361626104160⟩, 483990744))
 (.leaf (⟨2, 4, 4329555, 1377330, 361592550945, 361626104070⟩, 484777188))))))
 (.branch 128
 (.branch 125
 (.branch 124
 (.leaf (⟨2, 4, 4329555, 1377330, 361340892720, 361626081120⟩, 487136520))
 (.leaf (⟨2, 4, 4329555, 1377330, 361324115505, 361626081030⟩, 487922964)))
 (.branch 126
 (.leaf (⟨2, 4, 4329555, 1377330, 356760712770, 361625649270⟩, 490282296))
 (.branch 127
 (.leaf (⟨2, 4, 4329555, 1377330, 352465745475, 361625618550⟩, 491068740))
 (.leaf (⟨2, 4, 4329555, 1377330, 288309671505, 361617786630⟩, 491855184)))))
 (.branch 130
 (.branch 129
 (.leaf (⟨2, 4, 4329555, 1377330, 283746268755, 361617754230⟩, 492641628))
 (.leaf (⟨2, 4, 4329555, 1377330, 215026792020, 361617201270⟩, 495000960)))
 (.branch 131
 (.leaf (⟨3, 4, 4326705, 2429955, 361742426640, 434925761040⟩, 8952232257576216288545021160))
 (.branch 132
 (.leaf (⟨3, 4, 4326705, 2429955, 361473991440, 434925741840⟩, 9010261582374945032033082648))
 (.leaf (⟨3, 4, 4326705, 2429955, 283627709745, 434918463495⟩, 9097305569573038147265174880)))))))
 (.branch 142
 (.branch 137
 (.branch 135
 (.branch 134
 (.leaf (⟨3, 4, 4326705, 2429955, 141893788995, 434917935495⟩, 9140827563172084704881220996))
 (.leaf (⟨2, 4, 3280980, 1070130, 361626105360, 361626105360⟩, 483335374)))
 (.branch 136
 (.leaf (⟨2, 4, 3280980, 1070130, 361609328160, 361626104160⟩, 484121818))
 (.leaf (⟨2, 4, 3280980, 1070130, 361592550945, 361626104070⟩, 484908262))))
 (.branch 139
 (.branch 138
 (.leaf (⟨2, 4, 3280980, 1070130, 361340892720, 361626081120⟩, 487267594))
 (.leaf (⟨2, 4, 3280980, 1070130, 361324115505, 361626081030⟩, 488054038)))
 (.branch 140
 (.leaf (⟨2, 4, 3280980, 1070130, 356760712770, 361625649270⟩, 490413370))
 (.branch 141
 (.leaf (⟨2, 4, 3280980, 1070130, 352465745475, 361625618550⟩, 491199814))
 (.leaf (⟨2, 4, 3280980, 1070130, 288309671505, 361617786630⟩, 491986258))))))
 (.branch 147
 (.branch 144
 (.branch 143
 (.leaf (⟨2, 4, 3280980, 1070130, 283746268755, 361617754230⟩, 492772702))
 (.leaf (⟨2, 4, 3280980, 1070130, 215026792020, 361617201270⟩, 495132034)))
 (.branch 145
 (.leaf (⟨3, 4, 3212610, 2183235, 361742426640, 434925761040⟩, 8952232257576216288545021160))
 (.branch 146
 (.leaf (⟨3, 4, 3212610, 2183235, 361473991440, 434925741840⟩, 9010261582374945032033082648))
 (.leaf (⟨3, 4, 3212610, 2183235, 283627709745, 434918463495⟩, 9097305569573038147265174880)))))
 (.branch 149
 (.branch 148
 (.leaf (⟨3, 4, 3212610, 2183235, 141893788995, 434917935495⟩, 9140827563172084704881220996))
 (.leaf (⟨3, 4, 2164035, 2164035, 361742426640, 434925761040⟩, 8952232257576216288545021160)))
 (.branch 150
 (.leaf (⟨3, 4, 2164035, 2164035, 361473991440, 434925741840⟩, 9010261582374945032033082648))
 (.branch 151
 (.leaf (⟨3, 4, 2164035, 2164035, 283627709745, 434918463495⟩, 9097305569573038147265174880))
 (.leaf (⟨3, 4, 2164035, 2164035, 141893788995, 434917935495⟩, 9140827563172084704881220996))))))))))
noncomputable def raw (i : Fin blockCount) : RawFacePlacement.Block := (records.get i.val).1
noncomputable def witness (i : Fin blockCount) (code : Nat) : Fin 8084 :=
  Fin.ofNat 8084 (Nat.land (Nat.shiftRight (records.get i.val).2 (16 * code)) 65535)
noncomputable def faceTable : Table Nat :=
(.branch 20520
 (.branch 9226
 (.branch 5168
 (.branch 3120
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
 (.branch 3112
 (.leaf 7)
 (.leaf 8)))))
 (.branch 5130
 (.branch 5125
 (.branch 5123
 (.leaf 9)
 (.leaf 10))
 (.branch 5126
 (.leaf 11)
 (.branch 5129
 (.leaf 12)
 (.leaf 13))))
 (.branch 5144
 (.branch 5140
 (.leaf 14)
 (.leaf 15))
 (.branch 5154
 (.leaf 16)
 (.branch 5160
 (.leaf 17)
 (.leaf 18))))))
 (.branch 6184
 (.branch 6153
 (.branch 6149
 (.branch 6147
 (.leaf 19)
 (.leaf 20))
 (.branch 6150
 (.leaf 21)
 (.leaf 22)))
 (.branch 6164
 (.branch 6154
 (.leaf 23)
 (.leaf 24))
 (.branch 6168
 (.leaf 25)
 (.branch 6178
 (.leaf 26)
 (.leaf 27)))))
 (.branch 7224
 (.branch 7175
 (.branch 6192
 (.leaf 28)
 (.leaf 29))
 (.branch 7179
 (.leaf 30)
 (.branch 7210
 (.leaf 31)
 (.leaf 32))))
 (.branch 9221
 (.branch 9219
 (.leaf 33)
 (.leaf 34))
 (.branch 9222
 (.leaf 35)
 (.branch 9225
 (.leaf 36)
 (.leaf 37)))))))
 (.branch 11320
 (.branch 10249
 (.branch 9256
 (.branch 9240
 (.branch 9236
 (.leaf 38)
 (.leaf 39))
 (.branch 9250
 (.leaf 40)
 (.leaf 41)))
 (.branch 10243
 (.branch 9264
 (.leaf 42)
 (.leaf 43))
 (.branch 10245
 (.leaf 44)
 (.branch 10246
 (.leaf 45)
 (.leaf 46)))))
 (.branch 10280
 (.branch 10260
 (.branch 10250
 (.leaf 47)
 (.leaf 48))
 (.branch 10264
 (.leaf 49)
 (.branch 10274
 (.leaf 50)
 (.leaf 51))))
 (.branch 11271
 (.branch 10288
 (.leaf 52)
 (.leaf 53))
 (.branch 11275
 (.leaf 54)
 (.branch 11306
 (.leaf 55)
 (.leaf 56))))))
 (.branch 17448
 (.branch 17417
 (.branch 17413
 (.branch 17411
 (.leaf 57)
 (.leaf 58))
 (.branch 17414
 (.leaf 59)
 (.leaf 60)))
 (.branch 17428
 (.branch 17418
 (.leaf 61)
 (.leaf 62))
 (.branch 17432
 (.leaf 63)
 (.branch 17442
 (.leaf 64)
 (.leaf 65)))))
 (.branch 20489
 (.branch 20483
 (.branch 17456
 (.leaf 66)
 (.leaf 67))
 (.branch 20485
 (.leaf 68)
 (.branch 20486
 (.leaf 69)
 (.leaf 70))))
 (.branch 20500
 (.branch 20490
 (.leaf 71)
 (.leaf 72))
 (.branch 20504
 (.leaf 73)
 (.branch 20514
 (.leaf 74)
 (.leaf 75))))))))
 (.branch 36904
 (.branch 25656
 (.branch 24585
 (.branch 21546
 (.branch 21511
 (.branch 20528
 (.leaf 76)
 (.leaf 77))
 (.branch 21515
 (.leaf 78)
 (.leaf 79)))
 (.branch 24579
 (.branch 21560
 (.leaf 80)
 (.leaf 81))
 (.branch 24581
 (.leaf 82)
 (.branch 24582
 (.leaf 83)
 (.leaf 84)))))
 (.branch 24616
 (.branch 24596
 (.branch 24586
 (.leaf 85)
 (.leaf 86))
 (.branch 24600
 (.leaf 87)
 (.branch 24610
 (.leaf 88)
 (.leaf 89))))
 (.branch 25607
 (.branch 24624
 (.leaf 90)
 (.leaf 91))
 (.branch 25611
 (.leaf 92)
 (.branch 25642
 (.leaf 93)
 (.leaf 94))))))
 (.branch 34856
 (.branch 34825
 (.branch 34821
 (.branch 34819
 (.leaf 95)
 (.leaf 96))
 (.branch 34822
 (.leaf 97)
 (.leaf 98)))
 (.branch 34836
 (.branch 34826
 (.leaf 99)
 (.leaf 100))
 (.branch 34840
 (.leaf 101)
 (.branch 34850
 (.leaf 102)
 (.leaf 103)))))
 (.branch 36873
 (.branch 36867
 (.branch 34864
 (.leaf 104)
 (.leaf 105))
 (.branch 36869
 (.leaf 106)
 (.branch 36870
 (.leaf 107)
 (.leaf 108))))
 (.branch 36884
 (.branch 36874
 (.leaf 109)
 (.leaf 110))
 (.branch 36888
 (.leaf 111)
 (.branch 36898
 (.leaf 112)
 (.leaf 113)))))))
 (.branch 43064
 (.branch 40969
 (.branch 38954
 (.branch 38919
 (.branch 36912
 (.leaf 114)
 (.leaf 115))
 (.branch 38923
 (.leaf 116)
 (.leaf 117)))
 (.branch 40963
 (.branch 38968
 (.leaf 118)
 (.leaf 119))
 (.branch 40965
 (.leaf 120)
 (.branch 40966
 (.leaf 121)
 (.leaf 122)))))
 (.branch 41000
 (.branch 40980
 (.branch 40970
 (.leaf 123)
 (.leaf 124))
 (.branch 40984
 (.leaf 125)
 (.branch 40994
 (.leaf 126)
 (.leaf 127))))
 (.branch 43015
 (.branch 41008
 (.leaf 128)
 (.leaf 129))
 (.branch 43019
 (.leaf 130)
 (.branch 43050
 (.leaf 131)
 (.leaf 132))))))
 (.branch 49192
 (.branch 49161
 (.branch 49157
 (.branch 49155
 (.leaf 133)
 (.leaf 134))
 (.branch 49158
 (.leaf 135)
 (.leaf 136)))
 (.branch 49172
 (.branch 49162
 (.leaf 137)
 (.leaf 138))
 (.branch 49176
 (.leaf 139)
 (.branch 49186
 (.leaf 140)
 (.leaf 141)))))
 (.branch 53304
 (.branch 53255
 (.branch 49200
 (.leaf 142)
 (.leaf 143))
 (.branch 53259
 (.leaf 144)
 (.branch 53290
 (.leaf 145)
 (.leaf 146))))
 (.branch 57355
 (.branch 57351
 (.leaf 147)
 (.leaf 148))
 (.branch 57386
 (.leaf 149)
 (.branch 57400
 (.leaf 150)
 (.leaf 151)))))))))
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
end Papers.RationalityTen.RootedCanonical.RootedSixBase02.T2

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase02.T2
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
theorem check_0054_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 54)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 54)) 0 6 (by decide +kernel)
theorem block_0054 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 54)) 0 6 :=
  check_0054_0000
theorem check_0055_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 55)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 55)) 0 6 (by decide +kernel)
theorem block_0055 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 55)) 0 6 :=
  check_0055_0000
theorem check_0056_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 56)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 56)) 0 6 (by decide +kernel)
theorem block_0056 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 56)) 0 6 :=
  check_0056_0000
theorem check_0057_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 57)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 57)) 0 6 (by decide +kernel)
theorem block_0057 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 57)) 0 6 :=
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
end Papers.RationalityTen.RootedCanonical.RootedSixBase02.T2

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase02.T2
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
theorem check_0078_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 78)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 78)) 0 6 (by decide +kernel)
theorem block_0078 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 78)) 0 6 :=
  check_0078_0000
theorem check_0079_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 79)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 79)) 0 6 (by decide +kernel)
theorem block_0079 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 79)) 0 6 :=
  check_0079_0000
theorem check_0080_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 80)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 80)) 0 6 (by decide +kernel)
theorem block_0080 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 80)) 0 6 :=
  check_0080_0000
theorem check_0081_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 81)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 81)) 0 6 (by decide +kernel)
theorem block_0081 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 81)) 0 6 :=
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
theorem check_0092_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 92)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 92)) 0 6 (by decide +kernel)
theorem block_0092 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 92)) 0 6 :=
  check_0092_0000
theorem check_0093_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 93)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 93)) 0 6 (by decide +kernel)
theorem block_0093 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 93)) 0 6 :=
  check_0093_0000
theorem check_0094_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 94)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 94)) 0 6 (by decide +kernel)
theorem block_0094 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 94)) 0 6 :=
  check_0094_0000
theorem check_0095_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 95)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 95)) 0 6 (by decide +kernel)
theorem block_0095 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 95)) 0 6 :=
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
theorem check_0100_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 100)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 100)) 0 2 (by decide +kernel)
theorem block_0100 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 100)) 0 2 :=
  check_0100_0000
theorem check_0101_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 101)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 101)) 0 2 (by decide +kernel)
theorem block_0101 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 101)) 0 2 :=
  check_0101_0000
theorem check_0102_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 102)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 102)) 0 2 (by decide +kernel)
theorem block_0102 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 102)) 0 2 :=
  check_0102_0000
theorem check_0103_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 103)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 103)) 0 2 (by decide +kernel)
theorem block_0103 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 103)) 0 2 :=
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
theorem check_0114_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 114)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 114)) 0 2 (by decide +kernel)
theorem block_0114 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 114)) 0 2 :=
  check_0114_0000
theorem check_0115_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 115)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 115)) 0 2 (by decide +kernel)
theorem block_0115 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 115)) 0 2 :=
  check_0115_0000
theorem check_0116_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 116)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 116)) 0 6 (by decide +kernel)
theorem block_0116 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 116)) 0 6 :=
  check_0116_0000
theorem check_0117_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 117)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 117)) 0 6 (by decide +kernel)
theorem block_0117 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 117)) 0 6 :=
  check_0117_0000
theorem check_0118_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 118)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 118)) 0 6 (by decide +kernel)
theorem block_0118 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 118)) 0 6 :=
  check_0118_0000
theorem check_0119_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 119)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 119)) 0 6 (by decide +kernel)
theorem block_0119 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 119)) 0 6 :=
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
end Papers.RationalityTen.RootedCanonical.RootedSixBase02.T2

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase02.T2
theorem check_0128_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 128)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 128)) 0 2 (by decide +kernel)
theorem block_0128 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 128)) 0 2 :=
  check_0128_0000
theorem check_0129_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 129)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 129)) 0 2 (by decide +kernel)
theorem block_0129 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 129)) 0 2 :=
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
end Papers.RationalityTen.RootedCanonical.RootedSixBase02.T2

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase02.T2
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
theorem metadata_validity_0144 : FiniteChecks.Interval validity 144 152 :=
  FiniteChecks.interval_of_check validity 144 8 (by decide +kernel)
theorem metadata_validity : FiniteChecks.Interval validity 0 blockCount :=
  (FiniteChecks.interval_append (validity) 0 80 152
  (FiniteChecks.interval_append (validity) 0 32 80
  (FiniteChecks.interval_append (validity) 0 16 32
  metadata_validity_0000
  metadata_validity_0016)
  (FiniteChecks.interval_append (validity) 32 48 80
  metadata_validity_0032
  (FiniteChecks.interval_append (validity) 48 64 80
  metadata_validity_0048
  metadata_validity_0064)))
  (FiniteChecks.interval_append (validity) 80 112 152
  (FiniteChecks.interval_append (validity) 80 96 112
  metadata_validity_0080
  metadata_validity_0096)
  (FiniteChecks.interval_append (validity) 112 128 152
  metadata_validity_0112
  (FiniteChecks.interval_append (validity) 128 144 152
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
theorem metadata_symmetry_0144 : FiniteChecks.Interval symmetry 144 152 :=
  FiniteChecks.interval_of_check symmetry 144 8 (by decide +kernel)
theorem metadata_symmetry : FiniteChecks.Interval symmetry 0 blockCount :=
  (FiniteChecks.interval_append (symmetry) 0 80 152
  (FiniteChecks.interval_append (symmetry) 0 32 80
  (FiniteChecks.interval_append (symmetry) 0 16 32
  metadata_symmetry_0000
  metadata_symmetry_0016)
  (FiniteChecks.interval_append (symmetry) 32 48 80
  metadata_symmetry_0032
  (FiniteChecks.interval_append (symmetry) 48 64 80
  metadata_symmetry_0048
  metadata_symmetry_0064)))
  (FiniteChecks.interval_append (symmetry) 80 112 152
  (FiniteChecks.interval_append (symmetry) 80 96 112
  metadata_symmetry_0080
  metadata_symmetry_0096)
  (FiniteChecks.interval_append (symmetry) 112 128 152
  metadata_symmetry_0112
  (FiniteChecks.interval_append (symmetry) 128 144 152
  metadata_symmetry_0128
  metadata_symmetry_0144))))
theorem metadata_normalizers :
    RawFaceNormalizers.completeCheck 6 template root raw faceWitness = true := by decide +kernel
theorem metadata_root : RawFacetEmbedding.wellFormedCheck root = true := by decide +kernel
end Papers.RationalityTen.RootedCanonical.RootedSixBase02.T2

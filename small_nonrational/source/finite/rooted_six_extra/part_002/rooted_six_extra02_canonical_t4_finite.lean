module
prelude
public import RootedSixExtra02
public import RawKindedFacePlacement
public import RootedSixExtra02OutsideData
public import RawOutsidePlacement

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra02.T4
open ConcreteGrowth
abbrev blockCount : Nat := 120
noncomputable def template : Cell := ⟨10, 63, [3, 5, 6, 10, 12, 20, 24, 33, 36, 48], [7, 14, 28, 37, 52, 59]⟩
noncomputable def root : Cell := FacetUniverses.RootedSixExtra02.cells 0
noncomputable def records : Table (RawFacePlacement.Block × Nat) :=
(.branch 60
 (.branch 30
 (.branch 15
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf (⟨2, 4, 5517840, 5517840, 361626105360, 361626105360⟩, 383850204))
 (.branch 2
 (.leaf (⟨2, 4, 5517840, 5517840, 361609328160, 361626104160⟩, 386995980))
 (.leaf (⟨2, 4, 5517840, 5517840, 361592550945, 361626104070⟩, 390141756))))
 (.branch 5
 (.branch 4
 (.leaf (⟨2, 4, 5517840, 5517840, 361340892720, 361626081120⟩, 398006196))
 (.leaf (⟨2, 4, 5517840, 5517840, 361324115505, 361626081030⟩, 401151972)))
 (.branch 6
 (.leaf (⟨2, 4, 5517840, 5517840, 356760712770, 361625649270⟩, 409016412))
 (.leaf (⟨2, 4, 5517840, 5517840, 352465745475, 361625618550⟩, 412162188)))))
 (.branch 11
 (.branch 9
 (.branch 8
 (.leaf (⟨2, 4, 5517840, 5517840, 288309671505, 361617786630⟩, 415307964))
 (.leaf (⟨2, 4, 5517840, 5517840, 283746268755, 361617754230⟩, 418453740)))
 (.branch 10
 (.leaf (⟨2, 4, 5517840, 5517840, 215026792020, 361617201270⟩, 426318180))
 (.leaf (⟨2, 4, 5517600, 5517600, 361626105360, 361626105360⟩, 385881844))))
 (.branch 13
 (.branch 12
 (.leaf (⟨2, 4, 5517600, 5517600, 361609328160, 361626104160⟩, 389027620))
 (.leaf (⟨2, 4, 5517600, 5517600, 361592550945, 361626104070⟩, 392173396)))
 (.branch 14
 (.leaf (⟨2, 4, 5517600, 5517600, 361340892720, 361626081120⟩, 400037836))
 (.leaf (⟨2, 4, 5517600, 5517600, 361324115505, 361626081030⟩, 403183612))))))
 (.branch 22
 (.branch 18
 (.branch 16
 (.leaf (⟨2, 4, 5517600, 5517600, 356760712770, 361625649270⟩, 411048052))
 (.branch 17
 (.leaf (⟨2, 4, 5517600, 5517600, 352465745475, 361625618550⟩, 414193828))
 (.leaf (⟨2, 4, 5517600, 5517600, 288309671505, 361617786630⟩, 417339604))))
 (.branch 20
 (.branch 19
 (.leaf (⟨2, 4, 5517600, 5517600, 283746268755, 361617754230⟩, 420485380))
 (.leaf (⟨2, 4, 5517600, 5517600, 215026792020, 361617201270⟩, 428349820)))
 (.branch 21
 (.leaf (⟨2, 4, 5517345, 5517570, 361626105360, 361626105360⟩, 386209529))
 (.leaf (⟨2, 4, 5517345, 5517570, 361609328160, 361626104160⟩, 389355305)))))
 (.branch 26
 (.branch 24
 (.branch 23
 (.leaf (⟨2, 4, 5517345, 5517570, 361592550945, 361626104070⟩, 392501081))
 (.leaf (⟨2, 4, 5517345, 5517570, 361340892720, 361626081120⟩, 400365521)))
 (.branch 25
 (.leaf (⟨2, 4, 5517345, 5517570, 361324115505, 361626081030⟩, 403511297))
 (.leaf (⟨2, 4, 5517345, 5517570, 356760712770, 361625649270⟩, 411375737))))
 (.branch 28
 (.branch 27
 (.leaf (⟨2, 4, 5517345, 5517570, 352465745475, 361625618550⟩, 414521513))
 (.leaf (⟨2, 4, 5517345, 5517570, 288309671505, 361617786630⟩, 417667289)))
 (.branch 29
 (.leaf (⟨2, 4, 5517345, 5517570, 283746268755, 361617754230⟩, 420813065))
 (.leaf (⟨2, 4, 5517345, 5517570, 215026792020, 361617201270⟩, 428677505)))))))
 (.branch 45
 (.branch 37
 (.branch 33
 (.branch 31
 (.leaf (⟨3, 4, 5517840, 5517840, 361742426640, 434925761040⟩, 7269381783070598684973537132))
 (.branch 32
 (.leaf (⟨3, 4, 5517840, 5517840, 361473991440, 434925741840⟩, 7472484419866149287181752340))
 (.leaf (⟨3, 4, 5517840, 5517840, 283627709745, 434918463495⟩, 7791645706259157376366090524))))
 (.branch 35
 (.branch 34
 (.leaf (⟨3, 4, 5517840, 5517840, 141893788995, 434917935495⟩, 7936719018255979235086244244))
 (.leaf (⟨2, 4, 5513265, 5509890, 361626105360, 361626105360⟩, 383981285)))
 (.branch 36
 (.leaf (⟨2, 4, 5513265, 5509890, 361609328160, 361626104160⟩, 387127061))
 (.leaf (⟨2, 4, 5513265, 5509890, 361592550945, 361626104070⟩, 390272837)))))
 (.branch 41
 (.branch 39
 (.branch 38
 (.leaf (⟨2, 4, 5513265, 5509890, 361340892720, 361626081120⟩, 398137277))
 (.leaf (⟨2, 4, 5513265, 5509890, 361324115505, 361626081030⟩, 401283053)))
 (.branch 40
 (.leaf (⟨2, 4, 5513265, 5509890, 356760712770, 361625649270⟩, 409147493))
 (.leaf (⟨2, 4, 5513265, 5509890, 352465745475, 361625618550⟩, 412293269))))
 (.branch 43
 (.branch 42
 (.leaf (⟨2, 4, 5513265, 5509890, 288309671505, 361617786630⟩, 415439045))
 (.leaf (⟨2, 4, 5513265, 5509890, 283746268755, 361617754230⟩, 418584821)))
 (.branch 44
 (.leaf (⟨2, 4, 5513265, 5509890, 215026792020, 361617201270⟩, 426449261))
 (.leaf (⟨2, 4, 5509170, 5509170, 361626105360, 361626105360⟩, 385554183))))))
 (.branch 52
 (.branch 48
 (.branch 46
 (.leaf (⟨2, 4, 5509170, 5509170, 361609328160, 361626104160⟩, 388699959))
 (.branch 47
 (.leaf (⟨2, 4, 5509170, 5509170, 361592550945, 361626104070⟩, 391845735))
 (.leaf (⟨2, 4, 5509170, 5509170, 361340892720, 361626081120⟩, 399710175))))
 (.branch 50
 (.branch 49
 (.leaf (⟨2, 4, 5509170, 5509170, 361324115505, 361626081030⟩, 402855951))
 (.leaf (⟨2, 4, 5509170, 5509170, 356760712770, 361625649270⟩, 410720391)))
 (.branch 51
 (.leaf (⟨2, 4, 5509170, 5509170, 352465745475, 361625618550⟩, 413866167))
 (.leaf (⟨2, 4, 5509170, 5509170, 288309671505, 361617786630⟩, 417011943)))))
 (.branch 56
 (.branch 54
 (.branch 53
 (.leaf (⟨2, 4, 5509170, 5509170, 283746268755, 361617754230⟩, 420157719))
 (.leaf (⟨2, 4, 5509170, 5509170, 215026792020, 361617201270⟩, 428022159)))
 (.branch 55
 (.leaf (⟨3, 4, 5505825, 5513475, 361742426640, 434925761040⟩, 7257292321959423166081865589))
 (.leaf (⟨3, 4, 5505825, 5513475, 361473991440, 434925741840⟩, 7460394958754973768290080797))))
 (.branch 58
 (.branch 57
 (.leaf (⟨3, 4, 5505825, 5513475, 283627709745, 434918463495⟩, 7779556245147981857474418981))
 (.leaf (⟨3, 4, 5505825, 5513475, 141893788995, 434917935495⟩, 7924629557144803716194572701)))
 (.branch 59
 (.leaf (⟨2, 4, 5443650, 5324850, 361626105360, 361626105360⟩, 385816331))
 (.leaf (⟨2, 4, 5443650, 5324850, 361609328160, 361626104160⟩, 388962107))))))))
 (.branch 90
 (.branch 75
 (.branch 67
 (.branch 63
 (.branch 61
 (.leaf (⟨2, 4, 5443650, 5324850, 361592550945, 361626104070⟩, 392107883))
 (.branch 62
 (.leaf (⟨2, 4, 5443650, 5324850, 361340892720, 361626081120⟩, 399972323))
 (.leaf (⟨2, 4, 5443650, 5324850, 361324115505, 361626081030⟩, 403118099))))
 (.branch 65
 (.branch 64
 (.leaf (⟨2, 4, 5443650, 5324850, 356760712770, 361625649270⟩, 410982539))
 (.leaf (⟨2, 4, 5443650, 5324850, 352465745475, 361625618550⟩, 414128315)))
 (.branch 66
 (.leaf (⟨2, 4, 5443650, 5324850, 288309671505, 361617786630⟩, 417274091))
 (.leaf (⟨2, 4, 5443650, 5324850, 283746268755, 361617754230⟩, 420419867)))))
 (.branch 71
 (.branch 69
 (.branch 68
 (.leaf (⟨2, 4, 5443650, 5324850, 215026792020, 361617201270⟩, 428284307))
 (.leaf (⟨2, 4, 5378115, 5309490, 361626105360, 361626105360⟩, 384440044)))
 (.branch 70
 (.leaf (⟨2, 4, 5378115, 5309490, 361609328160, 361626104160⟩, 387585820))
 (.leaf (⟨2, 4, 5378115, 5309490, 361592550945, 361626104070⟩, 390731596))))
 (.branch 73
 (.branch 72
 (.leaf (⟨2, 4, 5378115, 5309490, 361340892720, 361626081120⟩, 398596036))
 (.leaf (⟨2, 4, 5378115, 5309490, 361324115505, 361626081030⟩, 401741812)))
 (.branch 74
 (.leaf (⟨2, 4, 5378115, 5309490, 356760712770, 361625649270⟩, 409606252))
 (.leaf (⟨2, 4, 5378115, 5309490, 352465745475, 361625618550⟩, 412752028))))))
 (.branch 82
 (.branch 78
 (.branch 76
 (.leaf (⟨2, 4, 5378115, 5309490, 288309671505, 361617786630⟩, 415897804))
 (.branch 77
 (.leaf (⟨2, 4, 5378115, 5309490, 283746268755, 361617754230⟩, 419043580))
 (.leaf (⟨2, 4, 5378115, 5309490, 215026792020, 361617201270⟩, 426908020))))
 (.branch 80
 (.branch 79
 (.leaf (⟨3, 4, 5309490, 5378115, 361742426640, 434925761040⟩, 7251247821991654722263979900))
 (.leaf (⟨3, 4, 5309490, 5378115, 361473991440, 434925741840⟩, 7454350458787205324472195108)))
 (.branch 81
 (.leaf (⟨3, 4, 5309490, 5378115, 283627709745, 434918463495⟩, 7773511745180213413656533292))
 (.leaf (⟨3, 4, 5309490, 5378115, 141893788995, 434917935495⟩, 7918585057177035272376687012)))))
 (.branch 86
 (.branch 84
 (.branch 83
 (.leaf (⟨2, 4, 4399440, 1393440, 361626105360, 361626105360⟩, 383915751))
 (.leaf (⟨2, 4, 4399440, 1393440, 361609328160, 361626104160⟩, 387061527)))
 (.branch 85
 (.leaf (⟨2, 4, 4399440, 1393440, 361592550945, 361626104070⟩, 390207303))
 (.leaf (⟨2, 4, 4399440, 1393440, 361340892720, 361626081120⟩, 398071743))))
 (.branch 88
 (.branch 87
 (.leaf (⟨2, 4, 4399440, 1393440, 361324115505, 361626081030⟩, 401217519))
 (.leaf (⟨2, 4, 4399440, 1393440, 356760712770, 361625649270⟩, 409081959)))
 (.branch 89
 (.leaf (⟨2, 4, 4399440, 1393440, 352465745475, 361625618550⟩, 412227735))
 (.leaf (⟨2, 4, 4399440, 1393440, 288309671505, 361617786630⟩, 415373511)))))))
 (.branch 105
 (.branch 97
 (.branch 93
 (.branch 91
 (.leaf (⟨2, 4, 4399440, 1393440, 283746268755, 361617754230⟩, 418519287))
 (.branch 92
 (.leaf (⟨2, 4, 4399440, 1393440, 215026792020, 361617201270⟩, 426383727))
 (.leaf (⟨2, 4, 4395090, 1392690, 361626105360, 361626105360⟩, 385095424))))
 (.branch 95
 (.branch 94
 (.leaf (⟨2, 4, 4395090, 1392690, 361609328160, 361626104160⟩, 388241200))
 (.leaf (⟨2, 4, 4395090, 1392690, 361592550945, 361626104070⟩, 391386976)))
 (.branch 96
 (.leaf (⟨2, 4, 4395090, 1392690, 361340892720, 361626081120⟩, 399251416))
 (.leaf (⟨2, 4, 4395090, 1392690, 361324115505, 361626081030⟩, 402397192)))))
 (.branch 101
 (.branch 99
 (.branch 98
 (.leaf (⟨2, 4, 4395090, 1392690, 356760712770, 361625649270⟩, 410261632))
 (.leaf (⟨2, 4, 4395090, 1392690, 352465745475, 361625618550⟩, 413407408)))
 (.branch 100
 (.leaf (⟨2, 4, 4395090, 1392690, 288309671505, 361617786630⟩, 416553184))
 (.leaf (⟨2, 4, 4395090, 1392690, 283746268755, 361617754230⟩, 419698960))))
 (.branch 103
 (.branch 102
 (.leaf (⟨2, 4, 4395090, 1392690, 215026792020, 361617201270⟩, 427563400))
 (.leaf (⟨3, 4, 4396320, 2441520, 361742426640, 434925761040⟩, 7256083377693627408856192887)))
 (.branch 104
 (.leaf (⟨3, 4, 4396320, 2441520, 361473991440, 434925741840⟩, 7459186014489178011064408095))
 (.leaf (⟨3, 4, 4396320, 2441520, 283627709745, 434918463495⟩, 7778347300882186100248746279))))))
 (.branch 112
 (.branch 108
 (.branch 106
 (.leaf (⟨3, 4, 4396320, 2441520, 141893788995, 434917935495⟩, 7923420612879007958968899999))
 (.branch 107
 (.leaf (⟨2, 4, 3280980, 1070130, 361626105360, 361626105360⟩, 384636648))
 (.leaf (⟨2, 4, 3280980, 1070130, 361609328160, 361626104160⟩, 387782424))))
 (.branch 110
 (.branch 109
 (.leaf (⟨2, 4, 3280980, 1070130, 361592550945, 361626104070⟩, 390928200))
 (.leaf (⟨2, 4, 3280980, 1070130, 361340892720, 361626081120⟩, 398792640)))
 (.branch 111
 (.leaf (⟨2, 4, 3280980, 1070130, 361324115505, 361626081030⟩, 401938416))
 (.leaf (⟨2, 4, 3280980, 1070130, 356760712770, 361625649270⟩, 409802856)))))
 (.branch 116
 (.branch 114
 (.branch 113
 (.leaf (⟨2, 4, 3280980, 1070130, 352465745475, 361625618550⟩, 412948632))
 (.leaf (⟨2, 4, 3280980, 1070130, 288309671505, 361617786630⟩, 416094408)))
 (.branch 115
 (.leaf (⟨2, 4, 3280980, 1070130, 283746268755, 361617754230⟩, 419240184))
 (.leaf (⟨2, 4, 3280980, 1070130, 215026792020, 361617201270⟩, 427104624))))
 (.branch 118
 (.branch 117
 (.leaf (⟨3, 4, 3212610, 2183235, 361742426640, 434925761040⟩, 7254874654791575238666753912))
 (.leaf (⟨3, 4, 3212610, 2183235, 361473991440, 434925741840⟩, 7457977291587125840874969120)))
 (.branch 119
 (.leaf (⟨3, 4, 3212610, 2183235, 283627709745, 434918463495⟩, 7777138577980133930059307304))
 (.leaf (⟨3, 4, 3212610, 2183235, 141893788995, 434917935495⟩, 7922211889976955788779461024)))))))))
noncomputable def raw (i : Fin blockCount) : RawFacePlacement.Block := (records.get i.val).1
noncomputable def witness (i : Fin blockCount) (code : Nat) : Fin 6620 :=
  Fin.ofNat 6620 (Nat.land (Nat.shiftRight (records.get i.val).2 (16 * code)) 65535)
noncomputable def faceTable : Table Nat :=
(.branch 20486
 (.branch 7175
 (.branch 5140
 (.branch 3106
 (.branch 3081
 (.branch 3077
 (.leaf 0)
 (.branch 3078
 (.leaf 1)
 (.leaf 2)))
 (.branch 3092
 (.branch 3082
 (.leaf 3)
 (.leaf 4))
 (.branch 3096
 (.leaf 5)
 (.leaf 6))))
 (.branch 5125
 (.branch 3120
 (.branch 3112
 (.leaf 7)
 (.leaf 8))
 (.branch 5123
 (.leaf 9)
 (.leaf 10)))
 (.branch 5129
 (.branch 5126
 (.leaf 11)
 (.leaf 12))
 (.branch 5130
 (.leaf 13)
 (.leaf 14)))))
 (.branch 6150
 (.branch 5160
 (.branch 5144
 (.leaf 15)
 (.branch 5154
 (.leaf 16)
 (.leaf 17)))
 (.branch 6147
 (.branch 5168
 (.leaf 18)
 (.leaf 19))
 (.branch 6149
 (.leaf 20)
 (.leaf 21))))
 (.branch 6168
 (.branch 6154
 (.branch 6153
 (.leaf 22)
 (.leaf 23))
 (.branch 6164
 (.leaf 24)
 (.leaf 25)))
 (.branch 6184
 (.branch 6178
 (.leaf 26)
 (.leaf 27))
 (.branch 6192
 (.leaf 28)
 (.leaf 29))))))
 (.branch 12293
 (.branch 10249
 (.branch 7224
 (.branch 7179
 (.leaf 30)
 (.branch 7210
 (.leaf 31)
 (.leaf 32)))
 (.branch 10245
 (.branch 10243
 (.leaf 33)
 (.leaf 34))
 (.branch 10246
 (.leaf 35)
 (.leaf 36))))
 (.branch 10274
 (.branch 10260
 (.branch 10250
 (.leaf 37)
 (.leaf 38))
 (.branch 10264
 (.leaf 39)
 (.leaf 40)))
 (.branch 10288
 (.branch 10280
 (.leaf 41)
 (.leaf 42))
 (.branch 12291
 (.leaf 43)
 (.leaf 44)))))
 (.branch 12328
 (.branch 12298
 (.branch 12294
 (.leaf 45)
 (.branch 12297
 (.leaf 46)
 (.leaf 47)))
 (.branch 12312
 (.branch 12308
 (.leaf 48)
 (.leaf 49))
 (.branch 12322
 (.leaf 50)
 (.leaf 51))))
 (.branch 14378
 (.branch 14343
 (.branch 12336
 (.leaf 52)
 (.leaf 53))
 (.branch 14347
 (.leaf 54)
 (.leaf 55)))
 (.branch 20483
 (.branch 14392
 (.leaf 56)
 (.leaf 57))
 (.branch 20485
 (.leaf 58)
 (.leaf 59)))))))
 (.branch 33832
 (.branch 24610
 (.branch 20528
 (.branch 20500
 (.branch 20489
 (.leaf 60)
 (.branch 20490
 (.leaf 61)
 (.leaf 62)))
 (.branch 20514
 (.branch 20504
 (.leaf 63)
 (.leaf 64))
 (.branch 20520
 (.leaf 65)
 (.leaf 66))))
 (.branch 24585
 (.branch 24581
 (.branch 24579
 (.leaf 67)
 (.leaf 68))
 (.branch 24582
 (.leaf 69)
 (.leaf 70)))
 (.branch 24596
 (.branch 24586
 (.leaf 71)
 (.leaf 72))
 (.branch 24600
 (.leaf 73)
 (.leaf 74)))))
 (.branch 33795
 (.branch 28679
 (.branch 24616
 (.leaf 75)
 (.branch 24624
 (.leaf 76)
 (.leaf 77)))
 (.branch 28714
 (.branch 28683
 (.leaf 78)
 (.leaf 79))
 (.branch 28728
 (.leaf 80)
 (.leaf 81))))
 (.branch 33802
 (.branch 33798
 (.branch 33797
 (.leaf 82)
 (.leaf 83))
 (.branch 33801
 (.leaf 84)
 (.leaf 85)))
 (.branch 33816
 (.branch 33812
 (.leaf 86)
 (.leaf 87))
 (.branch 33826
 (.leaf 88)
 (.leaf 89))))))
 (.branch 37944
 (.branch 36884
 (.branch 36869
 (.branch 33840
 (.leaf 90)
 (.branch 36867
 (.leaf 91)
 (.leaf 92)))
 (.branch 36873
 (.branch 36870
 (.leaf 93)
 (.leaf 94))
 (.branch 36874
 (.leaf 95)
 (.leaf 96))))
 (.branch 36912
 (.branch 36898
 (.branch 36888
 (.leaf 97)
 (.leaf 98))
 (.branch 36904
 (.leaf 99)
 (.leaf 100)))
 (.branch 37899
 (.branch 37895
 (.leaf 101)
 (.leaf 102))
 (.branch 37930
 (.leaf 103)
 (.leaf 104)))))
 (.branch 49176
 (.branch 49158
 (.branch 49155
 (.leaf 105)
 (.branch 49157
 (.leaf 106)
 (.leaf 107)))
 (.branch 49162
 (.branch 49161
 (.leaf 108)
 (.leaf 109))
 (.branch 49172
 (.leaf 110)
 (.leaf 111))))
 (.branch 53255
 (.branch 49192
 (.branch 49186
 (.leaf 112)
 (.leaf 113))
 (.branch 49200
 (.leaf 114)
 (.leaf 115)))
 (.branch 53290
 (.branch 53259
 (.leaf 116)
 (.leaf 117))
 (.branch 53304
 (.leaf 118)
 (.leaf 119))))))))
noncomputable def faceWitness (s r : Nat) : Fin blockCount :=
  Fin.ofNat blockCount (faceTable.get (s * 1024 + r))
noncomputable def validity (i : Nat) : Bool :=
  RawFaceNormalizers.blockValidCheck 6 (raw (Fin.ofNat blockCount i))
noncomputable def placement (b : Fin blockCount) (code : Nat) : Bool :=
  RawKindedFacePlacement.check 6 (raw b) template root FacetUniverses.RootedSixExtra02.cells
    code 0 (witness b code)
noncomputable def test (i : Nat) : Bool :=
  let b := Fin.ofNat blockCount i
  FiniteChecks.checkRange (placement b)
    0 (RawFacePlacement.count (raw b).shared (raw b).shared)
noncomputable def symmetry (i : Nat) : Bool :=
  RawOutsidePlacement.blockCheck FacetUniverses.RootedSixExtra02.Outside.vertexCode root.vertices
    (raw (Fin.ofNat blockCount i))
end Papers.RationalityTen.RootedCanonical.RootedSixExtra02.T4

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra02.T4
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
end Papers.RationalityTen.RootedCanonical.RootedSixExtra02.T4

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra02.T4
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
theorem check_0100_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 100)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 100)) 0 2 (by decide +kernel)
theorem block_0100 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 100)) 0 2 :=
  check_0100_0000
theorem check_0101_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 101)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 101)) 0 2 (by decide +kernel)
theorem block_0101 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 101)) 0 2 :=
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
end Papers.RationalityTen.RootedCanonical.RootedSixExtra02.T4

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra02.T4
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
theorem metadata_validity_0112 : FiniteChecks.Interval validity 112 120 :=
  FiniteChecks.interval_of_check validity 112 8 (by decide +kernel)
theorem metadata_validity : FiniteChecks.Interval validity 0 blockCount :=
  (FiniteChecks.interval_append (validity) 0 64 120
  (FiniteChecks.interval_append (validity) 0 32 64
  (FiniteChecks.interval_append (validity) 0 16 32
  metadata_validity_0000
  metadata_validity_0016)
  (FiniteChecks.interval_append (validity) 32 48 64
  metadata_validity_0032
  metadata_validity_0048))
  (FiniteChecks.interval_append (validity) 64 96 120
  (FiniteChecks.interval_append (validity) 64 80 96
  metadata_validity_0064
  metadata_validity_0080)
  (FiniteChecks.interval_append (validity) 96 112 120
  metadata_validity_0096
  metadata_validity_0112)))
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
theorem metadata_symmetry_0112 : FiniteChecks.Interval symmetry 112 120 :=
  FiniteChecks.interval_of_check symmetry 112 8 (by decide +kernel)
theorem metadata_symmetry : FiniteChecks.Interval symmetry 0 blockCount :=
  (FiniteChecks.interval_append (symmetry) 0 64 120
  (FiniteChecks.interval_append (symmetry) 0 32 64
  (FiniteChecks.interval_append (symmetry) 0 16 32
  metadata_symmetry_0000
  metadata_symmetry_0016)
  (FiniteChecks.interval_append (symmetry) 32 48 64
  metadata_symmetry_0032
  metadata_symmetry_0048))
  (FiniteChecks.interval_append (symmetry) 64 96 120
  (FiniteChecks.interval_append (symmetry) 64 80 96
  metadata_symmetry_0064
  metadata_symmetry_0080)
  (FiniteChecks.interval_append (symmetry) 96 112 120
  metadata_symmetry_0096
  metadata_symmetry_0112)))
theorem metadata_normalizers :
    RawFaceNormalizers.completeCheck 6 template root raw faceWitness = true := by decide +kernel
theorem metadata_root : RawFacetEmbedding.wellFormedCheck root = true := by decide +kernel
end Papers.RationalityTen.RootedCanonical.RootedSixExtra02.T4

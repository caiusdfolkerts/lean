module
prelude
public import RootedSixBase02
public import RawKindedFacePlacement
public import RootedSixBase02OutsideData
public import RawOutsidePlacement

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase02.S5T1
open ConcreteGrowth
abbrev blockCount : Nat := 128
noncomputable def template : Cell := ⟨3, 31, [3, 5, 6, 10, 12, 17, 20, 24], [7, 14, 21, 27, 28]⟩
noncomputable def root : Cell := FacetUniverses.RootedSixBase02.cells 0
noncomputable def records : Table (RawFacePlacement.Block × Nat) :=
(.branch 64
 (.branch 32
 (.branch 16
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf (⟨1, 4, 274960, 274960, 361617786720, 288326448720⟩, 518))
 (.leaf (⟨1, 4, 274960, 274960, 361616738145, 288326448645⟩, 871)))
 (.branch 3
 (.leaf (⟨1, 4, 274960, 274960, 361599960930, 288326447205⟩, 980))
 (.leaf (⟨1, 4, 274960, 274960, 361331525475, 288326420325⟩, 1245))))
 (.branch 6
 (.branch 5
 (.leaf (⟨1, 4, 274960, 274960, 357036558180, 288325928805⟩, 1354))
 (.leaf (⟨1, 4, 274960, 274960, 288317081445, 288317081445⟩, 1379)))
 (.branch 7
 (.leaf (⟨1, 4, 274945, 274945, 361617786720, 288326448720⟩, 519))
 (.leaf (⟨1, 4, 274945, 274945, 361616738145, 288326448645⟩, 872)))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf (⟨1, 4, 274945, 274945, 361599960930, 288326447205⟩, 981))
 (.leaf (⟨1, 4, 274945, 274945, 361331525475, 288326420325⟩, 1246)))
 (.branch 11
 (.leaf (⟨1, 4, 274945, 274945, 357036558180, 288325928805⟩, 1355))
 (.leaf (⟨1, 4, 274945, 274945, 288317081445, 288317081445⟩, 1380))))
 (.branch 14
 (.branch 13
 (.leaf (⟨2, 4, 274960, 274960, 361626105360, 361626105360⟩, 17170693))
 (.leaf (⟨2, 4, 274960, 274960, 361609328160, 361626104160⟩, 22937949)))
 (.branch 15
 (.leaf (⟨2, 4, 274960, 274960, 361592550945, 361626104070⟩, 35848738))
 (.leaf (⟨2, 4, 274960, 274960, 361340892720, 361626081120⟩, 28443057))))))
 (.branch 24
 (.branch 20
 (.branch 18
 (.branch 17
 (.leaf (⟨2, 4, 274960, 274960, 361324115505, 361626081030⟩, 46072510))
 (.leaf (⟨2, 4, 274960, 274960, 356760712770, 361625649270⟩, 58721151)))
 (.branch 19
 (.leaf (⟨2, 4, 274960, 274960, 352465745475, 361625618550⟩, 70583348))
 (.leaf (⟨2, 4, 274960, 274960, 288309671505, 361617786630⟩, 51577618))))
 (.branch 22
 (.branch 21
 (.leaf (⟨2, 4, 274960, 274960, 283746268755, 361617754230⟩, 76088456))
 (.leaf (⟨2, 4, 274960, 274960, 215026792020, 361617201270⟩, 83231989)))
 (.branch 23
 (.leaf (⟨1, 4, 274690, 274465, 361617786720, 288326448720⟩, 512))
 (.leaf (⟨1, 4, 274690, 274465, 361616738145, 288326448645⟩, 865)))))
 (.branch 28
 (.branch 26
 (.branch 25
 (.leaf (⟨1, 4, 274690, 274465, 361599960930, 288326447205⟩, 974))
 (.leaf (⟨1, 4, 274690, 274465, 361331525475, 288326420325⟩, 1239)))
 (.branch 27
 (.leaf (⟨1, 4, 274690, 274465, 357036558180, 288325928805⟩, 1348))
 (.leaf (⟨1, 4, 274690, 274465, 288317081445, 288317081445⟩, 1373))))
 (.branch 30
 (.branch 29
 (.leaf (⟨2, 4, 274720, 274720, 361626105360, 361626105360⟩, 16711938))
 (.leaf (⟨2, 4, 274720, 274720, 361609328160, 361626104160⟩, 22479194)))
 (.branch 31
 (.leaf (⟨2, 4, 274720, 274720, 361592550945, 361626104070⟩, 35389983))
 (.leaf (⟨2, 4, 274720, 274720, 361340892720, 361626081120⟩, 27984302)))))))
 (.branch 48
 (.branch 40
 (.branch 36
 (.branch 34
 (.branch 33
 (.leaf (⟨2, 4, 274720, 274720, 361324115505, 361626081030⟩, 45613755))
 (.leaf (⟨2, 4, 274720, 274720, 356760712770, 361625649270⟩, 58262396)))
 (.branch 35
 (.leaf (⟨2, 4, 274720, 274720, 352465745475, 361625618550⟩, 70124593))
 (.leaf (⟨2, 4, 274720, 274720, 288309671505, 361617786630⟩, 51118863))))
 (.branch 38
 (.branch 37
 (.leaf (⟨2, 4, 274720, 274720, 283746268755, 361617754230⟩, 75629701))
 (.leaf (⟨2, 4, 274720, 274720, 215026792020, 361617201270⟩, 82773234)))
 (.branch 39
 (.leaf (⟨2, 4, 274465, 274690, 361626105360, 361626105360⟩, 16777475))
 (.leaf (⟨2, 4, 274465, 274690, 361609328160, 361626104160⟩, 22544731)))))
 (.branch 44
 (.branch 42
 (.branch 41
 (.leaf (⟨2, 4, 274465, 274690, 361592550945, 361626104070⟩, 35455520))
 (.leaf (⟨2, 4, 274465, 274690, 361340892720, 361626081120⟩, 28049839)))
 (.branch 43
 (.leaf (⟨2, 4, 274465, 274690, 361324115505, 361626081030⟩, 45679292))
 (.leaf (⟨2, 4, 274465, 274690, 356760712770, 361625649270⟩, 58327933))))
 (.branch 46
 (.branch 45
 (.leaf (⟨2, 4, 274465, 274690, 352465745475, 361625618550⟩, 70190130))
 (.leaf (⟨2, 4, 274465, 274690, 288309671505, 361617786630⟩, 51184400)))
 (.branch 47
 (.leaf (⟨2, 4, 274465, 274690, 283746268755, 361617754230⟩, 75695238))
 (.leaf (⟨2, 4, 274465, 274690, 215026792020, 361617201270⟩, 82838771))))))
 (.branch 56
 (.branch 52
 (.branch 50
 (.branch 49
 (.leaf (⟨3, 4, 274960, 274960, 361742426640, 434925761040⟩, 131774906617317264861495408))
 (.leaf (⟨3, 4, 274960, 274960, 361473991440, 434925741840⟩, 218818893815410380093587640)))
 (.branch 51
 (.leaf (⟨3, 4, 274960, 274960, 283627709745, 434918463495⟩, 751963315403730710890152561))
 (.leaf (⟨3, 4, 274960, 274960, 141893788995, 434917935495⟩, 1204108471127158837234631655))))
 (.branch 54
 (.branch 53
 (.leaf (⟨1, 4, 270595, 262945, 361617786720, 288326448720⟩, 523))
 (.leaf (⟨1, 4, 270595, 262945, 361616738145, 288326448645⟩, 876)))
 (.branch 55
 (.leaf (⟨1, 4, 270595, 262945, 361599960930, 288326447205⟩, 985))
 (.leaf (⟨1, 4, 270595, 262945, 361331525475, 288326420325⟩, 1250)))))
 (.branch 60
 (.branch 58
 (.branch 57
 (.leaf (⟨1, 4, 270595, 262945, 357036558180, 288325928805⟩, 1359))
 (.leaf (⟨1, 4, 270595, 262945, 288317081445, 288317081445⟩, 1384)))
 (.branch 59
 (.leaf (⟨2, 4, 270385, 267010, 361626105360, 361626105360⟩, 17236232))
 (.leaf (⟨2, 4, 270385, 267010, 361609328160, 361626104160⟩, 23003488))))
 (.branch 62
 (.branch 61
 (.leaf (⟨2, 4, 270385, 267010, 361592550945, 361626104070⟩, 35914277))
 (.leaf (⟨2, 4, 270385, 267010, 361340892720, 361626081120⟩, 28508596)))
 (.branch 63
 (.leaf (⟨2, 4, 270385, 267010, 361324115505, 361626081030⟩, 46138049))
 (.leaf (⟨2, 4, 270385, 267010, 356760712770, 361625649270⟩, 58786690))))))))
 (.branch 96
 (.branch 80
 (.branch 72
 (.branch 68
 (.branch 66
 (.branch 65
 (.leaf (⟨2, 4, 270385, 267010, 352465745475, 361625618550⟩, 70648887))
 (.leaf (⟨2, 4, 270385, 267010, 288309671505, 361617786630⟩, 51643157)))
 (.branch 67
 (.leaf (⟨2, 4, 270385, 267010, 283746268755, 361617754230⟩, 76153995))
 (.leaf (⟨2, 4, 270385, 267010, 215026792020, 361617201270⟩, 83297528))))
 (.branch 70
 (.branch 69
 (.leaf (⟨2, 4, 266290, 266290, 361626105360, 361626105360⟩, 17039617))
 (.leaf (⟨2, 4, 266290, 266290, 361609328160, 361626104160⟩, 22806873)))
 (.branch 71
 (.leaf (⟨2, 4, 266290, 266290, 361592550945, 361626104070⟩, 35717662))
 (.leaf (⟨2, 4, 266290, 266290, 361340892720, 361626081120⟩, 28311981)))))
 (.branch 76
 (.branch 74
 (.branch 73
 (.leaf (⟨2, 4, 266290, 266290, 361324115505, 361626081030⟩, 45941434))
 (.leaf (⟨2, 4, 266290, 266290, 356760712770, 361625649270⟩, 58590075)))
 (.branch 75
 (.leaf (⟨2, 4, 266290, 266290, 352465745475, 361625618550⟩, 70452272))
 (.leaf (⟨2, 4, 266290, 266290, 288309671505, 361617786630⟩, 51446542))))
 (.branch 78
 (.branch 77
 (.leaf (⟨2, 4, 266290, 266290, 283746268755, 361617754230⟩, 75957380))
 (.leaf (⟨2, 4, 266290, 266290, 215026792020, 361617201270⟩, 83100913)))
 (.branch 79
 (.leaf (⟨3, 4, 262945, 270595, 361742426640, 434925761040⟩, 132983906224752600919375983))
 (.leaf (⟨3, 4, 262945, 270595, 361473991440, 434925741840⟩, 220027893422845716151468215))))))
 (.branch 88
 (.branch 84
 (.branch 82
 (.branch 81
 (.leaf (⟨3, 4, 262945, 270595, 283627709745, 434918463495⟩, 753172315011166046948033136))
 (.leaf (⟨3, 4, 262945, 270595, 141893788995, 434917935495⟩, 1205317470734594173292512230)))
 (.branch 83
 (.leaf (⟨1, 4, 205060, 17185, 361617786720, 288326448720⟩, 521))
 (.leaf (⟨1, 4, 205060, 17185, 361616738145, 288326448645⟩, 874))))
 (.branch 86
 (.branch 85
 (.leaf (⟨1, 4, 205060, 17185, 361599960930, 288326447205⟩, 983))
 (.leaf (⟨1, 4, 205060, 17185, 361331525475, 288326420325⟩, 1248)))
 (.branch 87
 (.leaf (⟨1, 4, 205060, 17185, 357036558180, 288325928805⟩, 1357))
 (.leaf (⟨1, 4, 205060, 17185, 288317081445, 288317081445⟩, 1382)))))
 (.branch 92
 (.branch 90
 (.branch 89
 (.leaf (⟨2, 4, 205120, 82720, 361626105360, 361626105360⟩, 17236232))
 (.leaf (⟨2, 4, 205120, 82720, 361609328160, 361626104160⟩, 23003488)))
 (.branch 91
 (.leaf (⟨2, 4, 205120, 82720, 361592550945, 361626104070⟩, 35914277))
 (.leaf (⟨2, 4, 205120, 82720, 361340892720, 361626081120⟩, 28508596))))
 (.branch 94
 (.branch 93
 (.leaf (⟨2, 4, 205120, 82720, 361324115505, 361626081030⟩, 46138049))
 (.leaf (⟨2, 4, 205120, 82720, 356760712770, 361625649270⟩, 58786690)))
 (.branch 95
 (.leaf (⟨2, 4, 205120, 82720, 352465745475, 361625618550⟩, 70648887))
 (.leaf (⟨2, 4, 205120, 82720, 288309671505, 361617786630⟩, 51643157)))))))
 (.branch 112
 (.branch 104
 (.branch 100
 (.branch 98
 (.branch 97
 (.leaf (⟨2, 4, 205120, 82720, 283746268755, 361617754230⟩, 76153995))
 (.leaf (⟨2, 4, 205120, 82720, 215026792020, 361617201270⟩, 83297528)))
 (.branch 99
 (.leaf (⟨2, 4, 200770, 81970, 361626105360, 361626105360⟩, 16908543))
 (.leaf (⟨2, 4, 200770, 81970, 361609328160, 361626104160⟩, 22675799))))
 (.branch 102
 (.branch 101
 (.leaf (⟨2, 4, 200770, 81970, 361592550945, 361626104070⟩, 35586588))
 (.leaf (⟨2, 4, 200770, 81970, 361340892720, 361626081120⟩, 28180907)))
 (.branch 103
 (.leaf (⟨2, 4, 200770, 81970, 361324115505, 361626081030⟩, 45810360))
 (.leaf (⟨2, 4, 200770, 81970, 356760712770, 361625649270⟩, 58459001)))))
 (.branch 108
 (.branch 106
 (.branch 105
 (.leaf (⟨2, 4, 200770, 81970, 352465745475, 361625618550⟩, 70321198))
 (.leaf (⟨2, 4, 200770, 81970, 288309671505, 361617786630⟩, 51315468)))
 (.branch 107
 (.leaf (⟨2, 4, 200770, 81970, 283746268755, 361617754230⟩, 75826306))
 (.leaf (⟨2, 4, 200770, 81970, 215026792020, 361617201270⟩, 82969839))))
 (.branch 110
 (.branch 109
 (.leaf (⟨3, 4, 201760, 147760, 361742426640, 434925761040⟩, 132983906224752600919375983))
 (.leaf (⟨3, 4, 201760, 147760, 361473991440, 434925741840⟩, 220027893422845716151468215)))
 (.branch 111
 (.leaf (⟨3, 4, 201760, 147760, 283627709745, 434918463495⟩, 753172315011166046948033136))
 (.leaf (⟨3, 4, 201760, 147760, 141893788995, 434917935495⟩, 1205317470734594173292512230))))))
 (.branch 120
 (.branch 116
 (.branch 114
 (.branch 113
 (.leaf (⟨2, 4, 135235, 66610, 361626105360, 361626105360⟩, 17432841))
 (.leaf (⟨2, 4, 135235, 66610, 361609328160, 361626104160⟩, 23200097)))
 (.branch 115
 (.leaf (⟨2, 4, 135235, 66610, 361592550945, 361626104070⟩, 36110886))
 (.leaf (⟨2, 4, 135235, 66610, 361340892720, 361626081120⟩, 28705205))))
 (.branch 118
 (.branch 117
 (.leaf (⟨2, 4, 135235, 66610, 361324115505, 361626081030⟩, 46334658))
 (.leaf (⟨2, 4, 135235, 66610, 356760712770, 361625649270⟩, 58983299)))
 (.branch 119
 (.leaf (⟨2, 4, 135235, 66610, 352465745475, 361625618550⟩, 70845496))
 (.leaf (⟨2, 4, 135235, 66610, 288309671505, 361617786630⟩, 51839766)))))
 (.branch 124
 (.branch 122
 (.branch 121
 (.leaf (⟨2, 4, 135235, 66610, 283746268755, 361617754230⟩, 76350604))
 (.leaf (⟨2, 4, 135235, 66610, 215026792020, 361617201270⟩, 83494137)))
 (.branch 123
 (.leaf (⟨4, 4, 148240, 205840, 350450238240, 508225069440⟩, 3027464367842201812538126329084002875463016389132361448213539724868548185447828351813877780274508698359562240))
 (.leaf (⟨4, 4, 148240, 205840, 208716321825, 508218741000⟩, 316846576927184514106193536597655625253602544847088552282322369547849318354207135841073642807312554612618904470031))))
 (.branch 126
 (.branch 125
 (.leaf (⟨3, 4, 66610, 135235, 361742426640, 434925761040⟩, 136610665235726532007034988))
 (.leaf (⟨3, 4, 66610, 135235, 361473991440, 434925741840⟩, 223654652433819647239127220)))
 (.branch 127
 (.leaf (⟨3, 4, 66610, 135235, 283627709745, 434918463495⟩, 756799074022139978035692141))
 (.leaf (⟨3, 4, 66610, 135235, 141893788995, 434917935495⟩, 1208944229745568104380171235)))))))))
noncomputable def raw (i : Fin blockCount) : RawFacePlacement.Block := (records.get i.val).1
noncomputable def witness (i : Fin blockCount) (code : Nat) : Fin 8084 :=
  Fin.ofNat 8084 (Nat.land (Nat.shiftRight (records.get i.val).2 (16 * code)) 65535)
noncomputable def faceTable : Table Nat :=
(.branch 10264
 (.branch 5130
 (.branch 3082
 (.branch 2052
 (.branch 1040
 (.branch 1028
 (.branch 1026
 (.leaf 0)
 (.leaf 1))
 (.branch 1032
 (.leaf 2)
 (.leaf 3)))
 (.branch 2049
 (.branch 1056
 (.leaf 4)
 (.leaf 5))
 (.branch 2050
 (.leaf 6)
 (.leaf 7))))
 (.branch 3075
 (.branch 2064
 (.branch 2056
 (.leaf 8)
 (.leaf 9))
 (.branch 2080
 (.leaf 10)
 (.leaf 11)))
 (.branch 3078
 (.branch 3077
 (.leaf 12)
 (.leaf 13))
 (.branch 3081
 (.leaf 14)
 (.leaf 15)))))
 (.branch 4100
 (.branch 3112
 (.branch 3096
 (.branch 3092
 (.leaf 16)
 (.leaf 17))
 (.branch 3106
 (.leaf 18)
 (.leaf 19)))
 (.branch 4097
 (.branch 3120
 (.leaf 20)
 (.leaf 21))
 (.branch 4098
 (.leaf 22)
 (.leaf 23))))
 (.branch 5123
 (.branch 4112
 (.branch 4104
 (.leaf 24)
 (.leaf 25))
 (.branch 4128
 (.leaf 26)
 (.leaf 27)))
 (.branch 5126
 (.branch 5125
 (.leaf 28)
 (.leaf 29))
 (.branch 5129
 (.leaf 30)
 (.leaf 31))))))
 (.branch 7175
 (.branch 6150
 (.branch 5160
 (.branch 5144
 (.branch 5140
 (.leaf 32)
 (.leaf 33))
 (.branch 5154
 (.leaf 34)
 (.leaf 35)))
 (.branch 6147
 (.branch 5168
 (.leaf 36)
 (.leaf 37))
 (.branch 6149
 (.leaf 38)
 (.leaf 39))))
 (.branch 6168
 (.branch 6154
 (.branch 6153
 (.leaf 40)
 (.leaf 41))
 (.branch 6164
 (.leaf 42)
 (.leaf 43)))
 (.branch 6184
 (.branch 6178
 (.leaf 44)
 (.leaf 45))
 (.branch 6192
 (.leaf 46)
 (.leaf 47)))))
 (.branch 8208
 (.branch 8193
 (.branch 7210
 (.branch 7179
 (.leaf 48)
 (.leaf 49))
 (.branch 7224
 (.leaf 50)
 (.leaf 51)))
 (.branch 8196
 (.branch 8194
 (.leaf 52)
 (.leaf 53))
 (.branch 8200
 (.leaf 54)
 (.leaf 55))))
 (.branch 10246
 (.branch 10243
 (.branch 8224
 (.leaf 56)
 (.leaf 57))
 (.branch 10245
 (.leaf 58)
 (.leaf 59)))
 (.branch 10250
 (.branch 10249
 (.leaf 60)
 (.leaf 61))
 (.branch 10260
 (.leaf 62)
 (.leaf 63)))))))
 (.branch 17448
 (.branch 14378
 (.branch 12298
 (.branch 12291
 (.branch 10280
 (.branch 10274
 (.leaf 64)
 (.leaf 65))
 (.branch 10288
 (.leaf 66)
 (.leaf 67)))
 (.branch 12294
 (.branch 12293
 (.leaf 68)
 (.leaf 69))
 (.branch 12297
 (.leaf 70)
 (.leaf 71))))
 (.branch 12328
 (.branch 12312
 (.branch 12308
 (.leaf 72)
 (.leaf 73))
 (.branch 12322
 (.leaf 74)
 (.leaf 75)))
 (.branch 14343
 (.branch 12336
 (.leaf 76)
 (.leaf 77))
 (.branch 14347
 (.leaf 78)
 (.leaf 79)))))
 (.branch 17411
 (.branch 16388
 (.branch 16385
 (.branch 14392
 (.leaf 80)
 (.leaf 81))
 (.branch 16386
 (.leaf 82)
 (.leaf 83)))
 (.branch 16400
 (.branch 16392
 (.leaf 84)
 (.leaf 85))
 (.branch 16416
 (.leaf 86)
 (.leaf 87))))
 (.branch 17418
 (.branch 17414
 (.branch 17413
 (.leaf 88)
 (.leaf 89))
 (.branch 17417
 (.leaf 90)
 (.leaf 91)))
 (.branch 17432
 (.branch 17428
 (.leaf 92)
 (.leaf 93))
 (.branch 17442
 (.leaf 94)
 (.leaf 95))))))
 (.branch 24579
 (.branch 20504
 (.branch 20486
 (.branch 20483
 (.branch 17456
 (.leaf 96)
 (.leaf 97))
 (.branch 20485
 (.leaf 98)
 (.leaf 99)))
 (.branch 20490
 (.branch 20489
 (.leaf 100)
 (.leaf 101))
 (.branch 20500
 (.leaf 102)
 (.leaf 103))))
 (.branch 21511
 (.branch 20520
 (.branch 20514
 (.leaf 104)
 (.leaf 105))
 (.branch 20528
 (.leaf 106)
 (.leaf 107)))
 (.branch 21546
 (.branch 21515
 (.leaf 108)
 (.leaf 109))
 (.branch 21560
 (.leaf 110)
 (.leaf 111)))))
 (.branch 24616
 (.branch 24586
 (.branch 24582
 (.branch 24581
 (.leaf 112)
 (.leaf 113))
 (.branch 24585
 (.leaf 114)
 (.leaf 115)))
 (.branch 24600
 (.branch 24596
 (.leaf 116)
 (.leaf 117))
 (.branch 24610
 (.leaf 118)
 (.leaf 119))))
 (.branch 28679
 (.branch 27677
 (.branch 24624
 (.leaf 120)
 (.leaf 121))
 (.branch 27702
 (.leaf 122)
 (.leaf 123)))
 (.branch 28714
 (.branch 28683
 (.leaf 124)
 (.leaf 125))
 (.branch 28728
 (.leaf 126)
 (.leaf 127))))))))
noncomputable def faceWitness (s r : Nat) : Fin blockCount :=
  Fin.ofNat blockCount (faceTable.get (s * 1024 + r))
noncomputable def validity (i : Nat) : Bool :=
  RawFaceNormalizers.blockValidCheck 5 (raw (Fin.ofNat blockCount i))
noncomputable def placement (b : Fin blockCount) (code : Nat) : Bool :=
  RawKindedFacePlacement.check 5 (raw b) template root FacetUniverses.RootedSixBase02.cells
    code 0 (witness b code)
noncomputable def test (i : Nat) : Bool :=
  let b := Fin.ofNat blockCount i
  FiniteChecks.checkRange (placement b)
    0 (RawFacePlacement.count (raw b).shared (raw b).shared)
noncomputable def symmetry (i : Nat) : Bool :=
  RawOutsidePlacement.blockCheck FacetUniverses.RootedSixBase02.Outside.vertexCode root.vertices
    (raw (Fin.ofNat blockCount i))
end Papers.RationalityTen.RootedCanonical.RootedSixBase02.S5T1

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase02.S5T1
theorem check_0000_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 0)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 0)) 0 1 (by decide +kernel)
theorem block_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 0)) 0 1 :=
  check_0000_0000
theorem check_0001_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 1)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 1)) 0 1 (by decide +kernel)
theorem block_0001 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 1)) 0 1 :=
  check_0001_0000
theorem check_0002_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 2)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 2)) 0 1 (by decide +kernel)
theorem block_0002 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 2)) 0 1 :=
  check_0002_0000
theorem check_0003_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 3)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 3)) 0 1 (by decide +kernel)
theorem block_0003 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 3)) 0 1 :=
  check_0003_0000
theorem check_0004_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 4)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 4)) 0 1 (by decide +kernel)
theorem block_0004 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 4)) 0 1 :=
  check_0004_0000
theorem check_0005_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 5)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 5)) 0 1 (by decide +kernel)
theorem block_0005 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 5)) 0 1 :=
  check_0005_0000
theorem check_0006_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 6)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 6)) 0 1 (by decide +kernel)
theorem block_0006 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 6)) 0 1 :=
  check_0006_0000
theorem check_0007_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 7)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 7)) 0 1 (by decide +kernel)
theorem block_0007 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 7)) 0 1 :=
  check_0007_0000
theorem check_0008_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 8)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 8)) 0 1 (by decide +kernel)
theorem block_0008 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 8)) 0 1 :=
  check_0008_0000
theorem check_0009_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 9)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 9)) 0 1 (by decide +kernel)
theorem block_0009 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 9)) 0 1 :=
  check_0009_0000
theorem check_0010_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 10)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 10)) 0 1 (by decide +kernel)
theorem block_0010 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 10)) 0 1 :=
  check_0010_0000
theorem check_0011_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 11)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 11)) 0 1 (by decide +kernel)
theorem block_0011 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 11)) 0 1 :=
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
theorem check_0022_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 22)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 22)) 0 1 (by decide +kernel)
theorem block_0022 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 22)) 0 1 :=
  check_0022_0000
theorem check_0023_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 23)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 23)) 0 1 (by decide +kernel)
theorem block_0023 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 23)) 0 1 :=
  check_0023_0000
theorem check_0024_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 24)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 24)) 0 1 (by decide +kernel)
theorem block_0024 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 24)) 0 1 :=
  check_0024_0000
theorem check_0025_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 25)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 25)) 0 1 (by decide +kernel)
theorem block_0025 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 25)) 0 1 :=
  check_0025_0000
theorem check_0026_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 26)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 26)) 0 1 (by decide +kernel)
theorem block_0026 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 26)) 0 1 :=
  check_0026_0000
theorem check_0027_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 27)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 27)) 0 1 (by decide +kernel)
theorem block_0027 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 27)) 0 1 :=
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
theorem check_0048_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 48)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 48)) 0 6 (by decide +kernel)
theorem block_0048 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 48)) 0 6 :=
  check_0048_0000
theorem check_0049_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 49)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 49)) 0 6 (by decide +kernel)
theorem block_0049 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 49)) 0 6 :=
  check_0049_0000
theorem check_0050_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 50)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 50)) 0 6 (by decide +kernel)
theorem block_0050 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 50)) 0 6 :=
  check_0050_0000
theorem check_0051_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 51)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 51)) 0 6 (by decide +kernel)
theorem block_0051 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 51)) 0 6 :=
  check_0051_0000
theorem check_0052_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 52)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 52)) 0 1 (by decide +kernel)
theorem block_0052 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 52)) 0 1 :=
  check_0052_0000
theorem check_0053_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 53)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 53)) 0 1 (by decide +kernel)
theorem block_0053 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 53)) 0 1 :=
  check_0053_0000
theorem check_0054_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 54)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 54)) 0 1 (by decide +kernel)
theorem block_0054 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 54)) 0 1 :=
  check_0054_0000
theorem check_0055_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 55)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 55)) 0 1 (by decide +kernel)
theorem block_0055 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 55)) 0 1 :=
  check_0055_0000
theorem check_0056_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 56)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 56)) 0 1 (by decide +kernel)
theorem block_0056 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 56)) 0 1 :=
  check_0056_0000
theorem check_0057_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 57)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 57)) 0 1 (by decide +kernel)
theorem block_0057 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 57)) 0 1 :=
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
end Papers.RationalityTen.RootedCanonical.RootedSixBase02.S5T1

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase02.S5T1
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
theorem check_0082_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 82)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 82)) 0 1 (by decide +kernel)
theorem block_0082 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 82)) 0 1 :=
  check_0082_0000
theorem check_0083_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 83)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 83)) 0 1 (by decide +kernel)
theorem block_0083 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 83)) 0 1 :=
  check_0083_0000
theorem check_0084_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 84)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 84)) 0 1 (by decide +kernel)
theorem block_0084 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 84)) 0 1 :=
  check_0084_0000
theorem check_0085_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 85)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 85)) 0 1 (by decide +kernel)
theorem block_0085 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 85)) 0 1 :=
  check_0085_0000
theorem check_0086_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 86)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 86)) 0 1 (by decide +kernel)
theorem block_0086 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 86)) 0 1 :=
  check_0086_0000
theorem check_0087_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 87)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 87)) 0 1 (by decide +kernel)
theorem block_0087 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 87)) 0 1 :=
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
theorem check_0108_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 108)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 108)) 0 6 (by decide +kernel)
theorem block_0108 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 108)) 0 6 :=
  check_0108_0000
theorem check_0109_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 109)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 109)) 0 6 (by decide +kernel)
theorem block_0109 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 109)) 0 6 :=
  check_0109_0000
theorem check_0110_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 110)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 110)) 0 6 (by decide +kernel)
theorem block_0110 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 110)) 0 6 :=
  check_0110_0000
theorem check_0111_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 111)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 111)) 0 6 (by decide +kernel)
theorem block_0111 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 111)) 0 6 :=
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
theorem check_0122_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 122)) 0 8 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 122)) 0 8 (by decide +kernel)
theorem check_0122_0008 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 122)) 8 16 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 122)) 8 8 (by decide +kernel)
theorem check_0122_0016 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 122)) 16 24 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 122)) 16 8 (by decide +kernel)
theorem block_0122 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 122)) 0 24 :=
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 122)) 0 8 24
  check_0122_0000
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 122)) 8 16 24
  check_0122_0008
  check_0122_0016))
theorem check_0123_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 123)) 0 8 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 123)) 0 8 (by decide +kernel)
theorem check_0123_0008 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 123)) 8 16 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 123)) 8 8 (by decide +kernel)
theorem check_0123_0016 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 123)) 16 24 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 123)) 16 8 (by decide +kernel)
theorem block_0123 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 123)) 0 24 :=
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 123)) 0 8 24
  check_0123_0000
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 123)) 8 16 24
  check_0123_0008
  check_0123_0016))
theorem check_0124_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 124)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 124)) 0 6 (by decide +kernel)
theorem block_0124 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 124)) 0 6 :=
  check_0124_0000
theorem check_0125_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 125)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 125)) 0 6 (by decide +kernel)
theorem block_0125 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 125)) 0 6 :=
  check_0125_0000
theorem check_0126_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 126)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 126)) 0 6 (by decide +kernel)
theorem block_0126 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 126)) 0 6 :=
  check_0126_0000
theorem check_0127_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 127)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 127)) 0 6 (by decide +kernel)
theorem block_0127 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 127)) 0 6 :=
  check_0127_0000
end Papers.RationalityTen.RootedCanonical.RootedSixBase02.S5T1

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase02.S5T1
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
theorem metadata_validity : FiniteChecks.Interval validity 0 blockCount :=
  (FiniteChecks.interval_append (validity) 0 64 128
  (FiniteChecks.interval_append (validity) 0 32 64
  (FiniteChecks.interval_append (validity) 0 16 32
  metadata_validity_0000
  metadata_validity_0016)
  (FiniteChecks.interval_append (validity) 32 48 64
  metadata_validity_0032
  metadata_validity_0048))
  (FiniteChecks.interval_append (validity) 64 96 128
  (FiniteChecks.interval_append (validity) 64 80 96
  metadata_validity_0064
  metadata_validity_0080)
  (FiniteChecks.interval_append (validity) 96 112 128
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
theorem metadata_symmetry_0112 : FiniteChecks.Interval symmetry 112 128 :=
  FiniteChecks.interval_of_check symmetry 112 16 (by decide +kernel)
theorem metadata_symmetry : FiniteChecks.Interval symmetry 0 blockCount :=
  (FiniteChecks.interval_append (symmetry) 0 64 128
  (FiniteChecks.interval_append (symmetry) 0 32 64
  (FiniteChecks.interval_append (symmetry) 0 16 32
  metadata_symmetry_0000
  metadata_symmetry_0016)
  (FiniteChecks.interval_append (symmetry) 32 48 64
  metadata_symmetry_0032
  metadata_symmetry_0048))
  (FiniteChecks.interval_append (symmetry) 64 96 128
  (FiniteChecks.interval_append (symmetry) 64 80 96
  metadata_symmetry_0064
  metadata_symmetry_0080)
  (FiniteChecks.interval_append (symmetry) 96 112 128
  metadata_symmetry_0096
  metadata_symmetry_0112)))
theorem metadata_normalizers :
    RawFaceNormalizers.completeCheck 5 template root raw faceWitness = true := by decide +kernel
theorem metadata_root : RawFacetEmbedding.wellFormedCheck root = true := by decide +kernel
end Papers.RationalityTen.RootedCanonical.RootedSixBase02.S5T1

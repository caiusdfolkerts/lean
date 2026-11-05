module
prelude
public import RootedSixExtra06
public import RawKindedFacePlacement
public import RootedSixExtra06OutsideData
public import RawOutsidePlacement

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra06.S5T1
open ConcreteGrowth
abbrev blockCount : Nat := 130
noncomputable def template : Cell := ⟨3, 31, [3, 5, 6, 10, 12, 17, 20, 24], [7, 14, 21, 27, 28]⟩
noncomputable def root : Cell := FacetUniverses.RootedSixExtra06.cells 0
noncomputable def records : Table (RawFacePlacement.Block × Nat) :=
(.branch 65
 (.branch 32
 (.branch 16
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf (⟨1, 4, 274960, 274960, 361617786720, 288326448720⟩, 518))
 (.leaf (⟨1, 4, 274960, 274960, 361616738145, 288326448645⟩, 783)))
 (.branch 3
 (.leaf (⟨1, 4, 274960, 274960, 361599960930, 288326447205⟩, 1204))
 (.leaf (⟨1, 4, 274960, 274960, 361331525475, 288326420325⟩, 1313))))
 (.branch 6
 (.branch 5
 (.leaf (⟨1, 4, 274960, 274960, 357036558180, 288325928805⟩, 1422))
 (.leaf (⟨1, 4, 274960, 274960, 288317081445, 288317081445⟩, 1447)))
 (.branch 7
 (.leaf (⟨1, 4, 274945, 274945, 361617786720, 288326448720⟩, 519))
 (.leaf (⟨1, 4, 274945, 274945, 361616738145, 288326448645⟩, 784)))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf (⟨1, 4, 274945, 274945, 361599960930, 288326447205⟩, 1205))
 (.leaf (⟨1, 4, 274945, 274945, 361331525475, 288326420325⟩, 1314)))
 (.branch 11
 (.leaf (⟨1, 4, 274945, 274945, 357036558180, 288325928805⟩, 1423))
 (.leaf (⟨1, 4, 274945, 274945, 288317081445, 288317081445⟩, 1448))))
 (.branch 14
 (.branch 13
 (.leaf (⟨2, 4, 274960, 274960, 361626105360, 361626105360⟩, 12714177))
 (.leaf (⟨2, 4, 274960, 274960, 361609328160, 361626104160⟩, 22937949)))
 (.branch 15
 (.leaf (⟨2, 4, 274960, 274960, 361592550945, 361626104070⟩, 40305254))
 (.leaf (⟨2, 4, 274960, 274960, 361324115505, 361626081030⟩, 45810362))))))
 (.branch 24
 (.branch 20
 (.branch 18
 (.branch 17
 (.leaf (⟨2, 4, 274960, 274960, 361055680050, 361626079350⟩, 57672559))
 (.leaf (⟨2, 4, 274960, 274960, 356760712770, 361625649270⟩, 67896331)))
 (.branch 19
 (.leaf (⟨2, 4, 274960, 274960, 352465745475, 361625618550⟩, 80544972))
 (.leaf (⟨2, 4, 274960, 274960, 288326448720, 361617786720⟩, 28443057))))
 (.branch 22
 (.branch 21
 (.leaf (⟨2, 4, 274960, 274960, 288041236050, 361617784950⟩, 73401439))
 (.leaf (⟨2, 4, 274960, 274960, 215026792020, 361617201270⟩, 87688505)))
 (.branch 23
 (.leaf (⟨1, 4, 274690, 274465, 361617786720, 288326448720⟩, 512))
 (.leaf (⟨1, 4, 274690, 274465, 361616738145, 288326448645⟩, 777)))))
 (.branch 28
 (.branch 26
 (.branch 25
 (.leaf (⟨1, 4, 274690, 274465, 361599960930, 288326447205⟩, 1198))
 (.leaf (⟨1, 4, 274690, 274465, 361331525475, 288326420325⟩, 1307)))
 (.branch 27
 (.leaf (⟨1, 4, 274690, 274465, 357036558180, 288325928805⟩, 1416))
 (.leaf (⟨1, 4, 274690, 274465, 288317081445, 288317081445⟩, 1441))))
 (.branch 30
 (.branch 29
 (.leaf (⟨2, 4, 274720, 274720, 361626105360, 361626105360⟩, 12255422))
 (.leaf (⟨2, 4, 274720, 274720, 361609328160, 361626104160⟩, 22479194)))
 (.branch 31
 (.leaf (⟨2, 4, 274720, 274720, 361592550945, 361626104070⟩, 39846499))
 (.leaf (⟨2, 4, 274720, 274720, 361324115505, 361626081030⟩, 45351607)))))))
 (.branch 48
 (.branch 40
 (.branch 36
 (.branch 34
 (.branch 33
 (.leaf (⟨2, 4, 274720, 274720, 361055680050, 361626079350⟩, 57213804))
 (.leaf (⟨2, 4, 274720, 274720, 356760712770, 361625649270⟩, 67437576)))
 (.branch 35
 (.leaf (⟨2, 4, 274720, 274720, 352465745475, 361625618550⟩, 80086217))
 (.leaf (⟨2, 4, 274720, 274720, 288326448720, 361617786720⟩, 27984302))))
 (.branch 38
 (.branch 37
 (.leaf (⟨2, 4, 274720, 274720, 288041236050, 361617784950⟩, 72942684))
 (.leaf (⟨2, 4, 274720, 274720, 215026792020, 361617201270⟩, 87229750)))
 (.branch 39
 (.leaf (⟨2, 4, 274465, 274690, 361626105360, 361626105360⟩, 12320959))
 (.leaf (⟨2, 4, 274465, 274690, 361609328160, 361626104160⟩, 22544731)))))
 (.branch 44
 (.branch 42
 (.branch 41
 (.leaf (⟨2, 4, 274465, 274690, 361592550945, 361626104070⟩, 39912036))
 (.leaf (⟨2, 4, 274465, 274690, 361324115505, 361626081030⟩, 45417144)))
 (.branch 43
 (.leaf (⟨2, 4, 274465, 274690, 361055680050, 361626079350⟩, 57279341))
 (.leaf (⟨2, 4, 274465, 274690, 356760712770, 361625649270⟩, 67503113))))
 (.branch 46
 (.branch 45
 (.leaf (⟨2, 4, 274465, 274690, 352465745475, 361625618550⟩, 80151754))
 (.leaf (⟨2, 4, 274465, 274690, 288326448720, 361617786720⟩, 28049839)))
 (.branch 47
 (.leaf (⟨2, 4, 274465, 274690, 288041236050, 361617784950⟩, 73008221))
 (.leaf (⟨2, 4, 274465, 274690, 215026792020, 361617201270⟩, 87295287))))))
 (.branch 56
 (.branch 52
 (.branch 50
 (.branch 49
 (.leaf (⟨3, 4, 274960, 274960, 361742426640, 434925761040⟩, 136610683683877993485500532))
 (.leaf (⟨3, 4, 274960, 274960, 360937120545, 434925740295⟩, 645576219939394681162039833)))
 (.branch 51
 (.leaf (⟨3, 4, 274960, 274960, 348052218930, 434925342855⟩, 965946450599042952502379298))
 (.leaf (⟨3, 4, 274960, 274960, 288191112480, 434918490480⟩, 325205989279746409821700368))))
 (.branch 54
 (.branch 53
 (.leaf (⟨3, 4, 274960, 274960, 210613265730, 434917970055⟩, 1154541756194911368838579134))
 (.leaf (⟨1, 4, 270595, 262945, 361617786720, 288326448720⟩, 523)))
 (.branch 55
 (.leaf (⟨1, 4, 270595, 262945, 361616738145, 288326448645⟩, 788))
 (.leaf (⟨1, 4, 270595, 262945, 361599960930, 288326447205⟩, 1209)))))
 (.branch 60
 (.branch 58
 (.branch 57
 (.leaf (⟨1, 4, 270595, 262945, 361331525475, 288326420325⟩, 1318))
 (.leaf (⟨1, 4, 270595, 262945, 357036558180, 288325928805⟩, 1427)))
 (.branch 59
 (.leaf (⟨1, 4, 270595, 262945, 288317081445, 288317081445⟩, 1452))
 (.leaf (⟨2, 4, 270385, 267010, 361626105360, 361626105360⟩, 12779716))))
 (.branch 62
 (.branch 61
 (.leaf (⟨2, 4, 270385, 267010, 361609328160, 361626104160⟩, 23003488))
 (.leaf (⟨2, 4, 270385, 267010, 361592550945, 361626104070⟩, 40370793)))
 (.branch 63
 (.leaf (⟨2, 4, 270385, 267010, 361324115505, 361626081030⟩, 45875901))
 (.branch 64
 (.leaf (⟨2, 4, 270385, 267010, 361055680050, 361626079350⟩, 57738098))
 (.leaf (⟨2, 4, 270385, 267010, 356760712770, 361625649270⟩, 67961870)))))))))
 (.branch 97
 (.branch 81
 (.branch 73
 (.branch 69
 (.branch 67
 (.branch 66
 (.leaf (⟨2, 4, 270385, 267010, 352465745475, 361625618550⟩, 80610511))
 (.leaf (⟨2, 4, 270385, 267010, 288326448720, 361617786720⟩, 28508596)))
 (.branch 68
 (.leaf (⟨2, 4, 270385, 267010, 288041236050, 361617784950⟩, 73466978))
 (.leaf (⟨2, 4, 270385, 267010, 215026792020, 361617201270⟩, 87754044))))
 (.branch 71
 (.branch 70
 (.leaf (⟨2, 4, 266290, 266290, 361626105360, 361626105360⟩, 12583101))
 (.leaf (⟨2, 4, 266290, 266290, 361609328160, 361626104160⟩, 22806873)))
 (.branch 72
 (.leaf (⟨2, 4, 266290, 266290, 361592550945, 361626104070⟩, 40174178))
 (.leaf (⟨2, 4, 266290, 266290, 361324115505, 361626081030⟩, 45679286)))))
 (.branch 77
 (.branch 75
 (.branch 74
 (.leaf (⟨2, 4, 266290, 266290, 361055680050, 361626079350⟩, 57541483))
 (.leaf (⟨2, 4, 266290, 266290, 356760712770, 361625649270⟩, 67765255)))
 (.branch 76
 (.leaf (⟨2, 4, 266290, 266290, 352465745475, 361625618550⟩, 80413896))
 (.leaf (⟨2, 4, 266290, 266290, 288326448720, 361617786720⟩, 28311981))))
 (.branch 79
 (.branch 78
 (.leaf (⟨2, 4, 266290, 266290, 288041236050, 361617784950⟩, 73270363))
 (.leaf (⟨2, 4, 266290, 266290, 215026792020, 361617201270⟩, 87557429)))
 (.branch 80
 (.leaf (⟨3, 4, 262945, 270595, 361742426640, 434925761040⟩, 137819683291313329543381107))
 (.leaf (⟨3, 4, 262945, 270595, 360937120545, 434925740295⟩, 646785219546830017219920408))))))
 (.branch 89
 (.branch 85
 (.branch 83
 (.branch 82
 (.leaf (⟨3, 4, 262945, 270595, 348052218930, 434925342855⟩, 967155450206478288560259873))
 (.leaf (⟨3, 4, 262945, 270595, 288191112480, 434918490480⟩, 326414988887181745879580943)))
 (.branch 84
 (.leaf (⟨3, 4, 262945, 270595, 210613265730, 434917970055⟩, 1155750755802346704896459709))
 (.leaf (⟨1, 4, 205060, 17185, 361617786720, 288326448720⟩, 521))))
 (.branch 87
 (.branch 86
 (.leaf (⟨1, 4, 205060, 17185, 361616738145, 288326448645⟩, 786))
 (.leaf (⟨1, 4, 205060, 17185, 361599960930, 288326447205⟩, 1207)))
 (.branch 88
 (.leaf (⟨1, 4, 205060, 17185, 361331525475, 288326420325⟩, 1316))
 (.leaf (⟨1, 4, 205060, 17185, 357036558180, 288325928805⟩, 1425)))))
 (.branch 93
 (.branch 91
 (.branch 90
 (.leaf (⟨1, 4, 205060, 17185, 288317081445, 288317081445⟩, 1450))
 (.leaf (⟨2, 4, 205120, 82720, 361626105360, 361626105360⟩, 12779716)))
 (.branch 92
 (.leaf (⟨2, 4, 205120, 82720, 361609328160, 361626104160⟩, 23003488))
 (.leaf (⟨2, 4, 205120, 82720, 361592550945, 361626104070⟩, 40370793))))
 (.branch 95
 (.branch 94
 (.leaf (⟨2, 4, 205120, 82720, 361324115505, 361626081030⟩, 45875901))
 (.leaf (⟨2, 4, 205120, 82720, 361055680050, 361626079350⟩, 57738098)))
 (.branch 96
 (.leaf (⟨2, 4, 205120, 82720, 356760712770, 361625649270⟩, 67961870))
 (.leaf (⟨2, 4, 205120, 82720, 352465745475, 361625618550⟩, 80610511)))))))
 (.branch 113
 (.branch 105
 (.branch 101
 (.branch 99
 (.branch 98
 (.leaf (⟨2, 4, 205120, 82720, 288326448720, 361617786720⟩, 28508596))
 (.leaf (⟨2, 4, 205120, 82720, 288041236050, 361617784950⟩, 73466978)))
 (.branch 100
 (.leaf (⟨2, 4, 205120, 82720, 215026792020, 361617201270⟩, 87754044))
 (.leaf (⟨2, 4, 200770, 81970, 361626105360, 361626105360⟩, 12452027))))
 (.branch 103
 (.branch 102
 (.leaf (⟨2, 4, 200770, 81970, 361609328160, 361626104160⟩, 22675799))
 (.leaf (⟨2, 4, 200770, 81970, 361592550945, 361626104070⟩, 40043104)))
 (.branch 104
 (.leaf (⟨2, 4, 200770, 81970, 361324115505, 361626081030⟩, 45548212))
 (.leaf (⟨2, 4, 200770, 81970, 361055680050, 361626079350⟩, 57410409)))))
 (.branch 109
 (.branch 107
 (.branch 106
 (.leaf (⟨2, 4, 200770, 81970, 356760712770, 361625649270⟩, 67634181))
 (.leaf (⟨2, 4, 200770, 81970, 352465745475, 361625618550⟩, 80282822)))
 (.branch 108
 (.leaf (⟨2, 4, 200770, 81970, 288326448720, 361617786720⟩, 28180907))
 (.leaf (⟨2, 4, 200770, 81970, 288041236050, 361617784950⟩, 73139289))))
 (.branch 111
 (.branch 110
 (.leaf (⟨2, 4, 200770, 81970, 215026792020, 361617201270⟩, 87426355))
 (.leaf (⟨3, 4, 201760, 147760, 361742426640, 434925761040⟩, 137819683291313329543381107)))
 (.branch 112
 (.leaf (⟨3, 4, 201760, 147760, 360937120545, 434925740295⟩, 646785219546830017219920408))
 (.leaf (⟨3, 4, 201760, 147760, 348052218930, 434925342855⟩, 967155450206478288560259873))))))
 (.branch 121
 (.branch 117
 (.branch 115
 (.branch 114
 (.leaf (⟨3, 4, 201760, 147760, 288191112480, 434918490480⟩, 326414988887181745879580943))
 (.leaf (⟨3, 4, 201760, 147760, 210613265730, 434917970055⟩, 1155750755802346704896459709)))
 (.branch 116
 (.leaf (⟨2, 4, 135235, 66610, 361626105360, 361626105360⟩, 12976325))
 (.leaf (⟨2, 4, 135235, 66610, 361609328160, 361626104160⟩, 23200097))))
 (.branch 119
 (.branch 118
 (.leaf (⟨2, 4, 135235, 66610, 361592550945, 361626104070⟩, 40567402))
 (.leaf (⟨2, 4, 135235, 66610, 361324115505, 361626081030⟩, 46072510)))
 (.branch 120
 (.leaf (⟨2, 4, 135235, 66610, 361055680050, 361626079350⟩, 57934707))
 (.leaf (⟨2, 4, 135235, 66610, 356760712770, 361625649270⟩, 68158479)))))
 (.branch 125
 (.branch 123
 (.branch 122
 (.leaf (⟨2, 4, 135235, 66610, 352465745475, 361625618550⟩, 80807120))
 (.leaf (⟨2, 4, 135235, 66610, 288326448720, 361617786720⟩, 28705205)))
 (.branch 124
 (.leaf (⟨2, 4, 135235, 66610, 288041236050, 361617784950⟩, 73663587))
 (.leaf (⟨2, 4, 135235, 66610, 215026792020, 361617201270⟩, 87950653))))
 (.branch 127
 (.branch 126
 (.leaf (⟨3, 4, 66610, 135235, 361742426640, 434925761040⟩, 141446442302287260631040112))
 (.leaf (⟨3, 4, 66610, 135235, 360937120545, 434925740295⟩, 650411978557803948307579413)))
 (.branch 128
 (.leaf (⟨3, 4, 66610, 135235, 348052218930, 434925342855⟩, 970782209217452219647918878))
 (.branch 129
 (.leaf (⟨3, 4, 66610, 135235, 288191112480, 434918490480⟩, 330041747898155676967239948))
 (.leaf (⟨3, 4, 66610, 135235, 210613265730, 434917970055⟩, 1159377514813320635984118714))))))))))
noncomputable def raw (i : Fin blockCount) : RawFacePlacement.Block := (records.get i.val).1
noncomputable def witness (i : Fin blockCount) (code : Nat) : Fin 2300 :=
  Fin.ofNat 2300 (Nat.land (Nat.shiftRight (records.get i.val).2 (16 * code)) 65535)
noncomputable def faceTable : Table Nat :=
(.branch 10264
 (.branch 5132
 (.branch 3084
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
 (.branch 3082
 (.leaf 14)
 (.leaf 15)))))
 (.branch 4100
 (.branch 3108
 (.branch 3096
 (.branch 3092
 (.leaf 16)
 (.leaf 17))
 (.branch 3105
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
 (.branch 5130
 (.leaf 30)
 (.leaf 31))))))
 (.branch 7175
 (.branch 6150
 (.branch 5156
 (.branch 5144
 (.branch 5140
 (.leaf 32)
 (.leaf 33))
 (.branch 5153
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
 (.branch 6156
 (.branch 6154
 (.leaf 40)
 (.leaf 41))
 (.branch 6164
 (.leaf 42)
 (.leaf 43)))
 (.branch 6180
 (.branch 6177
 (.leaf 44)
 (.leaf 45))
 (.branch 6192
 (.leaf 46)
 (.leaf 47)))))
 (.branch 8200
 (.branch 7220
 (.branch 7196
 (.branch 7182
 (.leaf 48)
 (.leaf 49))
 (.branch 7205
 (.leaf 50)
 (.leaf 51)))
 (.branch 8194
 (.branch 8193
 (.leaf 52)
 (.leaf 53))
 (.branch 8196
 (.leaf 54)
 (.leaf 55))))
 (.branch 10245
 (.branch 8224
 (.branch 8208
 (.leaf 56)
 (.leaf 57))
 (.branch 10243
 (.leaf 58)
 (.leaf 59)))
 (.branch 10250
 (.branch 10246
 (.leaf 60)
 (.leaf 61))
 (.branch 10252
 (.leaf 62)
 (.branch 10260
 (.leaf 63)
 (.leaf 64))))))))
 (.branch 17441
 (.branch 14364
 (.branch 12300
 (.branch 12291
 (.branch 10276
 (.branch 10273
 (.leaf 65)
 (.leaf 66))
 (.branch 10288
 (.leaf 67)
 (.leaf 68)))
 (.branch 12294
 (.branch 12293
 (.leaf 69)
 (.leaf 70))
 (.branch 12298
 (.leaf 71)
 (.leaf 72))))
 (.branch 12324
 (.branch 12312
 (.branch 12308
 (.leaf 73)
 (.leaf 74))
 (.branch 12321
 (.leaf 75)
 (.leaf 76)))
 (.branch 14343
 (.branch 12336
 (.leaf 77)
 (.leaf 78))
 (.branch 14350
 (.leaf 79)
 (.leaf 80)))))
 (.branch 16416
 (.branch 16386
 (.branch 14388
 (.branch 14373
 (.leaf 81)
 (.leaf 82))
 (.branch 16385
 (.leaf 83)
 (.leaf 84)))
 (.branch 16392
 (.branch 16388
 (.leaf 85)
 (.leaf 86))
 (.branch 16400
 (.leaf 87)
 (.leaf 88))))
 (.branch 17418
 (.branch 17413
 (.branch 17411
 (.leaf 89)
 (.leaf 90))
 (.branch 17414
 (.leaf 91)
 (.leaf 92)))
 (.branch 17428
 (.branch 17420
 (.leaf 93)
 (.leaf 94))
 (.branch 17432
 (.leaf 95)
 (.leaf 96))))))
 (.branch 21541
 (.branch 20500
 (.branch 20485
 (.branch 17456
 (.branch 17444
 (.leaf 97)
 (.leaf 98))
 (.branch 20483
 (.leaf 99)
 (.leaf 100)))
 (.branch 20490
 (.branch 20486
 (.leaf 101)
 (.leaf 102))
 (.branch 20492
 (.leaf 103)
 (.leaf 104))))
 (.branch 20528
 (.branch 20513
 (.branch 20504
 (.leaf 105)
 (.leaf 106))
 (.branch 20516
 (.leaf 107)
 (.leaf 108)))
 (.branch 21518
 (.branch 21511
 (.leaf 109)
 (.leaf 110))
 (.branch 21532
 (.leaf 111)
 (.leaf 112)))))
 (.branch 24600
 (.branch 24582
 (.branch 24579
 (.branch 21556
 (.leaf 113)
 (.leaf 114))
 (.branch 24581
 (.leaf 115)
 (.leaf 116)))
 (.branch 24588
 (.branch 24586
 (.leaf 117)
 (.leaf 118))
 (.branch 24596
 (.leaf 119)
 (.leaf 120))))
 (.branch 28679
 (.branch 24612
 (.branch 24609
 (.leaf 121)
 (.leaf 122))
 (.branch 24624
 (.leaf 123)
 (.leaf 124)))
 (.branch 28700
 (.branch 28686
 (.leaf 125)
 (.leaf 126))
 (.branch 28709
 (.leaf 127)
 (.branch 28724
 (.leaf 128)
 (.leaf 129)))))))))
noncomputable def faceWitness (s r : Nat) : Fin blockCount :=
  Fin.ofNat blockCount (faceTable.get (s * 1024 + r))
noncomputable def validity (i : Nat) : Bool :=
  RawFaceNormalizers.blockValidCheck 5 (raw (Fin.ofNat blockCount i))
noncomputable def placement (b : Fin blockCount) (code : Nat) : Bool :=
  RawKindedFacePlacement.check 5 (raw b) template root FacetUniverses.RootedSixExtra06.cells
    code 0 (witness b code)
noncomputable def test (i : Nat) : Bool :=
  let b := Fin.ofNat blockCount i
  FiniteChecks.checkRange (placement b)
    0 (RawFacePlacement.count (raw b).shared (raw b).shared)
noncomputable def symmetry (i : Nat) : Bool :=
  RawOutsidePlacement.blockCheck FacetUniverses.RootedSixExtra06.Outside.vertexCode root.vertices
    (raw (Fin.ofNat blockCount i))
end Papers.RationalityTen.RootedCanonical.RootedSixExtra06.S5T1

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra06.S5T1
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
theorem check_0052_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 52)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 52)) 0 6 (by decide +kernel)
theorem block_0052 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 52)) 0 6 :=
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
theorem check_0058_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 58)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 58)) 0 1 (by decide +kernel)
theorem block_0058 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 58)) 0 1 :=
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
end Papers.RationalityTen.RootedCanonical.RootedSixExtra06.S5T1

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra06.S5T1
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
theorem check_0078_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 78)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 78)) 0 2 (by decide +kernel)
theorem block_0078 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 78)) 0 2 :=
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
theorem check_0082_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 82)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 82)) 0 6 (by decide +kernel)
theorem block_0082 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 82)) 0 6 :=
  check_0082_0000
theorem check_0083_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 83)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 83)) 0 6 (by decide +kernel)
theorem block_0083 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 83)) 0 6 :=
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
theorem check_0088_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 88)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 88)) 0 1 (by decide +kernel)
theorem block_0088 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 88)) 0 1 :=
  check_0088_0000
theorem check_0089_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 89)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 89)) 0 1 (by decide +kernel)
theorem block_0089 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 89)) 0 1 :=
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
theorem check_0108_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 108)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 108)) 0 2 (by decide +kernel)
theorem block_0108 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 108)) 0 2 :=
  check_0108_0000
theorem check_0109_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 109)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 109)) 0 2 (by decide +kernel)
theorem block_0109 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 109)) 0 2 :=
  check_0109_0000
theorem check_0110_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 110)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 110)) 0 6 (by decide +kernel)
theorem block_0110 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 110)) 0 6 :=
  check_0110_0000
theorem check_0111_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 111)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 111)) 0 6 (by decide +kernel)
theorem block_0111 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 111)) 0 6 :=
  check_0111_0000
theorem check_0112_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 112)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 112)) 0 6 (by decide +kernel)
theorem block_0112 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 112)) 0 6 :=
  check_0112_0000
theorem check_0113_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 113)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 113)) 0 6 (by decide +kernel)
theorem block_0113 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 113)) 0 6 :=
  check_0113_0000
theorem check_0114_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 114)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 114)) 0 6 (by decide +kernel)
theorem block_0114 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 114)) 0 6 :=
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
end Papers.RationalityTen.RootedCanonical.RootedSixExtra06.S5T1

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra06.S5T1
theorem check_0128_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 128)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 128)) 0 6 (by decide +kernel)
theorem block_0128 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 128)) 0 6 :=
  check_0128_0000
theorem check_0129_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 129)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 129)) 0 6 (by decide +kernel)
theorem block_0129 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 129)) 0 6 :=
  check_0129_0000
end Papers.RationalityTen.RootedCanonical.RootedSixExtra06.S5T1

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra06.S5T1
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
theorem metadata_validity_0128 : FiniteChecks.Interval validity 128 130 :=
  FiniteChecks.interval_of_check validity 128 2 (by decide +kernel)
theorem metadata_validity : FiniteChecks.Interval validity 0 blockCount :=
  (FiniteChecks.interval_append (validity) 0 64 130
  (FiniteChecks.interval_append (validity) 0 32 64
  (FiniteChecks.interval_append (validity) 0 16 32
  metadata_validity_0000
  metadata_validity_0016)
  (FiniteChecks.interval_append (validity) 32 48 64
  metadata_validity_0032
  metadata_validity_0048))
  (FiniteChecks.interval_append (validity) 64 96 130
  (FiniteChecks.interval_append (validity) 64 80 96
  metadata_validity_0064
  metadata_validity_0080)
  (FiniteChecks.interval_append (validity) 96 112 130
  metadata_validity_0096
  (FiniteChecks.interval_append (validity) 112 128 130
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
theorem metadata_symmetry_0128 : FiniteChecks.Interval symmetry 128 130 :=
  FiniteChecks.interval_of_check symmetry 128 2 (by decide +kernel)
theorem metadata_symmetry : FiniteChecks.Interval symmetry 0 blockCount :=
  (FiniteChecks.interval_append (symmetry) 0 64 130
  (FiniteChecks.interval_append (symmetry) 0 32 64
  (FiniteChecks.interval_append (symmetry) 0 16 32
  metadata_symmetry_0000
  metadata_symmetry_0016)
  (FiniteChecks.interval_append (symmetry) 32 48 64
  metadata_symmetry_0032
  metadata_symmetry_0048))
  (FiniteChecks.interval_append (symmetry) 64 96 130
  (FiniteChecks.interval_append (symmetry) 64 80 96
  metadata_symmetry_0064
  metadata_symmetry_0080)
  (FiniteChecks.interval_append (symmetry) 96 112 130
  metadata_symmetry_0096
  (FiniteChecks.interval_append (symmetry) 112 128 130
  metadata_symmetry_0112
  metadata_symmetry_0128))))
theorem metadata_normalizers :
    RawFaceNormalizers.completeCheck 5 template root raw faceWitness = true := by decide +kernel
theorem metadata_root : RawFacetEmbedding.wellFormedCheck root = true := by decide +kernel
end Papers.RationalityTen.RootedCanonical.RootedSixExtra06.S5T1

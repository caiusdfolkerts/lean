module
prelude
public import RootedSixExtra05
public import RawKindedFacePlacement
public import RootedSixExtra05OutsideData
public import RawOutsidePlacement

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra05.S5T0
open ConcreteGrowth
abbrev blockCount : Nat := 123
noncomputable def template : Cell := ⟨2, 31, [3, 5, 6, 9, 10, 12, 17, 18, 24], [7, 13, 14, 19, 25, 26]⟩
noncomputable def root : Cell := FacetUniverses.RootedSixExtra05.cells 0
noncomputable def records : Table (RawFacePlacement.Block × Nat) :=
(.branch 61
 (.branch 30
 (.branch 15
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf (⟨1, 4, 274960, 274960, 361617786720, 288326448720⟩, 428))
 (.branch 2
 (.leaf (⟨1, 4, 274960, 274960, 361616738145, 288326448645⟩, 625))
 (.leaf (⟨1, 4, 274960, 274960, 361599960930, 288326447205⟩, 734))))
 (.branch 5
 (.branch 4
 (.leaf (⟨1, 4, 274960, 274960, 361331525475, 288326420325⟩, 999))
 (.leaf (⟨1, 4, 274960, 274960, 357036558180, 288325928805⟩, 1108)))
 (.branch 6
 (.leaf (⟨1, 4, 274960, 274960, 288317081445, 288317081445⟩, 1133))
 (.leaf (⟨1, 4, 274945, 274945, 361617786720, 288326448720⟩, 428)))))
 (.branch 11
 (.branch 9
 (.branch 8
 (.leaf (⟨1, 4, 274945, 274945, 361616738145, 288326448645⟩, 625))
 (.leaf (⟨1, 4, 274945, 274945, 361599960930, 288326447205⟩, 734)))
 (.branch 10
 (.leaf (⟨1, 4, 274945, 274945, 361331525475, 288326420325⟩, 999))
 (.leaf (⟨1, 4, 274945, 274945, 357036558180, 288325928805⟩, 1108))))
 (.branch 13
 (.branch 12
 (.leaf (⟨1, 4, 274945, 274945, 288317081445, 288317081445⟩, 1133))
 (.leaf (⟨2, 4, 274960, 274960, 361626105360, 361626105360⟩, 11206827)))
 (.branch 14
 (.leaf (⟨2, 4, 274960, 274960, 361609328160, 361626104160⟩, 16974083))
 (.leaf (⟨2, 4, 274960, 274960, 361592550945, 361626104070⟩, 29884872))))))
 (.branch 22
 (.branch 18
 (.branch 16
 (.leaf (⟨2, 4, 274960, 274960, 361340892720, 361626081120⟩, 22479191))
 (.branch 17
 (.leaf (⟨2, 4, 274960, 274960, 357029148225, 361625650950⟩, 35389980))
 (.leaf (⟨2, 4, 274960, 274960, 352465745475, 361625618550⟩, 54395710))))
 (.branch 20
 (.branch 19
 (.leaf (⟨2, 4, 274960, 274960, 288041236050, 361617784950⟩, 42533513))
 (.leaf (⟨2, 4, 274960, 274960, 283746268755, 361617754230⟩, 59900818)))
 (.branch 21
 (.leaf (⟨2, 4, 274960, 274960, 215026792020, 361617201270⟩, 67044351))
 (.leaf (⟨1, 4, 274690, 274465, 361617786720, 288326448720⟩, 423)))))
 (.branch 26
 (.branch 24
 (.branch 23
 (.leaf (⟨1, 4, 274690, 274465, 361616738145, 288326448645⟩, 620))
 (.leaf (⟨1, 4, 274690, 274465, 361599960930, 288326447205⟩, 729)))
 (.branch 25
 (.leaf (⟨1, 4, 274690, 274465, 361331525475, 288326420325⟩, 994))
 (.leaf (⟨1, 4, 274690, 274465, 357036558180, 288325928805⟩, 1103))))
 (.branch 28
 (.branch 27
 (.leaf (⟨1, 4, 274690, 274465, 288317081445, 288317081445⟩, 1128))
 (.leaf (⟨2, 4, 274720, 274720, 361626105360, 361626105360⟩, 10879145)))
 (.branch 29
 (.leaf (⟨2, 4, 274720, 274720, 361609328160, 361626104160⟩, 16646401))
 (.leaf (⟨2, 4, 274720, 274720, 361592550945, 361626104070⟩, 29557190)))))))
 (.branch 45
 (.branch 37
 (.branch 33
 (.branch 31
 (.leaf (⟨2, 4, 274720, 274720, 361340892720, 361626081120⟩, 22151509))
 (.branch 32
 (.leaf (⟨2, 4, 274720, 274720, 357029148225, 361625650950⟩, 35062298))
 (.leaf (⟨2, 4, 274720, 274720, 352465745475, 361625618550⟩, 54068028))))
 (.branch 35
 (.branch 34
 (.leaf (⟨2, 4, 274720, 274720, 288041236050, 361617784950⟩, 42205831))
 (.leaf (⟨2, 4, 274720, 274720, 283746268755, 361617754230⟩, 59573136)))
 (.branch 36
 (.leaf (⟨2, 4, 274720, 274720, 215026792020, 361617201270⟩, 66716669))
 (.leaf (⟨2, 4, 274465, 274690, 361626105360, 361626105360⟩, 10879145)))))
 (.branch 41
 (.branch 39
 (.branch 38
 (.leaf (⟨2, 4, 274465, 274690, 361609328160, 361626104160⟩, 16646401))
 (.leaf (⟨2, 4, 274465, 274690, 361592550945, 361626104070⟩, 29557190)))
 (.branch 40
 (.leaf (⟨2, 4, 274465, 274690, 361340892720, 361626081120⟩, 22151509))
 (.leaf (⟨2, 4, 274465, 274690, 357029148225, 361625650950⟩, 35062298))))
 (.branch 43
 (.branch 42
 (.leaf (⟨2, 4, 274465, 274690, 352465745475, 361625618550⟩, 54068028))
 (.leaf (⟨2, 4, 274465, 274690, 288041236050, 361617784950⟩, 42205831)))
 (.branch 44
 (.leaf (⟨2, 4, 274465, 274690, 283746268755, 361617754230⟩, 59573136))
 (.leaf (⟨2, 4, 274465, 274690, 215026792020, 361617201270⟩, 66716669))))))
 (.branch 53
 (.branch 49
 (.branch 47
 (.branch 46
 (.leaf (⟨3, 4, 274960, 274960, 361742426640, 434925761040⟩, 107596039731539170427732061))
 (.leaf (⟨3, 4, 274960, 274960, 141893788995, 434917935495⟩, 909126088513979939856581364)))
 (.branch 48
 (.leaf (⟨1, 4, 270595, 262945, 361617786720, 288326448720⟩, 429))
 (.leaf (⟨1, 4, 270595, 262945, 361616738145, 288326448645⟩, 626))))
 (.branch 51
 (.branch 50
 (.leaf (⟨1, 4, 270595, 262945, 361599960930, 288326447205⟩, 735))
 (.leaf (⟨1, 4, 270595, 262945, 361331525475, 288326420325⟩, 1000)))
 (.branch 52
 (.leaf (⟨1, 4, 270595, 262945, 357036558180, 288325928805⟩, 1109))
 (.leaf (⟨1, 4, 270595, 262945, 288317081445, 288317081445⟩, 1134)))))
 (.branch 57
 (.branch 55
 (.branch 54
 (.leaf (⟨2, 4, 270640, 267040, 361626105360, 361626105360⟩, 11272364))
 (.leaf (⟨2, 4, 270640, 267040, 361609328160, 361626104160⟩, 17039620)))
 (.branch 56
 (.leaf (⟨2, 4, 270640, 267040, 361592550945, 361626104070⟩, 29950409))
 (.leaf (⟨2, 4, 270640, 267040, 361340892720, 361626081120⟩, 22544728))))
 (.branch 59
 (.branch 58
 (.leaf (⟨2, 4, 270640, 267040, 357029148225, 361625650950⟩, 35455517))
 (.leaf (⟨2, 4, 270640, 267040, 352465745475, 361625618550⟩, 54461247)))
 (.branch 60
 (.leaf (⟨2, 4, 270640, 267040, 288041236050, 361617784950⟩, 42599050))
 (.leaf (⟨2, 4, 270640, 267040, 283746268755, 361617754230⟩, 59966355))))))))
 (.branch 92
 (.branch 76
 (.branch 68
 (.branch 64
 (.branch 62
 (.leaf (⟨2, 4, 270640, 267040, 215026792020, 361617201270⟩, 67109888))
 (.branch 63
 (.leaf (⟨2, 4, 270385, 267010, 361626105360, 361626105360⟩, 11272364))
 (.leaf (⟨2, 4, 270385, 267010, 361609328160, 361626104160⟩, 17039620))))
 (.branch 66
 (.branch 65
 (.leaf (⟨2, 4, 270385, 267010, 361592550945, 361626104070⟩, 29950409))
 (.leaf (⟨2, 4, 270385, 267010, 361340892720, 361626081120⟩, 22544728)))
 (.branch 67
 (.leaf (⟨2, 4, 270385, 267010, 357029148225, 361625650950⟩, 35455517))
 (.leaf (⟨2, 4, 270385, 267010, 352465745475, 361625618550⟩, 54461247)))))
 (.branch 72
 (.branch 70
 (.branch 69
 (.leaf (⟨2, 4, 270385, 267010, 288041236050, 361617784950⟩, 42599050))
 (.leaf (⟨2, 4, 270385, 267010, 283746268755, 361617754230⟩, 59966355)))
 (.branch 71
 (.leaf (⟨2, 4, 270385, 267010, 215026792020, 361617201270⟩, 67109888))
 (.leaf (⟨2, 4, 266290, 266290, 361626105360, 361626105360⟩, 11075750))))
 (.branch 74
 (.branch 73
 (.leaf (⟨2, 4, 266290, 266290, 361609328160, 361626104160⟩, 16843006))
 (.leaf (⟨2, 4, 266290, 266290, 361592550945, 361626104070⟩, 29753795)))
 (.branch 75
 (.leaf (⟨2, 4, 266290, 266290, 361340892720, 361626081120⟩, 22348114))
 (.leaf (⟨2, 4, 266290, 266290, 357029148225, 361625650950⟩, 35258903))))))
 (.branch 84
 (.branch 80
 (.branch 78
 (.branch 77
 (.leaf (⟨2, 4, 266290, 266290, 352465745475, 361625618550⟩, 54264633))
 (.leaf (⟨2, 4, 266290, 266290, 288041236050, 361617784950⟩, 42402436)))
 (.branch 79
 (.leaf (⟨2, 4, 266290, 266290, 283746268755, 361617754230⟩, 59769741))
 (.leaf (⟨2, 4, 266290, 266290, 215026792020, 361617201270⟩, 66913274))))
 (.branch 82
 (.branch 81
 (.leaf (⟨3, 4, 267040, 270640, 361742426640, 434925761040⟩, 110013965158307664978575451))
 (.leaf (⟨3, 4, 267040, 270640, 141893788995, 434917935495⟩, 911544013940748434407424754)))
 (.branch 83
 (.leaf (⟨3, 4, 262945, 270595, 361742426640, 434925761040⟩, 110013965158307664978575451))
 (.leaf (⟨3, 4, 262945, 270595, 141893788995, 434917935495⟩, 911544013940748434407424754)))))
 (.branch 88
 (.branch 86
 (.branch 85
 (.leaf (⟨1, 4, 205060, 17185, 361617786720, 288326448720⟩, 422))
 (.leaf (⟨1, 4, 205060, 17185, 361616738145, 288326448645⟩, 619)))
 (.branch 87
 (.leaf (⟨1, 4, 205060, 17185, 361599960930, 288326447205⟩, 728))
 (.leaf (⟨1, 4, 205060, 17185, 361331525475, 288326420325⟩, 993))))
 (.branch 90
 (.branch 89
 (.leaf (⟨1, 4, 205060, 17185, 357036558180, 288325928805⟩, 1102))
 (.leaf (⟨1, 4, 205060, 17185, 288317081445, 288317081445⟩, 1127)))
 (.branch 91
 (.leaf (⟨2, 4, 205120, 82720, 361626105360, 361626105360⟩, 10813608))
 (.leaf (⟨2, 4, 205120, 82720, 361609328160, 361626104160⟩, 16580864)))))))
 (.branch 107
 (.branch 99
 (.branch 95
 (.branch 93
 (.leaf (⟨2, 4, 205120, 82720, 361592550945, 361626104070⟩, 29491653))
 (.branch 94
 (.leaf (⟨2, 4, 205120, 82720, 361340892720, 361626081120⟩, 22085972))
 (.leaf (⟨2, 4, 205120, 82720, 357029148225, 361625650950⟩, 34996761))))
 (.branch 97
 (.branch 96
 (.leaf (⟨2, 4, 205120, 82720, 352465745475, 361625618550⟩, 54002491))
 (.leaf (⟨2, 4, 205120, 82720, 288041236050, 361617784950⟩, 42140294)))
 (.branch 98
 (.leaf (⟨2, 4, 205120, 82720, 283746268755, 361617754230⟩, 59507599))
 (.leaf (⟨2, 4, 205120, 82720, 215026792020, 361617201270⟩, 66651132)))))
 (.branch 103
 (.branch 101
 (.branch 100
 (.leaf (⟨2, 4, 204865, 82690, 361626105360, 361626105360⟩, 10813608))
 (.leaf (⟨2, 4, 204865, 82690, 361609328160, 361626104160⟩, 16580864)))
 (.branch 102
 (.leaf (⟨2, 4, 204865, 82690, 361592550945, 361626104070⟩, 29491653))
 (.leaf (⟨2, 4, 204865, 82690, 361340892720, 361626081120⟩, 22085972))))
 (.branch 105
 (.branch 104
 (.leaf (⟨2, 4, 204865, 82690, 357029148225, 361625650950⟩, 34996761))
 (.leaf (⟨2, 4, 204865, 82690, 352465745475, 361625618550⟩, 54002491)))
 (.branch 106
 (.leaf (⟨2, 4, 204865, 82690, 288041236050, 361617784950⟩, 42140294))
 (.leaf (⟨2, 4, 204865, 82690, 283746268755, 361617754230⟩, 59507599))))))
 (.branch 115
 (.branch 111
 (.branch 109
 (.branch 108
 (.leaf (⟨2, 4, 204865, 82690, 215026792020, 361617201270⟩, 66651132))
 (.leaf (⟨3, 4, 205840, 148240, 361742426640, 434925761040⟩, 106387095464898988271730780)))
 (.branch 110
 (.leaf (⟨3, 4, 205840, 148240, 141893788995, 434917935495⟩, 907917144247339757700580083))
 (.leaf (⟨2, 4, 135235, 66610, 361626105360, 361626105360⟩, 10879145))))
 (.branch 113
 (.branch 112
 (.leaf (⟨2, 4, 135235, 66610, 361609328160, 361626104160⟩, 16646401))
 (.leaf (⟨2, 4, 135235, 66610, 361592550945, 361626104070⟩, 29557190)))
 (.branch 114
 (.leaf (⟨2, 4, 135235, 66610, 361340892720, 361626081120⟩, 22151509))
 (.leaf (⟨2, 4, 135235, 66610, 357029148225, 361625650950⟩, 35062298)))))
 (.branch 119
 (.branch 117
 (.branch 116
 (.leaf (⟨2, 4, 135235, 66610, 352465745475, 361625618550⟩, 54068028))
 (.leaf (⟨2, 4, 135235, 66610, 288041236050, 361617784950⟩, 42205831)))
 (.branch 118
 (.leaf (⟨2, 4, 135235, 66610, 283746268755, 361617754230⟩, 59573136))
 (.leaf (⟨2, 4, 135235, 66610, 215026792020, 361617201270⟩, 66716669))))
 (.branch 121
 (.branch 120
 (.leaf (⟨3, 4, 136240, 136240, 361742426640, 434925761040⟩, 107596039731539170427732061))
 (.leaf (⟨3, 4, 136240, 136240, 141893788995, 434917935495⟩, 909126088513979939856581364)))
 (.branch 122
 (.leaf (⟨3, 4, 132145, 136195, 361742426640, 434925761040⟩, 107596039731539170427732061))
 (.leaf (⟨3, 4, 132145, 136195, 141893788995, 434917935495⟩, 909126088513979939856581364)))))))))
noncomputable def raw (i : Fin blockCount) : RawFacePlacement.Block := (records.get i.val).1
noncomputable def witness (i : Fin blockCount) (code : Nat) : Fin 2170 :=
  Fin.ofNat 2170 (Nat.land (Nat.shiftRight (records.get i.val).2 (16 * code)) 65535)
noncomputable def faceTable : Table Nat :=
(.branch 9264
 (.branch 5129
 (.branch 3081
 (.branch 2050
 (.branch 1032
 (.branch 1026
 (.leaf 0)
 (.branch 1028
 (.leaf 1)
 (.leaf 2)))
 (.branch 1056
 (.branch 1040
 (.leaf 3)
 (.leaf 4))
 (.branch 2049
 (.leaf 5)
 (.leaf 6))))
 (.branch 2080
 (.branch 2056
 (.branch 2052
 (.leaf 7)
 (.leaf 8))
 (.branch 2064
 (.leaf 9)
 (.leaf 10)))
 (.branch 3077
 (.branch 3075
 (.leaf 11)
 (.leaf 12))
 (.branch 3078
 (.leaf 13)
 (.leaf 14)))))
 (.branch 4098
 (.branch 3108
 (.branch 3090
 (.leaf 15)
 (.branch 3096
 (.leaf 16)
 (.leaf 17)))
 (.branch 3120
 (.branch 3112
 (.leaf 18)
 (.leaf 19))
 (.branch 4097
 (.leaf 20)
 (.leaf 21))))
 (.branch 4128
 (.branch 4104
 (.branch 4100
 (.leaf 22)
 (.leaf 23))
 (.branch 4112
 (.leaf 24)
 (.leaf 25)))
 (.branch 5125
 (.branch 5123
 (.leaf 26)
 (.leaf 27))
 (.branch 5126
 (.leaf 28)
 (.leaf 29))))))
 (.branch 7175
 (.branch 6149
 (.branch 5156
 (.branch 5138
 (.leaf 30)
 (.branch 5144
 (.leaf 31)
 (.leaf 32)))
 (.branch 5168
 (.branch 5160
 (.leaf 33)
 (.leaf 34))
 (.branch 6147
 (.leaf 35)
 (.leaf 36))))
 (.branch 6168
 (.branch 6153
 (.branch 6150
 (.leaf 37)
 (.leaf 38))
 (.branch 6162
 (.leaf 39)
 (.leaf 40)))
 (.branch 6184
 (.branch 6180
 (.leaf 41)
 (.leaf 42))
 (.branch 6192
 (.leaf 43)
 (.leaf 44)))))
 (.branch 9219
 (.branch 8196
 (.branch 8193
 (.branch 7224
 (.leaf 45)
 (.leaf 46))
 (.branch 8194
 (.leaf 47)
 (.leaf 48)))
 (.branch 8208
 (.branch 8200
 (.leaf 49)
 (.leaf 50))
 (.branch 8224
 (.leaf 51)
 (.leaf 52))))
 (.branch 9234
 (.branch 9222
 (.branch 9221
 (.leaf 53)
 (.leaf 54))
 (.branch 9225
 (.leaf 55)
 (.leaf 56)))
 (.branch 9252
 (.branch 9240
 (.leaf 57)
 (.leaf 58))
 (.branch 9256
 (.leaf 59)
 (.leaf 60)))))))
 (.branch 17414
 (.branch 12312
 (.branch 10276
 (.branch 10246
 (.branch 10243
 (.leaf 61)
 (.branch 10245
 (.leaf 62)
 (.leaf 63)))
 (.branch 10258
 (.branch 10249
 (.leaf 64)
 (.leaf 65))
 (.branch 10264
 (.leaf 66)
 (.leaf 67))))
 (.branch 12293
 (.branch 10288
 (.branch 10280
 (.leaf 68)
 (.leaf 69))
 (.branch 12291
 (.leaf 70)
 (.leaf 71)))
 (.branch 12297
 (.branch 12294
 (.leaf 72)
 (.leaf 73))
 (.branch 12306
 (.leaf 74)
 (.leaf 75)))))
 (.branch 16385
 (.branch 13319
 (.branch 12328
 (.branch 12324
 (.leaf 76)
 (.leaf 77))
 (.branch 12336
 (.leaf 78)
 (.leaf 79)))
 (.branch 14343
 (.branch 13368
 (.leaf 80)
 (.leaf 81))
 (.branch 14392
 (.leaf 82)
 (.leaf 83))))
 (.branch 16400
 (.branch 16388
 (.branch 16386
 (.leaf 84)
 (.leaf 85))
 (.branch 16392
 (.leaf 86)
 (.leaf 87)))
 (.branch 17411
 (.branch 16416
 (.leaf 88)
 (.leaf 89))
 (.branch 17413
 (.leaf 90)
 (.leaf 91))))))
 (.branch 18480
 (.branch 18435
 (.branch 17432
 (.branch 17417
 (.leaf 92)
 (.branch 17426
 (.leaf 93)
 (.leaf 94)))
 (.branch 17448
 (.branch 17444
 (.leaf 95)
 (.leaf 96))
 (.branch 17456
 (.leaf 97)
 (.leaf 98))))
 (.branch 18450
 (.branch 18438
 (.branch 18437
 (.leaf 99)
 (.leaf 100))
 (.branch 18441
 (.leaf 101)
 (.leaf 102)))
 (.branch 18468
 (.branch 18456
 (.leaf 103)
 (.leaf 104))
 (.branch 18472
 (.leaf 105)
 (.leaf 106)))))
 (.branch 24600
 (.branch 24581
 (.branch 19512
 (.branch 19463
 (.leaf 107)
 (.leaf 108))
 (.branch 24579
 (.leaf 109)
 (.leaf 110)))
 (.branch 24585
 (.branch 24582
 (.leaf 111)
 (.leaf 112))
 (.branch 24594
 (.leaf 113)
 (.leaf 114))))
 (.branch 25607
 (.branch 24616
 (.branch 24612
 (.leaf 115)
 (.leaf 116))
 (.branch 24624
 (.leaf 117)
 (.leaf 118)))
 (.branch 26631
 (.branch 25656
 (.leaf 119)
 (.leaf 120))
 (.branch 26680
 (.leaf 121)
 (.leaf 122))))))))
noncomputable def faceWitness (s r : Nat) : Fin blockCount :=
  Fin.ofNat blockCount (faceTable.get (s * 1024 + r))
noncomputable def validity (i : Nat) : Bool :=
  RawFaceNormalizers.blockValidCheck 5 (raw (Fin.ofNat blockCount i))
noncomputable def placement (b : Fin blockCount) (code : Nat) : Bool :=
  RawKindedFacePlacement.check 5 (raw b) template root FacetUniverses.RootedSixExtra05.cells
    code 0 (witness b code)
noncomputable def test (i : Nat) : Bool :=
  let b := Fin.ofNat blockCount i
  FiniteChecks.checkRange (placement b)
    0 (RawFacePlacement.count (raw b).shared (raw b).shared)
noncomputable def symmetry (i : Nat) : Bool :=
  RawOutsidePlacement.blockCheck FacetUniverses.RootedSixExtra05.Outside.vertexCode root.vertices
    (raw (Fin.ofNat blockCount i))
end Papers.RationalityTen.RootedCanonical.RootedSixExtra05.S5T0

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra05.S5T0
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
theorem check_0021_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 21)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 21)) 0 1 (by decide +kernel)
theorem block_0021 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 21)) 0 1 :=
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
theorem check_0045_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 45)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 45)) 0 6 (by decide +kernel)
theorem block_0045 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 45)) 0 6 :=
  check_0045_0000
theorem check_0046_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 46)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 46)) 0 6 (by decide +kernel)
theorem block_0046 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 46)) 0 6 :=
  check_0046_0000
theorem check_0047_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 47)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 47)) 0 1 (by decide +kernel)
theorem block_0047 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 47)) 0 1 :=
  check_0047_0000
theorem check_0048_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 48)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 48)) 0 1 (by decide +kernel)
theorem block_0048 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 48)) 0 1 :=
  check_0048_0000
theorem check_0049_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 49)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 49)) 0 1 (by decide +kernel)
theorem block_0049 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 49)) 0 1 :=
  check_0049_0000
theorem check_0050_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 50)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 50)) 0 1 (by decide +kernel)
theorem block_0050 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 50)) 0 1 :=
  check_0050_0000
theorem check_0051_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 51)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 51)) 0 1 (by decide +kernel)
theorem block_0051 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 51)) 0 1 :=
  check_0051_0000
theorem check_0052_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 52)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 52)) 0 1 (by decide +kernel)
theorem block_0052 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 52)) 0 1 :=
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
end Papers.RationalityTen.RootedCanonical.RootedSixExtra05.S5T0

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra05.S5T0
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
theorem check_0079_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 79)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 79)) 0 2 (by decide +kernel)
theorem block_0079 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 79)) 0 2 :=
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
theorem check_0108_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 108)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 108)) 0 6 (by decide +kernel)
theorem block_0108 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 108)) 0 6 :=
  check_0108_0000
theorem check_0109_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 109)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 109)) 0 6 (by decide +kernel)
theorem block_0109 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 109)) 0 6 :=
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
theorem check_0119_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 119)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 119)) 0 6 (by decide +kernel)
theorem block_0119 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 119)) 0 6 :=
  check_0119_0000
theorem check_0120_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 120)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 120)) 0 6 (by decide +kernel)
theorem block_0120 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 120)) 0 6 :=
  check_0120_0000
theorem check_0121_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 121)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 121)) 0 6 (by decide +kernel)
theorem block_0121 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 121)) 0 6 :=
  check_0121_0000
theorem check_0122_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 122)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 122)) 0 6 (by decide +kernel)
theorem block_0122 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 122)) 0 6 :=
  check_0122_0000
end Papers.RationalityTen.RootedCanonical.RootedSixExtra05.S5T0

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra05.S5T0
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
theorem metadata_validity_0112 : FiniteChecks.Interval validity 112 123 :=
  FiniteChecks.interval_of_check validity 112 11 (by decide +kernel)
theorem metadata_validity : FiniteChecks.Interval validity 0 blockCount :=
  (FiniteChecks.interval_append (validity) 0 64 123
  (FiniteChecks.interval_append (validity) 0 32 64
  (FiniteChecks.interval_append (validity) 0 16 32
  metadata_validity_0000
  metadata_validity_0016)
  (FiniteChecks.interval_append (validity) 32 48 64
  metadata_validity_0032
  metadata_validity_0048))
  (FiniteChecks.interval_append (validity) 64 96 123
  (FiniteChecks.interval_append (validity) 64 80 96
  metadata_validity_0064
  metadata_validity_0080)
  (FiniteChecks.interval_append (validity) 96 112 123
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
theorem metadata_symmetry_0112 : FiniteChecks.Interval symmetry 112 123 :=
  FiniteChecks.interval_of_check symmetry 112 11 (by decide +kernel)
theorem metadata_symmetry : FiniteChecks.Interval symmetry 0 blockCount :=
  (FiniteChecks.interval_append (symmetry) 0 64 123
  (FiniteChecks.interval_append (symmetry) 0 32 64
  (FiniteChecks.interval_append (symmetry) 0 16 32
  metadata_symmetry_0000
  metadata_symmetry_0016)
  (FiniteChecks.interval_append (symmetry) 32 48 64
  metadata_symmetry_0032
  metadata_symmetry_0048))
  (FiniteChecks.interval_append (symmetry) 64 96 123
  (FiniteChecks.interval_append (symmetry) 64 80 96
  metadata_symmetry_0064
  metadata_symmetry_0080)
  (FiniteChecks.interval_append (symmetry) 96 112 123
  metadata_symmetry_0096
  metadata_symmetry_0112)))
theorem metadata_normalizers :
    RawFaceNormalizers.completeCheck 5 template root raw faceWitness = true := by decide +kernel
theorem metadata_root : RawFacetEmbedding.wellFormedCheck root = true := by decide +kernel
end Papers.RationalityTen.RootedCanonical.RootedSixExtra05.S5T0

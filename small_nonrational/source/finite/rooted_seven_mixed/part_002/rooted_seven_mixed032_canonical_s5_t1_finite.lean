module
prelude
public import RootedSevenMixed032
public import RawKindedFacePlacement
public import RootedSevenMixed032OutsideData
public import RawOutsidePlacement

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed032.S5T1
open ConcreteGrowth
abbrev blockCount : Nat := 117
noncomputable def template : Cell := ⟨3, 31, [3, 5, 6, 10, 12, 17, 20, 24], [7, 14, 21, 27, 28]⟩
noncomputable def root : Cell := FacetUniverses.RootedSevenMixed032.cells 0
noncomputable def records : Table (RawFacePlacement.Block × Nat) :=
(.branch 58
 (.branch 29
 (.branch 14
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf (⟨2, 3, 274960, 274960, 434918491920, 288459547920⟩, 3473460))
 (.branch 2
 (.leaf (⟨2, 3, 274960, 274960, 434917443360, 288459546960⟩, 7209069))
 (.leaf (⟨2, 3, 274960, 274960, 434916394785, 288459546885⟩, 12320955))))
 (.branch 5
 (.branch 4
 (.leaf (⟨2, 3, 274960, 274960, 434899617585, 288459527685⟩, 13697232))
 (.leaf (⟨2, 3, 274960, 274960, 434882840370, 288459526245⟩, 15270120)))
 (.branch 6
 (.leaf (⟨2, 3, 274960, 274960, 434345969475, 288459130725⟩, 21758283))
 (.leaf (⟨2, 3, 274960, 274960, 430337263440, 288452277840⟩, 8585346)))))
 (.branch 10
 (.branch 8
 (.leaf (⟨2, 3, 274960, 274960, 430319437650, 288452276325⟩, 19005729))
 (.branch 9
 (.leaf (⟨2, 3, 274960, 274960, 425756034900, 288451757925⟩, 25493892))
 (.leaf (⟨2, 3, 274960, 274960, 361599960930, 288326447205⟩, 20382006))))
 (.branch 12
 (.branch 11
 (.leaf (⟨2, 3, 274960, 274960, 357036558180, 288325928805⟩, 26870169))
 (.leaf (⟨2, 3, 274960, 274960, 288317081445, 288317081445⟩, 28246446)))
 (.branch 13
 (.leaf (⟨2, 3, 274720, 274720, 434918491920, 288459547920⟩, 3014705))
 (.leaf (⟨2, 3, 274720, 274720, 434917443360, 288459546960⟩, 6750314))))))
 (.branch 21
 (.branch 17
 (.branch 15
 (.leaf (⟨2, 3, 274720, 274720, 434916394785, 288459546885⟩, 11862200))
 (.branch 16
 (.leaf (⟨2, 3, 274720, 274720, 434899617585, 288459527685⟩, 13238477))
 (.leaf (⟨2, 3, 274720, 274720, 434882840370, 288459526245⟩, 14811365))))
 (.branch 19
 (.branch 18
 (.leaf (⟨2, 3, 274720, 274720, 434345969475, 288459130725⟩, 21299528))
 (.leaf (⟨2, 3, 274720, 274720, 430337263440, 288452277840⟩, 8126591)))
 (.branch 20
 (.leaf (⟨2, 3, 274720, 274720, 430319437650, 288452276325⟩, 18546974))
 (.leaf (⟨2, 3, 274720, 274720, 425756034900, 288451757925⟩, 25035137)))))
 (.branch 25
 (.branch 23
 (.branch 22
 (.leaf (⟨2, 3, 274720, 274720, 361599960930, 288326447205⟩, 19923251))
 (.leaf (⟨2, 3, 274720, 274720, 357036558180, 288325928805⟩, 26411414)))
 (.branch 24
 (.leaf (⟨2, 3, 274720, 274720, 288317081445, 288317081445⟩, 27787691))
 (.leaf (⟨2, 3, 274465, 274690, 434918491920, 288459547920⟩, 3080242))))
 (.branch 27
 (.branch 26
 (.leaf (⟨2, 3, 274465, 274690, 434917443360, 288459546960⟩, 6815851))
 (.leaf (⟨2, 3, 274465, 274690, 434916394785, 288459546885⟩, 11927737)))
 (.branch 28
 (.leaf (⟨2, 3, 274465, 274690, 434899617585, 288459527685⟩, 13304014))
 (.leaf (⟨2, 3, 274465, 274690, 434882840370, 288459526245⟩, 14876902)))))))
 (.branch 43
 (.branch 36
 (.branch 32
 (.branch 30
 (.leaf (⟨2, 3, 274465, 274690, 434345969475, 288459130725⟩, 21365065))
 (.branch 31
 (.leaf (⟨2, 3, 274465, 274690, 430337263440, 288452277840⟩, 8192128))
 (.leaf (⟨2, 3, 274465, 274690, 430319437650, 288452276325⟩, 18612511))))
 (.branch 34
 (.branch 33
 (.leaf (⟨2, 3, 274465, 274690, 425756034900, 288451757925⟩, 25100674))
 (.leaf (⟨2, 3, 274465, 274690, 361599960930, 288326447205⟩, 19988788)))
 (.branch 35
 (.leaf (⟨2, 3, 274465, 274690, 357036558180, 288325928805⟩, 26476951))
 (.leaf (⟨2, 3, 274465, 274690, 288317081445, 288317081445⟩, 27853228)))))
 (.branch 39
 (.branch 37
 (.leaf (⟨3, 3, 274960, 274960, 434925761040, 361742426640⟩, 9671535686658867105366027))
 (.branch 38
 (.leaf (⟨3, 3, 274960, 274960, 434875429665, 361742409990⟩, 172879011683083458165538962))
 (.leaf (⟨3, 3, 274960, 274960, 430328804640, 361736204640⟩, 78581358885149249997439044))))
 (.branch 41
 (.branch 40
 (.leaf (⟨3, 3, 274960, 274960, 288041236050, 361617784950⟩, 296191326880382038077669624))
 (.leaf (⟨3, 3, 274960, 274960, 215026792020, 361617201270⟩, 415876809277760071521796443)))
 (.branch 42
 (.leaf (⟨2, 3, 270385, 267010, 434918491920, 288459547920⟩, 3538999))
 (.leaf (⟨2, 3, 270385, 267010, 434917443360, 288459546960⟩, 7274608))))))
 (.branch 50
 (.branch 46
 (.branch 44
 (.leaf (⟨2, 3, 270385, 267010, 434916394785, 288459546885⟩, 12386494))
 (.branch 45
 (.leaf (⟨2, 3, 270385, 267010, 434899617585, 288459527685⟩, 13762771))
 (.leaf (⟨2, 3, 270385, 267010, 434882840370, 288459526245⟩, 15335659))))
 (.branch 48
 (.branch 47
 (.leaf (⟨2, 3, 270385, 267010, 434345969475, 288459130725⟩, 21823822))
 (.leaf (⟨2, 3, 270385, 267010, 430337263440, 288452277840⟩, 8650885)))
 (.branch 49
 (.leaf (⟨2, 3, 270385, 267010, 430319437650, 288452276325⟩, 19071268))
 (.leaf (⟨2, 3, 270385, 267010, 425756034900, 288451757925⟩, 25559431)))))
 (.branch 54
 (.branch 52
 (.branch 51
 (.leaf (⟨2, 3, 270385, 267010, 361599960930, 288326447205⟩, 20447545))
 (.leaf (⟨2, 3, 270385, 267010, 357036558180, 288325928805⟩, 26935708)))
 (.branch 53
 (.leaf (⟨2, 3, 270385, 267010, 288317081445, 288317081445⟩, 28311985))
 (.leaf (⟨2, 3, 266290, 266290, 434918491920, 288459547920⟩, 3342384))))
 (.branch 56
 (.branch 55
 (.leaf (⟨2, 3, 266290, 266290, 434917443360, 288459546960⟩, 7077993))
 (.leaf (⟨2, 3, 266290, 266290, 434916394785, 288459546885⟩, 12189879)))
 (.branch 57
 (.leaf (⟨2, 3, 266290, 266290, 434899617585, 288459527685⟩, 13566156))
 (.leaf (⟨2, 3, 266290, 266290, 434882840370, 288459526245⟩, 15139044))))))))
 (.branch 87
 (.branch 72
 (.branch 65
 (.branch 61
 (.branch 59
 (.leaf (⟨2, 3, 266290, 266290, 434345969475, 288459130725⟩, 21627207))
 (.branch 60
 (.leaf (⟨2, 3, 266290, 266290, 430337263440, 288452277840⟩, 8454270))
 (.leaf (⟨2, 3, 266290, 266290, 430319437650, 288452276325⟩, 18874653))))
 (.branch 63
 (.branch 62
 (.leaf (⟨2, 3, 266290, 266290, 425756034900, 288451757925⟩, 25362816))
 (.leaf (⟨2, 3, 266290, 266290, 361599960930, 288326447205⟩, 20250930)))
 (.branch 64
 (.leaf (⟨2, 3, 266290, 266290, 357036558180, 288325928805⟩, 26739093))
 (.leaf (⟨2, 3, 266290, 266290, 288317081445, 288317081445⟩, 28115370)))))
 (.branch 68
 (.branch 66
 (.leaf (⟨3, 3, 262945, 270595, 434925761040, 361742426640⟩, 10880535294094203163246602))
 (.branch 67
 (.leaf (⟨3, 3, 262945, 270595, 434875429665, 361742409990⟩, 174088011290518794223419537))
 (.leaf (⟨3, 3, 262945, 270595, 430328804640, 361736204640⟩, 79790358492584586055319619))))
 (.branch 70
 (.branch 69
 (.leaf (⟨3, 3, 262945, 270595, 288041236050, 361617784950⟩, 297400326487817374135550199))
 (.leaf (⟨3, 3, 262945, 270595, 215026792020, 361617201270⟩, 417085808885195407579677018)))
 (.branch 71
 (.leaf (⟨2, 3, 205120, 82720, 434918491920, 288459547920⟩, 3538999))
 (.leaf (⟨2, 3, 205120, 82720, 434917443360, 288459546960⟩, 7274608))))))
 (.branch 79
 (.branch 75
 (.branch 73
 (.leaf (⟨2, 3, 205120, 82720, 434916394785, 288459546885⟩, 12386494))
 (.branch 74
 (.leaf (⟨2, 3, 205120, 82720, 434899617585, 288459527685⟩, 13762771))
 (.leaf (⟨2, 3, 205120, 82720, 434882840370, 288459526245⟩, 15335659))))
 (.branch 77
 (.branch 76
 (.leaf (⟨2, 3, 205120, 82720, 434345969475, 288459130725⟩, 21823822))
 (.leaf (⟨2, 3, 205120, 82720, 430337263440, 288452277840⟩, 8650885)))
 (.branch 78
 (.leaf (⟨2, 3, 205120, 82720, 430319437650, 288452276325⟩, 19071268))
 (.leaf (⟨2, 3, 205120, 82720, 425756034900, 288451757925⟩, 25559431)))))
 (.branch 83
 (.branch 81
 (.branch 80
 (.leaf (⟨2, 3, 205120, 82720, 361599960930, 288326447205⟩, 20447545))
 (.leaf (⟨2, 3, 205120, 82720, 357036558180, 288325928805⟩, 26935708)))
 (.branch 82
 (.leaf (⟨2, 3, 205120, 82720, 288317081445, 288317081445⟩, 28311985))
 (.leaf (⟨2, 3, 200770, 81970, 434918491920, 288459547920⟩, 3211310))))
 (.branch 85
 (.branch 84
 (.leaf (⟨2, 3, 200770, 81970, 434917443360, 288459546960⟩, 6946919))
 (.leaf (⟨2, 3, 200770, 81970, 434916394785, 288459546885⟩, 12058805)))
 (.branch 86
 (.leaf (⟨2, 3, 200770, 81970, 434899617585, 288459527685⟩, 13435082))
 (.leaf (⟨2, 3, 200770, 81970, 434882840370, 288459526245⟩, 15007970)))))))
 (.branch 102
 (.branch 94
 (.branch 90
 (.branch 88
 (.leaf (⟨2, 3, 200770, 81970, 434345969475, 288459130725⟩, 21496133))
 (.branch 89
 (.leaf (⟨2, 3, 200770, 81970, 430337263440, 288452277840⟩, 8323196))
 (.leaf (⟨2, 3, 200770, 81970, 430319437650, 288452276325⟩, 18743579))))
 (.branch 92
 (.branch 91
 (.leaf (⟨2, 3, 200770, 81970, 425756034900, 288451757925⟩, 25231742))
 (.leaf (⟨2, 3, 200770, 81970, 361599960930, 288326447205⟩, 20119856)))
 (.branch 93
 (.leaf (⟨2, 3, 200770, 81970, 357036558180, 288325928805⟩, 26608019))
 (.leaf (⟨2, 3, 200770, 81970, 288317081445, 288317081445⟩, 27984296)))))
 (.branch 98
 (.branch 96
 (.branch 95
 (.leaf (⟨3, 3, 201760, 147760, 434925761040, 361742426640⟩, 10880535294094203163246602))
 (.leaf (⟨3, 3, 201760, 147760, 434875429665, 361742409990⟩, 174088011290518794223419537)))
 (.branch 97
 (.leaf (⟨3, 3, 201760, 147760, 430328804640, 361736204640⟩, 79790358492584586055319619))
 (.leaf (⟨3, 3, 201760, 147760, 288041236050, 361617784950⟩, 297400326487817374135550199))))
 (.branch 100
 (.branch 99
 (.leaf (⟨3, 3, 201760, 147760, 215026792020, 361617201270⟩, 417085808885195407579677018))
 (.leaf (⟨2, 3, 135235, 66610, 434918491920, 288459547920⟩, 3735608)))
 (.branch 101
 (.leaf (⟨2, 3, 135235, 66610, 434917443360, 288459546960⟩, 7471217))
 (.leaf (⟨2, 3, 135235, 66610, 434916394785, 288459546885⟩, 12583103))))))
 (.branch 109
 (.branch 105
 (.branch 103
 (.leaf (⟨2, 3, 135235, 66610, 434899617585, 288459527685⟩, 13959380))
 (.branch 104
 (.leaf (⟨2, 3, 135235, 66610, 434882840370, 288459526245⟩, 15532268))
 (.leaf (⟨2, 3, 135235, 66610, 434345969475, 288459130725⟩, 22020431))))
 (.branch 107
 (.branch 106
 (.leaf (⟨2, 3, 135235, 66610, 430337263440, 288452277840⟩, 8847494))
 (.leaf (⟨2, 3, 135235, 66610, 430319437650, 288452276325⟩, 19267877)))
 (.branch 108
 (.leaf (⟨2, 3, 135235, 66610, 425756034900, 288451757925⟩, 25756040))
 (.leaf (⟨2, 3, 135235, 66610, 361599960930, 288326447205⟩, 20644154)))))
 (.branch 113
 (.branch 111
 (.branch 110
 (.leaf (⟨2, 3, 135235, 66610, 357036558180, 288325928805⟩, 27132317))
 (.leaf (⟨2, 3, 135235, 66610, 288317081445, 288317081445⟩, 28508594)))
 (.branch 112
 (.leaf (⟨4, 3, 148240, 205840, 348052218930, 434925342855⟩, 128662556854682136657922992090888622019489458438855692957147983080151336105882973567342997269003580051423995363542))
 (.leaf (⟨3, 3, 66610, 135235, 434925761040, 361742426640⟩, 14507294305068134250905607))))
 (.branch 115
 (.branch 114
 (.leaf (⟨3, 3, 66610, 135235, 434875429665, 361742409990⟩, 177714770301492725311078542))
 (.leaf (⟨3, 3, 66610, 135235, 430328804640, 361736204640⟩, 83417117503558517142978624)))
 (.branch 116
 (.leaf (⟨3, 3, 66610, 135235, 288041236050, 361617784950⟩, 301027085498791305223209204))
 (.leaf (⟨3, 3, 66610, 135235, 215026792020, 361617201270⟩, 420712567896169338667336023)))))))))
noncomputable def raw (i : Fin blockCount) : RawFacePlacement.Block := (records.get i.val).1
noncomputable def witness (i : Fin blockCount) (code : Nat) : Fin 529 :=
  Fin.ofNat 529 (Nat.land (Nat.shiftRight (records.get i.val).2 (16 * code)) 65535)
noncomputable def faceTable : Table Nat :=
(.branch 12312
 (.branch 6168
 (.branch 5126
 (.branch 3108
 (.branch 3082
 (.branch 3077
 (.leaf 0)
 (.branch 3078
 (.leaf 1)
 (.leaf 2)))
 (.branch 3096
 (.branch 3084
 (.leaf 3)
 (.leaf 4))
 (.branch 3105
 (.leaf 5)
 (.leaf 6))))
 (.branch 3152
 (.branch 3120
 (.leaf 7)
 (.branch 3140
 (.leaf 8)
 (.leaf 9)))
 (.branch 5123
 (.branch 3168
 (.leaf 10)
 (.leaf 11))
 (.branch 5125
 (.leaf 12)
 (.leaf 13)))))
 (.branch 5188
 (.branch 5144
 (.branch 5130
 (.leaf 14)
 (.branch 5132
 (.leaf 15)
 (.leaf 16)))
 (.branch 5156
 (.branch 5153
 (.leaf 17)
 (.leaf 18))
 (.branch 5168
 (.leaf 19)
 (.leaf 20))))
 (.branch 6149
 (.branch 5216
 (.branch 5200
 (.leaf 21)
 (.leaf 22))
 (.branch 6147
 (.leaf 23)
 (.leaf 24)))
 (.branch 6154
 (.branch 6150
 (.leaf 25)
 (.leaf 26))
 (.branch 6156
 (.leaf 27)
 (.leaf 28))))))
 (.branch 10246
 (.branch 7175
 (.branch 6192
 (.branch 6177
 (.leaf 29)
 (.branch 6180
 (.leaf 30)
 (.leaf 31)))
 (.branch 6224
 (.branch 6212
 (.leaf 32)
 (.leaf 33))
 (.branch 6240
 (.leaf 34)
 (.leaf 35))))
 (.branch 7268
 (.branch 7182
 (.leaf 36)
 (.branch 7205
 (.leaf 37)
 (.leaf 38)))
 (.branch 10243
 (.branch 7280
 (.leaf 39)
 (.leaf 40))
 (.branch 10245
 (.leaf 41)
 (.leaf 42)))))
 (.branch 10308
 (.branch 10264
 (.branch 10250
 (.leaf 43)
 (.branch 10252
 (.leaf 44)
 (.leaf 45)))
 (.branch 10276
 (.branch 10273
 (.leaf 46)
 (.leaf 47))
 (.branch 10288
 (.leaf 48)
 (.leaf 49))))
 (.branch 12293
 (.branch 10336
 (.branch 10320
 (.leaf 50)
 (.leaf 51))
 (.branch 12291
 (.leaf 52)
 (.leaf 53)))
 (.branch 12298
 (.branch 12294
 (.leaf 54)
 (.leaf 55))
 (.branch 12300
 (.leaf 56)
 (.leaf 57)))))))
 (.branch 20504
 (.branch 17414
 (.branch 14343
 (.branch 12336
 (.branch 12321
 (.leaf 58)
 (.branch 12324
 (.leaf 59)
 (.leaf 60)))
 (.branch 12368
 (.branch 12356
 (.leaf 61)
 (.leaf 62))
 (.branch 12384
 (.leaf 63)
 (.leaf 64))))
 (.branch 14436
 (.branch 14350
 (.leaf 65)
 (.branch 14373
 (.leaf 66)
 (.leaf 67)))
 (.branch 17411
 (.branch 14448
 (.leaf 68)
 (.leaf 69))
 (.branch 17413
 (.leaf 70)
 (.leaf 71)))))
 (.branch 17476
 (.branch 17432
 (.branch 17418
 (.leaf 72)
 (.branch 17420
 (.leaf 73)
 (.leaf 74)))
 (.branch 17444
 (.branch 17441
 (.leaf 75)
 (.leaf 76))
 (.branch 17456
 (.leaf 77)
 (.leaf 78))))
 (.branch 20485
 (.branch 17504
 (.branch 17488
 (.leaf 79)
 (.leaf 80))
 (.branch 20483
 (.leaf 81)
 (.leaf 82)))
 (.branch 20490
 (.branch 20486
 (.leaf 83)
 (.leaf 84))
 (.branch 20492
 (.leaf 85)
 (.leaf 86))))))
 (.branch 24586
 (.branch 21511
 (.branch 20528
 (.branch 20513
 (.leaf 87)
 (.branch 20516
 (.leaf 88)
 (.leaf 89)))
 (.branch 20560
 (.branch 20548
 (.leaf 90)
 (.leaf 91))
 (.branch 20576
 (.leaf 92)
 (.leaf 93))))
 (.branch 21616
 (.branch 21541
 (.branch 21518
 (.leaf 94)
 (.leaf 95))
 (.branch 21604
 (.leaf 96)
 (.leaf 97)))
 (.branch 24581
 (.branch 24579
 (.leaf 98)
 (.leaf 99))
 (.branch 24582
 (.leaf 100)
 (.leaf 101)))))
 (.branch 24656
 (.branch 24609
 (.branch 24588
 (.leaf 102)
 (.branch 24600
 (.leaf 103)
 (.leaf 104)))
 (.branch 24624
 (.branch 24612
 (.leaf 105)
 (.leaf 106))
 (.branch 24644
 (.leaf 107)
 (.leaf 108))))
 (.branch 28686
 (.branch 27740
 (.branch 24672
 (.leaf 109)
 (.leaf 110))
 (.branch 28679
 (.leaf 111)
 (.leaf 112)))
 (.branch 28772
 (.branch 28709
 (.leaf 113)
 (.leaf 114))
 (.branch 28784
 (.leaf 115)
 (.leaf 116))))))))
noncomputable def faceWitness (s r : Nat) : Fin blockCount :=
  Fin.ofNat blockCount (faceTable.get (s * 1024 + r))
noncomputable def validity (i : Nat) : Bool :=
  RawFaceNormalizers.blockValidCheck 5 (raw (Fin.ofNat blockCount i))
noncomputable def placement (b : Fin blockCount) (code : Nat) : Bool :=
  RawKindedFacePlacement.check 5 (raw b) template root FacetUniverses.RootedSevenMixed032.cells
    code 0 (witness b code)
noncomputable def test (i : Nat) : Bool :=
  let b := Fin.ofNat blockCount i
  FiniteChecks.checkRange (placement b)
    0 (RawFacePlacement.count (raw b).shared (raw b).shared)
noncomputable def symmetry (i : Nat) : Bool :=
  RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed032.Outside.vertexCode root.vertices
    (raw (Fin.ofNat blockCount i))
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed032.S5T1

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed032.S5T1
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
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed032.S5T1

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed032.S5T1
theorem check_0064_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 64)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 64)) 0 2 (by decide +kernel)
theorem block_0064 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 64)) 0 2 :=
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
theorem check_0068_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 68)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 68)) 0 6 (by decide +kernel)
theorem block_0068 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 68)) 0 6 :=
  check_0068_0000
theorem check_0069_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 69)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 69)) 0 6 (by decide +kernel)
theorem block_0069 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 69)) 0 6 :=
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
theorem check_0094_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 94)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 94)) 0 6 (by decide +kernel)
theorem block_0094 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 94)) 0 6 :=
  check_0094_0000
theorem check_0095_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 95)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 95)) 0 6 (by decide +kernel)
theorem block_0095 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 95)) 0 6 :=
  check_0095_0000
theorem check_0096_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 96)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 96)) 0 6 (by decide +kernel)
theorem block_0096 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 96)) 0 6 :=
  check_0096_0000
theorem check_0097_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 97)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 97)) 0 6 (by decide +kernel)
theorem block_0097 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 97)) 0 6 :=
  check_0097_0000
theorem check_0098_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 98)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 98)) 0 6 (by decide +kernel)
theorem block_0098 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 98)) 0 6 :=
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
theorem check_0111_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 111)) 0 8 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 111)) 0 8 (by decide +kernel)
theorem check_0111_0008 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 111)) 8 16 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 111)) 8 8 (by decide +kernel)
theorem check_0111_0016 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 111)) 16 24 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 111)) 16 8 (by decide +kernel)
theorem block_0111 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 111)) 0 24 :=
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 111)) 0 8 24
  check_0111_0000
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 111)) 8 16 24
  check_0111_0008
  check_0111_0016))
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
theorem check_0115_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 115)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 115)) 0 6 (by decide +kernel)
theorem block_0115 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 115)) 0 6 :=
  check_0115_0000
theorem check_0116_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 116)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 116)) 0 6 (by decide +kernel)
theorem block_0116 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 116)) 0 6 :=
  check_0116_0000
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed032.S5T1

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed032.S5T1
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
theorem metadata_validity_0112 : FiniteChecks.Interval validity 112 117 :=
  FiniteChecks.interval_of_check validity 112 5 (by decide +kernel)
theorem metadata_validity : FiniteChecks.Interval validity 0 blockCount :=
  (FiniteChecks.interval_append (validity) 0 64 117
  (FiniteChecks.interval_append (validity) 0 32 64
  (FiniteChecks.interval_append (validity) 0 16 32
  metadata_validity_0000
  metadata_validity_0016)
  (FiniteChecks.interval_append (validity) 32 48 64
  metadata_validity_0032
  metadata_validity_0048))
  (FiniteChecks.interval_append (validity) 64 96 117
  (FiniteChecks.interval_append (validity) 64 80 96
  metadata_validity_0064
  metadata_validity_0080)
  (FiniteChecks.interval_append (validity) 96 112 117
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
theorem metadata_symmetry_0112 : FiniteChecks.Interval symmetry 112 117 :=
  FiniteChecks.interval_of_check symmetry 112 5 (by decide +kernel)
theorem metadata_symmetry : FiniteChecks.Interval symmetry 0 blockCount :=
  (FiniteChecks.interval_append (symmetry) 0 64 117
  (FiniteChecks.interval_append (symmetry) 0 32 64
  (FiniteChecks.interval_append (symmetry) 0 16 32
  metadata_symmetry_0000
  metadata_symmetry_0016)
  (FiniteChecks.interval_append (symmetry) 32 48 64
  metadata_symmetry_0032
  metadata_symmetry_0048))
  (FiniteChecks.interval_append (symmetry) 64 96 117
  (FiniteChecks.interval_append (symmetry) 64 80 96
  metadata_symmetry_0064
  metadata_symmetry_0080)
  (FiniteChecks.interval_append (symmetry) 96 112 117
  metadata_symmetry_0096
  metadata_symmetry_0112)))
theorem metadata_normalizers :
    RawFaceNormalizers.completeCheck 5 template root raw faceWitness = true := by decide +kernel
theorem metadata_root : RawFacetEmbedding.wellFormedCheck root = true := by decide +kernel
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed032.S5T1

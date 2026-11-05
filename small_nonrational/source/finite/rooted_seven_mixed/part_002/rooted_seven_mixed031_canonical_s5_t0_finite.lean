module
prelude
public import RootedSevenMixed031
public import RawKindedFacePlacement
public import RootedSevenMixed031OutsideData
public import RawOutsidePlacement

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed031.S5T0
open ConcreteGrowth
abbrev blockCount : Nat := 159
noncomputable def template : Cell := ⟨2, 31, [3, 5, 6, 9, 10, 12, 17, 18, 24], [7, 13, 14, 19, 25, 26]⟩
noncomputable def root : Cell := FacetUniverses.RootedSevenMixed031.cells 0
noncomputable def records : Table (RawFacePlacement.Block × Nat) :=
(.branch 79
 (.branch 39
 (.branch 19
 (.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf (⟨2, 3, 274960, 274960, 434918491920, 288459547920⟩, 2883628))
 (.leaf (⟨2, 3, 274960, 274960, 434917443360, 288459546960⟩, 6619237)))
 (.branch 3
 (.leaf (⟨2, 3, 274960, 274960, 434916394785, 288459546885⟩, 11731123))
 (.leaf (⟨2, 3, 274960, 274960, 434899617585, 288459527685⟩, 13107400))))
 (.branch 6
 (.branch 5
 (.leaf (⟨2, 3, 274960, 274960, 434882840370, 288459526245⟩, 16843009))
 (.leaf (⟨2, 3, 274960, 274960, 434345969475, 288459130725⟩, 25690504)))
 (.branch 7
 (.leaf (⟨2, 3, 274960, 274960, 430337263440, 288452277840⟩, 7995514))
 (.branch 8
 (.leaf (⟨2, 3, 274960, 274960, 430319437650, 288452276325⟩, 20578618))
 (.leaf (⟨2, 3, 274960, 274960, 425756034900, 288451757925⟩, 30802390))))))
 (.branch 14
 (.branch 11
 (.branch 10
 (.leaf (⟨2, 3, 274960, 274960, 361599960930, 288326447205⟩, 21954895))
 (.leaf (⟨2, 3, 274960, 274960, 361331525475, 288326420325⟩, 27066781)))
 (.branch 12
 (.leaf (⟨2, 3, 274960, 274960, 357036558180, 288325928805⟩, 32178667))
 (.branch 13
 (.leaf (⟨2, 3, 274960, 274960, 288317081445, 288317081445⟩, 33554944))
 (.leaf (⟨2, 3, 274720, 274720, 434918491920, 288459547920⟩, 2555946)))))
 (.branch 16
 (.branch 15
 (.leaf (⟨2, 3, 274720, 274720, 434917443360, 288459546960⟩, 6291555))
 (.leaf (⟨2, 3, 274720, 274720, 434916394785, 288459546885⟩, 11403441)))
 (.branch 17
 (.leaf (⟨2, 3, 274720, 274720, 434899617585, 288459527685⟩, 12779718))
 (.branch 18
 (.leaf (⟨2, 3, 274720, 274720, 434882840370, 288459526245⟩, 16515327))
 (.leaf (⟨2, 3, 274720, 274720, 434345969475, 288459130725⟩, 25362822)))))))
 (.branch 29
 (.branch 24
 (.branch 21
 (.branch 20
 (.leaf (⟨2, 3, 274720, 274720, 430337263440, 288452277840⟩, 7667832))
 (.leaf (⟨2, 3, 274720, 274720, 430319437650, 288452276325⟩, 20250936)))
 (.branch 22
 (.leaf (⟨2, 3, 274720, 274720, 425756034900, 288451757925⟩, 30474708))
 (.branch 23
 (.leaf (⟨2, 3, 274720, 274720, 361599960930, 288326447205⟩, 21627213))
 (.leaf (⟨2, 3, 274720, 274720, 361331525475, 288326420325⟩, 26739099)))))
 (.branch 26
 (.branch 25
 (.leaf (⟨2, 3, 274720, 274720, 357036558180, 288325928805⟩, 31850985))
 (.leaf (⟨2, 3, 274720, 274720, 288317081445, 288317081445⟩, 33227262)))
 (.branch 27
 (.leaf (⟨2, 3, 274465, 274690, 434918491920, 288459547920⟩, 2555946))
 (.branch 28
 (.leaf (⟨2, 3, 274465, 274690, 434917443360, 288459546960⟩, 6291555))
 (.leaf (⟨2, 3, 274465, 274690, 434916394785, 288459546885⟩, 11403441))))))
 (.branch 34
 (.branch 31
 (.branch 30
 (.leaf (⟨2, 3, 274465, 274690, 434899617585, 288459527685⟩, 12779718))
 (.leaf (⟨2, 3, 274465, 274690, 434882840370, 288459526245⟩, 16515327)))
 (.branch 32
 (.leaf (⟨2, 3, 274465, 274690, 434345969475, 288459130725⟩, 25362822))
 (.branch 33
 (.leaf (⟨2, 3, 274465, 274690, 430337263440, 288452277840⟩, 7667832))
 (.leaf (⟨2, 3, 274465, 274690, 430319437650, 288452276325⟩, 20250936)))))
 (.branch 36
 (.branch 35
 (.leaf (⟨2, 3, 274465, 274690, 425756034900, 288451757925⟩, 30474708))
 (.leaf (⟨2, 3, 274465, 274690, 361599960930, 288326447205⟩, 21627213)))
 (.branch 37
 (.leaf (⟨2, 3, 274465, 274690, 361331525475, 288326420325⟩, 26739099))
 (.branch 38
 (.leaf (⟨2, 3, 274465, 274690, 357036558180, 288325928805⟩, 31850985))
 (.leaf (⟨2, 3, 274465, 274690, 288317081445, 288317081445⟩, 33227262))))))))
 (.branch 59
 (.branch 49
 (.branch 44
 (.branch 41
 (.branch 40
 (.leaf (⟨3, 3, 274960, 274960, 434925761040, 361742426640⟩, 2417888533843322855620614))
 (.leaf (⟨3, 3, 274960, 274960, 434875429665, 361742409990⟩, 165625364530267913915793549)))
 (.branch 42
 (.leaf (⟨3, 3, 274960, 274960, 430328804640, 361736204640⟩, 71327711732333705747693631))
 (.branch 43
 (.leaf (⟨3, 3, 274960, 274960, 361055680050, 361626079350⟩, 259923017328202122083893467))
 (.leaf (⟨3, 3, 274960, 274960, 352465745475, 361625618550⟩, 423130493324626713144066402)))))
 (.branch 46
 (.branch 45
 (.leaf (⟨3, 3, 274960, 274960, 288041236050, 361617784950⟩, 328832840526692504975966484))
 (.leaf (⟨3, 3, 274960, 274960, 215026792020, 361617201270⟩, 517428146122560921312166320)))
 (.branch 47
 (.leaf (⟨2, 3, 270640, 267040, 434918491920, 288459547920⟩, 2949165))
 (.branch 48
 (.leaf (⟨2, 3, 270640, 267040, 434917443360, 288459546960⟩, 6684774))
 (.leaf (⟨2, 3, 270640, 267040, 434916394785, 288459546885⟩, 11796660))))))
 (.branch 54
 (.branch 51
 (.branch 50
 (.leaf (⟨2, 3, 270640, 267040, 434899617585, 288459527685⟩, 13172937))
 (.leaf (⟨2, 3, 270640, 267040, 434882840370, 288459526245⟩, 16908546)))
 (.branch 52
 (.leaf (⟨2, 3, 270640, 267040, 434345969475, 288459130725⟩, 25756041))
 (.branch 53
 (.leaf (⟨2, 3, 270640, 267040, 430337263440, 288452277840⟩, 8061051))
 (.leaf (⟨2, 3, 270640, 267040, 430319437650, 288452276325⟩, 20644155)))))
 (.branch 56
 (.branch 55
 (.leaf (⟨2, 3, 270640, 267040, 425756034900, 288451757925⟩, 30867927))
 (.leaf (⟨2, 3, 270640, 267040, 361599960930, 288326447205⟩, 22020432)))
 (.branch 57
 (.leaf (⟨2, 3, 270640, 267040, 361331525475, 288326420325⟩, 27132318))
 (.branch 58
 (.leaf (⟨2, 3, 270640, 267040, 357036558180, 288325928805⟩, 32244204))
 (.leaf (⟨2, 3, 270640, 267040, 288317081445, 288317081445⟩, 33620481)))))))
 (.branch 69
 (.branch 64
 (.branch 61
 (.branch 60
 (.leaf (⟨2, 3, 270385, 267010, 434918491920, 288459547920⟩, 2949165))
 (.leaf (⟨2, 3, 270385, 267010, 434917443360, 288459546960⟩, 6684774)))
 (.branch 62
 (.leaf (⟨2, 3, 270385, 267010, 434916394785, 288459546885⟩, 11796660))
 (.branch 63
 (.leaf (⟨2, 3, 270385, 267010, 434899617585, 288459527685⟩, 13172937))
 (.leaf (⟨2, 3, 270385, 267010, 434882840370, 288459526245⟩, 16908546)))))
 (.branch 66
 (.branch 65
 (.leaf (⟨2, 3, 270385, 267010, 434345969475, 288459130725⟩, 25756041))
 (.leaf (⟨2, 3, 270385, 267010, 430337263440, 288452277840⟩, 8061051)))
 (.branch 67
 (.leaf (⟨2, 3, 270385, 267010, 430319437650, 288452276325⟩, 20644155))
 (.branch 68
 (.leaf (⟨2, 3, 270385, 267010, 425756034900, 288451757925⟩, 30867927))
 (.leaf (⟨2, 3, 270385, 267010, 361599960930, 288326447205⟩, 22020432))))))
 (.branch 74
 (.branch 71
 (.branch 70
 (.leaf (⟨2, 3, 270385, 267010, 361331525475, 288326420325⟩, 27132318))
 (.leaf (⟨2, 3, 270385, 267010, 357036558180, 288325928805⟩, 32244204)))
 (.branch 72
 (.leaf (⟨2, 3, 270385, 267010, 288317081445, 288317081445⟩, 33620481))
 (.branch 73
 (.leaf (⟨2, 3, 266290, 266290, 434918491920, 288459547920⟩, 2752551))
 (.leaf (⟨2, 3, 266290, 266290, 434917443360, 288459546960⟩, 6488160)))))
 (.branch 76
 (.branch 75
 (.leaf (⟨2, 3, 266290, 266290, 434916394785, 288459546885⟩, 11600046))
 (.leaf (⟨2, 3, 266290, 266290, 434899617585, 288459527685⟩, 12976323)))
 (.branch 77
 (.leaf (⟨2, 3, 266290, 266290, 434882840370, 288459526245⟩, 16711932))
 (.branch 78
 (.leaf (⟨2, 3, 266290, 266290, 434345969475, 288459130725⟩, 25559427))
 (.leaf (⟨2, 3, 266290, 266290, 430337263440, 288452277840⟩, 7864437)))))))))
 (.branch 119
 (.branch 99
 (.branch 89
 (.branch 84
 (.branch 81
 (.branch 80
 (.leaf (⟨2, 3, 266290, 266290, 430319437650, 288452276325⟩, 20447541))
 (.leaf (⟨2, 3, 266290, 266290, 425756034900, 288451757925⟩, 30671313)))
 (.branch 82
 (.leaf (⟨2, 3, 266290, 266290, 361599960930, 288326447205⟩, 21823818))
 (.branch 83
 (.leaf (⟨2, 3, 266290, 266290, 361331525475, 288326420325⟩, 26935704))
 (.leaf (⟨2, 3, 266290, 266290, 357036558180, 288325928805⟩, 32047590)))))
 (.branch 86
 (.branch 85
 (.leaf (⟨2, 3, 266290, 266290, 288317081445, 288317081445⟩, 33423867))
 (.leaf (⟨3, 3, 267040, 270640, 434925761040, 361742426640⟩, 4835813960611817406464004)))
 (.branch 87
 (.leaf (⟨3, 3, 267040, 270640, 434875429665, 361742409990⟩, 168043289957036408466636939))
 (.branch 88
 (.leaf (⟨3, 3, 267040, 270640, 430328804640, 361736204640⟩, 73745637159102200298537021))
 (.leaf (⟨3, 3, 267040, 270640, 361055680050, 361626079350⟩, 262340942754970616634736857))))))
 (.branch 94
 (.branch 91
 (.branch 90
 (.leaf (⟨3, 3, 267040, 270640, 352465745475, 361625618550⟩, 425548418751395207694909792))
 (.leaf (⟨3, 3, 267040, 270640, 288041236050, 361617784950⟩, 331250765953460999526809874)))
 (.branch 92
 (.leaf (⟨3, 3, 267040, 270640, 215026792020, 361617201270⟩, 519846071549329415863009710))
 (.branch 93
 (.leaf (⟨3, 3, 262945, 270595, 434925761040, 361742426640⟩, 4835813960611817406464004))
 (.leaf (⟨3, 3, 262945, 270595, 434875429665, 361742409990⟩, 168043289957036408466636939)))))
 (.branch 96
 (.branch 95
 (.leaf (⟨3, 3, 262945, 270595, 430328804640, 361736204640⟩, 73745637159102200298537021))
 (.leaf (⟨3, 3, 262945, 270595, 361055680050, 361626079350⟩, 262340942754970616634736857)))
 (.branch 97
 (.leaf (⟨3, 3, 262945, 270595, 352465745475, 361625618550⟩, 425548418751395207694909792))
 (.branch 98
 (.leaf (⟨3, 3, 262945, 270595, 288041236050, 361617784950⟩, 331250765953460999526809874))
 (.leaf (⟨3, 3, 262945, 270595, 215026792020, 361617201270⟩, 519846071549329415863009710)))))))
 (.branch 109
 (.branch 104
 (.branch 101
 (.branch 100
 (.leaf (⟨2, 3, 205120, 82720, 434918491920, 288459547920⟩, 2490409))
 (.leaf (⟨2, 3, 205120, 82720, 434917443360, 288459546960⟩, 6226018)))
 (.branch 102
 (.leaf (⟨2, 3, 205120, 82720, 434916394785, 288459546885⟩, 11337904))
 (.branch 103
 (.leaf (⟨2, 3, 205120, 82720, 434899617585, 288459527685⟩, 12714181))
 (.leaf (⟨2, 3, 205120, 82720, 434882840370, 288459526245⟩, 16449790)))))
 (.branch 106
 (.branch 105
 (.leaf (⟨2, 3, 205120, 82720, 434345969475, 288459130725⟩, 25297285))
 (.leaf (⟨2, 3, 205120, 82720, 430337263440, 288452277840⟩, 7602295)))
 (.branch 107
 (.leaf (⟨2, 3, 205120, 82720, 430319437650, 288452276325⟩, 20185399))
 (.branch 108
 (.leaf (⟨2, 3, 205120, 82720, 425756034900, 288451757925⟩, 30409171))
 (.leaf (⟨2, 3, 205120, 82720, 361599960930, 288326447205⟩, 21561676))))))
 (.branch 114
 (.branch 111
 (.branch 110
 (.leaf (⟨2, 3, 205120, 82720, 361331525475, 288326420325⟩, 26673562))
 (.leaf (⟨2, 3, 205120, 82720, 357036558180, 288325928805⟩, 31785448)))
 (.branch 112
 (.leaf (⟨2, 3, 205120, 82720, 288317081445, 288317081445⟩, 33161725))
 (.branch 113
 (.leaf (⟨2, 3, 204865, 82690, 434918491920, 288459547920⟩, 2490409))
 (.leaf (⟨2, 3, 204865, 82690, 434917443360, 288459546960⟩, 6226018)))))
 (.branch 116
 (.branch 115
 (.leaf (⟨2, 3, 204865, 82690, 434916394785, 288459546885⟩, 11337904))
 (.leaf (⟨2, 3, 204865, 82690, 434899617585, 288459527685⟩, 12714181)))
 (.branch 117
 (.leaf (⟨2, 3, 204865, 82690, 434882840370, 288459526245⟩, 16449790))
 (.branch 118
 (.leaf (⟨2, 3, 204865, 82690, 434345969475, 288459130725⟩, 25297285))
 (.leaf (⟨2, 3, 204865, 82690, 430337263440, 288452277840⟩, 7602295))))))))
 (.branch 139
 (.branch 129
 (.branch 124
 (.branch 121
 (.branch 120
 (.leaf (⟨2, 3, 204865, 82690, 430319437650, 288452276325⟩, 20185399))
 (.leaf (⟨2, 3, 204865, 82690, 425756034900, 288451757925⟩, 30409171)))
 (.branch 122
 (.leaf (⟨2, 3, 204865, 82690, 361599960930, 288326447205⟩, 21561676))
 (.branch 123
 (.leaf (⟨2, 3, 204865, 82690, 361331525475, 288326420325⟩, 26673562))
 (.leaf (⟨2, 3, 204865, 82690, 357036558180, 288325928805⟩, 31785448)))))
 (.branch 126
 (.branch 125
 (.leaf (⟨2, 3, 204865, 82690, 288317081445, 288317081445⟩, 33161725))
 (.leaf (⟨3, 3, 205840, 148240, 434925761040, 361742426640⟩, 1208944267203140699619333)))
 (.branch 127
 (.leaf (⟨3, 3, 205840, 148240, 434875429665, 361742409990⟩, 164416420263627731759792268))
 (.branch 128
 (.leaf (⟨3, 3, 205840, 148240, 430328804640, 361736204640⟩, 70118767465693523591692350))
 (.leaf (⟨3, 3, 205840, 148240, 361055680050, 361626079350⟩, 258714073061561939927892186))))))
 (.branch 134
 (.branch 131
 (.branch 130
 (.leaf (⟨3, 3, 205840, 148240, 352465745475, 361625618550⟩, 421921549057986530988065121))
 (.leaf (⟨3, 3, 205840, 148240, 288041236050, 361617784950⟩, 327623896260052322819965203)))
 (.branch 132
 (.leaf (⟨3, 3, 205840, 148240, 215026792020, 361617201270⟩, 516219201855920739156165039))
 (.branch 133
 (.leaf (⟨2, 3, 135235, 66610, 434918491920, 288459547920⟩, 2555946))
 (.leaf (⟨2, 3, 135235, 66610, 434917443360, 288459546960⟩, 6291555)))))
 (.branch 136
 (.branch 135
 (.leaf (⟨2, 3, 135235, 66610, 434916394785, 288459546885⟩, 11403441))
 (.leaf (⟨2, 3, 135235, 66610, 434899617585, 288459527685⟩, 12779718)))
 (.branch 137
 (.leaf (⟨2, 3, 135235, 66610, 434882840370, 288459526245⟩, 16515327))
 (.branch 138
 (.leaf (⟨2, 3, 135235, 66610, 434345969475, 288459130725⟩, 25362822))
 (.leaf (⟨2, 3, 135235, 66610, 430337263440, 288452277840⟩, 7667832)))))))
 (.branch 149
 (.branch 144
 (.branch 141
 (.branch 140
 (.leaf (⟨2, 3, 135235, 66610, 430319437650, 288452276325⟩, 20250936))
 (.leaf (⟨2, 3, 135235, 66610, 425756034900, 288451757925⟩, 30474708)))
 (.branch 142
 (.leaf (⟨2, 3, 135235, 66610, 361599960930, 288326447205⟩, 21627213))
 (.branch 143
 (.leaf (⟨2, 3, 135235, 66610, 361331525475, 288326420325⟩, 26739099))
 (.leaf (⟨2, 3, 135235, 66610, 357036558180, 288325928805⟩, 31850985)))))
 (.branch 146
 (.branch 145
 (.leaf (⟨2, 3, 135235, 66610, 288317081445, 288317081445⟩, 33227262))
 (.leaf (⟨3, 3, 136240, 136240, 434925761040, 361742426640⟩, 2417888533843322855620614)))
 (.branch 147
 (.leaf (⟨3, 3, 136240, 136240, 434875429665, 361742409990⟩, 165625364530267913915793549))
 (.branch 148
 (.leaf (⟨3, 3, 136240, 136240, 430328804640, 361736204640⟩, 71327711732333705747693631))
 (.leaf (⟨3, 3, 136240, 136240, 361055680050, 361626079350⟩, 259923017328202122083893467))))))
 (.branch 154
 (.branch 151
 (.branch 150
 (.leaf (⟨3, 3, 136240, 136240, 352465745475, 361625618550⟩, 423130493324626713144066402))
 (.leaf (⟨3, 3, 136240, 136240, 288041236050, 361617784950⟩, 328832840526692504975966484)))
 (.branch 152
 (.leaf (⟨3, 3, 136240, 136240, 215026792020, 361617201270⟩, 517428146122560921312166320))
 (.branch 153
 (.leaf (⟨3, 3, 132145, 136195, 434925761040, 361742426640⟩, 2417888533843322855620614))
 (.leaf (⟨3, 3, 132145, 136195, 434875429665, 361742409990⟩, 165625364530267913915793549)))))
 (.branch 156
 (.branch 155
 (.leaf (⟨3, 3, 132145, 136195, 430328804640, 361736204640⟩, 71327711732333705747693631))
 (.leaf (⟨3, 3, 132145, 136195, 361055680050, 361626079350⟩, 259923017328202122083893467)))
 (.branch 157
 (.leaf (⟨3, 3, 132145, 136195, 352465745475, 361625618550⟩, 423130493324626713144066402))
 (.branch 158
 (.leaf (⟨3, 3, 132145, 136195, 288041236050, 361617784950⟩, 328832840526692504975966484))
 (.leaf (⟨3, 3, 132145, 136195, 215026792020, 361617201270⟩, 517428146122560921312166320))))))))))
noncomputable def raw (i : Fin blockCount) : RawFacePlacement.Block := (records.get i.val).1
noncomputable def witness (i : Fin blockCount) (code : Nat) : Fin 655 :=
  Fin.ofNat 655 (Nat.land (Nat.shiftRight (records.get i.val).2 (16 * code)) 65535)
noncomputable def faceTable : Table Nat :=
(.branch 12324
 (.branch 7175
 (.branch 5153
 (.branch 3140
 (.branch 3084
 (.branch 3078
 (.branch 3077
 (.leaf 0)
 (.leaf 1))
 (.branch 3082
 (.leaf 2)
 (.leaf 3)))
 (.branch 3105
 (.branch 3096
 (.leaf 4)
 (.leaf 5))
 (.branch 3108
 (.leaf 6)
 (.branch 3120
 (.leaf 7)
 (.leaf 8)))))
 (.branch 5125
 (.branch 3152
 (.branch 3144
 (.leaf 9)
 (.leaf 10))
 (.branch 3168
 (.leaf 11)
 (.branch 5123
 (.leaf 12)
 (.leaf 13))))
 (.branch 5130
 (.branch 5126
 (.leaf 14)
 (.leaf 15))
 (.branch 5132
 (.leaf 16)
 (.branch 5144
 (.leaf 17)
 (.leaf 18))))))
 (.branch 6154
 (.branch 5200
 (.branch 5168
 (.branch 5156
 (.leaf 19)
 (.leaf 20))
 (.branch 5188
 (.leaf 21)
 (.branch 5192
 (.leaf 22)
 (.leaf 23))))
 (.branch 6147
 (.branch 5216
 (.leaf 24)
 (.leaf 25))
 (.branch 6149
 (.leaf 26)
 (.branch 6150
 (.leaf 27)
 (.leaf 28)))))
 (.branch 6192
 (.branch 6168
 (.branch 6156
 (.leaf 29)
 (.leaf 30))
 (.branch 6177
 (.leaf 31)
 (.branch 6180
 (.leaf 32)
 (.leaf 33))))
 (.branch 6216
 (.branch 6212
 (.leaf 34)
 (.leaf 35))
 (.branch 6224
 (.leaf 36)
 (.branch 6240
 (.leaf 37)
 (.leaf 38)))))))
 (.branch 10243
 (.branch 9226
 (.branch 7268
 (.branch 7205
 (.branch 7182
 (.leaf 39)
 (.leaf 40))
 (.branch 7244
 (.leaf 41)
 (.branch 7256
 (.leaf 42)
 (.leaf 43))))
 (.branch 9219
 (.branch 7280
 (.leaf 44)
 (.leaf 45))
 (.branch 9221
 (.leaf 46)
 (.branch 9222
 (.leaf 47)
 (.leaf 48)))))
 (.branch 9264
 (.branch 9240
 (.branch 9228
 (.leaf 49)
 (.leaf 50))
 (.branch 9249
 (.leaf 51)
 (.branch 9252
 (.leaf 52)
 (.leaf 53))))
 (.branch 9288
 (.branch 9284
 (.leaf 54)
 (.leaf 55))
 (.branch 9296
 (.leaf 56)
 (.branch 9312
 (.leaf 57)
 (.leaf 58))))))
 (.branch 10312
 (.branch 10264
 (.branch 10246
 (.branch 10245
 (.leaf 59)
 (.leaf 60))
 (.branch 10250
 (.leaf 61)
 (.branch 10252
 (.leaf 62)
 (.leaf 63))))
 (.branch 10276
 (.branch 10273
 (.leaf 64)
 (.leaf 65))
 (.branch 10288
 (.leaf 66)
 (.branch 10308
 (.leaf 67)
 (.leaf 68)))))
 (.branch 12294
 (.branch 10336
 (.branch 10320
 (.leaf 69)
 (.leaf 70))
 (.branch 12291
 (.leaf 71)
 (.branch 12293
 (.leaf 72)
 (.leaf 73))))
 (.branch 12300
 (.branch 12298
 (.leaf 74)
 (.leaf 75))
 (.branch 12312
 (.leaf 76)
 (.branch 12321
 (.leaf 77)
 (.leaf 78))))))))
 (.branch 18468
 (.branch 17411
 (.branch 13400
 (.branch 12384
 (.branch 12356
 (.branch 12336
 (.leaf 79)
 (.leaf 80))
 (.branch 12360
 (.leaf 81)
 (.branch 12368
 (.leaf 82)
 (.leaf 83))))
 (.branch 13326
 (.branch 13319
 (.leaf 84)
 (.leaf 85))
 (.branch 13349
 (.leaf 86)
 (.branch 13388
 (.leaf 87)
 (.leaf 88)))))
 (.branch 14373
 (.branch 13424
 (.branch 13412
 (.leaf 89)
 (.leaf 90))
 (.branch 14343
 (.leaf 91)
 (.branch 14350
 (.leaf 92)
 (.leaf 93))))
 (.branch 14424
 (.branch 14412
 (.leaf 94)
 (.leaf 95))
 (.branch 14436
 (.leaf 96)
 (.branch 14448
 (.leaf 97)
 (.leaf 98))))))
 (.branch 17480
 (.branch 17432
 (.branch 17414
 (.branch 17413
 (.leaf 99)
 (.leaf 100))
 (.branch 17418
 (.leaf 101)
 (.branch 17420
 (.leaf 102)
 (.leaf 103))))
 (.branch 17444
 (.branch 17441
 (.leaf 104)
 (.leaf 105))
 (.branch 17456
 (.leaf 106)
 (.branch 17476
 (.leaf 107)
 (.leaf 108)))))
 (.branch 18438
 (.branch 17504
 (.branch 17488
 (.leaf 109)
 (.leaf 110))
 (.branch 18435
 (.leaf 111)
 (.branch 18437
 (.leaf 112)
 (.leaf 113))))
 (.branch 18444
 (.branch 18442
 (.leaf 114)
 (.leaf 115))
 (.branch 18456
 (.leaf 116)
 (.branch 18465
 (.leaf 117)
 (.leaf 118)))))))
 (.branch 24612
 (.branch 19544
 (.branch 18528
 (.branch 18500
 (.branch 18480
 (.leaf 119)
 (.leaf 120))
 (.branch 18504
 (.leaf 121)
 (.branch 18512
 (.leaf 122)
 (.leaf 123))))
 (.branch 19470
 (.branch 19463
 (.leaf 124)
 (.leaf 125))
 (.branch 19493
 (.leaf 126)
 (.branch 19532
 (.leaf 127)
 (.leaf 128)))))
 (.branch 24582
 (.branch 19568
 (.branch 19556
 (.leaf 129)
 (.leaf 130))
 (.branch 24579
 (.leaf 131)
 (.branch 24581
 (.leaf 132)
 (.leaf 133))))
 (.branch 24588
 (.branch 24586
 (.leaf 134)
 (.leaf 135))
 (.branch 24600
 (.leaf 136)
 (.branch 24609
 (.leaf 137)
 (.leaf 138))))))
 (.branch 25688
 (.branch 24672
 (.branch 24644
 (.branch 24624
 (.leaf 139)
 (.leaf 140))
 (.branch 24648
 (.leaf 141)
 (.branch 24656
 (.leaf 142)
 (.leaf 143))))
 (.branch 25614
 (.branch 25607
 (.leaf 144)
 (.leaf 145))
 (.branch 25637
 (.leaf 146)
 (.branch 25676
 (.leaf 147)
 (.leaf 148)))))
 (.branch 26661
 (.branch 25712
 (.branch 25700
 (.leaf 149)
 (.leaf 150))
 (.branch 26631
 (.leaf 151)
 (.branch 26638
 (.leaf 152)
 (.leaf 153))))
 (.branch 26712
 (.branch 26700
 (.leaf 154)
 (.leaf 155))
 (.branch 26724
 (.leaf 156)
 (.branch 26736
 (.leaf 157)
 (.leaf 158)))))))))
noncomputable def faceWitness (s r : Nat) : Fin blockCount :=
  Fin.ofNat blockCount (faceTable.get (s * 1024 + r))
noncomputable def validity (i : Nat) : Bool :=
  RawFaceNormalizers.blockValidCheck 5 (raw (Fin.ofNat blockCount i))
noncomputable def placement (b : Fin blockCount) (code : Nat) : Bool :=
  RawKindedFacePlacement.check 5 (raw b) template root FacetUniverses.RootedSevenMixed031.cells
    code 0 (witness b code)
noncomputable def test (i : Nat) : Bool :=
  let b := Fin.ofNat blockCount i
  FiniteChecks.checkRange (placement b)
    0 (RawFacePlacement.count (raw b).shared (raw b).shared)
noncomputable def symmetry (i : Nat) : Bool :=
  RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed031.Outside.vertexCode root.vertices
    (raw (Fin.ofNat blockCount i))
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed031.S5T0

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed031.S5T0
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
theorem check_0044_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 44)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 44)) 0 6 (by decide +kernel)
theorem block_0044 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 44)) 0 6 :=
  check_0044_0000
theorem check_0045_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 45)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 45)) 0 6 (by decide +kernel)
theorem block_0045 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 45)) 0 6 :=
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
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed031.S5T0

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed031.S5T0
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
theorem check_0085_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 85)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 85)) 0 6 (by decide +kernel)
theorem block_0085 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 85)) 0 6 :=
  check_0085_0000
theorem check_0086_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 86)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 86)) 0 6 (by decide +kernel)
theorem block_0086 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 86)) 0 6 :=
  check_0086_0000
theorem check_0087_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 87)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 87)) 0 6 (by decide +kernel)
theorem block_0087 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 87)) 0 6 :=
  check_0087_0000
theorem check_0088_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 88)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 88)) 0 6 (by decide +kernel)
theorem block_0088 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 88)) 0 6 :=
  check_0088_0000
theorem check_0089_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 89)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 89)) 0 6 (by decide +kernel)
theorem block_0089 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 89)) 0 6 :=
  check_0089_0000
theorem check_0090_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 90)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 90)) 0 6 (by decide +kernel)
theorem block_0090 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 90)) 0 6 :=
  check_0090_0000
theorem check_0091_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 91)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 91)) 0 6 (by decide +kernel)
theorem block_0091 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 91)) 0 6 :=
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
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed031.S5T0

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed031.S5T0
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
theorem check_0144_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 144)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 144)) 0 2 (by decide +kernel)
theorem block_0144 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 144)) 0 2 :=
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
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed031.S5T0

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed031.S5T0
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
theorem metadata_validity_0144 : FiniteChecks.Interval validity 144 159 :=
  FiniteChecks.interval_of_check validity 144 15 (by decide +kernel)
theorem metadata_validity : FiniteChecks.Interval validity 0 blockCount :=
  (FiniteChecks.interval_append (validity) 0 80 159
  (FiniteChecks.interval_append (validity) 0 32 80
  (FiniteChecks.interval_append (validity) 0 16 32
  metadata_validity_0000
  metadata_validity_0016)
  (FiniteChecks.interval_append (validity) 32 48 80
  metadata_validity_0032
  (FiniteChecks.interval_append (validity) 48 64 80
  metadata_validity_0048
  metadata_validity_0064)))
  (FiniteChecks.interval_append (validity) 80 112 159
  (FiniteChecks.interval_append (validity) 80 96 112
  metadata_validity_0080
  metadata_validity_0096)
  (FiniteChecks.interval_append (validity) 112 128 159
  metadata_validity_0112
  (FiniteChecks.interval_append (validity) 128 144 159
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
theorem metadata_symmetry_0144 : FiniteChecks.Interval symmetry 144 159 :=
  FiniteChecks.interval_of_check symmetry 144 15 (by decide +kernel)
theorem metadata_symmetry : FiniteChecks.Interval symmetry 0 blockCount :=
  (FiniteChecks.interval_append (symmetry) 0 80 159
  (FiniteChecks.interval_append (symmetry) 0 32 80
  (FiniteChecks.interval_append (symmetry) 0 16 32
  metadata_symmetry_0000
  metadata_symmetry_0016)
  (FiniteChecks.interval_append (symmetry) 32 48 80
  metadata_symmetry_0032
  (FiniteChecks.interval_append (symmetry) 48 64 80
  metadata_symmetry_0048
  metadata_symmetry_0064)))
  (FiniteChecks.interval_append (symmetry) 80 112 159
  (FiniteChecks.interval_append (symmetry) 80 96 112
  metadata_symmetry_0080
  metadata_symmetry_0096)
  (FiniteChecks.interval_append (symmetry) 112 128 159
  metadata_symmetry_0112
  (FiniteChecks.interval_append (symmetry) 128 144 159
  metadata_symmetry_0128
  metadata_symmetry_0144))))
theorem metadata_normalizers :
    RawFaceNormalizers.completeCheck 5 template root raw faceWitness = true := by decide +kernel
theorem metadata_root : RawFacetEmbedding.wellFormedCheck root = true := by decide +kernel
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed031.S5T0

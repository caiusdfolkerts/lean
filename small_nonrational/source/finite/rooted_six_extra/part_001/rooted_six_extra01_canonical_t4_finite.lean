module
prelude
public import RootedSixExtra01
public import RawKindedFacePlacement
public import RootedSixExtra01OutsideData
public import RawOutsidePlacement

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra01.T4
open ConcreteGrowth
abbrev blockCount : Nat := 140
noncomputable def template : Cell := ⟨10, 63, [3, 5, 6, 10, 12, 20, 24, 33, 36, 48], [7, 14, 28, 37, 52, 59]⟩
noncomputable def root : Cell := FacetUniverses.RootedSixExtra01.cells 0
noncomputable def records : Table (RawFacePlacement.Block × Nat) :=
(.branch 70
 (.branch 35
 (.branch 17
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf (⟨2, 4, 5517840, 5517840, 361626105360, 361626105360⟩, 143853710))
 (.leaf (⟨2, 4, 5517840, 5517840, 361609328160, 361626104160⟩, 146999486)))
 (.branch 3
 (.leaf (⟨2, 4, 5517840, 5517840, 361592550945, 361626104070⟩, 150145262))
 (.leaf (⟨2, 4, 5517840, 5517840, 361340892720, 361626081120⟩, 158009702))))
 (.branch 6
 (.branch 5
 (.leaf (⟨2, 4, 5517840, 5517840, 361324115505, 361626081030⟩, 161155478))
 (.leaf (⟨2, 4, 5517840, 5517840, 361055680050, 361626079350⟩, 169019918)))
 (.branch 7
 (.leaf (⟨2, 4, 5517840, 5517840, 357029148225, 361625650950⟩, 176884358))
 (.leaf (⟨2, 4, 5517840, 5517840, 356760712770, 361625649270⟩, 180030134)))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf (⟨2, 4, 5517840, 5517840, 288041236050, 361617784950⟩, 187894574))
 (.leaf (⟨2, 4, 5517840, 5517840, 283746268755, 361617754230⟩, 191040350)))
 (.branch 11
 (.leaf (⟨2, 4, 5517840, 5517840, 215026792020, 361617201270⟩, 198904790))
 (.leaf (⟨2, 4, 5517600, 5517600, 361626105360, 361626105360⟩, 145885350))))
 (.branch 14
 (.branch 13
 (.leaf (⟨2, 4, 5517600, 5517600, 361609328160, 361626104160⟩, 149031126))
 (.leaf (⟨2, 4, 5517600, 5517600, 361592550945, 361626104070⟩, 152176902)))
 (.branch 15
 (.leaf (⟨2, 4, 5517600, 5517600, 361340892720, 361626081120⟩, 160041342))
 (.branch 16
 (.leaf (⟨2, 4, 5517600, 5517600, 361324115505, 361626081030⟩, 163187118))
 (.leaf (⟨2, 4, 5517600, 5517600, 361055680050, 361626079350⟩, 171051558)))))))
 (.branch 26
 (.branch 21
 (.branch 19
 (.branch 18
 (.leaf (⟨2, 4, 5517600, 5517600, 357029148225, 361625650950⟩, 178915998))
 (.leaf (⟨2, 4, 5517600, 5517600, 356760712770, 361625649270⟩, 182061774)))
 (.branch 20
 (.leaf (⟨2, 4, 5517600, 5517600, 288041236050, 361617784950⟩, 189926214))
 (.leaf (⟨2, 4, 5517600, 5517600, 283746268755, 361617754230⟩, 193071990))))
 (.branch 23
 (.branch 22
 (.leaf (⟨2, 4, 5517600, 5517600, 215026792020, 361617201270⟩, 200936430))
 (.leaf (⟨2, 4, 5517345, 5517570, 361626105360, 361626105360⟩, 146213035)))
 (.branch 24
 (.leaf (⟨2, 4, 5517345, 5517570, 361609328160, 361626104160⟩, 149358811))
 (.branch 25
 (.leaf (⟨2, 4, 5517345, 5517570, 361592550945, 361626104070⟩, 152504587))
 (.leaf (⟨2, 4, 5517345, 5517570, 361340892720, 361626081120⟩, 160369027))))))
 (.branch 30
 (.branch 28
 (.branch 27
 (.leaf (⟨2, 4, 5517345, 5517570, 361324115505, 361626081030⟩, 163514803))
 (.leaf (⟨2, 4, 5517345, 5517570, 361055680050, 361626079350⟩, 171379243)))
 (.branch 29
 (.leaf (⟨2, 4, 5517345, 5517570, 357029148225, 361625650950⟩, 179243683))
 (.leaf (⟨2, 4, 5517345, 5517570, 356760712770, 361625649270⟩, 182389459))))
 (.branch 32
 (.branch 31
 (.leaf (⟨2, 4, 5517345, 5517570, 288041236050, 361617784950⟩, 190253899))
 (.leaf (⟨2, 4, 5517345, 5517570, 283746268755, 361617754230⟩, 193399675)))
 (.branch 33
 (.leaf (⟨2, 4, 5517345, 5517570, 215026792020, 361617201270⟩, 201264115))
 (.branch 34
 (.leaf (⟨3, 4, 5517840, 5517840, 361742426640, 434925761040⟩, 2842227878634251629696846110))
 (.leaf (⟨3, 4, 5517840, 5517840, 361473991440, 434925741840⟩, 3045330515429802231905061318))))))))
 (.branch 52
 (.branch 43
 (.branch 39
 (.branch 37
 (.branch 36
 (.leaf (⟨3, 4, 5517840, 5517840, 361205556000, 434925740400⟩, 3190403827426624090625215038))
 (.leaf (⟨3, 4, 5517840, 5517840, 356642153505, 434925371655⟩, 3393506464222174692833430246)))
 (.branch 38
 (.leaf (⟨3, 4, 5517840, 5517840, 279332742450, 434918461575⟩, 3596609101017725295041645454))
 (.leaf (⟨3, 4, 5517840, 5517840, 210613265730, 434917970055⟩, 3741682413014547153761799174))))
 (.branch 41
 (.branch 40
 (.leaf (⟨2, 4, 5513265, 5509890, 361626105360, 361626105360⟩, 143984791))
 (.leaf (⟨2, 4, 5513265, 5509890, 361609328160, 361626104160⟩, 147130567)))
 (.branch 42
 (.leaf (⟨2, 4, 5513265, 5509890, 361592550945, 361626104070⟩, 150276343))
 (.leaf (⟨2, 4, 5513265, 5509890, 361340892720, 361626081120⟩, 158140783)))))
 (.branch 47
 (.branch 45
 (.branch 44
 (.leaf (⟨2, 4, 5513265, 5509890, 361324115505, 361626081030⟩, 161286559))
 (.leaf (⟨2, 4, 5513265, 5509890, 361055680050, 361626079350⟩, 169150999)))
 (.branch 46
 (.leaf (⟨2, 4, 5513265, 5509890, 357029148225, 361625650950⟩, 177015439))
 (.leaf (⟨2, 4, 5513265, 5509890, 356760712770, 361625649270⟩, 180161215))))
 (.branch 49
 (.branch 48
 (.leaf (⟨2, 4, 5513265, 5509890, 288041236050, 361617784950⟩, 188025655))
 (.leaf (⟨2, 4, 5513265, 5509890, 283746268755, 361617754230⟩, 191171431)))
 (.branch 50
 (.leaf (⟨2, 4, 5513265, 5509890, 215026792020, 361617201270⟩, 199035871))
 (.branch 51
 (.leaf (⟨2, 4, 5509170, 5509170, 361626105360, 361626105360⟩, 145557689))
 (.leaf (⟨2, 4, 5509170, 5509170, 361609328160, 361626104160⟩, 148703465)))))))
 (.branch 61
 (.branch 56
 (.branch 54
 (.branch 53
 (.leaf (⟨2, 4, 5509170, 5509170, 361592550945, 361626104070⟩, 151849241))
 (.leaf (⟨2, 4, 5509170, 5509170, 361340892720, 361626081120⟩, 159713681)))
 (.branch 55
 (.leaf (⟨2, 4, 5509170, 5509170, 361324115505, 361626081030⟩, 162859457))
 (.leaf (⟨2, 4, 5509170, 5509170, 361055680050, 361626079350⟩, 170723897))))
 (.branch 58
 (.branch 57
 (.leaf (⟨2, 4, 5509170, 5509170, 357029148225, 361625650950⟩, 178588337))
 (.leaf (⟨2, 4, 5509170, 5509170, 356760712770, 361625649270⟩, 181734113)))
 (.branch 59
 (.leaf (⟨2, 4, 5509170, 5509170, 288041236050, 361617784950⟩, 189598553))
 (.branch 60
 (.leaf (⟨2, 4, 5509170, 5509170, 283746268755, 361617754230⟩, 192744329))
 (.leaf (⟨2, 4, 5509170, 5509170, 215026792020, 361617201270⟩, 200608769))))))
 (.branch 65
 (.branch 63
 (.branch 62
 (.leaf (⟨3, 4, 5505825, 5513475, 361742426640, 434925761040⟩, 2830138417523076110805174567))
 (.leaf (⟨3, 4, 5505825, 5513475, 361473991440, 434925741840⟩, 3033241054318626713013389775)))
 (.branch 64
 (.leaf (⟨3, 4, 5505825, 5513475, 361205556000, 434925740400⟩, 3178314366315448571733543495))
 (.leaf (⟨3, 4, 5505825, 5513475, 356642153505, 434925371655⟩, 3381417003110999173941758703))))
 (.branch 67
 (.branch 66
 (.leaf (⟨3, 4, 5505825, 5513475, 279332742450, 434918461575⟩, 3584519639906549776149973911))
 (.leaf (⟨3, 4, 5505825, 5513475, 210613265730, 434917970055⟩, 3729592951903371634870127631)))
 (.branch 68
 (.leaf (⟨2, 4, 5443650, 5324850, 361626105360, 361626105360⟩, 145819837))
 (.branch 69
 (.leaf (⟨2, 4, 5443650, 5324850, 361609328160, 361626104160⟩, 148965613))
 (.leaf (⟨2, 4, 5443650, 5324850, 361592550945, 361626104070⟩, 152111389)))))))))
 (.branch 105
 (.branch 87
 (.branch 78
 (.branch 74
 (.branch 72
 (.branch 71
 (.leaf (⟨2, 4, 5443650, 5324850, 361340892720, 361626081120⟩, 159975829))
 (.leaf (⟨2, 4, 5443650, 5324850, 361324115505, 361626081030⟩, 163121605)))
 (.branch 73
 (.leaf (⟨2, 4, 5443650, 5324850, 361055680050, 361626079350⟩, 170986045))
 (.leaf (⟨2, 4, 5443650, 5324850, 357029148225, 361625650950⟩, 178850485))))
 (.branch 76
 (.branch 75
 (.leaf (⟨2, 4, 5443650, 5324850, 356760712770, 361625649270⟩, 181996261))
 (.leaf (⟨2, 4, 5443650, 5324850, 288041236050, 361617784950⟩, 189860701)))
 (.branch 77
 (.leaf (⟨2, 4, 5443650, 5324850, 283746268755, 361617754230⟩, 193006477))
 (.leaf (⟨2, 4, 5443650, 5324850, 215026792020, 361617201270⟩, 200870917)))))
 (.branch 82
 (.branch 80
 (.branch 79
 (.leaf (⟨2, 4, 5378115, 5309490, 361626105360, 361626105360⟩, 144443550))
 (.leaf (⟨2, 4, 5378115, 5309490, 361609328160, 361626104160⟩, 147589326)))
 (.branch 81
 (.leaf (⟨2, 4, 5378115, 5309490, 361592550945, 361626104070⟩, 150735102))
 (.leaf (⟨2, 4, 5378115, 5309490, 361340892720, 361626081120⟩, 158599542))))
 (.branch 84
 (.branch 83
 (.leaf (⟨2, 4, 5378115, 5309490, 361324115505, 361626081030⟩, 161745318))
 (.leaf (⟨2, 4, 5378115, 5309490, 361055680050, 361626079350⟩, 169609758)))
 (.branch 85
 (.leaf (⟨2, 4, 5378115, 5309490, 357029148225, 361625650950⟩, 177474198))
 (.branch 86
 (.leaf (⟨2, 4, 5378115, 5309490, 356760712770, 361625649270⟩, 180619974))
 (.leaf (⟨2, 4, 5378115, 5309490, 288041236050, 361617784950⟩, 188484414)))))))
 (.branch 96
 (.branch 91
 (.branch 89
 (.branch 88
 (.leaf (⟨2, 4, 5378115, 5309490, 283746268755, 361617754230⟩, 191630190))
 (.leaf (⟨2, 4, 5378115, 5309490, 215026792020, 361617201270⟩, 199494630)))
 (.branch 90
 (.leaf (⟨3, 4, 5309490, 5378115, 361742426640, 434925761040⟩, 2824093917555307666987288878))
 (.leaf (⟨3, 4, 5309490, 5378115, 361473991440, 434925741840⟩, 3027196554350858269195504086))))
 (.branch 93
 (.branch 92
 (.leaf (⟨3, 4, 5309490, 5378115, 361205556000, 434925740400⟩, 3172269866347680127915657806))
 (.leaf (⟨3, 4, 5309490, 5378115, 356642153505, 434925371655⟩, 3375372503143230730123873014)))
 (.branch 94
 (.leaf (⟨3, 4, 5309490, 5378115, 279332742450, 434918461575⟩, 3578475139938781332332088222))
 (.branch 95
 (.leaf (⟨3, 4, 5309490, 5378115, 210613265730, 434917970055⟩, 3723548451935603191052241942))
 (.leaf (⟨2, 4, 4399440, 1393440, 361626105360, 361626105360⟩, 143919257))))))
 (.branch 100
 (.branch 98
 (.branch 97
 (.leaf (⟨2, 4, 4399440, 1393440, 361609328160, 361626104160⟩, 147065033))
 (.leaf (⟨2, 4, 4399440, 1393440, 361592550945, 361626104070⟩, 150210809)))
 (.branch 99
 (.leaf (⟨2, 4, 4399440, 1393440, 361340892720, 361626081120⟩, 158075249))
 (.leaf (⟨2, 4, 4399440, 1393440, 361324115505, 361626081030⟩, 161221025))))
 (.branch 102
 (.branch 101
 (.leaf (⟨2, 4, 4399440, 1393440, 361055680050, 361626079350⟩, 169085465))
 (.leaf (⟨2, 4, 4399440, 1393440, 357029148225, 361625650950⟩, 176949905)))
 (.branch 103
 (.leaf (⟨2, 4, 4399440, 1393440, 356760712770, 361625649270⟩, 180095681))
 (.branch 104
 (.leaf (⟨2, 4, 4399440, 1393440, 288041236050, 361617784950⟩, 187960121))
 (.leaf (⟨2, 4, 4399440, 1393440, 283746268755, 361617754230⟩, 191105897))))))))
 (.branch 122
 (.branch 113
 (.branch 109
 (.branch 107
 (.branch 106
 (.leaf (⟨2, 4, 4399440, 1393440, 215026792020, 361617201270⟩, 198970337))
 (.leaf (⟨2, 4, 4395090, 1392690, 361626105360, 361626105360⟩, 145098930)))
 (.branch 108
 (.leaf (⟨2, 4, 4395090, 1392690, 361609328160, 361626104160⟩, 148244706))
 (.leaf (⟨2, 4, 4395090, 1392690, 361592550945, 361626104070⟩, 151390482))))
 (.branch 111
 (.branch 110
 (.leaf (⟨2, 4, 4395090, 1392690, 361340892720, 361626081120⟩, 159254922))
 (.leaf (⟨2, 4, 4395090, 1392690, 361324115505, 361626081030⟩, 162400698)))
 (.branch 112
 (.leaf (⟨2, 4, 4395090, 1392690, 361055680050, 361626079350⟩, 170265138))
 (.leaf (⟨2, 4, 4395090, 1392690, 357029148225, 361625650950⟩, 178129578)))))
 (.branch 117
 (.branch 115
 (.branch 114
 (.leaf (⟨2, 4, 4395090, 1392690, 356760712770, 361625649270⟩, 181275354))
 (.leaf (⟨2, 4, 4395090, 1392690, 288041236050, 361617784950⟩, 189139794)))
 (.branch 116
 (.leaf (⟨2, 4, 4395090, 1392690, 283746268755, 361617754230⟩, 192285570))
 (.leaf (⟨2, 4, 4395090, 1392690, 215026792020, 361617201270⟩, 200150010))))
 (.branch 119
 (.branch 118
 (.leaf (⟨3, 4, 4396320, 2441520, 361742426640, 434925761040⟩, 2828929473257280353579501865))
 (.leaf (⟨3, 4, 4396320, 2441520, 361473991440, 434925741840⟩, 3032032110052830955787717073)))
 (.branch 120
 (.leaf (⟨3, 4, 4396320, 2441520, 361205556000, 434925740400⟩, 3177105422049652814507870793))
 (.branch 121
 (.leaf (⟨3, 4, 4396320, 2441520, 356642153505, 434925371655⟩, 3380208058845203416716086001))
 (.leaf (⟨3, 4, 4396320, 2441520, 279332742450, 434918461575⟩, 3583310695640754018924301209)))))))
 (.branch 131
 (.branch 126
 (.branch 124
 (.branch 123
 (.leaf (⟨3, 4, 4396320, 2441520, 210613265730, 434917970055⟩, 3728384007637575877644454929))
 (.leaf (⟨2, 4, 3280980, 1070130, 361626105360, 361626105360⟩, 144640154)))
 (.branch 125
 (.leaf (⟨2, 4, 3280980, 1070130, 361609328160, 361626104160⟩, 147785930))
 (.leaf (⟨2, 4, 3280980, 1070130, 361592550945, 361626104070⟩, 150931706))))
 (.branch 128
 (.branch 127
 (.leaf (⟨2, 4, 3280980, 1070130, 361340892720, 361626081120⟩, 158796146))
 (.leaf (⟨2, 4, 3280980, 1070130, 361324115505, 361626081030⟩, 161941922)))
 (.branch 129
 (.leaf (⟨2, 4, 3280980, 1070130, 361055680050, 361626079350⟩, 169806362))
 (.branch 130
 (.leaf (⟨2, 4, 3280980, 1070130, 357029148225, 361625650950⟩, 177670802))
 (.leaf (⟨2, 4, 3280980, 1070130, 356760712770, 361625649270⟩, 180816578))))))
 (.branch 135
 (.branch 133
 (.branch 132
 (.leaf (⟨2, 4, 3280980, 1070130, 288041236050, 361617784950⟩, 188681018))
 (.leaf (⟨2, 4, 3280980, 1070130, 283746268755, 361617754230⟩, 191826794)))
 (.branch 134
 (.leaf (⟨2, 4, 3280980, 1070130, 215026792020, 361617201270⟩, 199691234))
 (.leaf (⟨3, 4, 3212610, 2183235, 361742426640, 434925761040⟩, 2827720750355228183390062890))))
 (.branch 137
 (.branch 136
 (.leaf (⟨3, 4, 3212610, 2183235, 361473991440, 434925741840⟩, 3030823387150778785598278098))
 (.leaf (⟨3, 4, 3212610, 2183235, 361205556000, 434925740400⟩, 3175896699147600644318431818)))
 (.branch 138
 (.leaf (⟨3, 4, 3212610, 2183235, 356642153505, 434925371655⟩, 3378999335943151246526647026))
 (.branch 139
 (.leaf (⟨3, 4, 3212610, 2183235, 279332742450, 434918461575⟩, 3582101972738701848734862234))
 (.leaf (⟨3, 4, 3212610, 2183235, 210613265730, 434917970055⟩, 3727175284735523707455015954))))))))))
noncomputable def raw (i : Fin blockCount) : RawFacePlacement.Block := (records.get i.val).1
noncomputable def witness (i : Fin blockCount) (code : Nat) : Fin 3150 :=
  Fin.ofNat 3150 (Nat.land (Nat.shiftRight (records.get i.val).2 (16 * code)) 65535)
noncomputable def faceTable : Table Nat :=
(.branch 20489
 (.branch 7181
 (.branch 5138
 (.branch 3108
 (.branch 3082
 (.branch 3078
 (.branch 3077
 (.leaf 0)
 (.leaf 1))
 (.branch 3081
 (.leaf 2)
 (.leaf 3)))
 (.branch 3090
 (.branch 3084
 (.leaf 4)
 (.leaf 5))
 (.branch 3092
 (.leaf 6)
 (.leaf 7))))
 (.branch 5125
 (.branch 3120
 (.branch 3112
 (.leaf 8)
 (.leaf 9))
 (.branch 5123
 (.leaf 10)
 (.leaf 11)))
 (.branch 5129
 (.branch 5126
 (.leaf 12)
 (.leaf 13))
 (.branch 5130
 (.leaf 14)
 (.branch 5132
 (.leaf 15)
 (.leaf 16))))))
 (.branch 6154
 (.branch 5168
 (.branch 5156
 (.branch 5140
 (.leaf 17)
 (.leaf 18))
 (.branch 5160
 (.leaf 19)
 (.leaf 20)))
 (.branch 6149
 (.branch 6147
 (.leaf 21)
 (.leaf 22))
 (.branch 6150
 (.leaf 23)
 (.branch 6153
 (.leaf 24)
 (.leaf 25)))))
 (.branch 6180
 (.branch 6162
 (.branch 6156
 (.leaf 26)
 (.leaf 27))
 (.branch 6164
 (.leaf 28)
 (.leaf 29)))
 (.branch 6192
 (.branch 6184
 (.leaf 30)
 (.leaf 31))
 (.branch 7175
 (.leaf 32)
 (.branch 7179
 (.leaf 33)
 (.leaf 34)))))))
 (.branch 12294
 (.branch 10250
 (.branch 10243
 (.branch 7212
 (.branch 7190
 (.leaf 35)
 (.leaf 36))
 (.branch 7220
 (.leaf 37)
 (.leaf 38)))
 (.branch 10246
 (.branch 10245
 (.leaf 39)
 (.leaf 40))
 (.branch 10249
 (.leaf 41)
 (.leaf 42))))
 (.branch 10276
 (.branch 10258
 (.branch 10252
 (.leaf 43)
 (.leaf 44))
 (.branch 10260
 (.leaf 45)
 (.leaf 46)))
 (.branch 10288
 (.branch 10280
 (.leaf 47)
 (.leaf 48))
 (.branch 12291
 (.leaf 49)
 (.branch 12293
 (.leaf 50)
 (.leaf 51))))))
 (.branch 14343
 (.branch 12306
 (.branch 12298
 (.branch 12297
 (.leaf 52)
 (.leaf 53))
 (.branch 12300
 (.leaf 54)
 (.leaf 55)))
 (.branch 12324
 (.branch 12308
 (.leaf 56)
 (.leaf 57))
 (.branch 12328
 (.leaf 58)
 (.branch 12336
 (.leaf 59)
 (.leaf 60)))))
 (.branch 14380
 (.branch 14349
 (.branch 14347
 (.leaf 61)
 (.leaf 62))
 (.branch 14358
 (.leaf 63)
 (.leaf 64)))
 (.branch 20483
 (.branch 14388
 (.leaf 65)
 (.leaf 66))
 (.branch 20485
 (.leaf 67)
 (.branch 20486
 (.leaf 68)
 (.leaf 69))))))))
 (.branch 33840
 (.branch 24616
 (.branch 24579
 (.branch 20500
 (.branch 20492
 (.branch 20490
 (.leaf 70)
 (.leaf 71))
 (.branch 20498
 (.leaf 72)
 (.leaf 73)))
 (.branch 20520
 (.branch 20516
 (.leaf 74)
 (.leaf 75))
 (.branch 20528
 (.leaf 76)
 (.leaf 77))))
 (.branch 24586
 (.branch 24582
 (.branch 24581
 (.leaf 78)
 (.leaf 79))
 (.branch 24585
 (.leaf 80)
 (.leaf 81)))
 (.branch 24594
 (.branch 24588
 (.leaf 82)
 (.leaf 83))
 (.branch 24596
 (.leaf 84)
 (.branch 24612
 (.leaf 85)
 (.leaf 86))))))
 (.branch 33797
 (.branch 28685
 (.branch 28679
 (.branch 24624
 (.leaf 87)
 (.leaf 88))
 (.branch 28683
 (.leaf 89)
 (.leaf 90)))
 (.branch 28716
 (.branch 28694
 (.leaf 91)
 (.leaf 92))
 (.branch 28724
 (.leaf 93)
 (.branch 33795
 (.leaf 94)
 (.leaf 95)))))
 (.branch 33804
 (.branch 33801
 (.branch 33798
 (.leaf 96)
 (.leaf 97))
 (.branch 33802
 (.leaf 98)
 (.leaf 99)))
 (.branch 33812
 (.branch 33810
 (.leaf 100)
 (.leaf 101))
 (.branch 33828
 (.leaf 102)
 (.branch 33832
 (.leaf 103)
 (.leaf 104)))))))
 (.branch 37940
 (.branch 36884
 (.branch 36873
 (.branch 36869
 (.branch 36867
 (.leaf 105)
 (.leaf 106))
 (.branch 36870
 (.leaf 107)
 (.leaf 108)))
 (.branch 36876
 (.branch 36874
 (.leaf 109)
 (.leaf 110))
 (.branch 36882
 (.leaf 111)
 (.leaf 112))))
 (.branch 37895
 (.branch 36904
 (.branch 36900
 (.leaf 113)
 (.leaf 114))
 (.branch 36912
 (.leaf 115)
 (.leaf 116)))
 (.branch 37901
 (.branch 37899
 (.leaf 117)
 (.leaf 118))
 (.branch 37910
 (.leaf 119)
 (.branch 37932
 (.leaf 120)
 (.leaf 121))))))
 (.branch 49188
 (.branch 49161
 (.branch 49157
 (.branch 49155
 (.leaf 122)
 (.leaf 123))
 (.branch 49158
 (.leaf 124)
 (.leaf 125)))
 (.branch 49164
 (.branch 49162
 (.leaf 126)
 (.leaf 127))
 (.branch 49170
 (.leaf 128)
 (.branch 49172
 (.leaf 129)
 (.leaf 130)))))
 (.branch 53259
 (.branch 49200
 (.branch 49192
 (.leaf 131)
 (.leaf 132))
 (.branch 53255
 (.leaf 133)
 (.leaf 134)))
 (.branch 53270
 (.branch 53261
 (.leaf 135)
 (.leaf 136))
 (.branch 53292
 (.leaf 137)
 (.branch 53300
 (.leaf 138)
 (.leaf 139)))))))))
noncomputable def faceWitness (s r : Nat) : Fin blockCount :=
  Fin.ofNat blockCount (faceTable.get (s * 1024 + r))
noncomputable def validity (i : Nat) : Bool :=
  RawFaceNormalizers.blockValidCheck 6 (raw (Fin.ofNat blockCount i))
noncomputable def placement (b : Fin blockCount) (code : Nat) : Bool :=
  RawKindedFacePlacement.check 6 (raw b) template root FacetUniverses.RootedSixExtra01.cells
    code 0 (witness b code)
noncomputable def test (i : Nat) : Bool :=
  let b := Fin.ofNat blockCount i
  FiniteChecks.checkRange (placement b)
    0 (RawFacePlacement.count (raw b).shared (raw b).shared)
noncomputable def symmetry (i : Nat) : Bool :=
  RawOutsidePlacement.blockCheck FacetUniverses.RootedSixExtra01.Outside.vertexCode root.vertices
    (raw (Fin.ofNat blockCount i))
end Papers.RationalityTen.RootedCanonical.RootedSixExtra01.T4

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra01.T4
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
theorem check_0033_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 33)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 33)) 0 6 (by decide +kernel)
theorem block_0033 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 33)) 0 6 :=
  check_0033_0000
theorem check_0034_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 34)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 34)) 0 6 (by decide +kernel)
theorem block_0034 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 34)) 0 6 :=
  check_0034_0000
theorem check_0035_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 35)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 35)) 0 6 (by decide +kernel)
theorem block_0035 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 35)) 0 6 :=
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
theorem check_0061_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 61)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 61)) 0 6 (by decide +kernel)
theorem block_0061 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 61)) 0 6 :=
  check_0061_0000
theorem check_0062_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 62)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 62)) 0 6 (by decide +kernel)
theorem block_0062 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 62)) 0 6 :=
  check_0062_0000
theorem check_0063_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 63)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 63)) 0 6 (by decide +kernel)
theorem block_0063 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 63)) 0 6 :=
  check_0063_0000
end Papers.RationalityTen.RootedCanonical.RootedSixExtra01.T4

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra01.T4
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
end Papers.RationalityTen.RootedCanonical.RootedSixExtra01.T4

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra01.T4
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
end Papers.RationalityTen.RootedCanonical.RootedSixExtra01.T4

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra01.T4
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
theorem metadata_validity_0128 : FiniteChecks.Interval validity 128 140 :=
  FiniteChecks.interval_of_check validity 128 12 (by decide +kernel)
theorem metadata_validity : FiniteChecks.Interval validity 0 blockCount :=
  (FiniteChecks.interval_append (validity) 0 64 140
  (FiniteChecks.interval_append (validity) 0 32 64
  (FiniteChecks.interval_append (validity) 0 16 32
  metadata_validity_0000
  metadata_validity_0016)
  (FiniteChecks.interval_append (validity) 32 48 64
  metadata_validity_0032
  metadata_validity_0048))
  (FiniteChecks.interval_append (validity) 64 96 140
  (FiniteChecks.interval_append (validity) 64 80 96
  metadata_validity_0064
  metadata_validity_0080)
  (FiniteChecks.interval_append (validity) 96 112 140
  metadata_validity_0096
  (FiniteChecks.interval_append (validity) 112 128 140
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
theorem metadata_symmetry_0128 : FiniteChecks.Interval symmetry 128 140 :=
  FiniteChecks.interval_of_check symmetry 128 12 (by decide +kernel)
theorem metadata_symmetry : FiniteChecks.Interval symmetry 0 blockCount :=
  (FiniteChecks.interval_append (symmetry) 0 64 140
  (FiniteChecks.interval_append (symmetry) 0 32 64
  (FiniteChecks.interval_append (symmetry) 0 16 32
  metadata_symmetry_0000
  metadata_symmetry_0016)
  (FiniteChecks.interval_append (symmetry) 32 48 64
  metadata_symmetry_0032
  metadata_symmetry_0048))
  (FiniteChecks.interval_append (symmetry) 64 96 140
  (FiniteChecks.interval_append (symmetry) 64 80 96
  metadata_symmetry_0064
  metadata_symmetry_0080)
  (FiniteChecks.interval_append (symmetry) 96 112 140
  metadata_symmetry_0096
  (FiniteChecks.interval_append (symmetry) 112 128 140
  metadata_symmetry_0112
  metadata_symmetry_0128))))
theorem metadata_normalizers :
    RawFaceNormalizers.completeCheck 6 template root raw faceWitness = true := by decide +kernel
theorem metadata_root : RawFacetEmbedding.wellFormedCheck root = true := by decide +kernel
end Papers.RationalityTen.RootedCanonical.RootedSixExtra01.T4

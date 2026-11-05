module
prelude
public import RootedSixBase00
public import RawKindedFacePlacement
public import RootedSixBase00OutsideData
public import RawOutsidePlacement

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase00.T0
open ConcreteGrowth
abbrev blockCount : Nat := 208
noncomputable def template : Cell := ⟨4, 63, [3, 5, 6, 9, 10, 12, 18, 20, 24, 36, 40, 48], [7, 11, 13, 22, 26, 44, 52, 56]⟩
noncomputable def root : Cell := FacetUniverses.RootedSixBase00.cells 0
noncomputable def records : Table (RawFacePlacement.Block × Nat) :=
(.branch 104
 (.branch 52
 (.branch 26
 (.branch 13
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf (⟨2, 4, 5517840, 5517840, 361626105360, 361626105360⟩, 122947400))
 (.branch 2
 (.leaf (⟨2, 4, 5517840, 5517840, 361609328160, 361626104160⟩, 132384728))
 (.leaf (⟨2, 4, 5517840, 5517840, 361592550945, 361626104070⟩, 141822056))))
 (.branch 4
 (.leaf (⟨2, 4, 5517840, 5517840, 361340892720, 361626081120⟩, 170134040))
 (.branch 5
 (.leaf (⟨2, 4, 5517840, 5517840, 361324115505, 361626081030⟩, 179571368))
 (.leaf (⟨2, 4, 5517840, 5517840, 361055680050, 361626079350⟩, 207883352)))))
 (.branch 9
 (.branch 7
 (.leaf (⟨2, 4, 5517840, 5517840, 357029148225, 361625650950⟩, 236195336))
 (.branch 8
 (.leaf (⟨2, 4, 5517840, 5517840, 356760712770, 361625649270⟩, 245632664))
 (.leaf (⟨2, 4, 5517840, 5517840, 352465745475, 361625618550⟩, 273944648))))
 (.branch 11
 (.branch 10
 (.leaf (⟨2, 4, 5517840, 5517840, 288041236050, 361617784950⟩, 302256632))
 (.leaf (⟨2, 4, 5517840, 5517840, 283746268755, 361617754230⟩, 311693960)))
 (.branch 12
 (.leaf (⟨2, 4, 5517840, 5517840, 215026792020, 361617201270⟩, 340005944))
 (.leaf (⟨2, 4, 5517600, 5517600, 361626105360, 361626105360⟩, 125306720))))))
 (.branch 19
 (.branch 16
 (.branch 14
 (.leaf (⟨2, 4, 5517600, 5517600, 361609328160, 361626104160⟩, 134744048))
 (.branch 15
 (.leaf (⟨2, 4, 5517600, 5517600, 361592550945, 361626104070⟩, 144181376))
 (.leaf (⟨2, 4, 5517600, 5517600, 361340892720, 361626081120⟩, 172493360))))
 (.branch 17
 (.leaf (⟨2, 4, 5517600, 5517600, 361324115505, 361626081030⟩, 181930688))
 (.branch 18
 (.leaf (⟨2, 4, 5517600, 5517600, 361055680050, 361626079350⟩, 210242672))
 (.leaf (⟨2, 4, 5517600, 5517600, 357029148225, 361625650950⟩, 238554656)))))
 (.branch 22
 (.branch 20
 (.leaf (⟨2, 4, 5517600, 5517600, 356760712770, 361625649270⟩, 247991984))
 (.branch 21
 (.leaf (⟨2, 4, 5517600, 5517600, 352465745475, 361625618550⟩, 276303968))
 (.leaf (⟨2, 4, 5517600, 5517600, 288041236050, 361617784950⟩, 304615952))))
 (.branch 24
 (.branch 23
 (.leaf (⟨2, 4, 5517600, 5517600, 283746268755, 361617754230⟩, 314053280))
 (.leaf (⟨2, 4, 5517600, 5517600, 215026792020, 361617201270⟩, 342365264)))
 (.branch 25
 (.leaf (⟨2, 4, 5517345, 5517570, 361626105360, 361626105360⟩, 128452496))
 (.leaf (⟨2, 4, 5517345, 5517570, 361609328160, 361626104160⟩, 137889824)))))))
 (.branch 39
 (.branch 32
 (.branch 29
 (.branch 27
 (.leaf (⟨2, 4, 5517345, 5517570, 361592550945, 361626104070⟩, 147327152))
 (.branch 28
 (.leaf (⟨2, 4, 5517345, 5517570, 361340892720, 361626081120⟩, 175639136))
 (.leaf (⟨2, 4, 5517345, 5517570, 361324115505, 361626081030⟩, 185076464))))
 (.branch 30
 (.leaf (⟨2, 4, 5517345, 5517570, 361055680050, 361626079350⟩, 213388448))
 (.branch 31
 (.leaf (⟨2, 4, 5517345, 5517570, 357029148225, 361625650950⟩, 241700432))
 (.leaf (⟨2, 4, 5517345, 5517570, 356760712770, 361625649270⟩, 251137760)))))
 (.branch 35
 (.branch 33
 (.leaf (⟨2, 4, 5517345, 5517570, 352465745475, 361625618550⟩, 279449744))
 (.branch 34
 (.leaf (⟨2, 4, 5517345, 5517570, 288041236050, 361617784950⟩, 307761728))
 (.leaf (⟨2, 4, 5517345, 5517570, 283746268755, 361617754230⟩, 317199056))))
 (.branch 37
 (.branch 36
 (.leaf (⟨2, 4, 5517345, 5517570, 215026792020, 361617201270⟩, 345511040))
 (.leaf (⟨3, 4, 5517840, 5517840, 361742426640, 434925761040⟩, 2812004142837379385132321016)))
 (.branch 38
 (.leaf (⟨3, 4, 5517840, 5517840, 361473991440, 434925741840⟩, 3508356040422124306989058872))
 (.leaf (⟨3, 4, 5517840, 5517840, 361205556000, 434925740400⟩, 4030619963610682998381612264))))))
 (.branch 45
 (.branch 42
 (.branch 40
 (.leaf (⟨3, 4, 5517840, 5517840, 356642153505, 434925371655⟩, 4726971861195427920238350120))
 (.branch 41
 (.leaf (⟨3, 4, 5517840, 5517840, 352347186225, 434925344775⟩, 5249235784383986611630903512))
 (.leaf (⟨3, 4, 5517840, 5517840, 279332742450, 434918461575⟩, 5945587681968731533487641368))))
 (.branch 43
 (.leaf (⟨3, 4, 5517840, 5517840, 210613265730, 434917970055⟩, 6467851605157290224880194760))
 (.branch 44
 (.leaf (⟨3, 4, 5517840, 5517840, 141893788995, 434917935495⟩, 6816027553949662685808563688))
 (.leaf (⟨2, 4, 5513520, 5509920, 361626105360, 361626105360⟩, 125306720)))))
 (.branch 48
 (.branch 46
 (.leaf (⟨2, 4, 5513520, 5509920, 361609328160, 361626104160⟩, 134744048))
 (.branch 47
 (.leaf (⟨2, 4, 5513520, 5509920, 361592550945, 361626104070⟩, 144181376))
 (.leaf (⟨2, 4, 5513520, 5509920, 361340892720, 361626081120⟩, 172493360))))
 (.branch 50
 (.branch 49
 (.leaf (⟨2, 4, 5513520, 5509920, 361324115505, 361626081030⟩, 181930688))
 (.leaf (⟨2, 4, 5513520, 5509920, 361055680050, 361626079350⟩, 210242672)))
 (.branch 51
 (.leaf (⟨2, 4, 5513520, 5509920, 357029148225, 361625650950⟩, 238554656))
 (.leaf (⟨2, 4, 5513520, 5509920, 356760712770, 361625649270⟩, 247991984))))))))
 (.branch 78
 (.branch 65
 (.branch 58
 (.branch 55
 (.branch 53
 (.leaf (⟨2, 4, 5513520, 5509920, 352465745475, 361625618550⟩, 276303968))
 (.branch 54
 (.leaf (⟨2, 4, 5513520, 5509920, 288041236050, 361617784950⟩, 304615952))
 (.leaf (⟨2, 4, 5513520, 5509920, 283746268755, 361617754230⟩, 314053280))))
 (.branch 56
 (.leaf (⟨2, 4, 5513520, 5509920, 215026792020, 361617201270⟩, 342365264))
 (.branch 57
 (.leaf (⟨2, 4, 5513265, 5509890, 361626105360, 361626105360⟩, 128452496))
 (.leaf (⟨2, 4, 5513265, 5509890, 361609328160, 361626104160⟩, 137889824)))))
 (.branch 61
 (.branch 59
 (.leaf (⟨2, 4, 5513265, 5509890, 361592550945, 361626104070⟩, 147327152))
 (.branch 60
 (.leaf (⟨2, 4, 5513265, 5509890, 361340892720, 361626081120⟩, 175639136))
 (.leaf (⟨2, 4, 5513265, 5509890, 361324115505, 361626081030⟩, 185076464))))
 (.branch 63
 (.branch 62
 (.leaf (⟨2, 4, 5513265, 5509890, 361055680050, 361626079350⟩, 213388448))
 (.leaf (⟨2, 4, 5513265, 5509890, 357029148225, 361625650950⟩, 241700432)))
 (.branch 64
 (.leaf (⟨2, 4, 5513265, 5509890, 356760712770, 361625649270⟩, 251137760))
 (.leaf (⟨2, 4, 5513265, 5509890, 352465745475, 361625618550⟩, 279449744))))))
 (.branch 71
 (.branch 68
 (.branch 66
 (.leaf (⟨2, 4, 5513265, 5509890, 288041236050, 361617784950⟩, 307761728))
 (.branch 67
 (.leaf (⟨2, 4, 5513265, 5509890, 283746268755, 361617754230⟩, 317199056))
 (.leaf (⟨2, 4, 5513265, 5509890, 215026792020, 361617201270⟩, 345511040))))
 (.branch 69
 (.leaf (⟨3, 4, 5514000, 5514000, 361742426640, 434925761040⟩, 2812004142837379385132321016))
 (.branch 70
 (.leaf (⟨3, 4, 5514000, 5514000, 361473991440, 434925741840⟩, 3508356040422124306989058872))
 (.leaf (⟨3, 4, 5514000, 5514000, 361205556000, 434925740400⟩, 4030619963610682998381612264)))))
 (.branch 74
 (.branch 72
 (.leaf (⟨3, 4, 5514000, 5514000, 356642153505, 434925371655⟩, 4726971861195427920238350120))
 (.branch 73
 (.leaf (⟨3, 4, 5514000, 5514000, 352347186225, 434925344775⟩, 5249235784383986611630903512))
 (.leaf (⟨3, 4, 5514000, 5514000, 279332742450, 434918461575⟩, 5945587681968731533487641368))))
 (.branch 76
 (.branch 75
 (.leaf (⟨3, 4, 5514000, 5514000, 210613265730, 434917970055⟩, 6467851605157290224880194760))
 (.leaf (⟨3, 4, 5514000, 5514000, 141893788995, 434917935495⟩, 6816027553949662685808563688)))
 (.branch 77
 (.leaf (⟨2, 4, 5509170, 5509170, 361626105360, 361626105360⟩, 130811852))
 (.leaf (⟨2, 4, 5509170, 5509170, 361609328160, 361626104160⟩, 140249180)))))))
 (.branch 91
 (.branch 84
 (.branch 81
 (.branch 79
 (.leaf (⟨2, 4, 5509170, 5509170, 361592550945, 361626104070⟩, 149686508))
 (.branch 80
 (.leaf (⟨2, 4, 5509170, 5509170, 361340892720, 361626081120⟩, 177998492))
 (.leaf (⟨2, 4, 5509170, 5509170, 361324115505, 361626081030⟩, 187435820))))
 (.branch 82
 (.leaf (⟨2, 4, 5509170, 5509170, 361055680050, 361626079350⟩, 215747804))
 (.branch 83
 (.leaf (⟨2, 4, 5509170, 5509170, 357029148225, 361625650950⟩, 244059788))
 (.leaf (⟨2, 4, 5509170, 5509170, 356760712770, 361625649270⟩, 253497116)))))
 (.branch 87
 (.branch 85
 (.leaf (⟨2, 4, 5509170, 5509170, 352465745475, 361625618550⟩, 281809100))
 (.branch 86
 (.leaf (⟨2, 4, 5509170, 5509170, 288041236050, 361617784950⟩, 310121084))
 (.leaf (⟨2, 4, 5509170, 5509170, 283746268755, 361617754230⟩, 319558412))))
 (.branch 89
 (.branch 88
 (.leaf (⟨2, 4, 5509170, 5509170, 215026792020, 361617201270⟩, 347870396))
 (.leaf (⟨3, 4, 5509920, 5513520, 361742426640, 434925761040⟩, 2833765250320744831688771868)))
 (.branch 90
 (.leaf (⟨3, 4, 5509920, 5513520, 361473991440, 434925741840⟩, 3530117147905489753545509724))
 (.leaf (⟨3, 4, 5509920, 5513520, 361205556000, 434925740400⟩, 4052381071094048444938063116))))))
 (.branch 97
 (.branch 94
 (.branch 92
 (.leaf (⟨3, 4, 5509920, 5513520, 356642153505, 434925371655⟩, 4748732968678793366794800972))
 (.branch 93
 (.leaf (⟨3, 4, 5509920, 5513520, 352347186225, 434925344775⟩, 5270996891867352058187354364))
 (.leaf (⟨3, 4, 5509920, 5513520, 279332742450, 434918461575⟩, 5967348789452096980044092220))))
 (.branch 95
 (.leaf (⟨3, 4, 5509920, 5513520, 210613265730, 434917970055⟩, 6489612712640655671436645612))
 (.branch 96
 (.leaf (⟨3, 4, 5509920, 5513520, 141893788995, 434917935495⟩, 6837788661433028132365014540))
 (.leaf (⟨2, 4, 5447745, 5325570, 361626105360, 361626105360⟩, 130746304)))))
 (.branch 100
 (.branch 98
 (.leaf (⟨2, 4, 5447745, 5325570, 361609328160, 361626104160⟩, 140183632))
 (.branch 99
 (.leaf (⟨2, 4, 5447745, 5325570, 361592550945, 361626104070⟩, 149620960))
 (.leaf (⟨2, 4, 5447745, 5325570, 361340892720, 361626081120⟩, 177932944))))
 (.branch 102
 (.branch 101
 (.leaf (⟨2, 4, 5447745, 5325570, 361324115505, 361626081030⟩, 187370272))
 (.leaf (⟨2, 4, 5447745, 5325570, 361055680050, 361626079350⟩, 215682256)))
 (.branch 103
 (.leaf (⟨2, 4, 5447745, 5325570, 357029148225, 361625650950⟩, 243994240))
 (.leaf (⟨2, 4, 5447745, 5325570, 356760712770, 361625649270⟩, 253431568)))))))))
 (.branch 156
 (.branch 130
 (.branch 117
 (.branch 110
 (.branch 107
 (.branch 105
 (.leaf (⟨2, 4, 5447745, 5325570, 352465745475, 361625618550⟩, 281743552))
 (.branch 106
 (.leaf (⟨2, 4, 5447745, 5325570, 288041236050, 361617784950⟩, 310055536))
 (.leaf (⟨2, 4, 5447745, 5325570, 283746268755, 361617754230⟩, 319492864))))
 (.branch 108
 (.leaf (⟨2, 4, 5447745, 5325570, 215026792020, 361617201270⟩, 347804848))
 (.branch 109
 (.leaf (⟨2, 4, 5443650, 5324850, 361626105360, 361626105360⟩, 128387007))
 (.leaf (⟨2, 4, 5443650, 5324850, 361609328160, 361626104160⟩, 137824335)))))
 (.branch 113
 (.branch 111
 (.leaf (⟨2, 4, 5443650, 5324850, 361592550945, 361626104070⟩, 147261663))
 (.branch 112
 (.leaf (⟨2, 4, 5443650, 5324850, 361340892720, 361626081120⟩, 175573647))
 (.leaf (⟨2, 4, 5443650, 5324850, 361324115505, 361626081030⟩, 185010975))))
 (.branch 115
 (.branch 114
 (.leaf (⟨2, 4, 5443650, 5324850, 361055680050, 361626079350⟩, 213322959))
 (.leaf (⟨2, 4, 5443650, 5324850, 357029148225, 361625650950⟩, 241634943)))
 (.branch 116
 (.leaf (⟨2, 4, 5443650, 5324850, 356760712770, 361625649270⟩, 251072271))
 (.leaf (⟨2, 4, 5443650, 5324850, 352465745475, 361625618550⟩, 279384255))))))
 (.branch 123
 (.branch 120
 (.branch 118
 (.leaf (⟨2, 4, 5443650, 5324850, 288041236050, 361617784950⟩, 307696239))
 (.branch 119
 (.leaf (⟨2, 4, 5443650, 5324850, 283746268755, 361617754230⟩, 317133567))
 (.leaf (⟨2, 4, 5443650, 5324850, 215026792020, 361617201270⟩, 345445551))))
 (.branch 121
 (.leaf (⟨3, 4, 5440545, 5390595, 361742426640, 434925761040⟩, 2847063858618374946157103406))
 (.branch 122
 (.leaf (⟨3, 4, 5440545, 5390595, 361473991440, 434925741840⟩, 3543415756203119868013841262))
 (.leaf (⟨3, 4, 5440545, 5390595, 361205556000, 434925740400⟩, 4065679679391678559406394654)))))
 (.branch 126
 (.branch 124
 (.leaf (⟨3, 4, 5440545, 5390595, 356642153505, 434925371655⟩, 4762031576976423481263132510))
 (.branch 125
 (.leaf (⟨3, 4, 5440545, 5390595, 352347186225, 434925344775⟩, 5284295500164982172655685902))
 (.leaf (⟨3, 4, 5440545, 5390595, 279332742450, 434918461575⟩, 5980647397749727094512423758))))
 (.branch 128
 (.branch 127
 (.leaf (⟨3, 4, 5440545, 5390595, 210613265730, 434917970055⟩, 6502911320938285785904977150))
 (.leaf (⟨3, 4, 5440545, 5390595, 141893788995, 434917935495⟩, 6851087269730658246833346078)))
 (.branch 129
 (.leaf (⟨2, 4, 5378115, 5309490, 361626105360, 361626105360⟩, 128387007))
 (.leaf (⟨2, 4, 5378115, 5309490, 361609328160, 361626104160⟩, 137824335)))))))
 (.branch 143
 (.branch 136
 (.branch 133
 (.branch 131
 (.leaf (⟨2, 4, 5378115, 5309490, 361592550945, 361626104070⟩, 147261663))
 (.branch 132
 (.leaf (⟨2, 4, 5378115, 5309490, 361340892720, 361626081120⟩, 175573647))
 (.leaf (⟨2, 4, 5378115, 5309490, 361324115505, 361626081030⟩, 185010975))))
 (.branch 134
 (.leaf (⟨2, 4, 5378115, 5309490, 361055680050, 361626079350⟩, 213322959))
 (.branch 135
 (.leaf (⟨2, 4, 5378115, 5309490, 357029148225, 361625650950⟩, 241634943))
 (.leaf (⟨2, 4, 5378115, 5309490, 356760712770, 361625649270⟩, 251072271)))))
 (.branch 139
 (.branch 137
 (.leaf (⟨2, 4, 5378115, 5309490, 352465745475, 361625618550⟩, 279384255))
 (.branch 138
 (.leaf (⟨2, 4, 5378115, 5309490, 288041236050, 361617784950⟩, 307696239))
 (.leaf (⟨2, 4, 5378115, 5309490, 283746268755, 361617754230⟩, 317133567))))
 (.branch 141
 (.branch 140
 (.leaf (⟨2, 4, 5378115, 5309490, 215026792020, 361617201270⟩, 345445551))
 (.leaf (⟨3, 4, 5375025, 5379075, 361742426640, 434925761040⟩, 2847063858618374946157103406)))
 (.branch 142
 (.leaf (⟨3, 4, 5375025, 5379075, 361473991440, 434925741840⟩, 3543415756203119868013841262))
 (.leaf (⟨3, 4, 5375025, 5379075, 361205556000, 434925740400⟩, 4065679679391678559406394654))))))
 (.branch 149
 (.branch 146
 (.branch 144
 (.leaf (⟨3, 4, 5375025, 5379075, 356642153505, 434925371655⟩, 4762031576976423481263132510))
 (.branch 145
 (.leaf (⟨3, 4, 5375025, 5379075, 352347186225, 434925344775⟩, 5284295500164982172655685902))
 (.leaf (⟨3, 4, 5375025, 5379075, 279332742450, 434918461575⟩, 5980647397749727094512423758))))
 (.branch 147
 (.leaf (⟨3, 4, 5375025, 5379075, 210613265730, 434917970055⟩, 6502911320938285785904977150))
 (.branch 148
 (.leaf (⟨3, 4, 5375025, 5379075, 141893788995, 434917935495⟩, 6851087269730658246833346078))
 (.leaf (⟨2, 4, 4395090, 1392690, 361626105360, 361626105360⟩, 125241231)))))
 (.branch 152
 (.branch 150
 (.leaf (⟨2, 4, 4395090, 1392690, 361609328160, 361626104160⟩, 134678559))
 (.branch 151
 (.leaf (⟨2, 4, 4395090, 1392690, 361592550945, 361626104070⟩, 144115887))
 (.leaf (⟨2, 4, 4395090, 1392690, 361340892720, 361626081120⟩, 172427871))))
 (.branch 154
 (.branch 153
 (.leaf (⟨2, 4, 4395090, 1392690, 361324115505, 361626081030⟩, 181865199))
 (.leaf (⟨2, 4, 4395090, 1392690, 361055680050, 361626079350⟩, 210177183)))
 (.branch 155
 (.leaf (⟨2, 4, 4395090, 1392690, 357029148225, 361625650950⟩, 238489167))
 (.leaf (⟨2, 4, 4395090, 1392690, 356760712770, 361625649270⟩, 247926495))))))))
 (.branch 182
 (.branch 169
 (.branch 162
 (.branch 159
 (.branch 157
 (.leaf (⟨2, 4, 4395090, 1392690, 352465745475, 361625618550⟩, 276238479))
 (.branch 158
 (.leaf (⟨2, 4, 4395090, 1392690, 288041236050, 361617784950⟩, 304550463))
 (.leaf (⟨2, 4, 4395090, 1392690, 283746268755, 361617754230⟩, 313987791))))
 (.branch 160
 (.leaf (⟨2, 4, 4395090, 1392690, 215026792020, 361617201270⟩, 342299775))
 (.branch 161
 (.leaf (⟨2, 4, 4329555, 1377330, 361626105360, 361626105360⟩, 125241231))
 (.leaf (⟨2, 4, 4329555, 1377330, 361609328160, 361626104160⟩, 134678559)))))
 (.branch 165
 (.branch 163
 (.leaf (⟨2, 4, 4329555, 1377330, 361592550945, 361626104070⟩, 144115887))
 (.branch 164
 (.leaf (⟨2, 4, 4329555, 1377330, 361340892720, 361626081120⟩, 172427871))
 (.leaf (⟨2, 4, 4329555, 1377330, 361324115505, 361626081030⟩, 181865199))))
 (.branch 167
 (.branch 166
 (.leaf (⟨2, 4, 4329555, 1377330, 361055680050, 361626079350⟩, 210177183))
 (.leaf (⟨2, 4, 4329555, 1377330, 357029148225, 361625650950⟩, 238489167)))
 (.branch 168
 (.leaf (⟨2, 4, 4329555, 1377330, 356760712770, 361625649270⟩, 247926495))
 (.leaf (⟨2, 4, 4329555, 1377330, 352465745475, 361625618550⟩, 276238479))))))
 (.branch 175
 (.branch 172
 (.branch 170
 (.leaf (⟨2, 4, 4329555, 1377330, 288041236050, 361617784950⟩, 304550463))
 (.branch 171
 (.leaf (⟨2, 4, 4329555, 1377330, 283746268755, 361617754230⟩, 313987791))
 (.leaf (⟨2, 4, 4329555, 1377330, 215026792020, 361617201270⟩, 342299775))))
 (.branch 173
 (.leaf (⟨3, 4, 4261170, 2428995, 361742426640, 434925761040⟩, 2825302751139794574205847853))
 (.branch 174
 (.leaf (⟨3, 4, 4261170, 2428995, 361473991440, 434925741840⟩, 3521654648724539496062585709))
 (.leaf (⟨3, 4, 4261170, 2428995, 361205556000, 434925740400⟩, 4043918571913098187455139101)))))
 (.branch 178
 (.branch 176
 (.leaf (⟨3, 4, 4261170, 2428995, 356642153505, 434925371655⟩, 4740270469497843109311876957))
 (.branch 177
 (.leaf (⟨3, 4, 4261170, 2428995, 352347186225, 434925344775⟩, 5262534392686401800704430349))
 (.leaf (⟨3, 4, 4261170, 2428995, 279332742450, 434918461575⟩, 5958886290271146722561168205))))
 (.branch 180
 (.branch 179
 (.leaf (⟨3, 4, 4261170, 2428995, 210613265730, 434917970055⟩, 6481150213459705413953721597))
 (.leaf (⟨3, 4, 4261170, 2428995, 141893788995, 434917935495⟩, 6829326162252077874882090525)))
 (.branch 181
 (.leaf (⟨2, 4, 3280980, 1070130, 361626105360, 361626105360⟩, 122881887))
 (.leaf (⟨2, 4, 3280980, 1070130, 361609328160, 361626104160⟩, 132319215)))))))
 (.branch 195
 (.branch 188
 (.branch 185
 (.branch 183
 (.leaf (⟨2, 4, 3280980, 1070130, 361592550945, 361626104070⟩, 141756543))
 (.branch 184
 (.leaf (⟨2, 4, 3280980, 1070130, 361340892720, 361626081120⟩, 170068527))
 (.leaf (⟨2, 4, 3280980, 1070130, 361324115505, 361626081030⟩, 179505855))))
 (.branch 186
 (.leaf (⟨2, 4, 3280980, 1070130, 361055680050, 361626079350⟩, 207817839))
 (.branch 187
 (.leaf (⟨2, 4, 3280980, 1070130, 357029148225, 361625650950⟩, 236129823))
 (.leaf (⟨2, 4, 3280980, 1070130, 356760712770, 361625649270⟩, 245567151)))))
 (.branch 191
 (.branch 189
 (.leaf (⟨2, 4, 3280980, 1070130, 352465745475, 361625618550⟩, 273879135))
 (.branch 190
 (.leaf (⟨2, 4, 3280980, 1070130, 288041236050, 361617784950⟩, 302191119))
 (.leaf (⟨2, 4, 3280980, 1070130, 283746268755, 361617754230⟩, 311628447))))
 (.branch 193
 (.branch 192
 (.leaf (⟨2, 4, 3280980, 1070130, 215026792020, 361617201270⟩, 339940431))
 (.leaf (⟨3, 4, 3212610, 2183235, 361742426640, 434925761040⟩, 2781780868224590184338229531)))
 (.branch 194
 (.leaf (⟨3, 4, 3212610, 2183235, 361473991440, 434925741840⟩, 3478132765809335106194967387))
 (.leaf (⟨3, 4, 3212610, 2183235, 361205556000, 434925740400⟩, 4000396688997893797587520779))))))
 (.branch 201
 (.branch 198
 (.branch 196
 (.leaf (⟨3, 4, 3212610, 2183235, 356642153505, 434925371655⟩, 4696748586582638719444258635))
 (.branch 197
 (.leaf (⟨3, 4, 3212610, 2183235, 352347186225, 434925344775⟩, 5219012509771197410836812027))
 (.leaf (⟨3, 4, 3212610, 2183235, 279332742450, 434918461575⟩, 5915364407355942332693549883))))
 (.branch 199
 (.leaf (⟨3, 4, 3212610, 2183235, 210613265730, 434917970055⟩, 6437628330544501024086103275))
 (.branch 200
 (.leaf (⟨3, 4, 3212610, 2183235, 141893788995, 434917935495⟩, 6785804279336873485014472203))
 (.leaf (⟨3, 4, 2164035, 2164035, 361742426640, 434925761040⟩, 2781780868224590184338229531)))))
 (.branch 204
 (.branch 202
 (.leaf (⟨3, 4, 2164035, 2164035, 361473991440, 434925741840⟩, 3478132765809335106194967387))
 (.branch 203
 (.leaf (⟨3, 4, 2164035, 2164035, 361205556000, 434925740400⟩, 4000396688997893797587520779))
 (.leaf (⟨3, 4, 2164035, 2164035, 356642153505, 434925371655⟩, 4696748586582638719444258635))))
 (.branch 206
 (.branch 205
 (.leaf (⟨3, 4, 2164035, 2164035, 352347186225, 434925344775⟩, 5219012509771197410836812027))
 (.leaf (⟨3, 4, 2164035, 2164035, 279332742450, 434918461575⟩, 5915364407355942332693549883)))
 (.branch 207
 (.leaf (⟨3, 4, 2164035, 2164035, 210613265730, 434917970055⟩, 6437628330544501024086103275))
 (.leaf (⟨3, 4, 2164035, 2164035, 141893788995, 434917935495⟩, 6785804279336873485014472203))))))))))
noncomputable def raw (i : Fin blockCount) : RawFacePlacement.Block := (records.get i.val).1
noncomputable def witness (i : Fin blockCount) (code : Nat) : Fin 21976 :=
  Fin.ofNat 21976 (Nat.land (Nat.shiftRight (records.get i.val).2 (16 * code)) 65535)
noncomputable def faceTable : Table Nat :=
(.branch 18456
 (.branch 9240
 (.branch 6150
 (.branch 5125
 (.branch 3090
 (.branch 3081
 (.branch 3077
 (.leaf 0)
 (.branch 3078
 (.leaf 1)
 (.leaf 2)))
 (.branch 3082
 (.leaf 3)
 (.branch 3084
 (.leaf 4)
 (.leaf 5))))
 (.branch 3108
 (.branch 3092
 (.leaf 6)
 (.branch 3096
 (.leaf 7)
 (.leaf 8)))
 (.branch 3120
 (.branch 3112
 (.leaf 9)
 (.leaf 10))
 (.branch 5123
 (.leaf 11)
 (.leaf 12)))))
 (.branch 5140
 (.branch 5130
 (.branch 5126
 (.leaf 13)
 (.branch 5129
 (.leaf 14)
 (.leaf 15)))
 (.branch 5132
 (.leaf 16)
 (.branch 5138
 (.leaf 17)
 (.leaf 18))))
 (.branch 5160
 (.branch 5144
 (.leaf 19)
 (.branch 5156
 (.leaf 20)
 (.leaf 21)))
 (.branch 6147
 (.branch 5168
 (.leaf 22)
 (.leaf 23))
 (.branch 6149
 (.leaf 24)
 (.leaf 25))))))
 (.branch 7190
 (.branch 6168
 (.branch 6156
 (.branch 6153
 (.leaf 26)
 (.branch 6154
 (.leaf 27)
 (.leaf 28)))
 (.branch 6162
 (.leaf 29)
 (.branch 6164
 (.leaf 30)
 (.leaf 31))))
 (.branch 6192
 (.branch 6180
 (.leaf 32)
 (.branch 6184
 (.leaf 33)
 (.leaf 34)))
 (.branch 7179
 (.branch 7175
 (.leaf 35)
 (.leaf 36))
 (.branch 7181
 (.leaf 37)
 (.leaf 38)))))
 (.branch 9221
 (.branch 7220
 (.branch 7194
 (.leaf 39)
 (.branch 7212
 (.leaf 40)
 (.leaf 41)))
 (.branch 7224
 (.leaf 42)
 (.branch 9219
 (.leaf 43)
 (.leaf 44))))
 (.branch 9226
 (.branch 9222
 (.leaf 45)
 (.branch 9225
 (.leaf 46)
 (.leaf 47)))
 (.branch 9234
 (.branch 9228
 (.leaf 48)
 (.leaf 49))
 (.branch 9236
 (.leaf 50)
 (.leaf 51)))))))
 (.branch 12294
 (.branch 10276
 (.branch 10246
 (.branch 9264
 (.branch 9252
 (.leaf 52)
 (.branch 9256
 (.leaf 53)
 (.leaf 54)))
 (.branch 10243
 (.leaf 55)
 (.branch 10245
 (.leaf 56)
 (.leaf 57))))
 (.branch 10252
 (.branch 10249
 (.leaf 58)
 (.branch 10250
 (.leaf 59)
 (.leaf 60)))
 (.branch 10260
 (.branch 10258
 (.leaf 61)
 (.leaf 62))
 (.branch 10264
 (.leaf 63)
 (.leaf 64)))))
 (.branch 11286
 (.branch 11271
 (.branch 10280
 (.leaf 65)
 (.branch 10288
 (.leaf 66)
 (.leaf 67)))
 (.branch 11275
 (.leaf 68)
 (.branch 11277
 (.leaf 69)
 (.leaf 70))))
 (.branch 11316
 (.branch 11290
 (.leaf 71)
 (.branch 11308
 (.leaf 72)
 (.leaf 73)))
 (.branch 12291
 (.branch 11320
 (.leaf 74)
 (.leaf 75))
 (.branch 12293
 (.leaf 76)
 (.leaf 77))))))
 (.branch 13334
 (.branch 12312
 (.branch 12300
 (.branch 12297
 (.leaf 78)
 (.branch 12298
 (.leaf 79)
 (.leaf 80)))
 (.branch 12306
 (.leaf 81)
 (.branch 12308
 (.leaf 82)
 (.leaf 83))))
 (.branch 12336
 (.branch 12324
 (.leaf 84)
 (.branch 12328
 (.leaf 85)
 (.leaf 86)))
 (.branch 13323
 (.branch 13319
 (.leaf 87)
 (.leaf 88))
 (.branch 13325
 (.leaf 89)
 (.leaf 90)))))
 (.branch 18437
 (.branch 13364
 (.branch 13338
 (.leaf 91)
 (.branch 13356
 (.leaf 92)
 (.leaf 93)))
 (.branch 13368
 (.leaf 94)
 (.branch 18435
 (.leaf 95)
 (.leaf 96))))
 (.branch 18442
 (.branch 18438
 (.leaf 97)
 (.branch 18441
 (.leaf 98)
 (.leaf 99)))
 (.branch 18450
 (.branch 18444
 (.leaf 100)
 (.leaf 101))
 (.branch 18452
 (.leaf 102)
 (.leaf 103))))))))
 (.branch 36888
 (.branch 24582
 (.branch 20516
 (.branch 20486
 (.branch 18480
 (.branch 18468
 (.leaf 104)
 (.branch 18472
 (.leaf 105)
 (.leaf 106)))
 (.branch 20483
 (.leaf 107)
 (.branch 20485
 (.leaf 108)
 (.leaf 109))))
 (.branch 20492
 (.branch 20489
 (.leaf 110)
 (.branch 20490
 (.leaf 111)
 (.leaf 112)))
 (.branch 20500
 (.branch 20498
 (.leaf 113)
 (.leaf 114))
 (.branch 20504
 (.leaf 115)
 (.leaf 116)))))
 (.branch 22550
 (.branch 22535
 (.branch 20520
 (.leaf 117)
 (.branch 20528
 (.leaf 118)
 (.leaf 119)))
 (.branch 22539
 (.leaf 120)
 (.branch 22541
 (.leaf 121)
 (.leaf 122))))
 (.branch 22580
 (.branch 22554
 (.leaf 123)
 (.branch 22572
 (.leaf 124)
 (.leaf 125)))
 (.branch 24579
 (.branch 22584
 (.leaf 126)
 (.leaf 127))
 (.branch 24581
 (.leaf 128)
 (.leaf 129))))))
 (.branch 26646
 (.branch 24600
 (.branch 24588
 (.branch 24585
 (.leaf 130)
 (.branch 24586
 (.leaf 131)
 (.leaf 132)))
 (.branch 24594
 (.leaf 133)
 (.branch 24596
 (.leaf 134)
 (.leaf 135))))
 (.branch 24624
 (.branch 24612
 (.leaf 136)
 (.branch 24616
 (.leaf 137)
 (.leaf 138)))
 (.branch 26635
 (.branch 26631
 (.leaf 139)
 (.leaf 140))
 (.branch 26637
 (.leaf 141)
 (.leaf 142)))))
 (.branch 36869
 (.branch 26676
 (.branch 26650
 (.leaf 143)
 (.branch 26668
 (.leaf 144)
 (.leaf 145)))
 (.branch 26680
 (.leaf 146)
 (.branch 36867
 (.leaf 147)
 (.leaf 148))))
 (.branch 36874
 (.branch 36870
 (.leaf 149)
 (.branch 36873
 (.leaf 150)
 (.leaf 151)))
 (.branch 36882
 (.branch 36876
 (.leaf 152)
 (.leaf 153))
 (.branch 36884
 (.leaf 154)
 (.leaf 155)))))))
 (.branch 49158
 (.branch 40996
 (.branch 40966
 (.branch 36912
 (.branch 36900
 (.leaf 156)
 (.branch 36904
 (.leaf 157)
 (.leaf 158)))
 (.branch 40963
 (.leaf 159)
 (.branch 40965
 (.leaf 160)
 (.leaf 161))))
 (.branch 40972
 (.branch 40969
 (.leaf 162)
 (.branch 40970
 (.leaf 163)
 (.leaf 164)))
 (.branch 40980
 (.branch 40978
 (.leaf 165)
 (.leaf 166))
 (.branch 40984
 (.leaf 167)
 (.leaf 168)))))
 (.branch 45078
 (.branch 45063
 (.branch 41000
 (.leaf 169)
 (.branch 41008
 (.leaf 170)
 (.leaf 171)))
 (.branch 45067
 (.leaf 172)
 (.branch 45069
 (.leaf 173)
 (.leaf 174))))
 (.branch 45108
 (.branch 45082
 (.leaf 175)
 (.branch 45100
 (.leaf 176)
 (.leaf 177)))
 (.branch 49155
 (.branch 45112
 (.leaf 178)
 (.leaf 179))
 (.branch 49157
 (.leaf 180)
 (.leaf 181))))))
 (.branch 53270
 (.branch 49176
 (.branch 49164
 (.branch 49161
 (.leaf 182)
 (.branch 49162
 (.leaf 183)
 (.leaf 184)))
 (.branch 49170
 (.leaf 185)
 (.branch 49172
 (.leaf 186)
 (.leaf 187))))
 (.branch 49200
 (.branch 49188
 (.leaf 188)
 (.branch 49192
 (.leaf 189)
 (.leaf 190)))
 (.branch 53259
 (.branch 53255
 (.leaf 191)
 (.leaf 192))
 (.branch 53261
 (.leaf 193)
 (.leaf 194)))))
 (.branch 57355
 (.branch 53300
 (.branch 53274
 (.leaf 195)
 (.branch 53292
 (.leaf 196)
 (.leaf 197)))
 (.branch 53304
 (.leaf 198)
 (.branch 57351
 (.leaf 199)
 (.leaf 200))))
 (.branch 57370
 (.branch 57357
 (.leaf 201)
 (.branch 57366
 (.leaf 202)
 (.leaf 203)))
 (.branch 57396
 (.branch 57388
 (.leaf 204)
 (.leaf 205))
 (.branch 57400
 (.leaf 206)
 (.leaf 207)))))))))
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
end Papers.RationalityTen.RootedCanonical.RootedSixBase00.T0

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase00.T0
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
end Papers.RationalityTen.RootedCanonical.RootedSixBase00.T0

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase00.T0
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
end Papers.RationalityTen.RootedCanonical.RootedSixBase00.T0

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase00.T0
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
end Papers.RationalityTen.RootedCanonical.RootedSixBase00.T0

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase00.T0
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
end Papers.RationalityTen.RootedCanonical.RootedSixBase00.T0

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase00.T0
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
end Papers.RationalityTen.RootedCanonical.RootedSixBase00.T0

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase00.T0
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
end Papers.RationalityTen.RootedCanonical.RootedSixBase00.T0

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase00.T0
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
end Papers.RationalityTen.RootedCanonical.RootedSixBase00.T0

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase00.T0
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
theorem check_0123_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 123)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 123)) 0 6 (by decide +kernel)
theorem block_0123 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 123)) 0 6 :=
  check_0123_0000
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
end Papers.RationalityTen.RootedCanonical.RootedSixBase00.T0

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase00.T0
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
theorem check_0140_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 140)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 140)) 0 6 (by decide +kernel)
theorem block_0140 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 140)) 0 6 :=
  check_0140_0000
theorem check_0141_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 141)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 141)) 0 6 (by decide +kernel)
theorem block_0141 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 141)) 0 6 :=
  check_0141_0000
theorem check_0142_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 142)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 142)) 0 6 (by decide +kernel)
theorem block_0142 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 142)) 0 6 :=
  check_0142_0000
theorem check_0143_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 143)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 143)) 0 6 (by decide +kernel)
theorem block_0143 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 143)) 0 6 :=
  check_0143_0000
end Papers.RationalityTen.RootedCanonical.RootedSixBase00.T0

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase00.T0
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
end Papers.RationalityTen.RootedCanonical.RootedSixBase00.T0

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase00.T0
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
theorem check_0164_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 164)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 164)) 0 2 (by decide +kernel)
theorem block_0164 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 164)) 0 2 :=
  check_0164_0000
theorem check_0165_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 165)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 165)) 0 2 (by decide +kernel)
theorem block_0165 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 165)) 0 2 :=
  check_0165_0000
theorem check_0166_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 166)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 166)) 0 2 (by decide +kernel)
theorem block_0166 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 166)) 0 2 :=
  check_0166_0000
theorem check_0167_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 167)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 167)) 0 2 (by decide +kernel)
theorem block_0167 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 167)) 0 2 :=
  check_0167_0000
theorem check_0168_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 168)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 168)) 0 2 (by decide +kernel)
theorem block_0168 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 168)) 0 2 :=
  check_0168_0000
theorem check_0169_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 169)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 169)) 0 2 (by decide +kernel)
theorem block_0169 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 169)) 0 2 :=
  check_0169_0000
theorem check_0170_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 170)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 170)) 0 2 (by decide +kernel)
theorem block_0170 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 170)) 0 2 :=
  check_0170_0000
theorem check_0171_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 171)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 171)) 0 2 (by decide +kernel)
theorem block_0171 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 171)) 0 2 :=
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
end Papers.RationalityTen.RootedCanonical.RootedSixBase00.T0

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase00.T0
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
theorem check_0180_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 180)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 180)) 0 2 (by decide +kernel)
theorem block_0180 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 180)) 0 2 :=
  check_0180_0000
theorem check_0181_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 181)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 181)) 0 2 (by decide +kernel)
theorem block_0181 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 181)) 0 2 :=
  check_0181_0000
theorem check_0182_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 182)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 182)) 0 2 (by decide +kernel)
theorem block_0182 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 182)) 0 2 :=
  check_0182_0000
theorem check_0183_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 183)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 183)) 0 2 (by decide +kernel)
theorem block_0183 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 183)) 0 2 :=
  check_0183_0000
theorem check_0184_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 184)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 184)) 0 2 (by decide +kernel)
theorem block_0184 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 184)) 0 2 :=
  check_0184_0000
theorem check_0185_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 185)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 185)) 0 2 (by decide +kernel)
theorem block_0185 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 185)) 0 2 :=
  check_0185_0000
theorem check_0186_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 186)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 186)) 0 2 (by decide +kernel)
theorem block_0186 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 186)) 0 2 :=
  check_0186_0000
theorem check_0187_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 187)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 187)) 0 2 (by decide +kernel)
theorem block_0187 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 187)) 0 2 :=
  check_0187_0000
theorem check_0188_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 188)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 188)) 0 2 (by decide +kernel)
theorem block_0188 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 188)) 0 2 :=
  check_0188_0000
theorem check_0189_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 189)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 189)) 0 2 (by decide +kernel)
theorem block_0189 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 189)) 0 2 :=
  check_0189_0000
theorem check_0190_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 190)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 190)) 0 2 (by decide +kernel)
theorem block_0190 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 190)) 0 2 :=
  check_0190_0000
theorem check_0191_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 191)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 191)) 0 2 (by decide +kernel)
theorem block_0191 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 191)) 0 2 :=
  check_0191_0000
end Papers.RationalityTen.RootedCanonical.RootedSixBase00.T0

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase00.T0
theorem check_0192_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 192)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 192)) 0 6 (by decide +kernel)
theorem block_0192 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 192)) 0 6 :=
  check_0192_0000
theorem check_0193_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 193)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 193)) 0 6 (by decide +kernel)
theorem block_0193 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 193)) 0 6 :=
  check_0193_0000
theorem check_0194_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 194)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 194)) 0 6 (by decide +kernel)
theorem block_0194 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 194)) 0 6 :=
  check_0194_0000
theorem check_0195_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 195)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 195)) 0 6 (by decide +kernel)
theorem block_0195 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 195)) 0 6 :=
  check_0195_0000
theorem check_0196_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 196)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 196)) 0 6 (by decide +kernel)
theorem block_0196 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 196)) 0 6 :=
  check_0196_0000
theorem check_0197_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 197)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 197)) 0 6 (by decide +kernel)
theorem block_0197 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 197)) 0 6 :=
  check_0197_0000
theorem check_0198_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 198)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 198)) 0 6 (by decide +kernel)
theorem block_0198 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 198)) 0 6 :=
  check_0198_0000
theorem check_0199_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 199)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 199)) 0 6 (by decide +kernel)
theorem block_0199 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 199)) 0 6 :=
  check_0199_0000
theorem check_0200_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 200)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 200)) 0 6 (by decide +kernel)
theorem block_0200 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 200)) 0 6 :=
  check_0200_0000
theorem check_0201_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 201)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 201)) 0 6 (by decide +kernel)
theorem block_0201 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 201)) 0 6 :=
  check_0201_0000
theorem check_0202_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 202)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 202)) 0 6 (by decide +kernel)
theorem block_0202 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 202)) 0 6 :=
  check_0202_0000
theorem check_0203_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 203)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 203)) 0 6 (by decide +kernel)
theorem block_0203 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 203)) 0 6 :=
  check_0203_0000
theorem check_0204_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 204)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 204)) 0 6 (by decide +kernel)
theorem block_0204 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 204)) 0 6 :=
  check_0204_0000
theorem check_0205_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 205)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 205)) 0 6 (by decide +kernel)
theorem block_0205 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 205)) 0 6 :=
  check_0205_0000
theorem check_0206_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 206)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 206)) 0 6 (by decide +kernel)
theorem block_0206 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 206)) 0 6 :=
  check_0206_0000
theorem check_0207_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 207)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 207)) 0 6 (by decide +kernel)
theorem block_0207 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 207)) 0 6 :=
  check_0207_0000
end Papers.RationalityTen.RootedCanonical.RootedSixBase00.T0

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase00.T0
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
theorem metadata_validity_0176 : FiniteChecks.Interval validity 176 192 :=
  FiniteChecks.interval_of_check validity 176 16 (by decide +kernel)
theorem metadata_validity_0192 : FiniteChecks.Interval validity 192 208 :=
  FiniteChecks.interval_of_check validity 192 16 (by decide +kernel)
theorem metadata_validity : FiniteChecks.Interval validity 0 blockCount :=
  (FiniteChecks.interval_append (validity) 0 96 208
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
  (FiniteChecks.interval_append (validity) 96 144 208
  (FiniteChecks.interval_append (validity) 96 112 144
  metadata_validity_0096
  (FiniteChecks.interval_append (validity) 112 128 144
  metadata_validity_0112
  metadata_validity_0128))
  (FiniteChecks.interval_append (validity) 144 176 208
  (FiniteChecks.interval_append (validity) 144 160 176
  metadata_validity_0144
  metadata_validity_0160)
  (FiniteChecks.interval_append (validity) 176 192 208
  metadata_validity_0176
  metadata_validity_0192))))
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
theorem metadata_symmetry_0176 : FiniteChecks.Interval symmetry 176 192 :=
  FiniteChecks.interval_of_check symmetry 176 16 (by decide +kernel)
theorem metadata_symmetry_0192 : FiniteChecks.Interval symmetry 192 208 :=
  FiniteChecks.interval_of_check symmetry 192 16 (by decide +kernel)
theorem metadata_symmetry : FiniteChecks.Interval symmetry 0 blockCount :=
  (FiniteChecks.interval_append (symmetry) 0 96 208
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
  (FiniteChecks.interval_append (symmetry) 96 144 208
  (FiniteChecks.interval_append (symmetry) 96 112 144
  metadata_symmetry_0096
  (FiniteChecks.interval_append (symmetry) 112 128 144
  metadata_symmetry_0112
  metadata_symmetry_0128))
  (FiniteChecks.interval_append (symmetry) 144 176 208
  (FiniteChecks.interval_append (symmetry) 144 160 176
  metadata_symmetry_0144
  metadata_symmetry_0160)
  (FiniteChecks.interval_append (symmetry) 176 192 208
  metadata_symmetry_0176
  metadata_symmetry_0192))))
theorem metadata_normalizers :
    RawFaceNormalizers.completeCheck 6 template root raw faceWitness = true := by decide +kernel
theorem metadata_root : RawFacetEmbedding.wellFormedCheck root = true := by decide +kernel
end Papers.RationalityTen.RootedCanonical.RootedSixBase00.T0

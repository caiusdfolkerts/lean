module
prelude
public import RootedSixExtra01
public import RawKindedFacePlacement
public import RootedSixExtra01OutsideData
public import RawOutsidePlacement

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra01.S5T0
open ConcreteGrowth
abbrev blockCount : Nat := 165
noncomputable def template : Cell := ⟨2, 31, [3, 5, 6, 9, 10, 12, 17, 18, 24], [7, 13, 14, 19, 25, 26]⟩
noncomputable def root : Cell := FacetUniverses.RootedSixExtra01.cells 0
noncomputable def records : Table (RawFacePlacement.Block × Nat) :=
(.branch 82
 (.branch 41
 (.branch 20
 (.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf (⟨1, 4, 274960, 274960, 361617786720, 288326448720⟩, 592))
 (.leaf (⟨1, 4, 274960, 274960, 361616738145, 288326448645⟩, 945)))
 (.branch 3
 (.leaf (⟨1, 4, 274960, 274960, 361599960930, 288326447205⟩, 1366))
 (.branch 4
 (.leaf (⟨1, 4, 274960, 274960, 361331525475, 288326420325⟩, 1475))
 (.leaf (⟨1, 4, 274960, 274960, 357036558180, 288325928805⟩, 1584)))))
 (.branch 7
 (.branch 6
 (.leaf (⟨1, 4, 274960, 274960, 288317081445, 288317081445⟩, 1609))
 (.leaf (⟨1, 4, 274945, 274945, 361617786720, 288326448720⟩, 592)))
 (.branch 8
 (.leaf (⟨1, 4, 274945, 274945, 361616738145, 288326448645⟩, 945))
 (.branch 9
 (.leaf (⟨1, 4, 274945, 274945, 361599960930, 288326447205⟩, 1366))
 (.leaf (⟨1, 4, 274945, 274945, 361331525475, 288326420325⟩, 1475))))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf (⟨1, 4, 274945, 274945, 357036558180, 288325928805⟩, 1584))
 (.leaf (⟨1, 4, 274945, 274945, 288317081445, 288317081445⟩, 1609)))
 (.branch 13
 (.leaf (⟨2, 4, 274960, 274960, 361626105360, 361626105360⟩, 17498379))
 (.branch 14
 (.leaf (⟨2, 4, 274960, 274960, 361609328160, 361626104160⟩, 27722151))
 (.leaf (⟨2, 4, 274960, 274960, 361592550945, 361626104070⟩, 45089456)))))
 (.branch 17
 (.branch 16
 (.leaf (⟨2, 4, 274960, 274960, 361340892720, 361626081120⟩, 33227259))
 (.leaf (⟨2, 4, 274960, 274960, 361324115505, 361626081030⟩, 50856712)))
 (.branch 18
 (.leaf (⟨2, 4, 274960, 274960, 361055680050, 361626079350⟩, 68224017))
 (.branch 19
 (.leaf (⟨2, 4, 274960, 274960, 357029148225, 361625650950⟩, 56361820))
 (.leaf (⟨2, 4, 274960, 274960, 356760712770, 361625649270⟩, 78447789)))))))
 (.branch 30
 (.branch 25
 (.branch 22
 (.branch 21
 (.leaf (⟨2, 4, 274960, 274960, 288041236050, 361617784950⟩, 83952897))
 (.leaf (⟨2, 4, 274960, 274960, 283746268755, 361617754230⟩, 91096430)))
 (.branch 23
 (.leaf (⟨2, 4, 274960, 274960, 215026792020, 361617201270⟩, 98239963))
 (.branch 24
 (.leaf (⟨1, 4, 274690, 274465, 361617786720, 288326448720⟩, 587))
 (.leaf (⟨1, 4, 274690, 274465, 361616738145, 288326448645⟩, 940)))))
 (.branch 27
 (.branch 26
 (.leaf (⟨1, 4, 274690, 274465, 361599960930, 288326447205⟩, 1361))
 (.leaf (⟨1, 4, 274690, 274465, 361331525475, 288326420325⟩, 1470)))
 (.branch 28
 (.leaf (⟨1, 4, 274690, 274465, 357036558180, 288325928805⟩, 1579))
 (.branch 29
 (.leaf (⟨1, 4, 274690, 274465, 288317081445, 288317081445⟩, 1604))
 (.leaf (⟨2, 4, 274720, 274720, 361626105360, 361626105360⟩, 17170697))))))
 (.branch 35
 (.branch 32
 (.branch 31
 (.leaf (⟨2, 4, 274720, 274720, 361609328160, 361626104160⟩, 27394469))
 (.leaf (⟨2, 4, 274720, 274720, 361592550945, 361626104070⟩, 44761774)))
 (.branch 33
 (.leaf (⟨2, 4, 274720, 274720, 361340892720, 361626081120⟩, 32899577))
 (.branch 34
 (.leaf (⟨2, 4, 274720, 274720, 361324115505, 361626081030⟩, 50529030))
 (.leaf (⟨2, 4, 274720, 274720, 361055680050, 361626079350⟩, 67896335)))))
 (.branch 38
 (.branch 36
 (.leaf (⟨2, 4, 274720, 274720, 357029148225, 361625650950⟩, 56034138))
 (.branch 37
 (.leaf (⟨2, 4, 274720, 274720, 356760712770, 361625649270⟩, 78120107))
 (.leaf (⟨2, 4, 274720, 274720, 288041236050, 361617784950⟩, 83625215))))
 (.branch 39
 (.leaf (⟨2, 4, 274720, 274720, 283746268755, 361617754230⟩, 90768748))
 (.branch 40
 (.leaf (⟨2, 4, 274720, 274720, 215026792020, 361617201270⟩, 97912281))
 (.leaf (⟨2, 4, 274465, 274690, 361626105360, 361626105360⟩, 17170697))))))))
 (.branch 61
 (.branch 51
 (.branch 46
 (.branch 43
 (.branch 42
 (.leaf (⟨2, 4, 274465, 274690, 361609328160, 361626104160⟩, 27394469))
 (.leaf (⟨2, 4, 274465, 274690, 361592550945, 361626104070⟩, 44761774)))
 (.branch 44
 (.leaf (⟨2, 4, 274465, 274690, 361340892720, 361626081120⟩, 32899577))
 (.branch 45
 (.leaf (⟨2, 4, 274465, 274690, 361324115505, 361626081030⟩, 50529030))
 (.leaf (⟨2, 4, 274465, 274690, 361055680050, 361626079350⟩, 67896335)))))
 (.branch 48
 (.branch 47
 (.leaf (⟨2, 4, 274465, 274690, 357029148225, 361625650950⟩, 56034138))
 (.leaf (⟨2, 4, 274465, 274690, 356760712770, 361625649270⟩, 78120107)))
 (.branch 49
 (.leaf (⟨2, 4, 274465, 274690, 288041236050, 361617784950⟩, 83625215))
 (.branch 50
 (.leaf (⟨2, 4, 274465, 274690, 283746268755, 361617754230⟩, 90768748))
 (.leaf (⟨2, 4, 274465, 274690, 215026792020, 361617201270⟩, 97912281))))))
 (.branch 56
 (.branch 53
 (.branch 52
 (.leaf (⟨3, 4, 274960, 274960, 361742426640, 434925761040⟩, 141446479197464270795767929))
 (.leaf (⟨3, 4, 274960, 274960, 361473991440, 434925741840⟩, 228490466395557386027860161)))
 (.branch 54
 (.leaf (⟨3, 4, 274960, 274960, 361205556000, 434925740400⟩, 417085771991425802364059997))
 (.branch 55
 (.leaf (⟨3, 4, 274960, 274960, 356642153505, 434925371655⟩, 737456002651074073704399462))
 (.leaf (⟨3, 4, 274960, 274960, 279332742450, 434918461575⟩, 1164213328775058374772851655)))))
 (.branch 58
 (.branch 57
 (.leaf (⟨3, 4, 274960, 274960, 210613265730, 434917970055⟩, 1352808634370926791109051491))
 (.leaf (⟨1, 4, 270595, 262945, 361617786720, 288326448720⟩, 593)))
 (.branch 59
 (.leaf (⟨1, 4, 270595, 262945, 361616738145, 288326448645⟩, 946))
 (.branch 60
 (.leaf (⟨1, 4, 270595, 262945, 361599960930, 288326447205⟩, 1367))
 (.leaf (⟨1, 4, 270595, 262945, 361331525475, 288326420325⟩, 1476)))))))
 (.branch 71
 (.branch 66
 (.branch 63
 (.branch 62
 (.leaf (⟨1, 4, 270595, 262945, 357036558180, 288325928805⟩, 1585))
 (.leaf (⟨1, 4, 270595, 262945, 288317081445, 288317081445⟩, 1610)))
 (.branch 64
 (.leaf (⟨2, 4, 270640, 267040, 361626105360, 361626105360⟩, 17563916))
 (.branch 65
 (.leaf (⟨2, 4, 270640, 267040, 361609328160, 361626104160⟩, 27787688))
 (.leaf (⟨2, 4, 270640, 267040, 361592550945, 361626104070⟩, 45154993)))))
 (.branch 68
 (.branch 67
 (.leaf (⟨2, 4, 270640, 267040, 361340892720, 361626081120⟩, 33292796))
 (.leaf (⟨2, 4, 270640, 267040, 361324115505, 361626081030⟩, 50922249)))
 (.branch 69
 (.leaf (⟨2, 4, 270640, 267040, 361055680050, 361626079350⟩, 68289554))
 (.branch 70
 (.leaf (⟨2, 4, 270640, 267040, 357029148225, 361625650950⟩, 56427357))
 (.leaf (⟨2, 4, 270640, 267040, 356760712770, 361625649270⟩, 78513326))))))
 (.branch 76
 (.branch 73
 (.branch 72
 (.leaf (⟨2, 4, 270640, 267040, 288041236050, 361617784950⟩, 84018434))
 (.leaf (⟨2, 4, 270640, 267040, 283746268755, 361617754230⟩, 91161967)))
 (.branch 74
 (.leaf (⟨2, 4, 270640, 267040, 215026792020, 361617201270⟩, 98305500))
 (.branch 75
 (.leaf (⟨2, 4, 270385, 267010, 361626105360, 361626105360⟩, 17563916))
 (.leaf (⟨2, 4, 270385, 267010, 361609328160, 361626104160⟩, 27787688)))))
 (.branch 79
 (.branch 77
 (.leaf (⟨2, 4, 270385, 267010, 361592550945, 361626104070⟩, 45154993))
 (.branch 78
 (.leaf (⟨2, 4, 270385, 267010, 361340892720, 361626081120⟩, 33292796))
 (.leaf (⟨2, 4, 270385, 267010, 361324115505, 361626081030⟩, 50922249))))
 (.branch 80
 (.leaf (⟨2, 4, 270385, 267010, 361055680050, 361626079350⟩, 68289554))
 (.branch 81
 (.leaf (⟨2, 4, 270385, 267010, 357029148225, 361625650950⟩, 56427357))
 (.leaf (⟨2, 4, 270385, 267010, 356760712770, 361625649270⟩, 78513326)))))))))
 (.branch 123
 (.branch 102
 (.branch 92
 (.branch 87
 (.branch 84
 (.branch 83
 (.leaf (⟨2, 4, 270385, 267010, 288041236050, 361617784950⟩, 84018434))
 (.leaf (⟨2, 4, 270385, 267010, 283746268755, 361617754230⟩, 91161967)))
 (.branch 85
 (.leaf (⟨2, 4, 270385, 267010, 215026792020, 361617201270⟩, 98305500))
 (.branch 86
 (.leaf (⟨2, 4, 266290, 266290, 361626105360, 361626105360⟩, 17367302))
 (.leaf (⟨2, 4, 266290, 266290, 361609328160, 361626104160⟩, 27591074)))))
 (.branch 89
 (.branch 88
 (.leaf (⟨2, 4, 266290, 266290, 361592550945, 361626104070⟩, 44958379))
 (.leaf (⟨2, 4, 266290, 266290, 361340892720, 361626081120⟩, 33096182)))
 (.branch 90
 (.leaf (⟨2, 4, 266290, 266290, 361324115505, 361626081030⟩, 50725635))
 (.branch 91
 (.leaf (⟨2, 4, 266290, 266290, 361055680050, 361626079350⟩, 68092940))
 (.leaf (⟨2, 4, 266290, 266290, 357029148225, 361625650950⟩, 56230743))))))
 (.branch 97
 (.branch 94
 (.branch 93
 (.leaf (⟨2, 4, 266290, 266290, 356760712770, 361625649270⟩, 78316712))
 (.leaf (⟨2, 4, 266290, 266290, 288041236050, 361617784950⟩, 83821820)))
 (.branch 95
 (.leaf (⟨2, 4, 266290, 266290, 283746268755, 361617754230⟩, 90965353))
 (.branch 96
 (.leaf (⟨2, 4, 266290, 266290, 215026792020, 361617201270⟩, 98108886))
 (.leaf (⟨3, 4, 267040, 270640, 361742426640, 434925761040⟩, 143864404624232765346611319)))))
 (.branch 99
 (.branch 98
 (.leaf (⟨3, 4, 267040, 270640, 361473991440, 434925741840⟩, 230908391822325880578703551))
 (.leaf (⟨3, 4, 267040, 270640, 361205556000, 434925740400⟩, 419503697418194296914903387)))
 (.branch 100
 (.leaf (⟨3, 4, 267040, 270640, 356642153505, 434925371655⟩, 739873928077842568255242852))
 (.branch 101
 (.leaf (⟨3, 4, 267040, 270640, 279332742450, 434918461575⟩, 1166631254201826869323695045))
 (.leaf (⟨3, 4, 267040, 270640, 210613265730, 434917970055⟩, 1355226559797695285659894881)))))))
 (.branch 112
 (.branch 107
 (.branch 104
 (.branch 103
 (.leaf (⟨3, 4, 262945, 270595, 361742426640, 434925761040⟩, 143864404624232765346611319))
 (.leaf (⟨3, 4, 262945, 270595, 361473991440, 434925741840⟩, 230908391822325880578703551)))
 (.branch 105
 (.leaf (⟨3, 4, 262945, 270595, 361205556000, 434925740400⟩, 419503697418194296914903387))
 (.branch 106
 (.leaf (⟨3, 4, 262945, 270595, 356642153505, 434925371655⟩, 739873928077842568255242852))
 (.leaf (⟨3, 4, 262945, 270595, 279332742450, 434918461575⟩, 1166631254201826869323695045)))))
 (.branch 109
 (.branch 108
 (.leaf (⟨3, 4, 262945, 270595, 210613265730, 434917970055⟩, 1355226559797695285659894881))
 (.leaf (⟨1, 4, 205060, 17185, 361617786720, 288326448720⟩, 586)))
 (.branch 110
 (.leaf (⟨1, 4, 205060, 17185, 361616738145, 288326448645⟩, 939))
 (.branch 111
 (.leaf (⟨1, 4, 205060, 17185, 361599960930, 288326447205⟩, 1360))
 (.leaf (⟨1, 4, 205060, 17185, 361331525475, 288326420325⟩, 1469))))))
 (.branch 117
 (.branch 114
 (.branch 113
 (.leaf (⟨1, 4, 205060, 17185, 357036558180, 288325928805⟩, 1578))
 (.leaf (⟨1, 4, 205060, 17185, 288317081445, 288317081445⟩, 1603)))
 (.branch 115
 (.leaf (⟨2, 4, 205120, 82720, 361626105360, 361626105360⟩, 17105160))
 (.branch 116
 (.leaf (⟨2, 4, 205120, 82720, 361609328160, 361626104160⟩, 27328932))
 (.leaf (⟨2, 4, 205120, 82720, 361592550945, 361626104070⟩, 44696237)))))
 (.branch 120
 (.branch 118
 (.leaf (⟨2, 4, 205120, 82720, 361340892720, 361626081120⟩, 32834040))
 (.branch 119
 (.leaf (⟨2, 4, 205120, 82720, 361324115505, 361626081030⟩, 50463493))
 (.leaf (⟨2, 4, 205120, 82720, 361055680050, 361626079350⟩, 67830798))))
 (.branch 121
 (.leaf (⟨2, 4, 205120, 82720, 357029148225, 361625650950⟩, 55968601))
 (.branch 122
 (.leaf (⟨2, 4, 205120, 82720, 356760712770, 361625649270⟩, 78054570))
 (.leaf (⟨2, 4, 205120, 82720, 288041236050, 361617784950⟩, 83559678))))))))
 (.branch 144
 (.branch 133
 (.branch 128
 (.branch 125
 (.branch 124
 (.leaf (⟨2, 4, 205120, 82720, 283746268755, 361617754230⟩, 90703211))
 (.leaf (⟨2, 4, 205120, 82720, 215026792020, 361617201270⟩, 97846744)))
 (.branch 126
 (.leaf (⟨2, 4, 204865, 82690, 361626105360, 361626105360⟩, 17105160))
 (.branch 127
 (.leaf (⟨2, 4, 204865, 82690, 361609328160, 361626104160⟩, 27328932))
 (.leaf (⟨2, 4, 204865, 82690, 361592550945, 361626104070⟩, 44696237)))))
 (.branch 130
 (.branch 129
 (.leaf (⟨2, 4, 204865, 82690, 361340892720, 361626081120⟩, 32834040))
 (.leaf (⟨2, 4, 204865, 82690, 361324115505, 361626081030⟩, 50463493)))
 (.branch 131
 (.leaf (⟨2, 4, 204865, 82690, 361055680050, 361626079350⟩, 67830798))
 (.branch 132
 (.leaf (⟨2, 4, 204865, 82690, 357029148225, 361625650950⟩, 55968601))
 (.leaf (⟨2, 4, 204865, 82690, 356760712770, 361625649270⟩, 78054570))))))
 (.branch 138
 (.branch 135
 (.branch 134
 (.leaf (⟨2, 4, 204865, 82690, 288041236050, 361617784950⟩, 83559678))
 (.leaf (⟨2, 4, 204865, 82690, 283746268755, 361617754230⟩, 90703211)))
 (.branch 136
 (.leaf (⟨2, 4, 204865, 82690, 215026792020, 361617201270⟩, 97846744))
 (.branch 137
 (.leaf (⟨3, 4, 205840, 148240, 361742426640, 434925761040⟩, 140237534930824088639766648))
 (.leaf (⟨3, 4, 205840, 148240, 361473991440, 434925741840⟩, 227281522128917203871858880)))))
 (.branch 141
 (.branch 139
 (.leaf (⟨3, 4, 205840, 148240, 361205556000, 434925740400⟩, 415876827724785620208058716))
 (.branch 140
 (.leaf (⟨3, 4, 205840, 148240, 356642153505, 434925371655⟩, 736247058384433891548398181))
 (.leaf (⟨3, 4, 205840, 148240, 279332742450, 434918461575⟩, 1163004384508418192616850374))))
 (.branch 142
 (.leaf (⟨3, 4, 205840, 148240, 210613265730, 434917970055⟩, 1351599690104286608953050210))
 (.branch 143
 (.leaf (⟨2, 4, 135235, 66610, 361626105360, 361626105360⟩, 17170697))
 (.leaf (⟨2, 4, 135235, 66610, 361609328160, 361626104160⟩, 27394469)))))))
 (.branch 154
 (.branch 149
 (.branch 146
 (.branch 145
 (.leaf (⟨2, 4, 135235, 66610, 361592550945, 361626104070⟩, 44761774))
 (.leaf (⟨2, 4, 135235, 66610, 361340892720, 361626081120⟩, 32899577)))
 (.branch 147
 (.leaf (⟨2, 4, 135235, 66610, 361324115505, 361626081030⟩, 50529030))
 (.branch 148
 (.leaf (⟨2, 4, 135235, 66610, 361055680050, 361626079350⟩, 67896335))
 (.leaf (⟨2, 4, 135235, 66610, 357029148225, 361625650950⟩, 56034138)))))
 (.branch 151
 (.branch 150
 (.leaf (⟨2, 4, 135235, 66610, 356760712770, 361625649270⟩, 78120107))
 (.leaf (⟨2, 4, 135235, 66610, 288041236050, 361617784950⟩, 83625215)))
 (.branch 152
 (.leaf (⟨2, 4, 135235, 66610, 283746268755, 361617754230⟩, 90768748))
 (.branch 153
 (.leaf (⟨2, 4, 135235, 66610, 215026792020, 361617201270⟩, 97912281))
 (.leaf (⟨3, 4, 136240, 136240, 361742426640, 434925761040⟩, 141446479197464270795767929))))))
 (.branch 159
 (.branch 156
 (.branch 155
 (.leaf (⟨3, 4, 136240, 136240, 361473991440, 434925741840⟩, 228490466395557386027860161))
 (.leaf (⟨3, 4, 136240, 136240, 361205556000, 434925740400⟩, 417085771991425802364059997)))
 (.branch 157
 (.leaf (⟨3, 4, 136240, 136240, 356642153505, 434925371655⟩, 737456002651074073704399462))
 (.branch 158
 (.leaf (⟨3, 4, 136240, 136240, 279332742450, 434918461575⟩, 1164213328775058374772851655))
 (.leaf (⟨3, 4, 136240, 136240, 210613265730, 434917970055⟩, 1352808634370926791109051491)))))
 (.branch 162
 (.branch 160
 (.leaf (⟨3, 4, 132145, 136195, 361742426640, 434925761040⟩, 141446479197464270795767929))
 (.branch 161
 (.leaf (⟨3, 4, 132145, 136195, 361473991440, 434925741840⟩, 228490466395557386027860161))
 (.leaf (⟨3, 4, 132145, 136195, 361205556000, 434925740400⟩, 417085771991425802364059997))))
 (.branch 163
 (.leaf (⟨3, 4, 132145, 136195, 356642153505, 434925371655⟩, 737456002651074073704399462))
 (.branch 164
 (.leaf (⟨3, 4, 132145, 136195, 279332742450, 434918461575⟩, 1164213328775058374772851655))
 (.leaf (⟨3, 4, 132145, 136195, 210613265730, 434917970055⟩, 1352808634370926791109051491))))))))))
noncomputable def raw (i : Fin blockCount) : RawFacePlacement.Block := (records.get i.val).1
noncomputable def witness (i : Fin blockCount) (code : Nat) : Fin 3150 :=
  Fin.ofNat 3150 (Nat.land (Nat.shiftRight (records.get i.val).2 (16 * code)) 65535)
noncomputable def faceTable : Table Nat :=
(.branch 10276
 (.branch 6149
 (.branch 3108
 (.branch 2064
 (.branch 1056
 (.branch 1028
 (.branch 1026
 (.leaf 0)
 (.leaf 1))
 (.branch 1032
 (.leaf 2)
 (.branch 1040
 (.leaf 3)
 (.leaf 4))))
 (.branch 2050
 (.branch 2049
 (.leaf 5)
 (.leaf 6))
 (.branch 2052
 (.leaf 7)
 (.branch 2056
 (.leaf 8)
 (.leaf 9)))))
 (.branch 3081
 (.branch 3075
 (.branch 2080
 (.leaf 10)
 (.leaf 11))
 (.branch 3077
 (.leaf 12)
 (.branch 3078
 (.leaf 13)
 (.leaf 14))))
 (.branch 3084
 (.branch 3082
 (.leaf 15)
 (.leaf 16))
 (.branch 3090
 (.leaf 17)
 (.branch 3092
 (.leaf 18)
 (.leaf 19))))))
 (.branch 5125
 (.branch 4100
 (.branch 3120
 (.branch 3112
 (.leaf 20)
 (.leaf 21))
 (.branch 4097
 (.leaf 22)
 (.branch 4098
 (.leaf 23)
 (.leaf 24))))
 (.branch 4112
 (.branch 4104
 (.leaf 25)
 (.leaf 26))
 (.branch 4128
 (.leaf 27)
 (.branch 5123
 (.leaf 28)
 (.leaf 29)))))
 (.branch 5138
 (.branch 5129
 (.branch 5126
 (.leaf 30)
 (.leaf 31))
 (.branch 5130
 (.leaf 32)
 (.branch 5132
 (.leaf 33)
 (.leaf 34))))
 (.branch 5160
 (.branch 5140
 (.leaf 35)
 (.branch 5156
 (.leaf 36)
 (.leaf 37)))
 (.branch 5168
 (.leaf 38)
 (.branch 6147
 (.leaf 39)
 (.leaf 40)))))))
 (.branch 8208
 (.branch 7175
 (.branch 6162
 (.branch 6153
 (.branch 6150
 (.leaf 41)
 (.leaf 42))
 (.branch 6154
 (.leaf 43)
 (.branch 6156
 (.leaf 44)
 (.leaf 45))))
 (.branch 6180
 (.branch 6164
 (.leaf 46)
 (.leaf 47))
 (.branch 6184
 (.leaf 48)
 (.branch 6192
 (.leaf 49)
 (.leaf 50)))))
 (.branch 7220
 (.branch 7181
 (.branch 7179
 (.leaf 51)
 (.leaf 52))
 (.branch 7190
 (.leaf 53)
 (.branch 7212
 (.leaf 54)
 (.leaf 55))))
 (.branch 8194
 (.branch 8193
 (.leaf 56)
 (.leaf 57))
 (.branch 8196
 (.leaf 58)
 (.branch 8200
 (.leaf 59)
 (.leaf 60))))))
 (.branch 9252
 (.branch 9225
 (.branch 9219
 (.branch 8224
 (.leaf 61)
 (.leaf 62))
 (.branch 9221
 (.leaf 63)
 (.branch 9222
 (.leaf 64)
 (.leaf 65))))
 (.branch 9228
 (.branch 9226
 (.leaf 66)
 (.leaf 67))
 (.branch 9234
 (.leaf 68)
 (.branch 9236
 (.leaf 69)
 (.leaf 70)))))
 (.branch 10246
 (.branch 9264
 (.branch 9256
 (.leaf 71)
 (.leaf 72))
 (.branch 10243
 (.leaf 73)
 (.branch 10245
 (.leaf 74)
 (.leaf 75))))
 (.branch 10252
 (.branch 10249
 (.leaf 76)
 (.branch 10250
 (.leaf 77)
 (.leaf 78)))
 (.branch 10258
 (.leaf 79)
 (.branch 10260
 (.leaf 80)
 (.leaf 81))))))))
 (.branch 17448
 (.branch 14343
 (.branch 12308
 (.branch 12294
 (.branch 10288
 (.branch 10280
 (.leaf 82)
 (.leaf 83))
 (.branch 12291
 (.leaf 84)
 (.branch 12293
 (.leaf 85)
 (.leaf 86))))
 (.branch 12298
 (.branch 12297
 (.leaf 87)
 (.leaf 88))
 (.branch 12300
 (.leaf 89)
 (.branch 12306
 (.leaf 90)
 (.leaf 91)))))
 (.branch 13323
 (.branch 12328
 (.branch 12324
 (.leaf 92)
 (.leaf 93))
 (.branch 12336
 (.leaf 94)
 (.branch 13319
 (.leaf 95)
 (.leaf 96))))
 (.branch 13334
 (.branch 13325
 (.leaf 97)
 (.leaf 98))
 (.branch 13356
 (.leaf 99)
 (.branch 13364
 (.leaf 100)
 (.leaf 101))))))
 (.branch 16400
 (.branch 14388
 (.branch 14349
 (.branch 14347
 (.leaf 102)
 (.leaf 103))
 (.branch 14358
 (.leaf 104)
 (.branch 14380
 (.leaf 105)
 (.leaf 106))))
 (.branch 16386
 (.branch 16385
 (.leaf 107)
 (.leaf 108))
 (.branch 16388
 (.leaf 109)
 (.branch 16392
 (.leaf 110)
 (.leaf 111)))))
 (.branch 17417
 (.branch 17411
 (.branch 16416
 (.leaf 112)
 (.leaf 113))
 (.branch 17413
 (.leaf 114)
 (.branch 17414
 (.leaf 115)
 (.leaf 116))))
 (.branch 17426
 (.branch 17418
 (.leaf 117)
 (.branch 17420
 (.leaf 118)
 (.leaf 119)))
 (.branch 17428
 (.leaf 120)
 (.branch 17444
 (.leaf 121)
 (.leaf 122)))))))
 (.branch 24582
 (.branch 18468
 (.branch 18441
 (.branch 18435
 (.branch 17456
 (.leaf 123)
 (.leaf 124))
 (.branch 18437
 (.leaf 125)
 (.branch 18438
 (.leaf 126)
 (.leaf 127))))
 (.branch 18444
 (.branch 18442
 (.leaf 128)
 (.leaf 129))
 (.branch 18450
 (.leaf 130)
 (.branch 18452
 (.leaf 131)
 (.leaf 132)))))
 (.branch 19469
 (.branch 18480
 (.branch 18472
 (.leaf 133)
 (.leaf 134))
 (.branch 19463
 (.leaf 135)
 (.branch 19467
 (.leaf 136)
 (.leaf 137))))
 (.branch 19508
 (.branch 19478
 (.leaf 138)
 (.branch 19500
 (.leaf 139)
 (.leaf 140)))
 (.branch 24579
 (.leaf 141)
 (.branch 24581
 (.leaf 142)
 (.leaf 143))))))
 (.branch 25611
 (.branch 24596
 (.branch 24586
 (.branch 24585
 (.leaf 144)
 (.leaf 145))
 (.branch 24588
 (.leaf 146)
 (.branch 24594
 (.leaf 147)
 (.leaf 148))))
 (.branch 24616
 (.branch 24612
 (.leaf 149)
 (.leaf 150))
 (.branch 24624
 (.leaf 151)
 (.branch 25607
 (.leaf 152)
 (.leaf 153)))))
 (.branch 26631
 (.branch 25622
 (.branch 25613
 (.leaf 154)
 (.leaf 155))
 (.branch 25644
 (.leaf 156)
 (.branch 25652
 (.leaf 157)
 (.leaf 158))))
 (.branch 26646
 (.branch 26635
 (.leaf 159)
 (.branch 26637
 (.leaf 160)
 (.leaf 161)))
 (.branch 26668
 (.leaf 162)
 (.branch 26676
 (.leaf 163)
 (.leaf 164)))))))))
noncomputable def faceWitness (s r : Nat) : Fin blockCount :=
  Fin.ofNat blockCount (faceTable.get (s * 1024 + r))
noncomputable def validity (i : Nat) : Bool :=
  RawFaceNormalizers.blockValidCheck 5 (raw (Fin.ofNat blockCount i))
noncomputable def placement (b : Fin blockCount) (code : Nat) : Bool :=
  RawKindedFacePlacement.check 5 (raw b) template root FacetUniverses.RootedSixExtra01.cells
    code 0 (witness b code)
noncomputable def test (i : Nat) : Bool :=
  let b := Fin.ofNat blockCount i
  FiniteChecks.checkRange (placement b)
    0 (RawFacePlacement.count (raw b).shared (raw b).shared)
noncomputable def symmetry (i : Nat) : Bool :=
  RawOutsidePlacement.blockCheck FacetUniverses.RootedSixExtra01.Outside.vertexCode root.vertices
    (raw (Fin.ofNat blockCount i))
end Papers.RationalityTen.RootedCanonical.RootedSixExtra01.S5T0

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra01.S5T0
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
theorem check_0022_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 22)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 22)) 0 2 (by decide +kernel)
theorem block_0022 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 22)) 0 2 :=
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
theorem check_0028_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 28)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 28)) 0 1 (by decide +kernel)
theorem block_0028 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 28)) 0 1 :=
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
theorem check_0051_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 51)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 51)) 0 6 (by decide +kernel)
theorem block_0051 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 51)) 0 6 :=
  check_0051_0000
theorem check_0052_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 52)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 52)) 0 6 (by decide +kernel)
theorem block_0052 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 52)) 0 6 :=
  check_0052_0000
theorem check_0053_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 53)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 53)) 0 6 (by decide +kernel)
theorem block_0053 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 53)) 0 6 :=
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
theorem check_0057_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 57)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 57)) 0 1 (by decide +kernel)
theorem block_0057 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 57)) 0 1 :=
  check_0057_0000
theorem check_0058_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 58)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 58)) 0 1 (by decide +kernel)
theorem block_0058 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 58)) 0 1 :=
  check_0058_0000
theorem check_0059_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 59)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 59)) 0 1 (by decide +kernel)
theorem block_0059 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 59)) 0 1 :=
  check_0059_0000
theorem check_0060_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 60)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 60)) 0 1 (by decide +kernel)
theorem block_0060 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 60)) 0 1 :=
  check_0060_0000
theorem check_0061_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 61)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 61)) 0 1 (by decide +kernel)
theorem block_0061 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 61)) 0 1 :=
  check_0061_0000
theorem check_0062_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 62)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 62)) 0 1 (by decide +kernel)
theorem block_0062 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 62)) 0 1 :=
  check_0062_0000
theorem check_0063_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 63)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 63)) 0 2 (by decide +kernel)
theorem block_0063 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 63)) 0 2 :=
  check_0063_0000
end Papers.RationalityTen.RootedCanonical.RootedSixExtra01.S5T0

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra01.S5T0
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
theorem check_0099_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 99)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 99)) 0 6 (by decide +kernel)
theorem block_0099 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 99)) 0 6 :=
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
theorem check_0108_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 108)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 108)) 0 1 (by decide +kernel)
theorem block_0108 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 108)) 0 1 :=
  check_0108_0000
theorem check_0109_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 109)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 109)) 0 1 (by decide +kernel)
theorem block_0109 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 109)) 0 1 :=
  check_0109_0000
theorem check_0110_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 110)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 110)) 0 1 (by decide +kernel)
theorem block_0110 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 110)) 0 1 :=
  check_0110_0000
theorem check_0111_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 111)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 111)) 0 1 (by decide +kernel)
theorem block_0111 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 111)) 0 1 :=
  check_0111_0000
theorem check_0112_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 112)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 112)) 0 1 (by decide +kernel)
theorem block_0112 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 112)) 0 1 :=
  check_0112_0000
theorem check_0113_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 113)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 113)) 0 1 (by decide +kernel)
theorem block_0113 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 113)) 0 1 :=
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
end Papers.RationalityTen.RootedCanonical.RootedSixExtra01.S5T0

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra01.S5T0
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
theorem check_0140_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 140)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 140)) 0 6 (by decide +kernel)
theorem block_0140 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 140)) 0 6 :=
  check_0140_0000
theorem check_0141_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 141)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 141)) 0 6 (by decide +kernel)
theorem block_0141 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 141)) 0 6 :=
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
theorem check_0152_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 152)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 152)) 0 2 (by decide +kernel)
theorem block_0152 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 152)) 0 2 :=
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
theorem check_0160_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 160)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 160)) 0 6 (by decide +kernel)
theorem block_0160 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 160)) 0 6 :=
  check_0160_0000
theorem check_0161_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 161)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 161)) 0 6 (by decide +kernel)
theorem block_0161 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 161)) 0 6 :=
  check_0161_0000
theorem check_0162_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 162)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 162)) 0 6 (by decide +kernel)
theorem block_0162 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 162)) 0 6 :=
  check_0162_0000
theorem check_0163_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 163)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 163)) 0 6 (by decide +kernel)
theorem block_0163 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 163)) 0 6 :=
  check_0163_0000
theorem check_0164_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 164)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 164)) 0 6 (by decide +kernel)
theorem block_0164 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 164)) 0 6 :=
  check_0164_0000
end Papers.RationalityTen.RootedCanonical.RootedSixExtra01.S5T0

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra01.S5T0
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
theorem metadata_validity_0160 : FiniteChecks.Interval validity 160 165 :=
  FiniteChecks.interval_of_check validity 160 5 (by decide +kernel)
theorem metadata_validity : FiniteChecks.Interval validity 0 blockCount :=
  (FiniteChecks.interval_append (validity) 0 80 165
  (FiniteChecks.interval_append (validity) 0 32 80
  (FiniteChecks.interval_append (validity) 0 16 32
  metadata_validity_0000
  metadata_validity_0016)
  (FiniteChecks.interval_append (validity) 32 48 80
  metadata_validity_0032
  (FiniteChecks.interval_append (validity) 48 64 80
  metadata_validity_0048
  metadata_validity_0064)))
  (FiniteChecks.interval_append (validity) 80 128 165
  (FiniteChecks.interval_append (validity) 80 96 128
  metadata_validity_0080
  (FiniteChecks.interval_append (validity) 96 112 128
  metadata_validity_0096
  metadata_validity_0112))
  (FiniteChecks.interval_append (validity) 128 144 165
  metadata_validity_0128
  (FiniteChecks.interval_append (validity) 144 160 165
  metadata_validity_0144
  metadata_validity_0160))))
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
theorem metadata_symmetry_0160 : FiniteChecks.Interval symmetry 160 165 :=
  FiniteChecks.interval_of_check symmetry 160 5 (by decide +kernel)
theorem metadata_symmetry : FiniteChecks.Interval symmetry 0 blockCount :=
  (FiniteChecks.interval_append (symmetry) 0 80 165
  (FiniteChecks.interval_append (symmetry) 0 32 80
  (FiniteChecks.interval_append (symmetry) 0 16 32
  metadata_symmetry_0000
  metadata_symmetry_0016)
  (FiniteChecks.interval_append (symmetry) 32 48 80
  metadata_symmetry_0032
  (FiniteChecks.interval_append (symmetry) 48 64 80
  metadata_symmetry_0048
  metadata_symmetry_0064)))
  (FiniteChecks.interval_append (symmetry) 80 128 165
  (FiniteChecks.interval_append (symmetry) 80 96 128
  metadata_symmetry_0080
  (FiniteChecks.interval_append (symmetry) 96 112 128
  metadata_symmetry_0096
  metadata_symmetry_0112))
  (FiniteChecks.interval_append (symmetry) 128 144 165
  metadata_symmetry_0128
  (FiniteChecks.interval_append (symmetry) 144 160 165
  metadata_symmetry_0144
  metadata_symmetry_0160))))
theorem metadata_normalizers :
    RawFaceNormalizers.completeCheck 5 template root raw faceWitness = true := by decide +kernel
theorem metadata_root : RawFacetEmbedding.wellFormedCheck root = true := by decide +kernel
end Papers.RationalityTen.RootedCanonical.RootedSixExtra01.S5T0

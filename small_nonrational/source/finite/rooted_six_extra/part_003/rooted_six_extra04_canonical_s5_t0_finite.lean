module
prelude
public import RootedSixExtra04
public import RawKindedFacePlacement
public import RootedSixExtra04OutsideData
public import RawOutsidePlacement

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra04.S5T0
open ConcreteGrowth
abbrev blockCount : Nat := 186
noncomputable def template : Cell := ⟨2, 31, [3, 5, 6, 9, 10, 12, 17, 18, 24], [7, 13, 14, 19, 25, 26]⟩
noncomputable def root : Cell := FacetUniverses.RootedSixExtra04.cells 0
noncomputable def records : Table (RawFacePlacement.Block × Nat) :=
(.branch 93
 (.branch 46
 (.branch 23
 (.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf (⟨1, 4, 274960, 274960, 361617786720, 288326448720⟩, 762))
 (.leaf (⟨1, 4, 274960, 274960, 361616738145, 288326448645⟩, 1183)))
 (.branch 3
 (.leaf (⟨1, 4, 274960, 274960, 361599960930, 288326447205⟩, 1448))
 (.branch 4
 (.leaf (⟨1, 4, 274960, 274960, 361331525475, 288326420325⟩, 1713))
 (.leaf (⟨1, 4, 274960, 274960, 357036558180, 288325928805⟩, 1822)))))
 (.branch 8
 (.branch 6
 (.leaf (⟨1, 4, 274960, 274960, 288317081445, 288317081445⟩, 1847))
 (.branch 7
 (.leaf (⟨1, 4, 274945, 274945, 361617786720, 288326448720⟩, 762))
 (.leaf (⟨1, 4, 274945, 274945, 361616738145, 288326448645⟩, 1183))))
 (.branch 9
 (.leaf (⟨1, 4, 274945, 274945, 361599960930, 288326447205⟩, 1448))
 (.branch 10
 (.leaf (⟨1, 4, 274945, 274945, 361331525475, 288326420325⟩, 1713))
 (.leaf (⟨1, 4, 274945, 274945, 357036558180, 288325928805⟩, 1822))))))
 (.branch 17
 (.branch 14
 (.branch 12
 (.leaf (⟨1, 4, 274945, 274945, 288317081445, 288317081445⟩, 1847))
 (.branch 13
 (.leaf (⟨2, 4, 274960, 274960, 361626105360, 361626105360⟩, 18415897))
 (.leaf (⟨2, 4, 274960, 274960, 361609328160, 361626104160⟩, 28639669))))
 (.branch 15
 (.leaf (⟨2, 4, 274960, 274960, 361592550945, 361626104070⟩, 56230746))
 (.branch 16
 (.leaf (⟨2, 4, 274960, 274960, 361340892720, 361626081120⟩, 38863441))
 (.leaf (⟨2, 4, 274960, 274960, 361324115505, 361626081030⟩, 66454518)))))
 (.branch 20
 (.branch 18
 (.leaf (⟨2, 4, 274960, 274960, 357045925440, 361625651040⟩, 44368549))
 (.branch 19
 (.leaf (⟨2, 4, 274960, 274960, 356760712770, 361625649270⟩, 83821823))
 (.leaf (⟨2, 4, 274960, 274960, 352465745475, 361625618550⟩, 101189128))))
 (.branch 21
 (.leaf (⟨2, 4, 274960, 274960, 288309671505, 361617786630⟩, 71959626))
 (.branch 22
 (.leaf (⟨2, 4, 274960, 274960, 288041236050, 361617784950⟩, 89326931))
 (.leaf (⟨2, 4, 274960, 274960, 283746268755, 361617754230⟩, 106694236)))))))
 (.branch 34
 (.branch 28
 (.branch 25
 (.branch 24
 (.leaf (⟨2, 4, 274960, 274960, 215026792020, 361617201270⟩, 113837769))
 (.leaf (⟨1, 4, 274690, 274465, 361617786720, 288326448720⟩, 757)))
 (.branch 26
 (.leaf (⟨1, 4, 274690, 274465, 361616738145, 288326448645⟩, 1178))
 (.branch 27
 (.leaf (⟨1, 4, 274690, 274465, 361599960930, 288326447205⟩, 1443))
 (.leaf (⟨1, 4, 274690, 274465, 361331525475, 288326420325⟩, 1708)))))
 (.branch 31
 (.branch 29
 (.leaf (⟨1, 4, 274690, 274465, 357036558180, 288325928805⟩, 1817))
 (.branch 30
 (.leaf (⟨1, 4, 274690, 274465, 288317081445, 288317081445⟩, 1842))
 (.leaf (⟨2, 4, 274720, 274720, 361626105360, 361626105360⟩, 18088215))))
 (.branch 32
 (.leaf (⟨2, 4, 274720, 274720, 361609328160, 361626104160⟩, 28311987))
 (.branch 33
 (.leaf (⟨2, 4, 274720, 274720, 361592550945, 361626104070⟩, 55903064))
 (.leaf (⟨2, 4, 274720, 274720, 361340892720, 361626081120⟩, 38535759))))))
 (.branch 40
 (.branch 37
 (.branch 35
 (.leaf (⟨2, 4, 274720, 274720, 361324115505, 361626081030⟩, 66126836))
 (.branch 36
 (.leaf (⟨2, 4, 274720, 274720, 357045925440, 361625651040⟩, 44040867))
 (.leaf (⟨2, 4, 274720, 274720, 356760712770, 361625649270⟩, 83494141))))
 (.branch 38
 (.leaf (⟨2, 4, 274720, 274720, 352465745475, 361625618550⟩, 100861446))
 (.branch 39
 (.leaf (⟨2, 4, 274720, 274720, 288309671505, 361617786630⟩, 71631944))
 (.leaf (⟨2, 4, 274720, 274720, 288041236050, 361617784950⟩, 88999249)))))
 (.branch 43
 (.branch 41
 (.leaf (⟨2, 4, 274720, 274720, 283746268755, 361617754230⟩, 106366554))
 (.branch 42
 (.leaf (⟨2, 4, 274720, 274720, 215026792020, 361617201270⟩, 113510087))
 (.leaf (⟨2, 4, 274465, 274690, 361626105360, 361626105360⟩, 18088215))))
 (.branch 44
 (.leaf (⟨2, 4, 274465, 274690, 361609328160, 361626104160⟩, 28311987))
 (.branch 45
 (.leaf (⟨2, 4, 274465, 274690, 361592550945, 361626104070⟩, 55903064))
 (.leaf (⟨2, 4, 274465, 274690, 361340892720, 361626081120⟩, 38535759))))))))
 (.branch 69
 (.branch 57
 (.branch 51
 (.branch 48
 (.branch 47
 (.leaf (⟨2, 4, 274465, 274690, 361324115505, 361626081030⟩, 66126836))
 (.leaf (⟨2, 4, 274465, 274690, 357045925440, 361625651040⟩, 44040867)))
 (.branch 49
 (.leaf (⟨2, 4, 274465, 274690, 356760712770, 361625649270⟩, 83494141))
 (.branch 50
 (.leaf (⟨2, 4, 274465, 274690, 352465745475, 361625618550⟩, 100861446))
 (.leaf (⟨2, 4, 274465, 274690, 288309671505, 361617786630⟩, 71631944)))))
 (.branch 54
 (.branch 52
 (.leaf (⟨2, 4, 274465, 274690, 288041236050, 361617784950⟩, 88999249))
 (.branch 53
 (.leaf (⟨2, 4, 274465, 274690, 283746268755, 361617754230⟩, 106366554))
 (.leaf (⟨2, 4, 274465, 274690, 215026792020, 361617201270⟩, 113510087))))
 (.branch 55
 (.leaf (⟨3, 4, 274960, 274960, 361742426640, 434925761040⟩, 158371698930426820979785863))
 (.branch 56
 (.leaf (⟨3, 4, 274960, 274960, 361473991440, 434925741840⟩, 245415686128519936211878095))
 (.leaf (⟨3, 4, 274960, 274960, 356910588960, 434925371760⟩, 434010991724388352548077931))))))
 (.branch 63
 (.branch 60
 (.branch 58
 (.leaf (⟨3, 4, 274960, 274960, 352615621680, 434925344880⟩, 622606297320256768884277767))
 (.branch 59
 (.leaf (⟨3, 4, 274960, 274960, 287922677025, 434918490375⟩, 942976527979905040224617232))
 (.leaf (⟨3, 4, 274960, 274960, 283627709745, 434918463495⟩, 1131571833575773456560817068))))
 (.branch 61
 (.leaf (⟨3, 4, 274960, 274960, 210613265730, 434917970055⟩, 1451942064235421727901156533))
 (.branch 62
 (.leaf (⟨3, 4, 274960, 274960, 141893788995, 434917935495⟩, 1772312294895069999241495998))
 (.leaf (⟨1, 4, 270595, 262945, 361617786720, 288326448720⟩, 763)))))
 (.branch 66
 (.branch 64
 (.leaf (⟨1, 4, 270595, 262945, 361616738145, 288326448645⟩, 1184))
 (.branch 65
 (.leaf (⟨1, 4, 270595, 262945, 361599960930, 288326447205⟩, 1449))
 (.leaf (⟨1, 4, 270595, 262945, 361331525475, 288326420325⟩, 1714))))
 (.branch 67
 (.leaf (⟨1, 4, 270595, 262945, 357036558180, 288325928805⟩, 1823))
 (.branch 68
 (.leaf (⟨1, 4, 270595, 262945, 288317081445, 288317081445⟩, 1848))
 (.leaf (⟨2, 4, 270640, 267040, 361626105360, 361626105360⟩, 18481434)))))))
 (.branch 81
 (.branch 75
 (.branch 72
 (.branch 70
 (.leaf (⟨2, 4, 270640, 267040, 361609328160, 361626104160⟩, 28705206))
 (.branch 71
 (.leaf (⟨2, 4, 270640, 267040, 361592550945, 361626104070⟩, 56296283))
 (.leaf (⟨2, 4, 270640, 267040, 361340892720, 361626081120⟩, 38928978))))
 (.branch 73
 (.leaf (⟨2, 4, 270640, 267040, 361324115505, 361626081030⟩, 66520055))
 (.branch 74
 (.leaf (⟨2, 4, 270640, 267040, 357045925440, 361625651040⟩, 44434086))
 (.leaf (⟨2, 4, 270640, 267040, 356760712770, 361625649270⟩, 83887360)))))
 (.branch 78
 (.branch 76
 (.leaf (⟨2, 4, 270640, 267040, 352465745475, 361625618550⟩, 101254665))
 (.branch 77
 (.leaf (⟨2, 4, 270640, 267040, 288309671505, 361617786630⟩, 72025163))
 (.leaf (⟨2, 4, 270640, 267040, 288041236050, 361617784950⟩, 89392468))))
 (.branch 79
 (.leaf (⟨2, 4, 270640, 267040, 283746268755, 361617754230⟩, 106759773))
 (.branch 80
 (.leaf (⟨2, 4, 270640, 267040, 215026792020, 361617201270⟩, 113903306))
 (.leaf (⟨2, 4, 270385, 267010, 361626105360, 361626105360⟩, 18481434))))))
 (.branch 87
 (.branch 84
 (.branch 82
 (.leaf (⟨2, 4, 270385, 267010, 361609328160, 361626104160⟩, 28705206))
 (.branch 83
 (.leaf (⟨2, 4, 270385, 267010, 361592550945, 361626104070⟩, 56296283))
 (.leaf (⟨2, 4, 270385, 267010, 361340892720, 361626081120⟩, 38928978))))
 (.branch 85
 (.leaf (⟨2, 4, 270385, 267010, 361324115505, 361626081030⟩, 66520055))
 (.branch 86
 (.leaf (⟨2, 4, 270385, 267010, 357045925440, 361625651040⟩, 44434086))
 (.leaf (⟨2, 4, 270385, 267010, 356760712770, 361625649270⟩, 83887360)))))
 (.branch 90
 (.branch 88
 (.leaf (⟨2, 4, 270385, 267010, 352465745475, 361625618550⟩, 101254665))
 (.branch 89
 (.leaf (⟨2, 4, 270385, 267010, 288309671505, 361617786630⟩, 72025163))
 (.leaf (⟨2, 4, 270385, 267010, 288041236050, 361617784950⟩, 89392468))))
 (.branch 91
 (.leaf (⟨2, 4, 270385, 267010, 283746268755, 361617754230⟩, 106759773))
 (.branch 92
 (.leaf (⟨2, 4, 270385, 267010, 215026792020, 361617201270⟩, 113903306))
 (.leaf (⟨2, 4, 266290, 266290, 361626105360, 361626105360⟩, 18284820)))))))))
 (.branch 139
 (.branch 116
 (.branch 104
 (.branch 98
 (.branch 95
 (.branch 94
 (.leaf (⟨2, 4, 266290, 266290, 361609328160, 361626104160⟩, 28508592))
 (.leaf (⟨2, 4, 266290, 266290, 361592550945, 361626104070⟩, 56099669)))
 (.branch 96
 (.leaf (⟨2, 4, 266290, 266290, 361340892720, 361626081120⟩, 38732364))
 (.branch 97
 (.leaf (⟨2, 4, 266290, 266290, 361324115505, 361626081030⟩, 66323441))
 (.leaf (⟨2, 4, 266290, 266290, 357045925440, 361625651040⟩, 44237472)))))
 (.branch 101
 (.branch 99
 (.leaf (⟨2, 4, 266290, 266290, 356760712770, 361625649270⟩, 83690746))
 (.branch 100
 (.leaf (⟨2, 4, 266290, 266290, 352465745475, 361625618550⟩, 101058051))
 (.leaf (⟨2, 4, 266290, 266290, 288309671505, 361617786630⟩, 71828549))))
 (.branch 102
 (.leaf (⟨2, 4, 266290, 266290, 288041236050, 361617784950⟩, 89195854))
 (.branch 103
 (.leaf (⟨2, 4, 266290, 266290, 283746268755, 361617754230⟩, 106563159))
 (.leaf (⟨2, 4, 266290, 266290, 215026792020, 361617201270⟩, 113706692))))))
 (.branch 110
 (.branch 107
 (.branch 105
 (.leaf (⟨3, 4, 267040, 270640, 361742426640, 434925761040⟩, 160789624357195315530629253))
 (.branch 106
 (.leaf (⟨3, 4, 267040, 270640, 361473991440, 434925741840⟩, 247833611555288430762721485))
 (.leaf (⟨3, 4, 267040, 270640, 356910588960, 434925371760⟩, 436428917151156847098921321))))
 (.branch 108
 (.leaf (⟨3, 4, 267040, 270640, 352615621680, 434925344880⟩, 625024222747025263435121157))
 (.branch 109
 (.leaf (⟨3, 4, 267040, 270640, 287922677025, 434918490375⟩, 945394453406673534775460622))
 (.leaf (⟨3, 4, 267040, 270640, 283627709745, 434918463495⟩, 1133989759002541951111660458)))))
 (.branch 113
 (.branch 111
 (.leaf (⟨3, 4, 267040, 270640, 210613265730, 434917970055⟩, 1454359989662190222451999923))
 (.branch 112
 (.leaf (⟨3, 4, 267040, 270640, 141893788995, 434917935495⟩, 1774730220321838493792339388))
 (.leaf (⟨3, 4, 262945, 270595, 361742426640, 434925761040⟩, 160789624357195315530629253))))
 (.branch 114
 (.leaf (⟨3, 4, 262945, 270595, 361473991440, 434925741840⟩, 247833611555288430762721485))
 (.branch 115
 (.leaf (⟨3, 4, 262945, 270595, 356910588960, 434925371760⟩, 436428917151156847098921321))
 (.leaf (⟨3, 4, 262945, 270595, 352615621680, 434925344880⟩, 625024222747025263435121157)))))))
 (.branch 127
 (.branch 121
 (.branch 118
 (.branch 117
 (.leaf (⟨3, 4, 262945, 270595, 287922677025, 434918490375⟩, 945394453406673534775460622))
 (.leaf (⟨3, 4, 262945, 270595, 283627709745, 434918463495⟩, 1133989759002541951111660458)))
 (.branch 119
 (.leaf (⟨3, 4, 262945, 270595, 210613265730, 434917970055⟩, 1454359989662190222451999923))
 (.branch 120
 (.leaf (⟨3, 4, 262945, 270595, 141893788995, 434917935495⟩, 1774730220321838493792339388))
 (.leaf (⟨1, 4, 205060, 17185, 361617786720, 288326448720⟩, 756)))))
 (.branch 124
 (.branch 122
 (.leaf (⟨1, 4, 205060, 17185, 361616738145, 288326448645⟩, 1177))
 (.branch 123
 (.leaf (⟨1, 4, 205060, 17185, 361599960930, 288326447205⟩, 1442))
 (.leaf (⟨1, 4, 205060, 17185, 361331525475, 288326420325⟩, 1707))))
 (.branch 125
 (.leaf (⟨1, 4, 205060, 17185, 357036558180, 288325928805⟩, 1816))
 (.branch 126
 (.leaf (⟨1, 4, 205060, 17185, 288317081445, 288317081445⟩, 1841))
 (.leaf (⟨2, 4, 205120, 82720, 361626105360, 361626105360⟩, 18022678))))))
 (.branch 133
 (.branch 130
 (.branch 128
 (.leaf (⟨2, 4, 205120, 82720, 361609328160, 361626104160⟩, 28246450))
 (.branch 129
 (.leaf (⟨2, 4, 205120, 82720, 361592550945, 361626104070⟩, 55837527))
 (.leaf (⟨2, 4, 205120, 82720, 361340892720, 361626081120⟩, 38470222))))
 (.branch 131
 (.leaf (⟨2, 4, 205120, 82720, 361324115505, 361626081030⟩, 66061299))
 (.branch 132
 (.leaf (⟨2, 4, 205120, 82720, 357045925440, 361625651040⟩, 43975330))
 (.leaf (⟨2, 4, 205120, 82720, 356760712770, 361625649270⟩, 83428604)))))
 (.branch 136
 (.branch 134
 (.leaf (⟨2, 4, 205120, 82720, 352465745475, 361625618550⟩, 100795909))
 (.branch 135
 (.leaf (⟨2, 4, 205120, 82720, 288309671505, 361617786630⟩, 71566407))
 (.leaf (⟨2, 4, 205120, 82720, 288041236050, 361617784950⟩, 88933712))))
 (.branch 137
 (.leaf (⟨2, 4, 205120, 82720, 283746268755, 361617754230⟩, 106301017))
 (.branch 138
 (.leaf (⟨2, 4, 205120, 82720, 215026792020, 361617201270⟩, 113444550))
 (.leaf (⟨2, 4, 204865, 82690, 361626105360, 361626105360⟩, 18022678))))))))
 (.branch 162
 (.branch 150
 (.branch 144
 (.branch 141
 (.branch 140
 (.leaf (⟨2, 4, 204865, 82690, 361609328160, 361626104160⟩, 28246450))
 (.leaf (⟨2, 4, 204865, 82690, 361592550945, 361626104070⟩, 55837527)))
 (.branch 142
 (.leaf (⟨2, 4, 204865, 82690, 361340892720, 361626081120⟩, 38470222))
 (.branch 143
 (.leaf (⟨2, 4, 204865, 82690, 361324115505, 361626081030⟩, 66061299))
 (.leaf (⟨2, 4, 204865, 82690, 357045925440, 361625651040⟩, 43975330)))))
 (.branch 147
 (.branch 145
 (.leaf (⟨2, 4, 204865, 82690, 356760712770, 361625649270⟩, 83428604))
 (.branch 146
 (.leaf (⟨2, 4, 204865, 82690, 352465745475, 361625618550⟩, 100795909))
 (.leaf (⟨2, 4, 204865, 82690, 288309671505, 361617786630⟩, 71566407))))
 (.branch 148
 (.leaf (⟨2, 4, 204865, 82690, 288041236050, 361617784950⟩, 88933712))
 (.branch 149
 (.leaf (⟨2, 4, 204865, 82690, 283746268755, 361617754230⟩, 106301017))
 (.leaf (⟨2, 4, 204865, 82690, 215026792020, 361617201270⟩, 113444550))))))
 (.branch 156
 (.branch 153
 (.branch 151
 (.leaf (⟨3, 4, 205840, 148240, 361742426640, 434925761040⟩, 157162754663786638823784582))
 (.branch 152
 (.leaf (⟨3, 4, 205840, 148240, 361473991440, 434925741840⟩, 244206741861879754055876814))
 (.leaf (⟨3, 4, 205840, 148240, 356910588960, 434925371760⟩, 432802047457748170392076650))))
 (.branch 154
 (.leaf (⟨3, 4, 205840, 148240, 352615621680, 434925344880⟩, 621397353053616586728276486))
 (.branch 155
 (.leaf (⟨3, 4, 205840, 148240, 287922677025, 434918490375⟩, 941767583713264858068615951))
 (.leaf (⟨3, 4, 205840, 148240, 283627709745, 434918463495⟩, 1130362889309133274404815787)))))
 (.branch 159
 (.branch 157
 (.leaf (⟨3, 4, 205840, 148240, 210613265730, 434917970055⟩, 1450733119968781545745155252))
 (.branch 158
 (.leaf (⟨3, 4, 205840, 148240, 141893788995, 434917935495⟩, 1771103350628429817085494717))
 (.leaf (⟨2, 4, 135235, 66610, 361626105360, 361626105360⟩, 18088215))))
 (.branch 160
 (.leaf (⟨2, 4, 135235, 66610, 361609328160, 361626104160⟩, 28311987))
 (.branch 161
 (.leaf (⟨2, 4, 135235, 66610, 361592550945, 361626104070⟩, 55903064))
 (.leaf (⟨2, 4, 135235, 66610, 361340892720, 361626081120⟩, 38535759)))))))
 (.branch 174
 (.branch 168
 (.branch 165
 (.branch 163
 (.leaf (⟨2, 4, 135235, 66610, 361324115505, 361626081030⟩, 66126836))
 (.branch 164
 (.leaf (⟨2, 4, 135235, 66610, 357045925440, 361625651040⟩, 44040867))
 (.leaf (⟨2, 4, 135235, 66610, 356760712770, 361625649270⟩, 83494141))))
 (.branch 166
 (.leaf (⟨2, 4, 135235, 66610, 352465745475, 361625618550⟩, 100861446))
 (.branch 167
 (.leaf (⟨2, 4, 135235, 66610, 288309671505, 361617786630⟩, 71631944))
 (.leaf (⟨2, 4, 135235, 66610, 288041236050, 361617784950⟩, 88999249)))))
 (.branch 171
 (.branch 169
 (.leaf (⟨2, 4, 135235, 66610, 283746268755, 361617754230⟩, 106366554))
 (.branch 170
 (.leaf (⟨2, 4, 135235, 66610, 215026792020, 361617201270⟩, 113510087))
 (.leaf (⟨3, 4, 136240, 136240, 361742426640, 434925761040⟩, 158371698930426820979785863))))
 (.branch 172
 (.leaf (⟨3, 4, 136240, 136240, 361473991440, 434925741840⟩, 245415686128519936211878095))
 (.branch 173
 (.leaf (⟨3, 4, 136240, 136240, 356910588960, 434925371760⟩, 434010991724388352548077931))
 (.leaf (⟨3, 4, 136240, 136240, 352615621680, 434925344880⟩, 622606297320256768884277767))))))
 (.branch 180
 (.branch 177
 (.branch 175
 (.leaf (⟨3, 4, 136240, 136240, 287922677025, 434918490375⟩, 942976527979905040224617232))
 (.branch 176
 (.leaf (⟨3, 4, 136240, 136240, 283627709745, 434918463495⟩, 1131571833575773456560817068))
 (.leaf (⟨3, 4, 136240, 136240, 210613265730, 434917970055⟩, 1451942064235421727901156533))))
 (.branch 178
 (.leaf (⟨3, 4, 136240, 136240, 141893788995, 434917935495⟩, 1772312294895069999241495998))
 (.branch 179
 (.leaf (⟨3, 4, 132145, 136195, 361742426640, 434925761040⟩, 158371698930426820979785863))
 (.leaf (⟨3, 4, 132145, 136195, 361473991440, 434925741840⟩, 245415686128519936211878095)))))
 (.branch 183
 (.branch 181
 (.leaf (⟨3, 4, 132145, 136195, 356910588960, 434925371760⟩, 434010991724388352548077931))
 (.branch 182
 (.leaf (⟨3, 4, 132145, 136195, 352615621680, 434925344880⟩, 622606297320256768884277767))
 (.leaf (⟨3, 4, 132145, 136195, 287922677025, 434918490375⟩, 942976527979905040224617232))))
 (.branch 184
 (.leaf (⟨3, 4, 132145, 136195, 283627709745, 434918463495⟩, 1131571833575773456560817068))
 (.branch 185
 (.leaf (⟨3, 4, 132145, 136195, 210613265730, 434917970055⟩, 1451942064235421727901156533))
 (.leaf (⟨3, 4, 132145, 136195, 141893788995, 434917935495⟩, 1772312294895069999241495998))))))))))
noncomputable def raw (i : Fin blockCount) : RawFacePlacement.Block := (records.get i.val).1
noncomputable def witness (i : Fin blockCount) (code : Nat) : Fin 3640 :=
  Fin.ofNat 3640 (Nat.land (Nat.shiftRight (records.get i.val).2 (16 * code)) 65535)
noncomputable def faceTable : Table Nat :=
(.branch 12293
 (.branch 6154
 (.branch 3120
 (.branch 2080
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
 (.branch 2052
 (.branch 2049
 (.leaf 5)
 (.branch 2050
 (.leaf 6)
 (.leaf 7)))
 (.branch 2056
 (.leaf 8)
 (.branch 2064
 (.leaf 9)
 (.leaf 10)))))
 (.branch 3089
 (.branch 3078
 (.branch 3075
 (.leaf 11)
 (.branch 3077
 (.leaf 12)
 (.leaf 13)))
 (.branch 3081
 (.leaf 14)
 (.branch 3082
 (.leaf 15)
 (.leaf 16))))
 (.branch 3106
 (.branch 3092
 (.leaf 17)
 (.branch 3096
 (.leaf 18)
 (.leaf 19)))
 (.branch 3108
 (.leaf 20)
 (.branch 3112
 (.leaf 21)
 (.leaf 22))))))
 (.branch 5130
 (.branch 4112
 (.branch 4098
 (.branch 4097
 (.leaf 23)
 (.leaf 24))
 (.branch 4100
 (.leaf 25)
 (.branch 4104
 (.leaf 26)
 (.leaf 27))))
 (.branch 5125
 (.branch 4128
 (.leaf 28)
 (.branch 5123
 (.leaf 29)
 (.leaf 30)))
 (.branch 5126
 (.leaf 31)
 (.branch 5129
 (.leaf 32)
 (.leaf 33)))))
 (.branch 5160
 (.branch 5144
 (.branch 5137
 (.leaf 34)
 (.branch 5140
 (.leaf 35)
 (.leaf 36)))
 (.branch 5154
 (.leaf 37)
 (.branch 5156
 (.leaf 38)
 (.leaf 39))))
 (.branch 6149
 (.branch 5168
 (.leaf 40)
 (.branch 6147
 (.leaf 41)
 (.leaf 42)))
 (.branch 6150
 (.leaf 43)
 (.branch 6153
 (.leaf 44)
 (.leaf 45)))))))
 (.branch 9221
 (.branch 7193
 (.branch 6180
 (.branch 6164
 (.branch 6161
 (.leaf 46)
 (.leaf 47))
 (.branch 6168
 (.leaf 48)
 (.branch 6178
 (.leaf 49)
 (.leaf 50))))
 (.branch 7175
 (.branch 6184
 (.leaf 51)
 (.branch 6192
 (.leaf 52)
 (.leaf 53)))
 (.branch 7179
 (.leaf 54)
 (.branch 7189
 (.leaf 55)
 (.leaf 56)))))
 (.branch 8194
 (.branch 7220
 (.branch 7206
 (.leaf 57)
 (.branch 7210
 (.leaf 58)
 (.leaf 59)))
 (.branch 7224
 (.leaf 60)
 (.branch 8193
 (.leaf 61)
 (.leaf 62))))
 (.branch 8208
 (.branch 8196
 (.leaf 63)
 (.branch 8200
 (.leaf 64)
 (.leaf 65)))
 (.branch 8224
 (.leaf 66)
 (.branch 9219
 (.leaf 67)
 (.leaf 68))))))
 (.branch 10245
 (.branch 9240
 (.branch 9226
 (.branch 9222
 (.leaf 69)
 (.branch 9225
 (.leaf 70)
 (.leaf 71)))
 (.branch 9233
 (.leaf 72)
 (.branch 9236
 (.leaf 73)
 (.leaf 74))))
 (.branch 9256
 (.branch 9250
 (.leaf 75)
 (.branch 9252
 (.leaf 76)
 (.leaf 77)))
 (.branch 9264
 (.leaf 78)
 (.branch 10243
 (.leaf 79)
 (.leaf 80)))))
 (.branch 10264
 (.branch 10250
 (.branch 10246
 (.leaf 81)
 (.branch 10249
 (.leaf 82)
 (.leaf 83)))
 (.branch 10257
 (.leaf 84)
 (.branch 10260
 (.leaf 85)
 (.leaf 86))))
 (.branch 10280
 (.branch 10274
 (.leaf 87)
 (.branch 10276
 (.leaf 88)
 (.leaf 89)))
 (.branch 10288
 (.leaf 90)
 (.branch 12291
 (.leaf 91)
 (.leaf 92))))))))
 (.branch 18437
 (.branch 14374
 (.branch 13319
 (.branch 12308
 (.branch 12297
 (.branch 12294
 (.leaf 93)
 (.leaf 94))
 (.branch 12298
 (.leaf 95)
 (.branch 12305
 (.leaf 96)
 (.leaf 97))))
 (.branch 12324
 (.branch 12312
 (.leaf 98)
 (.branch 12322
 (.leaf 99)
 (.leaf 100)))
 (.branch 12328
 (.leaf 101)
 (.branch 12336
 (.leaf 102)
 (.leaf 103)))))
 (.branch 13364
 (.branch 13337
 (.branch 13323
 (.leaf 104)
 (.branch 13333
 (.leaf 105)
 (.leaf 106)))
 (.branch 13350
 (.leaf 107)
 (.branch 13354
 (.leaf 108)
 (.leaf 109))))
 (.branch 14347
 (.branch 13368
 (.leaf 110)
 (.branch 14343
 (.leaf 111)
 (.leaf 112)))
 (.branch 14357
 (.leaf 113)
 (.branch 14361
 (.leaf 114)
 (.leaf 115))))))
 (.branch 17413
 (.branch 16386
 (.branch 14388
 (.branch 14378
 (.leaf 116)
 (.leaf 117))
 (.branch 14392
 (.leaf 118)
 (.branch 16385
 (.leaf 119)
 (.leaf 120))))
 (.branch 16400
 (.branch 16388
 (.leaf 121)
 (.branch 16392
 (.leaf 122)
 (.leaf 123)))
 (.branch 16416
 (.leaf 124)
 (.branch 17411
 (.leaf 125)
 (.leaf 126)))))
 (.branch 17432
 (.branch 17418
 (.branch 17414
 (.leaf 127)
 (.branch 17417
 (.leaf 128)
 (.leaf 129)))
 (.branch 17425
 (.leaf 130)
 (.branch 17428
 (.leaf 131)
 (.leaf 132))))
 (.branch 17448
 (.branch 17442
 (.leaf 133)
 (.branch 17444
 (.leaf 134)
 (.leaf 135)))
 (.branch 17456
 (.leaf 136)
 (.branch 18435
 (.leaf 137)
 (.leaf 138)))))))
 (.branch 24586
 (.branch 19463
 (.branch 18452
 (.branch 18441
 (.branch 18438
 (.leaf 139)
 (.leaf 140))
 (.branch 18442
 (.leaf 141)
 (.branch 18449
 (.leaf 142)
 (.leaf 143))))
 (.branch 18468
 (.branch 18456
 (.leaf 144)
 (.branch 18466
 (.leaf 145)
 (.leaf 146)))
 (.branch 18472
 (.leaf 147)
 (.branch 18480
 (.leaf 148)
 (.leaf 149)))))
 (.branch 19508
 (.branch 19481
 (.branch 19467
 (.leaf 150)
 (.branch 19477
 (.leaf 151)
 (.leaf 152)))
 (.branch 19494
 (.leaf 153)
 (.branch 19498
 (.leaf 154)
 (.leaf 155))))
 (.branch 24581
 (.branch 19512
 (.leaf 156)
 (.branch 24579
 (.leaf 157)
 (.leaf 158)))
 (.branch 24582
 (.leaf 159)
 (.branch 24585
 (.leaf 160)
 (.leaf 161))))))
 (.branch 25638
 (.branch 24616
 (.branch 24600
 (.branch 24593
 (.leaf 162)
 (.branch 24596
 (.leaf 163)
 (.leaf 164)))
 (.branch 24610
 (.leaf 165)
 (.branch 24612
 (.leaf 166)
 (.leaf 167))))
 (.branch 25611
 (.branch 24624
 (.leaf 168)
 (.branch 25607
 (.leaf 169)
 (.leaf 170)))
 (.branch 25621
 (.leaf 171)
 (.branch 25625
 (.leaf 172)
 (.leaf 173)))))
 (.branch 26645
 (.branch 25656
 (.branch 25642
 (.leaf 174)
 (.branch 25652
 (.leaf 175)
 (.leaf 176)))
 (.branch 26631
 (.leaf 177)
 (.branch 26635
 (.leaf 178)
 (.leaf 179))))
 (.branch 26666
 (.branch 26649
 (.leaf 180)
 (.branch 26662
 (.leaf 181)
 (.leaf 182)))
 (.branch 26676
 (.leaf 183)
 (.branch 26680
 (.leaf 184)
 (.leaf 185)))))))))
noncomputable def faceWitness (s r : Nat) : Fin blockCount :=
  Fin.ofNat blockCount (faceTable.get (s * 1024 + r))
noncomputable def validity (i : Nat) : Bool :=
  RawFaceNormalizers.blockValidCheck 5 (raw (Fin.ofNat blockCount i))
noncomputable def placement (b : Fin blockCount) (code : Nat) : Bool :=
  RawKindedFacePlacement.check 5 (raw b) template root FacetUniverses.RootedSixExtra04.cells
    code 0 (witness b code)
noncomputable def test (i : Nat) : Bool :=
  let b := Fin.ofNat blockCount i
  FiniteChecks.checkRange (placement b)
    0 (RawFacePlacement.count (raw b).shared (raw b).shared)
noncomputable def symmetry (i : Nat) : Bool :=
  RawOutsidePlacement.blockCheck FacetUniverses.RootedSixExtra04.Outside.vertexCode root.vertices
    (raw (Fin.ofNat blockCount i))
end Papers.RationalityTen.RootedCanonical.RootedSixExtra04.S5T0

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra04.S5T0
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
theorem check_0023_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 23)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 23)) 0 2 (by decide +kernel)
theorem block_0023 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 23)) 0 2 :=
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
theorem check_0029_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 29)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 29)) 0 1 (by decide +kernel)
theorem block_0029 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 29)) 0 1 :=
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
theorem check_0058_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 58)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 58)) 0 6 (by decide +kernel)
theorem block_0058 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 58)) 0 6 :=
  check_0058_0000
theorem check_0059_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 59)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 59)) 0 6 (by decide +kernel)
theorem block_0059 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 59)) 0 6 :=
  check_0059_0000
theorem check_0060_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 60)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 60)) 0 6 (by decide +kernel)
theorem block_0060 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 60)) 0 6 :=
  check_0060_0000
theorem check_0061_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 61)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 61)) 0 6 (by decide +kernel)
theorem block_0061 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 61)) 0 6 :=
  check_0061_0000
theorem check_0062_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 62)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 62)) 0 1 (by decide +kernel)
theorem block_0062 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 62)) 0 1 :=
  check_0062_0000
theorem check_0063_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 63)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 63)) 0 1 (by decide +kernel)
theorem block_0063 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 63)) 0 1 :=
  check_0063_0000
end Papers.RationalityTen.RootedCanonical.RootedSixExtra04.S5T0

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra04.S5T0
theorem check_0064_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 64)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 64)) 0 1 (by decide +kernel)
theorem block_0064 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 64)) 0 1 :=
  check_0064_0000
theorem check_0065_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 65)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 65)) 0 1 (by decide +kernel)
theorem block_0065 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 65)) 0 1 :=
  check_0065_0000
theorem check_0066_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 66)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 66)) 0 1 (by decide +kernel)
theorem block_0066 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 66)) 0 1 :=
  check_0066_0000
theorem check_0067_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 67)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 67)) 0 1 (by decide +kernel)
theorem block_0067 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 67)) 0 1 :=
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
theorem check_0120_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 120)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 120)) 0 1 (by decide +kernel)
theorem block_0120 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 120)) 0 1 :=
  check_0120_0000
theorem check_0121_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 121)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 121)) 0 1 (by decide +kernel)
theorem block_0121 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 121)) 0 1 :=
  check_0121_0000
theorem check_0122_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 122)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 122)) 0 1 (by decide +kernel)
theorem block_0122 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 122)) 0 1 :=
  check_0122_0000
theorem check_0123_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 123)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 123)) 0 1 (by decide +kernel)
theorem block_0123 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 123)) 0 1 :=
  check_0123_0000
theorem check_0124_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 124)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 124)) 0 1 (by decide +kernel)
theorem block_0124 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 124)) 0 1 :=
  check_0124_0000
theorem check_0125_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 125)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 125)) 0 1 (by decide +kernel)
theorem block_0125 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 125)) 0 1 :=
  check_0125_0000
theorem check_0126_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 126)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 126)) 0 2 (by decide +kernel)
theorem block_0126 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 126)) 0 2 :=
  check_0126_0000
theorem check_0127_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 127)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 127)) 0 2 (by decide +kernel)
theorem block_0127 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 127)) 0 2 :=
  check_0127_0000
end Papers.RationalityTen.RootedCanonical.RootedSixExtra04.S5T0

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra04.S5T0
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
theorem check_0158_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 158)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 158)) 0 2 (by decide +kernel)
theorem block_0158 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 158)) 0 2 :=
  check_0158_0000
theorem check_0159_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 159)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 159)) 0 2 (by decide +kernel)
theorem block_0159 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 159)) 0 2 :=
  check_0159_0000
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
theorem check_0170_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 170)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 170)) 0 6 (by decide +kernel)
theorem block_0170 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 170)) 0 6 :=
  check_0170_0000
theorem check_0171_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 171)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 171)) 0 6 (by decide +kernel)
theorem block_0171 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 171)) 0 6 :=
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
theorem check_0180_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 180)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 180)) 0 6 (by decide +kernel)
theorem block_0180 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 180)) 0 6 :=
  check_0180_0000
theorem check_0181_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 181)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 181)) 0 6 (by decide +kernel)
theorem block_0181 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 181)) 0 6 :=
  check_0181_0000
theorem check_0182_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 182)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 182)) 0 6 (by decide +kernel)
theorem block_0182 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 182)) 0 6 :=
  check_0182_0000
theorem check_0183_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 183)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 183)) 0 6 (by decide +kernel)
theorem block_0183 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 183)) 0 6 :=
  check_0183_0000
theorem check_0184_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 184)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 184)) 0 6 (by decide +kernel)
theorem block_0184 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 184)) 0 6 :=
  check_0184_0000
theorem check_0185_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 185)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 185)) 0 6 (by decide +kernel)
theorem block_0185 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 185)) 0 6 :=
  check_0185_0000
end Papers.RationalityTen.RootedCanonical.RootedSixExtra04.S5T0

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra04.S5T0
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
theorem metadata_validity_0176 : FiniteChecks.Interval validity 176 186 :=
  FiniteChecks.interval_of_check validity 176 10 (by decide +kernel)
theorem metadata_validity : FiniteChecks.Interval validity 0 blockCount :=
  (FiniteChecks.interval_append (validity) 0 96 186
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
  (FiniteChecks.interval_append (validity) 96 144 186
  (FiniteChecks.interval_append (validity) 96 112 144
  metadata_validity_0096
  (FiniteChecks.interval_append (validity) 112 128 144
  metadata_validity_0112
  metadata_validity_0128))
  (FiniteChecks.interval_append (validity) 144 160 186
  metadata_validity_0144
  (FiniteChecks.interval_append (validity) 160 176 186
  metadata_validity_0160
  metadata_validity_0176))))
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
theorem metadata_symmetry_0176 : FiniteChecks.Interval symmetry 176 186 :=
  FiniteChecks.interval_of_check symmetry 176 10 (by decide +kernel)
theorem metadata_symmetry : FiniteChecks.Interval symmetry 0 blockCount :=
  (FiniteChecks.interval_append (symmetry) 0 96 186
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
  (FiniteChecks.interval_append (symmetry) 96 144 186
  (FiniteChecks.interval_append (symmetry) 96 112 144
  metadata_symmetry_0096
  (FiniteChecks.interval_append (symmetry) 112 128 144
  metadata_symmetry_0112
  metadata_symmetry_0128))
  (FiniteChecks.interval_append (symmetry) 144 160 186
  metadata_symmetry_0144
  (FiniteChecks.interval_append (symmetry) 160 176 186
  metadata_symmetry_0160
  metadata_symmetry_0176))))
theorem metadata_normalizers :
    RawFaceNormalizers.completeCheck 5 template root raw faceWitness = true := by decide +kernel
theorem metadata_root : RawFacetEmbedding.wellFormedCheck root = true := by decide +kernel
end Papers.RationalityTen.RootedCanonical.RootedSixExtra04.S5T0

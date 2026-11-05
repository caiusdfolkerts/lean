module
prelude
public import RootedSixBase01
public import RawKindedFacePlacement
public import RootedSixBase01OutsideData
public import RawOutsidePlacement

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase01.T2
open ConcreteGrowth
abbrev blockCount : Nat := 180
noncomputable def template : Cell := ⟨8, 63, [3, 5, 6, 9, 10, 17, 20, 24, 34, 36, 40, 48], [7, 11, 21, 25, 38, 42, 52, 56]⟩
noncomputable def root : Cell := FacetUniverses.RootedSixBase01.cells 0
noncomputable def records : Table (RawFacePlacement.Block × Nat) :=
(.branch 90
 (.branch 45
 (.branch 22
 (.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf (⟨2, 4, 5517840, 5517840, 361626105360, 361626105360⟩, 944191558))
 (.leaf (⟨2, 4, 5517840, 5517840, 361609328160, 361626104160⟩, 944978002)))
 (.branch 3
 (.leaf (⟨2, 4, 5517840, 5517840, 361592550945, 361626104070⟩, 945764446))
 (.branch 4
 (.leaf (⟨2, 4, 5517840, 5517840, 361340892720, 361626081120⟩, 948123778))
 (.leaf (⟨2, 4, 5517840, 5517840, 361324115505, 361626081030⟩, 948910222)))))
 (.branch 8
 (.branch 6
 (.leaf (⟨2, 4, 5517840, 5517840, 361055680050, 361626079350⟩, 951269554))
 (.branch 7
 (.leaf (⟨2, 4, 5517840, 5517840, 357029148225, 361625650950⟩, 953628886))
 (.leaf (⟨2, 4, 5517840, 5517840, 356760712770, 361625649270⟩, 954415330))))
 (.branch 9
 (.leaf (⟨2, 4, 5517840, 5517840, 288041236050, 361617784950⟩, 956774662))
 (.branch 10
 (.leaf (⟨2, 4, 5517840, 5517840, 283746268755, 361617754230⟩, 957561106))
 (.leaf (⟨2, 4, 5517840, 5517840, 215026792020, 361617201270⟩, 959920438))))))
 (.branch 16
 (.branch 13
 (.branch 12
 (.leaf (⟨2, 4, 5517600, 5517600, 361626105360, 361626105360⟩, 944322632))
 (.leaf (⟨2, 4, 5517600, 5517600, 361609328160, 361626104160⟩, 945109076)))
 (.branch 14
 (.leaf (⟨2, 4, 5517600, 5517600, 361592550945, 361626104070⟩, 945895520))
 (.branch 15
 (.leaf (⟨2, 4, 5517600, 5517600, 361340892720, 361626081120⟩, 948254852))
 (.leaf (⟨2, 4, 5517600, 5517600, 361324115505, 361626081030⟩, 949041296)))))
 (.branch 19
 (.branch 17
 (.leaf (⟨2, 4, 5517600, 5517600, 361055680050, 361626079350⟩, 951400628))
 (.branch 18
 (.leaf (⟨2, 4, 5517600, 5517600, 357029148225, 361625650950⟩, 953759960))
 (.leaf (⟨2, 4, 5517600, 5517600, 356760712770, 361625649270⟩, 954546404))))
 (.branch 20
 (.leaf (⟨2, 4, 5517600, 5517600, 288041236050, 361617784950⟩, 956905736))
 (.branch 21
 (.leaf (⟨2, 4, 5517600, 5517600, 283746268755, 361617754230⟩, 957692180))
 (.leaf (⟨2, 4, 5517600, 5517600, 215026792020, 361617201270⟩, 960051512)))))))
 (.branch 33
 (.branch 27
 (.branch 24
 (.branch 23
 (.leaf (⟨2, 4, 5517345, 5517570, 361626105360, 361626105360⟩, 944453706))
 (.leaf (⟨2, 4, 5517345, 5517570, 361609328160, 361626104160⟩, 945240150)))
 (.branch 25
 (.leaf (⟨2, 4, 5517345, 5517570, 361592550945, 361626104070⟩, 946026594))
 (.branch 26
 (.leaf (⟨2, 4, 5517345, 5517570, 361340892720, 361626081120⟩, 948385926))
 (.leaf (⟨2, 4, 5517345, 5517570, 361324115505, 361626081030⟩, 949172370)))))
 (.branch 30
 (.branch 28
 (.leaf (⟨2, 4, 5517345, 5517570, 361055680050, 361626079350⟩, 951531702))
 (.branch 29
 (.leaf (⟨2, 4, 5517345, 5517570, 357029148225, 361625650950⟩, 953891034))
 (.leaf (⟨2, 4, 5517345, 5517570, 356760712770, 361625649270⟩, 954677478))))
 (.branch 31
 (.leaf (⟨2, 4, 5517345, 5517570, 288041236050, 361617784950⟩, 957036810))
 (.branch 32
 (.leaf (⟨2, 4, 5517345, 5517570, 283746268755, 361617754230⟩, 957823254))
 (.leaf (⟨2, 4, 5517345, 5517570, 215026792020, 361617201270⟩, 960182586))))))
 (.branch 39
 (.branch 36
 (.branch 34
 (.leaf (⟨3, 4, 5517840, 5517840, 361742426640, 434925761040⟩, 17465617783256379031106041962))
 (.branch 35
 (.leaf (⟨3, 4, 5517840, 5517840, 361473991440, 434925741840⟩, 17523647108055107774594103450))
 (.leaf (⟨3, 4, 5517840, 5517840, 361205556000, 434925740400⟩, 17567169101654154332210149566))))
 (.branch 37
 (.leaf (⟨3, 4, 5517840, 5517840, 356642153505, 434925371655⟩, 17625198426452883075698211054))
 (.branch 38
 (.leaf (⟨3, 4, 5517840, 5517840, 279332742450, 434918461575⟩, 17683227751251611819186272542))
 (.leaf (⟨3, 4, 5517840, 5517840, 210613265730, 434917970055⟩, 17726749744850658376802318658)))))
 (.branch 42
 (.branch 40
 (.leaf (⟨2, 4, 5513520, 5509920, 361626105360, 361626105360⟩, 944322632))
 (.branch 41
 (.leaf (⟨2, 4, 5513520, 5509920, 361609328160, 361626104160⟩, 945109076))
 (.leaf (⟨2, 4, 5513520, 5509920, 361592550945, 361626104070⟩, 945895520))))
 (.branch 43
 (.leaf (⟨2, 4, 5513520, 5509920, 361340892720, 361626081120⟩, 948254852))
 (.branch 44
 (.leaf (⟨2, 4, 5513520, 5509920, 361324115505, 361626081030⟩, 949041296))
 (.leaf (⟨2, 4, 5513520, 5509920, 361055680050, 361626079350⟩, 951400628))))))))
 (.branch 67
 (.branch 56
 (.branch 50
 (.branch 47
 (.branch 46
 (.leaf (⟨2, 4, 5513520, 5509920, 357029148225, 361625650950⟩, 953759960))
 (.leaf (⟨2, 4, 5513520, 5509920, 356760712770, 361625649270⟩, 954546404)))
 (.branch 48
 (.leaf (⟨2, 4, 5513520, 5509920, 288041236050, 361617784950⟩, 956905736))
 (.branch 49
 (.leaf (⟨2, 4, 5513520, 5509920, 283746268755, 361617754230⟩, 957692180))
 (.leaf (⟨2, 4, 5513520, 5509920, 215026792020, 361617201270⟩, 960051512)))))
 (.branch 53
 (.branch 51
 (.leaf (⟨2, 4, 5513265, 5509890, 361626105360, 361626105360⟩, 944453706))
 (.branch 52
 (.leaf (⟨2, 4, 5513265, 5509890, 361609328160, 361626104160⟩, 945240150))
 (.leaf (⟨2, 4, 5513265, 5509890, 361592550945, 361626104070⟩, 946026594))))
 (.branch 54
 (.leaf (⟨2, 4, 5513265, 5509890, 361340892720, 361626081120⟩, 948385926))
 (.branch 55
 (.leaf (⟨2, 4, 5513265, 5509890, 361324115505, 361626081030⟩, 949172370))
 (.leaf (⟨2, 4, 5513265, 5509890, 361055680050, 361626079350⟩, 951531702))))))
 (.branch 61
 (.branch 58
 (.branch 57
 (.leaf (⟨2, 4, 5513265, 5509890, 357029148225, 361625650950⟩, 953891034))
 (.leaf (⟨2, 4, 5513265, 5509890, 356760712770, 361625649270⟩, 954677478)))
 (.branch 59
 (.leaf (⟨2, 4, 5513265, 5509890, 288041236050, 361617784950⟩, 957036810))
 (.branch 60
 (.leaf (⟨2, 4, 5513265, 5509890, 283746268755, 361617754230⟩, 957823254))
 (.leaf (⟨2, 4, 5513265, 5509890, 215026792020, 361617201270⟩, 960182586)))))
 (.branch 64
 (.branch 62
 (.leaf (⟨3, 4, 5514000, 5514000, 361742426640, 434925761040⟩, 17465617783256379031106041962))
 (.branch 63
 (.leaf (⟨3, 4, 5514000, 5514000, 361473991440, 434925741840⟩, 17523647108055107774594103450))
 (.leaf (⟨3, 4, 5514000, 5514000, 361205556000, 434925740400⟩, 17567169101654154332210149566))))
 (.branch 65
 (.leaf (⟨3, 4, 5514000, 5514000, 356642153505, 434925371655⟩, 17625198426452883075698211054))
 (.branch 66
 (.leaf (⟨3, 4, 5514000, 5514000, 279332742450, 434918461575⟩, 17683227751251611819186272542))
 (.leaf (⟨3, 4, 5514000, 5514000, 210613265730, 434917970055⟩, 17726749744850658376802318658)))))))
 (.branch 78
 (.branch 72
 (.branch 69
 (.branch 68
 (.leaf (⟨2, 4, 5448000, 5325600, 361626105360, 361626105360⟩, 944584780))
 (.leaf (⟨2, 4, 5448000, 5325600, 361609328160, 361626104160⟩, 945371224)))
 (.branch 70
 (.leaf (⟨2, 4, 5448000, 5325600, 361592550945, 361626104070⟩, 946157668))
 (.branch 71
 (.leaf (⟨2, 4, 5448000, 5325600, 361340892720, 361626081120⟩, 948517000))
 (.leaf (⟨2, 4, 5448000, 5325600, 361324115505, 361626081030⟩, 949303444)))))
 (.branch 75
 (.branch 73
 (.leaf (⟨2, 4, 5448000, 5325600, 361055680050, 361626079350⟩, 951662776))
 (.branch 74
 (.leaf (⟨2, 4, 5448000, 5325600, 357029148225, 361625650950⟩, 954022108))
 (.leaf (⟨2, 4, 5448000, 5325600, 356760712770, 361625649270⟩, 954808552))))
 (.branch 76
 (.leaf (⟨2, 4, 5448000, 5325600, 288041236050, 361617784950⟩, 957167884))
 (.branch 77
 (.leaf (⟨2, 4, 5448000, 5325600, 283746268755, 361617754230⟩, 957954328))
 (.leaf (⟨2, 4, 5448000, 5325600, 215026792020, 361617201270⟩, 960313660))))))
 (.branch 84
 (.branch 81
 (.branch 79
 (.leaf (⟨2, 4, 5443650, 5324850, 361626105360, 361626105360⟩, 944453706))
 (.branch 80
 (.leaf (⟨2, 4, 5443650, 5324850, 361609328160, 361626104160⟩, 945240150))
 (.leaf (⟨2, 4, 5443650, 5324850, 361592550945, 361626104070⟩, 946026594))))
 (.branch 82
 (.leaf (⟨2, 4, 5443650, 5324850, 361340892720, 361626081120⟩, 948385926))
 (.branch 83
 (.leaf (⟨2, 4, 5443650, 5324850, 361324115505, 361626081030⟩, 949172370))
 (.leaf (⟨2, 4, 5443650, 5324850, 361055680050, 361626079350⟩, 951531702)))))
 (.branch 87
 (.branch 85
 (.leaf (⟨2, 4, 5443650, 5324850, 357029148225, 361625650950⟩, 953891034))
 (.branch 86
 (.leaf (⟨2, 4, 5443650, 5324850, 356760712770, 361625649270⟩, 954677478))
 (.leaf (⟨2, 4, 5443650, 5324850, 288041236050, 361617784950⟩, 957036810))))
 (.branch 88
 (.leaf (⟨2, 4, 5443650, 5324850, 283746268755, 361617754230⟩, 957823254))
 (.branch 89
 (.leaf (⟨2, 4, 5443650, 5324850, 215026792020, 361617201270⟩, 960182586))
 (.leaf (⟨3, 4, 5444640, 5390640, 361742426640, 434925761040⟩, 17465617783256379031106041962)))))))))
 (.branch 135
 (.branch 112
 (.branch 101
 (.branch 95
 (.branch 92
 (.branch 91
 (.leaf (⟨3, 4, 5444640, 5390640, 361473991440, 434925741840⟩, 17523647108055107774594103450))
 (.leaf (⟨3, 4, 5444640, 5390640, 361205556000, 434925740400⟩, 17567169101654154332210149566)))
 (.branch 93
 (.leaf (⟨3, 4, 5444640, 5390640, 356642153505, 434925371655⟩, 17625198426452883075698211054))
 (.branch 94
 (.leaf (⟨3, 4, 5444640, 5390640, 279332742450, 434918461575⟩, 17683227751251611819186272542))
 (.leaf (⟨3, 4, 5444640, 5390640, 210613265730, 434917970055⟩, 17726749744850658376802318658)))))
 (.branch 98
 (.branch 96
 (.leaf (⟨2, 4, 5378115, 5309490, 361626105360, 361626105360⟩, 944453706))
 (.branch 97
 (.leaf (⟨2, 4, 5378115, 5309490, 361609328160, 361626104160⟩, 945240150))
 (.leaf (⟨2, 4, 5378115, 5309490, 361592550945, 361626104070⟩, 946026594))))
 (.branch 99
 (.leaf (⟨2, 4, 5378115, 5309490, 361340892720, 361626081120⟩, 948385926))
 (.branch 100
 (.leaf (⟨2, 4, 5378115, 5309490, 361324115505, 361626081030⟩, 949172370))
 (.leaf (⟨2, 4, 5378115, 5309490, 361055680050, 361626079350⟩, 951531702))))))
 (.branch 106
 (.branch 103
 (.branch 102
 (.leaf (⟨2, 4, 5378115, 5309490, 357029148225, 361625650950⟩, 953891034))
 (.leaf (⟨2, 4, 5378115, 5309490, 356760712770, 361625649270⟩, 954677478)))
 (.branch 104
 (.leaf (⟨2, 4, 5378115, 5309490, 288041236050, 361617784950⟩, 957036810))
 (.branch 105
 (.leaf (⟨2, 4, 5378115, 5309490, 283746268755, 361617754230⟩, 957823254))
 (.leaf (⟨2, 4, 5378115, 5309490, 215026792020, 361617201270⟩, 960182586)))))
 (.branch 109
 (.branch 107
 (.leaf (⟨3, 4, 5379120, 5379120, 361742426640, 434925761040⟩, 17465617783256379031106041962))
 (.branch 108
 (.leaf (⟨3, 4, 5379120, 5379120, 361473991440, 434925741840⟩, 17523647108055107774594103450))
 (.leaf (⟨3, 4, 5379120, 5379120, 361205556000, 434925740400⟩, 17567169101654154332210149566))))
 (.branch 110
 (.leaf (⟨3, 4, 5379120, 5379120, 356642153505, 434925371655⟩, 17625198426452883075698211054))
 (.branch 111
 (.leaf (⟨3, 4, 5379120, 5379120, 279332742450, 434918461575⟩, 17683227751251611819186272542))
 (.leaf (⟨3, 4, 5379120, 5379120, 210613265730, 434917970055⟩, 17726749744850658376802318658)))))))
 (.branch 123
 (.branch 117
 (.branch 114
 (.branch 113
 (.leaf (⟨2, 4, 4399185, 1393410, 361626105360, 361626105360⟩, 944584780))
 (.leaf (⟨2, 4, 4399185, 1393410, 361609328160, 361626104160⟩, 945371224)))
 (.branch 115
 (.leaf (⟨2, 4, 4399185, 1393410, 361592550945, 361626104070⟩, 946157668))
 (.branch 116
 (.leaf (⟨2, 4, 4399185, 1393410, 361340892720, 361626081120⟩, 948517000))
 (.leaf (⟨2, 4, 4399185, 1393410, 361324115505, 361626081030⟩, 949303444)))))
 (.branch 120
 (.branch 118
 (.leaf (⟨2, 4, 4399185, 1393410, 361055680050, 361626079350⟩, 951662776))
 (.branch 119
 (.leaf (⟨2, 4, 4399185, 1393410, 357029148225, 361625650950⟩, 954022108))
 (.leaf (⟨2, 4, 4399185, 1393410, 356760712770, 361625649270⟩, 954808552))))
 (.branch 121
 (.leaf (⟨2, 4, 4399185, 1393410, 288041236050, 361617784950⟩, 957167884))
 (.branch 122
 (.leaf (⟨2, 4, 4399185, 1393410, 283746268755, 361617754230⟩, 957954328))
 (.leaf (⟨2, 4, 4399185, 1393410, 215026792020, 361617201270⟩, 960313660))))))
 (.branch 129
 (.branch 126
 (.branch 124
 (.leaf (⟨2, 4, 4395090, 1392690, 361626105360, 361626105360⟩, 944715854))
 (.branch 125
 (.leaf (⟨2, 4, 4395090, 1392690, 361609328160, 361626104160⟩, 945502298))
 (.leaf (⟨2, 4, 4395090, 1392690, 361592550945, 361626104070⟩, 946288742))))
 (.branch 127
 (.leaf (⟨2, 4, 4395090, 1392690, 361340892720, 361626081120⟩, 948648074))
 (.branch 128
 (.leaf (⟨2, 4, 4395090, 1392690, 361324115505, 361626081030⟩, 949434518))
 (.leaf (⟨2, 4, 4395090, 1392690, 361055680050, 361626079350⟩, 951793850)))))
 (.branch 132
 (.branch 130
 (.leaf (⟨2, 4, 4395090, 1392690, 357029148225, 361625650950⟩, 954153182))
 (.branch 131
 (.leaf (⟨2, 4, 4395090, 1392690, 356760712770, 361625649270⟩, 954939626))
 (.leaf (⟨2, 4, 4395090, 1392690, 288041236050, 361617784950⟩, 957298958))))
 (.branch 133
 (.leaf (⟨2, 4, 4395090, 1392690, 283746268755, 361617754230⟩, 958085402))
 (.branch 134
 (.leaf (⟨2, 4, 4395090, 1392690, 215026792020, 361617201270⟩, 960444734))
 (.leaf (⟨3, 4, 4392225, 2441475, 361742426640, 434925761040⟩, 17465617783256379031106041962))))))))
 (.branch 157
 (.branch 146
 (.branch 140
 (.branch 137
 (.branch 136
 (.leaf (⟨3, 4, 4392225, 2441475, 361473991440, 434925741840⟩, 17523647108055107774594103450))
 (.leaf (⟨3, 4, 4392225, 2441475, 361205556000, 434925740400⟩, 17567169101654154332210149566)))
 (.branch 138
 (.leaf (⟨3, 4, 4392225, 2441475, 356642153505, 434925371655⟩, 17625198426452883075698211054))
 (.branch 139
 (.leaf (⟨3, 4, 4392225, 2441475, 279332742450, 434918461575⟩, 17683227751251611819186272542))
 (.leaf (⟨3, 4, 4392225, 2441475, 210613265730, 434917970055⟩, 17726749744850658376802318658)))))
 (.branch 143
 (.branch 141
 (.leaf (⟨2, 4, 4329555, 1377330, 361626105360, 361626105360⟩, 944715854))
 (.branch 142
 (.leaf (⟨2, 4, 4329555, 1377330, 361609328160, 361626104160⟩, 945502298))
 (.leaf (⟨2, 4, 4329555, 1377330, 361592550945, 361626104070⟩, 946288742))))
 (.branch 144
 (.leaf (⟨2, 4, 4329555, 1377330, 361340892720, 361626081120⟩, 948648074))
 (.branch 145
 (.leaf (⟨2, 4, 4329555, 1377330, 361324115505, 361626081030⟩, 949434518))
 (.leaf (⟨2, 4, 4329555, 1377330, 361055680050, 361626079350⟩, 951793850))))))
 (.branch 151
 (.branch 148
 (.branch 147
 (.leaf (⟨2, 4, 4329555, 1377330, 357029148225, 361625650950⟩, 954153182))
 (.leaf (⟨2, 4, 4329555, 1377330, 356760712770, 361625649270⟩, 954939626)))
 (.branch 149
 (.leaf (⟨2, 4, 4329555, 1377330, 288041236050, 361617784950⟩, 957298958))
 (.branch 150
 (.leaf (⟨2, 4, 4329555, 1377330, 283746268755, 361617754230⟩, 958085402))
 (.leaf (⟨2, 4, 4329555, 1377330, 215026792020, 361617201270⟩, 960444734)))))
 (.branch 154
 (.branch 152
 (.leaf (⟨3, 4, 4326705, 2429955, 361742426640, 434925761040⟩, 17465617783256379031106041962))
 (.branch 153
 (.leaf (⟨3, 4, 4326705, 2429955, 361473991440, 434925741840⟩, 17523647108055107774594103450))
 (.leaf (⟨3, 4, 4326705, 2429955, 361205556000, 434925740400⟩, 17567169101654154332210149566))))
 (.branch 155
 (.leaf (⟨3, 4, 4326705, 2429955, 356642153505, 434925371655⟩, 17625198426452883075698211054))
 (.branch 156
 (.leaf (⟨3, 4, 4326705, 2429955, 279332742450, 434918461575⟩, 17683227751251611819186272542))
 (.leaf (⟨3, 4, 4326705, 2429955, 210613265730, 434917970055⟩, 17726749744850658376802318658)))))))
 (.branch 168
 (.branch 162
 (.branch 159
 (.branch 158
 (.leaf (⟨2, 4, 3280980, 1070130, 361626105360, 361626105360⟩, 944846928))
 (.leaf (⟨2, 4, 3280980, 1070130, 361609328160, 361626104160⟩, 945633372)))
 (.branch 160
 (.leaf (⟨2, 4, 3280980, 1070130, 361592550945, 361626104070⟩, 946419816))
 (.branch 161
 (.leaf (⟨2, 4, 3280980, 1070130, 361340892720, 361626081120⟩, 948779148))
 (.leaf (⟨2, 4, 3280980, 1070130, 361324115505, 361626081030⟩, 949565592)))))
 (.branch 165
 (.branch 163
 (.leaf (⟨2, 4, 3280980, 1070130, 361055680050, 361626079350⟩, 951924924))
 (.branch 164
 (.leaf (⟨2, 4, 3280980, 1070130, 357029148225, 361625650950⟩, 954284256))
 (.leaf (⟨2, 4, 3280980, 1070130, 356760712770, 361625649270⟩, 955070700))))
 (.branch 166
 (.leaf (⟨2, 4, 3280980, 1070130, 288041236050, 361617784950⟩, 957430032))
 (.branch 167
 (.leaf (⟨2, 4, 3280980, 1070130, 283746268755, 361617754230⟩, 958216476))
 (.leaf (⟨2, 4, 3280980, 1070130, 215026792020, 361617201270⟩, 960575808))))))
 (.branch 174
 (.branch 171
 (.branch 169
 (.leaf (⟨3, 4, 3212610, 2183235, 361742426640, 434925761040⟩, 17465617783256379031106041962))
 (.branch 170
 (.leaf (⟨3, 4, 3212610, 2183235, 361473991440, 434925741840⟩, 17523647108055107774594103450))
 (.leaf (⟨3, 4, 3212610, 2183235, 361205556000, 434925740400⟩, 17567169101654154332210149566))))
 (.branch 172
 (.leaf (⟨3, 4, 3212610, 2183235, 356642153505, 434925371655⟩, 17625198426452883075698211054))
 (.branch 173
 (.leaf (⟨3, 4, 3212610, 2183235, 279332742450, 434918461575⟩, 17683227751251611819186272542))
 (.leaf (⟨3, 4, 3212610, 2183235, 210613265730, 434917970055⟩, 17726749744850658376802318658)))))
 (.branch 177
 (.branch 175
 (.leaf (⟨3, 4, 2164035, 2164035, 361742426640, 434925761040⟩, 17465617783256379031106041962))
 (.branch 176
 (.leaf (⟨3, 4, 2164035, 2164035, 361473991440, 434925741840⟩, 17523647108055107774594103450))
 (.leaf (⟨3, 4, 2164035, 2164035, 361205556000, 434925740400⟩, 17567169101654154332210149566))))
 (.branch 178
 (.leaf (⟨3, 4, 2164035, 2164035, 356642153505, 434925371655⟩, 17625198426452883075698211054))
 (.branch 179
 (.leaf (⟨3, 4, 2164035, 2164035, 279332742450, 434918461575⟩, 17683227751251611819186272542))
 (.leaf (⟨3, 4, 2164035, 2164035, 210613265730, 434917970055⟩, 17726749744850658376802318658))))))))))
noncomputable def raw (i : Fin blockCount) : RawFacePlacement.Block := (records.get i.val).1
noncomputable def witness (i : Fin blockCount) (code : Nat) : Fin 15246 :=
  Fin.ofNat 15246 (Nat.land (Nat.shiftRight (records.get i.val).2 (16 * code)) 65535)
noncomputable def faceTable : Table Nat :=
(.branch 21515
 (.branch 9234
 (.branch 6147
 (.branch 5123
 (.branch 3084
 (.branch 3078
 (.branch 3077
 (.leaf 0)
 (.leaf 1))
 (.branch 3081
 (.leaf 2)
 (.branch 3082
 (.leaf 3)
 (.leaf 4))))
 (.branch 3108
 (.branch 3090
 (.leaf 5)
 (.branch 3092
 (.leaf 6)
 (.leaf 7)))
 (.branch 3112
 (.leaf 8)
 (.branch 3120
 (.leaf 9)
 (.leaf 10)))))
 (.branch 5132
 (.branch 5126
 (.branch 5125
 (.leaf 11)
 (.leaf 12))
 (.branch 5129
 (.leaf 13)
 (.branch 5130
 (.leaf 14)
 (.leaf 15))))
 (.branch 5156
 (.branch 5138
 (.leaf 16)
 (.branch 5140
 (.leaf 17)
 (.leaf 18)))
 (.branch 5160
 (.leaf 19)
 (.branch 5168
 (.leaf 20)
 (.leaf 21))))))
 (.branch 7175
 (.branch 6156
 (.branch 6150
 (.branch 6149
 (.leaf 22)
 (.leaf 23))
 (.branch 6153
 (.leaf 24)
 (.branch 6154
 (.leaf 25)
 (.leaf 26))))
 (.branch 6180
 (.branch 6162
 (.leaf 27)
 (.branch 6164
 (.leaf 28)
 (.leaf 29)))
 (.branch 6184
 (.leaf 30)
 (.branch 6192
 (.leaf 31)
 (.leaf 32)))))
 (.branch 9219
 (.branch 7190
 (.branch 7179
 (.leaf 33)
 (.branch 7181
 (.leaf 34)
 (.leaf 35)))
 (.branch 7212
 (.leaf 36)
 (.branch 7220
 (.leaf 37)
 (.leaf 38))))
 (.branch 9225
 (.branch 9221
 (.leaf 39)
 (.branch 9222
 (.leaf 40)
 (.leaf 41)))
 (.branch 9226
 (.leaf 42)
 (.branch 9228
 (.leaf 43)
 (.leaf 44)))))))
 (.branch 17411
 (.branch 10258
 (.branch 10243
 (.branch 9252
 (.branch 9236
 (.leaf 45)
 (.leaf 46))
 (.branch 9256
 (.leaf 47)
 (.branch 9264
 (.leaf 48)
 (.leaf 49))))
 (.branch 10249
 (.branch 10245
 (.leaf 50)
 (.branch 10246
 (.leaf 51)
 (.leaf 52)))
 (.branch 10250
 (.leaf 53)
 (.branch 10252
 (.leaf 54)
 (.leaf 55)))))
 (.branch 11271
 (.branch 10276
 (.branch 10260
 (.leaf 56)
 (.leaf 57))
 (.branch 10280
 (.leaf 58)
 (.branch 10288
 (.leaf 59)
 (.leaf 60))))
 (.branch 11286
 (.branch 11275
 (.leaf 61)
 (.branch 11277
 (.leaf 62)
 (.leaf 63)))
 (.branch 11308
 (.leaf 64)
 (.branch 11316
 (.leaf 65)
 (.leaf 66))))))
 (.branch 20483
 (.branch 17420
 (.branch 17414
 (.branch 17413
 (.leaf 67)
 (.leaf 68))
 (.branch 17417
 (.leaf 69)
 (.branch 17418
 (.leaf 70)
 (.leaf 71))))
 (.branch 17444
 (.branch 17426
 (.leaf 72)
 (.branch 17428
 (.leaf 73)
 (.leaf 74)))
 (.branch 17448
 (.leaf 75)
 (.branch 17456
 (.leaf 76)
 (.leaf 77)))))
 (.branch 20498
 (.branch 20489
 (.branch 20485
 (.leaf 78)
 (.branch 20486
 (.leaf 79)
 (.leaf 80)))
 (.branch 20490
 (.leaf 81)
 (.branch 20492
 (.leaf 82)
 (.leaf 83))))
 (.branch 20520
 (.branch 20500
 (.leaf 84)
 (.branch 20516
 (.leaf 85)
 (.leaf 86)))
 (.branch 20528
 (.leaf 87)
 (.branch 21511
 (.leaf 88)
 (.leaf 89))))))))
 (.branch 38923
 (.branch 34819
 (.branch 24594
 (.branch 24579
 (.branch 21526
 (.branch 21517
 (.leaf 90)
 (.leaf 91))
 (.branch 21548
 (.leaf 92)
 (.branch 21556
 (.leaf 93)
 (.leaf 94))))
 (.branch 24585
 (.branch 24581
 (.leaf 95)
 (.branch 24582
 (.leaf 96)
 (.leaf 97)))
 (.branch 24586
 (.leaf 98)
 (.branch 24588
 (.leaf 99)
 (.leaf 100)))))
 (.branch 25607
 (.branch 24612
 (.branch 24596
 (.leaf 101)
 (.leaf 102))
 (.branch 24616
 (.leaf 103)
 (.branch 24624
 (.leaf 104)
 (.leaf 105))))
 (.branch 25622
 (.branch 25611
 (.leaf 106)
 (.branch 25613
 (.leaf 107)
 (.leaf 108)))
 (.branch 25644
 (.leaf 109)
 (.branch 25652
 (.leaf 110)
 (.leaf 111))))))
 (.branch 36867
 (.branch 34828
 (.branch 34822
 (.branch 34821
 (.leaf 112)
 (.leaf 113))
 (.branch 34825
 (.leaf 114)
 (.branch 34826
 (.leaf 115)
 (.leaf 116))))
 (.branch 34852
 (.branch 34834
 (.leaf 117)
 (.branch 34836
 (.leaf 118)
 (.leaf 119)))
 (.branch 34856
 (.leaf 120)
 (.branch 34864
 (.leaf 121)
 (.leaf 122)))))
 (.branch 36882
 (.branch 36873
 (.branch 36869
 (.leaf 123)
 (.branch 36870
 (.leaf 124)
 (.leaf 125)))
 (.branch 36874
 (.leaf 126)
 (.branch 36876
 (.leaf 127)
 (.leaf 128))))
 (.branch 36904
 (.branch 36884
 (.leaf 129)
 (.branch 36900
 (.leaf 130)
 (.leaf 131)))
 (.branch 36912
 (.leaf 132)
 (.branch 38919
 (.leaf 133)
 (.leaf 134)))))))
 (.branch 49155
 (.branch 40978
 (.branch 40963
 (.branch 38934
 (.branch 38925
 (.leaf 135)
 (.leaf 136))
 (.branch 38956
 (.leaf 137)
 (.branch 38964
 (.leaf 138)
 (.leaf 139))))
 (.branch 40969
 (.branch 40965
 (.leaf 140)
 (.branch 40966
 (.leaf 141)
 (.leaf 142)))
 (.branch 40970
 (.leaf 143)
 (.branch 40972
 (.leaf 144)
 (.leaf 145)))))
 (.branch 43015
 (.branch 40996
 (.branch 40980
 (.leaf 146)
 (.leaf 147))
 (.branch 41000
 (.leaf 148)
 (.branch 41008
 (.leaf 149)
 (.leaf 150))))
 (.branch 43030
 (.branch 43019
 (.leaf 151)
 (.branch 43021
 (.leaf 152)
 (.leaf 153)))
 (.branch 43052
 (.leaf 154)
 (.branch 43060
 (.leaf 155)
 (.leaf 156))))))
 (.branch 53255
 (.branch 49164
 (.branch 49158
 (.branch 49157
 (.leaf 157)
 (.leaf 158))
 (.branch 49161
 (.leaf 159)
 (.branch 49162
 (.leaf 160)
 (.leaf 161))))
 (.branch 49188
 (.branch 49170
 (.leaf 162)
 (.branch 49172
 (.leaf 163)
 (.leaf 164)))
 (.branch 49192
 (.leaf 165)
 (.branch 49200
 (.leaf 166)
 (.leaf 167)))))
 (.branch 57351
 (.branch 53270
 (.branch 53259
 (.leaf 168)
 (.branch 53261
 (.leaf 169)
 (.leaf 170)))
 (.branch 53292
 (.leaf 171)
 (.branch 53300
 (.leaf 172)
 (.leaf 173))))
 (.branch 57366
 (.branch 57355
 (.leaf 174)
 (.branch 57357
 (.leaf 175)
 (.leaf 176)))
 (.branch 57388
 (.leaf 177)
 (.branch 57396
 (.leaf 178)
 (.leaf 179)))))))))
noncomputable def faceWitness (s r : Nat) : Fin blockCount :=
  Fin.ofNat blockCount (faceTable.get (s * 1024 + r))
noncomputable def validity (i : Nat) : Bool :=
  RawFaceNormalizers.blockValidCheck 6 (raw (Fin.ofNat blockCount i))
noncomputable def placement (b : Fin blockCount) (code : Nat) : Bool :=
  RawKindedFacePlacement.check 6 (raw b) template root FacetUniverses.RootedSixBase01.cells
    code 0 (witness b code)
noncomputable def test (i : Nat) : Bool :=
  let b := Fin.ofNat blockCount i
  FiniteChecks.checkRange (placement b)
    0 (RawFacePlacement.count (raw b).shared (raw b).shared)
noncomputable def symmetry (i : Nat) : Bool :=
  RawOutsidePlacement.blockCheck FacetUniverses.RootedSixBase01.Outside.vertexCode root.vertices
    (raw (Fin.ofNat blockCount i))
end Papers.RationalityTen.RootedCanonical.RootedSixBase01.T2

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase01.T2
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
end Papers.RationalityTen.RootedCanonical.RootedSixBase01.T2

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase01.T2
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
end Papers.RationalityTen.RootedCanonical.RootedSixBase01.T2

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase01.T2
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
theorem check_0150_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 150)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 150)) 0 2 (by decide +kernel)
theorem block_0150 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 150)) 0 2 :=
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
theorem check_0168_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 168)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 168)) 0 6 (by decide +kernel)
theorem block_0168 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 168)) 0 6 :=
  check_0168_0000
theorem check_0169_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 169)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 169)) 0 6 (by decide +kernel)
theorem block_0169 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 169)) 0 6 :=
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
end Papers.RationalityTen.RootedCanonical.RootedSixBase01.T2

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase01.T2
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
theorem metadata_validity_0176 : FiniteChecks.Interval validity 176 180 :=
  FiniteChecks.interval_of_check validity 176 4 (by decide +kernel)
theorem metadata_validity : FiniteChecks.Interval validity 0 blockCount :=
  (FiniteChecks.interval_append (validity) 0 96 180
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
  (FiniteChecks.interval_append (validity) 96 144 180
  (FiniteChecks.interval_append (validity) 96 112 144
  metadata_validity_0096
  (FiniteChecks.interval_append (validity) 112 128 144
  metadata_validity_0112
  metadata_validity_0128))
  (FiniteChecks.interval_append (validity) 144 160 180
  metadata_validity_0144
  (FiniteChecks.interval_append (validity) 160 176 180
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
theorem metadata_symmetry_0176 : FiniteChecks.Interval symmetry 176 180 :=
  FiniteChecks.interval_of_check symmetry 176 4 (by decide +kernel)
theorem metadata_symmetry : FiniteChecks.Interval symmetry 0 blockCount :=
  (FiniteChecks.interval_append (symmetry) 0 96 180
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
  (FiniteChecks.interval_append (symmetry) 96 144 180
  (FiniteChecks.interval_append (symmetry) 96 112 144
  metadata_symmetry_0096
  (FiniteChecks.interval_append (symmetry) 112 128 144
  metadata_symmetry_0112
  metadata_symmetry_0128))
  (FiniteChecks.interval_append (symmetry) 144 160 180
  metadata_symmetry_0144
  (FiniteChecks.interval_append (symmetry) 160 176 180
  metadata_symmetry_0160
  metadata_symmetry_0176))))
theorem metadata_normalizers :
    RawFaceNormalizers.completeCheck 6 template root raw faceWitness = true := by decide +kernel
theorem metadata_root : RawFacetEmbedding.wellFormedCheck root = true := by decide +kernel
end Papers.RationalityTen.RootedCanonical.RootedSixBase01.T2

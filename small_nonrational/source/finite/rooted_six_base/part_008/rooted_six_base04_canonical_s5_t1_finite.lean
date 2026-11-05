module
prelude
public import RootedSixBase04
public import RawKindedFacePlacement
public import RootedSixBase04OutsideData
public import RawOutsidePlacement

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase04.S5T1
open ConcreteGrowth
abbrev blockCount : Nat := 158
noncomputable def template : Cell := ⟨3, 31, [3, 5, 6, 10, 12, 17, 20, 24], [7, 14, 21, 27, 28]⟩
noncomputable def root : Cell := FacetUniverses.RootedSixBase04.cells 0
noncomputable def records : Table (RawFacePlacement.Block × Nat) :=
(.branch 79
 (.branch 39
 (.branch 19
 (.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf (⟨1, 4, 274960, 274960, 361617786720, 288326448720⟩, 770))
 (.leaf (⟨1, 4, 274960, 274960, 361616738145, 288326448645⟩, 1191)))
 (.branch 3
 (.leaf (⟨1, 4, 274960, 274960, 361599960930, 288326447205⟩, 1456))
 (.leaf (⟨1, 4, 274960, 274960, 361331525475, 288326420325⟩, 1721))))
 (.branch 6
 (.branch 5
 (.leaf (⟨1, 4, 274960, 274960, 357036558180, 288325928805⟩, 1830))
 (.leaf (⟨1, 4, 274960, 274960, 288317081445, 288317081445⟩, 1855)))
 (.branch 7
 (.leaf (⟨1, 4, 274945, 274945, 361617786720, 288326448720⟩, 771))
 (.branch 8
 (.leaf (⟨1, 4, 274945, 274945, 361616738145, 288326448645⟩, 1192))
 (.leaf (⟨1, 4, 274945, 274945, 361599960930, 288326447205⟩, 1457))))))
 (.branch 14
 (.branch 11
 (.branch 10
 (.leaf (⟨1, 4, 274945, 274945, 361331525475, 288326420325⟩, 1722))
 (.leaf (⟨1, 4, 274945, 274945, 357036558180, 288325928805⟩, 1831)))
 (.branch 12
 (.leaf (⟨1, 4, 274945, 274945, 288317081445, 288317081445⟩, 1856))
 (.branch 13
 (.leaf (⟨2, 4, 274960, 274960, 361626105360, 361626105360⟩, 19005729))
 (.leaf (⟨2, 4, 274960, 274960, 361609328160, 361626104160⟩, 29229501)))))
 (.branch 16
 (.branch 15
 (.leaf (⟨2, 4, 274960, 274960, 361592550945, 361626104070⟩, 56820578))
 (.leaf (⟨2, 4, 274960, 274960, 361340892720, 361626081120⟩, 39453273)))
 (.branch 17
 (.leaf (⟨2, 4, 274960, 274960, 361324115505, 361626081030⟩, 67044350))
 (.branch 18
 (.leaf (⟨2, 4, 274960, 274960, 357045925440, 361625651040⟩, 44958381))
 (.leaf (⟨2, 4, 274960, 274960, 356760712770, 361625649270⟩, 84411655)))))))
 (.branch 29
 (.branch 24
 (.branch 21
 (.branch 20
 (.leaf (⟨2, 4, 274960, 274960, 352465745475, 361625618550⟩, 101778960))
 (.leaf (⟨2, 4, 274960, 274960, 288309671505, 361617786630⟩, 72549458)))
 (.branch 22
 (.leaf (⟨2, 4, 274960, 274960, 288041236050, 361617784950⟩, 89916763))
 (.branch 23
 (.leaf (⟨2, 4, 274960, 274960, 283746268755, 361617754230⟩, 107284068))
 (.leaf (⟨2, 4, 274960, 274960, 215026792020, 361617201270⟩, 114427601)))))
 (.branch 26
 (.branch 25
 (.leaf (⟨1, 4, 274690, 274465, 361617786720, 288326448720⟩, 764))
 (.leaf (⟨1, 4, 274690, 274465, 361616738145, 288326448645⟩, 1185)))
 (.branch 27
 (.leaf (⟨1, 4, 274690, 274465, 361599960930, 288326447205⟩, 1450))
 (.branch 28
 (.leaf (⟨1, 4, 274690, 274465, 361331525475, 288326420325⟩, 1715))
 (.leaf (⟨1, 4, 274690, 274465, 357036558180, 288325928805⟩, 1824))))))
 (.branch 34
 (.branch 31
 (.branch 30
 (.leaf (⟨1, 4, 274690, 274465, 288317081445, 288317081445⟩, 1849))
 (.leaf (⟨2, 4, 274720, 274720, 361626105360, 361626105360⟩, 18546974)))
 (.branch 32
 (.leaf (⟨2, 4, 274720, 274720, 361609328160, 361626104160⟩, 28770746))
 (.branch 33
 (.leaf (⟨2, 4, 274720, 274720, 361592550945, 361626104070⟩, 56361823))
 (.leaf (⟨2, 4, 274720, 274720, 361340892720, 361626081120⟩, 38994518)))))
 (.branch 36
 (.branch 35
 (.leaf (⟨2, 4, 274720, 274720, 361324115505, 361626081030⟩, 66585595))
 (.leaf (⟨2, 4, 274720, 274720, 357045925440, 361625651040⟩, 44499626)))
 (.branch 37
 (.leaf (⟨2, 4, 274720, 274720, 356760712770, 361625649270⟩, 83952900))
 (.branch 38
 (.leaf (⟨2, 4, 274720, 274720, 352465745475, 361625618550⟩, 101320205))
 (.leaf (⟨2, 4, 274720, 274720, 288309671505, 361617786630⟩, 72090703))))))))
 (.branch 59
 (.branch 49
 (.branch 44
 (.branch 41
 (.branch 40
 (.leaf (⟨2, 4, 274720, 274720, 288041236050, 361617784950⟩, 89458008))
 (.leaf (⟨2, 4, 274720, 274720, 283746268755, 361617754230⟩, 106825313)))
 (.branch 42
 (.leaf (⟨2, 4, 274720, 274720, 215026792020, 361617201270⟩, 113968846))
 (.branch 43
 (.leaf (⟨2, 4, 274465, 274690, 361626105360, 361626105360⟩, 18612511))
 (.leaf (⟨2, 4, 274465, 274690, 361609328160, 361626104160⟩, 28836283)))))
 (.branch 46
 (.branch 45
 (.leaf (⟨2, 4, 274465, 274690, 361592550945, 361626104070⟩, 56427360))
 (.leaf (⟨2, 4, 274465, 274690, 361340892720, 361626081120⟩, 39060055)))
 (.branch 47
 (.leaf (⟨2, 4, 274465, 274690, 361324115505, 361626081030⟩, 66651132))
 (.branch 48
 (.leaf (⟨2, 4, 274465, 274690, 357045925440, 361625651040⟩, 44565163))
 (.leaf (⟨2, 4, 274465, 274690, 356760712770, 361625649270⟩, 84018437))))))
 (.branch 54
 (.branch 51
 (.branch 50
 (.leaf (⟨2, 4, 274465, 274690, 352465745475, 361625618550⟩, 101385742))
 (.leaf (⟨2, 4, 274465, 274690, 288309671505, 361617786630⟩, 72156240)))
 (.branch 52
 (.leaf (⟨2, 4, 274465, 274690, 288041236050, 361617784950⟩, 89523545))
 (.branch 53
 (.leaf (⟨2, 4, 274465, 274690, 283746268755, 361617754230⟩, 106890850))
 (.leaf (⟨2, 4, 274465, 274690, 215026792020, 361617201270⟩, 114034383)))))
 (.branch 56
 (.branch 55
 (.leaf (⟨3, 4, 274960, 274960, 361742426640, 434925761040⟩, 165625346083242365229531276))
 (.leaf (⟨3, 4, 274960, 274960, 361473991440, 434925741840⟩, 252669333281335480461623508)))
 (.branch 57
 (.leaf (⟨3, 4, 274960, 274960, 356910588960, 434925371760⟩, 441264638877203896797823344))
 (.branch 58
 (.leaf (⟨3, 4, 274960, 274960, 352615621680, 434925344880⟩, 629859944473072313134023180))
 (.leaf (⟨3, 4, 274960, 274960, 287922677025, 434918490375⟩, 950230175132720584474362645)))))))
 (.branch 69
 (.branch 64
 (.branch 61
 (.branch 60
 (.leaf (⟨3, 4, 274960, 274960, 283627709745, 434918463495⟩, 1138825480728589000810562481))
 (.leaf (⟨3, 4, 274960, 274960, 210613265730, 434917970055⟩, 1459195711388237272150901946)))
 (.branch 62
 (.leaf (⟨3, 4, 274960, 274960, 141893788995, 434917935495⟩, 1779565942047885543491241411))
 (.branch 63
 (.leaf (⟨1, 4, 270595, 262945, 361617786720, 288326448720⟩, 775))
 (.leaf (⟨1, 4, 270595, 262945, 361616738145, 288326448645⟩, 1196)))))
 (.branch 66
 (.branch 65
 (.leaf (⟨1, 4, 270595, 262945, 361599960930, 288326447205⟩, 1461))
 (.leaf (⟨1, 4, 270595, 262945, 361331525475, 288326420325⟩, 1726)))
 (.branch 67
 (.leaf (⟨1, 4, 270595, 262945, 357036558180, 288325928805⟩, 1835))
 (.branch 68
 (.leaf (⟨1, 4, 270595, 262945, 288317081445, 288317081445⟩, 1860))
 (.leaf (⟨2, 4, 270385, 267010, 361626105360, 361626105360⟩, 19071268))))))
 (.branch 74
 (.branch 71
 (.branch 70
 (.leaf (⟨2, 4, 270385, 267010, 361609328160, 361626104160⟩, 29295040))
 (.leaf (⟨2, 4, 270385, 267010, 361592550945, 361626104070⟩, 56886117)))
 (.branch 72
 (.leaf (⟨2, 4, 270385, 267010, 361340892720, 361626081120⟩, 39518812))
 (.branch 73
 (.leaf (⟨2, 4, 270385, 267010, 361324115505, 361626081030⟩, 67109889))
 (.leaf (⟨2, 4, 270385, 267010, 357045925440, 361625651040⟩, 45023920)))))
 (.branch 76
 (.branch 75
 (.leaf (⟨2, 4, 270385, 267010, 356760712770, 361625649270⟩, 84477194))
 (.leaf (⟨2, 4, 270385, 267010, 352465745475, 361625618550⟩, 101844499)))
 (.branch 77
 (.leaf (⟨2, 4, 270385, 267010, 288309671505, 361617786630⟩, 72614997))
 (.branch 78
 (.leaf (⟨2, 4, 270385, 267010, 288041236050, 361617784950⟩, 89982302))
 (.leaf (⟨2, 4, 270385, 267010, 283746268755, 361617754230⟩, 107349607)))))))))
 (.branch 118
 (.branch 98
 (.branch 88
 (.branch 83
 (.branch 81
 (.branch 80
 (.leaf (⟨2, 4, 270385, 267010, 215026792020, 361617201270⟩, 114493140))
 (.leaf (⟨2, 4, 266290, 266290, 361626105360, 361626105360⟩, 18874653)))
 (.branch 82
 (.leaf (⟨2, 4, 266290, 266290, 361609328160, 361626104160⟩, 29098425))
 (.leaf (⟨2, 4, 266290, 266290, 361592550945, 361626104070⟩, 56689502))))
 (.branch 85
 (.branch 84
 (.leaf (⟨2, 4, 266290, 266290, 361340892720, 361626081120⟩, 39322197))
 (.leaf (⟨2, 4, 266290, 266290, 361324115505, 361626081030⟩, 66913274)))
 (.branch 86
 (.leaf (⟨2, 4, 266290, 266290, 357045925440, 361625651040⟩, 44827305))
 (.branch 87
 (.leaf (⟨2, 4, 266290, 266290, 356760712770, 361625649270⟩, 84280579))
 (.leaf (⟨2, 4, 266290, 266290, 352465745475, 361625618550⟩, 101647884))))))
 (.branch 93
 (.branch 90
 (.branch 89
 (.leaf (⟨2, 4, 266290, 266290, 288309671505, 361617786630⟩, 72418382))
 (.leaf (⟨2, 4, 266290, 266290, 288041236050, 361617784950⟩, 89785687)))
 (.branch 91
 (.leaf (⟨2, 4, 266290, 266290, 283746268755, 361617754230⟩, 107152992))
 (.branch 92
 (.leaf (⟨2, 4, 266290, 266290, 215026792020, 361617201270⟩, 114296525))
 (.leaf (⟨3, 4, 262945, 270595, 361742426640, 434925761040⟩, 166834345690677701287411851)))))
 (.branch 95
 (.branch 94
 (.leaf (⟨3, 4, 262945, 270595, 361473991440, 434925741840⟩, 253878332888770816519504083))
 (.leaf (⟨3, 4, 262945, 270595, 356910588960, 434925371760⟩, 442473638484639232855703919)))
 (.branch 96
 (.leaf (⟨3, 4, 262945, 270595, 352615621680, 434925344880⟩, 631068944080507649191903755))
 (.branch 97
 (.leaf (⟨3, 4, 262945, 270595, 287922677025, 434918490375⟩, 951439174740155920532243220))
 (.leaf (⟨3, 4, 262945, 270595, 283627709745, 434918463495⟩, 1140034480336024336868443056)))))))
 (.branch 108
 (.branch 103
 (.branch 100
 (.branch 99
 (.leaf (⟨3, 4, 262945, 270595, 210613265730, 434917970055⟩, 1460404710995672608208782521))
 (.leaf (⟨3, 4, 262945, 270595, 141893788995, 434917935495⟩, 1780774941655320879549121986)))
 (.branch 101
 (.leaf (⟨1, 4, 205060, 17185, 361617786720, 288326448720⟩, 773))
 (.branch 102
 (.leaf (⟨1, 4, 205060, 17185, 361616738145, 288326448645⟩, 1194))
 (.leaf (⟨1, 4, 205060, 17185, 361599960930, 288326447205⟩, 1459)))))
 (.branch 105
 (.branch 104
 (.leaf (⟨1, 4, 205060, 17185, 361331525475, 288326420325⟩, 1724))
 (.leaf (⟨1, 4, 205060, 17185, 357036558180, 288325928805⟩, 1833)))
 (.branch 106
 (.leaf (⟨1, 4, 205060, 17185, 288317081445, 288317081445⟩, 1858))
 (.branch 107
 (.leaf (⟨2, 4, 205120, 82720, 361626105360, 361626105360⟩, 19071268))
 (.leaf (⟨2, 4, 205120, 82720, 361609328160, 361626104160⟩, 29295040))))))
 (.branch 113
 (.branch 110
 (.branch 109
 (.leaf (⟨2, 4, 205120, 82720, 361592550945, 361626104070⟩, 56886117))
 (.leaf (⟨2, 4, 205120, 82720, 361340892720, 361626081120⟩, 39518812)))
 (.branch 111
 (.leaf (⟨2, 4, 205120, 82720, 361324115505, 361626081030⟩, 67109889))
 (.branch 112
 (.leaf (⟨2, 4, 205120, 82720, 357045925440, 361625651040⟩, 45023920))
 (.leaf (⟨2, 4, 205120, 82720, 356760712770, 361625649270⟩, 84477194)))))
 (.branch 115
 (.branch 114
 (.leaf (⟨2, 4, 205120, 82720, 352465745475, 361625618550⟩, 101844499))
 (.leaf (⟨2, 4, 205120, 82720, 288309671505, 361617786630⟩, 72614997)))
 (.branch 116
 (.leaf (⟨2, 4, 205120, 82720, 288041236050, 361617784950⟩, 89982302))
 (.branch 117
 (.leaf (⟨2, 4, 205120, 82720, 283746268755, 361617754230⟩, 107349607))
 (.leaf (⟨2, 4, 205120, 82720, 215026792020, 361617201270⟩, 114493140))))))))
 (.branch 138
 (.branch 128
 (.branch 123
 (.branch 120
 (.branch 119
 (.leaf (⟨2, 4, 200770, 81970, 361626105360, 361626105360⟩, 18743579))
 (.leaf (⟨2, 4, 200770, 81970, 361609328160, 361626104160⟩, 28967351)))
 (.branch 121
 (.leaf (⟨2, 4, 200770, 81970, 361592550945, 361626104070⟩, 56558428))
 (.branch 122
 (.leaf (⟨2, 4, 200770, 81970, 361340892720, 361626081120⟩, 39191123))
 (.leaf (⟨2, 4, 200770, 81970, 361324115505, 361626081030⟩, 66782200)))))
 (.branch 125
 (.branch 124
 (.leaf (⟨2, 4, 200770, 81970, 357045925440, 361625651040⟩, 44696231))
 (.leaf (⟨2, 4, 200770, 81970, 356760712770, 361625649270⟩, 84149505)))
 (.branch 126
 (.leaf (⟨2, 4, 200770, 81970, 352465745475, 361625618550⟩, 101516810))
 (.branch 127
 (.leaf (⟨2, 4, 200770, 81970, 288309671505, 361617786630⟩, 72287308))
 (.leaf (⟨2, 4, 200770, 81970, 288041236050, 361617784950⟩, 89654613))))))
 (.branch 133
 (.branch 130
 (.branch 129
 (.leaf (⟨2, 4, 200770, 81970, 283746268755, 361617754230⟩, 107021918))
 (.leaf (⟨2, 4, 200770, 81970, 215026792020, 361617201270⟩, 114165451)))
 (.branch 131
 (.leaf (⟨3, 4, 201760, 147760, 361742426640, 434925761040⟩, 166834345690677701287411851))
 (.branch 132
 (.leaf (⟨3, 4, 201760, 147760, 361473991440, 434925741840⟩, 253878332888770816519504083))
 (.leaf (⟨3, 4, 201760, 147760, 356910588960, 434925371760⟩, 442473638484639232855703919)))))
 (.branch 135
 (.branch 134
 (.leaf (⟨3, 4, 201760, 147760, 352615621680, 434925344880⟩, 631068944080507649191903755))
 (.leaf (⟨3, 4, 201760, 147760, 287922677025, 434918490375⟩, 951439174740155920532243220)))
 (.branch 136
 (.leaf (⟨3, 4, 201760, 147760, 283627709745, 434918463495⟩, 1140034480336024336868443056))
 (.branch 137
 (.leaf (⟨3, 4, 201760, 147760, 210613265730, 434917970055⟩, 1460404710995672608208782521))
 (.leaf (⟨3, 4, 201760, 147760, 141893788995, 434917935495⟩, 1780774941655320879549121986)))))))
 (.branch 148
 (.branch 143
 (.branch 140
 (.branch 139
 (.leaf (⟨2, 4, 135235, 66610, 361626105360, 361626105360⟩, 19267877))
 (.leaf (⟨2, 4, 135235, 66610, 361609328160, 361626104160⟩, 29491649)))
 (.branch 141
 (.leaf (⟨2, 4, 135235, 66610, 361592550945, 361626104070⟩, 57082726))
 (.branch 142
 (.leaf (⟨2, 4, 135235, 66610, 361340892720, 361626081120⟩, 39715421))
 (.leaf (⟨2, 4, 135235, 66610, 361324115505, 361626081030⟩, 67306498)))))
 (.branch 145
 (.branch 144
 (.leaf (⟨2, 4, 135235, 66610, 357045925440, 361625651040⟩, 45220529))
 (.leaf (⟨2, 4, 135235, 66610, 356760712770, 361625649270⟩, 84673803)))
 (.branch 146
 (.leaf (⟨2, 4, 135235, 66610, 352465745475, 361625618550⟩, 102041108))
 (.branch 147
 (.leaf (⟨2, 4, 135235, 66610, 288309671505, 361617786630⟩, 72811606))
 (.leaf (⟨2, 4, 135235, 66610, 288041236050, 361617784950⟩, 90178911))))))
 (.branch 153
 (.branch 150
 (.branch 149
 (.leaf (⟨2, 4, 135235, 66610, 283746268755, 361617754230⟩, 107546216))
 (.leaf (⟨2, 4, 135235, 66610, 215026792020, 361617201270⟩, 114689749)))
 (.branch 151
 (.leaf (⟨3, 4, 66610, 135235, 361742426640, 434925761040⟩, 170461104701651632375070856))
 (.branch 152
 (.leaf (⟨3, 4, 66610, 135235, 361473991440, 434925741840⟩, 257505091899744747607163088))
 (.leaf (⟨3, 4, 66610, 135235, 356910588960, 434925371760⟩, 446100397495613163943362924)))))
 (.branch 155
 (.branch 154
 (.leaf (⟨3, 4, 66610, 135235, 352615621680, 434925344880⟩, 634695703091481580279562760))
 (.leaf (⟨3, 4, 66610, 135235, 287922677025, 434918490375⟩, 955065933751129851619902225)))
 (.branch 156
 (.leaf (⟨3, 4, 66610, 135235, 283627709745, 434918463495⟩, 1143661239346998267956102061))
 (.branch 157
 (.leaf (⟨3, 4, 66610, 135235, 210613265730, 434917970055⟩, 1464031470006646539296441526))
 (.leaf (⟨3, 4, 66610, 135235, 141893788995, 434917935495⟩, 1784401700666294810636780991))))))))))
noncomputable def raw (i : Fin blockCount) : RawFacePlacement.Block := (records.get i.val).1
noncomputable def witness (i : Fin blockCount) (code : Nat) : Fin 2824 :=
  Fin.ofNat 2824 (Nat.land (Nat.shiftRight (records.get i.val).2 (16 * code)) 65535)
noncomputable def faceTable : Table Nat :=
(.branch 10288
 (.branch 5156
 (.branch 3096
 (.branch 2056
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
 (.branch 2052
 (.leaf 7)
 (.leaf 8)))))
 (.branch 3078
 (.branch 2080
 (.branch 2064
 (.leaf 9)
 (.leaf 10))
 (.branch 3075
 (.leaf 11)
 (.branch 3077
 (.leaf 12)
 (.leaf 13))))
 (.branch 3082
 (.branch 3081
 (.leaf 14)
 (.leaf 15))
 (.branch 3089
 (.leaf 16)
 (.branch 3092
 (.leaf 17)
 (.leaf 18))))))
 (.branch 4128
 (.branch 4097
 (.branch 3108
 (.branch 3106
 (.leaf 19)
 (.leaf 20))
 (.branch 3112
 (.leaf 21)
 (.branch 3120
 (.leaf 22)
 (.leaf 23))))
 (.branch 4100
 (.branch 4098
 (.leaf 24)
 (.leaf 25))
 (.branch 4104
 (.leaf 26)
 (.branch 4112
 (.leaf 27)
 (.leaf 28)))))
 (.branch 5130
 (.branch 5125
 (.branch 5123
 (.leaf 29)
 (.leaf 30))
 (.branch 5126
 (.leaf 31)
 (.branch 5129
 (.leaf 32)
 (.leaf 33))))
 (.branch 5140
 (.branch 5137
 (.leaf 34)
 (.leaf 35))
 (.branch 5144
 (.leaf 36)
 (.branch 5154
 (.leaf 37)
 (.leaf 38)))))))
 (.branch 7210
 (.branch 6168
 (.branch 6150
 (.branch 5168
 (.branch 5160
 (.leaf 39)
 (.leaf 40))
 (.branch 6147
 (.leaf 41)
 (.branch 6149
 (.leaf 42)
 (.leaf 43))))
 (.branch 6154
 (.branch 6153
 (.leaf 44)
 (.leaf 45))
 (.branch 6161
 (.leaf 46)
 (.branch 6164
 (.leaf 47)
 (.leaf 48)))))
 (.branch 7175
 (.branch 6180
 (.branch 6178
 (.leaf 49)
 (.leaf 50))
 (.branch 6184
 (.leaf 51)
 (.branch 6192
 (.leaf 52)
 (.leaf 53))))
 (.branch 7189
 (.branch 7179
 (.leaf 54)
 (.leaf 55))
 (.branch 7193
 (.leaf 56)
 (.branch 7206
 (.leaf 57)
 (.leaf 58))))))
 (.branch 10245
 (.branch 8196
 (.branch 7224
 (.branch 7220
 (.leaf 59)
 (.leaf 60))
 (.branch 8193
 (.leaf 61)
 (.branch 8194
 (.leaf 62)
 (.leaf 63))))
 (.branch 8208
 (.branch 8200
 (.leaf 64)
 (.leaf 65))
 (.branch 8224
 (.leaf 66)
 (.branch 10243
 (.leaf 67)
 (.leaf 68)))))
 (.branch 10260
 (.branch 10249
 (.branch 10246
 (.leaf 69)
 (.leaf 70))
 (.branch 10250
 (.leaf 71)
 (.branch 10257
 (.leaf 72)
 (.leaf 73))))
 (.branch 10274
 (.branch 10264
 (.leaf 74)
 (.leaf 75))
 (.branch 10276
 (.leaf 76)
 (.branch 10280
 (.leaf 77)
 (.leaf 78))))))))
 (.branch 20483
 (.branch 14388
 (.branch 12322
 (.branch 12297
 (.branch 12293
 (.branch 12291
 (.leaf 79)
 (.leaf 80))
 (.branch 12294
 (.leaf 81)
 (.leaf 82)))
 (.branch 12305
 (.branch 12298
 (.leaf 83)
 (.leaf 84))
 (.branch 12308
 (.leaf 85)
 (.branch 12312
 (.leaf 86)
 (.leaf 87)))))
 (.branch 14347
 (.branch 12328
 (.branch 12324
 (.leaf 88)
 (.leaf 89))
 (.branch 12336
 (.leaf 90)
 (.branch 14343
 (.leaf 91)
 (.leaf 92))))
 (.branch 14361
 (.branch 14357
 (.leaf 93)
 (.leaf 94))
 (.branch 14374
 (.leaf 95)
 (.branch 14378
 (.leaf 96)
 (.leaf 97))))))
 (.branch 17414
 (.branch 16392
 (.branch 16385
 (.branch 14392
 (.leaf 98)
 (.leaf 99))
 (.branch 16386
 (.leaf 100)
 (.branch 16388
 (.leaf 101)
 (.leaf 102))))
 (.branch 16416
 (.branch 16400
 (.leaf 103)
 (.leaf 104))
 (.branch 17411
 (.leaf 105)
 (.branch 17413
 (.leaf 106)
 (.leaf 107)))))
 (.branch 17432
 (.branch 17418
 (.branch 17417
 (.leaf 108)
 (.leaf 109))
 (.branch 17425
 (.leaf 110)
 (.branch 17428
 (.leaf 111)
 (.leaf 112))))
 (.branch 17444
 (.branch 17442
 (.leaf 113)
 (.leaf 114))
 (.branch 17448
 (.leaf 115)
 (.branch 17456
 (.leaf 116)
 (.leaf 117)))))))
 (.branch 24579
 (.branch 20520
 (.branch 20497
 (.branch 20486
 (.branch 20485
 (.leaf 118)
 (.leaf 119))
 (.branch 20489
 (.leaf 120)
 (.branch 20490
 (.leaf 121)
 (.leaf 122))))
 (.branch 20504
 (.branch 20500
 (.leaf 123)
 (.leaf 124))
 (.branch 20514
 (.leaf 125)
 (.branch 20516
 (.leaf 126)
 (.leaf 127)))))
 (.branch 21529
 (.branch 21511
 (.branch 20528
 (.leaf 128)
 (.leaf 129))
 (.branch 21515
 (.leaf 130)
 (.branch 21525
 (.leaf 131)
 (.leaf 132))))
 (.branch 21546
 (.branch 21542
 (.leaf 133)
 (.leaf 134))
 (.branch 21556
 (.leaf 135)
 (.branch 21560
 (.leaf 136)
 (.leaf 137))))))
 (.branch 24616
 (.branch 24593
 (.branch 24582
 (.branch 24581
 (.leaf 138)
 (.leaf 139))
 (.branch 24585
 (.leaf 140)
 (.branch 24586
 (.leaf 141)
 (.leaf 142))))
 (.branch 24600
 (.branch 24596
 (.leaf 143)
 (.leaf 144))
 (.branch 24610
 (.leaf 145)
 (.branch 24612
 (.leaf 146)
 (.leaf 147)))))
 (.branch 28697
 (.branch 28679
 (.branch 24624
 (.leaf 148)
 (.leaf 149))
 (.branch 28683
 (.leaf 150)
 (.branch 28693
 (.leaf 151)
 (.leaf 152))))
 (.branch 28714
 (.branch 28710
 (.leaf 153)
 (.leaf 154))
 (.branch 28724
 (.leaf 155)
 (.branch 28728
 (.leaf 156)
 (.leaf 157)))))))))
noncomputable def faceWitness (s r : Nat) : Fin blockCount :=
  Fin.ofNat blockCount (faceTable.get (s * 1024 + r))
noncomputable def validity (i : Nat) : Bool :=
  RawFaceNormalizers.blockValidCheck 5 (raw (Fin.ofNat blockCount i))
noncomputable def placement (b : Fin blockCount) (code : Nat) : Bool :=
  RawKindedFacePlacement.check 5 (raw b) template root FacetUniverses.RootedSixBase04.cells
    code 0 (witness b code)
noncomputable def test (i : Nat) : Bool :=
  let b := Fin.ofNat blockCount i
  FiniteChecks.checkRange (placement b)
    0 (RawFacePlacement.count (raw b).shared (raw b).shared)
noncomputable def symmetry (i : Nat) : Bool :=
  RawOutsidePlacement.blockCheck FacetUniverses.RootedSixBase04.Outside.vertexCode root.vertices
    (raw (Fin.ofNat blockCount i))
end Papers.RationalityTen.RootedCanonical.RootedSixBase04.S5T1

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase04.S5T1
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
end Papers.RationalityTen.RootedCanonical.RootedSixBase04.S5T1

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase04.S5T1
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
theorem check_0099_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 99)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 99)) 0 6 (by decide +kernel)
theorem block_0099 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 99)) 0 6 :=
  check_0099_0000
theorem check_0100_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 100)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 100)) 0 1 (by decide +kernel)
theorem block_0100 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 100)) 0 1 :=
  check_0100_0000
theorem check_0101_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 101)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 101)) 0 1 (by decide +kernel)
theorem block_0101 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 101)) 0 1 :=
  check_0101_0000
theorem check_0102_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 102)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 102)) 0 1 (by decide +kernel)
theorem block_0102 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 102)) 0 1 :=
  check_0102_0000
theorem check_0103_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 103)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 103)) 0 1 (by decide +kernel)
theorem block_0103 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 103)) 0 1 :=
  check_0103_0000
theorem check_0104_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 104)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 104)) 0 1 (by decide +kernel)
theorem block_0104 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 104)) 0 1 :=
  check_0104_0000
theorem check_0105_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 105)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 105)) 0 1 (by decide +kernel)
theorem block_0105 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 105)) 0 1 :=
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
end Papers.RationalityTen.RootedCanonical.RootedSixBase04.S5T1

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase04.S5T1
theorem check_0128_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 128)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 128)) 0 2 (by decide +kernel)
theorem block_0128 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 128)) 0 2 :=
  check_0128_0000
theorem check_0129_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 129)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 129)) 0 2 (by decide +kernel)
theorem block_0129 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 129)) 0 2 :=
  check_0129_0000
theorem check_0130_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 130)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 130)) 0 6 (by decide +kernel)
theorem block_0130 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 130)) 0 6 :=
  check_0130_0000
theorem check_0131_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 131)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 131)) 0 6 (by decide +kernel)
theorem block_0131 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 131)) 0 6 :=
  check_0131_0000
theorem check_0132_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 132)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 132)) 0 6 (by decide +kernel)
theorem block_0132 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 132)) 0 6 :=
  check_0132_0000
theorem check_0133_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 133)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 133)) 0 6 (by decide +kernel)
theorem block_0133 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 133)) 0 6 :=
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
end Papers.RationalityTen.RootedCanonical.RootedSixBase04.S5T1

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase04.S5T1
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
theorem metadata_validity_0144 : FiniteChecks.Interval validity 144 158 :=
  FiniteChecks.interval_of_check validity 144 14 (by decide +kernel)
theorem metadata_validity : FiniteChecks.Interval validity 0 blockCount :=
  (FiniteChecks.interval_append (validity) 0 80 158
  (FiniteChecks.interval_append (validity) 0 32 80
  (FiniteChecks.interval_append (validity) 0 16 32
  metadata_validity_0000
  metadata_validity_0016)
  (FiniteChecks.interval_append (validity) 32 48 80
  metadata_validity_0032
  (FiniteChecks.interval_append (validity) 48 64 80
  metadata_validity_0048
  metadata_validity_0064)))
  (FiniteChecks.interval_append (validity) 80 112 158
  (FiniteChecks.interval_append (validity) 80 96 112
  metadata_validity_0080
  metadata_validity_0096)
  (FiniteChecks.interval_append (validity) 112 128 158
  metadata_validity_0112
  (FiniteChecks.interval_append (validity) 128 144 158
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
theorem metadata_symmetry_0144 : FiniteChecks.Interval symmetry 144 158 :=
  FiniteChecks.interval_of_check symmetry 144 14 (by decide +kernel)
theorem metadata_symmetry : FiniteChecks.Interval symmetry 0 blockCount :=
  (FiniteChecks.interval_append (symmetry) 0 80 158
  (FiniteChecks.interval_append (symmetry) 0 32 80
  (FiniteChecks.interval_append (symmetry) 0 16 32
  metadata_symmetry_0000
  metadata_symmetry_0016)
  (FiniteChecks.interval_append (symmetry) 32 48 80
  metadata_symmetry_0032
  (FiniteChecks.interval_append (symmetry) 48 64 80
  metadata_symmetry_0048
  metadata_symmetry_0064)))
  (FiniteChecks.interval_append (symmetry) 80 112 158
  (FiniteChecks.interval_append (symmetry) 80 96 112
  metadata_symmetry_0080
  metadata_symmetry_0096)
  (FiniteChecks.interval_append (symmetry) 112 128 158
  metadata_symmetry_0112
  (FiniteChecks.interval_append (symmetry) 128 144 158
  metadata_symmetry_0128
  metadata_symmetry_0144))))
theorem metadata_normalizers :
    RawFaceNormalizers.completeCheck 5 template root raw faceWitness = true := by decide +kernel
theorem metadata_root : RawFacetEmbedding.wellFormedCheck root = true := by decide +kernel
end Papers.RationalityTen.RootedCanonical.RootedSixBase04.S5T1

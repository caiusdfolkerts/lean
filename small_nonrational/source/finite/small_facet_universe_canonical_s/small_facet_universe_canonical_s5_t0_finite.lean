module
prelude
public import SmallFacetUniverse
public import RawKindedFacePlacement
public import SmallFacetUniverseOutsideData
public import RawOutsidePlacement

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.SmallFacetUniverse.S5T0
open ConcreteGrowth
abbrev blockCount : Nat := 143
noncomputable def template : Cell := ⟨2, 31, [3, 5, 6, 9, 10, 12, 17, 18, 24], [7, 13, 14, 19, 25, 26]⟩
noncomputable def root : Cell := FacetUniverses.Small.cells 0
noncomputable def records : Table (RawFacePlacement.Block × Nat) :=
(.branch 71
 (.branch 35
 (.branch 17
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf (⟨0, 5, 274960, 274960, 288317081445, 288317081445⟩, 3419))
 (.leaf (⟨1, 5, 274960, 274960, 288326448720, 361617786720⟩, 1504)))
 (.branch 3
 (.leaf (⟨1, 5, 274960, 274960, 288309671505, 361617786630⟩, 2499))
 (.leaf (⟨1, 5, 274960, 274960, 288041236050, 361617784950⟩, 3044))))
 (.branch 6
 (.branch 5
 (.leaf (⟨1, 5, 274960, 274960, 283746268755, 361617754230⟩, 3169))
 (.leaf (⟨1, 5, 274960, 274960, 215026792020, 361617201270⟩, 3294)))
 (.branch 7
 (.leaf (⟨1, 5, 274945, 274945, 288326448720, 361617786720⟩, 1504))
 (.leaf (⟨1, 5, 274945, 274945, 288309671505, 361617786630⟩, 2499)))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf (⟨1, 5, 274945, 274945, 288041236050, 361617784950⟩, 3044))
 (.leaf (⟨1, 5, 274945, 274945, 283746268755, 361617754230⟩, 3169)))
 (.branch 11
 (.leaf (⟨1, 5, 274945, 274945, 215026792020, 361617201270⟩, 3294))
 (.leaf (⟨2, 5, 274960, 274960, 288459547920, 434918491920⟩, 27722151))))
 (.branch 14
 (.branch 13
 (.leaf (⟨2, 5, 274960, 274960, 288191112480, 434918490480⟩, 57213801))
 (.leaf (⟨2, 5, 274960, 274960, 287922677025, 434918490375⟩, 122423116)))
 (.branch 15
 (.leaf (⟨2, 5, 274960, 274960, 283896145200, 434918463600⟩, 70976571))
 (.branch 16
 (.leaf (⟨2, 5, 274960, 274960, 283627709745, 434918463495⟩, 136185886))
 (.leaf (⟨2, 5, 274960, 274960, 279332742450, 434918461575⟩, 171903551)))))))
 (.branch 26
 (.branch 21
 (.branch 19
 (.branch 18
 (.leaf (⟨2, 5, 274960, 274960, 215176668480, 434917972080⟩, 84739341))
 (.leaf (⟨2, 5, 274960, 274960, 214908233025, 434917971975⟩, 149948656)))
 (.branch 20
 (.leaf (⟨2, 5, 274960, 274960, 210613265730, 434917970055⟩, 185666321))
 (.leaf (⟨1, 5, 274690, 274465, 288326448720, 361617786720⟩, 1499))))
 (.branch 23
 (.branch 22
 (.leaf (⟨1, 5, 274690, 274465, 288309671505, 361617786630⟩, 2494))
 (.leaf (⟨1, 5, 274690, 274465, 288041236050, 361617784950⟩, 3039)))
 (.branch 24
 (.leaf (⟨1, 5, 274690, 274465, 283746268755, 361617754230⟩, 3164))
 (.branch 25
 (.leaf (⟨1, 5, 274690, 274465, 215026792020, 361617201270⟩, 3289))
 (.leaf (⟨2, 5, 274720, 274720, 288459547920, 434918491920⟩, 27394469))))))
 (.branch 30
 (.branch 28
 (.branch 27
 (.leaf (⟨2, 5, 274720, 274720, 288191112480, 434918490480⟩, 56886119))
 (.leaf (⟨2, 5, 274720, 274720, 287922677025, 434918490375⟩, 122095434)))
 (.branch 29
 (.leaf (⟨2, 5, 274720, 274720, 283896145200, 434918463600⟩, 70648889))
 (.leaf (⟨2, 5, 274720, 274720, 283627709745, 434918463495⟩, 135858204))))
 (.branch 32
 (.branch 31
 (.leaf (⟨2, 5, 274720, 274720, 279332742450, 434918461575⟩, 171575869))
 (.leaf (⟨2, 5, 274720, 274720, 215176668480, 434917972080⟩, 84411659)))
 (.branch 33
 (.leaf (⟨2, 5, 274720, 274720, 214908233025, 434917971975⟩, 149620974))
 (.branch 34
 (.leaf (⟨2, 5, 274720, 274720, 210613265730, 434917970055⟩, 185338639))
 (.leaf (⟨2, 5, 274465, 274690, 288459547920, 434918491920⟩, 27394469))))))))
 (.branch 53
 (.branch 44
 (.branch 39
 (.branch 37
 (.branch 36
 (.leaf (⟨2, 5, 274465, 274690, 288191112480, 434918490480⟩, 56886119))
 (.leaf (⟨2, 5, 274465, 274690, 287922677025, 434918490375⟩, 122095434)))
 (.branch 38
 (.leaf (⟨2, 5, 274465, 274690, 283896145200, 434918463600⟩, 70648889))
 (.leaf (⟨2, 5, 274465, 274690, 283627709745, 434918463495⟩, 135858204))))
 (.branch 41
 (.branch 40
 (.leaf (⟨2, 5, 274465, 274690, 279332742450, 434918461575⟩, 171575869))
 (.leaf (⟨2, 5, 274465, 274690, 215176668480, 434917972080⟩, 84411659)))
 (.branch 42
 (.leaf (⟨2, 5, 274465, 274690, 214908233025, 434917971975⟩, 149620974))
 (.branch 43
 (.leaf (⟨2, 5, 274465, 274690, 210613265730, 434917970055⟩, 185338639))
 (.leaf (⟨3, 5, 274960, 274960, 286025732880, 508219172880⟩, 213983135195875200155844789))))))
 (.branch 48
 (.branch 46
 (.branch 45
 (.leaf (⟨3, 5, 274960, 274960, 281730765600, 508219171200⟩, 758008055183957170356421239))
 (.leaf (⟨3, 5, 274960, 274960, 277435798305, 508219171080⟩, 1960907600490938415577695834)))
 (.branch 47
 (.leaf (⟨3, 5, 274960, 274960, 217306256400, 508218742800⟩, 359056447192697058875998509))
 (.leaf (⟨3, 5, 274960, 274960, 213011289120, 508218741120⟩, 903081367180779029076574959))))
 (.branch 50
 (.branch 49
 (.leaf (⟨3, 5, 274960, 274960, 208716321825, 508218741000⟩, 2105980912487760274297849554))
 (.leaf (⟨1, 5, 270595, 262945, 288326448720, 361617786720⟩, 1505)))
 (.branch 51
 (.leaf (⟨1, 5, 270595, 262945, 288309671505, 361617786630⟩, 2500))
 (.branch 52
 (.leaf (⟨1, 5, 270595, 262945, 288041236050, 361617784950⟩, 3045))
 (.leaf (⟨1, 5, 270595, 262945, 283746268755, 361617754230⟩, 3170)))))))
 (.branch 62
 (.branch 57
 (.branch 55
 (.branch 54
 (.leaf (⟨1, 5, 270595, 262945, 215026792020, 361617201270⟩, 3295))
 (.leaf (⟨2, 5, 270640, 267040, 288459547920, 434918491920⟩, 27787688)))
 (.branch 56
 (.leaf (⟨2, 5, 270640, 267040, 288191112480, 434918490480⟩, 57279338))
 (.leaf (⟨2, 5, 270640, 267040, 287922677025, 434918490375⟩, 122488653))))
 (.branch 59
 (.branch 58
 (.leaf (⟨2, 5, 270640, 267040, 283896145200, 434918463600⟩, 71042108))
 (.leaf (⟨2, 5, 270640, 267040, 283627709745, 434918463495⟩, 136251423)))
 (.branch 60
 (.leaf (⟨2, 5, 270640, 267040, 279332742450, 434918461575⟩, 171969088))
 (.branch 61
 (.leaf (⟨2, 5, 270640, 267040, 215176668480, 434917972080⟩, 84804878))
 (.leaf (⟨2, 5, 270640, 267040, 214908233025, 434917971975⟩, 150014193))))))
 (.branch 66
 (.branch 64
 (.branch 63
 (.leaf (⟨2, 5, 270640, 267040, 210613265730, 434917970055⟩, 185731858))
 (.leaf (⟨2, 5, 270385, 267010, 288459547920, 434918491920⟩, 27787688)))
 (.branch 65
 (.leaf (⟨2, 5, 270385, 267010, 288191112480, 434918490480⟩, 57279338))
 (.leaf (⟨2, 5, 270385, 267010, 287922677025, 434918490375⟩, 122488653))))
 (.branch 68
 (.branch 67
 (.leaf (⟨2, 5, 270385, 267010, 283896145200, 434918463600⟩, 71042108))
 (.leaf (⟨2, 5, 270385, 267010, 283627709745, 434918463495⟩, 136251423)))
 (.branch 69
 (.leaf (⟨2, 5, 270385, 267010, 279332742450, 434918461575⟩, 171969088))
 (.branch 70
 (.leaf (⟨2, 5, 270385, 267010, 215176668480, 434917972080⟩, 84804878))
 (.leaf (⟨2, 5, 270385, 267010, 214908233025, 434917971975⟩, 150014193)))))))))
 (.branch 107
 (.branch 89
 (.branch 80
 (.branch 75
 (.branch 73
 (.branch 72
 (.leaf (⟨2, 5, 270385, 267010, 210613265730, 434917970055⟩, 185731858))
 (.leaf (⟨2, 5, 266290, 266290, 288459547920, 434918491920⟩, 27591074)))
 (.branch 74
 (.leaf (⟨2, 5, 266290, 266290, 288191112480, 434918490480⟩, 57082724))
 (.leaf (⟨2, 5, 266290, 266290, 287922677025, 434918490375⟩, 122292039))))
 (.branch 77
 (.branch 76
 (.leaf (⟨2, 5, 266290, 266290, 283896145200, 434918463600⟩, 70845494))
 (.leaf (⟨2, 5, 266290, 266290, 283627709745, 434918463495⟩, 136054809)))
 (.branch 78
 (.leaf (⟨2, 5, 266290, 266290, 279332742450, 434918461575⟩, 171772474))
 (.branch 79
 (.leaf (⟨2, 5, 266290, 266290, 215176668480, 434917972080⟩, 84608264))
 (.leaf (⟨2, 5, 266290, 266290, 214908233025, 434917971975⟩, 149817579))))))
 (.branch 84
 (.branch 82
 (.branch 81
 (.leaf (⟨2, 5, 266290, 266290, 210613265730, 434917970055⟩, 185535244))
 (.leaf (⟨3, 5, 267040, 270640, 286025732880, 508219172880⟩, 216401060622643694706688179)))
 (.branch 83
 (.leaf (⟨3, 5, 267040, 270640, 281730765600, 508219171200⟩, 760425980610725664907264629))
 (.leaf (⟨3, 5, 267040, 270640, 277435798305, 508219171080⟩, 1963325525917706910128539224))))
 (.branch 86
 (.branch 85
 (.leaf (⟨3, 5, 267040, 270640, 217306256400, 508218742800⟩, 361474372619465553426841899))
 (.leaf (⟨3, 5, 267040, 270640, 213011289120, 508218741120⟩, 905499292607547523627418349)))
 (.branch 87
 (.leaf (⟨3, 5, 267040, 270640, 208716321825, 508218741000⟩, 2108398837914528768848692944))
 (.branch 88
 (.leaf (⟨3, 5, 262945, 270595, 286025732880, 508219172880⟩, 216401060622643694706688179))
 (.leaf (⟨3, 5, 262945, 270595, 281730765600, 508219171200⟩, 760425980610725664907264629)))))))
 (.branch 98
 (.branch 93
 (.branch 91
 (.branch 90
 (.leaf (⟨3, 5, 262945, 270595, 277435798305, 508219171080⟩, 1963325525917706910128539224))
 (.leaf (⟨3, 5, 262945, 270595, 217306256400, 508218742800⟩, 361474372619465553426841899)))
 (.branch 92
 (.leaf (⟨3, 5, 262945, 270595, 213011289120, 508218741120⟩, 905499292607547523627418349))
 (.leaf (⟨3, 5, 262945, 270595, 208716321825, 508218741000⟩, 2108398837914528768848692944))))
 (.branch 95
 (.branch 94
 (.leaf (⟨1, 5, 205060, 17185, 288326448720, 361617786720⟩, 1498))
 (.leaf (⟨1, 5, 205060, 17185, 288309671505, 361617786630⟩, 2493)))
 (.branch 96
 (.leaf (⟨1, 5, 205060, 17185, 288041236050, 361617784950⟩, 3038))
 (.branch 97
 (.leaf (⟨1, 5, 205060, 17185, 283746268755, 361617754230⟩, 3163))
 (.leaf (⟨1, 5, 205060, 17185, 215026792020, 361617201270⟩, 3288))))))
 (.branch 102
 (.branch 100
 (.branch 99
 (.leaf (⟨2, 5, 205120, 82720, 288459547920, 434918491920⟩, 27328932))
 (.leaf (⟨2, 5, 205120, 82720, 288191112480, 434918490480⟩, 56820582)))
 (.branch 101
 (.leaf (⟨2, 5, 205120, 82720, 287922677025, 434918490375⟩, 122029897))
 (.leaf (⟨2, 5, 205120, 82720, 283896145200, 434918463600⟩, 70583352))))
 (.branch 104
 (.branch 103
 (.leaf (⟨2, 5, 205120, 82720, 283627709745, 434918463495⟩, 135792667))
 (.leaf (⟨2, 5, 205120, 82720, 279332742450, 434918461575⟩, 171510332)))
 (.branch 105
 (.leaf (⟨2, 5, 205120, 82720, 215176668480, 434917972080⟩, 84346122))
 (.branch 106
 (.leaf (⟨2, 5, 205120, 82720, 214908233025, 434917971975⟩, 149555437))
 (.leaf (⟨2, 5, 205120, 82720, 210613265730, 434917970055⟩, 185273102))))))))
 (.branch 125
 (.branch 116
 (.branch 111
 (.branch 109
 (.branch 108
 (.leaf (⟨2, 5, 204865, 82690, 288459547920, 434918491920⟩, 27328932))
 (.leaf (⟨2, 5, 204865, 82690, 288191112480, 434918490480⟩, 56820582)))
 (.branch 110
 (.leaf (⟨2, 5, 204865, 82690, 287922677025, 434918490375⟩, 122029897))
 (.leaf (⟨2, 5, 204865, 82690, 283896145200, 434918463600⟩, 70583352))))
 (.branch 113
 (.branch 112
 (.leaf (⟨2, 5, 204865, 82690, 283627709745, 434918463495⟩, 135792667))
 (.leaf (⟨2, 5, 204865, 82690, 279332742450, 434918461575⟩, 171510332)))
 (.branch 114
 (.leaf (⟨2, 5, 204865, 82690, 215176668480, 434917972080⟩, 84346122))
 (.branch 115
 (.leaf (⟨2, 5, 204865, 82690, 214908233025, 434917971975⟩, 149555437))
 (.leaf (⟨2, 5, 204865, 82690, 210613265730, 434917970055⟩, 185273102))))))
 (.branch 120
 (.branch 118
 (.branch 117
 (.leaf (⟨3, 5, 205840, 148240, 286025732880, 508219172880⟩, 212774190929235017999843508))
 (.leaf (⟨3, 5, 205840, 148240, 281730765600, 508219171200⟩, 756799110917316988200419958)))
 (.branch 119
 (.leaf (⟨3, 5, 205840, 148240, 277435798305, 508219171080⟩, 1959698656224298233421694553))
 (.leaf (⟨3, 5, 205840, 148240, 217306256400, 508218742800⟩, 357847502926056876719997228))))
 (.branch 122
 (.branch 121
 (.leaf (⟨3, 5, 205840, 148240, 213011289120, 508218741120⟩, 901872422914138846920573678))
 (.leaf (⟨3, 5, 205840, 148240, 208716321825, 508218741000⟩, 2104771968221120092141848273)))
 (.branch 123
 (.leaf (⟨2, 5, 135235, 66610, 288459547920, 434918491920⟩, 27394469))
 (.branch 124
 (.leaf (⟨2, 5, 135235, 66610, 288191112480, 434918490480⟩, 56886119))
 (.leaf (⟨2, 5, 135235, 66610, 287922677025, 434918490375⟩, 122095434)))))))
 (.branch 134
 (.branch 129
 (.branch 127
 (.branch 126
 (.leaf (⟨2, 5, 135235, 66610, 283896145200, 434918463600⟩, 70648889))
 (.leaf (⟨2, 5, 135235, 66610, 283627709745, 434918463495⟩, 135858204)))
 (.branch 128
 (.leaf (⟨2, 5, 135235, 66610, 279332742450, 434918461575⟩, 171575869))
 (.leaf (⟨2, 5, 135235, 66610, 215176668480, 434917972080⟩, 84411659))))
 (.branch 131
 (.branch 130
 (.leaf (⟨2, 5, 135235, 66610, 214908233025, 434917971975⟩, 149620974))
 (.leaf (⟨2, 5, 135235, 66610, 210613265730, 434917970055⟩, 185338639)))
 (.branch 132
 (.leaf (⟨3, 5, 136240, 136240, 286025732880, 508219172880⟩, 213983135195875200155844789))
 (.branch 133
 (.leaf (⟨3, 5, 136240, 136240, 281730765600, 508219171200⟩, 758008055183957170356421239))
 (.leaf (⟨3, 5, 136240, 136240, 277435798305, 508219171080⟩, 1960907600490938415577695834))))))
 (.branch 138
 (.branch 136
 (.branch 135
 (.leaf (⟨3, 5, 136240, 136240, 217306256400, 508218742800⟩, 359056447192697058875998509))
 (.leaf (⟨3, 5, 136240, 136240, 213011289120, 508218741120⟩, 903081367180779029076574959)))
 (.branch 137
 (.leaf (⟨3, 5, 136240, 136240, 208716321825, 508218741000⟩, 2105980912487760274297849554))
 (.leaf (⟨3, 5, 132145, 136195, 286025732880, 508219172880⟩, 213983135195875200155844789))))
 (.branch 140
 (.branch 139
 (.leaf (⟨3, 5, 132145, 136195, 281730765600, 508219171200⟩, 758008055183957170356421239))
 (.leaf (⟨3, 5, 132145, 136195, 277435798305, 508219171080⟩, 1960907600490938415577695834)))
 (.branch 141
 (.leaf (⟨3, 5, 132145, 136195, 217306256400, 508218742800⟩, 359056447192697058875998509))
 (.branch 142
 (.leaf (⟨3, 5, 132145, 136195, 213011289120, 508218741120⟩, 903081367180779029076574959))
 (.leaf (⟨3, 5, 132145, 136195, 208716321825, 508218741000⟩, 2105980912487760274297849554))))))))))
noncomputable def raw (i : Fin blockCount) : RawFacePlacement.Block := (records.get i.val).1
noncomputable def witness (i : Fin blockCount) (code : Nat) : Fin 3436 :=
  Fin.ofNat 3436 (Nat.land (Nat.shiftRight (records.get i.val).2 (16 * code)) 65535)
noncomputable def faceTable : Table Nat :=
(.branch 10260
 (.branch 6149
 (.branch 3089
 (.branch 2052
 (.branch 1032
 (.branch 1026
 (.branch 1025
 (.leaf 0)
 (.leaf 1))
 (.branch 1028
 (.leaf 2)
 (.leaf 3)))
 (.branch 2049
 (.branch 1040
 (.leaf 4)
 (.leaf 5))
 (.branch 2050
 (.leaf 6)
 (.leaf 7))))
 (.branch 3077
 (.branch 2064
 (.branch 2056
 (.leaf 8)
 (.leaf 9))
 (.branch 3075
 (.leaf 10)
 (.leaf 11)))
 (.branch 3081
 (.branch 3078
 (.leaf 12)
 (.leaf 13))
 (.branch 3082
 (.leaf 14)
 (.branch 3084
 (.leaf 15)
 (.leaf 16))))))
 (.branch 5125
 (.branch 4098
 (.branch 3092
 (.branch 3090
 (.leaf 17)
 (.leaf 18))
 (.branch 4097
 (.leaf 19)
 (.leaf 20)))
 (.branch 4104
 (.branch 4100
 (.leaf 21)
 (.leaf 22))
 (.branch 4112
 (.leaf 23)
 (.branch 5123
 (.leaf 24)
 (.leaf 25)))))
 (.branch 5132
 (.branch 5129
 (.branch 5126
 (.leaf 26)
 (.leaf 27))
 (.branch 5130
 (.leaf 28)
 (.leaf 29)))
 (.branch 5138
 (.branch 5137
 (.leaf 30)
 (.leaf 31))
 (.branch 5140
 (.leaf 32)
 (.branch 6147
 (.leaf 33)
 (.leaf 34)))))))
 (.branch 8208
 (.branch 7181
 (.branch 6156
 (.branch 6153
 (.branch 6150
 (.leaf 35)
 (.leaf 36))
 (.branch 6154
 (.leaf 37)
 (.leaf 38)))
 (.branch 6162
 (.branch 6161
 (.leaf 39)
 (.leaf 40))
 (.branch 6164
 (.leaf 41)
 (.branch 7179
 (.leaf 42)
 (.leaf 43)))))
 (.branch 7190
 (.branch 7187
 (.branch 7182
 (.leaf 44)
 (.leaf 45))
 (.branch 7189
 (.leaf 46)
 (.leaf 47)))
 (.branch 8194
 (.branch 8193
 (.leaf 48)
 (.leaf 49))
 (.branch 8196
 (.leaf 50)
 (.branch 8200
 (.leaf 51)
 (.leaf 52))))))
 (.branch 9236
 (.branch 9225
 (.branch 9221
 (.branch 9219
 (.leaf 53)
 (.leaf 54))
 (.branch 9222
 (.leaf 55)
 (.leaf 56)))
 (.branch 9228
 (.branch 9226
 (.leaf 57)
 (.leaf 58))
 (.branch 9233
 (.leaf 59)
 (.branch 9234
 (.leaf 60)
 (.leaf 61)))))
 (.branch 10249
 (.branch 10245
 (.branch 10243
 (.leaf 62)
 (.leaf 63))
 (.branch 10246
 (.leaf 64)
 (.leaf 65)))
 (.branch 10252
 (.branch 10250
 (.leaf 66)
 (.leaf 67))
 (.branch 10257
 (.leaf 68)
 (.branch 10258
 (.leaf 69)
 (.leaf 70))))))))
 (.branch 18435
 (.branch 14350
 (.branch 12308
 (.branch 12297
 (.branch 12293
 (.branch 12291
 (.leaf 71)
 (.leaf 72))
 (.branch 12294
 (.leaf 73)
 (.leaf 74)))
 (.branch 12300
 (.branch 12298
 (.leaf 75)
 (.leaf 76))
 (.branch 12305
 (.leaf 77)
 (.branch 12306
 (.leaf 78)
 (.leaf 79)))))
 (.branch 13331
 (.branch 13325
 (.branch 13323
 (.leaf 80)
 (.leaf 81))
 (.branch 13326
 (.leaf 82)
 (.leaf 83)))
 (.branch 13334
 (.branch 13333
 (.leaf 84)
 (.leaf 85))
 (.branch 14347
 (.leaf 86)
 (.branch 14349
 (.leaf 87)
 (.leaf 88))))))
 (.branch 17411
 (.branch 16385
 (.branch 14357
 (.branch 14355
 (.leaf 89)
 (.leaf 90))
 (.branch 14358
 (.leaf 91)
 (.leaf 92)))
 (.branch 16388
 (.branch 16386
 (.leaf 93)
 (.leaf 94))
 (.branch 16392
 (.leaf 95)
 (.branch 16400
 (.leaf 96)
 (.leaf 97)))))
 (.branch 17418
 (.branch 17414
 (.branch 17413
 (.leaf 98)
 (.leaf 99))
 (.branch 17417
 (.leaf 100)
 (.leaf 101)))
 (.branch 17425
 (.branch 17420
 (.leaf 102)
 (.leaf 103))
 (.branch 17426
 (.leaf 104)
 (.branch 17428
 (.leaf 105)
 (.leaf 106)))))))
 (.branch 24585
 (.branch 19467
 (.branch 18442
 (.branch 18438
 (.branch 18437
 (.leaf 107)
 (.leaf 108))
 (.branch 18441
 (.leaf 109)
 (.leaf 110)))
 (.branch 18449
 (.branch 18444
 (.leaf 111)
 (.leaf 112))
 (.branch 18450
 (.leaf 113)
 (.branch 18452
 (.leaf 114)
 (.leaf 115)))))
 (.branch 19477
 (.branch 19470
 (.branch 19469
 (.leaf 116)
 (.leaf 117))
 (.branch 19475
 (.leaf 118)
 (.leaf 119)))
 (.branch 24579
 (.branch 19478
 (.leaf 120)
 (.leaf 121))
 (.branch 24581
 (.leaf 122)
 (.branch 24582
 (.leaf 123)
 (.leaf 124))))))
 (.branch 25619
 (.branch 24594
 (.branch 24588
 (.branch 24586
 (.leaf 125)
 (.leaf 126))
 (.branch 24593
 (.leaf 127)
 (.leaf 128)))
 (.branch 25611
 (.branch 24596
 (.leaf 129)
 (.leaf 130))
 (.branch 25613
 (.leaf 131)
 (.branch 25614
 (.leaf 132)
 (.leaf 133)))))
 (.branch 26637
 (.branch 25622
 (.branch 25621
 (.leaf 134)
 (.leaf 135))
 (.branch 26635
 (.leaf 136)
 (.leaf 137)))
 (.branch 26643
 (.branch 26638
 (.leaf 138)
 (.leaf 139))
 (.branch 26645
 (.leaf 140)
 (.branch 26646
 (.leaf 141)
 (.leaf 142)))))))))
noncomputable def faceWitness (s r : Nat) : Fin blockCount :=
  Fin.ofNat blockCount (faceTable.get (s * 1024 + r))
noncomputable def validity (i : Nat) : Bool :=
  RawFaceNormalizers.blockValidCheck 5 (raw (Fin.ofNat blockCount i))
noncomputable def placement (b : Fin blockCount) (code : Nat) : Bool :=
  RawKindedFacePlacement.check 5 (raw b) template root FacetUniverses.Small.cells
    code 0 (witness b code)
noncomputable def test (i : Nat) : Bool :=
  let b := Fin.ofNat blockCount i
  FiniteChecks.checkRange (placement b)
    0 (RawFacePlacement.count (raw b).shared (raw b).shared)
noncomputable def symmetry (i : Nat) : Bool :=
  RawOutsidePlacement.blockCheck FacetUniverses.Small.Outside.vertexCode root.vertices
    (raw (Fin.ofNat blockCount i))
end Papers.RationalityTen.RootedCanonical.SmallFacetUniverse.S5T0

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.SmallFacetUniverse.S5T0
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
theorem check_0020_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 20)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 20)) 0 1 (by decide +kernel)
theorem block_0020 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 20)) 0 1 :=
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
theorem check_0046_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 46)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 46)) 0 6 (by decide +kernel)
theorem block_0046 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 46)) 0 6 :=
  check_0046_0000
theorem check_0047_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 47)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 47)) 0 6 (by decide +kernel)
theorem block_0047 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 47)) 0 6 :=
  check_0047_0000
theorem check_0048_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 48)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 48)) 0 6 (by decide +kernel)
theorem block_0048 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 48)) 0 6 :=
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
theorem check_0053_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 53)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 53)) 0 1 (by decide +kernel)
theorem block_0053 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 53)) 0 1 :=
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
end Papers.RationalityTen.RootedCanonical.SmallFacetUniverse.S5T0

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.SmallFacetUniverse.S5T0
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
theorem check_0084_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 84)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 84)) 0 6 (by decide +kernel)
theorem block_0084 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 84)) 0 6 :=
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
theorem check_0093_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 93)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 93)) 0 1 (by decide +kernel)
theorem block_0093 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 93)) 0 1 :=
  check_0093_0000
theorem check_0094_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 94)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 94)) 0 1 (by decide +kernel)
theorem block_0094 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 94)) 0 1 :=
  check_0094_0000
theorem check_0095_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 95)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 95)) 0 1 (by decide +kernel)
theorem block_0095 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 95)) 0 1 :=
  check_0095_0000
theorem check_0096_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 96)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 96)) 0 1 (by decide +kernel)
theorem block_0096 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 96)) 0 1 :=
  check_0096_0000
theorem check_0097_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 97)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 97)) 0 1 (by decide +kernel)
theorem block_0097 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 97)) 0 1 :=
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
theorem check_0120_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 120)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 120)) 0 6 (by decide +kernel)
theorem block_0120 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 120)) 0 6 :=
  check_0120_0000
theorem check_0121_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 121)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 121)) 0 6 (by decide +kernel)
theorem block_0121 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 121)) 0 6 :=
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
end Papers.RationalityTen.RootedCanonical.SmallFacetUniverse.S5T0

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.SmallFacetUniverse.S5T0
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
theorem check_0142_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 142)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 142)) 0 6 (by decide +kernel)
theorem block_0142 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 142)) 0 6 :=
  check_0142_0000
end Papers.RationalityTen.RootedCanonical.SmallFacetUniverse.S5T0

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.SmallFacetUniverse.S5T0
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
theorem metadata_validity_0128 : FiniteChecks.Interval validity 128 143 :=
  FiniteChecks.interval_of_check validity 128 15 (by decide +kernel)
theorem metadata_validity : FiniteChecks.Interval validity 0 blockCount :=
  (FiniteChecks.interval_append (validity) 0 64 143
  (FiniteChecks.interval_append (validity) 0 32 64
  (FiniteChecks.interval_append (validity) 0 16 32
  metadata_validity_0000
  metadata_validity_0016)
  (FiniteChecks.interval_append (validity) 32 48 64
  metadata_validity_0032
  metadata_validity_0048))
  (FiniteChecks.interval_append (validity) 64 96 143
  (FiniteChecks.interval_append (validity) 64 80 96
  metadata_validity_0064
  metadata_validity_0080)
  (FiniteChecks.interval_append (validity) 96 112 143
  metadata_validity_0096
  (FiniteChecks.interval_append (validity) 112 128 143
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
theorem metadata_symmetry_0128 : FiniteChecks.Interval symmetry 128 143 :=
  FiniteChecks.interval_of_check symmetry 128 15 (by decide +kernel)
theorem metadata_symmetry : FiniteChecks.Interval symmetry 0 blockCount :=
  (FiniteChecks.interval_append (symmetry) 0 64 143
  (FiniteChecks.interval_append (symmetry) 0 32 64
  (FiniteChecks.interval_append (symmetry) 0 16 32
  metadata_symmetry_0000
  metadata_symmetry_0016)
  (FiniteChecks.interval_append (symmetry) 32 48 64
  metadata_symmetry_0032
  metadata_symmetry_0048))
  (FiniteChecks.interval_append (symmetry) 64 96 143
  (FiniteChecks.interval_append (symmetry) 64 80 96
  metadata_symmetry_0064
  metadata_symmetry_0080)
  (FiniteChecks.interval_append (symmetry) 96 112 143
  metadata_symmetry_0096
  (FiniteChecks.interval_append (symmetry) 112 128 143
  metadata_symmetry_0112
  metadata_symmetry_0128))))
theorem metadata_normalizers :
    RawFaceNormalizers.completeCheck 5 template root raw faceWitness = true := by decide +kernel
theorem metadata_root : RawFacetEmbedding.wellFormedCheck root = true := by decide +kernel
end Papers.RationalityTen.RootedCanonical.SmallFacetUniverse.S5T0

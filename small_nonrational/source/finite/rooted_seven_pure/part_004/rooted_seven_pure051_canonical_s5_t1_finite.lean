module
prelude
public import RootedSevenPure051
public import RawKindedFacePlacement
public import RootedSevenPure051OutsideData
public import RawOutsidePlacement

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSevenPure051.S5T1
open ConcreteGrowth
abbrev blockCount : Nat := 130
noncomputable def template : Cell := ⟨3, 31, [3, 5, 6, 10, 12, 17, 20, 24], [7, 14, 21, 27, 28]⟩
noncomputable def root : Cell := FacetUniverses.RootedSevenPure051.cells 0
noncomputable def records : Table (RawFacePlacement.Block × Nat) :=
(.branch 65
 (.branch 32
 (.branch 16
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf (⟨2, 3, 274960, 274960, 434918491920, 288459547920⟩, 7864439))
 (.leaf (⟨2, 3, 274960, 274960, 434917443360, 288459546960⟩, 11600048)))
 (.branch 3
 (.leaf (⟨2, 3, 274960, 274960, 434916394785, 288459546885⟩, 16711934))
 (.leaf (⟨2, 3, 274960, 274960, 434899617585, 288459527685⟩, 18088211))))
 (.branch 6
 (.branch 5
 (.leaf (⟨2, 3, 274960, 274960, 434882840370, 288459526245⟩, 21823820))
 (.leaf (⟨2, 3, 274960, 274960, 434632230720, 288459159120⟩, 12976325)))
 (.branch 7
 (.leaf (⟨2, 3, 274960, 274960, 434614404930, 288459157605⟩, 25559429))
 (.leaf (⟨2, 3, 274960, 274960, 434345969475, 288459130725⟩, 32244203)))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf (⟨2, 3, 274960, 274960, 430319437650, 288452276325⟩, 29295038))
 (.leaf (⟨2, 3, 274960, 274960, 430051002195, 288452249445⟩, 33620480)))
 (.branch 11
 (.leaf (⟨2, 3, 274960, 274960, 361599960930, 288326447205⟩, 30671315))
 (.leaf (⟨2, 3, 274960, 274960, 357036558180, 288325928805⟩, 34996757))))
 (.branch 14
 (.branch 13
 (.leaf (⟨2, 3, 274960, 274960, 288317081445, 288317081445⟩, 36373034))
 (.leaf (⟨2, 3, 274720, 274720, 434918491920, 288459547920⟩, 7405684)))
 (.branch 15
 (.leaf (⟨2, 3, 274720, 274720, 434917443360, 288459546960⟩, 11141293))
 (.leaf (⟨2, 3, 274720, 274720, 434916394785, 288459546885⟩, 16253179))))))
 (.branch 24
 (.branch 20
 (.branch 18
 (.branch 17
 (.leaf (⟨2, 3, 274720, 274720, 434899617585, 288459527685⟩, 17629456))
 (.leaf (⟨2, 3, 274720, 274720, 434882840370, 288459526245⟩, 21365065)))
 (.branch 19
 (.leaf (⟨2, 3, 274720, 274720, 434632230720, 288459159120⟩, 12517570))
 (.leaf (⟨2, 3, 274720, 274720, 434614404930, 288459157605⟩, 25100674))))
 (.branch 22
 (.branch 21
 (.leaf (⟨2, 3, 274720, 274720, 434345969475, 288459130725⟩, 31785448))
 (.leaf (⟨2, 3, 274720, 274720, 430319437650, 288452276325⟩, 28836283)))
 (.branch 23
 (.leaf (⟨2, 3, 274720, 274720, 430051002195, 288452249445⟩, 33161725))
 (.leaf (⟨2, 3, 274720, 274720, 361599960930, 288326447205⟩, 30212560)))))
 (.branch 28
 (.branch 26
 (.branch 25
 (.leaf (⟨2, 3, 274720, 274720, 357036558180, 288325928805⟩, 34538002))
 (.leaf (⟨2, 3, 274720, 274720, 288317081445, 288317081445⟩, 35914279)))
 (.branch 27
 (.leaf (⟨2, 3, 274465, 274690, 434918491920, 288459547920⟩, 7471221))
 (.leaf (⟨2, 3, 274465, 274690, 434917443360, 288459546960⟩, 11206830))))
 (.branch 30
 (.branch 29
 (.leaf (⟨2, 3, 274465, 274690, 434916394785, 288459546885⟩, 16318716))
 (.leaf (⟨2, 3, 274465, 274690, 434899617585, 288459527685⟩, 17694993)))
 (.branch 31
 (.leaf (⟨2, 3, 274465, 274690, 434882840370, 288459526245⟩, 21430602))
 (.leaf (⟨2, 3, 274465, 274690, 434632230720, 288459159120⟩, 12583107)))))))
 (.branch 48
 (.branch 40
 (.branch 36
 (.branch 34
 (.branch 33
 (.leaf (⟨2, 3, 274465, 274690, 434614404930, 288459157605⟩, 25166211))
 (.leaf (⟨2, 3, 274465, 274690, 434345969475, 288459130725⟩, 31850985)))
 (.branch 35
 (.leaf (⟨2, 3, 274465, 274690, 430319437650, 288452276325⟩, 28901820))
 (.leaf (⟨2, 3, 274465, 274690, 430051002195, 288452249445⟩, 33227262))))
 (.branch 38
 (.branch 37
 (.leaf (⟨2, 3, 274465, 274690, 361599960930, 288326447205⟩, 30278097))
 (.leaf (⟨2, 3, 274465, 274690, 357036558180, 288325928805⟩, 34603539)))
 (.branch 39
 (.leaf (⟨2, 3, 274465, 274690, 288317081445, 288317081445⟩, 35979816))
 (.leaf (⟨3, 3, 274960, 274960, 434925761040, 361742426640⟩, 87043968751630525089448011)))))
 (.branch 44
 (.branch 42
 (.branch 41
 (.leaf (⟨3, 3, 274960, 274960, 434875429665, 361742409990⟩, 253878277547975662617624789))
 (.leaf (⟨3, 3, 274960, 274960, 434623771680, 361742102880⟩, 159580624750041454449524871)))
 (.branch 43
 (.leaf (⟨3, 3, 274960, 274960, 429775156530, 361736179830⟩, 348175930345909870785724707))
 (.leaf (⟨3, 3, 274960, 274960, 356760712770, 361625649270⟩, 417085753544400253677797724))))
 (.branch 46
 (.branch 45
 (.leaf (⟨3, 3, 274960, 274960, 288041236050, 361617784950⟩, 485995576742890636569870741))
 (.leaf (⟨2, 3, 270385, 267010, 434918491920, 288459547920⟩, 7929978)))
 (.branch 47
 (.leaf (⟨2, 3, 270385, 267010, 434917443360, 288459546960⟩, 11665587))
 (.leaf (⟨2, 3, 270385, 267010, 434916394785, 288459546885⟩, 16777473))))))
 (.branch 56
 (.branch 52
 (.branch 50
 (.branch 49
 (.leaf (⟨2, 3, 270385, 267010, 434899617585, 288459527685⟩, 18153750))
 (.leaf (⟨2, 3, 270385, 267010, 434882840370, 288459526245⟩, 21889359)))
 (.branch 51
 (.leaf (⟨2, 3, 270385, 267010, 434632230720, 288459159120⟩, 13041864))
 (.leaf (⟨2, 3, 270385, 267010, 434614404930, 288459157605⟩, 25624968))))
 (.branch 54
 (.branch 53
 (.leaf (⟨2, 3, 270385, 267010, 434345969475, 288459130725⟩, 32309742))
 (.leaf (⟨2, 3, 270385, 267010, 430319437650, 288452276325⟩, 29360577)))
 (.branch 55
 (.leaf (⟨2, 3, 270385, 267010, 430051002195, 288452249445⟩, 33686019))
 (.leaf (⟨2, 3, 270385, 267010, 361599960930, 288326447205⟩, 30736854)))))
 (.branch 60
 (.branch 58
 (.branch 57
 (.leaf (⟨2, 3, 270385, 267010, 357036558180, 288325928805⟩, 35062296))
 (.leaf (⟨2, 3, 270385, 267010, 288317081445, 288317081445⟩, 36438573)))
 (.branch 59
 (.leaf (⟨2, 3, 266290, 266290, 434918491920, 288459547920⟩, 7733363))
 (.leaf (⟨2, 3, 266290, 266290, 434917443360, 288459546960⟩, 11468972))))
 (.branch 62
 (.branch 61
 (.leaf (⟨2, 3, 266290, 266290, 434916394785, 288459546885⟩, 16580858))
 (.leaf (⟨2, 3, 266290, 266290, 434899617585, 288459527685⟩, 17957135)))
 (.branch 63
 (.leaf (⟨2, 3, 266290, 266290, 434882840370, 288459526245⟩, 21692744))
 (.branch 64
 (.leaf (⟨2, 3, 266290, 266290, 434632230720, 288459159120⟩, 12845249))
 (.leaf (⟨2, 3, 266290, 266290, 434614404930, 288459157605⟩, 25428353)))))))))
 (.branch 97
 (.branch 81
 (.branch 73
 (.branch 69
 (.branch 67
 (.branch 66
 (.leaf (⟨2, 3, 266290, 266290, 434345969475, 288459130725⟩, 32113127))
 (.leaf (⟨2, 3, 266290, 266290, 430319437650, 288452276325⟩, 29163962)))
 (.branch 68
 (.leaf (⟨2, 3, 266290, 266290, 430051002195, 288452249445⟩, 33489404))
 (.leaf (⟨2, 3, 266290, 266290, 361599960930, 288326447205⟩, 30540239))))
 (.branch 71
 (.branch 70
 (.leaf (⟨2, 3, 266290, 266290, 357036558180, 288325928805⟩, 34865681))
 (.leaf (⟨2, 3, 266290, 266290, 288317081445, 288317081445⟩, 36241958)))
 (.branch 72
 (.leaf (⟨3, 3, 262945, 270595, 434925761040, 361742426640⟩, 88252968359065861147328586))
 (.leaf (⟨3, 3, 262945, 270595, 434875429665, 361742409990⟩, 255087277155410998675505364)))))
 (.branch 77
 (.branch 75
 (.branch 74
 (.leaf (⟨3, 3, 262945, 270595, 434623771680, 361742102880⟩, 160789624357476790507405446))
 (.leaf (⟨3, 3, 262945, 270595, 429775156530, 361736179830⟩, 349384929953345206843605282)))
 (.branch 76
 (.leaf (⟨3, 3, 262945, 270595, 356760712770, 361625649270⟩, 418294753151835589735678299))
 (.leaf (⟨3, 3, 262945, 270595, 288041236050, 361617784950⟩, 487204576350325972627751316))))
 (.branch 79
 (.branch 78
 (.leaf (⟨2, 3, 205120, 82720, 434918491920, 288459547920⟩, 7929978))
 (.leaf (⟨2, 3, 205120, 82720, 434917443360, 288459546960⟩, 11665587)))
 (.branch 80
 (.leaf (⟨2, 3, 205120, 82720, 434916394785, 288459546885⟩, 16777473))
 (.leaf (⟨2, 3, 205120, 82720, 434899617585, 288459527685⟩, 18153750))))))
 (.branch 89
 (.branch 85
 (.branch 83
 (.branch 82
 (.leaf (⟨2, 3, 205120, 82720, 434882840370, 288459526245⟩, 21889359))
 (.leaf (⟨2, 3, 205120, 82720, 434632230720, 288459159120⟩, 13041864)))
 (.branch 84
 (.leaf (⟨2, 3, 205120, 82720, 434614404930, 288459157605⟩, 25624968))
 (.leaf (⟨2, 3, 205120, 82720, 434345969475, 288459130725⟩, 32309742))))
 (.branch 87
 (.branch 86
 (.leaf (⟨2, 3, 205120, 82720, 430319437650, 288452276325⟩, 29360577))
 (.leaf (⟨2, 3, 205120, 82720, 430051002195, 288452249445⟩, 33686019)))
 (.branch 88
 (.leaf (⟨2, 3, 205120, 82720, 361599960930, 288326447205⟩, 30736854))
 (.leaf (⟨2, 3, 205120, 82720, 357036558180, 288325928805⟩, 35062296)))))
 (.branch 93
 (.branch 91
 (.branch 90
 (.leaf (⟨2, 3, 205120, 82720, 288317081445, 288317081445⟩, 36438573))
 (.leaf (⟨2, 3, 200770, 81970, 434918491920, 288459547920⟩, 7602289)))
 (.branch 92
 (.leaf (⟨2, 3, 200770, 81970, 434917443360, 288459546960⟩, 11337898))
 (.leaf (⟨2, 3, 200770, 81970, 434916394785, 288459546885⟩, 16449784))))
 (.branch 95
 (.branch 94
 (.leaf (⟨2, 3, 200770, 81970, 434899617585, 288459527685⟩, 17826061))
 (.leaf (⟨2, 3, 200770, 81970, 434882840370, 288459526245⟩, 21561670)))
 (.branch 96
 (.leaf (⟨2, 3, 200770, 81970, 434632230720, 288459159120⟩, 12714175))
 (.leaf (⟨2, 3, 200770, 81970, 434614404930, 288459157605⟩, 25297279)))))))
 (.branch 113
 (.branch 105
 (.branch 101
 (.branch 99
 (.branch 98
 (.leaf (⟨2, 3, 200770, 81970, 434345969475, 288459130725⟩, 31982053))
 (.leaf (⟨2, 3, 200770, 81970, 430319437650, 288452276325⟩, 29032888)))
 (.branch 100
 (.leaf (⟨2, 3, 200770, 81970, 430051002195, 288452249445⟩, 33358330))
 (.leaf (⟨2, 3, 200770, 81970, 361599960930, 288326447205⟩, 30409165))))
 (.branch 103
 (.branch 102
 (.leaf (⟨2, 3, 200770, 81970, 357036558180, 288325928805⟩, 34734607))
 (.leaf (⟨2, 3, 200770, 81970, 288317081445, 288317081445⟩, 36110884)))
 (.branch 104
 (.leaf (⟨3, 3, 201760, 147760, 434925761040, 361742426640⟩, 88252968359065861147328586))
 (.leaf (⟨3, 3, 201760, 147760, 434875429665, 361742409990⟩, 255087277155410998675505364)))))
 (.branch 109
 (.branch 107
 (.branch 106
 (.leaf (⟨3, 3, 201760, 147760, 434623771680, 361742102880⟩, 160789624357476790507405446))
 (.leaf (⟨3, 3, 201760, 147760, 429775156530, 361736179830⟩, 349384929953345206843605282)))
 (.branch 108
 (.leaf (⟨3, 3, 201760, 147760, 356760712770, 361625649270⟩, 418294753151835589735678299))
 (.leaf (⟨3, 3, 201760, 147760, 288041236050, 361617784950⟩, 487204576350325972627751316))))
 (.branch 111
 (.branch 110
 (.leaf (⟨2, 3, 135235, 66610, 434918491920, 288459547920⟩, 8126587))
 (.leaf (⟨2, 3, 135235, 66610, 434917443360, 288459546960⟩, 11862196)))
 (.branch 112
 (.leaf (⟨2, 3, 135235, 66610, 434916394785, 288459546885⟩, 16974082))
 (.leaf (⟨2, 3, 135235, 66610, 434899617585, 288459527685⟩, 18350359))))))
 (.branch 121
 (.branch 117
 (.branch 115
 (.branch 114
 (.leaf (⟨2, 3, 135235, 66610, 434882840370, 288459526245⟩, 22085968))
 (.leaf (⟨2, 3, 135235, 66610, 434632230720, 288459159120⟩, 13238473)))
 (.branch 116
 (.leaf (⟨2, 3, 135235, 66610, 434614404930, 288459157605⟩, 25821577))
 (.leaf (⟨2, 3, 135235, 66610, 434345969475, 288459130725⟩, 32506351))))
 (.branch 119
 (.branch 118
 (.leaf (⟨2, 3, 135235, 66610, 430319437650, 288452276325⟩, 29557186))
 (.leaf (⟨2, 3, 135235, 66610, 430051002195, 288452249445⟩, 33882628)))
 (.branch 120
 (.leaf (⟨2, 3, 135235, 66610, 361599960930, 288326447205⟩, 30933463))
 (.leaf (⟨2, 3, 135235, 66610, 357036558180, 288325928805⟩, 35258905)))))
 (.branch 125
 (.branch 123
 (.branch 122
 (.leaf (⟨2, 3, 135235, 66610, 288317081445, 288317081445⟩, 36635182))
 (.leaf (⟨4, 3, 148240, 205840, 434488427280, 435025028880⟩, 60723917020200447675001038323269863663403903281889836395663300425678901620066263225708610860604493388756184727653)))
 (.branch 124
 (.leaf (⟨4, 3, 148240, 205840, 141893788995, 434917935495⟩, 4339365593907155931304647738353737454830323491089718075772740272311585732475220637599891485060129134315372544))
 (.leaf (⟨3, 3, 66610, 135235, 434925761040, 361742426640⟩, 91879727370039792234987591))))
 (.branch 127
 (.branch 126
 (.leaf (⟨3, 3, 66610, 135235, 434875429665, 361742409990⟩, 258714036166384929763164369))
 (.leaf (⟨3, 3, 66610, 135235, 434623771680, 361742102880⟩, 164416383368450721595064451)))
 (.branch 128
 (.leaf (⟨3, 3, 66610, 135235, 429775156530, 361736179830⟩, 353011688964319137931264287))
 (.branch 129
 (.leaf (⟨3, 3, 66610, 135235, 356760712770, 361625649270⟩, 421921512162809520823337304))
 (.leaf (⟨3, 3, 66610, 135235, 288041236050, 361617784950⟩, 490831335361299903715410321))))))))))
noncomputable def raw (i : Fin blockCount) : RawFacePlacement.Block := (records.get i.val).1
noncomputable def witness (i : Fin blockCount) (code : Nat) : Fin 560 :=
  Fin.ofNat 560 (Nat.land (Nat.shiftRight (records.get i.val).2 (16 * code)) 65535)
noncomputable def faceTable : Table Nat :=
(.branch 12312
 (.branch 6164
 (.branch 5130
 (.branch 3108
 (.branch 3084
 (.branch 3078
 (.branch 3077
 (.leaf 0)
 (.leaf 1))
 (.branch 3082
 (.leaf 2)
 (.leaf 3)))
 (.branch 3092
 (.branch 3089
 (.leaf 4)
 (.leaf 5))
 (.branch 3096
 (.leaf 6)
 (.leaf 7))))
 (.branch 3168
 (.branch 3140
 (.branch 3112
 (.leaf 8)
 (.leaf 9))
 (.branch 3152
 (.leaf 10)
 (.leaf 11)))
 (.branch 5125
 (.branch 5123
 (.leaf 12)
 (.leaf 13))
 (.branch 5126
 (.leaf 14)
 (.leaf 15)))))
 (.branch 5200
 (.branch 5144
 (.branch 5137
 (.branch 5132
 (.leaf 16)
 (.leaf 17))
 (.branch 5140
 (.leaf 18)
 (.leaf 19)))
 (.branch 5160
 (.branch 5156
 (.leaf 20)
 (.leaf 21))
 (.branch 5188
 (.leaf 22)
 (.leaf 23))))
 (.branch 6150
 (.branch 6147
 (.branch 5216
 (.leaf 24)
 (.leaf 25))
 (.branch 6149
 (.leaf 26)
 (.leaf 27)))
 (.branch 6156
 (.branch 6154
 (.leaf 28)
 (.leaf 29))
 (.branch 6161
 (.leaf 30)
 (.leaf 31))))))
 (.branch 10250
 (.branch 7182
 (.branch 6212
 (.branch 6180
 (.branch 6168
 (.leaf 32)
 (.leaf 33))
 (.branch 6184
 (.leaf 34)
 (.leaf 35)))
 (.branch 6240
 (.branch 6224
 (.leaf 36)
 (.leaf 37))
 (.branch 7175
 (.leaf 38)
 (.leaf 39))))
 (.branch 7268
 (.branch 7212
 (.branch 7189
 (.leaf 40)
 (.leaf 41))
 (.branch 7252
 (.leaf 42)
 (.leaf 43)))
 (.branch 10245
 (.branch 10243
 (.leaf 44)
 (.leaf 45))
 (.branch 10246
 (.leaf 46)
 (.leaf 47)))))
 (.branch 10320
 (.branch 10264
 (.branch 10257
 (.branch 10252
 (.leaf 48)
 (.leaf 49))
 (.branch 10260
 (.leaf 50)
 (.leaf 51)))
 (.branch 10280
 (.branch 10276
 (.leaf 52)
 (.leaf 53))
 (.branch 10308
 (.leaf 54)
 (.leaf 55))))
 (.branch 12294
 (.branch 12291
 (.branch 10336
 (.leaf 56)
 (.leaf 57))
 (.branch 12293
 (.leaf 58)
 (.leaf 59)))
 (.branch 12300
 (.branch 12298
 (.leaf 60)
 (.leaf 61))
 (.branch 12305
 (.leaf 62)
 (.branch 12308
 (.leaf 63)
 (.leaf 64))))))))
 (.branch 20504
 (.branch 17420
 (.branch 14357
 (.branch 12368
 (.branch 12328
 (.branch 12324
 (.leaf 65)
 (.leaf 66))
 (.branch 12356
 (.leaf 67)
 (.leaf 68)))
 (.branch 14343
 (.branch 12384
 (.leaf 69)
 (.leaf 70))
 (.branch 14350
 (.leaf 71)
 (.leaf 72))))
 (.branch 17411
 (.branch 14420
 (.branch 14380
 (.leaf 73)
 (.leaf 74))
 (.branch 14436
 (.leaf 75)
 (.leaf 76)))
 (.branch 17414
 (.branch 17413
 (.leaf 77)
 (.leaf 78))
 (.branch 17418
 (.leaf 79)
 (.leaf 80)))))
 (.branch 17504
 (.branch 17444
 (.branch 17428
 (.branch 17425
 (.leaf 81)
 (.leaf 82))
 (.branch 17432
 (.leaf 83)
 (.leaf 84)))
 (.branch 17476
 (.branch 17448
 (.leaf 85)
 (.leaf 86))
 (.branch 17488
 (.leaf 87)
 (.leaf 88))))
 (.branch 20490
 (.branch 20485
 (.branch 20483
 (.leaf 89)
 (.leaf 90))
 (.branch 20486
 (.leaf 91)
 (.leaf 92)))
 (.branch 20497
 (.branch 20492
 (.leaf 93)
 (.leaf 94))
 (.branch 20500
 (.leaf 95)
 (.leaf 96))))))
 (.branch 24588
 (.branch 21525
 (.branch 20560
 (.branch 20520
 (.branch 20516
 (.leaf 97)
 (.leaf 98))
 (.branch 20548
 (.leaf 99)
 (.leaf 100)))
 (.branch 21511
 (.branch 20576
 (.leaf 101)
 (.leaf 102))
 (.branch 21518
 (.leaf 103)
 (.leaf 104))))
 (.branch 24579
 (.branch 21588
 (.branch 21548
 (.leaf 105)
 (.leaf 106))
 (.branch 21604
 (.leaf 107)
 (.leaf 108)))
 (.branch 24582
 (.branch 24581
 (.leaf 109)
 (.leaf 110))
 (.branch 24586
 (.leaf 111)
 (.leaf 112)))))
 (.branch 24672
 (.branch 24612
 (.branch 24596
 (.branch 24593
 (.leaf 113)
 (.leaf 114))
 (.branch 24600
 (.leaf 115)
 (.leaf 116)))
 (.branch 24644
 (.branch 24616
 (.leaf 117)
 (.leaf 118))
 (.branch 24656
 (.leaf 119)
 (.leaf 120))))
 (.branch 28686
 (.branch 27768
 (.branch 27675
 (.leaf 121)
 (.leaf 122))
 (.branch 28679
 (.leaf 123)
 (.leaf 124)))
 (.branch 28716
 (.branch 28693
 (.leaf 125)
 (.leaf 126))
 (.branch 28756
 (.leaf 127)
 (.branch 28772
 (.leaf 128)
 (.leaf 129)))))))))
noncomputable def faceWitness (s r : Nat) : Fin blockCount :=
  Fin.ofNat blockCount (faceTable.get (s * 1024 + r))
noncomputable def validity (i : Nat) : Bool :=
  RawFaceNormalizers.blockValidCheck 5 (raw (Fin.ofNat blockCount i))
noncomputable def placement (b : Fin blockCount) (code : Nat) : Bool :=
  RawKindedFacePlacement.check 5 (raw b) template root FacetUniverses.RootedSevenPure051.cells
    code 0 (witness b code)
noncomputable def test (i : Nat) : Bool :=
  let b := Fin.ofNat blockCount i
  FiniteChecks.checkRange (placement b)
    0 (RawFacePlacement.count (raw b).shared (raw b).shared)
noncomputable def symmetry (i : Nat) : Bool :=
  RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenPure051.Outside.vertexCode root.vertices
    (raw (Fin.ofNat blockCount i))
end Papers.RationalityTen.RootedCanonical.RootedSevenPure051.S5T1

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSevenPure051.S5T1
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
end Papers.RationalityTen.RootedCanonical.RootedSevenPure051.S5T1

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSevenPure051.S5T1
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
theorem check_0076_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 76)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 76)) 0 6 (by decide +kernel)
theorem block_0076 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 76)) 0 6 :=
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
theorem check_0108_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 108)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 108)) 0 6 (by decide +kernel)
theorem block_0108 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 108)) 0 6 :=
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
theorem check_0122_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 122)) 0 8 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 122)) 0 8 (by decide +kernel)
theorem check_0122_0008 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 122)) 8 16 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 122)) 8 8 (by decide +kernel)
theorem check_0122_0016 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 122)) 16 24 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 122)) 16 8 (by decide +kernel)
theorem block_0122 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 122)) 0 24 :=
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 122)) 0 8 24
  check_0122_0000
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 122)) 8 16 24
  check_0122_0008
  check_0122_0016))
theorem check_0123_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 123)) 0 8 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 123)) 0 8 (by decide +kernel)
theorem check_0123_0008 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 123)) 8 16 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 123)) 8 8 (by decide +kernel)
theorem check_0123_0016 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 123)) 16 24 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 123)) 16 8 (by decide +kernel)
theorem block_0123 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 123)) 0 24 :=
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 123)) 0 8 24
  check_0123_0000
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 123)) 8 16 24
  check_0123_0008
  check_0123_0016))
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
end Papers.RationalityTen.RootedCanonical.RootedSevenPure051.S5T1

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSevenPure051.S5T1
theorem check_0128_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 128)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 128)) 0 6 (by decide +kernel)
theorem block_0128 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 128)) 0 6 :=
  check_0128_0000
theorem check_0129_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 129)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 129)) 0 6 (by decide +kernel)
theorem block_0129 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 129)) 0 6 :=
  check_0129_0000
end Papers.RationalityTen.RootedCanonical.RootedSevenPure051.S5T1

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSevenPure051.S5T1
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
theorem metadata_validity_0128 : FiniteChecks.Interval validity 128 130 :=
  FiniteChecks.interval_of_check validity 128 2 (by decide +kernel)
theorem metadata_validity : FiniteChecks.Interval validity 0 blockCount :=
  (FiniteChecks.interval_append (validity) 0 64 130
  (FiniteChecks.interval_append (validity) 0 32 64
  (FiniteChecks.interval_append (validity) 0 16 32
  metadata_validity_0000
  metadata_validity_0016)
  (FiniteChecks.interval_append (validity) 32 48 64
  metadata_validity_0032
  metadata_validity_0048))
  (FiniteChecks.interval_append (validity) 64 96 130
  (FiniteChecks.interval_append (validity) 64 80 96
  metadata_validity_0064
  metadata_validity_0080)
  (FiniteChecks.interval_append (validity) 96 112 130
  metadata_validity_0096
  (FiniteChecks.interval_append (validity) 112 128 130
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
theorem metadata_symmetry_0128 : FiniteChecks.Interval symmetry 128 130 :=
  FiniteChecks.interval_of_check symmetry 128 2 (by decide +kernel)
theorem metadata_symmetry : FiniteChecks.Interval symmetry 0 blockCount :=
  (FiniteChecks.interval_append (symmetry) 0 64 130
  (FiniteChecks.interval_append (symmetry) 0 32 64
  (FiniteChecks.interval_append (symmetry) 0 16 32
  metadata_symmetry_0000
  metadata_symmetry_0016)
  (FiniteChecks.interval_append (symmetry) 32 48 64
  metadata_symmetry_0032
  metadata_symmetry_0048))
  (FiniteChecks.interval_append (symmetry) 64 96 130
  (FiniteChecks.interval_append (symmetry) 64 80 96
  metadata_symmetry_0064
  metadata_symmetry_0080)
  (FiniteChecks.interval_append (symmetry) 96 112 130
  metadata_symmetry_0096
  (FiniteChecks.interval_append (symmetry) 112 128 130
  metadata_symmetry_0112
  metadata_symmetry_0128))))
theorem metadata_normalizers :
    RawFaceNormalizers.completeCheck 5 template root raw faceWitness = true := by decide +kernel
theorem metadata_root : RawFacetEmbedding.wellFormedCheck root = true := by decide +kernel
end Papers.RationalityTen.RootedCanonical.RootedSevenPure051.S5T1
